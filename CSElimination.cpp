#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"        
#include "llvm/Support/Casting.h" 
#include <iostream>
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <queue>
#include <vector>

using namespace llvm;
using namespace std;


#define DEBUG_TYPE "CSElimination"

namespace
{
  
struct Expression{
  std::vector<Value*> operands;
  Instruction* instruction;
  unsigned opcode;
  Expression(Instruction* instr_,unsigned op, std::vector<Value*> ops):instruction(instr_), opcode(op), operands(ops) {}

    static bool sameValue(Value* A, Value* B) {
      // Same pointer => same
      if (A == B) return true;

      // If both are constants, compare them structurally
      if (auto *CA = dyn_cast<Constant>(A)) {
          if (auto *CB = dyn_cast<Constant>(B))
              return CA->isElementWiseEqual(CB);
      }

      // If both have names (%x, %y)
      if (A->hasName() && B->hasName())
          return A->getName() == B->getName();

      // Otherwise treat as not equal
      return false;
  }

  bool operator==(const Expression& rhs) const {
        if (opcode != rhs.opcode){
          //errs() << "Returning false because of opcode: " << opcode << " " << rhs.opcode << "\n";
          return false;
        }
        if (operands.size() != rhs.operands.size()){
          errs() << "Returning false because of operand LENGTH: " << operands.size() << " " << rhs.operands.size() << "\n";
          return false;
        }

        for (size_t i = 0; i < operands.size(); i++) {
            if (!sameValue(operands[i], rhs.operands[i])){
              errs() << "Returning false because of: " << *(operands[i]) << " " << *(rhs.operands[i]) << "\n";
              return false;
            }
        }
        return true;
    }

  bool operator!=(const Expression& rhs) const {
    return !(*this == rhs);
  }

  bool usesOperand(Value* V) const {
    for (auto *op : operands) {
        if (op == V)
            return true;
    }
    return false;
  }
};

struct ExpressionHash {
    std::size_t operator()(Expression const& e) const noexcept {
        std::size_t h = std::hash<unsigned>()(e.opcode);
        for (auto *op : e.operands)
            h ^= std::hash<Value*>()(op) + 0x9e3779b97f4a7c15ULL + (h<<6) + (h>>2);
        return h;
    }
};

struct Definition{
  llvm::Instruction* instruction;
  llvm::Value* variable; //where its being written

  Definition(llvm::Instruction* instr, llvm::Value* var): instruction(instr), variable(var){}

  bool operator<(const Definition& other) const {
        return variable < other.variable;
  }

  bool operator==(const Definition& other) const {
      return variable == other.variable;
  }
};

struct DefinitionHash {
    size_t operator()(Definition const& d) const noexcept {
        return std::hash<void*>()(d.variable) ^
               (std::hash<void*>()(d.instruction) << 1);
    }
};

struct ReplacementTask {
  std::vector<Instruction*> redundants;    // all others that compute B op C
  Expression expr;

  ReplacementTask(std::vector<Instruction*>& redun_, Expression expr_):
  redundants(redun_),
  expr(expr_){}
};

std::vector<llvm::Value*> getOperands(llvm::Instruction& instruction){
  std::vector<llvm::Value*> ops;
    for(unsigned i = 0; i < instruction.getNumOperands(); ++i) {
        // Skip non-value operands (like block addresses, metadata)
        llvm::Value* operand = instruction.getOperand(i);
        if (isa<BasicBlock>(operand)) continue;
        if (isa<MetadataAsValue>(operand)) continue;
        if (isa<Function>(operand) && isa<CallBase>(instruction)) continue;

        LoadInst* load = dyn_cast<LoadInst>((&instruction)->getOperand(i));
        if(load){
          ops.push_back(load->getPointerOperand());
        }else{
          ops.push_back((&instruction)->getOperand(i));          
        }
        
    }
    return ops;
}

bool isPureIntegerOp(Instruction *I) {
    
    switch (I->getOpcode()) {
        case Instruction::Add:
        case Instruction::Sub:
        case Instruction::Mul:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Xor:
        case Instruction::Shl:
        case Instruction::LShr:
        case Instruction::AShr:
            return true;
        default:
            return false;
    }
}


  //Contains all the available expression in each basic block
struct AvailableExpr{
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> IN;
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> OUT;

  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> killSets;
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> genSets;

  AvailableExpr(){}

  ~AvailableExpr(){}
 
  void runAvailableExpr(Function &F, std::unordered_set<Expression, ExpressionHash>& allExprs){     


    //Kill sets
    //any expression in which the operands are redefined in the block
    for (auto &basic_block : F) {
        for(auto& instruction : basic_block){
          if (auto *SI = dyn_cast<StoreInst>(&instruction)) {
              Value *storedPtr = SI->getPointerOperand();

              for (auto &expr : allExprs) {
                  bool containsLoad = false;
                  if(isa<LoadInst>(expr.instruction)) containsLoad = true;

                  for(int i = 0; i < expr.instruction->getNumOperands(); ++i){
                    LoadInst* load = dyn_cast<LoadInst>((expr.instruction)->getOperand(i));
                    if(load) containsLoad = true;
                  }

                  if (!containsLoad)
                      continue;

                  for(auto& op : expr.operands){
                    if(Expression::sameValue(op,storedPtr)){
                      killSets[&basic_block].insert(expr);
                      break;
                    }
                  }


              }
          }
        }
    }

    /*std::cout << "Available Expressions KILL SETS!" << std::endl;
    for(auto& basic_block : F){
      for(auto& aExpr : killSets[&basic_block]){
        errs() << *(aExpr.instruction) << " | ";
        for(auto& op: aExpr.operands){
          errs() << *(op) << " ";
        }
        errs() << "\n";
        
      }
      errs() << "b--------\n";
    }*/
    

    //Gen sets
    //any expression used in block where operands are not redefined
    for (auto &basic_block : F) {

        for (auto &inst : basic_block) {
            
            // Must produce a value
            if (inst.getType()->isVoidTy())
                continue;

            // Must be a pure, side-effect-free expression
            if (!isPureIntegerOp(&inst))
                continue;

            if((&inst)->getOpcode() == Instruction::Load){
                auto *LI = dyn_cast<LoadInst>(&inst);
                if (!(LI->isVolatile() || LI->isAtomic())) continue;
            }

            genSets[&basic_block].emplace(&inst,inst.getOpcode(), getOperands(inst));
        }
    }
    
    //go through all the blocks
    //eventually it'll stabilize
    //you have to compare the previous set and the current set
    //set the unordered map at the end
    
    //initialize all IN and OUT sets of the CFG
    for(auto &basic_block : F){

      //if num of predeccessors is 0, i.e. is the start node, initialize IN to be empty
      if(std::distance(pred_begin(&basic_block), pred_end(&basic_block)) == 0) continue;

      //otherwise, set to all expr
      IN[&basic_block] = allExprs;
    }

    /*
    std::cout << "Available Expressions GEN SETS!" << std::endl;
    for(auto& basic_block : F){
      for(auto& aExpr : genSets[&basic_block]){
        errs() << *(aExpr.instruction) << " | ";
        for(auto& op: aExpr.operands){
          errs() << *(op) << " ";
        }
        errs() << "\n";
        
      }
      errs() << "b--------\n";
    }*/





    bool changes = true;
    while(changes){
      changes = false;
      //compute the in and out sets of each block
      for(auto& basic_block : F){
        std::unordered_set<Expression,ExpressionHash> oldIN = IN[&basic_block];
        std::unordered_set<Expression,ExpressionHash> oldOUT = OUT[&basic_block];

        //IN is the intersection of all predecessors
        if(std::distance(pred_begin(&basic_block), pred_end(&basic_block)) > 0){
          
          std::unordered_set<Expression, ExpressionHash> intersection = OUT[*pred_begin(&basic_block)];

          for(auto i = pred_begin(&basic_block); i != pred_end(&basic_block); ++i){
            for (auto it = intersection.begin(); it != intersection.end(); ) {
                if (!OUT[*i].count(*it)) {
                    it = intersection.erase(it);   // remove expressions not in this pred
                } else {
                    ++it;
                }
            }
          }

          IN[&basic_block] = std::move(intersection);

          /*
          std::cout << "Available Expressions COMPUTED INS!" << std::endl;
          for(auto& basic_block : F){
            for(auto& aExpr : IN[&basic_block]){
              errs() << *(aExpr.instruction) << " | ";
              for(auto& op : aExpr.operands){
                errs() << *(op) << " ";
              }
              errs() << "\n";
              
            }
            errs() << "b--------\n";
          }*/
        }

        //compute difference
        std::unordered_set<Expression, ExpressionHash> diff;
        for(Expression expr : IN[&basic_block]){
          if(killSets[&basic_block].find(expr) == killSets[&basic_block].end()){
            diff.insert(expr);
          }
        }

        //compute out = gen u (in - kill)
        OUT[&basic_block] = genSets[&basic_block];
        for(Expression expr : diff){
          OUT[&basic_block].insert(expr);
        }

        

        //set changes based on if theres any differences in the sets
        if(oldIN != IN[&basic_block] || oldOUT != OUT[&basic_block]){
          errs() << "AE CHANGED **************************\n"; 
          changes = true;
        }

      }
    }


  }
};

struct ReachingDefs{
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Definition, DefinitionHash>> IN;
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Definition, DefinitionHash>> OUT;


  ReachingDefs(){}

  ~ReachingDefs(){}
 
  void runReachingDefs(Function &F, std::unordered_set<Definition, DefinitionHash>& allDefs){     
    //TO DO
    //will this run into issues if two identical expressions in the same block
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Definition, DefinitionHash>> killSets;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Definition, DefinitionHash>> genSets;

    //Generate GEN sets
    for(auto &basic_block : F){
      for(auto &instruction : basic_block){
          // skip instructions that do not define a value
          if(!instruction.getType()->isVoidTy()){

            // add instruction to GEN set
            genSets[&basic_block].emplace(&instruction, &instruction);
          }

          if (auto *SI = dyn_cast<StoreInst>(&instruction)) {
            genSets[&basic_block].emplace(&instruction, &instruction);  // treat store as a def
          }
      }
    }


    //Generate KILL sets
    for (auto &basic_block : F) {
        for(auto& instruction : basic_block){
          if (auto *SI = dyn_cast<StoreInst>(&instruction)) {
              Value *storedPtr = SI->getPointerOperand();

              for (auto &def : allDefs) {
                  

                  if (auto *PrevStore = dyn_cast<StoreInst>(def.instruction)) {
                    if (PrevStore == SI) continue;
                    Value *previousDef = PrevStore->getPointerOperand();

                    if (Expression::sameValue(previousDef, storedPtr)) {
                        killSets[&basic_block].emplace(PrevStore,PrevStore);
                    }
                }
              }


          }
        }
    }

    std::cout << "Reaching Definitions KILL SETS!" << std::endl;
    for(auto& basic_block : F){
      for(auto& aExpr : killSets[&basic_block]){
        errs() << *(aExpr.instruction) << " | ";
        
        errs() << "\n";
        
      }
      errs() << "b--------\n";
    }

    //Actual reaching definition pass here

    //initialize the in out sets
    for(auto& basic_block : F){
      OUT[&basic_block] = {};
      IN[&basic_block] = {};
    }

    bool change = true;

    while(change){
      change = false;
      //compute the in and out sets of each block
      for(auto& basic_block : F){
        std::unordered_set<Definition,DefinitionHash> oldIN = IN[&basic_block];
        std::unordered_set<Definition,DefinitionHash> oldOUT = OUT[&basic_block];

        //IN is the union of all predecessors
        IN[&basic_block].clear();
        for(auto i = pred_begin(&basic_block); i != pred_end(&basic_block); ++i){
          for(Definition def : OUT[*i]){
            IN[&basic_block].insert(def);
          }
        }

        //compute difference
        std::unordered_set<Definition, DefinitionHash> diff;
        for(Definition def : IN[&basic_block]){
          if(killSets[&basic_block].find(def) == killSets[&basic_block].end()){
            diff.insert(def);
          }
        }

        //compute out = gen u (in - kill)
        OUT[&basic_block] = genSets[&basic_block];
        for(Definition def : diff){
          OUT[&basic_block].insert(def);
        }

        //set change based on if theres any differences in the sets
        if(oldIN != IN[&basic_block] || oldOUT != OUT[&basic_block]) change = true;

      }
    }

    ///////////////////////////////////////


  }
};

struct CSElimination : public FunctionPass
{
  static char ID;
  CSElimination() : FunctionPass(ID) {}

bool runOnFunction(Function &F) override {
    // ... (Setup/Run AvailableExpr AE) ...

    std::cout << "Process started!" << std::endl;

    AvailableExpr AE;
    ReachingDefs RD;
    bool changed = false;

    std::unordered_set<Expression, ExpressionHash> allExprs;
    std::unordered_set<Definition, DefinitionHash> allDefs;

    //need all definitions and expressions regardless of block
    for(auto &basic_block : F){
      for(auto& instruction : basic_block){
        //check if the current instruction is a definition.

        if(!instruction.getType()->isVoidTy() || isa<StoreInst>(instruction)){
            allDefs.emplace(&instruction,&instruction);
        }
        
        if(!instruction.getType()->isVoidTy()){
            allExprs.emplace(&instruction,instruction.getOpcode(), getOperands(instruction));
        }

      }
    }

    //Just do this once, is ran for all blocks
    AE.runAvailableExpr(F,allExprs);
    std::cout << "Available Expressions has run!" << std::endl;
    for(auto& basic_block : F){
      for(auto& aExpr : AE.IN[&basic_block]){
        errs() << *(aExpr.instruction) << "\n";
      }
      errs() << "b--------\n";
    }

    RD.runReachingDefs(F,allDefs);
    std::cout << "Reaching Definitions has run!" << std::endl;
    for(auto& basic_block : F){
      for(auto& def : RD.IN[&basic_block]){
        errs() << *(def.instruction) << "\n";
      }
      errs() << "b--------\n";
    }
    errs() << "---------------------\n"; 
    errs() << "Data Flow Analysis Complete\n"; 
    errs() << "---------------------\n"; 
    std::vector<ReplacementTask> tasks;

    //forward traversal, one pass
    for(auto& basic_block : F){

      //if OUT = GEN u IN, then...

      for(auto& aExpr : AE.OUT[&basic_block]){
        
        //reaching definition instructions to change
        std::vector<Instruction*> instructionsToChange;

        //in the corresponding reaching definitions of the block, find all who have the same rhs (i.e. same operands and opcode)
        for(auto& def : RD.OUT[&basic_block]){
          
          //construct expression from rhs
          Expression defExpr(def.instruction, def.instruction->getOpcode(), getOperands(*def.instruction));
          
          if(!(defExpr == aExpr)) continue;
          if (!isPureIntegerOp(def.instruction)) continue;   // only include pure integer operations
          if(def.instruction == aExpr.instruction) continue;

          std::cout << "Found instruction to change!" << std::endl;
          changed = true;
          //if rhs is equal, add to list of instructions to change later
          instructionsToChange.push_back(def.instruction);
        }

        if (instructionsToChange.size() > 1){
          tasks.push_back(ReplacementTask(instructionsToChange,aExpr));
        }
      }
    }

    errs() << "---------------------\n"; 
    errs() << "Finding Common Subexpressions Complete\n"; 
    errs() << "---------------------\n"; 
    
    std::vector<Instruction*> deleteList;

    if(tasks.size() == 0) return true;

    llvm::IRBuilder<> entryBuilder(&F.getEntryBlock(), F.getEntryBlock().begin());
    llvm::AllocaInst* tmpPtr = entryBuilder.CreateAlloca(
        llvm::Type::getInt32Ty(F.getContext()), // type: i32
        nullptr,                                // optional array size
        "tmp"                                    // name
    );

    for (auto &task : tasks) {

      Instruction *rep = task.expr.instruction; //original to consider

      

      errs() << "Replacing instruction! " << *(task.expr.instruction)<<" \n";
      // Create the new T

      for(auto& instruction : task.redundants){
        IRBuilder<> storeBuilder(instruction->getNextNode());
        StoreInst* ST = storeBuilder.CreateStore(instruction, tmpPtr);

        //Load stored value
        IRBuilder<> builder(ST->getNextNode());
        LoadInst *L = builder.CreateLoad(
          Type::getInt32Ty(F.getContext()),
          tmpPtr
        );

        instruction->replaceAllUsesWith(L);
        ST->setOperand(0, instruction);
      }

      //load
      IRBuilder<> builder(rep->getNextNode());
        LoadInst *L = builder.CreateLoad(
          Type::getInt32Ty(F.getContext()),
          tmpPtr
        );

      //replace rep isntances
      rep->replaceAllUsesWith(L);

      //delete rep
      rep->eraseFromParent();
    }

    for(auto it = deleteList.begin(); it != deleteList.end(); ){

      if((*it)->use_empty() && (*it)->getParent()){
          if(*it) (*it)->eraseFromParent();
      } else {
          ++it;
      }
    }
    errs()<<F;
    return changed;
    
}
}; // end of struct CSElimination
} // end of anonymous namespace

char CSElimination::ID = 0;
static RegisterPass<CSElimination> X("CSElimination", "CSElimination Pass",
                                      false /* Only looks at CFG */,
                                      true /* Tranform Pass */);

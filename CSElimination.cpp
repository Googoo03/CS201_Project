#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
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
          errs() << "Returning false because of opcode: " << opcode << " " << rhs.opcode << "\n";
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

        ops.push_back(instruction.getOperand(i));
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
            return I->getOperand(0)->getType()->isIntegerTy() &&
                   I->getOperand(1)->getType()->isIntegerTy();
        default:
            return false;
    }
}


  //Contains all the available expression in each basic block
struct AvailableExpr{
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> IN;
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> OUT;

  AvailableExpr(){}

  ~AvailableExpr(){}
 
  void runAvailableExpr(Function &F, std::unordered_set<Expression, ExpressionHash>& allExprs){     
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> killSets;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> genSets;

    //Kill sets
    //any expression in which the operands are redefined in the block
    for(auto &basic_block : F){

      //set of lhs vars
      std::set<llvm::Value*> lhs_vars;

      for(auto &instruction : basic_block){
        //find all rhs expressions

        //find all lhs variables that are defined
        if (!instruction.getType()->isVoidTy()){// instruction produces a value
            lhs_vars.insert(&instruction);
        }
      }

      //resulting kill set for the block is any expression that isnt eliminated by lhs.
      for(auto expr: allExprs){
        for(auto operand: expr.operands){
          if(lhs_vars.count(operand)){ //issue arising
            killSets[&basic_block].insert(expr);
            break;
          }
        }
      }
    }

    //Gen sets
    //any expression used in block where operands are not redefined
    for(auto &basic_block : F){
      
      //set of lhs vars thus 
      std::set<llvm::Value*> lhs_vars;
      
      for(auto &instruction : basic_block){

        int canAdd = true;
        for(int i = 0; i < instruction.getNumOperands(); ++i){
          Value* op = instruction.getOperand(i);
          //no longer safe to add this to gen
          if(lhs_vars.count(op)){
            canAdd = false;
            break;
          }
        }
        if (!instruction.getType()->isVoidTy()){// instruction produces a value
            lhs_vars.insert(&instruction);
        }

        if(!canAdd) continue;

        //add to gen set
        genSets[&basic_block].emplace(&instruction,instruction.getOpcode(), getOperands(instruction));

        
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
            for(Expression expr : OUT[*i]){
              if(OUT[*i].find(expr) == OUT[*i].end()){
                intersection.erase(expr);
              }
            }
          }
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
        if(!(oldIN == IN[&basic_block] && oldOUT == OUT[&basic_block])) changes = true;

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
        //check if the instruction assigns a value
        if(instruction.getType()->isVoidTy()) continue;


        //if it does, add to the gen set
        for(auto it = genSets[&basic_block].begin(); it != genSets[&basic_block].end();){
          if ((*it).variable == dyn_cast<Value>(&instruction)){
              it = genSets[&basic_block].erase(it);
          }else{
              ++it;
          }
        }

        genSets[&basic_block].emplace(&instruction, &instruction);
      }
    }


    //Generate KILL sets
    for(auto &basic_block : F){
      for(Definition def  : genSets[&basic_block]){
        for(Definition otherDef : allDefs){
          if(def == otherDef) continue; //same one, skip it
          
          //two different definitions assigning to same variable, kill all others that
          //assign to the same variable
          if(def.variable == otherDef.variable){ 
            
            killSets[&basic_block].insert(otherDef);
          }
        }
      }
    }

    //Actual reaching definition pass here

    //initialize the in out sets
    for(auto& basic_block : F){
      OUT[&basic_block] = genSets[&basic_block]; 
    }

    bool change = false;

    while(change){
      //compute the in and out sets of each block
      for(auto& basic_block : F){
        std::unordered_set<Definition,DefinitionHash> oldIN = IN[&basic_block];
        std::unordered_set<Definition,DefinitionHash> oldOUT = OUT[&basic_block];

        //IN is the union of all predecessors
        for(auto i = pred_begin(&basic_block); i != pred_end(&basic_block); ++i){
          for(Definition def : OUT[*i]){
            IN[&basic_block].insert(def);
          }
        }

        //compute difference
        std::set<Definition> diff;
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
        if(!(oldIN == IN[&basic_block] && oldOUT == OUT[&basic_block])) change = true;

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
        if(instruction.getType()->isVoidTy()) continue;

        allDefs.emplace(&instruction,&instruction);

        allExprs.emplace(&instruction,instruction.getOpcode(), getOperands(instruction));

      }
    }

    //Just do this once, is ran for all blocks
    AE.runAvailableExpr(F,allExprs);
    std::cout << "Available Expressions has run!" << std::endl;

    RD.runReachingDefs(F,allDefs);
    std::cout << "Reaching Definitions has run!" << std::endl;

    std::vector<ReplacementTask> tasks;

    //forward traversal, one pass
    for(auto& basic_block : F){

      //loop through all expressions that make it to the end of the block (OUT)
      for(auto& aExpr : AE.IN[&basic_block]){
        
        //reaching definition instructions to change
        std::vector<Instruction*> instructionsToChange;

        std::cout << "Iterate ae" << std::endl;

        //in the corresponding reaching definitions of the block, find all who have the same rhs (i.e. same operands and opcode)
        for(auto& def : RD.OUT[&basic_block]){
          //what's a better way to do this? Will be cover all situations if we use both OUTs?
          if(def.instruction == nullptr){
            errs() << "NULL INSTRUCTION \n";
            continue;
          }
          //Make sure OUT actually has something
          errs() << *(def.instruction) << "\n";
          
          //construct expression from rhs
          Expression defExpr(def.instruction, def.instruction->getOpcode(), getOperands(*def.instruction));
          
          if(!(defExpr == aExpr)) continue;
          if (!isPureIntegerOp(def.instruction)) continue;   // only include pure integer operations

          std::cout << "Found instruction to change!" << std::endl;

          //if rhs is equal, add to list of instructions to change later
          instructionsToChange.push_back(def.instruction);
        }

        if (!instructionsToChange.empty()){
          tasks.push_back(ReplacementTask(instructionsToChange,aExpr));
        }
      }
    }

    std::vector<Instruction*> deleteList;

    for (auto &task : tasks) {

      Instruction *rep = task.expr.instruction;

      errs() << "Replacing instruction! \n";
      // Create the new T
      Instruction *T = BinaryOperator::Create(
          (Instruction::BinaryOps)task.expr.opcode,
          task.expr.operands[0],
          task.expr.operands[1]
      );
      T->setName("tmp");

      T->insertBefore(rep);

      // Replace all redundant expressions with T
      for (Instruction *I : task.redundants) {
          I->replaceAllUsesWith(T);
          deleteList.push_back(I);
      }
    }

    for (Instruction *I : deleteList)
        I->eraseFromParent();
    
}
}; // end of struct CSElimination
} // end of anonymous namespace

char CSElimination::ID = 0;
static RegisterPass<CSElimination> X("CSElimination", "CSElimination Pass",
                                      false /* Only looks at CFG */,
                                      true /* Tranform Pass */);

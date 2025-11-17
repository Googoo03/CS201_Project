#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"        
#include "llvm/Support/Casting.h" 
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
  unsigned opcode;
  Expression(unsigned op, std::vector<Value*> ops): opcode(op), operands(ops) {}

  bool operator==(const Expression& rhs) const {
    return this->opcode == rhs.opcode && this->operands == rhs.operands;
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
            auto* SI = llvm::dyn_cast<llvm::StoreInst>(&instruction);
            lhs_vars.insert(SI->getPointerOperand());
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
            //Add it
            auto* SI = llvm::dyn_cast<llvm::StoreInst>(&instruction);
            lhs_vars.insert(SI->getPointerOperand());
        }

        if(!canAdd) continue;

        //add to gen set
        std::vector<Value*> ops;
        for(int i = 0; i < instruction.getNumOperands(); ++i){
          ops.push_back(instruction.getOperand(i));
        }
        
        genSets[&basic_block].emplace(instruction.getOpcode(), ops);

        
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
      //compute the in and out sets of each block
      for(auto& basic_block : F){
        std::unordered_set<Expression,ExpressionHash> oldIN = IN[&basic_block];
        std::unordered_set<Expression,ExpressionHash> oldOUT = OUT[&basic_block];

        //IN is the intersection of all predecessors
        std::unordered_set<Expression, ExpressionHash> intersection = OUT[*pred_begin(&basic_block)];
        for(auto i = pred_begin(&basic_block); i != pred_end(&basic_block); ++i){
          for(Expression expr : OUT[*i]){
            if(OUT[*i].find(expr) == OUT[*i].end()){
              intersection.erase(expr);
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

        //if it does, add to the gen set
        if (instruction.getOpcode() == Instruction::Store) {
          auto *SI = llvm::dyn_cast<llvm::StoreInst>(&instruction);

          for(auto it = genSets[&basic_block].begin(); it != genSets[&basic_block].end();){
            if ((*it).variable == SI->getPointerOperand())
                it = genSets[&basic_block].erase(it);
            else
                ++it;
          }

          genSets[&basic_block].emplace(SI, SI->getPointerOperand());
        }
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

        allExprs.emplace(instruction.getOpcode(), getOperands(instruction));

      }
    }

    //Just do this once, is ran for all blocks
    AE.runAvailableExpr(F,allExprs);
    RD.runReachingDefs(F,allDefs);

    //forward traversal, one pass
    for(auto& basic_block : F){

      //loop through all expressions that make it to the end of the block (OUT)
      for(auto& aExpr : AE.OUT[&basic_block]){

        std::vector<Instruction*> instructionsToChange;

        //in the corresponding reaching definitions of the block, find all who have the same rhs (i.e. same operands and opcode)
        for(auto& def : RD.OUT[&basic_block]){
          //what's a better way to do this? Will be cover all situations if we use both OUTs?
          
          //construct expression from rhs
          Expression defExpr(def.instruction->getOpcode(), getOperands(*def.instruction));
          if(defExpr != aExpr) continue;

          //if rhs is equal, add to list of instructions to change later
          instructionsToChange.push_back(def.instruction);
        }

        for(auto& instruction : instructionsToChange){

          //define new T. Instructions can only belong to 1 block at a time, therefore we recreate it for each needed spot.
          Instruction* T = BinaryOperator::Create(
              (Instruction::BinaryOps)aExpr.opcode,
              aExpr.operands.at(0),
              aExpr.operands.at(1)
          );

          //insert T before each instruction
          T->insertBefore(instruction);
          
          //change current instruction to simply setting it to T
          //This is in SSA form, therefore we can replace all its uses with T directly, then delete it
          instruction->replaceAllUsesWith(T);
          instruction->eraseFromParent();
        }

        

      }
    }

    /*
    for (auto &basic_block : F) {
        // knownExpressions map: Expression* -> Instruction*
        // This holds the Instruction that is the canonical definition for an available Expression.
        // It's crucial for CSE to know which instruction to replace the use with.
        std::unordered_map<Expression*, Instruction*> knownExpressions;
        

        // --- Step 1: Initialize knownExpressions from IN set (Simplification) ---
        // In a full implementation, you'd iterate through predecessors' OUT sets
        // to find the *actual* instruction that computed each available expression.
        // For this example, we'll focus on the in-block generation/killing.

        // Loop through all instructions in the current block
        for (auto I = basic_block.begin(); I != basic_block.end(); /* No increment here ) {
            Instruction *CurrentInst = &(*I);
            I++; // Increment iterator safely before potential erasure

            // Skip non-value instructions (Stores, Branches, etc.)
            if (CurrentInst->getType()->isVoidTy() || CurrentInst->isTerminator()) {
                // If it's a store, you'd perform the Kill operation here.
                continue;
            }

            // --- Step 2: Create the Expression for the current Instruction ---
            std::vector<Value*> ops;
            for(unsigned i = 0; i < CurrentInst->getNumOperands(); ++i) {
                // Skip non-value operands (like block addresses, metadata)
                if (isa<BasicBlock>(CurrentInst->getOperand(i))) continue;
                ops.push_back(CurrentInst->getOperand(i));
            }

            // Use a unique pointer for the temporary expression object for lookup
            Expression TempExpr(CurrentInst->getOpcode(), ops);

            Instruction *PrevInst = nullptr;
            
            // --- Step 3: Look Up (Substitution) ---
            // Search through the currently known expressions to see if TempExpr is available
            for (auto const& [expr_ptr, inst_ptr] : knownExpressions) {
                if (*expr_ptr == TempExpr) {
                    PrevInst = inst_ptr;
                    break;
                }
            }

            if (PrevInst) {
                // Redundant computation found! Perform the substitution.
                CurrentInst->replaceAllUsesWith(PrevInst);
                CurrentInst->eraseFromParent();
                changed = true;
                continue; // Move to the next instruction
            }

            // --- Step 4: Generation ---
            // The instruction is not redundant. It is now the *canonical definition*
            // for this expression within the block. We must add it to the known set.
            
            // IMPORTANT: You need to ensure the Expression* added to the map is unique and persistent.
            // Since you were collecting allExprs globally, you should reuse an existing one or
            // create a new one and add it to allExprs.
            
            // For a complete solution, you'd need a way to look up the persistent Expression*
            // from the global allExprs set using TempExpr.
            
            // For a simpler, in-block only demonstration:
            Expression* NewExpr = new Expression(CurrentInst->getOpcode(), ops);
            knownExpressions[NewExpr] = CurrentInst;
        }
      }
      errs() << F;

    return changed;
    */
}
}; // end of struct CSElimination
} // end of anonymous namespace

char CSElimination::ID = 0;
static RegisterPass<CSElimination> X("CSElimination", "CSElimination Pass",
                                      false /* Only looks at CFG */,
                                      true /* Tranform Pass */);

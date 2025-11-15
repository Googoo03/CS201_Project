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
};


  //Contains all the available expression in each basic block
struct AvailableExpr{
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression*>> IN;
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression*>> OUT;

  AvailableExpr(){}

  ~AvailableExpr(){}
 
  void runAvailableExpr(Function &F, std::unordered_set<Expression*>& allExprs){     
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression*>> killSets;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression*>> genSets;

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
        for(auto operand: expr->operands){
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
        
        Expression* expr = new Expression(instruction.getOpcode(), ops);
        genSets[&basic_block].insert(expr);

        
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
        std::unordered_set<Expression*> oldIN = IN[&basic_block];
        std::unordered_set<Expression*> oldOUT = OUT[&basic_block];

        //IN is the intersection of all predecessors
        std::unordered_set<Expression*> intersection = OUT[*pred_begin(&basic_block)];
        for(auto i = pred_begin(&basic_block); i != pred_end(&basic_block); ++i){
          for(Expression* expr : OUT[*i]){
            if(OUT[*i].find(expr) == OUT[*i].end()){
              intersection.erase(expr);
            }
          }
        }

        //compute difference
        std::unordered_set<Expression*> diff;
        for(Expression* expr : IN[&basic_block]){
          if(killSets[&basic_block].find(expr) == killSets[&basic_block].end()){
            diff.insert(expr);
          }
        }

        //compute out = gen u (in - kill)
        OUT[&basic_block] = genSets[&basic_block];
        for(Expression* expr : diff){
          OUT[&basic_block].insert(expr);
        }

        //set changes based on if theres any differences in the sets
        if(oldIN != IN[&basic_block] || oldOUT != OUT[&basic_block]) changes = true;

      }
    }


  }
};

struct Definition{
  llvm::Instruction* instruction;
  llvm::Value* variable; //where its being written

  Definition(llvm::Instruction* instr, llvm::Value* var): instruction(instr), variable(var){}
};

struct ReachingDefs{
  std::unordered_map<llvm::BasicBlock*, std::set<Definition*>> IN;
  std::unordered_map<llvm::BasicBlock*, std::set<Definition*>> OUT;


  ReachingDefs(){}

  ~ReachingDefs(){}
 
  void runReachingDefs(Function &F, std::set<Definition*> allDefs){     
    //TO DO
    //will this run into issues if two identical expressions in the same block
    std::unordered_map<llvm::BasicBlock*, std::set<Definition*>> killSets;
    std::unordered_map<llvm::BasicBlock*, std::set<Definition*>> genSets;

    //Generate GEN sets
    for(auto &basic_block : F){
      for(auto &instruction : basic_block){
        //check if the instruction assigns a value

        //if it does, add to the gen set
        if (instruction.getOpcode() == Instruction::Store) {
          auto *SI = llvm::dyn_cast<llvm::StoreInst>(&instruction);

          for(auto it = genSets[&basic_block].begin(); it != genSets[&basic_block].end();){
            if ((*it)->variable == SI->getPointerOperand())
                it = genSets[&basic_block].erase(it);
            else
                ++it;
          }


          Definition *def = new Definition(SI, SI->getPointerOperand());
          genSets[&basic_block].insert(def);
        }
      }
    }


    //Generate KILL sets
    for(auto &basic_block : F){
      for(Definition* def  : genSets[&basic_block]){
        for(Definition* otherDef : allDefs){
          if(def == otherDef) continue; //same one, skip it
          
          //two different definitions assigning to same variable, kill all others that
          //assign to the same variable
          if(def->variable == otherDef->variable){ 
            
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
        std::set<Definition*> oldIN = IN[&basic_block];
        std::set<Definition*> oldOUT = OUT[&basic_block];

        //IN is the union of all predecessors
        for(auto i = pred_begin(&basic_block); i != pred_end(&basic_block); ++i){
          for(Definition* def : OUT[*i]){
            IN[&basic_block].insert(def);
          }
        }

        //compute difference
        std::set<Definition*> diff;
        for(Definition* def : IN[&basic_block]){
          if(killSets[&basic_block].find(def) == killSets[&basic_block].end()){
            diff.insert(def);
          }
        }

        //compute out = gen u (in - kill)
        OUT[&basic_block] = genSets[&basic_block];
        for(Definition* def : diff){
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

  bool runOnFunction(Function &F) override
  {
    for (auto &basic_block : F)
      {

      }
    return true; // Indicate this is a Transform pass
  }
}; // end of struct CSElimination
} // end of anonymous namespace

char CSElimination::ID = 0;
static RegisterPass<CSElimination> X("CSElimination", "CSElimination Pass",
                                      false /* Only looks at CFG */,
                                      true /* Tranform Pass */);

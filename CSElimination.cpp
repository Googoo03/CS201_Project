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
  std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression*>> availExprs;

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

    bool changes = true;
    while(changes){
      changes = false;
      for (auto &basic_block : F)
      {
        std::unordered_set<Expression*> newSet;

        //intersection of all predecessors
        bool firstPred = true;
        for(auto pred = pred_begin(&basic_block); pred != pred_end(&basic_block); ++pred){
          if(firstPred){
            newSet = availExprs[*pred];
            firstPred = false;
          } else {
            std::unordered_set<Expression*> tempSet;
            for(auto expr: newSet){
              if(availExprs[*pred].count(expr)){
                tempSet.insert(expr);
              }
            }
            newSet = tempSet;
          }
        }

        //remove kill set
        for(auto expr: killSets[&basic_block]){
          newSet.erase(expr);
        }

        //add gen set
        for(auto expr: genSets[&basic_block]){
          newSet.insert(expr);
        }

        //check if changed
        if(newSet != availExprs[&basic_block]){
          changes = true;
          availExprs[&basic_block] = newSet;
        }
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
  std::unordered_map<llvm::BasicBlock*, std::set<Definition*>> reachDefs;


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

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <queue>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "PRElimination"

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

bool Used(llvm::BasicBlock* node, Expression expr){
  //For a given expression, return true if the block evaluates the expression

}


struct Earliestness{

    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> IN;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> OUT;

    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> killSets;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> genSets;


    Earliestness();
    ~Earliestness();

    void runEarliestness(Function& F, std::unordered_set<Expression, ExpressionHash>& allExprs){
        
    }
};

struct DownSafety{

    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> IN;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> OUT;
  
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> Transp;
    std::unordered_map<llvm::BasicBlock*, std::unordered_set<Expression, ExpressionHash>> Used;

    DownSafety();
    ~DownSafety();

    void runDownSafety(Function& F, std::unordered_set<Expression, ExpressionHash>& allExprs){
      //generate Used set. Contains all expressions that are computed (used) in the block

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

            Used[&basic_block].emplace(&inst,inst.getOpcode(), getOperands(inst));
        }
      }

      //generate Transp set. Contains all expressions that are not killed by the block

      for (auto &basic_block : F) {
        for(auto& instruction : basic_block){
          if (auto *SI = dyn_cast<StoreInst>(&instruction)) {
              Value *storedPtr = SI->getPointerOperand();

              for (auto &expr : allExprs) {
                  bool containsLoad = false;
                  bool killed = false;
                  if(isa<LoadInst>(expr.instruction)) containsLoad = true;

                  for(int i = 0; i < expr.instruction->getNumOperands(); ++i){
                    LoadInst* load = dyn_cast<LoadInst>((expr.instruction)->getOperand(i));
                    if(load) containsLoad = true;
                  }

                  if (!containsLoad)
                      continue;

                  for(auto& op : expr.operands){
                    if(Expression::sameValue(op,storedPtr)){

                      //mark as killed
                      killed = true;
                      break;
                    }
                  }

                  if(!killed) Transp[&basic_block].insert(expr);
              }
          }
        }
      }

      //Initialize IN & OUT sets.
      for(auto& basic_block : F){
        //The exit block should have a IN of empty (i.e. all expressions are absent and evaluate to false)
        if(std::distance(succ_begin(&basic_block), succ_end(&basic_block)) > 0){
          OUT[&basic_block] = allExprs;
        }
      }

      //Actual pass
      bool changes = true;
      while(changes){
        changes = false;
        //compute the in and out sets of each block
        for(auto& basic_block : F){
          std::unordered_set<Expression,ExpressionHash> oldIN = IN[&basic_block];
          std::unordered_set<Expression,ExpressionHash> oldOUT = OUT[&basic_block];

          //OUT is the intersection of all predecessors
          if(std::distance(succ_begin(&basic_block), succ_end(&basic_block)) > 0){
            
            std::unordered_set<Expression, ExpressionHash> intersection = IN[*succ_begin(&basic_block)];

            for(auto i = succ_begin(&basic_block); i != succ_end(&basic_block); ++i){
              for (auto it = intersection.begin(); it != intersection.end(); ) {
                  if (!OUT[*i].count(*it)) {
                      it = intersection.erase(it);   // remove expressions not in this pred
                  } else {
                      ++it;
                  }
              }
            }

            OUT[&basic_block] = std::move(intersection);
          }

          //compute Transp ^ OUT
          std::unordered_set<Expression, ExpressionHash> intersection = Transp[&basic_block];
          
          for (auto it = intersection.begin(); it != intersection.end(); ) {
              if (!OUT[&basic_block].count(*it)) {
                  it = intersection.erase(it);   // remove expressions not in this pred
              } else {
                  ++it;
              }
          }

          //compute in = used u (transp ^ out)
          IN[&basic_block] = Used[&basic_block];
          for(Expression expr : intersection){
            IN[&basic_block].insert(expr);
          }

          

          //set changes based on if theres any differences in the sets
          if(oldIN != IN[&basic_block] || oldOUT != OUT[&basic_block]){
            errs() << "Down Safety CHANGED **************************\n"; 
            changes = true;
          }

        }
      }

    }
};

struct PRElimination : public FunctionPass
{
  static char ID;
  PRElimination() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override
  {
    errs() << "PRElimination: ";
    errs() << F.getName() << "\n";

    return true;
  }
}; // end of struct PRElimination
} // end of anonymous namespace

char PRElimination::ID = 0;
static RegisterPass<PRElimination> X("PRElimination", "PRElimination Pass",
                                      false /* Only looks at CFG */,
                                      true /* Analysis Pass */);

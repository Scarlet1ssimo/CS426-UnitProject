// Usage: opt -load-pass-plugin=libUnitProject.so -passes="unit-licm"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>

#include "UnitLICM.h"
#include "UnitLoopInfo.h"

#define DEBUG_TYPE UnitLICM
// Define any statistics here

using namespace llvm;
using namespace cs426;
using namespace std;

void getTraverseOrder(LoopNode *outmostLoop, vector<LoopNode *> &order) {
  for (auto L : outmostLoop->Children)
    getTraverseOrder(L, order);
  order.push_back(outmostLoop);
}
bool ifDominateAll(DominatorTree &DT, BasicBlock *use, BasicBlocks exits) {
  for (auto E : exits) {
    if (!DT.dominates(use, E))
      return false;
  }
  return true;
}
static bool isForUnitProject(Instruction &I) {
  // [x] unary, binary, and bitwise operations
  // [x] bitcasts,
  if (I.isBinaryOp() || I.isUnaryOp() || I.isBitwiseLogicOp() || I.isCast())
    return true;
  switch (I.getOpcode()) {
  // case Instruction::BitCast:
  // [x] icmp and fcmp instructions, select instructions
  case Instruction::ICmp:
  case Instruction::FCmp:
  case Instruction::Select:
  // [x] getelementptr instructions
  case Instruction::GetElementPtr:
  // [x] store load instructions
  case Instruction::Store:
  case Instruction::Load:
    return true;
  }
  return false;
}
void getAllStore(LoopNode *L, vector<StoreInst *> &Stores) {
  for (auto SL : L->Children)
    getAllStore(SL, Stores);
  for (auto B : L->BlockOfLoop) {
    for (auto &I : *B) {
      if (I.mayWriteToMemory()) {
        auto S = dyn_cast<StoreInst>(&I);
        assert(S);
        Stores.push_back(S);
      }
    }
  }
}

/// Main function for running the LICM optimization
PreservedAnalyses UnitLICM::run(Function &F, FunctionAnalysisManager &FAM) {
  dbgs() << "UnitLICM running on " << F.getName() << "\n";
  // Acquires the UnitLoopInfo object constructed by your Loop Identification
  // (LoopAnalysis) pass
  UnitLoopInfo &Loops = FAM.getResult<UnitLoopAnalysis>(F);
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  AAResults &AA = FAM.getResult<AAManager>(F);

  // Perform the optimization
  // Loops.debug();
  for (auto OL : Loops.OutmostLoops) {
    OL->debug("Outmost");
    vector<LoopNode *> SubLoops;
    getTraverseOrder(OL, SubLoops);
    dbgs() << SubLoops.size() << "\n";
    for (auto L : SubLoops) {
      // L->debug("Subloop");
      vector<StoreInst *> Stores;
      getAllStore(L, Stores);

      for (bool NewMark = true; NewMark;) {
        NewMark = false;
        map<Instruction *, bool> IsInvariantBlock;
        vector<Instruction *> MovingInstr;
        for (auto B : L->BlockOfLoop) {
          for (auto &I : *B) {
            bool isInvariant = true; // I is Invariant
            int reason = [&] {
              if (!isForUnitProject(I))
                return 2;
              auto LL = dyn_cast<LoadInst>(&I);
              if (LL && ![&] {
                    // is safe for hoist
                    for (auto S : Stores) {
                      if (AA.alias(S->getPointerOperand(),
                                   LL->getPointerOperand()) !=
                          AliasResult::NoAlias) {
                        dbgs() << "May Alias " << *S << " With" << *LL << "\n";
                        return false;
                      }
                    }
                    return true;
                  }())
                return 4;
              if (ifDominateAll(DT, B, L->Exits))
                return -1;
              // [x] isSafeToSpeculativelyExecute
              if (!isSafeToSpeculativelyExecute(&I))
                return 3;
              // [x] isnoalias
              return 0;
            }();

            if (reason <= 0) { // check instruction validity
              for (auto &U : I.operands()) {
                // U is operand of I
                auto V = U.get();
                auto Inst = dyn_cast<Instruction>(V);
                if (Inst) {
                  // Inst is def of operand U
                  auto InstBlock = Inst->getParent();
                  if (Loops.getLoopFor(InstBlock)->isInnerLoopOf(L))
                    if (!IsInvariantBlock[Inst])
                      isInvariant = false;
                }
              }
            } else {
              dbgs() << "Not Invariant Reason " << reason << I << "\n";
              isInvariant = false;
            }

            if (isInvariant) {
              // dbgs() << "Invariant " << I << "\n";
              IsInvariantBlock[&I] = true;
              MovingInstr.push_back(&I);
            }
          }
        };

        for (auto I : MovingInstr) {
          if (auto PreHeader = L->getPreHeader()) {
            auto InsertPtr = PreHeader->getTerminator();
            dbgs() << "Invariant " << *I << " Move before " << *InsertPtr
                   << "\n";
            I->moveBefore(InsertPtr);
            NewMark = true;
          }
        }
      }
    }
  }

  // Set proper preserved analyses

  PreservedAnalyses PA;
  return PA;
  // PA.preserve<DominatorTreeAnalysis>();

  // return PreservedAnalyses::all();
}

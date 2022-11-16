#include "llvm/IR/Dominators.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

#include "UnitLoopInfo.h"

using namespace llvm;
using namespace cs426;

/// Main function for running the Loop Identification analysis. This function
/// returns information about the loops in the function via the UnitLoopInfo
/// object

UnitLoopInfo UnitLoopAnalysis::run(Function &F, FunctionAnalysisManager &FAM) {
  dbgs() << "UnitLoopAnalysis running on " << F.getName() << "\n";
  // Acquires the Dominator Tree constructed by LLVM for this function. You may
  // find this useful in identifying the natural loops
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);

  UnitLoopInfo Loops;
  // Fill in appropriate information
  auto Rt = DT.getRootNode();
  for (auto Node : post_order(Rt)) {
    auto D = Node->getBlock(); // header
    BasicBlocks BackEdges;
    for (auto N : predecessors(D)) {
      if (DT.dominates(D, N)) {
        // dbgs() << "potential back edges:" << getSimpleNodeLabel(N) << "->"
        //        << getSimpleNodeLabel(D) << "\n";
        BackEdges.push_back(N);
      }
    }
    if (!BackEdges.empty())
      Loops.addLoopInfo(D, BackEdges, DT);
  }
  Loops.discoverOutmostLoops();
  return Loops;
}

void UnitLoopInfo::addLoopInfo(BasicBlock *Header, BasicBlocks &BackEdges,
                               DominatorTree &DT) {
  assert(LoopMap.find(Header) == LoopMap.end());
  auto CurLoop = new LoopNode(Header, this);
  AllLoops.push_back(CurLoop);
  queue<BasicBlock *> Q;
  for (auto B : BackEdges)
    Q.push(B);
  // dbgs() << "Header:" << getSimpleNodeLabel(Header) << "\n";

  while (!Q.empty()) {
    auto u = Q.front();
    Q.pop();
    // dbgs() << getSimpleNodeLabel(u) << "\n";
    assert(DT.dominates(Header, u));
    auto L = getLoopFor(u);
    if (L) {
      L = LoopNode::getFirstParent(L);
      if (L == CurLoop) { // visited
        continue;
      }
      CurLoop->Children.push_back(L);
      L->setParent(CurLoop);
      for (auto tmp : predecessors(L->Header)) { // safe?
        if (getLoopFor(tmp) != CurLoop)
          Q.push(tmp);
      }
    } else {
      // Undiscovered node, add to loop
      CurLoop->BlockOfLoop.push_back(u);
      LoopMap[u] = CurLoop;
      if (u == Header)
        continue;
      for (auto tmp : predecessors(u)) {
        if (getLoopFor(tmp) != CurLoop)
          Q.push(tmp);
      }
    }
  }
  reverse(CurLoop->BlockOfLoop.begin(), CurLoop->BlockOfLoop.end());
  reverse(CurLoop->Children.begin(), CurLoop->Children.end());
  for (auto B : CurLoop->BlockOfLoop) {
    for (auto C : successors(B)) {
      auto L = getLoopFor(C);
      if (!L || LoopNode::getFirstParent(L) != CurLoop) { // Exits
        CurLoop->Exits.push_back(B);
      }
    }
  }
  for (auto C : predecessors(Header)) {
    auto L = getLoopFor(C);
    if (!L || LoopNode::getFirstParent(L) != CurLoop) { // Enters
      CurLoop->Enters.push_back(C);
    }
  }

  // int cnt = 0;
  // BasicBlock *PreHeader = nullptr;
  // for (auto p : predecessors(Header)) {
  //   if (!DT.dominates(Header, p)) {
  //     PreHeader = p;
  //     cnt++;
  //   }
  // }
  // CurLoop->PreHeader = cnt == 1 ? PreHeader : nullptr;
}

AnalysisKey UnitLoopAnalysis::Key;

BasicBlock *LoopNode::getPreHeader() {
  if (PreHeader)
    return PreHeader;
  if (Enters.size() == 1)
    return PreHeader = Enters[0];

  // PreHeader = Header;
  PreHeader =
      BasicBlock::Create(Header->getContext(), "", Header->getParent(), Header);
  for (BasicBlock *Pred : Enters) {
    auto I = Pred->getTerminator();
    I->replaceSuccessorWith(Header, PreHeader);
    Header->replacePhiUsesWith(Pred, PreHeader);
  }
  dbgs() << "Made Preheader " << getSimpleNodeLabel(PreHeader) << " for header "
         << getSimpleNodeLabel(Header) << "\n";
  BranchInst *BI = BranchInst::Create(Header, PreHeader);
  LoopInfo->registerPreHeader(this, PreHeader);

  // PreHeader->print(dbgs());
  // Header->print(dbgs());
  return PreHeader;
}
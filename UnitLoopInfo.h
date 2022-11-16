#ifndef INCLUDE_UNIT_LOOP_INFO_H
#define INCLUDE_UNIT_LOOP_INFO_H
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PassManager.h"

#include <algorithm>
#include <map>
#include <queue>
#include <vector>

using namespace llvm;

static std::string getSimpleNodeLabel(const BasicBlock *Node) {
  if (!Node->getName().empty())
    return Node->getName().str();

  std::string Str;
  raw_string_ostream OS(Str);

  Node->printAsOperand(OS, false);
  return OS.str();
}

using namespace std;
using BasicBlocks = vector<BasicBlock *>;

namespace cs426 {
/// An object holding information about the (natural) loops in an LLVM
/// function. At minimum this will need to identify the loops, may hold
/// additional information you find useful for your LICM pass
// template <>
// struct GraphTraits<LoopNode *>
//     : public DomTreeGraphTraitsBase<DomTreeNode, DomTreeNode::const_iterator>
//     {
// };
class UnitLoopInfo;

struct LoopNode {
  vector<LoopNode *> Children;
  LoopNode *Parent;
  BasicBlocks Exits;
  BasicBlocks Enters;
  BasicBlocks BlockOfLoop; // Pre Order
  BasicBlock *Header;
  BasicBlock *PreHeader;
  UnitLoopInfo *LoopInfo;
  LoopNode(BasicBlock *Header, UnitLoopInfo *LoopInfo)
      : Header(Header), Parent(nullptr), PreHeader(nullptr),
        LoopInfo(LoopInfo) {}
  bool isInnerLoopOf(LoopNode *L) {
    for (auto p = this; p != nullptr; p = p->Parent) {
      if (p == L)
        return true;
    }
    return false;
  }
  void setParent(LoopNode *L) { Parent = L; }
  static auto getFirstParent(LoopNode *L) {
    while (L->Parent)
      L = L->Parent;
    return L;
  }
  void debug(string str = "") {
    dbgs() << "LoopNode:" << this << "for " << str << "\n";
    dbgs() << "Header" << getSimpleNodeLabel(Header) << "\n";
    dbgs() << "Children"
           << "\n";
    for (auto uu : Children)
      dbgs() << uu << "\n";
    dbgs() << "BlockOfLoop"
           << "\n";
    for (auto uu : BlockOfLoop)
      dbgs() << getSimpleNodeLabel(uu) << "\n";
    dbgs() << "Exits"
           << "\n";
    for (auto uu : Exits)
      dbgs() << getSimpleNodeLabel(uu) << "\n";
    dbgs() << "Parent" << Parent << ": "
           << (Parent ? getSimpleNodeLabel(Parent->Header) : "nullptr") << "\n";
  }
  BasicBlock *getPreHeader();
};
class UnitLoopInfo {
  // Define this class to provide the information you need in LICM
  // iterable all Loops (Loops tree)
  // BBs in a Loop
  std::map<BasicBlock *, LoopNode *> LoopMap;

public:
  // UnitLoopInfo(){}
  std::vector<LoopNode *> OutmostLoops;
  std::vector<LoopNode *> AllLoops;
  LoopNode *getLoopFor(BasicBlock *B) {
    return LoopMap.find(B) != LoopMap.end() ? LoopMap[B] : nullptr;
  }

  void addLoopInfo(BasicBlock *Header, BasicBlocks &BackEdges,
                   DominatorTree &DT);
  void discoverOutmostLoops() {
    for (auto u : AllLoops)
      if (u->Parent == nullptr)
        OutmostLoops.push_back(u);
  }
  ~UnitLoopInfo() {}
  void debug(string str = "") {
    dbgs() << "UnitLoopInfo:" << this << "for " << str << "\n";
    for (auto u : AllLoops) {
      u->debug();
    }
  }
  void registerPreHeader(LoopNode *L, BasicBlock *PreHeader) {
    if (L->Parent) {
      LoopMap[PreHeader] = L->Parent;
      L->Parent->BlockOfLoop.push_back(PreHeader);
    }
  }
};

/// Loop Identification Analysis Pass. Produces a UnitLoopInfo object which
/// should contain any information about the loops in the function which is
/// needed for your implementation of LICM
class UnitLoopAnalysis : public AnalysisInfoMixin<UnitLoopAnalysis> {
  friend AnalysisInfoMixin<UnitLoopAnalysis>;
  static AnalysisKey Key;

public:
  typedef UnitLoopInfo Result;

  UnitLoopInfo run(Function &F, FunctionAnalysisManager &AM);
};
} // namespace cs426
#endif // INCLUDE_UNIT_LOOP_INFO_H

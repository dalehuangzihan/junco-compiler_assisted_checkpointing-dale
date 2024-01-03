/**
 * Does DFS on BB CFG for each Function in Module.
 * For each BB, finds the "modified values" that are stored within the BB via store instructions.
 * Each predecessor BB propagates its "modified values" to all its successor BBs.
 * Modified Values are stored in a map with key as BB and value as set of modified values.
 *
 * To Run:
 * $ opt -enable-new-pm=0 -load /path/to/build/lib/libSubroutineInjection.so `\`
 *   -module-transformation-pass -S /path/to/input/IR.ll -o /path/to/output/IR.ll
 */

#include "dale_passes/SubroutineInjection.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/Support/Debug.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Type.h"
#include "llvm/Analysis/LoopInfo.h"

#include "llvm/IR/Dominators.h" // test
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/IR/Instruction.h"

#include "json/JsonHelper.h"

#include <asm-generic/errno.h>
#include <cstddef>
#include <exception>
#include <iostream>
#include <sys/stat.h>
#include <fstream>
#include <cmath>

#define DEBUG_TYPE "module-transformation-pass"

#define SEGMENT_PTR_NAME "ckpt_mem"

#define SAVE_ONLY "save"
#define RESTORE_ONLY "restore"
#define SAVE_RESTORE "save_restore"

using namespace llvm;

static cl::opt<std::string> InjectionOption("inject", cl::desc("Specify subroutine injection option"), cl::value_desc("option"));

static cl::opt<bool> TrackIndexOption("trackingIndex", cl::desc("activate tracking indexes optimization"), cl::value_desc("optimization"));

char SubroutineInjection::ID = 0;

// This is the core interface for pass plugins. It guarantees that 'opt' will
// recognize LegacyHelloWorld when added to the pass pipeline on the command
// line, i.e.  via '--legacy-hello-world'
static RegisterPass<SubroutineInjection>
    X("subroutine-injection", "Subroutine Injection",
      false, // This pass does modify the CFG => false
      false  // This pass is not a pure analysis pass => false
    );

namespace llvm
{
  ModulePass *createSubroutineInjection() { return new SubroutineInjection(); }
}

///////////////////////////////////////////////////////////////////////////////
// Public API
///////////////////////////////////////////////////////////////////////////////

SubroutineInjection::SubroutineInjection(void) : ModulePass(ID) {}

void SubroutineInjection::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<DominatorTreeWrapperPass>();
}

bool SubroutineInjection::runOnModule(Module &M)
{
  std::cout << "Module Transformation Pass printout" << std::endl;

  // set default InjectionOption as SAVE_RESTORE
  if (InjectionOption != SAVE_ONLY && InjectionOption != RESTORE_ONLY && InjectionOption != SAVE_RESTORE)
  {
    InjectionOption = SAVE_RESTORE;
  }

  // load live values analysis results.
  FuncBBLiveValsByName = JsonHelper::getLiveValuesResultsFromJson(LIVENESS_JSON_PATH);
  JsonHelper::printJsonMap(FuncBBLiveValsByName);
  std::cout << "===========\n";

  // load Tracked values analysis results.
  FuncBBTrackedValsByName = JsonHelper::getTrackedValuesResultsFromJson(TRACKED_VALS_JSON_PATH);
  JsonHelper::printJsonMap(FuncBBTrackedValsByName);
  std::cout << "===========\n";

  FuncValuePtrs = getFuncValuePtrsMap(M, FuncBBTrackedValsByName);
  printFuncValuePtrsMap(FuncValuePtrs, M);

  // re-build tracked values pointer map
  std::cout << "#TRACKED VALUES ======\n";
  LiveValues::TrackedValuesResult funcBBTrackedValsMap = JsonHelper::getFuncBBTrackedValsMap(FuncValuePtrs, FuncBBTrackedValsByName, M);
  // printTrackedValues(OS, funcBBTrackedValsMap);

  // re-build liveness analysis results pointer map
  std::cout << "#LIVE VALUES ======\n";
  LiveValues::FullLiveValsInfo fullLiveValsInfo = JsonHelper::getFuncBBLiveValsInfo(FuncValuePtrs, FuncBBLiveValsByName, M);
  LiveValues::LivenessResult funcBBLiveValsMap = fullLiveValsInfo.first;
  LiveValues::FuncVariableDefMap funcVariableDefMap = fullLiveValsInfo.second;

  for (auto fIter : funcVariableDefMap)
  {
    /** TODO: is for debugging */
    Function *F = fIter.first;
    LiveValues::VariableDefMap sizeMap = fIter.second;
    std::cout << "INI SIZE ANALYSIS RESULTS FOR FUNC " << JsonHelper::getOpName(F, &M) << " :" << std::endl;
    for (auto vIter : sizeMap)
    {
      Value *val = const_cast<Value *>(vIter.first);
      int size = vIter.second;
      std::cout << "  " << JsonHelper::getOpName(val, &M) << "(" << val << ") : " << size << " bytes" << std::endl;
    }
  }

  bool isModified = injectSubroutines(M, funcBBTrackedValsMap, funcBBLiveValsMap, funcVariableDefMap);

  printCheckPointBBs(funcBBTrackedValsMap, M);

  return isModified;
}

void SubroutineInjection::print(raw_ostream &O, const Function *F) const
{
  /** TODO: implement me! */
  return;
}

void SubroutineInjection::printTrackedValues(raw_ostream &O, const LiveValues::TrackedValuesResult &LVResult) const
{
  LiveValues::TrackedValuesResult::const_iterator funcIt;
  LiveValues::BBTrackedVals::const_iterator bbIt;
  std::set<const Value *>::const_iterator valIt;

  O << "Results from LiveValues tracked-value analysis\n";

  for (funcIt = LVResult.cbegin(); funcIt != LVResult.cend(); funcIt++)
  {
    const Function *F = funcIt->first;
    const LiveValues::BBTrackedVals *bbTrackedVals = &funcIt->second;
    const Module *M = F->getParent();

    O << "For function " << F->getName() << ":\n";

    for (bbIt = bbTrackedVals->cbegin(); bbIt != bbTrackedVals->cend(); bbIt++)
    {
      const BasicBlock *BB = bbIt->first;
      const std::set<const Value *> &trackedVals = bbIt->second;

      O << "Results for BB ";
      BB->printAsOperand(O, false, M);
      O << ":";

      O << "\n  Tracked:\n    ";
      for (valIt = trackedVals.cbegin(); valIt != trackedVals.cend(); valIt++)
      {
        (*valIt)->printAsOperand(O, false, M);
        O << " ";
      }

      O << "\n";
    }
  }
}

///////////////////////////////////////////////////////////////////////////////
// Private API
///////////////////////////////////////////////////////////////////////////////

bool SubroutineInjection::isEntryBlock(const BasicBlock *BB) const
{
  const Function *F = BB->getParent();
  assert(F && "Block must have a parent function to use this API");
  return BB == &F->getEntryBlock();
}

/// Set every incoming value(s) for block \p BB to \p V.
void SubroutineInjection::setIncomingValueForBlock(PHINode *phi, const BasicBlock *BB, Value *V)
{
  assert(BB && "PHI node got a null basic block!");
  bool Found = false;
  for (unsigned Op = 0, NumOps = phi->getNumOperands(); Op != NumOps; ++Op)
    if (phi->getIncomingBlock(Op) == BB)
    {
      Found = true;
      phi->setIncomingValue(Op, V);
    }
  (void)Found;
  assert(Found && "Invalid basic block argument to set!");
}

bool SubroutineInjection::hasNPredecessorsOrMore(const BasicBlock *BB, unsigned N)
{
  return hasNItemsOrMore(pred_begin(BB), pred_end(BB), N);
}

bool SubroutineInjection::injectSubroutines(
    Module &M,
    const LiveValues::TrackedValuesResult &funcBBTrackedValsMap,
    const LiveValues::LivenessResult &funcBBLiveValsMap,
    const LiveValues::FuncVariableDefMap &funcVariableDefMap)
{
  // init map to store size #bytes required for each checkpoint in each func
  JsonHelper::FuncCkptSizeMap funcCkptSizeMap;
  // init the id number of the first checkpoint in the module
  int moduleCkptIDCounter = 1; // start with 1; id=0 means no ckpt has been inserted

  Function *func_mem_cpy_index_f = M.getFunction("mem_cpy_index_f");

  // Function* func_stack_push = M.getFunction("stack_push");

  // Function* func_mem_cpy_custom_f = M.getFunction("mem_cpy_custom_f");
  Function *func_mem_cpy_wrapper_f = M.getFunction("cpy_wrapper_f");

  if (func_mem_cpy_index_f == NULL)
  {
    std::cout << "External mem_cpy_index function CANNOT be found. Disable index tracking optimization." << std::endl;
    TrackIndexOption = false;
  }

  if (func_mem_cpy_wrapper_f == NULL)
  {
    std::cout << "External mem_cpy_wrapper function CANNOT be found. Disable index tracking optimization." << std::endl;
  }

  if (TrackIndexOption)
  {
#ifndef LLVM14_VER
    func_mem_cpy_index_f->addAttribute(AttributeList::FunctionIndex, Attribute::NoInline);
#else
    func_mem_cpy_index_f->addFnAttr(Attribute::NoInline);
#endif
  }

  if (func_mem_cpy_wrapper_f != NULL)
    func_mem_cpy_wrapper_f->addAttribute(AttributeList::FunctionIndex, Attribute::NoInline);

  bool isModified = false;
  const DataLayout &DL = M.getDataLayout();
  for (auto &F : M.getFunctionList())
  {
    // init map to store size #bytes required for each checkpoint
    JsonHelper::CkptSizeMap ckptSizeMap;

    // Check function linkage
    // We do not analyze external functions
    if (F.getLinkage() == F.LinkOnceODRLinkage)
      continue;

    std::string funcName = JsonHelper::getOpName(&F, &M);
    std::cout << "\nFunction " << funcName << " ==== \n";
    if (!(funcBBTrackedValsMap.count(&F) && funcBBLiveValsMap.count(&F) && funcVariableDefMap.count(&F)))
    {
      std::cout << "WARNING: No BB liveness data for '" << funcName << "'\n";
      continue;
    }

    LiveValues::BBTrackedVals bbTrackedVals = funcBBTrackedValsMap.at(&F);
    LiveValues::VariableDefMap liveValDefMap = funcVariableDefMap.at(&F);

    // re-calculate variableDefMap for func (could include alloca-ed vals that are not part of live-in/out sets)
    LiveValues::VariableDefMap valDefMap;
    LiveValues::getVariablesDefinition(&F, &valDefMap);
    valDefMap.insert(liveValDefMap.begin(), liveValDefMap.end());
    /** TODO: remove std::cout after testing */
    for (auto iter : valDefMap)
    {
      std::cout << "$$" << JsonHelper::getOpName(iter.first, &M) << ":" << iter.second << std::endl;
    }

    // get vars for instruction building
    LLVMContext &context = F.getContext();
    IRBuilder<> builder(context);

    // get function parameters
    std::set<Value *> funcParams = getFuncParams(&F);
    std::set<Value *> constFuncParams = LiveValues::getConstFuncParams(&F);
    // testing:
    std::cout << ">>> func '" << JsonHelper::getOpName(&F, &M) << "': " << std::endl;
    for (auto iter : constFuncParams)
    {
      std::cout << ">>> " << JsonHelper::getOpName(iter, &M) << std::endl;
    }

    // get Value* to ckpt_mem memory segment pointer
    StringRef segmentName = SEGMENT_PTR_NAME;
    Value *ckptMemSegment = getSelectedFuncParam(funcParams, segmentName, &M);
    if (!ckptMemSegment)
    {
      std::cout << "WARNING: Could not get pointer to memory segment of name '" << segmentName.str() << "'" << std::endl;
      continue;
    }

    // get memory segment contained type
    Type *memSegPtrType = ckptMemSegment->getType();
    Type *ckptMemSegContainedType = ckptMemSegment->getType()->getContainedType(0); // %ckpt_mem should be <primitive>** type.
    int ckptMemSegContainedTypeSize = DL.getTypeAllocSizeInBits(ckptMemSegContainedType) / 8;
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    ckptMemSegContainedType->print(rso);
    std::cout << "MEM SEG CONTAINED TYPE = " << rso.str() << "(" << ckptMemSegContainedTypeSize << ") bytes;" << std::endl;
    ;

    // get entryBB (could be %entry or %entry.upper, depending on whether entryBB has > 1 successors)
    BasicBlock *entryBB = &*(F.begin());
    std::cout << "ENTRY_BB_UPPER=" << JsonHelper::getOpName(entryBB, &M) << "\n";
    if (getBBSuccessors(entryBB).size() < 1)
    {
      std::cout << "WARNING: Function '" << JsonHelper::getOpName(&F, &M) << "' only comprises 1 basic block. Ignore Function." << std::endl;
      continue;
    }

    bool hasInjectedSubroutinesForFunc = false;

    /*
    = 0: get candidate checkpoint BBs
    ============================================================================= */
    LiveValues::BBTrackedVals filteredBBTrackedVals = getBBsWithOneSuccessor(bbTrackedVals);
    std::set<Value *> ignoredVals;
    ignoredVals.insert(ckptMemSegment);
    ignoredVals.insert(constFuncParams.begin(), constFuncParams.end());
    filteredBBTrackedVals = removeSelectedTrackedVals(filteredBBTrackedVals, ignoredVals);
    filteredBBTrackedVals = removeMatchedNestedPtrVals(filteredBBTrackedVals, segmentName);
    filteredBBTrackedVals = removeBBsWithNoTrackedVals(filteredBBTrackedVals);
    CheckpointBBMap bbCheckpoints = chooseBBWithCheckpointDirective(filteredBBTrackedVals, &F);
    // original tracked vals as key, updated tracked vals as value:
    CheckpointBBOldNewValsMap bbCheckpointsOldNewVals = initBBCheckpointsOldNewVals(bbCheckpoints);

    // testing:
    std::cout << "\n\n===========================" << std::endl;
    std::cout << "\n\nFiltered " << JsonHelper::getOpName(&F, &M) << " tracked vals:" << std::endl;
    for (auto iter : bbCheckpoints)
    {
      std::cout << JsonHelper::getOpName(iter.first, &M) << std::endl;
      for (auto iterr : iter.second)
      {
        std::cout << "  " << JsonHelper::getOpName(iterr, &M) << std::endl;
      }
    }
    std::cout << "===========================\n\n"
              << std::endl;

    if (bbCheckpoints.size() == 0)
    {
      // Could not find BBs with checkpoint directive
      std::cout << "WARNING: Could not find any valid BBs with checkpoint directive in function '" << funcName << std::endl;
      continue;
    }
    int currMinValsCount = bbCheckpoints.begin()->second.size();
    std::cout << "#currNumOfTrackedVals=" << currMinValsCount << "\n";

    /*
    = 1: get pointers to Entry BB and checkpoint BBs
    ============================================================================= */
    std::cout << "Checkpoint BBs:\n";
    std::set<BasicBlock *> checkpointBBPtrSet = getCkptBBsInFunc(&F, bbCheckpoints);

    /*
    = 2. Add block on exit edge of entry.upper block (pre-split)
    ============================================================================= */
    BasicBlock *restoreControllerBB = nullptr;
    BasicBlock *restoreControllerSuccessor = nullptr;
    if (InjectionOption == RESTORE_ONLY || InjectionOption == SAVE_RESTORE)
    {
      restoreControllerSuccessor = *succ_begin(entryBB);
      ;
      std::string restoreControllerBBName = funcName.erase(0, 1) + ".restoreControllerBB";
      restoreControllerBB = splitEdgeWrapper(entryBB, restoreControllerSuccessor, restoreControllerBBName, M);
      if (restoreControllerBB)
      {
        isModified = true;
        restoreControllerSuccessor = restoreControllerBB->getSingleSuccessor();
        std::cout << "successor of restoreControllerBB=" << JsonHelper::getOpName(restoreControllerSuccessor, &M) << "\n";
      }
      else
      {
        // Split-edge fails for adding BB after function entry block => skip this function
        std::cout << "WARNING: Split-edge for restoreControllerBB failed for function '" << funcName << "'" << std::endl;
        continue;
      }
    }

    /*
    = 3: Add subroutines for each checkpoint BB, one checkpoint at a time:
    ============================================================================= */
    // store subroutine BBs for each checkpoint
    std::map<BasicBlock *, CheckpointTopo> checkpointBBTopoMap;

    // store live-out data for all saveBBs, restoreBBs and junctionBBs in current function.
    std::map<BasicBlock *, std::set<const Value *>> funcSaveBBsLiveOutMap;
    std::map<BasicBlock *, std::set<const Value *>> funcRestoreBBsLiveOutMap;
    std::map<BasicBlock *, std::set<const Value *>> funcJunctionBBsLiveOutMap;

    // store map<junctionBB, map<trackedVal, phi>>
    std::map<BasicBlock *, std::map<Value *, PHINode *>> funcJunctionBBPhiValsMap;
    // store all the versions of tracked vals ever used during propagation
    std::map<const Value *, std::set<const Value *>> allTrackedValVersions = initAllTrackedValVersions(bbCheckpoints);

    for (auto bbIter : checkpointBBPtrSet)
    {
      int ckptSizeBytes = 0;
      BasicBlock *checkpointBB = &(*bbIter);
      std::string checkpointBBName = JsonHelper::getOpName(checkpointBB, &M).erase(0, 1);
      std::vector<BasicBlock *> checkpointBBSuccessorsList = getBBSuccessors(checkpointBB);

      /*
      ++ 3.1: Add saveBB on exit edge of checkpointed block
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      for (auto succIter : checkpointBBSuccessorsList)
      {
        BasicBlock *saveBB = nullptr;
        BasicBlock *successorBB = &*succIter;
        if (InjectionOption == SAVE_ONLY || InjectionOption == SAVE_RESTORE)
        {
          // Insert the new saveBB into the edge between thisBB and a successorBB:
          saveBB = splitEdgeWrapper(checkpointBB, successorBB, checkpointBBName + ".saveBB", M);
          if (saveBB)
          {
            isModified = true;
          }
          else
          {
            continue;
          }
        }

        /*
        ++ 3.2: For each successful saveBB, add restoreBBs and junctionBBs
        +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
        std::string checkpointBBName = JsonHelper::getOpName(checkpointBB, &M).erase(0, 1);

        BasicBlock *junctionBB = nullptr;
        BasicBlock *restoreBB = nullptr;
        BasicBlock *resumeBB = successorBB; // resume at successor of checkpointBB
        if (InjectionOption == RESTORE_ONLY || InjectionOption == SAVE_RESTORE)
        {
          // create mediator BB as junction to combine output of saveBB and restoreBB
          if (InjectionOption == SAVE_RESTORE)
          {
            junctionBB = splitEdgeWrapper(saveBB, resumeBB, checkpointBBName + ".junctionBB", M);
          }
          else
          {
            junctionBB = splitEdgeWrapper(checkpointBB, resumeBB, checkpointBBName + ".junctionBB", M);
          }

          if (junctionBB)
          {
            // create restoreBB for this saveBB
            restoreBB = BasicBlock::Create(context, checkpointBBName + ".restoreBB", &F, nullptr);
            // have successfully inserted all components (BBs) of subroutine
            BranchInst::Create(junctionBB, restoreBB);
          }
          else
          {
            // failed to inject mediator BB => skip this checkpoint
            /** TODO: remove saveBB for this checkpoint from CFG */
            continue;
          }
        }

        CheckpointTopo checkpointTopo = {
            .checkpointBB = checkpointBB,
            .saveBB = saveBB,
            .restoreBB = restoreBB,
            .junctionBB = junctionBB,
            .resumeBB = resumeBB};
        checkpointBBTopoMap.emplace(checkpointBB, checkpointTopo);

        /*
        ++ 3.3: Populate saveBB and restoreBB with load and store instructions.
        +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */

        if (InjectionOption == RESTORE_ONLY)
        {
          if (instScopeExit != NULL)
          {
            instScopeExit->eraseFromParent();
          }
          if (instScopeEntry != NULL)
          {
            instScopeEntry->eraseFromParent();
          }
        }

        std::map<const Value *, const Value *> oldNewTrackedVals = bbCheckpointsOldNewVals.at(checkpointBB);
        auto oldNewTrackedValsSetsPair = getOldNewTrackedValsSets(oldNewTrackedVals);
        std::set<const Value *> originalTrackedVals = oldNewTrackedValsSetsPair.first;
        std::set<const Value *> trackedVals = oldNewTrackedValsSetsPair.second;

        // sort tracked vals set by val name for consistent access later
        auto cmp = [&](const Value *a, const Value *b)
        {
          std::string aName = JsonHelper::getOpName(a, &M).erase(0,1);
          std::string bName = JsonHelper::getOpName(b, &M).erase(0,1);
          return (aName.compare(bName)<0); };
        std::set<const Value *, decltype(cmp)> trackedValsOrdered(cmp);

        for (auto iter : trackedVals)
        {
          Value *trackedVal = const_cast<Value *>(&*iter);
          trackedValsOrdered.insert(trackedVal);
        }

        if (TrackIndexOption)
        {
          allocateindexStacks(trackedVals, oldNewTrackedVals, allTrackedValVersions, valDefMap, liveValDefMap, ckptMemSegment, F, M);
          insertIndexTracking(F);
        }

        std::set<const Value *> saveBBLiveOutSet;
        std::set<const Value *> restoreBBLiveOutSet;
        std::set<const Value *> junctionBBLiveOutSet;

        // stores map<trackedVal, phi> pairings for current junctionBB
        std::map<Value *, PHINode *> trackedValPhiValMap;

        int valMemSegIndex = VALUES_START; // start index of "slots" for values in memory segment
        for (auto iter : trackedValsOrdered)
        {
          printf("$$ valMemSegIndex = %d\n", valMemSegIndex);
          /*
          --- 3.3.2: Set up vars used for instruction creation
          ----------------------------------------------------------------------------- */
          /** TODO: verify safety of cast to non-const!! this is dangerous*/
          Value *trackedVal = const_cast<Value *>(&*iter); // is the current version of tracked val after previous propagations
          Value *originalTrackedVal = const_cast<Value *>(findKeyByValueInMap(&*iter, oldNewTrackedVals));
          std::string valName = JsonHelper::getOpName(trackedVal, &M).erase(0, 1);
          Type *valRawType = trackedVal->getType();
          bool isPointer = valRawType->isPointerTy();
          Type *containedType = isPointer ? valRawType->getContainedType(0) : valRawType;
          bool isPointerPointer = isPointer && containedType->isPointerTy();

          // init store location (index) in memory segment:
          Value *indexList[1] = {ConstantInt::get(Type::getInt32Ty(context), valMemSegIndex)};
          // init valSize and numOfArrSlotsUsed for case where Value has a "primitive" type
          int valSizeBytes = liveValDefMap.at(originalTrackedVal);
          int numOfArrSlotsUsed = 1;
          if (isPointer)
          {
            if (containedType->isArrayTy())
            {
              // array is alloca-ed from within the fucnction
              numOfArrSlotsUsed = ceil((float)valSizeBytes / (float)ckptMemSegContainedTypeSize);
            }
            else
            {
              // array is allocated outside the function
              // find value that this trackedVal points to
              std::set<const Value *> valVersions = allTrackedValVersions.at(originalTrackedVal);
              Value *trackedValDeref = getDerefValFromPointer(originalTrackedVal, valVersions, &F);
              // std::cout<<"TRACKED_VAL_DEREF="<<JsonHelper::getOpName(trackedValDeref, &M)<<"("<<trackedValDeref<<")"<<std::endl;
              if (trackedValDeref != nullptr)
              {
                if (valDefMap.count(trackedValDeref))
                {
                  // get number of ckpt_mem array slots used to store this element:
                  valSizeBytes = valDefMap.at(trackedValDeref);
                  numOfArrSlotsUsed = ceil((float)valSizeBytes / (float)ckptMemSegContainedTypeSize);
                }
                else
                {
                  // val has not been alloca-ed for in this function => means it is of "primitive" type
                  numOfArrSlotsUsed = 1;
                }
              }
              else
              {
                std::cout << "WARNING: Could not dereference'" << valName << "'; ignoring tracked value!" << std::endl;
                continue;
              }
            }
          }
          // if valSizeBytes was 1, we "sign extend" it to fill up the available byte width of the ckpt mem segment.
          int sizeInCkptMemArr = ckptMemSegContainedTypeSize * numOfArrSlotsUsed;
          int paddedValSizeBytes = (valSizeBytes < sizeInCkptMemArr) ? sizeInCkptMemArr : valSizeBytes;
          printf("paddedValSizeBytes = %d, ckptMemSegContainedTypeSize = %d\n", paddedValSizeBytes, ckptMemSegContainedTypeSize);
          std::cout << "numOfArrSlotsUsed for " << valName << " = " << numOfArrSlotsUsed << std::endl;

          if (InjectionOption == SAVE_ONLY || InjectionOption == SAVE_RESTORE)
          {
            /*
            --- 3.3.3: Create instructions to store value to memory segment
            ----------------------------------------------------------------------------- */
            Instruction *saveBBTerminator = saveBB->getTerminator();
            Instruction *elemPtrStore = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                          ArrayRef<Value *>(indexList, 1), "idx_" + valName,
                                                                          saveBBTerminator);
            Value *storeLocation = trackedVal;
            if (isPointer)
            {
              if (containedType->isArrayTy())
              {

                auto type = IntegerType::getInt8Ty(F.getContext());
                Value *globalSync = M.getOrInsertGlobal(StringRef("sync_bit"), type);
                if (globalSync != NULL)
                {
                  auto vZero = llvm::ConstantInt::get(Type::getInt8Ty(F.getContext()), 0);
                  StoreInst *storeSync = new StoreInst(vZero, globalSync, false, saveBBTerminator);
                }

                bool copy_done = false;
                if (TrackIndexOption)
                {
                  std::vector<Value *> call_params;
                  call_params.push_back(reinterpret_cast<Value *>(elemPtrStore));
                  // call_params.push_back(storeLocation);

                  auto ite = stacksMem.find(trackedVal);
                  if (ite != stacksMem.end())
                  {
                    // Retrieve index stack to push on
                    Value *stack = stacksMem[trackedVal];
                    Value *index = stacksIndex[trackedVal];
                    Type *ArrayTy = stacksType[trackedVal];

                    IRBuilder<> IR(saveBBTerminator);
                    Value *indexList[2] = {IR.getInt32(0), IR.getInt32(0)}; // post inc

                    Instruction *storePtrSrc = GetElementPtrInst::CreateInBounds(containedType, storeLocation, ArrayRef<Value *>(indexList, 2), "", saveBBTerminator);
                    call_params.push_back(storePtrSrc);

                    Instruction *elemPtrSrc = GetElementPtrInst::CreateInBounds(ArrayTy, stack, ArrayRef<Value *>(indexList, 2), "", saveBBTerminator);

                    call_params.push_back(elemPtrSrc);
                    call_params.push_back(index);
                    call_params.push_back(IR.getInt32(stackArraySize));
                    call_params.push_back(IR.getInt32(ceil((float)paddedValSizeBytes / (float)ckptMemSegContainedTypeSize)));

                    // void mem_cpy_index_f(float* dest, float* src, int* index_list, int* sp)
                    CallInst *call1 = CallInst::Create(func_mem_cpy_index_f, call_params, "", saveBBTerminator);
                    Instruction *resetIdx = new StoreInst(llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), 0), index, saveBBTerminator);

                    printf("called \n");

                    /*
                    ValueToValueMapTy vmap;

                    for(Instruction* v : instWaitFor) {
                      //v->removeFromParent();
                      //v->insertBefore(saveBBTerminator);
                      auto *new_inst = v->clone();
                      new_inst->insertBefore(saveBBTerminator);
                      vmap[v] = new_inst;
                      llvm::RemapInstruction(new_inst, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
                    }
                    */
                    copy_done = true;
                  }
                }
                if (!copy_done)
                {

#ifndef LLVM14_VER
                  auto srcAlign = DL.getPrefTypeAlignment(storeLocation->getType());
                  auto dstAlign = DL.getPrefTypeAlignment(elemPtrStore->getType());
#else
                  MaybeAlign srcAlign = DL.getPrefTypeAlign(storeLocation->getType());
                  MaybeAlign dstAlign = DL.getPrefTypeAlign(elemPtrStore->getType());
#endif

                  // TODO: data type filtering

                  builder.SetInsertPoint(saveBBTerminator);
                  /*
                  #ifndef LLVM14_VER
                    CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value*>(elemPtrStore), storeLocation, paddedValSizeBytes, srcAlign, true);
                  #else
                    CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value*>(elemPtrStore), dstAlign, storeLocation, srcAlign, paddedValSizeBytes, true);
                  #endif
                  */

                  // array copy triggered
                  std::vector<Value *> call_params;
                  call_params.push_back(reinterpret_cast<Value *>(elemPtrStore));

                  IRBuilder<> IR(saveBBTerminator);
                  Value *indexList[2] = {IR.getInt32(0), IR.getInt32(0)}; // post inc
                  Instruction *storePtrSrc = GetElementPtrInst::CreateInBounds(containedType, storeLocation, ArrayRef<Value *>(indexList, 2), "", saveBBTerminator);
                  call_params.push_back(storePtrSrc);

                  auto size = llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), paddedValSizeBytes);
                  call_params.push_back(size);
                  CallInst *call1 = CallInst::Create(func_mem_cpy_wrapper_f, call_params, "", saveBBTerminator);

                  /*
                  for(Instruction* v : instWaitFor) {
                  v->removeFromParent();
                  v->insertBefore(saveBBTerminator);
                  //auto *new_inst = v->clone();
                  //new_inst->insertBefore(saveBBTerminator);
                  }
                  /// end copy
                  */
                }
              }
              else if (isPointerPointer) // || numOfArrSlotsUsed > 1)
              {
                // trackedVal is <type>** pointing to array
                Instruction *loadedAddrS = new LoadInst(containedType, storeLocation, "loaded_" + valName, false, saveBBTerminator);
                storeLocation = loadedAddrS;

                auto type = IntegerType::getInt8Ty(F.getContext());
                Value *globalSync = M.getOrInsertGlobal(StringRef("sync_bit"), type);
                if (globalSync != NULL)
                {
                  auto vZero = llvm::ConstantInt::get(Type::getInt8Ty(F.getContext()), 0);
                  StoreInst *storeSync = new StoreInst(vZero, globalSync, false, saveBBTerminator);
                }

                bool copy_done = false;
                if (TrackIndexOption)
                {
                  std::vector<Value *> call_params;
                  call_params.push_back(reinterpret_cast<Value *>(elemPtrStore));
                  call_params.push_back(storeLocation);

                  auto ite = stacksMem.find(trackedVal);
                  if (ite != stacksMem.end())
                  {
                    printf("found\n");
                    // Retrieve index stack to push on
                    Value *stack = stacksMem[trackedVal];
                    Value *index = stacksIndex[trackedVal];
                    Type *ArrayTy = stacksType[trackedVal];

                    IRBuilder<> IR(saveBBTerminator);
                    Value *indexList[2] = {IR.getInt32(0), IR.getInt32(0)}; // post inc
                    Instruction *elemPtrSrc = GetElementPtrInst::CreateInBounds(ArrayTy, stack, ArrayRef<Value *>(indexList, 2), "", saveBBTerminator);

                    call_params.push_back(elemPtrSrc);
                    call_params.push_back(index);
                    call_params.push_back(IR.getInt32(stackArraySize));
                    call_params.push_back(IR.getInt32(ceil((float)paddedValSizeBytes / (float)ckptMemSegContainedTypeSize)));

                    // void mem_cpy_index_f(float* dest, float* src, int* index_list, int* sp)
                    CallInst *call1 = CallInst::Create(func_mem_cpy_index_f, call_params, "", saveBBTerminator);
                    Instruction *resetIdx = new StoreInst(llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), 0), index, saveBBTerminator);
                    printf("called \n");

                    /*
                    for(Instruction* v : instWaitFor) {
                      v->removeFromParent();
                      //v->insertBefore(saveBBTerminator);
                      v->insertBefore(saveBBTerminator);
                      //Instruction* new_inst = v->clone();
                    }
                    */

                    copy_done = true;
                  }
                }
                if (!copy_done)
                {
// create memcpy inst (autoconverts pointers to i8*)
#ifndef LLVM14_VER
                  auto srcAlign = DL.getPrefTypeAlignment(storeLocation->getType());
                  auto dstAlign = DL.getPrefTypeAlignment(elemPtrStore->getType());
#else
                  MaybeAlign srcAlign = DL.getPrefTypeAlign(storeLocation->getType());
                  MaybeAlign dstAlign = DL.getPrefTypeAlign(elemPtrStore->getType());
#endif
                  builder.SetInsertPoint(saveBBTerminator);

                  // TODO: data type filtering

#ifndef LLVM14_VER
                  /*
                  CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value*>(elemPtrStore), storeLocation, paddedValSizeBytes, srcAlign, true);

                  auto type = IntegerType::getInt8Ty(F.getContext());
                  Value* globalSync = M.getOrInsertGlobal(StringRef("sync_bit"), type);
                  if(globalSync != NULL){
                    auto vOne = llvm::ConstantInt::get(Type::getInt8Ty(F.getContext()), 1);
                    StoreInst *storeSync = new StoreInst(vOne, globalSync, false, saveBBTerminator);
                  }
                  */

                  // array copy triggered
                  std::vector<Value *> call_params;
                  call_params.push_back(reinterpret_cast<Value *>(elemPtrStore));
                  call_params.push_back(storeLocation);
                  auto size = llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), paddedValSizeBytes);
                  call_params.push_back(size);
                  CallInst *call1 = CallInst::Create(func_mem_cpy_wrapper_f, call_params, "", saveBBTerminator);

                  /*
                  for(Instruction* v : instWaitFor) {
                    v->removeFromParent();
                    v->insertBefore(saveBBTerminator);
                    //auto *new_inst = v->clone();
                    //new_inst->insertBefore(saveBBTerminator);
                  }
                  */
                  // end copy

#else
                  CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value *>(elemPtrStore), dstAlign, storeLocation, srcAlign, paddedValSizeBytes, true);
#endif
                }
              }
              else
              {
                // save dereferenced value by first loading value from the pointer
                Instruction *deref = new LoadInst(containedType, storeLocation, "deref_" + valName, false, saveBBTerminator);
                if (ckptMemSegContainedType != containedType)
                {
                  std::string name = JsonHelper::getOpName(reinterpret_cast<Value *>(deref), &M).erase(0, 1);
                  deref = addTypeConversionInst(deref, ckptMemSegContainedType, name, saveBBTerminator);
                }
                Instruction *storeInst = new StoreInst(deref, elemPtrStore, false, saveBBTerminator);
              }
            }
            else
            {
              // do direct store
              if (ckptMemSegContainedType != storeLocation->getType())
              {
                Instruction *typeConv = addTypeConversionInst(storeLocation, ckptMemSegContainedType, valName, saveBBTerminator);
                StoreInst *storeInst = new StoreInst(typeConv, elemPtrStore, false, saveBBTerminator);
              }
              else
              {
                StoreInst *storeInst = new StoreInst(storeLocation, elemPtrStore, false, saveBBTerminator);
              }
            }

            // synthesize liveness data with both updated and original versions of tracked values:
            saveBBLiveOutSet.insert(trackedVal);
            saveBBLiveOutSet.insert(originalTrackedVal);
          }

          if (InjectionOption == RESTORE_ONLY || InjectionOption == SAVE_RESTORE)
          {
            /*
            --- 3.3.4: Create instructions to load value from memory.
            ----------------------------------------------------------------------------- */
            Instruction *restoreBBTerminator = restoreBB->getTerminator();
            Value *restoredVal = nullptr;
            Instruction *elemPtrLoad = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                         ArrayRef<Value *>(indexList, 1), "idx_" + valName,
                                                                         restoreBBTerminator);
            Value *storeLocationOrig = originalTrackedVal; // is where the original value was stored during save operation
            if (isPointer)
            {
              if (containedType->isArrayTy())
              {
// originalTrackedVal is a ptr to a [<size> x <type>] array
// restore values back into original pointer
#ifndef LLVM14_VER
                auto srcAlignOriginalPtr = DL.getPrefTypeAlignment(elemPtrLoad->getType());
                auto dstAlignOriginalPtr = DL.getPrefTypeAlignment(storeLocationOrig->getType());
#else
                MaybeAlign srcAlignOriginalPtr = DL.getPrefTypeAlign(elemPtrLoad->getType());
                MaybeAlign dstAlignOriginalPtr = DL.getPrefTypeAlign(storeLocationOrig->getType());
#endif
                builder.SetInsertPoint(restoreBBTerminator);
                // #ifndef LLVM14_VER
                //   CallInst *memcpyCallOrig =  builder.CreateMemCpy(storeLocationOrig, reinterpret_cast<Value*>(elemPtrLoad), paddedValSizeBytes, srcAlignOriginalPtr, true);
                // #else
                CallInst *memcpyCallOrig = builder.CreateMemCpy(storeLocationOrig, dstAlignOriginalPtr, reinterpret_cast<Value *>(elemPtrLoad), srcAlignOriginalPtr, paddedValSizeBytes, true);
                // #endif
                restoredVal = nullptr; // do not propagate
              }
              else if (isPointerPointer) // || numOfArrSlotsUsed > 1)
              {
                // at this point, allocaInstR has type <type>** (is allocated memory for array.addr)

                /** TODO: ----- memcpy new (restored) array back into the original array pointer ----- */
                // place inst in restoreBB to load array base-address (<type>*) from originalTrackedVal (<type>**) into "local" Value
                Instruction *loadedAddrSOrig = new LoadInst(containedType, storeLocationOrig, "loaded_" + valName, false, restoreBBTerminator);
                storeLocationOrig = loadedAddrSOrig;
#ifndef LLVM14_VER
                auto srcAlignOriginalPtr = DL.getPrefTypeAlignment(elemPtrLoad->getType());
                auto dstAlignOriginalPtr = DL.getPrefTypeAlignment(storeLocationOrig->getType());
#else
                MaybeAlign srcAlignOriginalPtr = DL.getPrefTypeAlign(elemPtrLoad->getType());
                MaybeAlign dstAlignOriginalPtr = DL.getPrefTypeAlign(storeLocationOrig->getType());
#endif
                builder.SetInsertPoint(restoreBBTerminator);
                // #ifndef LLVM14_VER
                //   CallInst *memcpyCallOrig =  builder.CreateMemCpy(storeLocationOrig, reinterpret_cast<Value*>(elemPtrLoad), paddedValSizeBytes, srcAlignOriginalPtr, true);
                // #else
                CallInst *memcpyCallOrig = builder.CreateMemCpy(storeLocationOrig, dstAlignOriginalPtr, reinterpret_cast<Value *>(elemPtrLoad), srcAlignOriginalPtr, paddedValSizeBytes, true);
                // #endif

                /** TODO: The following store inst is unnecessary since we're using the original array address */
                // store <type>* into original the <type>** Value (i.e. originalTrackedVal) pointing to the array
                // StoreInst *storeInst = new StoreInst(storeLocationOrig, originalTrackedVal, false, restoreBBTerminator);
                restoredVal = nullptr; // do not propagate
              }
              else
              {
                /** TODO: Choose between 1) propagating newly-allocated single-ptr OR 2) storing back to original val */

                /** ----- Option 1: newly-allocate single-ptr and propgate new value ----- */
                // allocate memory (ptr) to store value into
                AllocaInst *allocaInstR = new AllocaInst(containedType, 0, "alloca_" + valName, restoreBBTerminator);

                // load value from memory and store into alloca-ed mem
                Instruction *loadInst = new LoadInst(ckptMemSegContainedType, elemPtrLoad, "load_derefed_" + valName, false, restoreBBTerminator);
                if (ckptMemSegContainedType != containedType)
                {
                  std::string name = JsonHelper::getOpName(reinterpret_cast<Value *>(loadInst), &M).erase(0, 1);
                  loadInst = addTypeConversionInst(loadInst, containedType, name, restoreBBTerminator);
                }
                // store <type>* into new <type>** to propagate through CFG
                StoreInst *storeInst = new StoreInst(loadInst, allocaInstR, false, restoreBBTerminator);
                restoredVal = allocaInstR;

                /** ----- Option 2: store new (restored) value back into the original pointer ----- */
                /** TODO: removing this option will somehow cause a "instructoin does not dominate" error*/
                // StoreInst *storeInstOriginal = new StoreInst(loadInst, storeLocationOrig, false, restoreBBTerminator);
                // restoredVal = nullptr;
              }
            }
            else
            {
              // do direct load
              LoadInst *loadInst = new LoadInst(ckptMemSegContainedType, elemPtrLoad, "load_" + valName, false, restoreBBTerminator);
              restoredVal = loadInst;
              if (ckptMemSegContainedType != containedType)
              {
                std::string name = JsonHelper::getOpName(reinterpret_cast<Value *>(loadInst), &M).erase(0, 1);
                Instruction *typeConv = addTypeConversionInst(loadInst, containedType, name, restoreBBTerminator);
                restoredVal = typeConv;
              }
            }

            /*
            --- 3.3.5: Add phi node into junctionBB to merge loaded val & original val
            ----------------------------------------------------------------------------- */
            if (restoredVal != nullptr) // do not add phi node if we choose not to propagate
            {
              PHINode *phi = PHINode::Create(trackedVal->getType(), 2, "new_" + valName, junctionBB->getTerminator());
              phi->addIncoming(restoredVal, restoreBB);
              if (InjectionOption == SAVE_RESTORE)
              {
                phi->addIncoming(trackedVal, saveBB);
              }
              else
              {
                phi->addIncoming(trackedVal, checkpointBB);
              }
              trackedValPhiValMap[trackedVal] = phi;
            }

            /*
            --- 3.3.6: Configure live-out sets for saveBB, restoreBB and junctionBB; init trackValPhiValMap.
            ----------------------------------------------------------------------------- */
            /* Since the live-out data for all other BBs use the original value version too (and algo checks
            live-out using this live-out data), it would be more consistent to use original value version
            as live-out of saveBB, restoreBB & junctionBB instead of the new phi. */
            // synthesize liveness data with both updated and original versions of tracked values:
            restoreBBLiveOutSet.insert(trackedVal);
            junctionBBLiveOutSet.insert(trackedVal);
            restoreBBLiveOutSet.insert(originalTrackedVal);
            junctionBBLiveOutSet.insert(originalTrackedVal);
          }

          valMemSegIndex += numOfArrSlotsUsed;
          printf("$$ next valMemSegIndex = %d\n", valMemSegIndex);
          ckptSizeBytes += paddedValSizeBytes;
        }
        funcSaveBBsLiveOutMap[saveBB] = saveBBLiveOutSet;
        funcRestoreBBsLiveOutMap[restoreBB] = restoreBBLiveOutSet;
        funcJunctionBBsLiveOutMap[junctionBB] = junctionBBLiveOutSet;
        funcJunctionBBPhiValsMap[junctionBB] = trackedValPhiValMap;

        if (InjectionOption == RESTORE_ONLY || InjectionOption == SAVE_RESTORE)
        {
          /*
          ++ 3.4: Propagate loaded values from restoreBB across CFG.
          +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
          for (auto iter : oldNewTrackedVals)
          {
            /** TODO: verify safety of cast to non-const!! this is dangerous*/
            Value *originalTrackedVal = const_cast<Value *>(iter.first);
            Value *trackedVal = const_cast<Value *>(iter.second);
            std::string valName = JsonHelper::getOpName(trackedVal, &M).erase(0, 1);

            Type *valType = trackedVal->getType();
            if (valType->isPointerTy())
            {
              /** TODO: do 'continue' here if not propagating all pointer types*/
              // continue;
              // do not propagate <type>** Values
              if (valType->getContainedType(0)->isPointerTy())
                continue;
              // do not propagate llvm array pointer type Values (ptr to [<size> x <type>] arr)
              if (valType->getContainedType(0)->isArrayTy())
                continue;
            }

            // for each BB, keeps track of versions of values that have been encountered in this BB (including the original value)
            std::map<BasicBlock *, std::set<Value *>> visitedBBs;

            // get phi value in junctionBB that merges original & loaded versions of trackVal
            if (!funcJunctionBBPhiValsMap.at(junctionBB).count(trackedVal))
            {
              std::cout << "WARNING: No PHI node inserted in junctionBB for tracked val"
                        << JsonHelper::getOpName(trackedVal, &M)
                        << "; do not propagate." << std::endl;
              continue;
            }
            PHINode *phi = funcJunctionBBPhiValsMap.at(junctionBB).at(trackedVal);

            propagateRestoredValuesBFS(resumeBB, junctionBB, trackedVal, phi,
                                       originalTrackedVal, &visitedBBs,
                                       &funcBBLiveValsMap, funcSaveBBsLiveOutMap,
                                       funcRestoreBBsLiveOutMap, funcJunctionBBsLiveOutMap,
                                       &bbCheckpointsOldNewVals, &allTrackedValVersions);
            printf("----------------\n");
          }
        }
        // store ckpt size into map
        ckptSizeMap[checkpointBB] = ckptSizeBytes;
      }

      // break; /** TODO: IS FOR TESTING (limits to 1 checkpoint; propagation algo does not work with > 1 ckpt) */
    }

    /*
    = 4: Add checkpoint IDs & heartbeat to saveBBs and restoreBBs
    ============================================================================= */
    std::pair<SubroutineInjection::CheckpointIdBBMap, int> ckptIDPair = getCheckpointIdBBMap(checkpointBBTopoMap, moduleCkptIDCounter, M);
    CheckpointIdBBMap ckptIDsCkptToposMap = ckptIDPair.first;
    // update module ckpt id counter to next ckpt ID to use
    moduleCkptIDCounter = ckptIDPair.second;
    // printCheckpointIdBBMap(ckptIDsCkptToposMap, &F);
    for (auto iter : ckptIDsCkptToposMap)
    {
      /*
      ++ 4.1: for each ckpt's saveBB, add inst to store ckpt id
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      unsigned ckptID = iter.first;
      BasicBlock *saveBB = iter.second.saveBB;
      BasicBlock *restoreBB = iter.second.restoreBB;
      Instruction *saveBBTerminator = (saveBB != nullptr) ? saveBB->getTerminator() : nullptr;
      Instruction *restoreBBTerminator = (restoreBB != nullptr) ? restoreBB->getTerminator() : nullptr;

      if (InjectionOption == SAVE_ONLY || InjectionOption == SAVE_RESTORE)
      {
        Instruction *firstNonPhiInstSaveBB = saveBB->getFirstNonPHI();
        Value *ckptIDIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), CKPT_ID)};
        Instruction *elemPtrCkptId = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                       ArrayRef<Value *>(ckptIDIndexList, 1),
                                                                       "idx_ckpt_id", firstNonPhiInstSaveBB);

        Value *memLockCkptIDInt = {ConstantInt::get(Type::getInt32Ty(context), -1)}; // set ckpt_id to -1 to indicate it's currently being written to by ckpt.
        Value *savedMemLockCkptIDVal = memLockCkptIDInt;

        Value *ckptIDValInt = {ConstantInt::get(Type::getInt32Ty(context), ckptID)};
        Value *savedCkptIDVal = ckptIDValInt;

        if (ckptMemSegContainedType != Type::getInt32Ty(context))
        {
          Value *memLockCkptIDValFloat = addTypeConversionInst(memLockCkptIDInt, ckptMemSegContainedType, "mem_lock_ckpt_id", firstNonPhiInstSaveBB);
          savedMemLockCkptIDVal = memLockCkptIDValFloat;

          Value *ckptIDValFloat = addTypeConversionInst(ckptIDValInt, ckptMemSegContainedType, "ckpt_id", saveBBTerminator);
          savedCkptIDVal = ckptIDValFloat;
        }
        /*
        StoreInst *storeMemLockCkptID = new StoreInst(savedMemLockCkptIDVal, elemPtrCkptId, false, firstNonPhiInstSaveBB);
        StoreInst *storeCkptId = new StoreInst(savedCkptIDVal, elemPtrCkptId, false, saveBBTerminator);
        */

        if ((instScopeEntry != NULL) && ((instScopeExit != NULL)))
        {
          instScopeExit->removeFromParent();
          instScopeEntry->removeFromParent();
          std::cout << "remove" << std::endl;

          Instruction *saveBBTerminator = saveBB->getTerminator();
          std::cout << "Terminal" << std::endl;
          instScopeEntry->insertBefore(elemPtrCkptId);
          std::cout << "Inserted" << std::endl;

          auto type = IntegerType::getInt8Ty(F.getContext());
          Value *globalSync = M.getOrInsertGlobal(StringRef("sync_bit"), type);
          if (globalSync != NULL)
          {
            auto vzero = llvm::ConstantInt::get(Type::getInt8Ty(F.getContext()), 0);
            printf("type %d\n", globalSync->getType()->getTypeID());
            StoreInst *storeSync = new StoreInst(vzero, globalSync, false, elemPtrCkptId);
          }

          for (Instruction *v : instWaitFor)
          {
            v->removeFromParent();
            // v->insertBefore(saveBBTerminator);
            v->insertBefore(saveBBTerminator);
            // Instruction* new_inst = v->clone();
          }

          StoreInst *storeMemLockCkptID = new StoreInst(savedMemLockCkptIDVal, elemPtrCkptId, false, firstNonPhiInstSaveBB);
          StoreInst *storeCkptId = new StoreInst(savedCkptIDVal, elemPtrCkptId, false, saveBBTerminator);

          instScopeExit->insertAfter(storeCkptId);
        }
        else
        {
          StoreInst *storeMemLockCkptID = new StoreInst(savedMemLockCkptIDVal, elemPtrCkptId, false, firstNonPhiInstSaveBB);
          StoreInst *storeCkptId = new StoreInst(savedCkptIDVal, elemPtrCkptId, false, saveBBTerminator);

          for (Instruction *v : instWaitFor)
          {
            v->removeFromParent();
          }
        }
      }

      /*
      ++ 4.2: for each ckpt's saveBB & restoreBB, add inst to increment heartbeat
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      /** TODO: remove after testing phase */
      Value *heartbeatIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), HEARTBEAT)};
      Value *addRhsOperandInt = ConstantInt::get(Type::getInt32Ty(context), 1);
      if (InjectionOption == SAVE_ONLY || InjectionOption == SAVE_RESTORE)
      {
        // add inst to saveBB
        Instruction *elemPtrHeartbeatS = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                           ArrayRef<Value *>(heartbeatIndexList, 1),
                                                                           "idx_heartbeat", saveBBTerminator);
        Value *loadHeartbeatS = new LoadInst(ckptMemSegContainedType, elemPtrHeartbeatS, "load_heartbeat", false, saveBBTerminator);
        if (!ckptMemSegContainedType->isIntegerTy())
        {
          // convert float to int for addition
          loadHeartbeatS = addTypeConversionInst(loadHeartbeatS, Type::getInt32Ty(context), "heartbeat", saveBBTerminator);
        }
        builder.SetInsertPoint(saveBBTerminator);
        Value *addInstS = builder.CreateAdd(loadHeartbeatS, addRhsOperandInt, "heartbeat_incr");
        if (!ckptMemSegContainedType->isIntegerTy())
        {
          // convert int to float for storage
          addInstS = addTypeConversionInst(addInstS, ckptMemSegContainedType, "heartbeat_incr", saveBBTerminator);
        }
        StoreInst *storeHeartBeatS = new StoreInst(addInstS, elemPtrHeartbeatS, false, saveBBTerminator);

        /*
        for(Instruction* v : instWaitFor) {
          v->removeFromParent();
          //v->insertBefore(saveBBTerminator);
          v->insertBefore(saveBBTerminator);
          //Instruction* new_inst = v->clone();
        }
        */
      }

      if (InjectionOption == RESTORE_ONLY || InjectionOption == SAVE_RESTORE)
      {
        // add inst to restoreBB
        Instruction *elemPtrHeartbeatR = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                           ArrayRef<Value *>(heartbeatIndexList, 1),
                                                                           "idx_heartbeat", restoreBBTerminator);
        Value *loadHeartbeatR = new LoadInst(ckptMemSegContainedType, elemPtrHeartbeatR, "load_heartbeat", false, restoreBBTerminator);
        if (!ckptMemSegContainedType->isIntegerTy())
        {
          // convert float to int for addition
          loadHeartbeatR = addTypeConversionInst(loadHeartbeatR, Type::getInt32Ty(context), "heartbeat", restoreBBTerminator);
        }
        builder.SetInsertPoint(restoreBBTerminator);
        Value *addInstR = builder.CreateAdd(loadHeartbeatR, addRhsOperandInt, "heartbeat_incr");
        if (!ckptMemSegContainedType->isIntegerTy())
        {
          // convert int to float for storage
          addInstR = addTypeConversionInst(addInstR, ckptMemSegContainedType, "heartbeat_incr", restoreBBTerminator);
        }
        StoreInst *storeHeartBeatR = new StoreInst(addInstR, elemPtrHeartbeatR, false, restoreBBTerminator);
      }
    }

    if (InjectionOption == RESTORE_ONLY || InjectionOption == SAVE_RESTORE)
    {
      /*
      = 5: Populate restoreControllerBB with switch instructions.
      ============================================================================= */
      /* a. if CheckpointID indicates no checkpoint has been saved, continue to computation.
        b. if CheckpointID exists, jump to restoreBB for that CheckpointID. */

      // load CheckpointID from memory
      Instruction *terminatorInst = restoreControllerBB->getTerminator();
      Value *ckptIDIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), CKPT_ID)};
      Instruction *elemPtrLoad = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                   ArrayRef<Value *>(ckptIDIndexList, 1), "idx_ckpt_id_load",
                                                                   terminatorInst);
      LoadInst *loadCheckpointID = new LoadInst(ckptMemSegContainedType, elemPtrLoad, "load_ckpt_id", false, terminatorInst);
      Value *intCkptId = loadCheckpointID;
      // convert loaded ckpt id into int32
      if (!ckptMemSegContainedType->isIntegerTy())
      {
        intCkptId = addTypeConversionInst(loadCheckpointID, Type::getInt32Ty(context), "ckpt_id", terminatorInst);
      }

      /*
      ++ 5.b: Create switch instruction in restoreControllerBB
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      unsigned int numCases = ckptIDsCkptToposMap.size();
      builder.SetInsertPoint(terminatorInst);
      SwitchInst *switchInst = builder.CreateSwitch(intCkptId, restoreControllerSuccessor, numCases);
      switchInst->removeFromParent();
      // printf("p terminatorInst %x p switchInst %x\n", terminatorInst->getParent(), switchInst->getParent());
      // assert(switchInst->getParent() == nullptr && "ReplaceInstWithInst: Instruction already inserted into basic block!");
      ReplaceInstWithInst(terminatorInst, switchInst);
      for (auto iter : ckptIDsCkptToposMap)
      {
        ConstantInt *checkpointID = ConstantInt::get(Type::getInt32Ty(context), iter.first);
        CheckpointTopo checkpointTopo = iter.second;
        BasicBlock *restoreBB = checkpointTopo.restoreBB;
        switchInst->addCase(checkpointID, restoreBB); // insert new jump to basic block
      }
    }

    /*
    = 5.3.6: Save isComplete in memorySegment[1]; Insert inst in exitBB
    ============================================================================= */
    Value *isCompleteIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), IS_COMPLETE)};
    for (auto funcIter = F.begin(); funcIter != F.end(); ++funcIter)
    {
      BasicBlock *BB = &*funcIter;
      for (auto bbIter = BB->begin(); bbIter != BB->end(); ++bbIter)
      {
        Instruction *Inst = &*bbIter;
        if (isa<ReturnInst>(Inst))
        {
          Value *isComplete = nullptr;
          if (Inst->getNumOperands() == 0)
          {
            // returns void; set isComplete = 1
            isComplete = ConstantInt::get(Type::getInt32Ty(context), 1);
          }
          else
          {
            /** TODO:
             * Storing return value will cause current pass to throw segfault if retVal is a pointer.
             * Is cuz pointer cannot be type-converted using simple instructions. */
            Value *p_retVal = dyn_cast<ReturnInst>(Inst)->getReturnValue();
            isComplete = (p_retVal->getType()->isPointerTy())
                             ? ConstantInt::get(Type::getInt32Ty(context), 1)
                             : p_retVal;
          }

          // insert inst into saveBB
          Instruction *elemPtrIsCompleteS = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment,
                                                                              ArrayRef<Value *>(isCompleteIndexList, 1),
                                                                              "idx_isComplete", Inst);
          if (ckptMemSegContainedType != isComplete->getType())
          {
            Value *isCompleteTyConv = addTypeConversionInst(isComplete, ckptMemSegContainedType, "isComplete", Inst);
            StoreInst *storeIsCompleteS = new StoreInst(isCompleteTyConv, elemPtrIsCompleteS, false, Inst);
          }
          else
          {
            StoreInst *storeIsCompleteS = new StoreInst(isComplete, elemPtrIsCompleteS, false, Inst);
          }
        }
      }
    }

    /* ============================================================================= */
    // store map of ckpt sizes; done only after all ckpting infrastructure is completed
    funcCkptSizeMap[&F] = ckptSizeMap;

    if (ckptIDsCkptToposMap.size() == 0)
    {
      // no checkpoints were added for func, return false
      std::cout << "WARNING: No checkpoints were inserted for function '" << funcName << "'" << std::endl;
      continue;
    }

    // FOR TESTING:
    hasInjectedSubroutinesForFunc = true;

    if (!hasInjectedSubroutinesForFunc)
    {
      // none of BBs in function lead to successful subroutine injection.
      std::cout << "WARNING: None of BBs in function '" << funcName << "' result in successful subroutine injection. No checkpoints added to function.\n";
    }
  }

  /** TODO: write funcCkptSizeMap to JSON */
  JsonHelper::writeFuncCkptSizesToJson(funcCkptSizeMap, CKPT_SIZES_JSON_PATH);

  return isModified;
}

void SubroutineInjection::propagateRestoredValuesBFS(BasicBlock *startBB, BasicBlock *prevBB, Value *oldVal, Value *newVal,
                                                     Value *originalTrackedVal,
                                                     std::map<BasicBlock *, std::set<Value *>> *visitedBBs,
                                                     const LiveValues::LivenessResult *funcBBLiveValsMap,
                                                     std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                                     std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                                     std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap,
                                                     CheckpointBBOldNewValsMap *ckptBBOldNewValsMap,
                                                     std::map<const Value *, std::set<const Value *>> *allTrackedValVersions)
{
  std::queue<SubroutineInjection::BBUpdateRequest> q;

  // track versions of values in current "thread/path" of propagation
  std::set<Value *> valueVersions;
  valueVersions.insert(oldVal);
  valueVersions.insert(newVal);
  updateAllTrackedValVersionsMap(originalTrackedVal, newVal, allTrackedValVersions, startBB->getParent()->getParent());

  SubroutineInjection::BBUpdateRequest updateRequest = {
      .startBB = startBB,
      .currBB = startBB,
      .prevBB = prevBB,
      .oldVal = oldVal,
      .newVal = newVal,
      .valueVersions = valueVersions};
  q.push(updateRequest);

  while (!q.empty())
  {
    SubroutineInjection::BBUpdateRequest updateRequest = q.front();
    q.pop();
    processUpdateRequest(updateRequest, &q, originalTrackedVal, visitedBBs,
                         funcBBLiveValsMap, funcSaveBBsLiveOutMap,
                         funcRestoreBBsLiveOutMap, funcJunctionBBsLiveOutMap,
                         ckptBBOldNewValsMap);
    updateAllTrackedValVersionsMap(originalTrackedVal, updateRequest.newVal, allTrackedValVersions, startBB->getParent()->getParent());
  }
}

void SubroutineInjection::processUpdateRequest(SubroutineInjection::BBUpdateRequest updateRequest,
                                               std::queue<SubroutineInjection::BBUpdateRequest> *q,
                                               Value *originalTrackedVal,
                                               std::map<BasicBlock *, std::set<Value *>> *visitedBBs,
                                               const LiveValues::LivenessResult *funcBBLiveValsMap,
                                               std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                               std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                               std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap,
                                               CheckpointBBOldNewValsMap *ckptBBOldNewValsMap)
{
  BasicBlock *startBB = updateRequest.startBB;
  BasicBlock *currBB = updateRequest.currBB;
  BasicBlock *prevBB = updateRequest.prevBB;
  Value *oldVal = updateRequest.oldVal;
  Value *newVal = updateRequest.newVal;
  std::set<Value *> valueVersions = updateRequest.valueVersions;

  Function *F = currBB->getParent();
  Module *M = F->getParent();

  std::cout << "---\n";
  std::cout << "prevBB:{" << JsonHelper::getOpName(prevBB, M) << "}\n";
  std::cout << "currBB:{" << JsonHelper::getOpName(currBB, M) << "}\n";
  std::cout << "oldVal=" << JsonHelper::getOpName(oldVal, M) << "; newVal=" << JsonHelper::getOpName(newVal, M) << "\n";

  // stop after we loop back to (and re-process) startBB
  bool isStop = currBB == startBB && visitedBBs->count(currBB);
  std::cout << "isStop=" << isStop << "\n";

  // tracks history of the valueVersions set across successive visits of this BB.
  std::set<Value *> bbValueVersions = getOrDefault(currBB, visitedBBs); // marks BB as visited (if not already)
  // stop propagation if val versions in valueVersions and bbValueVersions match exactly.
  bool isAllContained = true;
  for (auto valIter : bbValueVersions)
  {
    isAllContained = isAllContained && valueVersions.count(&*valIter);
  }
  if (isAllContained && bbValueVersions.size() == valueVersions.size())
    isStop = true;

  if (hasNPredecessorsOrMore(currBB, 2) && 1 < numOfPredsWhereVarIsLiveOut(currBB, originalTrackedVal, funcBBLiveValsMap,
                                                                           funcSaveBBsLiveOutMap, funcRestoreBBsLiveOutMap,
                                                                           funcJunctionBBsLiveOutMap))
  {
    if (isPhiInstExistForIncomingBBForTrackedVal(valueVersions, currBB, prevBB))
    {
      std::cout << "MODIFY EXISTING PHI NODE\n";
      // modify existing phi input from %oldVal to %newVal
      for (auto phiIter = currBB->phis().begin(); phiIter != currBB->phis().end(); phiIter++)
      {
        PHINode *phi = &*phiIter;
        for (unsigned i = 0; i < phi->getNumIncomingValues(); i++)
        {
          Value *incomingValue = phi->getIncomingValue(i);
          BasicBlock *incomingBB = phi->getIncomingBlock(i);
          if (incomingBB == prevBB && valueVersions.count(incomingValue))
          {
            if (incomingValue == newVal)
            {
              // we've already updated this phi instruction to use newVal in a previous traversal path
              // do not add successors to BFS queue again.
              continue;
            }
            else
            {
              setIncomingValueForBlock(phi, incomingBB, newVal);
              bbValueVersions.insert(valueVersions.begin(), valueVersions.end()); // copy contents of valueVersions into bbValueVersions
              updateMapEntry(currBB, bbValueVersions, visitedBBs);

              std::string phiName = JsonHelper::getOpName(phi, M);
              std::string incomingBBName = JsonHelper::getOpName(incomingBB, M);
              std::string valueName = JsonHelper::getOpName(incomingValue, M);
              std::string newValName = JsonHelper::getOpName(newVal, M);
              std::cout << "modify " << phiName << ": change [" << valueName << ", " << incomingBBName << "] to [" << newValName << ", " << incomingBBName << "]\n";
            }
          }
        }
      }
      // Do not propagate the LHS of the modified phi node further through the cfg
      // If it's a new phi that algo has added, it should already have been propagated by the "Add new PHI" block.
      // If it's an existing phi that was part of the CFG before propagation, then the phi value should already be
      // in the correct places in the cfg and does not need to be re-propagtaed.
    }
    else
    {
      std::cout << "ADD NEW PHI NODE\n";
      // make new phi node
      std::string bbName = JsonHelper::getOpName(currBB, M).erase(0, 1);
      std::string newValName = JsonHelper::getOpName(newVal, M).erase(0, 1);
      std::vector<BasicBlock *> predecessors = getBBPredecessors(currBB);
      Instruction *firstInst = &*(currBB->begin());
      PHINode *newPhi = PHINode::Create(oldVal->getType(), predecessors.size(), newValName + ".phi", firstInst);
      std::cout << "added new phi: " << JsonHelper::getOpName(dyn_cast<Value>(newPhi), M) << "\n";
      for (BasicBlock *predBB : predecessors)
      {
        // if pred has exit edge to startBB and val is live-out from it, add new entry in new phi instruction.
        if (isValLiveOutofBB(predBB, originalTrackedVal, funcBBLiveValsMap,
                             funcSaveBBsLiveOutMap, funcRestoreBBsLiveOutMap,
                             funcJunctionBBsLiveOutMap))
        {
          Value *phiInput = (predBB == prevBB) ? newVal : oldVal;
          std::cout << "  add to phi: {" << JsonHelper::getOpName(phiInput, M) << ", " << JsonHelper::getOpName(predBB, M) << "}\n";
          newPhi->addIncoming(phiInput, predBB);
          valueVersions.insert(phiInput);
        }
      }

      // update each subsequent instruction in this BB from oldVal to newPhi
      for (auto instIter = currBB->begin(); instIter != currBB->end(); instIter++)
      {
        Instruction *inst = &*instIter;
        if (inst != dyn_cast<Instruction>(newPhi)) // don't update new phi instruction
        {
          std::cout << "  try updating inst '" << JsonHelper::getOpName(dyn_cast<Value>(inst), M) << "'\n";
          replaceOperandsInInst(inst, oldVal, newPhi);
        }
        if (valueVersions.count(inst))
          isStop = true; // inst is a definition of one of the value versions.
      }
      valueVersions.insert(newPhi);
      bbValueVersions.insert(valueVersions.begin(), valueVersions.end()); // copy contents of valueVersions into bbValueVersions
      updateMapEntry(currBB, bbValueVersions, visitedBBs);
      // replace old value in ckptBBMap with this newPhi (if curBB is part of ckptBBOldNewValsMap)
      if (ckptBBOldNewValsMap->count(currBB))
        updateCkptBBMap(currBB, newPhi, bbValueVersions, ckptBBOldNewValsMap, originalTrackedVal);

      if (!isStop)
      {
        // add direct successors of BB to queue (convert oldVal to newPhi)
        for (BasicBlock *succBB : getBBSuccessors(currBB))
        {
          if (succBB != currBB)
          {
            SubroutineInjection::BBUpdateRequest newUpdateRequest = {
                .startBB = startBB,
                .currBB = succBB,
                .prevBB = currBB,
                .oldVal = oldVal,
                .newVal = newPhi,
                .valueVersions = valueVersions};
            q->push(newUpdateRequest);
          }
        }
      }
    }
  }
  else
  {
    // update instructions in BB
    for (auto instIter = currBB->begin(); instIter != currBB->end(); instIter++)
    {
      Instruction *inst = &*instIter;
      replaceOperandsInInst(inst, oldVal, newVal);
      if (valueVersions.count(inst))
        isStop = true; // inst is a definition of one of the value versions.
    }
    valueVersions.insert(newVal);
    bbValueVersions.insert(valueVersions.begin(), valueVersions.end()); // copy contents of valueVersions into bbValueVersions
    updateMapEntry(currBB, bbValueVersions, visitedBBs);
    // replace old value in ckptBBMap with this newVal (if curBB is part of ckptBBOldNewValsMap)
    if (ckptBBOldNewValsMap->count(currBB))
      updateCkptBBMap(currBB, newVal, bbValueVersions, ckptBBOldNewValsMap, originalTrackedVal);

    if (!isStop)
    {
      // add direct successors of BB to queue (convert oldVal to newVal)
      for (BasicBlock *succBB : getBBSuccessors(currBB))
      {
        if (succBB != currBB)
        {
          SubroutineInjection::BBUpdateRequest newUpdateRequest = {
              .startBB = startBB,
              .currBB = succBB,
              .prevBB = currBB,
              .oldVal = oldVal,
              .newVal = newVal,
              .valueVersions = valueVersions};
          q->push(newUpdateRequest);
        }
      }
    }
  }

  std::cout << "@@@ valueVersions: (";
  for (auto valIter : valueVersions)
  {
    Value *val = &*valIter;
    std::cout << JsonHelper::getOpName(val, M) << ", ";
  }
  std::cout << ")" << std::endl;
  std::cout << "@@@ bbValueVersions: (";
  for (auto valIter : bbValueVersions)
  {
    Value *val = &*valIter;
    std::cout << JsonHelper::getOpName(val, M) << ", ";
  }
  std::cout << ")" << std::endl;
}

void SubroutineInjection::updateMapEntry(BasicBlock *key, std::set<Value *> newVal, std::map<BasicBlock *, std::set<Value *>> *map)
{
  if (map->count(key))
  {
    // map::emplace will silently fail if key already exists in map, so we delete the key first.
    map->erase(key);
  }
  map->emplace(key, newVal);
}

std::set<Value *>
SubroutineInjection::getOrDefault(BasicBlock *key, std::map<BasicBlock *, std::set<Value *>> *map)
{
  if (!map->count(key))
  {
    // if key not present, emplace and initialise key-value pair
    std::set<Value *> emptySet;
    map->emplace(key, emptySet);
  }
  return map->at(key);
}

const Value *
SubroutineInjection::findKeyByValueInMap(const Value *value, std::map<const Value *, const Value *> map)
{
  for (auto it : map)
  {
    if (it.second == value)
      return it.first;
  }
  return nullptr;
}

const Value *
SubroutineInjection::findKeyByValueInMap(Value *value, std::map<const Value *, std::set<const Value *>> map)
{
  for (auto it : map)
  {
    if (it.second.count(value))
      return it.first;
  }
  return nullptr;
}

bool SubroutineInjection::isValLiveOutofBB(BasicBlock *BB, Value *val, const LiveValues::LivenessResult *funcBBLiveValsMap,
                                           std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                           std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                           std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap)
{
  Function *F = BB->getParent();
  std::set<const Value *> liveOutSet;
  if (funcJunctionBBsLiveOutMap.count(BB))
  {
    // BB is a junctionBB
    liveOutSet = funcJunctionBBsLiveOutMap.at(BB);
  }
  else if (funcSaveBBsLiveOutMap.count(BB))
  {
    // BB is a saveBB
    liveOutSet = funcSaveBBsLiveOutMap.at(BB);
  }
  else if (funcRestoreBBsLiveOutMap.count(BB))
  {
    // BB is a restoreBB
    liveOutSet = funcRestoreBBsLiveOutMap.at(BB);
  }
  else if (funcBBLiveValsMap->at(F).count(BB))
  {
    // BB is an original BB
    liveOutSet = funcBBLiveValsMap->at(F).at(BB).liveOutVals;
  }
  return liveOutSet.count(val);
}

/** TODO: this should also ideally also consider the live-out set of restoreControllerBB, which is the live-out set of entryBB*/
unsigned
SubroutineInjection::numOfPredsWhereVarIsLiveOut(BasicBlock *BB, Value *val, const LiveValues::LivenessResult *funcBBLiveValsMap,
                                                 std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                                 std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                                 std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap)
{
  unsigned count = 0;
  for (auto iter = pred_begin(BB); iter != pred_end(BB); iter++)
  {
    BasicBlock *pred = *iter;
    if (isValLiveOutofBB(pred, val, funcBBLiveValsMap, funcSaveBBsLiveOutMap,
                         funcRestoreBBsLiveOutMap, funcJunctionBBsLiveOutMap))
    {
      count++;
    }
  }
  return count;
}

bool SubroutineInjection::isPhiInstExistForIncomingBBForTrackedVal(std::set<Value *> valueVersions, BasicBlock *currBB, BasicBlock *prevBB)
{
  for (auto phiIter = currBB->phis().begin(); phiIter != currBB->phis().end(); phiIter++)
  {
    PHINode *phi = &*phiIter;
    for (unsigned i = 0; i < phi->getNumIncomingValues(); i++)
    {
      Value *incomingValue = phi->getIncomingValue(i);
      BasicBlock *incomingBB = phi->getIncomingBlock(i);
      if (incomingBB == prevBB && valueVersions.count(incomingValue))
      {
        return true;
      }
    }
  }
  return false;
}

bool SubroutineInjection::isPhiInstForValExistInBB(Value *val, BasicBlock *BB)
{
  for (auto phiIter = BB->phis().begin(); phiIter != BB->phis().end(); phiIter++)
  {
    PHINode *phi = &*phiIter;
    User::op_iterator operandIter;
    for (operandIter = phi->op_begin(); operandIter != phi->op_end(); operandIter++)
    {
      const Value *operand = *operandIter;
      if (operand == val)
        return true;
    }
  }
  return false;
}

bool SubroutineInjection::replaceOperandsInInst(Instruction *inst, Value *oldVal, Value *newVal)
{
  bool hasReplaced = false;
  Module *M = inst->getParent()->getParent()->getParent();
  User::op_iterator operandIter;
  for (operandIter = inst->op_begin(); operandIter != inst->op_end(); operandIter++)
  {
    const Value *value = *operandIter;
    std::string valName = JsonHelper::getOpName(value, M);
    // std::cout<<"\n\n*** "<<JsonHelper::getOpName(value, M)<<"\n\n";
    if (value == oldVal)
    {
      // replace old operand with new operand
      *operandIter = newVal;
      hasReplaced = true;
      std::string newValName = JsonHelper::getOpName(*operandIter, M);
      std::cout << "Replacement: OldVal=" << valName << "; NewVal=" << newValName << "\n";
    }
  }
  return hasReplaced;
}

void SubroutineInjection::updateCkptBBMap(BasicBlock *ckptBB, Value *newVal, std::set<Value *> bbValueVersions,
                                          CheckpointBBOldNewValsMap *ckptBBOldNewValsMap, Value *originalTrackedVal)
{
  // if ckptBBMap contains value in valueVersions, remove value and replace it with newVal.
  Module *M = ckptBB->getParent()->getParent();
  std::map<const Value *, const Value *> *ckptBBOldNewTrackedVals = &ckptBBOldNewValsMap->at(ckptBB);
  std::set<const Value *> updatedTrackedVals = getOldNewTrackedValsSets(*ckptBBOldNewTrackedVals).second;
  for (auto val : bbValueVersions)
  {
    if (updatedTrackedVals.count(val))
    {
      ckptBBOldNewTrackedVals->erase(originalTrackedVal);
      ckptBBOldNewTrackedVals->emplace(originalTrackedVal, newVal);
      std::cout << ">> " << JsonHelper::getOpName(ckptBB, M) << ": Replaced " << JsonHelper::getOpName(val, M) << " with " << JsonHelper::getOpName(newVal, M) << std::endl;
      break; // there should only be one version of value in ckptBBTrackedVals set
    }
  }
}

SubroutineInjection::CheckpointBBOldNewValsMap
SubroutineInjection::initBBCheckpointsOldNewVals(CheckpointBBMap bbCheckpoints)
{
  CheckpointBBOldNewValsMap bbCheckpointsOldNewVals;
  for (auto bbIt : bbCheckpoints)
  {
    std::map<const Value *, const Value *> oldNewVals;
    const BasicBlock *bb = bbIt.first;
    for (auto val : bbIt.second)
    {
      oldNewVals.emplace(val, val);
    }
    bbCheckpointsOldNewVals.emplace(bb, oldNewVals);
  }
  return bbCheckpointsOldNewVals;
}

std::map<const Value *, std::set<const Value *>>
SubroutineInjection::initAllTrackedValVersions(CheckpointBBMap bbCheckpoints)
{
  std::map<const Value *, std::set<const Value *>> allTrackedValVersions;
  std::set<const Value *> allValsSet;
  for (auto bbIt : bbCheckpoints)
  {
    std::set<const Value *> bbTrackedVals = bbIt.second;
    allValsSet.insert(bbTrackedVals.begin(), bbTrackedVals.end());
  }
  for (auto val : allValsSet)
  {
    std::set<const Value *> valVersionsSet;
    valVersionsSet.insert(val);
    allTrackedValVersions.emplace(val, valVersionsSet);
  }
  return allTrackedValVersions;
}

void SubroutineInjection::updateAllTrackedValVersionsMap(Value *originalTrackedVal, Value *newTrackedVal,
                                                         std::map<const Value *, std::set<const Value *>> *allTrackedValVersions,
                                                         Module *M)
{
  if (allTrackedValVersions->count(originalTrackedVal))
  {
    std::cout << "£££ add " << JsonHelper::getOpName(newTrackedVal, M) << " to " << JsonHelper::getOpName(originalTrackedVal, M) << " set" << std::endl;
    std::set<const Value *> *valVersionsSet = &allTrackedValVersions->at(originalTrackedVal);
    valVersionsSet->insert(newTrackedVal);
  }
  else
  {
    std::cout << "£££ XX " << JsonHelper::getOpName(newTrackedVal, M) << " not found!" << std::endl;
  }
}

std::pair<std::set<const Value *>, std::set<const Value *>>
SubroutineInjection::getOldNewTrackedValsSets(std::map<const Value *, const Value *> oldNewTrackedVals)
{
  std::set<const Value *> originalTrackedVals;
  std::set<const Value *> updatedTrackedVals;
  for (auto iter : oldNewTrackedVals)
  {
    originalTrackedVals.insert(iter.first);
    updatedTrackedVals.insert(iter.second);
  }
  std::pair<std::set<const Value *>, std::set<const Value *>> pair = {originalTrackedVals, updatedTrackedVals};
  return pair;
}

std::pair<SubroutineInjection::CheckpointIdBBMap, int>
SubroutineInjection::getCheckpointIdBBMap(
    std::map<BasicBlock *, SubroutineInjection::CheckpointTopo> &checkpointBBTopoMap,
    int startingCkptNum,
    Module &M) const
{
  int funcCkptIDCounter = startingCkptNum; // id=0 means no ckpt has been saved
  CheckpointIdBBMap checkpointIdBBMap;
  std::map<BasicBlock *, SubroutineInjection::CheckpointTopo>::iterator iter;
  for (iter = checkpointBBTopoMap.begin(); iter != checkpointBBTopoMap.end(); ++iter)
  {
    SubroutineInjection::CheckpointTopo checkpointTopo = iter->second;
    BasicBlock *saveBB = checkpointTopo.saveBB;
    BasicBlock *restoreBB = checkpointTopo.restoreBB;
    BasicBlock *junctionBB = checkpointTopo.junctionBB;
    // append checkpoint id to saveBB and restoreBB names
    if (saveBB != nullptr)
    {
      std::string saveBBName = JsonHelper::getOpName(saveBB, &M).erase(0, 1) + ".id" + std::to_string(funcCkptIDCounter);
      dyn_cast<Value>(saveBB)->setName(saveBBName);
    }

    if (restoreBB != nullptr)
    {
      std::string restoreBBName = JsonHelper::getOpName(restoreBB, &M).erase(0, 1) + ".id" + std::to_string(funcCkptIDCounter);
      dyn_cast<Value>(restoreBB)->setName(restoreBBName);
    }

    if (junctionBB != nullptr)
    {
      std::string junctionBBName = JsonHelper::getOpName(junctionBB, &M).erase(0, 1) + ".id" + std::to_string(funcCkptIDCounter);
      dyn_cast<Value>(junctionBB)->setName(junctionBBName);
    }

    checkpointIdBBMap.emplace(funcCkptIDCounter, checkpointTopo);
    funcCkptIDCounter++;
  }
  std::pair<SubroutineInjection::CheckpointIdBBMap, int> ckptIDInfoPair(checkpointIdBBMap, funcCkptIDCounter);
  return ckptIDInfoPair;
}

/** TODO: remove Module param when removing print statement */
Instruction *
SubroutineInjection::getCmpInstForCondiBrInst(Instruction *condiBranchInst, Module &M) const
{
  Value *condition = dyn_cast<BranchInst>(condiBranchInst)->getCondition();
  Instruction *cmp_instr = nullptr;
  while (cmp_instr == nullptr)
  {
    // attempt to find branch instr's corresponding cmp instr
    Instruction *instr = condiBranchInst->getPrevNode();

    if (instr == nullptr)
      break; // have reached list head; desired cmp instr not found

    Value *instr_val = dyn_cast<Value>(instr);
    std::cout << "?" << JsonHelper::getOpName(instr_val, &M) << "\n";
    if ((isa<ICmpInst>(instr) || isa<FCmpInst>(instr)) && instr == condition)
    {
      cmp_instr = instr;
    }
  }
  return cmp_instr;
}

std::set<BasicBlock *>
SubroutineInjection::getCkptBBsInFunc(Function *F, CheckpointBBMap &bbCheckpoints) const
{
  std::set<BasicBlock *> checkpointBBPtrSet;

  Function::iterator funcIter;
  for (funcIter = F->begin(); funcIter != F->end(); ++funcIter)
  {
    BasicBlock *bb_ptr = &(*funcIter);
    if (bbCheckpoints.count(bb_ptr))
    {
      checkpointBBPtrSet.insert(bb_ptr);
      Module *M = F->getParent();
      std::cout << JsonHelper::getOpName(bb_ptr, M) << "\n";
    }
  }
  return checkpointBBPtrSet;
}

std::set<Value *>
SubroutineInjection::getFuncParams(Function *F) const
{
  std::set<Value *> argSet;
  Function::arg_iterator argIter;
  for (argIter = F->arg_begin(); argIter != F->arg_end(); argIter++)
  {
    Value *arg = &*argIter;
    StringRef argName = JsonHelper::getOpName(arg, F->getParent()).erase(0, 1);
    std::cout << "ARG: " << argName.str() << std::endl;
    argSet.insert(arg);
  }
  return argSet;
}

Value *
SubroutineInjection::getDerefValFromPointer(Value *ptrValue, std::set<const Value *> valVersions, Function *F) const
{
  for (auto funcIter = F->begin(); funcIter != F->end(); ++funcIter)
  {
    BasicBlock *BB = &*funcIter;
    for (auto bbIter = BB->begin(); bbIter != BB->end(); ++bbIter)
    {
      Instruction *Inst = &*bbIter;
      if (isa<StoreInst>(Inst))
      {
        Value *storeValue = Inst->getOperand(0);
        Value *storeAddrPtr = Inst->getOperand(1);
        if (valVersions.count(storeAddrPtr))
        {
          return storeValue;
        }
      }
    }
  }
  std::cout << "WARNING: Could not find value stored to by '"
            << JsonHelper::getOpName(ptrValue, F->getParent())
            << " " << ptrValue
            << "'!" << std::endl;
  return nullptr;
}

Instruction *
SubroutineInjection::addTypeConversionInst(Value *val, Type *destType, std::string valName, Instruction *insertBefore)
{
  if (val->getType()->isIntegerTy(32) && (destType->isFloatTy() || destType->isDoubleTy()))
  {
    return new SIToFPInst(val, destType, "fp_" + valName, insertBefore);
  }
  else if ((val->getType()->isFloatTy() || val->getType()->isDoubleTy()) && destType->isIntegerTy(32))
  {
    return new FPToSIInst(val, destType, "i32_" + valName, insertBefore);
  }
  return nullptr;
}

Value *
SubroutineInjection::getSelectedFuncParam(std::set<Value *> funcParams, StringRef segmentName, Module *M) const
{
  for (auto iter : funcParams)
  {
    Value *arg = &*iter;
    StringRef argName = JsonHelper::getOpName(arg, M).erase(0, 1);
    if (argName.equals(segmentName))
    {
      std::cout << "Found target memory segment ARG: " << argName.str() << std::endl;
      return arg;
    }
  }
  return nullptr;
}

std::vector<BasicBlock *>
SubroutineInjection::getBBPredecessors(BasicBlock *BB) const
{
  std::vector<BasicBlock *> BBPredecessorsList;
  for (auto pit = pred_begin(BB); pit != pred_end(BB); pit++)
  {
    BasicBlock *pred = *pit;
    BBPredecessorsList.push_back(pred);
  }
  return BBPredecessorsList;
}

std::vector<BasicBlock *>
SubroutineInjection::getBBSuccessors(BasicBlock *BB) const
{
  std::vector<BasicBlock *> BBSuccessorsList;
  // find successors to this checkpoint BB
  for (auto sit = succ_begin(BB); sit != succ_end(BB); ++sit)
  {
    BasicBlock *successor = *sit;
    BBSuccessorsList.push_back(successor);
  }
  return BBSuccessorsList;
}

std::vector<BasicBlock *>
SubroutineInjection::getNonExitBBSuccessors(BasicBlock *BB) const
{
  std::vector<BasicBlock *> BBSuccessorsList;
  // find BBs that are not the exit block
  for (auto sit = succ_begin(BB); sit != succ_end(BB); ++sit)
  {
    BasicBlock *successor = *sit;
    int grandChildCount = successor->getTerminator()->getNumSuccessors();
    if (grandChildCount > 0)
    {
      BBSuccessorsList.push_back(successor);
    }
  }
  return BBSuccessorsList;
}

BasicBlock *SubroutineInjection::SplitEdgeCustom(BasicBlock *BB, BasicBlock *Succ, DominatorTree *DT,
                                                 LoopInfo *LI) const
{
  unsigned SuccNum = GetSuccessorNumber(BB, Succ);

  // If this is a critical edge, let SplitCriticalEdge do it.
  if (SplitCriticalEdge(BB->getTerminator(), SuccNum, CriticalEdgeSplittingOptions(DT, LI).setPreserveLCSSA()))
    return BB->getTerminator()->getSuccessor(SuccNum);

  // Otherwise, if BB has a single successor, split it at the bottom of the
  // block.
  assert(BB->getTerminator()->getNumSuccessors() == 1 &&
         "Should have a single succ!");
  return SplitBlock(BB, BB->getTerminator(), DT, LI);
}

BasicBlock *
SubroutineInjection::splitEdgeWrapper(BasicBlock *edgeStartBB, BasicBlock *edgeEndBB, std::string checkpointName, Module &M) const
{
  /** TODO: figure out whether to specify DominatorTree, LoopInfo and MemorySSAUpdater params */
  // BasicBlock *insertedBB = SplitEdge(edgeStartBB, edgeEndBB, nullptr, nullptr, nullptr, checkpointName);
  BasicBlock *insertedBB = SplitEdgeCustom(edgeStartBB, edgeEndBB, nullptr, nullptr);
  insertedBB->setName(checkpointName);
  if (!insertedBB)
  {
    // SplitEdge can fail, e.g. if the successor is a landing pad
    std::cerr << "Split-edge failed between BB{"
              << JsonHelper::getOpName(edgeStartBB, &M)
              << "} and BB{"
              << JsonHelper::getOpName(edgeEndBB, &M)
              << "}\n";
    // Don't insert BB if it fails, if this causes 0 ckpts to be added, then choose ckpt of a larger size)
    return nullptr;
  }
  else
  {
    return insertedBB;
  }
}

SubroutineInjection::FuncValuePtrsMap
SubroutineInjection::getFuncValuePtrsMap(Module &M, LiveValues::TrackedValuesMap_JSON &jsonMap)
{
  SubroutineInjection::FuncValuePtrsMap funcValuePtrsMap;
  for (auto &F : M.getFunctionList())
  {
    std::string funcName = JsonHelper::getOpName(&F, &M);
    if (!jsonMap.count(funcName))
    {
      std::cerr << "No BB Analysis data for function '" << funcName << "'\n";
      continue;
    }
    LiveValues::BBTrackedVals bbTrackedVals;

    // std::set<const Value*> valuePtrsSet;
    std::map<std::string, const Value *> valuePtrsMap;

    Function::iterator bbIter;
    for (bbIter = F.begin(); bbIter != F.end(); ++bbIter)
    {
      const BasicBlock *bb = &(*bbIter);
      std::set<const Value *> trackedVals;
      BasicBlock::const_iterator instrIter;
      for (instrIter = bb->begin(); instrIter != bb->end(); ++instrIter)
      {
        User::const_op_iterator operand;
        for (operand = instrIter->op_begin(); operand != instrIter->op_end(); ++operand)
        {
          const Value *value = *operand;
          std::string valName = JsonHelper::getOpName(value, &M);

          // valuePtrsSet.insert(valuePtr);
          valuePtrsMap.emplace(valName, value);
        }
      }
    }
    funcValuePtrsMap.emplace(&F, valuePtrsMap);
  }
  return funcValuePtrsMap;
}

long unsigned int
SubroutineInjection::getMaxNumOfTrackedValsForBBs(LiveValues::BBTrackedVals &bbTrackedVals) const
{
  auto maxElem = std::max_element(bbTrackedVals.cbegin(), bbTrackedVals.cend(),
                                  [](const auto &a, const auto &b)
                                  {
                                    return a.second.size() < b.second.size();
                                  });
  return (maxElem->second).size();
}

SubroutineInjection::CheckpointBBMap
SubroutineInjection::chooseBBWithLeastTrackedVals(LiveValues::BBTrackedVals bbTrackedVals, Function *F,
                                                  long unsigned int minValsCount) const
{
  CheckpointBBMap cpBBMap;
  const Module *M = F->getParent();

  long unsigned int maxSize = getMaxNumOfTrackedValsForBBs(bbTrackedVals);
  std::cout << "MaxSize=" << maxSize << "\n";
  if (maxSize < minValsCount)
  {
    // function does not contain BBs that have at least minValsCount tracked values.
    std::cout << "Function '" << JsonHelper::getOpName(F, M)
              << "' does not have BBs with at least " << minValsCount
              << " tracked values. BB ignored.\n";
    // short circuit return empty map
    return cpBBMap;
  }

  // Find min number of tracked values that is >= minValsCount (search across all BBs)
  auto minElem = std::min_element(bbTrackedVals.cbegin(), bbTrackedVals.cend(),
                                  [=](const auto &a, const auto &b)
                                  {
                                    // return true if a < b:
                                    // ignore blocks with fewer tracked values than the minValsCount
                                    if (a.second.size() < minValsCount)
                                      return false;
                                    if (b.second.size() < minValsCount)
                                      return true;
                                    return a.second.size() < b.second.size();
                                  });
  long unsigned int minSize = (minElem->second).size();
  std::cout << "(" << F->getName().str() << " min num of tracked vals per BB = " << minSize << ")\n";

  if (minSize >= minValsCount)
  {
    // For each BB with this number of live values, add entry into cpBBMap.
    LiveValues::BBTrackedVals::const_iterator bbIt;
    for (bbIt = bbTrackedVals.cbegin(); bbIt != bbTrackedVals.cend(); bbIt++)
    {
      const BasicBlock *bb = bbIt->first;
      const std::set<const Value *> &trackedVals = bbIt->second;
      // get elements of trackedVals with min number of tracked values that is at least minValCount
      if (trackedVals.size() == minSize)
      {
        cpBBMap.emplace(bb, trackedVals);
      }
    }
  }
  else
  {
    std::cout << "Unable to find checkpoint BB candidates for function '" << JsonHelper::getOpName(F, M) << "'\n";
  }

  return cpBBMap;
}

LiveValues::BBTrackedVals
SubroutineInjection::getBBsWithOneSuccessor(LiveValues::BBTrackedVals bbTrackedVals) const
{
  LiveValues::BBTrackedVals filteredBBTrackedVals;
  LiveValues::BBTrackedVals::const_iterator funcIter;
  for (funcIter = bbTrackedVals.cbegin(); funcIter != bbTrackedVals.cend(); ++funcIter)
  {
    const BasicBlock *BB = funcIter->first;
    const std::set<const Value *> &trackedValues = funcIter->second;
    if (BB->getTerminator()->getNumSuccessors() == 1)
    {
      filteredBBTrackedVals.emplace(BB, trackedValues);
    }
  }
  return filteredBBTrackedVals;
}

LiveValues::BBTrackedVals
SubroutineInjection::removeSelectedTrackedVals(LiveValues::BBTrackedVals bbTrackedVals, std::set<Value *> ignoredValues) const
{
  LiveValues::BBTrackedVals filteredBBTrackedVals;
  LiveValues::BBTrackedVals::const_iterator funcIter;
  for (funcIter = bbTrackedVals.cbegin(); funcIter != bbTrackedVals.cend(); ++funcIter)
  {
    const BasicBlock *BB = funcIter->first;
    const Module *M = BB->getParent()->getParent();
    const std::set<const Value *> &trackedValues = funcIter->second;

    std::set<const Value *> filteredTrackedValues;
    for (auto valIter : trackedValues)
    {
      const Value *val = &*valIter;
      std::string valName = JsonHelper::getOpName(const_cast<Value *>(val), M);

      // if ignoredValues contains a value whose name is a substring in valName => ingore
      bool isMatchNameInIgnoredValues = false;
      for (auto ignoredVal : ignoredValues)
      {
        std::string ignoredValName = JsonHelper::getOpName(ignoredVal, M) + ".";
        // valName must have "%<ignoredValName>." as substring
        // is mainly to target "%<valName>.addr" for when val is a pointer-pointer
        if (valName.find(ignoredValName) != std::string::npos)
          isMatchNameInIgnoredValues = true;
      }
      if (isMatchNameInIgnoredValues)
        continue;

      // check (via matching pointers) if val is in ignoredValues
      if (ignoredValues.count(const_cast<Value *>(val))) /** TODO: verify safety of cast to non-const!! this is dangerous*/
      {
        std::cout << "Tracked value '" << JsonHelper::getOpName(val, M)
                  << "' in BB '" << JsonHelper::getOpName(BB, M)
                  << "' is a 'const' function parameter. Removed from bbTrackedVals map."
                  << std::endl;
      }
      else
      {
        filteredTrackedValues.insert(val);
      }
    }
    filteredBBTrackedVals.emplace(BB, filteredTrackedValues);
  }
  return filteredBBTrackedVals;
}

LiveValues::BBTrackedVals
SubroutineInjection::removeMatchedNestedPtrVals(LiveValues::BBTrackedVals bbTrackedVals, StringRef matchStr) const
{
  LiveValues::BBTrackedVals filteredBBTrackedVals;
  LiveValues::BBTrackedVals::const_iterator funcIter;
  for (funcIter = bbTrackedVals.cbegin(); funcIter != bbTrackedVals.cend(); ++funcIter)
  {
    const BasicBlock *BB = funcIter->first;
    const Module *M = BB->getParent()->getParent();
    const std::set<const Value *> &trackedValues = funcIter->second;

    std::set<const Value *> filteredTrackedValues;
    for (auto valIter : trackedValues)
    {
      const Value *val = &*valIter;
      StringRef valName = StringRef(JsonHelper::getOpName(val, M));
      Type *valType = val->getType();
      if (valName.contains(matchStr) && valType->isPointerTy() && valType->getContainedType(0)->getNumContainedTypes() > 0)
      {
        std::cout << "Tracked value '" << JsonHelper::getOpName(val, M)
                  << "' in BB '" << JsonHelper::getOpName(BB, M)
                  << "' is a nested pointer type. Removed from bbTrackedVals map."
                  << std::endl;
      }
      else
      {
        filteredTrackedValues.insert(val);
      }
    }
    filteredBBTrackedVals.emplace(BB, filteredTrackedValues);
  }
  return filteredBBTrackedVals;
}

LiveValues::BBTrackedVals
SubroutineInjection::removeBBsWithNoTrackedVals(LiveValues::BBTrackedVals bbTrackedVals) const
{
  LiveValues::BBTrackedVals filteredBBTrackedVals;
  LiveValues::BBTrackedVals::const_iterator funcIter;
  for (funcIter = bbTrackedVals.cbegin(); funcIter != bbTrackedVals.cend(); ++funcIter)
  {
    const BasicBlock *BB = funcIter->first;
    const Module *M = BB->getParent()->getParent();
    const std::set<const Value *> &trackedValues = funcIter->second;
    if (trackedValues.size() > 0)
    {
      filteredBBTrackedVals.emplace(BB, trackedValues);
    }
    else
    {
      std::cout << "BB '" << JsonHelper::getOpName(BB, M)
                << "' has no tracked values. BB is no longer considered for checkpointing."
                << std::endl;
    }
  }
  return filteredBBTrackedVals;
}

void SubroutineInjection::printCheckPointBBs(const CheckpointFuncBBMap &fBBMap, Module &M) const
{
  CheckpointFuncBBMap::const_iterator funcIt;
  CheckpointBBMap::const_iterator bbIt;
  std::set<const Value *>::const_iterator valIt;
  for (funcIt = fBBMap.cbegin(); funcIt != fBBMap.cend(); funcIt++)
  {
    const Function *func = funcIt->first;
    const CheckpointBBMap bbMap = funcIt->second;

    std::cout << "Checkpoint candidate BBs for '" << JsonHelper::getOpName(func, &M) << "':\n";
    for (bbIt = bbMap.cbegin(); bbIt != bbMap.cend(); bbIt++)
    {
      const BasicBlock *bb = bbIt->first;
      const std::set<const Value *> vals = bbIt->second;
      std::cout << "  BB: " << JsonHelper::getOpName(bb, &M) << "\n    ";

      for (valIt = vals.cbegin(); valIt != vals.cend(); valIt++)
      {
        const Value *val = *valIt;
        std::cout << JsonHelper::getOpName(val, &M) << " ";
      }
      std::cout << '\n';
    }
    std::cout << "\n";
  }

  return;
}

void SubroutineInjection::printCheckpointIdBBMap(SubroutineInjection::CheckpointIdBBMap map, Function *F)
{
  Module *M = F->getParent();
  std::cout << "\nXXX ----CHECKPOINTS for '" << JsonHelper::getOpName(F, M) << "'---- XXX\n";
  SubroutineInjection::CheckpointIdBBMap::const_iterator iter;
  for (iter = map.cbegin(); iter != map.cend(); ++iter)
  {
    uint8_t id = iter->first;
    CheckpointTopo topo = iter->second;
    std::cout << "ID = " << std::to_string(id) << "\n";
    std::cout << "CheckpointBB = " << JsonHelper::getOpName(topo.checkpointBB, M) << "\n";
    std::cout << "SaveBB = " << JsonHelper::getOpName(topo.saveBB, M) << "\n";
    std::cout << "RestoreBB = " << JsonHelper::getOpName(topo.restoreBB, M) << "\n";
    std::cout << "JunctionBB = " << JsonHelper::getOpName(topo.junctionBB, M) << "\n";
    std::cout << "\n";
  }
}

void SubroutineInjection::printFuncValuePtrsMap(SubroutineInjection::FuncValuePtrsMap map, Module &M)
{
  SubroutineInjection::FuncValuePtrsMap::const_iterator iter;
  for (iter = map.cbegin(); iter != map.cend(); ++iter)
  {
    const Function *func = iter->first;
    std::map<std::string, const Value *> valuePtrsMap = iter->second;
    std::cout << func->getName().str() << ":\n";

    std::map<std::string, const Value *>::iterator it;
    for (it = valuePtrsMap.begin(); it != valuePtrsMap.end(); ++it)
    {
      std::string valName = it->first;
      const Value *val = it->second;
      std::cout << "  " << valName << " {" << JsonHelper::getOpName(val, &M) << "}\n";
    }
    // std::cout << "## size = " << valuePtrsMap.size() << "\n";
  }
}

SubroutineInjection::CheckpointBBMap
SubroutineInjection::chooseBBWithCheckpointDirective(LiveValues::BBTrackedVals bbTrackedVals, Function *F)
{
  std::cout << "\n\n\n\n **************** chooseBBWithCheckpointDirective ********* \n\n"
            << std::endl;
  Module *M = F->getParent();
  CheckpointBBMap cpBBMap;

  // Search for checkpoint directive in BBs of function F
  std::cout << "Function Name = " << F->getName().str() << std::endl;
  Function::iterator funcIter;
  LiveValues::BBTrackedVals::const_iterator bbIt;

  instScopeEntry = NULL;

  for (funcIter = F->begin(); funcIter != F->end(); ++funcIter)
  {
    BasicBlock *BB = &(*funcIter);
    std::cout << "BB=" << JsonHelper::getOpName(BB, M) << std::endl;
    bool curr_BB_added = false;
    BasicBlock::iterator instrIter;

    // scope search
    for (instrIter = BB->begin(); instrIter != BB->end(); ++instrIter)
    {
      Instruction *inst = &(*instrIter);
      if (inst->getOpcode() == Instruction::Call || inst->getOpcode() == Instruction::Invoke)
      {
        StringRef name = cast<CallInst>(*inst).getCalledFunction()->getName();
        if (name.contains("scope.entry"))
        {
          std::cout << "\n contain scope entry\n";
          std::cout << ">>>>>>>>>>>> instruction name = " << name.str() << std::endl;
          instScopeEntry = inst;
          // ensure that we have tracked-values information on the selected checkpoint BB
        }
        else if (name.contains("scope.exit"))
        {
          std::cout << "\n contain scope exit \n";
          std::cout << ">>>>>>>>>>>> instruction name = " << name.str() << std::endl;
          instScopeExit = inst;
        }
      }
    }

    // sync search
    bool save_instructions = false;
    globalSync = NULL;
    for (instrIter = BB->begin(); instrIter != BB->end(); ++instrIter)
    {
      Instruction *inst = &(*instrIter);
      if (inst->getOpcode() == Instruction::Call || inst->getOpcode() == Instruction::Invoke)
      {
        StringRef name = cast<CallInst>(*inst).getCalledFunction()->getName();
        if (name.contains("ssdm_op_Wait"))
        {
          save_instructions = true;
          instWaitFor.push_back(inst);
          // ensure that we have tracked-values information on the selected checkpoint BB
        }
        else if (name.contains("ssdm_op_Poll"))
        {
          std::cout << "\n ssdm_op_Poll \n";
          std::cout << ">>>>>>>>>>>> instruction name = " << name.str() << std::endl;
          instWaitFor.push_back(inst);
          save_instructions = false;
        }
      }
      if (save_instructions == true)
      {
        instWaitFor.push_back(inst);
      }
    }

    // checkpoint search
    for (instrIter = BB->begin(); instrIter != BB->end(); ++instrIter)
    {
      Instruction *inst = &(*instrIter);
      if (inst->getOpcode() == Instruction::Call || inst->getOpcode() == Instruction::Invoke)
      {
        StringRef name = cast<CallInst>(*inst).getCalledFunction()->getName();
        if (name.contains("checkpoint"))
        {
          std::cout << "\n contain checkpoint \n";
          // ensure that we have tracked-values information on the selected checkpoint BB
          for (bbIt = bbTrackedVals.cbegin(); bbIt != bbTrackedVals.cend(); bbIt++)
          {
            const BasicBlock *trackedBB = bbIt->first;
            const std::set<const Value *> &trackedVals = bbIt->second;
            std::cout << "  trackedBB=" << JsonHelper::getOpName(trackedBB, M) << std::endl;
            if (trackedBB == BB)
            {
              std::cout << "\n BB added" << std::endl;
              curr_BB_added = true;
              cpBBMap.emplace(trackedBB, trackedVals);
              inst->eraseFromParent();
              break; // break out of bbTrackedVals for-loop
            }
          }
        }
        if (curr_BB_added)
          break; // break out of inst for-loop
      }
    }
  }

  return cpBBMap;
}

std::tuple<llvm::Value *, Value *>
SubroutineInjection::getOffsetArray(Value *v, Function &F)
{
  Value *offset = nullptr;
  Function::iterator BBIter;
  for (BBIter = F.begin(); BBIter != F.end(); ++BBIter)
  {
    BasicBlock *BB = &(*BBIter);
    BasicBlock::iterator instrIter;
    for (instrIter = BB->begin(); instrIter != BB->end(); ++instrIter)
    {
      Instruction *I = &(*instrIter);
      if (I == v)
      {
        // Found affectation
        if (I->getOpcode() == Instruction::GetElementPtr)
        {
          Value *value;
          std::tie(value, offset) = getOffsetArray(I->getOperand(0), F);
          int number_operands = I->getNumOperands();
          offset = I->getOperand(number_operands - 1);
          // int offset = I->getOperand(1);
          return std::tuple<llvm::Value *, Value *>{value, offset};
        }
        return std::tuple<llvm::Value *, Value *>{I, offset};
      }
    }
  }
  return std::tuple<llvm::Value *, Value *>{nullptr, offset};
}

int SubroutineInjection::insertIndexTracking(Function &F)
{
  /*
  Module *M = F.getParent();
  Function* func_stack_push = M->getFunction("push_stack");

  if(TrackIndexOption){
    #ifndef LLVM14_VER
      func_stack_push->addAttribute(AttributeList::FunctionIndex, Attribute::NoInline);
    #else
      func_stack_push->addFnAttr(Attribute::NoInline);
    #endif
  }
  */

  Function::iterator BBIter;
  std::cout << F.getName().str() << std::endl;
  for (BBIter = F.begin(); BBIter != F.end(); ++BBIter)
  {
    BasicBlock *BB = &(*BBIter);
    BasicBlock::iterator instrIter;
    for (instrIter = BB->begin(); instrIter != BB->end(); ++instrIter)
    {
      Instruction *I = &(*instrIter);
      if (I->getOpcode() == Instruction::Store)
      {
        // I->print(errs());
        // printf("\n");

        if (I->getOperand(0)->getType()->isPointerTy())
        {
          // Skip: we do not save memory addresses
          continue;
        }

        Value *value = nullptr;
        Value *offset = nullptr;
        // if(I->getOperand(1)->getType()->isPointerTy()){
        std::tie(value, offset) = getOffsetArray(I->getOperand(1), F);
        if (offset != nullptr)
        {
          printf("ID var array %p ID offset %p \n", value, offset);
          I->print(errs());
          printf("\n");
          value->print(errs());
          printf("\n");
          if (isa<AllocaInst>(value))
          {
            std::cout << "stack map  contains:\n";
            for (auto it = stacksMem.begin(); it != stacksMem.end(); ++it)
              std::cout << it->first << " => " << it->second << '\n';

            auto ite = stacksMem.find(value);
            if (ite == stacksMem.end())
            {
              std::cout << "! Can find Stack" << std::endl;
              continue;
            }

            // Retrieve index stack to push on
            Value *stack = stacksMem[value];
            Value *index = stacksIndex[value];
            Type *ArrayTy = stacksType[value];

            // Push the new index
            Type *integer32T = Type::getInt32Ty(F.getContext());
            // %idx_c = load i32, i32* %i
            Instruction *loadedAddr = new LoadInst(integer32T, index, "", false, I);
            // %idx_new = add nsw i32 %idx_c, 1
            IRBuilder<> IR(I);
            Value *Inc = IR.CreateAdd(IR.getInt32(1), loadedAddr);
            Instruction *storeSP = new StoreInst(Inc, index, I);
            // %y = getelementptr inbounds i32, i32* %x, i32 %idx_new
            Value *IndexTrunc = BinaryOperator::Create(Instruction::And, loadedAddr, IR.getInt32(stackArraySizeMask), "", I);
            Value *indexList[2] = {IR.getInt32(0), IndexTrunc}; // post inc
            // Value *indexList[2] = {IR.getInt32(0), loadedAddr};
            // Value *indexList[2] = {IR.getInt32(0), IR.getInt32(0)}; //pointer to base
            Instruction *elemPtrStore = GetElementPtrInst::CreateInBounds(ArrayTy, stack, ArrayRef<Value *>(indexList, 2), "idx_stack_", I);
            // store i32 {offset}, i32* %y
            Value *offset_val;
            if (offset->getType()->isIntegerTy())
            {
              if (offset->getType() != integer32T)
              {
                offset_val = CastInst::CreateIntegerCast(offset, integer32T, true, "", I);
              }
              else
              {
                offset_val = offset;
              }
            }
            else if (offset->getType()->isFloatingPointTy())
            {
              offset_val = CastInst::Create(Instruction::FPToSI, offset, integer32T, "castedOffset", I);
            }

            /*
            std::vector<Value*> call_params;
            call_params.push_back(elemPtrStore);
            call_params.push_back(index);
            call_params.push_back(offset_val);
            call_params.push_back(IR.getInt32(stackArraySize));

            for (unsigned i = 0; i != call_params.size();++i)
              std::cout << "i = " << i << "fun " << func_stack_push->getFunctionType()->getParamType(i)->getTypeID() << " param " << call_params[i]->getType()->getTypeID() << std::endl;

            CallInst* call1 = CallInst::Create(func_stack_push, call_params, "", I);
            */

            Instruction *storeInst = new StoreInst(offset_val, elemPtrStore, I);
          }
          else if (isa<LoadInst>(value))
          {
            LoadInst *LI = cast<LoadInst>(value);
            std::cout << "value->getOperand(0) = " << LI->getOperand(0) << std::endl;

            std::cout << "stack map  contains:\n";
            for (auto it = stacksMem.begin(); it != stacksMem.end(); ++it)
              std::cout << it->first << " => " << it->second << '\n';

            auto ite = stacksMem.find(LI->getOperand(0));
            if (ite == stacksMem.end())
            {
              std::cout << "! Can find Stack" << std::endl;
              continue;
            }

            // Retrieve index stack to push on
            Value *stack = stacksMem[LI->getOperand(0)];
            Value *index = stacksIndex[LI->getOperand(0)];
            Type *ArrayTy = stacksType[LI->getOperand(0)];

            // Push the new index
            Type *integer32T = Type::getInt32Ty(F.getContext());
            // %idx_c = load i32, i32* %i
            Instruction *loadedAddr = new LoadInst(integer32T, index, "", false, I);
            // %idx_new = add nsw i32 %idx_c, 1
            IRBuilder<> IR(I);
            Value *Inc = IR.CreateAdd(IR.getInt32(1), loadedAddr);
            Instruction *storeSP = new StoreInst(Inc, index, I);
            // %y = getelementptr inbounds i32, i32* %x, i32 %idx_new
            Value *IndexTrunc = BinaryOperator::Create(Instruction::And, loadedAddr, IR.getInt32(stackArraySizeMask), "", I);
            Value *indexList[2] = {IR.getInt32(0), IndexTrunc}; // post inc
            // Value *indexList[2] = {IR.getInt32(0), IR.getInt32(0)}; //pointer to base
            // Value *indexList[2] = {IR.getInt32(0), loadedAddr}; //post inc
            Instruction *elemPtrStore = GetElementPtrInst::CreateInBounds(ArrayTy, stack, ArrayRef<Value *>(indexList, 2), "idx_stack_", I);
            // store i32 {offset}, i32* %y
            Value *offset_val;
            if (offset->getType()->isIntegerTy())
            {
              if (offset->getType() != integer32T)
              {
                offset_val = CastInst::CreateIntegerCast(offset, integer32T, true, "", I);
              }
              else
              {
                offset_val = offset;
              }
            }
            else if (offset->getType()->isFloatingPointTy())
            {
              offset_val = CastInst::Create(Instruction::FPToSI, offset, integer32T, "castedOffset", I);
            }

            /*
            std::vector<Value*> call_params;
            call_params.push_back(elemPtrStore);
            call_params.push_back(index);
            call_params.push_back(offset_val);
            call_params.push_back(IR.getInt32(stackArraySize));
            CallInst* call1 = CallInst::Create(func_stack_push, call_params, "", I);
            */

            Instruction *storeInst = new StoreInst(offset_val, elemPtrStore, I);
          }
        }

        if (value == nullptr)
        {
          printf("Variable identifier not found. Skip!\n");
          I->print(errs());
          printf("\n");
          continue;
        }
      }
    }
  }
  return 1;
}

void SubroutineInjection::allocateindexStacks(std::set<const Value *> trackedVals, std::map<const Value *, const Value *> oldNewTrackedVals,
                                              std::map<const Value *, std::set<const Value *>> allTrackedValVersions,
                                              LiveValues::VariableDefMap valDefMap, LiveValues::VariableDefMap liveValDefMap,
                                              Value *ckptMemSegment, Function &F, Module &M)
{
  const DataLayout &DL = M.getDataLayout();
  BasicBlock *BB = &(*F.begin());
  Instruction *term = BB->getTerminator();

  auto cmp = [&](const Value *a, const Value *b)
  {
    std::string aName = JsonHelper::getOpName(a, &M).erase(0,1);
    std::string bName = JsonHelper::getOpName(b, &M).erase(0,1);
    return (aName.compare(bName)<0); };
  std::set<const Value *, decltype(cmp)> trackedValsOrdered(cmp);

  for (auto iter : trackedVals)
  {
    Value *trackedVal = const_cast<Value *>(&*iter);
    trackedValsOrdered.insert(trackedVal);
  }

  Type *ckptMemSegContainedType = ckptMemSegment->getType()->getContainedType(0);
  int ckptMemSegContainedTypeSize = DL.getTypeAllocSizeInBits(ckptMemSegContainedType) / 8;
  int valMemSegIndex = VALUES_START; // start index of "slots" for values in memory segment
  for (auto iter : trackedValsOrdered)
  {
    int numOfArrSlotsUsed = 1;
    Value *trackedVal = const_cast<Value *>(&*iter);
    std::string valTrackedName = JsonHelper::getOpName(trackedVal, &M).erase(0, 1);
    if (valTrackedName.find("mem_ckpt") != std::string::npos)
    {
      printf("mem_ckpt skip!");
      continue;
    }
    Type *valRawType = trackedVal->getType();
    bool isPointer = valRawType->isPointerTy();
    Type *containedType = isPointer ? valRawType->getContainedType(0) : valRawType;
    bool isPointerPointer = isPointer && containedType->isPointerTy();
    int valSizeBytes = liveValDefMap.at(trackedVal);

    if (isPointer)
    {
      const Value *originalTrackedVal = findKeyByValueInMap(trackedVal, allTrackedValVersions);
      std::set<const Value *> valVersions = allTrackedValVersions.at(originalTrackedVal);
      Value *trackedValDeref = getDerefValFromPointer(trackedVal, valVersions, &F);
      if (trackedValDeref != nullptr)
      {
        if (valDefMap.count(trackedValDeref))
        {
          // get number of ckpt_mem array slots used to store this element:
          valSizeBytes = valDefMap.at(trackedValDeref);
          numOfArrSlotsUsed = ceil((float)valSizeBytes / (float)ckptMemSegContainedTypeSize);
        }
      }
      //}
      int valSizeBytes = liveValDefMap.at(trackedVal);
      // const Value *originalTrackedVal = findKeyByValueInMap(trackedVal, allTrackedValVersions);
      // std::set<const Value*> valVersions = allTrackedValVersions.at(originalTrackedVal);
      // Value *trackedValDeref = getDerefValFromPointer(trackedVal, valVersions, &F);

      if (containedType->isArrayTy())
      {

        // if(containedType->getElementType()->isArrayTy())

        numOfArrSlotsUsed = ceil((float)valSizeBytes / (float)ckptMemSegContainedTypeSize);

        int containedTypeSize = DL.getTypeAllocSizeInBits(containedType) / 8;
        // int arraySize = 1024*128; //int(valSizeBytes / containedTypeSize);
        Type *ArrayTy = ArrayType::get(Type::getInt32Ty(F.getContext()), stackArraySize);
        std::string valName = JsonHelper::getOpName(trackedVal, &M).erase(0, 1);
        std::string fullName = valName + "_index_stack";
        AllocaInst *allocaInst = new AllocaInst(ArrayTy, 0, fullName, term);
        stacksMem.insert(std::pair<Value *, Value *>(trackedVal, allocaInst));
        std::string IndexName = valName + "_index_sp";
        auto index_size = llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), 1);
        AllocaInst *allocaInstSP = new AllocaInst(Type::getInt32Ty(F.getContext()), 0, index_size, IndexName, term);
        Instruction *storeInst = new StoreInst(llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), 0), allocaInstSP, term);
        stacksIndex.insert(std::pair<Value *, Value *>(trackedVal, allocaInstSP));
        stacksType.insert(std::pair<Value *, Type *>(trackedVal, ArrayTy));

        Value *storeLocation = trackedVal;
        // Instruction *loadedAddrS = new LoadInst(valRawType->getContainedType(0), trackedVal, "loaded."+valName, false, term);
        // storeLocation = loadedAddrS;

        Value *indexList[1] = {ConstantInt::get(Type::getInt32Ty(F.getContext()), valMemSegIndex)};
        Instruction *elemPtrStore = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment, ArrayRef<Value *>(indexList, 1), "idx_" + valName, term);

        int paddedValSizeBytes = (valSizeBytes < ckptMemSegContainedTypeSize) ? ckptMemSegContainedTypeSize : valSizeBytes;

        // create memcpy inst (autoconverts pointers to i8*)
#ifndef LLVM14_VER
        auto srcAlign = DL.getPrefTypeAlignment(storeLocation->getType());
        auto dstAlign = DL.getPrefTypeAlignment(elemPtrStore->getType());
#else
        MaybeAlign srcAlign = DL.getPrefTypeAlign(storeLocation->getType());
        MaybeAlign dstAlign = DL.getPrefTypeAlign(elemPtrStore->getType());
#endif
        IRBuilder<> builder(F.getContext());
        builder.SetInsertPoint(term);
        // #ifndef LLVM14_VER
        // 	CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value*>(elemPtrStore), storeLocation, paddedValSizeBytes, srcAlign, true);
        // #else
        CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value *>(elemPtrStore), dstAlign, storeLocation, srcAlign, paddedValSizeBytes, true);
        // #endif
      }
      else if (isPointerPointer)
      {
        // find value that this trackedVal points to
        if (trackedValDeref != nullptr)
        {
          if (valDefMap.count(trackedValDeref))
          {
            // get number of ckpt_mem array slots used to store this element:
            valSizeBytes = valDefMap.at(trackedValDeref);
            Type *containedType = trackedValDeref->getType()->getContainedType(0);
            int containedTypeSize = DL.getTypeAllocSizeInBits(containedType) / 8;
            // int arraySize = 1024*256;//1024;//int(valSizeBytes / containedTypeSize)
            Type *ArrayTy = ArrayType::get(Type::getInt32Ty(F.getContext()), stackArraySize);
            std::string valName = JsonHelper::getOpName(trackedValDeref, &M).erase(0, 1);
            std::string fullName = valName + "_index_stack";
            AllocaInst *allocaInst = new AllocaInst(ArrayTy, 0, fullName, term);
            stacksMem.insert(std::pair<Value *, Value *>(trackedVal, allocaInst));
            std::string IndexName = valName + "_index_sp";
            auto index_size = llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), 1);
            AllocaInst *allocaInstSP = new AllocaInst(Type::getInt32Ty(F.getContext()), 0, index_size, IndexName, term);
            Instruction *storeInst = new StoreInst(llvm::ConstantInt::get(Type::getInt32Ty(F.getContext()), 0), allocaInstSP, term);
            stacksIndex.insert(std::pair<Value *, Value *>(trackedVal, allocaInstSP));
            stacksType.insert(std::pair<Value *, Type *>(trackedVal, ArrayTy));

            // Initiate ckpt_mem with intial values (Required due to partial array checkpointing)
            Value *storeLocation = trackedVal;
            Instruction *loadedAddrS = new LoadInst(valRawType->getContainedType(0), trackedVal, "loaded." + valName, false, term);
            storeLocation = loadedAddrS;

            Value *indexList[1] = {ConstantInt::get(Type::getInt32Ty(F.getContext()), valMemSegIndex)};
            Instruction *elemPtrStore = GetElementPtrInst::CreateInBounds(ckptMemSegContainedType, ckptMemSegment, ArrayRef<Value *>(indexList, 1), "idx_" + valName, term);

            int paddedValSizeBytes = (valSizeBytes < ckptMemSegContainedTypeSize) ? ckptMemSegContainedTypeSize : valSizeBytes;

            // create memcpy inst (autoconverts pointers to i8*)
#ifndef LLVM14_VER
            auto srcAlign = DL.getPrefTypeAlignment(storeLocation->getType());
            auto dstAlign = DL.getPrefTypeAlignment(elemPtrStore->getType());
#else
            MaybeAlign srcAlign = DL.getPrefTypeAlign(storeLocation->getType());
            MaybeAlign dstAlign = DL.getPrefTypeAlign(elemPtrStore->getType());
#endif
            IRBuilder<> builder(F.getContext());
            builder.SetInsertPoint(term);
            // #ifndef LLVM14_VER
            //             CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value*>(elemPtrStore), storeLocation, paddedValSizeBytes, srcAlign, true);
            // #else
            CallInst *memcpyCall = builder.CreateMemCpy(reinterpret_cast<Value *>(elemPtrStore), dstAlign, storeLocation, srcAlign, paddedValSizeBytes, true);
            // #endif
          }
        }
      }
    }
    valMemSegIndex += numOfArrSlotsUsed;
  }
}

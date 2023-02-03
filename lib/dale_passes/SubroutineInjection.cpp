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

#include "json/JsonHelper.h"

#include <cstddef>
#include <exception>
#include <iostream>
#include <sys/stat.h>
#include <fstream>

#define DEBUG_TYPE "module-transformation-pass"

using namespace llvm;

char SubroutineInjection::ID = 0;

// This is the core interface for pass plugins. It guarantees that 'opt' will
// recognize LegacyHelloWorld when added to the pass pipeline on the command
// line, i.e.  via '--legacy-hello-world'
static RegisterPass<SubroutineInjection>
    X("subroutine-injection", "Subroutine Injection",
      false, // This pass does modify the CFG => false
      false // This pass is not a pure analysis pass => false
    );

namespace llvm {
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

  // load live values analysis results.
  FuncBBLiveValsByName = JsonHelper::getLiveValuesResultsFromJson("live_values.json");
  JsonHelper::printJsonMap(FuncBBLiveValsByName);
  std::cout << "===========\n";

  // load Tracked values analysis results.
  FuncBBTrackedValsByName = JsonHelper::getTrackedValuesResultsFromJson("tracked_values.json");
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
  LiveValues::FullLiveValsData fullLivenessData = JsonHelper::getFuncBBLiveValsMap(FuncValuePtrs, FuncBBLiveValsByName, M);
  LiveValues::LivenessResult funcBBLiveValsMap = fullLivenessData.first;
  LiveValues::FuncVariableDefMap funcVariableDefMap = fullLivenessData.second;

  for (auto fIter : funcVariableDefMap)
  {
    Function *F = fIter.first;
    LiveValues::VariableDefMap sizeMap = fIter.second;
    std::cout<<"SIZE ANALYSIS RESULTS FOR FUNC "<<JsonHelper::getOpName(F, &M)<<" :"<<std::endl;
    for (auto vIter : sizeMap)
    {
      Value * val = const_cast<Value*>(vIter.first);
      int size = vIter.second;
      std::cout<<"  "<<JsonHelper::getOpName(val, &M)<<" : "<<size<<" bytes"<<std::endl;
    }
  }

  bool isModified = injectSubroutines(M, funcBBTrackedValsMap, funcBBLiveValsMap);

  printCheckPointBBs(funcBBTrackedValsMap, M);

  return isModified;
}

void
SubroutineInjection::print(raw_ostream &O, const Function *F) const
{
  /** TODO: implement me! */
  return;
}

void
SubroutineInjection::printTrackedValues(raw_ostream &O, const LiveValues::TrackedValuesResult &LVResult) const
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
      for(valIt = trackedVals.cbegin(); valIt != trackedVals.cend(); valIt++)
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

bool SubroutineInjection::isEntryBlock(const BasicBlock* BB) const {
   const Function *F = BB->getParent();
   assert(F && "Block must have a parent function to use this API");
   return BB == &F->getEntryBlock();
}

/// Set every incoming value(s) for block \p BB to \p V.
void SubroutineInjection::setIncomingValueForBlock(PHINode *phi, const BasicBlock *BB, Value *V) {
    assert(BB && "PHI node got a null basic block!");
    bool Found = false;
    for (unsigned Op = 0, NumOps = phi->getNumOperands(); Op != NumOps; ++Op)
      if (phi->getIncomingBlock(Op) == BB) {
        Found = true;
        phi->setIncomingValue(Op, V);
      }
    (void)Found;
    assert(Found && "Invalid basic block argument to set!");
}

bool SubroutineInjection::hasNPredecessorsOrMore(const BasicBlock* BB, unsigned N) {
  return hasNItemsOrMore(pred_begin(BB), pred_end(BB), N);
}

bool
SubroutineInjection::injectSubroutines(
  Module &M,
  const LiveValues::TrackedValuesResult &funcBBTrackedValsMap,
  const LiveValues::LivenessResult &funcBBLiveValsMap
)
{
  bool isModified = false;
  for (auto &F : M.getFunctionList())
  {
    // Check function linkage
    // We do not analyze external functions
    if(F.getLinkage() == F.LinkOnceODRLinkage)
      continue;
    
    std::string funcName = JsonHelper::getOpName(&F, &M);
    std::cout << "\nFunction " << funcName << " ==== \n";
    if (!funcBBTrackedValsMap.count(&F))
    {
      std::cout << "WARNING: No BB tracked values data for '" << funcName << "'\n";
      continue;
    }
    LiveValues::BBTrackedVals bbTrackedVals = funcBBTrackedValsMap.at(&F);

    // get vars for instruction building
    LLVMContext &context = F.getContext();
    IRBuilder<> builder(context);

    // get function parameters
    std::set<Value *> funcParams = getFuncParams(&F);

    // get Value* to ckpt_mem memory segment pointer
    StringRef segmentName = "ckpt_mem";
    Type *ptrType = Type::getInt32PtrTy(context);
    Value *ckptMemSegment = getCkptMemSegmentPtr(funcParams, segmentName, &M);
    if (!ckptMemSegment)
    {
      std::cout << "WARNING: Could not get pointer to memory segment of name '" << segmentName.str() << "'" << std::endl;
      continue;
    }

    // get memory segment contained type
    Type *ckptMemSegmentContainedType = ckptMemSegment->getType()->getContainedType(0); // %ckpt_mem should be <primitive>** type.
    std::string type_str;
    llvm::raw_string_ostream rso(type_str);
    ckptMemSegmentContainedType->print(rso);
    std::cout<<"MEM SEG CONTAINED TYPE = "<<rso.str()<<std::endl;;

    /** TODO: get list of const func params to ignore */
    // std::set<Value *> constFuncParams = getConstFuncParams(funcParams);

    // get entryBB (could be %entry or %entry.upper, depending on whether entryBB has > 1 successors)
    BasicBlock *entryBB = &*(F.begin());
    std::cout<<"ENTRY_BB_UPPER="<<JsonHelper::getOpName(entryBB, &M)<<"\n";
    if (getBBSuccessors(entryBB).size() < 1)
    {
      std::cout << "WARNING: Function '" << JsonHelper::getOpName(&F, &M) << "' only comprises 1 basic block. Ignore Function." << std::endl;
      continue;
    }

    bool hasInjectedSubroutinesForFunc = false;

    /*
    = 0: get candidate checkpoint BBs
    ============================================================================= */
    // filter for BBs that only have one successor.
    LiveValues::BBTrackedVals filteredBBTrackedVals = getBBsWithOneSuccessor(bbTrackedVals);
    // filteredBBTrackedVals = removeSelectedTrackedVals(filteredBBTrackedVals, constFuncParams);
    filteredBBTrackedVals = removeNestedPtrTrackedVals(filteredBBTrackedVals);
    filteredBBTrackedVals = removeBBsWithNoTrackedVals(filteredBBTrackedVals);
    CheckpointBBMap bbCheckpoints = chooseBBWithCheckpointDirective(filteredBBTrackedVals, &F);
    
    if (bbCheckpoints.size() == 0)
    {
      // Could not find BBs with checkpoint directive
      std::cout << "WARNING: Could not find any valid BBs with checkpoint directive in function '" << funcName << std::endl;
      continue;
    }
    int currMinValsCount = bbCheckpoints.begin()->second.size();
    std::cout<< "#currNumOfTrackedVals=" << currMinValsCount << "\n";
    // store new added BBs (saveBB, restoreBB, junctionBB) for this current checkpoint, and the restoreControllerBB
    std::set<BasicBlock *> newBBs;

    /*
    = 1: get pointers to Entry BB and checkpoint BBs
    ============================================================================= */
    std::cout << "Checkpoint BBs:\n";
    std::set<BasicBlock*> checkpointBBPtrSet = getCkptBBsInFunc(&F, bbCheckpoints);

    /*
    = 2. Add block on exit edge of entry.upper block (pre-split)
    ============================================================================= */
    BasicBlock *restoreControllerBB = nullptr;
    BasicBlock *restoreControllerSuccessor = *succ_begin(entryBB);;
    std::string restoreControllerBBName = funcName.erase(0,1) + ".restoreControllerBB";
    restoreControllerBB = splitEdgeWrapper(entryBB, restoreControllerSuccessor, restoreControllerBBName, M);
    if (restoreControllerBB)
    {
      isModified = true;
      restoreControllerSuccessor = restoreControllerBB->getSingleSuccessor();
      std::cout<<"successor of restoreControllerBB=" << JsonHelper::getOpName(restoreControllerSuccessor, &M) << "\n";
      newBBs.insert(restoreControllerBB);
    }
    else
    {
      // Split-edge fails for adding BB after function entry block => skip this function
      std::cout << "WARNING: Split-edge for restoreControllerBB failed for function '" << funcName << "'" << std::endl;
      continue;
    }

    
    /*
    = 3: Add subroutines for each checkpoint BB, one checkpoint at a time:
    ============================================================================= */
    // store saveBB-checkpointBB pairing
    std::map<BasicBlock *, BasicBlock *> saveBBcheckpointBBMap;
    // store subroutine BBs for each checkpoint
    std::map<BasicBlock *, CheckpointTopo> checkpointBBTopoMap;

    // store live-out data for all saveBBs, restoreBBs and junctionBBs in current function.
    std::map<BasicBlock *, std::set<const Value *>> funcSaveBBsLiveOutMap;
    std::map<BasicBlock *, std::set<const Value *>> funcRestoreBBsLiveOutMap;
    std::map<BasicBlock *, std::set<const Value *>> funcJunctionBBsLiveOutMap;

    // store map<junctionBB, map<trackedVal, phi>>
    std::map<BasicBlock *, std::map<Value *, PHINode *>> funcJunctionBBPhiValsMap;

    for (auto bbIter : checkpointBBPtrSet)
    {
      BasicBlock *checkpointBB = &(*bbIter);
      std::string checkpointBBName = JsonHelper::getOpName(checkpointBB, &M).erase(0,1);
      std::vector<BasicBlock *> checkpointBBSuccessorsList = getBBSuccessors(checkpointBB);

      /*
      ++ 3.1: Add saveBB on exit edge of checkpointed block
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      for (auto succIter : checkpointBBSuccessorsList)
      {
        // Insert the new saveBB into the edge between thisBB and a successorBB:
        BasicBlock *successorBB = &*succIter;
        BasicBlock *saveBB = splitEdgeWrapper(checkpointBB, successorBB, checkpointBBName + ".saveBB", M);
        if (saveBB)
        {
          saveBBcheckpointBBMap.emplace(saveBB, checkpointBB);
          newBBs.insert(saveBB);
        }
        else
        {
          continue;
        }

        /*
        ++ 3.2: For each successful saveBB, add restoreBBs and junctionBBs
        +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
        std::string checkpointBBName = JsonHelper::getOpName(checkpointBB, &M).erase(0,1);
        // create mediator BB as junction to combine output of saveBB and restoreBB
        BasicBlock *resumeBB = *(succ_begin(saveBB)); // saveBBs should only have one successor.
        BasicBlock *junctionBB = splitEdgeWrapper(saveBB, resumeBB, checkpointBBName + ".junctionBB", M);
        BasicBlock *restoreBB;
        if (junctionBB)
        {
          // create restoreBB for this saveBB
          restoreBB = BasicBlock::Create(context, checkpointBBName + ".restoreBB", &F, nullptr);
          // have successfully inserted all components (BBs) of subroutine
          BranchInst::Create(junctionBB, restoreBB);
          CheckpointTopo checkpointTopo = {
            .checkpointBB = checkpointBB,
            .saveBB = saveBB,
            .restoreBB = restoreBB,
            .junctionBB = junctionBB,
            .resumeBB = resumeBB
          };
          checkpointBBTopoMap.emplace(checkpointBB, checkpointTopo);
          newBBs.insert(restoreBB);
          newBBs.insert(junctionBB);
        }
        else
        {
          // failed to inject mediator BB => skip this checkpoint
          // remove saveBB from saveBBcheckpointBBMap
          saveBBcheckpointBBMap.erase(saveBB);
          /** TODO: remove saveBB for this checkpoint from CFG */
          continue; 
        }

        /*
        ++ 3.3: Populate saveBB and restoreBB with load and store instructions.
        +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
        std::set<const Value *> trackedVals = bbCheckpoints.at(checkpointBB);
      
        std::set<const Value *> saveBBLiveOutSet;
        std::set<const Value *> restoreBBLiveOutSet;
        std::set<const Value *> junctionBBLiveOutSet;

        // stores map<trackedVal, phi> pairings for current junctionBB
        std::map<Value *, PHINode *> trackedValPhiValMap;

        Instruction *saveBBTerminator = saveBB->getTerminator();
        Instruction *restoreBBTerminator = restoreBB->getTerminator();
        
        int valMemSegIndex = VALUES_START; // start index of "slots" for values in memory segment
        for (auto iter : trackedVals)
        {
          /*
          --- 3.3.2: Set up vars used for instruction creation
          ----------------------------------------------------------------------------- */
          Value *trackedVal = const_cast<Value*>(&*iter); /** TODO: verify safety of cast to non-const!! this is dangerous*/
          std::string valName = JsonHelper::getOpName(trackedVal, &M).erase(0,1);
          Type *valRawType = trackedVal->getType();
          bool isPointer = valRawType->isPointerTy();
          Type *containedType = isPointer ? valRawType->getContainedType(0) : valRawType;

          // init store location (index) in memory segment:
          Value *indexList[1] = {ConstantInt::get(Type::getInt32Ty(context), valMemSegIndex)};

          /*
          --- 3.3.3: Create instructions to store value to memory segment
          ----------------------------------------------------------------------------- */
          Value *saveVal = nullptr;
          if (isPointer)
          {
            // trackedVal is a pointer type, so need to dereference via load instruction to save the value it points to
            saveVal = new LoadInst(Type::getInt32Ty(context), trackedVal, "deref_"+valName, false, saveBBTerminator);
          }
          else
          {
            saveVal = trackedVal;
          }
          Instruction *elemPtrStore = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                        ArrayRef<Value *>(indexList, 1), "idx_"+valName,
                                                                        saveBBTerminator);
          StoreInst *storeInst = new StoreInst(saveVal, elemPtrStore, false, saveBBTerminator);

          /*
          --- 3.3.4: Create instructions to load value from memory.
          ----------------------------------------------------------------------------- */
          Value *restoredVal = nullptr;
          Instruction *elemPtrLoad = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                      ArrayRef<Value *>(indexList, 1), "idx_"+valName,
                                                                      restoreBBTerminator);
          LoadInst *loadInst = new LoadInst(containedType, elemPtrLoad, "load."+valName, false, restoreBBTerminator);
          restoredVal = loadInst;
          if (isPointer)
          {
            /** TODO: figure out what to use for `unsigned AddrSpace` */
            // trackedVAl
            AllocaInst *allocaInstR = new AllocaInst(containedType, 0, "alloca."+valName, restoreBBTerminator);
            StoreInst *storeToPtr = new StoreInst(loadInst, allocaInstR, false, restoreBBTerminator);
            restoredVal = allocaInstR;
          }

          /*
          --- 3.3.5: Add phi node into junctionBB to merge loaded val & original val
          ----------------------------------------------------------------------------- */
          PHINode *phi = PHINode::Create(trackedVal->getType(), 2, "new."+valName, junctionBB->getTerminator());
          phi->addIncoming(trackedVal, saveBB);
          phi->addIncoming(restoredVal, restoreBB);

          /*
          --- 3.3.6: Configure live-out sets for saveBB, restoreBB and junctionBB; init trackValPhiValMap.
          ----------------------------------------------------------------------------- */
          /* Since the live-out data for all other BBs use the original value version too (and algo checks
          live-out using this live-out data), it would be more consistent to use original value version
          as live-out of saveBB, restoreBB & junctionBB instead of the new phi. */
          saveBBLiveOutSet.insert(trackedVal);
          restoreBBLiveOutSet.insert(trackedVal);
          // Insert original value version as live-out of junctionBB (phi is just a new version of the original live-out val)
          junctionBBLiveOutSet.insert(trackedVal);
          trackedValPhiValMap[trackedVal] = phi;

          valMemSegIndex ++;
        }
        funcSaveBBsLiveOutMap[saveBB] = saveBBLiveOutSet;
        funcRestoreBBsLiveOutMap[restoreBB] = restoreBBLiveOutSet;
        funcJunctionBBsLiveOutMap[junctionBB] = junctionBBLiveOutSet;
        funcJunctionBBPhiValsMap[junctionBB] = trackedValPhiValMap;

        /*
        --- 3.3.6: save isComplete in memorySegment[1]
        ----------------------------------------------------------------------------- */
        Value *isCompleteIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), IS_COMPLETE)};
        Value *isComplete = ConstantInt::get(Type::getInt32Ty(context), 1);
        // insert inst into saveBB
        Instruction *elemPtrIsCompleteS = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                          ArrayRef<Value *>(isCompleteIndexList, 1),
                                                                          "idx_isComplete", saveBBTerminator);
        StoreInst *storeIsCompleteS = new StoreInst(isComplete, elemPtrIsCompleteS, false, saveBBTerminator);

        /*
        ++ 3.4: Propagate loaded values from restoreBB across CFG.
        +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
        for (auto iter : trackedVals)
        {
          Value *trackedVal = const_cast<Value*>(&*iter); /** TODO: verify safety of cast to non-const!! this is dangerous*/
          std::string valName = JsonHelper::getOpName(trackedVal, &M).erase(0,1);
          
          // for each BB, keeps track of versions of values that have been encountered in this BB (including the original value)
          std::map<BasicBlock *, std::set<Value *>> visitedBBs;

          // get phi value in junctionBB that merges original & loaded versions of trackVal
          PHINode *phi = funcJunctionBBPhiValsMap.at(junctionBB).at(trackedVal);

          propagateRestoredValuesBFS(resumeBB, junctionBB, trackedVal, phi,
                                    &newBBs, &visitedBBs,
                                    funcBBLiveValsMap, funcSaveBBsLiveOutMap, 
                                    funcRestoreBBsLiveOutMap, funcJunctionBBsLiveOutMap);
        }

        // clear newBBs set after this checkpoint has been processed (to prepare for next checkpoint)
        newBBs.erase(saveBB);
        newBBs.erase(restoreBB);
        newBBs.erase(junctionBB);
      }
      break; // FOR TESTING (limits to 1 checkpoint; propagation algo does not work with > 1 ckpt)
    }

    /*
    = 4: Add checkpoint IDs & heartbeat to saveBBs and restoreBBs
    ============================================================================= */
    CheckpointIdBBMap ckptIDsCkptToposMap = getCheckpointIdBBMap(checkpointBBTopoMap, M);
    // printCheckpointIdBBMap(ckptIDsCkptToposMap, &F);
    for (auto iter : ckptIDsCkptToposMap)
    {
      /*
      ++ 4.1: for each ckpt's saveBB, add inst to store ckpt id
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      unsigned ckpt_id = iter.first;
      BasicBlock *saveBB = iter.second.saveBB;
      BasicBlock *restoreBB = iter.second.restoreBB;
      Instruction *saveBBTerminator = saveBB->getTerminator();
      Instruction *restoreBBTerminator = restoreBB->getTerminator();

      Value *ckptIDIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), CKPT_ID)};
      Instruction *elemPtrCkptId = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                    ArrayRef<Value *>(ckptIDIndexList, 1),
                                                                    "idx_ckpt_id", saveBBTerminator);
      Value *ckpt_id_val = {ConstantInt::get(Type::getInt32Ty(context), ckpt_id)};
      StoreInst *storeCkptId = new StoreInst(ckpt_id_val, elemPtrCkptId, false, saveBBTerminator);

      /*
      ++ 4.2: for each ckpt's saveBB & restoreBB, add inst to increment heartbeat
      +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
      /** TODO: think about how to avoid overflow */
      // add inst to saveBB
      Value *heartbeatIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), HEARTBEAT)};
      Value *add_rhs_operand = ConstantInt::get(Type::getInt32Ty(context), 1);
      Instruction *elemPtrHeartbeatS = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                            ArrayRef<Value *>(heartbeatIndexList, 1),
                                                                            "idx_heartbeat", saveBBTerminator);
      LoadInst *loadHeartbeatS = new LoadInst(Type::getInt32Ty(context), elemPtrHeartbeatS, "load.heartbeat", false, saveBBTerminator);
      builder.SetInsertPoint(saveBBTerminator);
      Value* addInstS = builder.CreateAdd(loadHeartbeatS, add_rhs_operand, "heartbeat_incr");
      StoreInst *storeHeartBeatS = new StoreInst(addInstS, elemPtrHeartbeatS, false, saveBBTerminator);
      // add inst to restoreBB
      Instruction *elemPtrHeartbeatR = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                              ArrayRef<Value *>(heartbeatIndexList, 1),
                                                                              "idx_heartbeat", restoreBBTerminator);
      LoadInst *loadHeartbeatR = new LoadInst(Type::getInt32Ty(context), elemPtrHeartbeatR, "load.heartbeat", false, restoreBBTerminator);  
      builder.SetInsertPoint(restoreBBTerminator);     
      Value* addInstR = builder.CreateAdd(loadHeartbeatR, add_rhs_operand, "heartbeat_incr");
      StoreInst *storeHeartBeatR = new StoreInst(addInstR, elemPtrHeartbeatR, false, restoreBBTerminator);
    }

    /*
    = 5: Populate restoreControllerBB with switch instructions.
    ============================================================================= */
    /* a. if CheckpointID indicates no checkpoint has been saved, continue to computation.
       b. if CheckpointID exists, jump to restoreBB for that CheckpointID. */

    // load CheckpointID from memory
    Instruction *terminatorInst = restoreControllerBB->getTerminator();
    Value *ckptIDIndexList[1] = {ConstantInt::get(Type::getInt32Ty(context), CKPT_ID)};
    Instruction *elemPtrLoad = GetElementPtrInst::CreateInBounds(Type::getInt32Ty(context), ckptMemSegment,
                                                                ArrayRef<Value *>(ckptIDIndexList, 1), "idx_ckpt_id_load",
                                                                terminatorInst);
    LoadInst *loadCheckpointID = new LoadInst(Type::getInt32Ty(context), elemPtrLoad, "load.ckpt_id", false, terminatorInst);
  
    /*
    ++ 5.b: Create switch instruction in restoreControllerBB
    +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ */
    unsigned int numCases = ckptIDsCkptToposMap.size();
    builder.SetInsertPoint(terminatorInst);
    SwitchInst *switchInst = builder.CreateSwitch(loadCheckpointID, restoreControllerSuccessor, numCases);
    ReplaceInstWithInst(terminatorInst, switchInst);
    for (auto iter : ckptIDsCkptToposMap)
    {
      ConstantInt *checkpointID = ConstantInt::get(Type::getInt32Ty(context), iter.first);
      CheckpointTopo checkpointTopo = iter.second;
      BasicBlock *restoreBB = checkpointTopo.restoreBB;
      switchInst->addCase(checkpointID, restoreBB); // insert new jump to basic block
    }

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
      std::cout << "WARNING: None of BBs in function '" << funcName <<"' result in successful subroutine injection. No checkpoints added to function.\n";
    }
  }
  return isModified;
}

void
SubroutineInjection::propagateRestoredValuesBFS(BasicBlock *startBB, BasicBlock *prevBB, Value *oldVal, Value *newVal,
                                                std::set<BasicBlock *> *newBBs,
                                                // std::set<BasicBlock *> *visitedBBs,
                                                std::map<BasicBlock *, std::set<Value *>> *visitedBBs,
                                                const LiveValues::LivenessResult &funcBBLiveValsMap,
                                                std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                                std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                                std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap)
{
  std::queue<SubroutineInjection::BBUpdateRequest> q;

  // track versions of values in current "thread/path" of propagation
  std::set<Value *> valueVersions;
  valueVersions.insert(oldVal);
  valueVersions.insert(newVal);

  SubroutineInjection::BBUpdateRequest updateRequest = {
    .startBB = startBB,
    .currBB = startBB,
    .prevBB = prevBB,
    .oldVal = oldVal,
    .newVal = newVal,
    .valueVersions = valueVersions
  };
  q.push(updateRequest);
  
  while(!q.empty())
  {
    SubroutineInjection::BBUpdateRequest updateRequest = q.front();
    q.pop();
    processUpdateRequest(updateRequest, &q, newBBs, visitedBBs,
                        funcBBLiveValsMap, funcSaveBBsLiveOutMap,
                        funcRestoreBBsLiveOutMap, funcJunctionBBsLiveOutMap);
  }
}

void
SubroutineInjection::processUpdateRequest(SubroutineInjection::BBUpdateRequest updateRequest,
                                          std::queue<SubroutineInjection::BBUpdateRequest> *q,
                                          std::set<BasicBlock *> *newBBs,
                                          // std::set<BasicBlock *> *visitedBBs,
                                          std::map<BasicBlock *, std::set<Value *>> *visitedBBs,
                                          const LiveValues::LivenessResult &funcBBLiveValsMap,
                                          std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                          std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                          std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap)
{
  BasicBlock *startBB = updateRequest.startBB;
  BasicBlock *currBB = updateRequest.currBB;
  BasicBlock *prevBB = updateRequest.prevBB;
  Value *oldVal = updateRequest.oldVal;
  Value *newVal = updateRequest.newVal;
  std::set<Value *> valueVersions = updateRequest.valueVersions;

  Function *F = currBB->getParent();
  Module *M = F->getParent();

  std::cout<<"---\n";
  std::cout<<"prevBB:{"<<JsonHelper::getOpName(prevBB, M)<<"}\n";
  std::cout<<"currBB:{"<<JsonHelper::getOpName(currBB, M)<<"}\n";
  std::cout<<"oldVal="<<JsonHelper::getOpName(oldVal, M)<<"; newVal="<<JsonHelper::getOpName(newVal, M)<<"\n";

  // stop after we loop back to (and re-process) startBB
  bool isStop = currBB == startBB && visitedBBs->count(currBB);
  std::cout<<"isStop="<<isStop<<"\n";

  // if reached exit BB, do not process request
  if (currBB->getTerminator()->getNumSuccessors() == 0) isStop = true;

  // tracks history of the valueVersions set across successive visits of this BB.
  std::set<Value *> bbValueVersions = getOrDefault(currBB, visitedBBs);  // marks BB as visited (if not already)
  // stop propagation if val versions in valueVersions and bbValueVersions match exactly.
  bool isAllContained = true;
  for (auto valIter : bbValueVersions)
  {
    isAllContained = isAllContained && valueVersions.count(&*valIter);
  }
  if (isAllContained && bbValueVersions.size() == valueVersions.size()) isStop = true;

  if (!newBBs->count(currBB)
      && hasNPredecessorsOrMore(currBB, 2)
      && 1 < numOfPredsWhereVarIsLiveOut(currBB, oldVal, funcBBLiveValsMap,
                                  funcSaveBBsLiveOutMap, funcRestoreBBsLiveOutMap, 
                                  funcJunctionBBsLiveOutMap)
  )
  {
    if (isPhiInstExistForIncomingBBForTrackedVal(valueVersions, currBB, prevBB))
    {
      std::cout<<"MODIFY EXISTING PHI NODE\n";
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
              bbValueVersions.insert(valueVersions.begin(), valueVersions.end());   // copy contents of valueVersions into bbValueVersions
              updateMapEntry(currBB, bbValueVersions, visitedBBs);

              std::string phiName = JsonHelper::getOpName(phi, M);
              std::string incomingBBName = JsonHelper::getOpName(incomingBB, M);
              std::string valueName = JsonHelper::getOpName(incomingValue, M);
              std::string newValName = JsonHelper::getOpName(newVal, M);
              std::cout<<"modify "<<phiName<<": change ["<<valueName<<", "<<incomingBBName<<"] to ["<<newValName<<", "<<incomingBBName<<"]\n";
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
      std::cout<<"ADD NEW PHI NODE\n";      
      // make new phi node
      std::string bbName = JsonHelper::getOpName(currBB, M).erase(0,1);
      std::string newValName = JsonHelper::getOpName(newVal, M).erase(0,1);
      std::vector<BasicBlock *> predecessors = getBBPredecessors(currBB);
      Instruction *firstInst = &*(currBB->begin());
      PHINode *newPhi = PHINode::Create(oldVal->getType(), predecessors.size(), newValName + ".phi", firstInst);
      std::cout<<"added new phi: "<<JsonHelper::getOpName(dyn_cast<Value>(newPhi), M)<<"\n";
      for (BasicBlock *predBB : predecessors)
      {
        // if pred has exit edge to startBB, add new entry in new phi instruction.
        Value *phiInput = (predBB == prevBB) ? newVal : oldVal;
        std::cout<<"  add to phi: {"<<JsonHelper::getOpName(phiInput, M)<<", "<<JsonHelper::getOpName(predBB, M)<<"}\n";
        newPhi->addIncoming(phiInput, predBB);
        valueVersions.insert(phiInput);
      }

      // update each subsequent instruction in this BB from oldVal to newPhi
      for (auto instIter = currBB->begin(); instIter != currBB->end(); instIter++)
      {
        Instruction *inst = &*instIter;
        if (inst != dyn_cast<Instruction>(newPhi))   // don't update new phi instruction
        {
          std::cout<<"  try updating inst '"<<JsonHelper::getOpName(dyn_cast<Value>(inst), M)<<"'\n";
          replaceOperandsInInst(inst, oldVal, newPhi);
        }
        if (valueVersions.count(inst)) isStop = true;   // inst is a definition of one of the value versions.
      }
      valueVersions.insert(newPhi);
      bbValueVersions.insert(valueVersions.begin(), valueVersions.end());   // copy contents of valueVersions into bbValueVersions
      updateMapEntry(currBB, bbValueVersions, visitedBBs);

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
              .valueVersions = valueVersions
            };
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
      if (valueVersions.count(inst)) isStop = true;  // inst is a definition of one of the value versions.
    }
    valueVersions.insert(newVal);
    bbValueVersions.insert(valueVersions.begin(), valueVersions.end());   // copy contents of valueVersions into bbValueVersions
    updateMapEntry(currBB, bbValueVersions, visitedBBs);

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
            .valueVersions = valueVersions
          };
          q->push(newUpdateRequest);
        }
      }
    }
  }

  std::cout<<"@@@ valueVersions: (";
  for (auto valIter : valueVersions)
  {
    Value *val = &*valIter;
    std::cout<<JsonHelper::getOpName(val, M)<<", ";
  }
  std::cout<<")"<<std::endl;
  std::cout<<"@@@ bbValueVersions: (";
  for (auto valIter : bbValueVersions)
  {
    Value *val = &*valIter;
    std::cout<<JsonHelper::getOpName(val, M)<<", ";
  }
  std::cout<<")"<<std::endl;
}

void
SubroutineInjection::updateMapEntry(BasicBlock *key, std::set<Value *> newVal, std::map<BasicBlock *, std::set<Value *>> *map)
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

unsigned
SubroutineInjection::numOfPredsWhereVarIsLiveOut(BasicBlock *BB, Value *val, const LiveValues::LivenessResult &funcBBLiveValsMap,
                                                std::map<BasicBlock *, std::set<const Value *>> &funcSaveBBsLiveOutMap,
                                                std::map<BasicBlock *, std::set<const Value *>> &funcRestoreBBsLiveOutMap,
                                                std::map<BasicBlock *, std::set<const Value *>> &funcJunctionBBsLiveOutMap)
{
  unsigned count = 0;
  Function *F = BB->getParent();
  for (auto iter = pred_begin(BB); iter != pred_end(BB); iter++)
  {
    BasicBlock *pred = *iter;
    std::set<const Value *> liveOutSet;
    if (funcJunctionBBsLiveOutMap.count(pred))
    {
      // pred is a junctionBB
      liveOutSet = funcJunctionBBsLiveOutMap.at(pred);
    }
    else if (funcSaveBBsLiveOutMap.count(pred)) {
      // pred is a saveBB
      liveOutSet = funcSaveBBsLiveOutMap.at(pred);
    }
    else if (funcRestoreBBsLiveOutMap.count(pred))
    {
      // pred is a restoreBB
      liveOutSet = funcRestoreBBsLiveOutMap.at(pred);
    }
    else if (funcBBLiveValsMap.at(F).count(pred))
    {
      // pred is an original BB
      liveOutSet = funcBBLiveValsMap.at(F).at(pred).liveOutVals;
    }

    if (liveOutSet.count(val)) count ++;
  }
  return count;
}

bool
SubroutineInjection::isPhiInstExistForIncomingBBForTrackedVal(std::set<Value *> valueVersions, BasicBlock *currBB, BasicBlock *prevBB)
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

bool
SubroutineInjection::isPhiInstForValExistInBB(Value *val, BasicBlock *BB)
{
  for (auto phiIter = BB->phis().begin(); phiIter != BB->phis().end(); phiIter++)
  {
    PHINode *phi = &*phiIter;
    User::op_iterator operandIter;
    for (operandIter = phi->op_begin(); operandIter != phi->op_end(); operandIter++)
    {
      const Value *operand = *operandIter;
      if (operand == val) return true; 
    }
  }
  return false;
}

bool
SubroutineInjection::replaceOperandsInInst(Instruction *inst, Value *oldVal, Value *newVal)
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

SubroutineInjection::CheckpointIdBBMap
SubroutineInjection::getCheckpointIdBBMap(
  std::map<BasicBlock *, SubroutineInjection::CheckpointTopo> &checkpointBBTopoMap,
  Module &M
) const
{
  uint8_t checkpointIDCounter = 1;  // id=0 means no ckpt has been saved
  CheckpointIdBBMap checkpointIdBBMap;
  std::map<BasicBlock *, SubroutineInjection::CheckpointTopo>::iterator iter;
  for (iter = checkpointBBTopoMap.begin(); iter != checkpointBBTopoMap.end(); ++iter)
  {
    SubroutineInjection::CheckpointTopo checkpointTopo = iter->second;
    BasicBlock *saveBB = checkpointTopo.saveBB;
    BasicBlock *restoreBB = checkpointTopo.restoreBB;
    BasicBlock *junctionBB = checkpointTopo.junctionBB;
    // append checkpoint id to saveBB and restoreBB names
    std::string saveBBName = JsonHelper::getOpName(saveBB, &M).erase(0,1) + ".id" + std::to_string(checkpointIDCounter);
    dyn_cast<Value>(saveBB)->setName(saveBBName);
    std::string restoreBBName = JsonHelper::getOpName(restoreBB, &M).erase(0,1) + ".id" + std::to_string(checkpointIDCounter);
    dyn_cast<Value>(restoreBB)->setName(restoreBBName);
    std::string junctionBBName = JsonHelper::getOpName(junctionBB, &M).erase(0,1) + ".id" + std::to_string(checkpointIDCounter);
    dyn_cast<Value>(junctionBB)->setName(junctionBBName);

    checkpointIdBBMap.emplace(checkpointIDCounter, checkpointTopo);
    checkpointIDCounter ++;
  }
  return checkpointIdBBMap;
}

/** TODO: remove Module param when removing print statement */
Instruction *
SubroutineInjection::getCmpInstForCondiBrInst(Instruction *condiBranchInst, Module &M) const
{
  Value* condition = dyn_cast<BranchInst>(condiBranchInst)->getCondition();
  Instruction *cmp_instr = nullptr;
  while(cmp_instr == nullptr)
  {
    // attempt to find branch instr's corresponding cmp instr
    Instruction *instr = condiBranchInst->getPrevNode();
    
    if (instr == nullptr) break;  // have reached list head; desired cmp instr not found
    
    Value *instr_val = dyn_cast<Value>(instr);
    std::cout << "?" << JsonHelper::getOpName(instr_val, &M) << "\n";
    if ((isa <ICmpInst> (instr) || isa <FCmpInst> (instr)) && instr == condition)
    {
      cmp_instr = instr;
    }
  }
  return cmp_instr;
}

std::set<BasicBlock*>
SubroutineInjection::getCkptBBsInFunc(Function *F, CheckpointBBMap &bbCheckpoints) const
{
  std::set<BasicBlock*> checkpointBBPtrSet;

  Function::iterator funcIter;
  for (funcIter = F->begin(); funcIter != F->end(); ++funcIter)
  {
    BasicBlock* bb_ptr = &(*funcIter);
    if (bbCheckpoints.count(bb_ptr))
    {
      checkpointBBPtrSet.insert(bb_ptr);
      Module *M = F->getParent();
      std::cout<<JsonHelper::getOpName(bb_ptr, M)<<"\n";
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
    StringRef argName = JsonHelper::getOpName(arg, F->getParent()).erase(0,1);
    std::cout<<"ARG: "<<argName.str()<<std::endl;
    argSet.insert(arg);
  }
  return argSet;
}

std::set<Value *>
SubroutineInjection::getConstFuncParams(std::set<Value *> funcParams) const
{
  std::set<Value *> constParams;
  for (auto iter : funcParams)
  {
    Value *param = &*iter;
    /** TODO: find out how to find any/all 'const' function params */
    if(isa<Argument>(param) && cast<Argument>(param)->onlyReadsMemory()) // this only applies for pointer types!
    {
      constParams.insert(param);
    }
  }
  return constParams;
}

Value *
SubroutineInjection::getCkptMemSegmentPtr(std::set<Value *> funcParams, StringRef segmentName, Module *M) const
{
  for (auto iter : funcParams)
  {
    Value *arg = &*iter;
    StringRef argName = JsonHelper::getOpName(arg, M).erase(0,1);
    if (argName.equals(segmentName)) 
    {
      std::cout<<"Found target memeory segment ARG: "<<argName.str()<<std::endl;
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


BasicBlock* SubroutineInjection::SplitEdgeCustom(BasicBlock *BB, BasicBlock *Succ, DominatorTree *DT,
					   LoopInfo *LI) const {
  unsigned SuccNum = GetSuccessorNumber(BB, Succ);

  // If this is a critical edge, let SplitCriticalEdge do it.
  if (SplitCriticalEdge(BB->getTerminator(), SuccNum, CriticalEdgeSplittingOptions(DT, LI)
                                                .setPreserveLCSSA()))
    return BB->getTerminator()->getSuccessor(SuccNum);

  // Otherwise, if BB has a single successor, split it at the bottom of the
  // block.
  assert(BB->getTerminator()->getNumSuccessors() == 1 &&
         "Should have a single succ!");
  return SplitBlock(BB, BB->getTerminator(), DT, LI);
}

BasicBlock*
SubroutineInjection::splitEdgeWrapper(BasicBlock *edgeStartBB, BasicBlock *edgeEndBB, std::string checkpointName, Module &M) const
{
  /** TODO: figure out whether to specify DominatorTree, LoopInfo and MemorySSAUpdater params */
  //BasicBlock *insertedBB = SplitEdge(edgeStartBB, edgeEndBB, nullptr, nullptr, nullptr, checkpointName);
  BasicBlock *insertedBB = SplitEdgeCustom(edgeStartBB, edgeEndBB, nullptr, nullptr);
  insertedBB->setName(checkpointName);
  if (!insertedBB)
  {
    // SplitEdge can fail, e.g. if the successor is a landing pad
    std::cerr << "Split-edge failed between BB{" 
              << JsonHelper::getOpName(edgeStartBB, &M) 
              << "} and BB{" 
              << JsonHelper::getOpName(edgeEndBB, &M)
              <<"}\n";
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
    std::map<std::string, const Value*> valuePtrsMap;

    Function::iterator bbIter;
    for (bbIter = F.begin(); bbIter != F.end(); ++bbIter)
    {
      const BasicBlock* bb = &(*bbIter);
      std::set<const Value*> trackedVals;
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
                                    if (a.second.size() < minValsCount) return false;
                                    if (b.second.size() < minValsCount) return true;
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
    const std::set<const Value*> &trackedValues = funcIter->second;

    std::set<const Value*> filteredTrackedValues;
    for (auto valIter : trackedValues)
    {
      const Value * val = &*valIter;
      if (ignoredValues.count(const_cast<Value*>(val))) /** TODO: verify safety of cast to non-const!! this is dangerous*/
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
SubroutineInjection::removeNestedPtrTrackedVals(LiveValues::BBTrackedVals bbTrackedVals) const
{
  LiveValues::BBTrackedVals filteredBBTrackedVals;
  LiveValues::BBTrackedVals::const_iterator funcIter;
  for (funcIter = bbTrackedVals.cbegin(); funcIter != bbTrackedVals.cend(); ++funcIter)
  {
    const BasicBlock *BB = funcIter->first;
    const Module *M = BB->getParent()->getParent();
    const std::set<const Value*> &trackedValues = funcIter->second;

    std::set<const Value*> filteredTrackedValues;
    for (auto valIter : trackedValues)
    {
      const Value * val = &*valIter;
      Type *valType = val->getType();
      if (valType->isPointerTy() && valType->getContainedType(0)->getNumContainedTypes() > 0)
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
    const std::set<const Value*> &trackedValues = funcIter->second;
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

void
SubroutineInjection::printCheckPointBBs(const CheckpointFuncBBMap &fBBMap, Module &M) const
{
  CheckpointFuncBBMap::const_iterator funcIt;
  CheckpointBBMap::const_iterator bbIt;
  std::set<const Value *>::const_iterator valIt;
  for (funcIt = fBBMap.cbegin(); funcIt != fBBMap.cend(); funcIt++){
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

void
SubroutineInjection::printCheckpointIdBBMap(SubroutineInjection::CheckpointIdBBMap map, Function *F)
{
  Module *M = F->getParent();
  std::cout << "\n----CHECKPOINTS for '" << JsonHelper::getOpName(F, M) << "'----\n";
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

void
SubroutineInjection::printFuncValuePtrsMap(SubroutineInjection::FuncValuePtrsMap map, Module &M)
{
  SubroutineInjection::FuncValuePtrsMap::const_iterator iter;
  for (iter = map.cbegin(); iter != map.cend(); ++iter)
  {
    const Function *func = iter->first;
    std::map<std::string, const Value*> valuePtrsMap = iter->second;
    std::cout << func->getName().str() << ":\n";

    std::map<std::string, const Value*>::iterator it;
    for (it = valuePtrsMap.begin(); it != valuePtrsMap.end(); ++it)
    {
      std::string valName = it->first;
      const Value* val = it->second;
      std::cout << "  " << valName << " {" << JsonHelper::getOpName(val, &M) << "}\n";
    }
    // std::cout << "## size = " << valuePtrsMap.size() << "\n";
  }
}


SubroutineInjection::CheckpointBBMap
SubroutineInjection::chooseBBWithCheckpointDirective(LiveValues::BBTrackedVals bbTrackedVals, Function *F) const
{
  std::cout << "\n\n\n\n **************** chooseBBWithCheckpointDirective ********* \n\n" << std::endl;
  Module *M = F->getParent();
  CheckpointBBMap cpBBMap;

  // Search for checkpoint directive in BBs of function F
  std::cout << "Function Name = " << F->getName().str() << std::endl;
  Function::iterator funcIter;
  LiveValues::BBTrackedVals::const_iterator bbIt;

  for (funcIter = F->begin(); funcIter != F->end(); ++funcIter)
  {
    BasicBlock* BB = &(*funcIter);
    std::cout<<"BB="<<JsonHelper::getOpName(BB, M)<<std::endl;
    bool curr_BB_added = false;
    BasicBlock::iterator instrIter;
    for (instrIter = BB->begin(); instrIter != BB->end(); ++instrIter)
    {
      Instruction* inst =  &(*instrIter);
      if(inst->getOpcode() == Instruction::Call || inst->getOpcode() == Instruction::Invoke)
      {
        StringRef name = cast<CallInst>(*inst).getCalledFunction()->getName();
        if(name.contains("checkpoint")){
          std::cout << "\n contain checkpoint \n";
          // ensure that we have tracked-values information on the selected checkpoint BB
          for (bbIt = bbTrackedVals.cbegin(); bbIt != bbTrackedVals.cend(); bbIt++)
          {
            const BasicBlock *trackedBB = bbIt->first;
            const std::set<const Value *> &trackedVals = bbIt->second;
            std::cout<<"  trackedBB="<<JsonHelper::getOpName(trackedBB, M)<<std::endl;
            if (trackedBB == BB)
            {
              std::cout << "\n BB added" << std::endl;
              curr_BB_added = true;
              cpBBMap.emplace(trackedBB, trackedVals);
              inst->eraseFromParent();
              break;  // break out of bbTrackedVals for-loop
            }
          }
        }
        if(curr_BB_added) break; // break out of inst for-loop
      }
    }
  }

  return cpBBMap;
}

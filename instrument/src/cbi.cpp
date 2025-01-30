#include "Util/SVFUtil.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/LLVMModule.h"
#include "Graphs/SVFG.h"
#include "Graphs/ICFG.h"
#include <llvm/Support/Path.h> // for llvm::sys::path::filename, etc.
#include "llvm/Support/raw_ostream.h" // Include for raw_string_ostream
#include "llvm/Support/raw_os_ostream.h"
#include "WPA/Andersen.h"
#include "SABER/LeakChecker.h"
#include "llvm/IR/CFG.h"
#include <fstream>
#include <sstream>
#include <ctime>

#include <stack>
#include <regex>

#include "Graphs/VFG.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVF-LLVM/ICFGBuilder.h"
#include "Util/Options.h"
#include "SVFIR/PAGBuilderFromFile.h"
#include "SABER/SaberSVFGBuilder.h"

using namespace SVF;
using namespace llvm;
using namespace std;

#define MAP_SIZE_POW2       16
#define MAP_SIZE            (1 << MAP_SIZE_POW2)
#define AFL_R(x) (random() % (x))
#define SUF_NUM             500 
#define SUF_NUM_CFG         50000 
#define PRE_NUM_CFG         50000
#define TARGETS_NUM         10 
#define TARGETS_NUM_ORIG         32 

static llvm::cl::opt<std::string> InputFilename(cl::Positional,
        llvm::cl::desc("<input bitcode>"), llvm::cl::init("-"));
static llvm::cl::opt<std::string> TargetsFile("targets", llvm::cl::desc("specify targes file"), llvm::cl::Required);


std::set<const BasicBlock*> targets_llvm_bb;
std::set<const BasicBlock*> targets_DT_bb;
std::set<const BasicBlock*> targets_DT_bb_orig;
int targets_DT_bb_num = TARGETS_NUM;
int targets_DT_bb_num_orig = TARGETS_NUM;
std::set<const Function*> targets_llvm_func;
std::map<const Function *, std::set<const BasicBlock *>> targets_llvm_func_bbs;
std::map<const BasicBlock *, const BasicBlock *> origBB2DTBB;
SVFModule* svfModule;
SVFG *svfg;
ICFG* icfg;
Module* M;
LLVMContext* C;


std::list<const VFGNode *> VFGNodes;
std::map<uint32_t,std::set<const BasicBlock*>> targets_pre_cfg_bb;
std::map<uint32_t,std::set<const BasicBlock*>> targets_suf_cfg_bb;
std::map<uint32_t,std::set<const BasicBlock*>> targets_suf_data_bb;
std::map<uint32_t,std::set<const BasicBlock*>> targets_suf_data_bb_target;
std::map<const BasicBlock *,uint32_t> BB_IDs;
std::map<uint32_t,double> BBID2dis;
std::set<uint32_t> test;
std::set<const BasicBlock*> all_pre_cfg_bb;
std::set<const BasicBlock*> all_suf_cfg_bb;
std::set<const BasicBlock*> all_suf_data_bb;
uint32_t test_dfs=0;

std::map<const ICFGNode *, double > preNodeMap;
std::map<NodeID, std::map<const ICFGNode *, double >> targetID2preNodeMap;
std::map<const BasicBlock *, double > preNodeMapBB;
std::map<NodeID, std::map<const BasicBlock *, double >> targetID2preNodeMapBB;
std::map<const BasicBlock *, double > HMpreNodeMapBB;


std::string getDebugInfo(BasicBlock* bb) {
	for (BasicBlock::iterator it = bb->begin(), eit = bb->end(); it != eit; ++it) {
		Instruction* inst = &(*it);
		std::string str=LLVMUtil::getSourceLoc(inst);
		if (str != "{  }" && str.find("ln: 0  cl: 0") == str.npos)
			return str;
	}
	return "{ }";
}

void instrument_orig() {
	ofstream outfile4("bbinfo.txt", std::ios::out | std::ios::app);
	uint32_t bb_id = 0;

  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
			BasicBlock* bb = &*(bit);

      const BasicBlock *constbb = (const BasicBlock *)bb;
      if(getDebugInfo(bb).find("/usr/") == string::npos ){
        outfile4 << bb_id << getDebugInfo(bb) << std::endl;
        if(BB_IDs.find(constbb) == BB_IDs.end()){
          BB_IDs[constbb] = bb_id;
          bb_id++;
        }
      }
    }
	}
	outfile4.close();
}

void instrument() {
	ofstream outfile("distance.txt", std::ios::out | std::ios::app);
	ofstream outfile2("functions.txt", std::ios::out | std::ios::app);
	ofstream outfile3("targets.txt", std::ios::out | std::ios::app);
	ofstream outfile5("targets_id.txt", std::ios::out | std::ios::app);
	ofstream outfile7("targets_id_orig.txt", std::ios::out | std::ios::app);
	uint32_t bb_id = 0;
	uint32_t target_id = 0;
	uint32_t target_id_orig = 0;
  uint32_t target_id_orig_toomany = 0;

  IntegerType *Int8Ty = IntegerType::getInt8Ty(*C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(*C);

	GlobalVariable *AFLMapPtr = (GlobalVariable*)M->getOrInsertGlobal("__afl_area_ptr",PointerType::get(IntegerType::getInt8Ty(*C), 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
    });

  IntegerType *LargestType = Int64Ty;
  ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);
  ConstantInt *MapTargetLoc = ConstantInt::get(LargestType, MAP_SIZE + 24);
  ConstantInt *MapCrashLoc = ConstantInt::get(LargestType, MAP_SIZE + 56);
  ConstantInt *MapDistLoc = ConstantInt::get(LargestType, MAP_SIZE);
  ConstantInt *One = ConstantInt::get(LargestType, 1);

  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
			BasicBlock* bb = &*(bit);
      const BasicBlock *constbb = (const BasicBlock *)bb;
      bb_id=BB_IDs[constbb];
        BasicBlock::iterator IP = bb->getFirstInsertionPt();
        llvm::IRBuilder<> IRB(&(*IP));

				/* Load SHM pointer */

				LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
				MapPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

        const BasicBlock *tempBB = (const BasicBlock *)bb;
        llvm::Value* value = llvm::ConstantInt::get(LargestType, 0);
        if( !target_id_orig_toomany && targets_DT_bb_orig.count(tempBB)){
          Value *MapTargetPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapTargetLoc), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapTargetPtr);
          MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          ConstantInt *bitValue = llvm::ConstantInt::get(LargestType, 1 << target_id_orig);
          value = IRB.CreateOr(MapCnt, bitValue);

          IRB.CreateStore(value, MapTargetPtr)
              ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          target_id_orig++;
          if(target_id_orig >= TARGETS_NUM_ORIG - 1 ){
            errs() << "target_id_orig>TARGETS_NUM_ORIG\n";
            target_id_orig_toomany = 1;
          }
          outfile7 << bb_id << std::endl;
        }

      uint32_t distance = -1;
      std::map<NodeID, uint32_t> distance_targets;

      if(HMpreNodeMapBB.count(bb)){
        distance = (uint32_t)(100 * HMpreNodeMapBB[bb]);

        int i = -1;
        for (auto target_bb: targets_DT_bb)
        {
          i++;
          if(i>=TARGETS_NUM){
            exit(1);
          }
          NodeID target_bb_id = BB_IDs[target_bb];
          if(!targetID2preNodeMapBB[target_bb_id].count(bb)){
            continue;
          }
          distance_targets[target_bb_id] = (uint32_t)(100 * targetID2preNodeMapBB[target_bb_id][bb]);

          ConstantInt *Distance = ConstantInt::get(LargestType, (unsigned) distance_targets[target_bb_id]);

          /* Add distance to shm[MAPSIZE] */

          ConstantInt *MapDistLoc_index = ConstantInt::get(LargestType, MAP_SIZE + 64 + 16 * i);
          ConstantInt *MapCntLoc_index = ConstantInt::get(LargestType, MAP_SIZE + 64 + 8 + 16 * i);

          Value *MapDistPtr = IRB.CreateBitCast(
            IRB.CreateGEP(MapPtr, MapDistLoc_index), LargestType->getPointerTo());
          LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
          MapDist->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
          IRB.CreateStore(IncrDist, MapDistPtr)
            ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          /* Increase count at shm[MAPSIZE + (4 or 8)] */

          Value *MapCntPtr = IRB.CreateBitCast(
            IRB.CreateGEP(MapPtr, MapCntLoc_index), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
          MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
          IRB.CreateStore(IncrCnt, MapCntPtr)
            ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

        }

				ConstantInt *Distance = ConstantInt::get(LargestType, (unsigned) distance);

				/* Add distance to shm[MAPSIZE] */

				Value *MapDistPtr = IRB.CreateBitCast(
					IRB.CreateGEP(MapPtr, MapDistLoc), LargestType->getPointerTo());
				LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
				MapDist->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
				IRB.CreateStore(IncrDist, MapDistPtr)
					->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				/* Increase count at shm[MAPSIZE + (4 or 8)] */

				Value *MapCntPtr = IRB.CreateBitCast(
					IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
				LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
				MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
				IRB.CreateStore(IncrCnt, MapCntPtr)
					->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				if (distance == 0 && target_id < TARGETS_NUM) {
					ConstantInt *TFlagLoc = ConstantInt::get(LargestType, MAP_SIZE + 16 + 16 + 16 + 16 + TARGETS_NUM * 16 + target_id);
					Value* TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
					ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);
					IRB.CreateStore(FlagOne, TFlagPtr)
						->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

					outfile3 << target_id << " " << getDebugInfo(bb) << std::endl;
          outfile5 << bb_id << std::endl;
					target_id++;
				}

				outfile << bb_id << " " << distance << " ";
				outfile << 0 << " "; 
				outfile << getDebugInfo(bb) << std::endl;
			}
      if(getDebugInfo(bb).find("/usr/") == string::npos ){
        BBID2dis[bb_id] = distance;
      }
    }
	}

	outfile.close();
	outfile2.close();
	outfile3.close();
	outfile5.close();
	outfile7.close();
}


void instrumentSuffix() {
  ofstream outfile("suffix.txt", std::ios::out | std::ios::app);
	ofstream outfile2("prefix.txt", std::ios::out | std::ios::app);
	ofstream outfile3("suffix_data.txt", std::ios::out | std::ios::app);

  IntegerType *Int64Ty = IntegerType::getInt64Ty(*C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(*C);
  GlobalVariable *AFLMapPtrSufBB = (GlobalVariable*)M->getOrInsertGlobal("__afl_area_ptr_suf_bb",PointerType::get(IntegerType::getInt8Ty(*C), 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr_suf_bb");
    });
  
  GlobalVariable *AFLMapPtr = (GlobalVariable*)M->getOrInsertGlobal("__afl_area_ptr",PointerType::get(IntegerType::getInt8Ty(*C), 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
    });
  IntegerType *LargestType = Int64Ty;  
  ConstantInt *MapCntLocSuf = ConstantInt::get(LargestType, MAP_SIZE + 32);
  ConstantInt *One = ConstantInt::get(LargestType, 1);
  
  uint32_t bb_id = 0;
  uint32_t suf_bb_id = 0;
  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
      
        BasicBlock *bb = &*(bit);
        if(!BB_IDs.count(bb))
          continue;
        if(test.find(BB_IDs[bb])!=test.end()){
          ;
        }
        test.insert(BB_IDs[bb]);

        
        if (all_suf_cfg_bb.find(bb) != all_suf_cfg_bb.end()){
          BasicBlock::iterator IP3 = bb->getFirstInsertionPt();
          llvm::IRBuilder<> IRB3(&(*IP3));
          llvm::LoadInst *MapPtrSufBB = IRB3.CreateLoad(AFLMapPtrSufBB);
          ConstantInt *cur_id = llvm::ConstantInt::get(IntegerType::getInt32Ty(*C), suf_bb_id);

          llvm::Value *MapPtrIdxSufBB = IRB3.CreateGEP(MapPtrSufBB, cur_id);
          llvm::LoadInst *CounterBB = IRB3.CreateLoad(MapPtrIdxSufBB);
          llvm::Value *IncrBB = IRB3.CreateAdd(CounterBB, ConstantInt::get(Int8Ty, 1));
          IRB3.CreateStore(IncrBB, MapPtrIdxSufBB)
              ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));
          suf_bb_id++;
          if(suf_bb_id >= MAP_SIZE){
            suf_bb_id = 0;
            errs() << "suf_bb_id reset\n";
            exit(1);
          }

        /* Load SHM pointer */

				LoadInst *MapPtr = IRB3.CreateLoad(AFLMapPtr);
				MapPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

        
				/* Increase count at shm[MAPSIZE + (4 or 8)] */

				Value *MapCntPtrSuf = IRB3.CreateBitCast(
					IRB3.CreateGEP(MapPtr, MapCntLocSuf), LargestType->getPointerTo());
				LoadInst *MapCntSuf = IRB3.CreateLoad(MapCntPtrSuf);
				MapCntSuf->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				Value *IncrCntSuf = IRB3.CreateAdd(MapCntSuf, One);
				IRB3.CreateStore(IncrCntSuf, MapCntPtrSuf)
					->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));


        }
    }
  }
  outfile << suf_bb_id<< " hello" << std::endl;
  outfile2 << " hello" << std::endl;
  outfile3 << " hello" << std::endl;

  for(auto tbb:targets_llvm_bb){
    uint32_t target_bb_id = BB_IDs[tbb];
    // errs() << target_bb_id << "\n";
    for (auto sufbb : targets_suf_cfg_bb[target_bb_id])
    {
      uint32_t suffix_bb_id = BB_IDs[sufbb];
      outfile << target_bb_id << " " << suffix_bb_id << " " << std::endl;
    }
  }
  for(auto tbb:targets_llvm_bb){
    uint32_t target_bb_id = BB_IDs[tbb];
    for (auto sufbb : targets_pre_cfg_bb[target_bb_id])
    {
      uint32_t suffix_bb_id = BB_IDs[sufbb];
      outfile2 << target_bb_id << " " << suffix_bb_id << " " << std::endl;
    }
  }
  for(auto tbb:targets_llvm_bb){
    const BasicBlock *dtbb = origBB2DTBB[tbb];
    uint32_t target_bb_id_dt = BB_IDs[dtbb];
    uint32_t target_bb_id = BB_IDs[tbb];
    string filename = to_string(target_bb_id_dt) + "_suffix_data.txt";
    ofstream outfile5(filename.c_str(), std::ios::out | std::ios::app);

    for (auto sufbb : targets_suf_data_bb[target_bb_id])
    {
      uint32_t suffix_bb_id = BB_IDs[sufbb];
      outfile3 << target_bb_id << " " << suffix_bb_id << " " << std::endl;
      targets_suf_data_bb_target[target_bb_id_dt].insert(sufbb);
      outfile5 << target_bb_id_dt << " " << suffix_bb_id << " " << std::endl;

    }

    outfile5.close();
  }

  outfile.close();
  outfile2.close();
  outfile3.close();

}

void findTargetControl(std::vector<NodeID> x){
    
    // Sets to keep track of visited nodes during predecessor and successor traversals
    set<const ICFGNode *> isvisited_pre;
    set<const ICFGNode *> isvisited_suf;

  // Iterate through the basic blocks that are targets (targets_DT_bb)
  std::cout << "--- Searching for control flow paths to targets in findTargetControl ---" << std::endl;
  for(const BasicBlock* BB:targets_DT_bb){
    // Print out BB's id 
    std::cout << "BB from targets_DT_bb: " << BB_IDs[BB] << std::endl;

    // Get the last instruction in the basic block
    const Instruction *lastInstr = BB->getTerminator();
    
    // Get the corresponding ICFGNode for the last instruction
    NodeID id = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(lastInstr))->getId();
    ICFGNode *iNode = icfg->getICFGNode(id);
    // Retrieve the corresponding SVFBasicBlock and LLVM BasicBlock
    const SVFBasicBlock *svfbb = iNode->getBB();
    const BasicBlock *BB_target = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));

    // Get the unique BB ID of the target basic block
    uint32_t taget_bb_id = BB_IDs[BB_target];

    std::cout << "Target BB ID: " << taget_bb_id << std::endl;

    // Flags to control predecessor and successor exploration
    bool sufFlag = 1;   
    bool preFlag = 1;

    // Check if the node has already been visited during forward traversal
    if(isvisited_suf.find(iNode)!=isvisited_suf.end()){
      sufFlag = 0; // If visited, skip forward traversal
    }else{
      isvisited_suf.clear(); // Otherwise, clear the visited set for a fresh forward traversal
    }

    // Check if the node has already been visited during backward traversal
    if(isvisited_pre.find(iNode)!=isvisited_pre.end()){
      isvisited_pre.clear(); // Always clear for backward traversal, regardless of prior visits in this loop's iteration.
    }else{
      isvisited_pre.clear();
    }

    // Temporary sets to store predecessor and forward (successor) traversal (BFS)
    std::set<const BasicBlock*> tmp_pre_bbs;
    std::set<const BasicBlock*> tmp_suf_bbs;

    // Worklists for backward (predecessor) and successor traversal
    FIFOWorkList<const ICFGNode *> worklist;
    FIFOWorkList<const SVF::ICFGNode *> worklist_suf;

    // Initialize worklists and maps for backward exploration
    worklist.push(iNode);
     // Initialize maps to store distances from target to predecessor nodes/basic blocks
    targetID2preNodeMap[taget_bb_id][iNode] = 0;
    targetID2preNodeMapBB[taget_bb_id][BB] = 0;
    // Add the initial basic block to the temporary set for backward traversal
    tmp_pre_bbs.insert(BB);

    // Initialize the forward worklist with the current ICFG node
    worklist_suf.push(iNode);

    // Sets to track caller nodes and functions
    set<const ICFGNode *> caller;
    set<const SVFFunction *> caller_func;

    // Counter for predecessor exploration
    int pre_num_cfg = 0;

    // Backward traversal () predecessor from the target node
    while(!worklist.empty() && preFlag && (pre_num_cfg<PRE_NUM_CFG)){
      pre_num_cfg++;
      const ICFGNode *iNode = worklist.pop(); // Get the next node from the worklist
      isvisited_pre.insert(iNode); // Mark the node as visited

      const BasicBlock *nowBB = NULL;
      if(iNode->getBB()){
        // Get the LLVM BasicBlock corresponding to the current ICFG node
        nowBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(iNode->getBB()));
      }

      // Iterate through the predecessors of the current node
      for(ICFGNode::const_iterator it = iNode->InEdgeBegin(), eit = iNode->InEdgeEnd(); it != eit; ++it)
      {
        ICFGEdge *edge = *it;
        ICFGNode *preNode = edge->getSrcNode(); // Get the predecessor node

         // If the predecessor has already been visited, skip it
        if(isvisited_pre.find(preNode) != isvisited_pre.end()){
          continue;
        }

        const IntraICFGNode *intraNode = NULL;
        const BasicBlock *callBB = NULL;
        const BasicBlock *preBB = NULL;

        if(preNode->getBB()){
          // Get the LLVM BasicBlock corresponding to the predecessor ICFG node
          preBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(preNode->getBB()));
        }

        // Handle return nodes (special case for inter-procedural analysis), if the predecessor is a return node (RetICFGNode).
        if(RetICFGNode * retNode = dyn_cast<RetICFGNode>(preNode)){ 
          const ICFGNode *callICFGNode = retNode->getCallICFGNode(); // Get the corresponding call node
          worklist.push(callICFGNode); // Add the call node to the worklist
          if(callICFGNode->getBB()){
            // Get the LLVM BasicBlock of the call site
            callBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(callICFGNode->getBB()));
          }

          // Update distance to call site BB
          if(callBB == nowBB){
            ; // Same BB, no distance change
          }else if(targetID2preNodeMapBB[taget_bb_id].count(callBB)){ // 1 if callBB exists in the map by count().
            // If callBB already in map, take the minimum distance.
            // E.g., if a new distance (adding 1, one step further aways from the target node) is shoter than the current distance, update the map with the new distance.
            // Otherwise, keep the existing distance.
            targetID2preNodeMapBB[taget_bb_id][callBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 < targetID2preNodeMapBB[taget_bb_id][callBB] ? targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 : targetID2preNodeMapBB[taget_bb_id][callBB];

          }else{
            // Otherwise, add callBB to map with distance from current BB + 1
            targetID2preNodeMapBB[taget_bb_id][callBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1;
          }

          // Iterate through predecessors of the return node to identify caller functions
          for(ICFGNode::const_iterator it = retNode->InEdgeBegin(), eit = retNode->InEdgeEnd(); it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunExitICFGNode *FunExitNode = NULL;
            if(FunExitNode = dyn_cast<FunExitICFGNode>(edge->getSrcNode())) {
              // If predecessor is a function exit node, add the call site and function to caller sets
              caller.insert(callICFGNode);
              caller_func.insert(FunExitNode->getFun());
            }
          }
        }
        // Handle call nodes (special case for inter-procedural analysis)
        else if(CallICFGNode* callICFGNode= dyn_cast<CallICFGNode>(preNode)){
          // if the predecessor is a call node, 
          if(caller_func.count(iNode->getFun())){
            // If the caller function is already in the set, skip the call node
            if(caller.find(callICFGNode) == caller.end()){
              continue;
            }
          }
        }

        // Add the predecessor to the worklist for further exploration
        worklist.push(preNode);
        
        // Update distance to predecessor BB
        if(preBB == nowBB){
          ; // Same BB, no distance change
        }else if(targetID2preNodeMapBB[taget_bb_id].count(preBB)){
          // If preBB already in map, take minimum distance
          targetID2preNodeMapBB[taget_bb_id][preBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 < targetID2preNodeMapBB[taget_bb_id][preBB] ? targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 : targetID2preNodeMapBB[taget_bb_id][preBB];
        }else{
          // Otherwise, add preBB to map with distance from current BB + 1
          targetID2preNodeMapBB[taget_bb_id][preBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1;
        }
        
      }
    }

    // If backward traversal was performed (preFlag is true)
    if(preFlag){
      /// Collect all LLVM Values
      for(auto it = isvisited_pre.begin(), eit = isvisited_pre.end(); it!=eit; ++it)
      {
        const ICFGNode *node = *it;
        const IntraICFGNode *intraNode = NULL;
        // Check if the node is an intra-procedural node
        if (intraNode= dyn_cast<IntraICFGNode>(node)){
          // Get the LLVM Instruction and its BasicBlock
          const Instruction *inst = cast<const Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(intraNode->getInst()));
          if (inst)
          {
            const BasicBlock *BB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(intraNode->getBB()));
            // Add the BasicBlock to the temporary set
            tmp_pre_bbs.insert(BB);
          }
        }
      }
      // Update the set of predecessor basic blocks for the current target
      targets_pre_cfg_bb[taget_bb_id].insert(tmp_pre_bbs.begin(), tmp_pre_bbs.end());
      // Update the global set of all predecessor basic blocks
      all_pre_cfg_bb.insert(tmp_pre_bbs.begin(), tmp_pre_bbs.end());
    }

    // Set to track callee functions during forward traversal
    set<FunEntryICFGNode *> callee;

    // Counter for the number of forward traversal steps (limited by SUF_NUM_CFG)
    int suf_num_cfg = 0;

    // Forward traversal (BFS) from the target node
    while(!worklist_suf.empty() && sufFlag &&(suf_num_cfg<SUF_NUM_CFG)){
      suf_num_cfg++;
      const ICFGNode *iNode = worklist_suf.pop();// Get the next node from the worklist
      isvisited_suf.insert(iNode); // Mark the node as visited

      // Handle call nodes (special case for inter-procedural analysis)
      if(const CallICFGNode * callNode = dyn_cast<const CallICFGNode>(iNode)){
        worklist_suf.push(callNode->getRetICFGNode()); // Add the return node to the worklist

        // Iterate through successors of the call node to identify callee functions
        for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit = callNode->OutEdgeEnd(); it != eit; ++it)
        {
          ICFGEdge *edge = *it;
          FunEntryICFGNode *FunEntryNode = NULL;
          if(FunEntryNode = dyn_cast<FunEntryICFGNode>(edge->getDstNode())) {
            // If successor is a function entry node, add it to the callee set
            callee.insert(FunEntryNode);
          }
        }

      }
      // Iterate through the successors of the current node - using OutEdgeBegin() and OutEdgeEnd() to get the successors
      for(ICFGNode::const_iterator it = iNode->OutEdgeBegin(), eit = iNode->OutEdgeEnd(); it != eit; ++it)
      {
        ICFGEdge *edge = *it;
        ICFGNode *sufNode = edge->getDstNode(); // Get the successor node

        // If the successor has already been visited, skip it
        if(isvisited_suf.find(sufNode) != isvisited_suf.end()){
          continue;
        }

        // Handle call nodes (similar to above)
        if(CallICFGNode * callNode = dyn_cast<CallICFGNode>(sufNode)){
          worklist_suf.push(callNode->getRetICFGNode());
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                            callNode->OutEdgeEnd();
              it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = NULL;
            if(FunEntryNode = dyn_cast<FunEntryICFGNode>(edge->getDstNode())) {
              callee.insert(FunEntryNode);
            }
          }

        }
        // Handle function exit nodes that corresponds to a return statement (or the implicit return at the end of a void function).
        else if(FunExitICFGNode* funExitNode = dyn_cast<FunExitICFGNode>(sufNode)){
          FunEntryICFGNode *funEntryNode = icfg->getFunEntryICFGNode(funExitNode->getFun());
          if(callee.find(funEntryNode)!=callee.end()){
            continue;
          }
        }
        // Add the successor to the worklist for further exploration
        worklist_suf.push(sufNode);

      }
    }

    // If forward traversal was performed (sufFlag is true)
    if(sufFlag){
      /// Collect all LLVM Values
      for(auto it = isvisited_suf.begin(), eit = isvisited_suf.end(); it!=eit; ++it)
      {
        const SVF::ICFGNode *node = *it;
        const SVF::IntraICFGNode *intraNode = NULL;
        // Check if the node is an intra-procedural node
        if (intraNode= dyn_cast<SVF::IntraICFGNode>(node)){
          // Get the LLVM Instruction and its BasicBlock
          const Instruction *inst = cast<const Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(intraNode->getInst()));
          if (inst)
          {
            const BasicBlock *BB = (BasicBlock*)inst->getParent();
            // Add the BasicBlock to the temporary set
            tmp_suf_bbs.insert(BB);
          }
        }

      }
      // Update the set of successor basic blocks for the current target
      targets_suf_cfg_bb[taget_bb_id].insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
      // Update the global set of all successor basic blocks
      all_suf_cfg_bb.insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
    }
   
	}


  ofstream outfile("targetBB_dis_sep.txt", std::ios::out | std::ios::app);
  ofstream outfile1("BBtargetBB_dis_sep.txt", std::ios::out | std::ios::app);
  // Sets to store IDs and LLVM BasicBlocks for the target basic blocks
  std::set<uint32_t> targetBBIDs;
  std::set<const BasicBlock *> targetBBs;

  // Iterate through the target basic blocks and collect their IDs and LLVM BasicBlocks
  for(const BasicBlock* BB:targets_DT_bb){
     // Get the first instruction of the BasicBlock
    const Instruction *firstInstr = &*(BB->begin());
    NodeID id = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(firstInstr))->getId();
    
    // Retrieve the ICFGNode for the NodeID
    ICFGNode* iNode = icfg->getICFGNode(id);
    // Retrieve the SVFBasicBlock and LLVM BasicBlock corresponding to the ICFGNode
    const SVFBasicBlock *svfbb = iNode->getBB();
    const BasicBlock *BB_target = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
    uint32_t taget_bb_id = BB_IDs[BB_target];
    targetBBIDs.insert(taget_bb_id);
    targetBBs.insert(BB_target);
  }

  // Iterate through ALL predecessor basic blocks to compute and write distances
  for(auto BB : all_pre_cfg_bb){
    uint32_t BBID = BB_IDs[BB]; // Get the unique ID for the current BasicBlock
    outfile1 << BBID <<" : "; // Write the ID to the output file

    // Iterate through all target BasicBlocks
    for(auto BB_target : targetBBs ){
      uint32_t taget_bb_id = BB_IDs[BB_target]; // Get the unique ID for the target BasicBlock

      // Check if the current BasicBlock is in the distance map for the target
      if(targetID2preNodeMapBB[taget_bb_id].count(BB)){
        // Update the harmonic mean map with the distance
        if(HMpreNodeMapBB.count(BB)){
          // If either value is 0, the harmonic mean is 0
          if(HMpreNodeMapBB[BB]==0 || targetID2preNodeMapBB[taget_bb_id][BB]==0){
            HMpreNodeMapBB[BB]=0;
          }else{
            // Update using harmonic mean formula
            HMpreNodeMapBB[BB] = (double)2 / (((double)1 / targetID2preNodeMapBB[taget_bb_id][BB]) + ((double)1 / (HMpreNodeMapBB[BB])));
          }
        }else{
          // If not in the map, initialize the harmonic mean map with the current distance
          HMpreNodeMapBB[BB] = targetID2preNodeMapBB[taget_bb_id][BB];
        }
        // Write the distance to the target to the output file
        outfile1 << " " << targetID2preNodeMapBB[taget_bb_id][BB];
      }else{
        // If no distance is recorded, write "None"
        outfile1 << " None";
      }
    }
    // Write the harmonic mean distance for the current BasicBlock
    outfile1 <<" "<< HMpreNodeMapBB[BB] << std::endl;
  }

  // Write distances between target BasicBlocks and their predecessors
  for(auto BB_target : targetBBs ){
    uint32_t taget_bb_id = BB_IDs[BB_target]; // Get the unique ID for the target BasicBlock
    // Iterate through all predecessor BasicBlocks
    for(auto BB : all_pre_cfg_bb){
      uint32_t BBID = BB_IDs[BB]; // Get the unique ID for the predecessor BasicBlock
       // Check if the distance is recorded in the map
      if(targetID2preNodeMapBB[taget_bb_id].count(BB)){
        // Write the target ID, predecessor ID, and distance to the output file
        outfile<<taget_bb_id<<" "<<BBID<<" "<<targetID2preNodeMapBB[taget_bb_id][BB]<<std::endl;
      }
    }
  }

  outfile.close();
  outfile1.close();
}

SVFGNode * SVFVar2SVFNode(const SVFVar *Var){
  const SVFValue *val = Var->getValue(); // Get the LLVM Value associated with the SVFVar.
  uint32_t totalNodeNum = svfg->getTotalNodeNum(); // Get the total number of nodes in the SVFG.
  SVF::SVFGNode *vNode;

  // Iterate through all the nodes in the SVFG
  for (uint32_t i = 0; i < totalNodeNum; i++)
  {
    if (!svfg->hasSVFGNode(i)) // Check if the node at the index i exists
    {
      errs() << "i num: " << i << "\n";
      break;
    }
    vNode = svfg->getSVFGNode(i); // Get the SVFGNode at index i
    if (vNode->getValue() == val) // Compare the value of the SVFGNode with the value of the SVFVar
    {
      break; // If the values match, this is the corresponding SVFGNode, so we exit the loop.
    }
  }

  return vNode; // Return the found SVFGNode
}

bool isBlacklisted(const SVFVar * Var ) {
  static const SmallVector<std::string, 50> Blacklist = {
    "alloc",
    "strcpy",
    "strncpy",
    "bsearch",
    "_Znwm",
    "_Znam",
    "strcat",
    "memchr",
    "mmap",
    "strchr",
    "fopen",
    "strdup",
    "pthread_getspecific",
    "fgets",
    "realpath",
    "__dynamic_cast",
    "getenv",
    "strstr",
    "fdopen",
    "popen",
    "strrchr",
    "str",
    "gmtime",
    "time",
    "open",
    "isdigit",
    "inet_ntop"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (Var->toString().find(BlacklistFunc)!=string::npos) {
      return true;
    }
  }

  return false;
}

void findTargetUse(SVFG *svfg, int num){
  // Initialize a FIFO worklist to store VFGNodes for processing.
    FIFOWorkList<const VFGNode *> worklist;
    // Initialize a set to keep track of visited VFGNodes.
    set<const VFGNode*> visited;

  // Iterate through a collection of VFGNodes (presumably a global or member variable).
  for(auto val : VFGNodes){
    // Cast the current node to an SVFG (sparse value flow graph) node.
    SVFGNode *vNode = (SVFGNode *)val;

    // Flag to indicate whether the current node satisfies certain conditions (sufficiency).
    // NOTE: It is initialized to 'true' but never changed in the given code (might be used in extended logic).
    bool sufFlag = 1;   
    
    // Check if the node has already been visited in a previous outer loop iteration.
    if(visited.find(vNode)!=visited.end()){
      ; // If visited before, skip processing.
    }else{
      visited.clear();
    }

    // Debug: print out the val by std::cout
    std::cout << "val: " << vNode->toString() << std::endl;

    // Add the current node to the worklist to explore.
    worklist.push(vNode);

    // Get the ICFGNode corresponding to the current VFGNode.
    const ICFGNode* iNode = val->getICFGNode();
    // Get the SVFBasicBlock associated with the ICFGNode.
    const SVFBasicBlock *svfbb = iNode->getBB();
    // Get the LLVM BasicBlock corresponding to the SVFBasicBlock.
    const BasicBlock *BB_target = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
     // Get the unique ID of the target BasicBlock.
    uint32_t taget_bb_id = BB_IDs[BB_target];

    // Temporary set to store BasicBlocks related to the current node.
    std::set<const BasicBlock*> tmp_suf_bbs;
    // Set to store callees encountered during traversal.
    set<FunEntryICFGNode *> callee;

    int suf_num = 0;

    // Inner loop: Process nodes from the worklist until it's empty, 
    // sufFlag is false, or the iteration limit (SUF_NUM) is reached.
    while(!worklist.empty() && sufFlag && (suf_num<SUF_NUM)){
      suf_num++;

      // Pop the next node from the worklist.
      const VFGNode *treeNode = worklist.pop();
      // Mark the current node as visited.
      visited.insert(treeNode);

      // Check if the node is an Actual Parameter Node (ActualParmVFGNode).
      // Actual Parameter Node represents an actual arguemnt at a call site. 
      // For instance, if we have 'x = 5; func(&x);' ActualParmVFGNode captures the address of x.
      if(const ActualParmVFGNode* AParmNode=dyn_cast<ActualParmVFGNode>(treeNode)){
          const CallICFGNode *callNode = AParmNode->getCallSite(); // Get the call site associated with the ActualParmVFGNode

          // Iterate through all out-edges of the call node to identify the callee functions.
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit = callNode->OutEdgeEnd(); it != eit; ++it)
          {
            // Get the destination node (function entry) of the outgoing edge.
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode); // Add the callee (function entry) to the 'callee' set.
          }

          // Get the set of Actual OUT nodes connected to the call site in the SVFG.
          // For example, if the call site is func(&x) and the value of x is modified in the function,
          // and the function also assigned a new value to one of the global variables, the Actual OUT nodes
          // would include the SVFG nodes representing the global variable and x.
          NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
          // Add the Actual OUT nodes to the worklist for further exploration.
          for (auto nodeid : AOUTNodeSet)
          {
            worklist.push(svfg->getSVFGNode(nodeid));
          }

          // Get the return node associated with the call site.
          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet(); // Get the variable associated with the return node.

          // If no variable is associated (e.g., void return), there's nothing to follow up.
          if(Var ==NULL){
            continue;
          }
          
          // Get the value associated with the variable.
          const SVFValue *val = Var->getValue();
          // Check if the variable is blacklisted, i.e., the return value (Var) originates from a function that is considered uninteresting or irrelevant,
          // for example, malloc, strcpy, etc. And if so, add the corresponding SVFGNode that represents the pointer it "returns" (e.g., the allocated memory).
          // And track how it's used in the rest of the program. (i.e, continues to analyze how that pointer (returned from the blacklisted function) is used in the program.)
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            // Otherwise, get the Actual Return VFGNode associated with the variable.
            // We want to coninue our analysis inside this function to see how the return value was used/computed. 
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
      
      // Check if the node is an Actual IN Node (ActualINSVFGNode). 
      // An ActualINSVFGNode corresponds to the argument's flow *into* the callee function at this call site. 
      // For example, if we call 'foo(&x)', the ActualINSVFGNode represents how '&x' is now seen by 'foo' as its incoming parameter.
      // I,e., ActualINSVFGNode = "the data-flow node inside the callee environment representing the actual parameter at the call site."
      // NOTE: SVF uses ActualParmVFGNode <-> ActualINSVFNode <-> FormalParmVFGNode to represent that entire chain of data flow.
      }else if(const ActualINSVFGNode * AINNode = dyn_cast<ActualINSVFGNode>(treeNode)){
          // Retrieve the call site associated with the ActualINSVFGNode.
          const CallICFGNode *callNode = AINNode->getCallSite();

          // Iterate through all out-edges of the call node to identify the callee functions.
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit = callNode->OutEdgeEnd(); it != eit; ++it)
          {
            // Get the destination node (function entry) of the outgoing edge.
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
            // break;
          }

          // Get the set of Actual OUT nodes connected to the call site in the SVFG.
          // For further details, see the comments in the ActualParmVFGNode section above.
          NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
          for(auto nodeid : AOUTNodeSet){
            worklist.push(svfg->getSVFGNode(nodeid));
          }
          
          // Get the return node associated with the call site.
          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet(); // Get the variable associated with the return node.
           // If no variable is associated (e.g., void return), there's nothing to follow up.
          if(Var ==NULL){
            continue;
          }

          // Get the value associated with the variable.
          const SVFValue *val = Var->getValue();
          // Check if the variable is blacklisted. See further details in the ActualParmVFGNode section above.
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
      }

      // Process all out-edges from the current VFGNode to continue BFS.
      for (VFGNode::const_iterator it = treeNode->OutEdgeBegin(), eit = treeNode->OutEdgeEnd(); it != eit; ++it)
      {
        VFGEdge *edge = *it;
        VFGNode *sufNode = edge->getDstNode();

         // If we've already visited this node, skip enqueuing it again.
        if(visited.find(sufNode) != visited.end()){
          continue;
        }
        // Handling other special node types similarly to the ActualParmVFGNode and ActualINSVFGNode above...
        if(ActualParmVFGNode* AParmNode=dyn_cast<ActualParmVFGNode>(sufNode)){
          const CallICFGNode *callNode = AParmNode->getCallSite();
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit = callNode->OutEdgeEnd(); it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
          }
               
            NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
            for(auto nodeid : AOUTNodeSet){
              worklist.push(svfg->getSVFGNode(nodeid));
            }

          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet();
          if(Var ==NULL){
            continue;
          }
          const SVFValue *SVFval = Var->getValue();
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
        // FormalRetVFGNode = Represents the return value inside the callee.
        // I.e., If we have already recognized that function as a callee (e.g., from the ActualParmVFGNode or ActualINSVFGNode),
        // then skip further processing of the return value.
        }else if(FormalRetVFGNode * FRetNode = dyn_cast<FormalRetVFGNode>(sufNode)){
          FunEntryICFGNode *funEntryNode = icfg->getFunEntryICFGNode(FRetNode->getFun());
          // that callee has already been discovered, skip further processing.
          if(callee.find(funEntryNode)!=callee.end()){
            continue;
          }
        // See the comments in the ActualParmVFGNode section above.
        }else if(ActualINSVFGNode * AINNode = dyn_cast<ActualINSVFGNode>(sufNode)){
          const CallICFGNode *callNode = AINNode->getCallSite();
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                          callNode->OutEdgeEnd();
            it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
          }
          NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
          for(auto nodeid : AOUTNodeSet){
            worklist.push(svfg->getSVFGNode(nodeid));
          }
          
          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet();
          if(Var ==NULL){
            continue;
          }
          const SVFValue *val = Var->getValue();
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
        // FormalRetVFGNode = Representation of changes made to the callee's parameters before returning.
        // I.e., it tracks the data flow out of a function through pointer parameters and global variables 
        // that are modified inside the callee function.
        }else if(FormalOUTSVFGNode * FOUTNode=dyn_cast<FormalOUTSVFGNode>(sufNode)){
          FunEntryICFGNode *funEntryNode = icfg->getFunEntryICFGNode(FOUTNode->getFunExitNode()->getFun());
          // Skip if the function was already known as a callee.
          if(callee.find(funEntryNode)!=callee.end()){
            continue;
          }
        }
        worklist.push(sufNode);
      }
    }

    // If the BFS path was "sufficient" (NOTE: sufFlag 'never' turned false),
    // record all the BasicBlocks encountered from the visited VFGNodes.
    if(sufFlag){
      for(auto it = visited.begin(), eit = visited.end(); it!=eit; ++it)
      {
        const VFGNode *node = *it;
        const StmtVFGNode *stmtNode = NULL;
        // StmtVFGNode corresponds to an LLVM instruction or statement.
        if (stmtNode= dyn_cast<StmtVFGNode>(node)){
          if(stmtNode->getInst() == nullptr){
            continue;
          }
          // Convert the SVF instruction to an LLVM instruction, then retrieve its parent BB.
          const Instruction *inst = cast<const Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(stmtNode->getInst()));
          
          if (inst)
          {
            // Get the parent BB of the instruction.
            // A parent BB is a BasicBlock that contains the instruction.
            const BasicBlock *BB = (BasicBlock*)inst->getParent();
            // tmp_suf_bbs is the set of LLVM BB that the analysis above encountered. or deemed "relevant"
            // I.e., because these is some data-flow path into thse blocks stemming from the target BB (starting point).
            tmp_suf_bbs.insert(BB);
          }
        }
      }
      // Store all discovered BB that are data-flow dependent, tainted, or relevant to the target BB.
      // Hence, we can use targets_suf_data_bb to look up "from that target BB, which BBs did we discover to be reachable or to contain relevant data-flow paths."
      targets_suf_data_bb[taget_bb_id].insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
      // a global set that contains every discovered block from all targets.
      all_suf_data_bb.insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
    }

  }

}

const BasicBlock *getDominatorBB(const Function* fun, std::set<const BasicBlock *> BBs)
{
  // print out the function name
  errs() << "Processing function: " << fun->getName().str() << "\n";

  // Build the dominator tree for this function
  // Dominator Tree is a data structure that consists of dominator information for each basic block in the function.
  const DominatorTree DT(const_cast<Function&>(*fun));
  
  // Debug - print out the dominator tree
  DT.print(errs());

  // Find the common dominator of the given basic blocks
  const BasicBlock *DominatorBB = nullptr;
  
  for (auto it = BBs.begin(); it != BBs.end(); it++) {
    const BasicBlock *BB = *it;

    // Skip unreachable basic blocks from the dominator tree
    if (!DT.isReachableFromEntry(BB))
    {
      ;
    }else{
      if (!DominatorBB) {
        DominatorBB = BB;
      } else {
        DominatorBB = DT.findNearestCommonDominator(DominatorBB, BB);
        // Debug - print out the dominator basic block's id
        errs() << "DominatorBB: " << DT.getNode(DominatorBB);
      }
    }
  }
  
  if(!DominatorBB){
    exit(1);
  }

  // In the end, there is only one dominator basic block
  return DominatorBB;
}


void filter_target(){
  errs() << "filter targets...\n";
  std::cout << "filter targets...\n" << std::endl;
  // targets_llvm_func is from result of loadTargets
  for (auto func: targets_llvm_func){
    std::cout << "Processing function: " << func->getName().str() << std::endl;
    
    const BasicBlock *dominatorBB = getDominatorBB(func, targets_llvm_func_bbs[func]);
    // Each function has only one dominator basic block
    targets_DT_bb.insert(dominatorBB);

    errs() << "In the for loop targets_llvm_func_bbs\n";
    for(auto origBB: targets_llvm_func_bbs[func]){
      // Assign the dominator basic block to the original basic block
      origBB2DTBB[origBB] = dominatorBB;
    }

    // Debug - print out origBB2DTBB
    for (auto bb = origBB2DTBB.begin(); bb != origBB2DTBB.end(); bb++) {
      errs() << "origBB2DTBB: ";
      bb->first->printAsOperand(errs(), false);
      errs() << " -> ";
      bb->second->printAsOperand(errs(), false);
      errs() << "\n";
      
    }
  }

  int i = 0;
  for (auto it = targets_DT_bb.begin(); it != targets_DT_bb.end(); ) {
      i++;
      if (i >= TARGETS_NUM) { // TARGETS_NUM is a constant (default value is 10)
          errs() << "target too many!, delete over target\n";
          it = targets_DT_bb.erase(it); 
      } else {
          ++it; 
      }
  }

  targets_DT_bb_num = i;
  targets_DT_bb_num_orig = targets_DT_bb_orig.size();
  errs() << "targets_DT_bb_num: " << targets_DT_bb_num << "\n";
}



std::vector<NodeID> loadTargets(std::string filename) {
  /* Load the target file
    eventually return a vector of ICFG NodeIDs (result).

    Each node in the result contains at least one type of VFGNode (e.g., StoreVFGNode, CopyVFGNode, CmpVFGNode, BinaryOPVFGNode, UnaryOPVFGNode).
    This ID can use used to fetch the correspoding information such as 
    - function name
    - basic block
    - instruction
  */

  // 1. read the target file
  ifstream inFile(filename);
	if (!inFile) {
		std::cerr << "can't open target file!" << std::endl;
		exit(1);
	}

  // 2. read the target line by line
	std::vector<NodeID> result; // store the target node id
	std::vector<std::pair<std::string,u32_t>> targets; // store the target function name and line number
	std::string line;
	while(getline(inFile, line)) {
		std::string func;
		uint32_t num;
		std::istringstream text_stream(line);
		getline(text_stream, func, ':'); // Extract the function name (up to the ':' delimiter) into 'func'.
    if(func.empty()){ 
      errs() << "empty\n";
      continue;
    }
		text_stream >> num; // Read the line number.
    targets.push_back(make_pair(func, num)); // add the target function name and line number
	}

  // 3. Iterating Through LLVM IR:
  // iterate though all the functions in the module
  for (Module::const_iterator F = M->begin(), E = M->end(); F != E; ++F){
    const Function *fun = &*(F);
		std::string file_name = "";
		std::string Filename = "";

    // Get the file name of the function if the debug info is available
		if (llvm::DISubprogram *SP = fun->getSubprogram()){
			if (SP->describes(fun))
				file_name = (SP->getFilename()).str();
		}

    // 1. Check if the function's file name matches any of the targets
		bool flag = false;
		for (auto target : targets) {
      // get the canonical file name
      std::string TargetFileName = llvm::sys::path::filename(target.first).str();
      auto idx = file_name.find(TargetFileName);
      // auto idx = file_name.find(target.first); // This doesn't work because target.first is the full path...
      if (idx != string::npos) {
				flag = true;
				break;
			}
		}
    // If the function's file name does not match any of the targets, skip the function
		if (!flag)
			continue;

    
     // Inner loop (1): Iterate through all "basic blocks" in the current function.
    for (Function::const_iterator bit = fun->begin(), ebit = fun->end(); bit != ebit; ++bit) {

			const BasicBlock* bb = &(*bit);
      // Inner loop (2): Iterate through all "instructions" in the current basic block.
			for (BasicBlock::const_iterator it = bb->begin(), eit = bb->end(); it != eit; ++it) {
				uint32_t line_num = 0;
				const Instruction* inst = &(*it);
				std::string str=LLVMUtil::getSourceLoc(inst);
        // Debug the value of LLVMUtil::getSourceLoc(inst);
        // Convert the instruction to a string
        std::string inst_str;
        llvm::raw_string_ostream rso(inst_str);
        inst->print(rso);

          // 4. Target Matching:
          // Skip alloca instructions (they are not relevant for our targets).
					if (SVFUtil::isa<AllocaInst>(inst)) {
            continue;
					}
          // Get debug information (line number and filename) if available.
					else if (MDNode *N = inst->getMetadata("dbg")) {
						llvm::DILocation* Loc = SVFUtil::cast<llvm::DILocation>(N);
						line_num = Loc->getLine();
            Filename = Loc->getFilename().str();
					}

          // Iterate through the targets read from the file.
					for (auto target : targets) {
            // Check if the current instruction's filename contains the target function name.
            // The (idx == 0 || Filename[idx-1]=='/') part ensures that we match the whole function name
            // and not just a part of it (e.g., we want to match "foo", not "myfoo").
            std::string TargetFileName = llvm::sys::path::filename(target.first).str();
            auto idx = Filename.find(TargetFileName);
						//auto idx = Filename.find(target.first);
						if (idx != string::npos && (idx == 0 || Filename[idx-1]=='/')) {
              // Check if the current instruction's line number matches the target line number.
              // Only process the instruction that matches the target line number (i.e., exact line of code changed by the commit)
							if ((target.second == line_num) ) {
                // 5. Identifying and Storing Targets:
                // Get the VFG nodes associated with this instruction.
                std::list<const VFGNode *> TempVFGNodes = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst))->getVFGNodes();

                // only search for StoreVFGNode
                // Filter out VFG nodes that are not relevant to our analysis. We only keep nodes related to data flow.
                std::list<const VFGNode *>::iterator it = TempVFGNodes.begin();
                while (it != TempVFGNodes.end()) {

                  // Using dyn_cast to check if the VFG node belongs to one of the following types:StoreVFGNode, CopyVFGNode, CmpVFGNode, BinaryOPVFGNode, UnaryOPVFGNode.
                  // If a node is not one of these types, we remove it from the list.
                  if (!dyn_cast<const StoreVFGNode>(*it) && !dyn_cast<const CopyVFGNode>(*it) && !dyn_cast<const CmpVFGNode>(*it) && !dyn_cast<const BinaryOPVFGNode>(*it) && !dyn_cast<const UnaryOPVFGNode>(*it)) {
                    it = TempVFGNodes.erase(it); 
                  }else{
                    ++it;
                    // Print out the basic block that contains the current matched instruction.
                    errs() << "Basic Block containing the matched instruction: ";
                    bb->printAsOperand(errs(), false);
                    errs() << "\n";

                    // Insert the current basic block into 'targets_DT_bb_orig'.
                    // this basic block contains the instruction that matches the target and one of the VFG nodes is a StoreVFGNode, CopyVFGNode, CmpVFGNode, BinaryOPVFGNode, or UnaryOPVFGNode.
                    targets_DT_bb_orig.insert(bb);
                    NodeID id = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst))->getId();
                    result.push_back(id); // Add the ICFG node ID to the 'result' vector.
                    // the result only has instructions that match the target and one of the VFG nodes is a StoreVFGNode, CopyVFGNode, CmpVFGNode, BinaryOPVFGNode, or UnaryOPVFGNode.
                  }
                }
                VFGNodes.splice(VFGNodes.end(), TempVFGNodes);
              }
						}
					}
        }
      }
    }
  inFile.close();

  for (NodeID id : result) {
		ICFGNode* iNode = icfg->getICFGNode(id);
    const SVFBasicBlock *svfbb = iNode->getBB();
    const BasicBlock *bb = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
    const Function *func = bb->getParent();

    // If bb is already in targets_llvm_bb, nothing changes bacause the set is unique
    targets_llvm_bb.insert(bb);
    // If func is already in targets_llvm_func, nothing changes bacause the set is unique
    targets_llvm_func.insert(func);
    // If bb is already in targets_llvm_func_bbs[func], nothing changes bacause the set is unique
    targets_llvm_func_bbs[func].insert(bb);
  }

  filter_target();

  // Debug - print out the content of targets_llvm_func_bbs
  std::cout << "--- Printing targets_llvm_func_bbs ---" << std::endl;
  for (auto it = targets_llvm_func_bbs.begin(); it != targets_llvm_func_bbs.end(); ++it) {
    const Function *func = it->first;
    std::cout << "Function: " << func->getName().str() << std::endl;
    std::cout << "Basic blocks in the function: " << std::endl;
    for (auto bb : it->second) {
      // std::cout << "  Basic Block: " << bb << std::endl;
      // std::cout << "Hello!\n" << std::endl;
      // Create a raw_os_ostream that writes to std::cout
      llvm::raw_os_ostream cout_stream(std::cout); 
      bb->printAsOperand(cout_stream, false);
      cout_stream << "\n"; //
    }
  }

	return result; // Result is a vector of ICFG NodeIDs (i.e., target_ids)
}

static void buildBranchInfo(std::vector<NodeID> target_ids){
  std::map<const BasicBlock *,uint32_t> BB2Loc;
	ofstream outfile("icfg-edge.txt", std::ios::out | std::ios::app);
	ofstream outfile2("edge-test.txt", std::ios::out | std::ios::app);
	ofstream outfile3("branch-distance.txt", std::ios::out | std::ios::app);
	ofstream outfile4("branch-distance-min.txt", std::ios::out | std::ios::app);
	ofstream outfile5("branch-curloc.txt", std::ios::out | std::ios::app);
  ofstream outfile6("branch-data.txt", std::ios::out | std::ios::app);
  ofstream outfile7("branch-distance-min-data.txt", std::ios::out | std::ios::app);

  vector<ofstream> files;
  for(auto target_bb:targets_DT_bb){
    NodeID target_bb_id = BB_IDs[target_bb];

    string filename = to_string(target_bb_id) + "_distance.txt";
    files.emplace_back(filename);
  }

  vector<ofstream> files_data;
  for(auto target_bb:targets_DT_bb){
    NodeID target_bb_id = BB_IDs[target_bb];

    string filename = to_string(target_bb_id) + "_edge_suffix_data.txt";
    files_data.emplace_back(filename);
  }

  srandom(994);
  int num = 0;
  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
      
        BasicBlock *bb = &*(bit);
      unsigned int cur_loc = AFL_R(MAP_SIZE);
      BB2Loc[bb] = cur_loc;
      num++;
      outfile2 <<"bbid: "<<BB_IDs[bb]<<" cur_loc: " << cur_loc << " bbinfo: "<< getDebugInfo(bb)<<" \n";     
    }
  }

  std::set<const BasicBlock *> visited_bb;
  Set<const ICFGNode *> visited;
  NodeID id = 0;
  ICFGNode* iNode = icfg->getICFGNode(id);
  FIFOWorkList<const ICFGNode*> worklist;
  worklist.push(iNode);
  for(auto nodeid:target_ids){
    worklist.push(icfg->getICFGNode(nodeid));
  }

  while (!worklist.empty())
    {
        const ICFGNode* iNode = worklist.pop();
        const SVFBasicBlock *svfbb = iNode->getBB();
        const BasicBlock *SrcBB = nullptr;
        if(!svfbb) {
          ;
        }else{
          SrcBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
        }
        
        visited_bb.insert(SrcBB);
        for (ICFGNode::const_iterator it = iNode->OutEdgeBegin(), eit =
                    iNode->OutEdgeEnd(); it != eit; ++it)
        {
            ICFGEdge* edge = *it;
            ICFGNode* succNode = edge->getDstNode();
            const BasicBlock *DstBB = nullptr;
            if(!(succNode->getBB())) {
              ;
            }
            else{
              DstBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(succNode->getBB()));
            }
            if(SrcBB != DstBB){
              uint32_t cur_loc = BB2Loc[DstBB];
              uint32_t pre_loc = BB2Loc[SrcBB];
              uint32_t temp_pre_loc = pre_loc;
              pre_loc = pre_loc >> 1;
              uint32_t edge_index = cur_loc ^ pre_loc;
              uint32_t distance = (uint32_t)BBID2dis[BB_IDs[DstBB]];

              std::map<NodeID, double> distance_target;
              for (auto target_bb:targets_DT_bb){
                NodeID target_bb_id = BB_IDs[target_bb];
                if(targetID2preNodeMapBB[target_bb_id].count(DstBB)){
                  distance_target[target_bb_id] = targetID2preNodeMapBB[target_bb_id][DstBB];

                }else{
                  distance_target[target_bb_id] = -1;
                }
              }

              outfile << "bbid: " << BB_IDs[DstBB] << " pre_loc: " << temp_pre_loc << " cur_loc: " << cur_loc << " branch_index: " << edge_index << " distance: " << distance << "\n";
              outfile5 << edge_index << " " << cur_loc << " "<< distance<< "\n";
              outfile3 << "branch_index: " << edge_index << " distance: " << distance << "\n";
              if(distance<(uint32_t)(-1)){
                outfile4 << edge_index << " " << distance << "\n";
              }
              int i = 0;
              for(auto target_bb:targets_DT_bb){
                NodeID target_bb_id = BB_IDs[target_bb];
                if(targetID2preNodeMapBB[target_bb_id].count(DstBB)){
                  uint32_t distance_target_temp = targetID2preNodeMapBB[target_bb_id][DstBB];
                  if(distance_target_temp<(uint32_t)(-1)){
                    files[i] << edge_index << " " << distance_target_temp << "\n";
                  }
                }
                if(targets_suf_data_bb_target[target_bb_id].count(DstBB)){
                  files_data[i] << edge_index << " \n";
                  outfile7 << edge_index << " \n";
                }
                i++;
              }
            }

            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }
    outfile <<"BBnum: "<<num<< " total: " << visited_bb.size() << "\n";

    outfile.close();
    outfile2.close();
    outfile3.close();
    outfile4.close();
    outfile5.close();    
    outfile6.close();
    outfile7.close();
    for (int i = 0; i < files.size(); i++) {
      files[i].close();
      files_data[i].close();
    }
}

int main(int argc, char ** argv) {
    int arg_num = 0;
    char **arg_value = new char*[argc];
    std::vector<std::string> moduleNameVec;
    LLVMUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
    std::string firstElement = moduleNameVec.front();
    std::cout << firstElement << std::endl; 
    for (const std::string& str : moduleNameVec) {
      
        std::cout << str << std::endl;
    }

    cl::ParseCommandLineOptions(arg_num, arg_value,
                                "analyze the vinilla distance of bb\n");

    svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);
    SVFIRBuilder builder(svfModule);
    SVFIR *svfir = builder.build();
    AndersenWaveDiff *ander = AndersenWaveDiff::createAndersenWaveDiff(svfir);
    
    SVFGBuilder svfBuilder(true);
    svfg = svfBuilder.buildFullSVFG(ander);

    icfg = svfir->getICFG();

    PTACallGraph* callgraph = ander->getPTACallGraph();
    icfg->updateCallGraph(callgraph);
    
    svfg->updateCallGraph(ander);

    for (Module& Mi : LLVMModuleSet::getLLVMModuleSet()->getLLVMModules()){
          errs() << "ModuleName: " << Mi.getName().str() << "\n";
          if (Mi.getName().str() == firstElement) {
              M = &Mi;
          }
    }
    C = &(LLVMModuleSet::getLLVMModuleSet()->getContext());

    std::cout << "loadTargets..." << std::endl;
    std::vector<NodeID> target_ids = loadTargets(TargetsFile);
    std::cout << "caculate vanilla distance..." << std::endl;
    instrument_orig();

    std::cout << "findTargetControl..." << std::endl;
    findTargetControl(target_ids);
    std::cout << "findTargetUse..." << std::endl;
    findTargetUse(svfg,0);
    std::cout << "instrument distance..." << std::endl;
    instrument();
    std::cout << "instrument suffix..." << std::endl;
    instrumentSuffix();
    std::cout << "ci.bc..." << std::endl;
    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".ci.bc");

    std::cout << "buildBranchInfo..." << std::endl;
    buildBranchInfo(target_ids);

    return 0;
}
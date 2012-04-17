#define DEBUG_TYPE "ABCDPass"
#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/CallGraphSCCPass.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/CFG.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/InstrTypes.h"
#include "llvm/Constants.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include <set>
#include <vector>
#include <list>
#include "llvm/ADT/Twine.h"

using namespace llvm;
using namespace std;

namespace Graph{

	struct _INEQNode {
		//most imp attr
		Value *value;
		bool isPhi;
		
		//adjacency
		map<struct _INEQNode * , int> in ;
		map<struct _INEQNode * , int > out ;

		int length; 
	};
	typedef struct _INEQNode  INEQNode ;


	typedef struct{
		map<Value*, INEQNode * > arrayLengthList;//Stores A.length and 0 node
		map<Value*, INEQNode * > variableList;
	}INEQGraph ;


	INEQNode  *createNode(Value *value, int length){
		INEQNode  *newNode;
		newNode = new INEQNode ();
		newNode->value = value;
		newNode->length = length;
		newNode->isPhi = false;
		return newNode;
	}

	INEQNode  *getOrInsertNode(INEQGraph  *graph, llvm::Value *value, int length){
		map<Value*, INEQNode * > *list;
		map<Value*, INEQNode * >::iterator it;
		list = (length == 0) ? &(graph->variableList) : &(graph->arrayLengthList);
		//Hack for lower bound
		if(length==-1)
			length =0;
		it = list->find(value);
		if (it != list->end())
			return it->second;
		INEQNode  *newNode = createNode(value, length);
		list->insert(pair<Value*, INEQNode *>(value, newNode));
		return newNode;
	}

	void insertEdge(INEQNode  *n1, INEQNode  *n2, int edgeWeight ){
		map<INEQNode * , int >::iterator it;
		it = n1->out .find(n2);
		if (it == n1->out .end())
			n1->out .insert(pair<INEQNode *, int>(n2, edgeWeight ));
		it = n2->in .find(n1);
		if (it == n2->in .end())
			n2->in .insert(pair<INEQNode *,int>(n1, edgeWeight ));
	}


}

namespace {

	struct ABCDPass : public FunctionPass{
		static char ID;
		
		//the following data structures can be used for DemandProve if necessary
		vector<Instruction *> LB_arrayCheckInstList;
		vector<Instruction *> UB_arrayCheckInstList;
		ABCDPass() : FunctionPass(ID) {}

			virtual bool runOnFunction(Function &F){

				//Construct 2 graphs to handle upper and lower bound
				Graph::INEQGraph  *lbgraph = construct_lbgraph(F);
				Graph::INEQGraph  *ubgraph = construct_ubgraph(F);

				return true;
			}

			Graph::INEQGraph  * construct_lbgraph(Function &F){
				char *lowerChkBlock = "checkLower";
				char *piFoo  = "piFunc";
				Graph::INEQGraph  *inequalityGraph = new Graph::INEQGraph ();
				for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
					if(isa<AllocaInst>(*I)){
						AllocaInst *ai = (AllocaInst *)&*I;
						if (ai->getAllocatedType()->isArrayTy()){
							 //small hack: length added as -1 to use the same graph library functions
							//this should go into arraylist rather than variable list
							 Graph::getOrInsertNode(inequalityGraph, (Value *)ai, -1);
						}
					} else if (isa<ICmpInst>(*I)){
						ICmpInst *icmpInstr = cast<ICmpInst>(&*I);	
						BasicBlock *instrBlock= icmpInstr->getParent();
						if ((instrBlock)->getName().startswith(StringRef(lowerChkBlock))){
							LB_arrayCheckInstList.push_back(&*I);
						}
					}
				}
				for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
					if (isa<PHINode>(*I)){
						PHINode *phi = (PHINode *)(&*I);
						//Process pi functions
						if((*I).getName().startswith(StringRef(piFoo)))
						{
							//Insert code to handle piFunctions
							inst_iterator temp_I = I;
							Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,cast<CallInst>(&*temp_I)->getArgOperand(0),0);
							if(phi->getNumIncomingValues()==1){
								
							}
							if(phi->getNumIncomingValues()==2){
							}
							continue;
						}
						Graph::INEQNode  *res = Graph::getOrInsertNode(inequalityGraph, (Value *)phi, 0);
						res->isPhi = true;
						std::map<Value*, Graph::INEQNode * > *arrayLengthPtr = &(inequalityGraph->arrayLengthList);
						for (int i = 0, total = phi->getNumIncomingValues(); i < total; i++){
							Value *inVal = phi->getIncomingValue(i);
							if (isa<Constant>(*inVal)){
                                        	                 if (!isa<ConstantInt>(*inVal))
                                                	                 continue;
	
								ConstantInt *cons = cast<ConstantInt>(inVal);
								for (map<Value*, Graph::INEQNode * >::iterator AI = (*arrayLengthPtr).begin(),
										AE = (*arrayLengthPtr).end(); AI != AE; ++AI){
									//edgeWeight  of the edge = cons - arraylength
									//cons->getSExtValue()-
									Graph::insertEdge((*AI).second, res,cons->getSExtValue()-(*AI).second->length);
							}
							continue;
						}
						Graph::INEQNode  *in = Graph::getOrInsertNode(inequalityGraph, inVal, 0);
						Graph::insertEdge(in, res, 0);
					}
				}else if(isa<BinaryOperator>(*I)){
					int op = I->getOpcode();
					if(op == Instruction::Add || op == Instruction::Sub || op == Instruction::FAdd || op == Instruction::FSub){
						Value* varOprnd ;
						ConstantInt* constOprnd ;

						int opType = ( (op == Instruction::Add || op == Instruction::FAdd) )?1:-1;
						if(isa<ConstantInt>(*(I->getOperand(0)))){
							constOprnd  = cast<ConstantInt>(I->getOperand(0));
							varOprnd  = I->getOperand(1);
						}else if(isa<ConstantInt>(*(I->getOperand(1)))){
							constOprnd  = cast<ConstantInt>(I->getOperand(1));
							varOprnd  = I->getOperand(0);
						}else
							continue;

						Graph::INEQNode * ndDest  = Graph::getOrInsertNode(inequalityGraph,varOprnd ,0);
						Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,(Value*)(&*I),0);
						Graph::insertEdge(ndSrc ,ndDest ,(opType * constOprnd ->getSExtValue()));
					}
				}else if(isa<SExtInst>(*I)){
					Value* operand = I->getOperand(0);
					Graph::INEQNode * ndDest  = Graph::getOrInsertNode(inequalityGraph,operand,0);
					Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,(Value*)(&*I),0);
					Graph::insertEdge(ndSrc ,ndDest ,0);

				}else if(isa<CallInst>(*I)){
					//I->dump();e
					//Deal with pair of PI functions here
					inst_iterator temp_I = I;
					Graph::INEQNode * ndDest [2];
					int i = 0, cntPI = 0;
					do{
						Function *func = cast<CallInst>(&*temp_I)->getCalledFunction();
						if(func != NULL && func->hasName()){
							if(func->getName().startswith(StringRef(piFoo ))){
								Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,cast<CallInst>(&*temp_I)->getArgOperand(0),0);

								ndDest [cntPI] = Graph::getOrInsertNode(inequalityGraph,((Value*)&*temp_I),0);

								Graph::insertEdge(ndSrc ,ndDest [cntPI],0);
								i--;
								cntPI++;
							}
						}
						temp_I++;
						i++;
					}while(isa<CallInst>(*temp_I) && i == 0);

					if(cntPI>0){
						int trueBB  = -1;
						BranchInst* brI = cast<BranchInst>(I->getParent()->getSinglePredecessor()->getTerminator());
						if(brI->getSuccessor(0) == I->getParent())
							trueBB  = 1;

						CmpInst* cmpI = cast<CmpInst>(brI->getCondition());
						int predicate = cmpI->getPredicate();
						int predicateClass;
						//Identifies the type of branch compare instr
						if(predicate == CmpInst::FCMP_OLT || predicate == CmpInst::FCMP_ULT || predicate == CmpInst::ICMP_ULT || predicate == CmpInst::ICMP_SLT){
							predicate = 1;
							predicateClass = 1;

						}else if(predicate == CmpInst::FCMP_OEQ ||predicate == CmpInst::FCMP_OLE || predicate == CmpInst::FCMP_ULE || predicate == CmpInst::FCMP_UEQ || predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SLE || predicate == CmpInst::ICMP_EQ){
							predicate = 1;
							predicateClass = 2;

						}else if(predicate == CmpInst::FCMP_OGT || predicate == CmpInst::FCMP_UGT || predicate == CmpInst::ICMP_UGT || predicate == CmpInst::ICMP_SGT){
							predicate = -1;
							predicateClass = -1;

						}else if(predicate == CmpInst::FCMP_OGE || predicate == CmpInst::FCMP_UGE || predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_SGE){
							predicate = -1;
							predicateClass = -2;

						}else{
							predicate = 0;
						}


						Value *operand1, *operand2;
						int operandLoc;

						if(cntPI == 1){//Array bounds check
							if(isa<ConstantInt>(*(cmpI->getOperand(0)))){
								operand1 = cmpI->getOperand(1);
								operand2 = cmpI->getOperand(0);
								operandLoc = -1;
							}else if(isa<ConstantInt>(*(cmpI->getOperand(1)))){
								operand1 = cmpI->getOperand(0);
								operand2 = cmpI->getOperand(1);
								operandLoc = 1;
							}else
								continue;
							for(std::map<Value*, Graph::INEQNode * >::iterator it = (inequalityGraph->arrayLengthList).begin(); it !=(inequalityGraph->arrayLengthList).end(); ++it){
								if(predicateClass == 1){
									Graph::insertEdge(it->second,ndDest [0],(cast<ConstantInt>(operand2)->getSExtValue() - 1 - it->second->length));
								}
								else{
									Graph::insertEdge(it->second,ndDest [0],(cast<ConstantInt>(operand2)->getSExtValue() - it->second->length));
								}

							}

						}else{//cntPI == 2 for  'if, while'
							I++;
							if(trueBB  == 1 &&  predicate == 1){
								if(predicateClass == 1)
									Graph::insertEdge(ndDest [1], ndDest [0], -1);
								else
									Graph::insertEdge(ndDest [1], ndDest [0], 0);
							}
							else if(trueBB  == 1 &&  predicate == -1){
								if(predicateClass == -1)
									Graph::insertEdge(ndDest [0], ndDest [1], -1);
								else
									Graph::insertEdge(ndDest [0], ndDest [1], 0);
							}    
							else if(trueBB  == -1 &&  predicate == 1){
								predicate = cmpI->getPredicate();
								if(predicate == CmpInst::FCMP_OLT || predicate == CmpInst::FCMP_ULT || predicate == CmpInst::ICMP_ULT || predicate == CmpInst::ICMP_SLT){
									Graph::insertEdge(ndDest [0], ndDest [1], 0);
								}else if(predicate == CmpInst::FCMP_OLE || predicate == CmpInst::FCMP_ULE || predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SLE){
									Graph::insertEdge(ndDest [0], ndDest [1], -1);
								}    
							}else if(trueBB  == -1 &&  predicate == -1){
								predicate = cmpI->getPredicate();
								if(predicate == CmpInst::FCMP_OGT || predicate == CmpInst::FCMP_UGT || predicate == CmpInst::ICMP_UGT || predicate == CmpInst::ICMP_SGT){
									Graph::insertEdge(ndDest [1], ndDest [0], 0);
								}else if(predicate == CmpInst::FCMP_OGE || predicate == CmpInst::FCMP_UGE || predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_SGE){
									Graph::insertEdge(ndDest [1], ndDest [0], -1);
								}
							}
						}

					}
				}
			}

/*
			//Print out graph
						int count = 0;
						for (std::map<Value *, Graph::INEQNode* >::iterator PI = inequalityGraph->variableList.begin(),
						PE = inequalityGraph->variableList.end(); PI != PE; ++PI){

						errs() << "\nNode" << count; PI->first->dump(); //errs() << "\n";
						for (std::map<Graph::INEQNode*, int >::iterator PII = PI->second->out.begin(),
						PEE = PI->second->out.end(); PII != PEE; ++PII){
						errs() << "Node" << count << "outlist::To"; PII->first->value->dump(); errs() << " Weight::" << PII->second << "\n";
						}
						count++;
						}

						for (std::map<Value *, Graph::INEQNode* >::iterator PI = inequalityGraph->arrayLengthList.begin(),
						PE = inequalityGraph->arrayLengthList.end(); PI != PE; ++PI){

						errs() << "\nNode" << count; PI->first->dump(); //errs() << "\n";
						for (std::map<Graph::INEQNode*, int >::iterator PII = PI->second->out.begin(),
						PEE = PI->second->out.end(); PII != PEE; ++PII){
						errs() << "Node" << count << "outlist::To";  PII->first->value->dump(); errs() << " Weight::" << PII->second << "\n";
						}
						count++;
						}
*/
			 
			return inequalityGraph;
			}
			Graph::INEQGraph  * construct_ubgraph(Function &F){
				
				char *upperChkBlock = "checkUpper";
				char *piFoo  = "piInt";
				Graph::INEQGraph  *inequalityGraph = new Graph::INEQGraph ();
				for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
					if(isa<AllocaInst>(*I)){
						AllocaInst *ai = (AllocaInst *)&*I;
						if (ai->getAllocatedType()->isArrayTy()){
							int NumElements = ((const ArrayType *)ai->getAllocatedType())->getNumElements();
							Graph::getOrInsertNode(inequalityGraph, (Value *)ai, NumElements);
						}
					}
					else if (isa<ICmpInst>(*I)){
                                                ICmpInst *icmpInstr = cast<ICmpInst>(&*I);    
                                                BasicBlock *instrBlock= icmpInstr->getParent();
                                                if ((instrBlock)->getName().startswith(StringRef(upperChkBlock))){
                                                        UB_arrayCheckInstList.push_back(&*I);
                                                }   
                                        }   
 
				}
				for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
					if (isa<PHINode>(*I)){
						PHINode *phi = (PHINode *)(&*I);
						Graph::INEQNode  *res = Graph::getOrInsertNode(inequalityGraph, (Value *)phi, 0);
						res->isPhi = true;
						map<Value*, Graph::INEQNode * > *arrayLengthPtr = &(inequalityGraph->arrayLengthList);
						for (int i = 0, total = phi->getNumIncomingValues(); i < total; i++){
							Value *inVal = phi->getIncomingValue(i);
							if (isa<Constant>(*inVal)){
                                        	                 if (!isa<ConstantInt>(*inVal))
                                                	                 continue;
	
								ConstantInt *cons = cast<ConstantInt>(inVal);
								for (map<Value*, Graph::INEQNode * >::iterator AI = (*arrayLengthPtr).begin(),
										AE = (*arrayLengthPtr).end(); AI != AE; ++AI){
									//edgeWeight  of the edge = cons - arraylength
									//cons->getSExtValue()-
									Graph::insertEdge((*AI).second, res,cons->getSExtValue()-(*AI).second->length);
							}
							continue;
						}
						Graph::INEQNode  *in = Graph::getOrInsertNode(inequalityGraph, inVal, 0);
						Graph::insertEdge(in, res, 0);
					}
				}else if(isa<BinaryOperator>(*I)){
					int op = I->getOpcode();
					if(op == Instruction::Add || op == Instruction::Sub || op == Instruction::FAdd || op == Instruction::FSub){
						Value* varOprnd ;
						ConstantInt* constOprnd ;

						int opType = ( (op == Instruction::Add || op == Instruction::FAdd) )?1:-1;
						if(isa<ConstantInt>(*(I->getOperand(0)))){
							constOprnd  = cast<ConstantInt>(I->getOperand(0));
							varOprnd  = I->getOperand(1);
						}else if(isa<ConstantInt>(*(I->getOperand(1)))){
							constOprnd  = cast<ConstantInt>(I->getOperand(1));
							varOprnd  = I->getOperand(0);
						}else
							continue;

						Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,varOprnd ,0);
						Graph::INEQNode * ndDest  = Graph::getOrInsertNode(inequalityGraph,(Value*)(&*I),0);
						Graph::insertEdge(ndSrc ,ndDest ,(opType * constOprnd ->getSExtValue()));
					}
				}else if(isa<SExtInst>(*I)){
					Value* operand = I->getOperand(0);
					Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,operand,0);
					Graph::INEQNode * ndDest  = Graph::getOrInsertNode(inequalityGraph,(Value*)(&*I),0);
					Graph::insertEdge(ndSrc ,ndDest ,0);

				}else if(isa<CallInst>(*I)){
					//I->dump();e
					//Deal with pair of PI functions here
					inst_iterator temp_I = I;
					Graph::INEQNode * ndDest [2];
					int i = 0, cntPI = 0;
					do{
						Function *func = cast<CallInst>(&*temp_I)->getCalledFunction();
						if(func != NULL && func->hasName()){
							if(func->getName().startswith(StringRef(piFoo ))){
								Graph::INEQNode * ndSrc  = Graph::getOrInsertNode(inequalityGraph,cast<CallInst>(&*temp_I)->getArgOperand(0),0);

								ndDest [cntPI] = Graph::getOrInsertNode(inequalityGraph,((Value*)&*temp_I),0);

								Graph::insertEdge(ndSrc ,ndDest [cntPI],0);
								i--;
								cntPI++;
							}
						}
						temp_I++;
						i++;
					}while(isa<CallInst>(*temp_I) && i == 0);

					if(cntPI>0){
						int trueBB  = -1;
						BranchInst* brI = cast<BranchInst>(I->getParent()->getSinglePredecessor()->getTerminator());
						if(brI->getSuccessor(0) == I->getParent())
							trueBB  = 1;

						CmpInst* cmpI = cast<CmpInst>(brI->getCondition());
						int predicate = cmpI->getPredicate();
						int predicateClass;
						//Identifies the type of branch compare instr
						if(predicate == CmpInst::FCMP_OLT || predicate == CmpInst::FCMP_ULT || predicate == CmpInst::ICMP_ULT || predicate == CmpInst::ICMP_SLT){
							predicate = 1;
							predicateClass = 1;

						}else if(predicate == CmpInst::FCMP_OEQ ||predicate == CmpInst::FCMP_OLE || predicate == CmpInst::FCMP_ULE || predicate == CmpInst::FCMP_UEQ || predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SLE || predicate == CmpInst::ICMP_EQ){
							predicate = 1;
							predicateClass = 2;

						}else if(predicate == CmpInst::FCMP_OGT || predicate == CmpInst::FCMP_UGT || predicate == CmpInst::ICMP_UGT || predicate == CmpInst::ICMP_SGT){
							predicate = -1;
							predicateClass = -1;

						}else if(predicate == CmpInst::FCMP_OGE || predicate == CmpInst::FCMP_UGE || predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_SGE){
							predicate = -1;
							predicateClass = -2;

						}else{
							predicate = 0;
						}


						Value *operand1, *operand2;
						int operandLoc;

						if(cntPI == 1){//Array bounds check
							if(isa<ConstantInt>(*(cmpI->getOperand(0)))){
								operand1 = cmpI->getOperand(1);
								operand2 = cmpI->getOperand(0);
								operandLoc = -1;
							}else if(isa<ConstantInt>(*(cmpI->getOperand(1)))){
								operand1 = cmpI->getOperand(0);
								operand2 = cmpI->getOperand(1);
								operandLoc = 1;
							}else
								continue;
							if(trueBB  * predicate * operandLoc > 0)//Ignore cases where variable is greater than constant since we
								//are only considering upper bound checksin this case
								for(std::map<Value*, Graph::INEQNode * >::iterator it = (inequalityGraph->arrayLengthList).begin(); it !=(inequalityGraph->arrayLengthList).end(); ++it){
									if(predicateClass == 1){
										Graph::insertEdge(it->second,ndDest [0],(cast<ConstantInt>(operand2)->getSExtValue() - 1 - it->second->length));
									}
									else{
										Graph::insertEdge(it->second,ndDest [0],(cast<ConstantInt>(operand2)->getSExtValue() - it->second->length));
									}

								}

						}else{//cntPI == 2 for  'if, while'
							I++;
							if(trueBB  == 1 &&  predicate == 1){
								if(predicateClass == 1)
									Graph::insertEdge(ndDest [1], ndDest [0], -1);
								else
									Graph::insertEdge(ndDest [1], ndDest [0], 0);
							}
							else if(trueBB  == 1 &&  predicate == -1){
								if(predicateClass == -1)
									Graph::insertEdge(ndDest [0], ndDest [1], -1);
								else
									Graph::insertEdge(ndDest [0], ndDest [1], 0);
							}    
							else if(trueBB  == -1 &&  predicate == 1){
								predicate = cmpI->getPredicate();
								if(predicate == CmpInst::FCMP_OLT || predicate == CmpInst::FCMP_ULT || predicate == CmpInst::ICMP_ULT || predicate == CmpInst::ICMP_SLT){
									Graph::insertEdge(ndDest [0], ndDest [1], 0);
								}else if(predicate == CmpInst::FCMP_OLE || predicate == CmpInst::FCMP_ULE || predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SLE){
									Graph::insertEdge(ndDest [0], ndDest [1], -1);
								}    
							}else if(trueBB  == -1 &&  predicate == -1){
								predicate = cmpI->getPredicate();
								if(predicate == CmpInst::FCMP_OGT || predicate == CmpInst::FCMP_UGT || predicate == CmpInst::ICMP_UGT || predicate == CmpInst::ICMP_SGT){
									Graph::insertEdge(ndDest [1], ndDest [0], 0);
								}else if(predicate == CmpInst::FCMP_OGE || predicate == CmpInst::FCMP_UGE || predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_SGE){
									Graph::insertEdge(ndDest [1], ndDest [0], -1);
								}
							}
						}

					}
				}
			}

/*				  //Print out graph
                  int count = 0;
                  for (std::map<Value *, Graph::INEQNode* >::iterator PI = inequalityGraph->variableList.begin(),
                  PE = inequalityGraph->variableList.end(); PI != PE; ++PI){

                  errs() << "\nNode" << count; PI->first->dump(); //errs() << "\n";
                  for (std::map<Graph::INEQNode*, int >::iterator PII = PI->second->out.begin(),
                  PEE = PI->second->out.end(); PII != PEE; ++PII){
                  errs() << "Node" << count << "outlist::To"; PII->first->value->dump(); errs() << " Weight::" << PII->second << "\n";
                  }
                  count++;
                  }

                  for (std::map<Value *, Graph::INEQNode* >::iterator PI = inequalityGraph->arrayLengthList.begin(),
                  PE = inequalityGraph->arrayLengthList.end(); PI != PE; ++PI){

                  errs() << "\nNode" << count; PI->first->dump(); //errs() << "\n";
                  for (std::map<Graph::INEQNode*, int >::iterator PII = PI->second->out.begin(),
                  PEE = PI->second->out.end(); PII != PEE; ++PII){
                  errs() << "Node" << count << "outlist::To";  PII->first->value->dump(); errs() << " Weight::" << PII->second << "\n";
                  }
                  count++;
                  }
*/

				return inequalityGraph;
			}

		};

		char ABCDPass::ID = 0;
		RegisterPass<ABCDPass> X("abcd", "Inequality graph construction", false, false);
	}

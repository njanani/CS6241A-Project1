#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Argument.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/LLVMContext.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <cstdio>
#include <vector>

//NOTE:  Run this and then run Mem2Reg. The pi function just returns
//the value passed to them.  Since a new assignment is made, mem2reg
//sets up the SSA correctly and the output becomes essa.  Another nice
//benefit is that Mem2Reg also automically adds the necessary PHI nodes.


//debug off
//#define DEBUG

#ifdef DEBUG
#define DEBUG_PRINT(text) errs() << text << "\n"

#else   //do nothing
#define DEBUG_PRINT(text)

#endif

using namespace llvm;

struct ESSA : public ModulePass
{
       static char ID; // Pass identification, replacement for typeid
       ESSA() : ModulePass(ID) {}

       virtual bool runOnModule(Module &M)
       {
               LLVMContext &C = M.getContext();

               //errs() << "Pass called sucessfully!\n";
               std::vector<BranchInst*> vCondBranch;

               //Function *pi = (Function*)M.getOrInsertFunction("piInt", Type::getInt32Ty(C), Type::getInt32Ty(C), NULL);
               //BasicBlock* piBlock = BasicBlock::Create(C, "piFuncBlock", pi);
               //IRBuilder<> builder(piBlock);
               //builder.CreateRet(pi->arg_begin());

               //first go through and grab all of the conditional branches
               for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI)
               {
                       for(Function::iterator b = MI->begin(), end = MI->end(); b != end; ++b)
                       {
                               //leave func defs alone
                               if (!MI->isDeclaration())
                               {
                                       if(BranchInst *bi = dyn_cast<BranchInst>(b->getTerminator()))
                                       {
                                               if(bi->isConditional())
                                               {
                                                       //errs() << "Have a conditional branch!\n";
                                                       vCondBranch.push_back(bi);
                                               }
                                       }
                               }
                       }
               }
               for(std::vector<BranchInst*>::iterator i = vCondBranch.begin(), e = vCondBranch.end(); i != e; ++i)
               {
                       DEBUG_PRINT("Examining a conditional branch!");
                       Value *ops[2];
                       if(CmpInst *cmp = dyn_cast<CmpInst>((*i)->getCondition()))
                       {
               if (cmp->getNumOperands() < 2)
                       continue;
               if (!cmp->isIntPredicate())
                   continue;

                               ops[0] = cmp->getOperand(0);
                               ops[1] = cmp->getOperand(1);

                               //for(unsigned int x = 0; x < (*i)->getNumSuccessors(); ++x)
                               //{
                                       BasicBlock* trueBlock = (*i)->getSuccessor(0);
                                       BasicBlock* falseBlock = (*i)->getSuccessor(1);

                                       //BasicBlock* curr = (*i)->getSuccessor(x);
                                       IRBuilder<> builder(trueBlock->getFirstNonPHI());
                                       //builder.SetInsertPoint(curr->getFirstNonPHI());
                                       if(!isa<Constant>(ops[0]))
                                       {
                                               if(isa<LoadInst>(ops[0]))
                                               {
                                                       pred_iterator PI = pred_begin(trueBlock);
                                                       BasicBlock* Pred = *PI;

                                                       if(++PI != pred_end(trueBlock))
                                                               continue;

                                                       PHINode* pi;

                                                       pi = PHINode::Create(ops[0]->getType(), 1, "piFunc_t", trueBlock->begin());
                                                       pi->addIncoming(ops[0], Pred);

                                                       builder.SetInsertPoint(trueBlock->getFirstNonPHI());
                                               builder.CreateStore(pi, ((LoadInst*)ops[0])->getOperand(0));

                                                       PI = pred_begin(falseBlock);
                                                       Pred = *PI;

                                                       if(++PI != pred_end(falseBlock))
                                                               continue;

                                                       pi = PHINode::Create(ops[0]->getType(), 1, "piFunc_f", falseBlock->begin());
                                                       pi->addIncoming(ops[0], Pred);

                                                       builder.SetInsertPoint(falseBlock->getFirstNonPHI());
                                               builder.CreateStore(pi, ((LoadInst*)ops[0])->getOperand(0));


                                               }
                                       }
                                       if(!isa<Constant>(ops[1]))
                                       {
                                               if(isa<LoadInst>(ops[1]))
                                               {
                                                       pred_iterator PI = pred_begin(trueBlock);
                                                       BasicBlock* Pred = *PI;

                                                       if(++PI != pred_end(trueBlock))
                                                               continue;

                                                       PHINode* pi;


                                                       pi = PHINode::Create(ops[1]->getType(), 1, "piFunc_t", trueBlock->begin());
                                                       pi->addIncoming(ops[1], Pred);

                                                       builder.SetInsertPoint(trueBlock->getFirstNonPHI());
                                                       builder.CreateStore(pi, ((LoadInst*)ops[1])->getOperand(0));

                                                       PI = pred_begin(falseBlock);
                                                       Pred = *PI;

                                                       if(++PI != pred_end(falseBlock))
                                                               continue;

                                                       pi = PHINode::Create(ops[1]->getType(), 1, "piFunc_f", falseBlock->begin());
                                                       pi->addIncoming(ops[1], Pred);

                                                       builder.SetInsertPoint(falseBlock->getFirstNonPHI());
                                                       builder.CreateStore(pi, ((LoadInst*)ops[1])->getOperand(0));
                                               }
                                       }
                               //}
                       }
               }

               DEBUG_PRINT("Done!");

               return true;
       }
};

char ESSA::ID = 1;
static RegisterPass<ESSA> ESSA("essa", "convert ess to essa");

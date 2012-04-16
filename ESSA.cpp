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

#else	//do nothing
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

		Function *pi = (Function*)M.getOrInsertFunction("piInt", Type::getInt32Ty(C), Type::getInt32Ty(C), NULL);
		BasicBlock* piBlock = BasicBlock::Create(C, "piFuncBlock", pi);
		IRBuilder<> builder(piBlock);
		builder.CreateRet(pi->arg_begin());

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
			DEBUG_PRINT("Examining a conditional branch!);
			Value *ops[2];
			CmpInst *cmp = dyn_cast<CmpInst>((*i)->getCondition());

			ops[0] = cmp->getOperand(0);
			ops[1] = cmp->getOperand(1);
				
			for(unsigned int x = 0; x < (*i)->getNumSuccessors(); ++x)
			{
							
				BasicBlock* curr = (*i)->getSuccessor(x);											
				
				for(int y = 0; y < 2; ++y)
				{
					//dont bother with constants.  
					//Note after mem2reg may still have some with constants
					if(!isa<Constant>(ops[y])) 
					{	
						BasicBlock::iterator iter = curr->begin();
						BasicBlock* newBlock = SplitBlock(curr, iter, this);
						
						BasicBlock* piBlock = BasicBlock::Create(C, "piFuncCall", curr->getParent(), newBlock);

						//remove old terminator
						builder.SetInsertPoint(curr);
						TerminatorInst* term = curr->getTerminator();
						DEBUG_PRINT("Joy");
						term->eraseFromParent();
						//create new one
						builder.CreateBr(piBlock);
						
					
						builder.SetInsertPoint(piBlock);
						CallInst* cPi = builder.CreateCall(pi, ops[y]); 
						DEBUG_PRINT("Made it after create all!!!");
						builder.CreateStore(cPi, ((LoadInst*)ops[y])->getOperand(0));
						DEBUG_PRINT("Still no seg faults!!");
						builder.CreateBr(newBlock);
					}						
				}
			}
		}

		DEBUG_PRINT("Done!");

		return true;
	}
};

char ESSA::ID = 1;
static RegisterPass<ESSA> ESSA("essa", "convert ess to essa");

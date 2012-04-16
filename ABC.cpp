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

using namespace llvm;

struct ABC : public ModulePass 
{
	static char ID; // Pass identification, replacement for typeid
	ABC() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		LLVMContext &C = M.getContext();
		Function *printError_func = (Function*)M.getOrInsertFunction("printErrorMessage", Type::getVoidTy(C), NULL);

		BasicBlock* entryBlock = BasicBlock::Create(C, "", printError_func);
		IRBuilder<> builder(entryBlock);

		Constant *msg = ConstantArray::get(C, "ERROR!  Array Index Out of Bounds", true);

		Constant *zero_32 = Constant::getNullValue(IntegerType::getInt32Ty(C));
		Constant *gep_params[] = {zero_32, zero_32};


		GlobalVariable *errorMsg = new GlobalVariable(M, msg->getType(), true, GlobalValue::InternalLinkage, msg, "errorMsg");
		Function *puts_func = (Function*)(M.getOrInsertFunction("puts", IntegerType::getInt32Ty(C), PointerType::getUnqual(IntegerType::getInt8Ty(C)), NULL));
		Constant *msgptr = ConstantExpr::getGetElementPtr(errorMsg, gep_params);

		Value *puts_params[] = {msgptr};

		CallInst *puts_call = builder.CreateCall(puts_func, puts_params);
		puts_call->setTailCall(false);

		Function *exit_func = cast<Function>(M.getOrInsertFunction("exit", IntegerType::getVoidTy(C), Type::getInt32Ty(C),NULL));

		Value *exit_val = ConstantInt::get(IntegerType::getInt32Ty(C), 1);
		
		//create exit block.  This block prints the error and calls exit system function
		BasicBlock* exitBlock = BasicBlock::Create(C, "exitBlock", printError_func);
		builder.CreateBr(exitBlock);
		builder.SetInsertPoint(exitBlock);


		builder.CreateCall(exit_func,exit_val);
		builder.CreateBr(exitBlock);

		int checksInserted = 0;

		for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI)
		{
			//leave func defs alone
			if (!MI->isDeclaration()) 
			{
				for (inst_iterator I = inst_begin(*MI), E = inst_end(*MI); I != E; ++I)
				{
					Instruction *inst = &*I;
					
					if(GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(inst))
					{
						if (const ArrayType *ar = dyn_cast<ArrayType>(gep->getPointerOperandType()->getElementType()))
						{           
							//increment checks inserted counter
							checksInserted++;
	
							//create split in basic block for function call insertion (branch)
							Instruction* next = inst->getNextNode();
							BasicBlock* oldBlock = inst->getParent();
							BasicBlock* newBlock = SplitBlock(oldBlock, next, this);

							//get upper limit and index used
							unsigned upperLim = ar->getNumElements();
							int index = gep->getNumOperands() - 1;
							Value *vIndexUsed = gep->getOperand(index);
							Value *vUpperLimit = ConstantInt::get(vIndexUsed->getType(), upperLim);

							BasicBlock* checkUpperBlock = BasicBlock::Create(C, "checkUpperBlock", MI, newBlock);
							BasicBlock* checkLowerBlock = BasicBlock::Create(C, "checkLowerBlock", MI, checkUpperBlock);
							
							builder.SetInsertPoint(oldBlock);
							
							//remove old terminator
							TerminatorInst* term = oldBlock->getTerminator();
							term->eraseFromParent();
							//insert new one
							builder.CreateBr(checkUpperBlock);
							
							//configure uppper bound test
							builder.SetInsertPoint(checkUpperBlock);
							Value* condUpperInst = builder.CreateICmpSLT(vIndexUsed, vUpperLimit, "checkUpperBounds");
							BasicBlock* errorBlock = BasicBlock::Create(C, "errorBlock", MI, newBlock);
							builder.CreateCondBr(condUpperInst, checkLowerBlock, errorBlock);

							//configure lower bound test
							builder.SetInsertPoint(checkLowerBlock);
							Value *vLowerLimit = ConstantInt::get(vIndexUsed->getType(), -1);
							Value *condLowerInst = builder.CreateICmpSGT(vIndexUsed, vLowerLimit, "checkLowerBounds");
							builder.CreateCondBr(condLowerInst, newBlock, errorBlock);

							//setup error block.  All this block does is call func to print error and exit
							builder.SetInsertPoint(errorBlock);
							builder.CreateCall(printError_func);
							builder.CreateBr(errorBlock);
						}
					}				
				}
			}
		}
		errs() << "This pass has inserted " << checksInserted << " checks\n";
      return true;
	}
};


char ABC::ID = 0;
static RegisterPass<ABC> ABC("abc", "auto bounds check");

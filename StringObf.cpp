#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"

#include <random>

namespace {

class GlobalStringVariable {
private:
    std::vector<uint8_t> enc;
    std::vector<uint8_t> key;
    llvm::GlobalVariable *glob;
public:
    GlobalStringVariable(std::vector<uint8_t> &v1, std::vector<uint8_t> &v2, llvm::GlobalVariable *g) 
        : enc(v1), key(v2), glob(g) { }
    llvm::GlobalVariable *getGlob() { return glob; }
    std::vector<uint8_t> &getEnc()  { return enc;  }
    std::vector<uint8_t> &getKey()  { return key;  }
};

struct StringObf : llvm::PassInfoMixin<StringObf> {

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        
        std::vector<GlobalStringVariable> globalStrings = getStrings(M);

        // create decode functions
        auto *f = buildDecodeFunction(M);

        // create decode caller
        auto *caller = buildDecodeCallerFunction(M, globalStrings, f);

        // inject call
        injectDecodeCall(M, caller);

        return llvm::PreservedAnalyses::all();
    }

    void injectDecodeCall(llvm::Module &M, llvm::Function *f) {

        auto *main = M.getFunction("main");
        auto &ctx = main->getContext();
        auto &b = main->getEntryBlock();

        auto *bb = llvm::BasicBlock::Create(ctx, "", b.getParent(), &b);
        llvm::IRBuilder<> *builder = new llvm::IRBuilder<>(bb);
        builder->CreateCall(f);
        builder->CreateBr(&b);
    }

    llvm::Function *buildDecodeCallerFunction(llvm::Module &M, std::vector<GlobalStringVariable> &globalStrings, llvm::Function *decodeFunction) {
        auto &ctx = M.getContext();

        llvm::FunctionCallee decodeFunctionCallerCallee = M.getOrInsertFunction(
            "decode_caller",
            llvm::Type::getVoidTy(ctx)
        );

        auto *decodeFunctionCallerFunction = cast<llvm::Function>(decodeFunctionCallerCallee.getCallee());
        decodeFunctionCallerFunction->setCallingConv(llvm::CallingConv::C);

        llvm::BasicBlock *functionBB = llvm::BasicBlock::Create(ctx, "", decodeFunctionCallerFunction);

        llvm::IRBuilder<> *functionBuilder = new llvm::IRBuilder<>(functionBB);

        for(auto &str_var : globalStrings) {
            auto *enc_str = functionBuilder->CreatePointerCast(str_var.getGlob(), llvm::Type::getInt8PtrTy(ctx));
            auto *glob = str_var.getGlob();
            auto key_glob = new llvm::GlobalVariable(
                M,
                glob->getType()->getElementType(),
                true, 
                glob->getLinkage(),
                nullptr, 
                glob->getName(),
                nullptr,
                glob->getThreadLocalMode(),
                glob->getType()->getAddressSpace()
            );
            key_glob->setInitializer(llvm::ConstantDataArray::get(glob->getParent()->getContext(),
                                                                  llvm::ArrayRef<uint8_t>(str_var.getKey())));
            auto *key_str = functionBuilder->CreatePointerCast(key_glob, llvm::Type::getInt8PtrTy(ctx));
            auto *len = llvm::ConstantInt::get(llvm::IntegerType::getInt64Ty(ctx), str_var.getEnc().size());

            functionBuilder->CreateCall(
                decodeFunction,
                { enc_str, key_str, len }
            );

        }
        functionBuilder->CreateRetVoid();
        return decodeFunctionCallerFunction;
    }

    llvm::Function *buildDecodeFunction(llvm::Module &M) {
        auto &ctx = M.getContext();

        llvm::FunctionCallee decodeCallee = M.getOrInsertFunction(
            "decode",
            llvm::Type::getVoidTy(ctx),
            llvm::Type::getInt8PtrTy(ctx),
            llvm::Type::getInt8PtrTy(ctx),
            llvm::Type::getInt64Ty(ctx)
        );

        llvm::Function *decodeFunction = cast<llvm::Function>(decodeCallee.getCallee());
        decodeFunction->setCallingConv(llvm::CallingConv::C);

        llvm::BasicBlock *functionBB = llvm::BasicBlock::Create(ctx, "", decodeFunction);

        // now build the decode function    
        llvm::IRBuilder<> *functionBuilder = new llvm::IRBuilder<>(functionBB);

        auto *v0 = decodeFunction->arg_begin();
        auto *v1 = decodeFunction->arg_begin()+1;
        auto *v2 = decodeFunction->arg_begin()+2;

        auto *v4 = functionBuilder->CreateAlloca(llvm::Type::getInt8PtrTy(ctx));
        auto *v5 = functionBuilder->CreateAlloca(llvm::Type::getInt8PtrTy(ctx));
        auto *v6 = functionBuilder->CreateAlloca(llvm::Type::getInt64Ty(ctx));

        auto *store1 = functionBuilder->CreateStore(v0, v4);
        auto *store2 = functionBuilder->CreateStore(v1, v5);
        auto *store3 = functionBuilder->CreateStore(v2, v6);

        llvm::BasicBlock *functionBB7 = llvm::BasicBlock::Create(ctx, "functionBB7", decodeFunction);
        auto *branch1 = functionBuilder->CreateBr(functionBB7);

        llvm::IRBuilder<> *functionBB7Builder = new llvm::IRBuilder<>(functionBB7);
        auto *v8 = functionBB7Builder->CreateLoad(llvm::Type::getInt64Ty(ctx), v6, false, "v7");
        auto *v9 = functionBB7Builder->CreateAdd(v8, llvm::ConstantInt::getSigned(llvm::IntegerType::get(ctx, 64), -1));
        auto *store4 = functionBB7Builder->CreateStore(v9, v6);
        auto *v10 = functionBB7Builder->CreateICmpSGE(v9, llvm::ConstantInt::getSigned(llvm::IntegerType::get(ctx, 64), 0));

        llvm::BasicBlock *functionBB11 = llvm::BasicBlock::Create(ctx, "functionBB11", decodeFunction);
        llvm::BasicBlock *functionBB24 = llvm::BasicBlock::Create(ctx, "functionBB24", decodeFunction);
        auto *branch2 = functionBB7Builder->CreateCondBr(v10, functionBB11, functionBB24);

        llvm::IRBuilder<> *functionBB11Builder = new llvm::IRBuilder<>(functionBB11);
        llvm::IRBuilder<> *functionBB24Builder = new llvm::IRBuilder<>(functionBB24);

        auto *v12 = functionBB11Builder->CreateLoad(llvm::Type::getInt8PtrTy(ctx), v5, false);
        auto *v13 = functionBB11Builder->CreateLoad(llvm::Type::getInt64Ty(ctx), v6, false);
        auto *v14 = functionBB11Builder->CreateInBoundsGEP(v12, v13);
        auto *v15 = functionBB11Builder->CreateLoad(llvm::Type::getInt8Ty(ctx), v14);
        auto *v16 = functionBB11Builder->CreateSExt(v15, llvm::Type::getInt32Ty(ctx));
        auto *v17 = functionBB11Builder->CreateLoad(llvm::Type::getInt8PtrTy(ctx), v4, false);
        auto *v18 = functionBB11Builder->CreateLoad(llvm::Type::getInt64Ty(ctx), v6, false);
        auto *v19 = functionBB11Builder->CreateInBoundsGEP(v17, v18);
        auto *v20 = functionBB11Builder->CreateLoad(llvm::Type::getInt8Ty(ctx), v19, false);
        auto *v21 = functionBB11Builder->CreateSExt(v20, llvm::Type::getInt32Ty(ctx));
        auto *v22 = functionBB11Builder->CreateXor(v21, v16);
        auto *v23 = functionBB11Builder->CreateTrunc(v22, llvm::Type::getInt8Ty(ctx));
        auto *store5 = functionBB11Builder->CreateStore(v23, v19);
        auto *branch3 = functionBB11Builder->CreateBr(functionBB7);

        auto *ret = functionBB24Builder->CreateRetVoid();

        return decodeFunction;
    }

    std::vector<GlobalStringVariable> getStrings(llvm::Module &M) {

        // std::vector<llvm::GlobalVariable *> enc, key;
        std::vector<GlobalStringVariable> enc_key_vec;

        std::default_random_engine generator;
        std::uniform_int_distribution<uint8_t> distribution(0, 255);

        // iterate all global variable in module.
        for(auto &glob : M.globals()) {
            if (!glob.hasInitializer() || glob.hasExternalLinkage()) continue;

            llvm::StringRef section = glob.getSection();
            if (section == "llvm.metadata") continue;

            llvm::Constant *Initializer = glob.getInitializer();

            if (isa<llvm::ConstantDataArray>(Initializer)) {
                auto arr = cast<llvm::ConstantDataArray>(Initializer);
                if (!arr->isString()) continue;

                const char *buf = arr->getAsString().begin();
                const int size = arr->getAsString().size();
                if (!buf) continue;

                // generate xor key and encode the string
                std::vector<uint8_t> enc_str, xor_key;
                for(size_t i = 0; i < size; ++i) {
                    uint8_t key = distribution(generator);
                    xor_key.push_back(key);
                    enc_str.push_back(buf[i] ^ key);
                }

                enc_key_vec.push_back(
                    {
                        enc_str, xor_key, &glob
                    }
                );

                llvm::Constant *enc_dt = llvm::ConstantDataArray::get(glob.getParent()->getContext(),
                                                                      llvm::ArrayRef<uint8_t>(enc_str));
                glob.setInitializer(enc_dt);
                glob.setConstant(false);

            }
        }

        return enc_key_vec;
    }
};

};

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "StringObf", LLVM_VERSION_STRING, [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback([](llvm::StringRef Name, llvm::ModulePassManager &MPM,
                                                  llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                if (Name == "stringobf") {
                    MPM.addPass(StringObf());
                    return true;
                }
                return false;
            });
        }};
}

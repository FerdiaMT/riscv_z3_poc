#include <iostream>
#include "llvm/Support/CommandLine.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"

// this creates a label for grouping stuff
using namespace clang;

class MyConsumer : public ASTConsumer {
public:
    void HandleTranslationUnit(ASTContext& Context) override {
        std::cout << "AST reciebed !" << std::endl;

        //this is the root of the translation
        auto* root = Context.getTranslationUnitDecl();

        for (const auto& node : root->decls()) 
        {
            if(FunctionDecl* FD = dyn_cast<FunctionDecl>(node))
            {
                std::cout << " func found in our tree: " << FD->getNameAsString() <<std::endl;
            }
            else
            {
                std::cout << " type found in our tree: " << node->getDeclKindName() <<std::endl;
            }
        }

    }
};

class MyAction : public ASTFrontendAction { //inherits from the AST frontend actions (such as the print tree we aere doing before)
    public:
        std::unique_ptr<ASTConsumer> CreateASTConsumer( CompilerInstance& CI, StringRef file )  override { //creates an ASTConsumer, pass in the compiler and file
            
            std::cout << "CreateASTConsumer called!" << std::endl;
            
            return std::make_unique<MyConsumer>(); // return the consumer (who now has the ast to himself)
        }
};
static llvm::cl::OptionCategory MyCategory("my options");
int main(int argc , const char** argv) {

    std::cout << "ARGS PASSSED IN" << std::endl;
    std::cout<< "===============" <<  std::endl;
    for(int i = 1; i < argc; i++)
    {
        std::cout << argv[i] << std::endl;
    }

    std::cout<< "===============" <<  std::endl;

    auto ExpectedParser = clang::tooling::CommonOptionsParser::create(argc,argv,MyCategory);

    // if(!ExpectedParser)
    // {
    //     llvm::errs() << ExpectedParser.takeError();
    //     return 1;
    // }
    // else
    // {
    //     std::cout << "Args passed in all right";
    // }

    // unwrapping the Expected parser with get, using & to just transfer the pointer
    clang::tooling::CommonOptionsParser& OptionsParser = ExpectedParser.get(); 

    std::vector<std::string> sources = OptionsParser.getSourcePathList();

    std::cout << "I will analyze " << sources.size() << " file(s):" << std::endl;
    for (const auto& source : sources) {
        std::cout << "  - " << source << std::endl;
    }

    clang::tooling::ClangTool myTool(OptionsParser.getCompilations(), OptionsParser.getSourcePathList());

    int result = myTool.run(clang::tooling::newFrontendActionFactory<MyAction>().get());

    std::cout << "tool finished with result "<< result << std::endl;

    return result;
}
#include <iostream>
#include <clang/Tooling/CommonOptionsParser.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/CommandLine.h>
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Attr.h"

static llvm::cl::OptionCategory optionList("opListA");

class myConsumer : public clang::ASTConsumer 
{
    //consumer is provided the AST tree with this method, we shall override to include our custom logic
    void HandleTranslationUnit(clang::ASTContext& context) override
    {
        auto tree = context.getTranslationUnitDecl();

        for( const auto& node : tree -> decls() )
        {
            //iterating through every node on the tree

            //check if the current node is a function
            if( clang::FunctionDecl* FD = clang::dyn_cast<clang::FunctionDecl>(node) )
            {
                //check if it has any attributes (part we added)
                if( FD -> hasAttrs() )
                {
                    std::cout << FD->getNameAsString() <<" has the attributes: " << std::endl;
                    //functions can have many attributes
                    for(const clang::Attr* attr : FD->attrs() )
                    {
                        std::cout << attr->getAttrName() << std::endl;
                    }
                }
                else
                {
                    std::cout << FD->getNameAsString() <<" has no attributes " << std::endl;                    
                }
            }
        }
    }
};

class myAction : public clang::ASTFrontendAction
{
    public:
        //Overidieing the ASTConsumer logic to create our own custom one with the difference being it can parse our cusom annotations
        std::unique_ptr<clang::ASTConsumer> CreateASTConsumer( clang::CompilerInstance& CI, clang::StringRef file) override
        {
            return std::make_unique<myConsumer>();
        }
};

int main(int argc, const char** argv)
{
    //create the commonOptionsParser
    auto expectedParser = clang::tooling::CommonOptionsParser::create(argc,argv,optionList);

    if(!expectedParser)
    {
        llvm::errs() << expectedParser.takeError();
        return 1;
    }
    //create our commonOptionsParser
    clang::tooling::CommonOptionsParser& parser = expectedParser.get();
    // this parser contains a list of options and compiler flags

    //now we make our tool
    clang::tooling::ClangTool tool(parser.getCompilations() , parser.getSourcePathList());
    // this tool has now been passed the parsed list of compilations and sourcepathlists

    //create a factory that knows how to make instances of action
    auto factory = clang::tooling::newFrontendActionFactory<myAction>();

    //get a pointer to this factory object we just made
    clang::tooling::FrontendActionFactory* factoryPtr = factory.get();

    //execute by passing in a factory maker for the action
    tool.run(factoryPtr);




    return 0;
}
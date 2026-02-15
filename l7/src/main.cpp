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
#include <array>

static llvm::cl::OptionCategory optionList("opListA");

struct FunctionAnnotations
{
    inline const static std::array<std::string, 2> varTypNames = {"requires", "ensures"};
    enum varTyp
    {
        REQ,
        ENS
    };
    struct annotation
    {
        varTyp type;
        std::string val;

        std::string toStr() const
        {
            return FunctionAnnotations::varTypNames[type] + ": " + val;
        }
    };

    std::string functionName; // store the function this annotation applys to
    std::vector<annotation> annotations; // list the anotations described to the function

    //function that turns string into annotion
    annotation parseAnnotation(std::string input)
    {
        annotation a;

        size_t pos = input.find(":");
        if(pos == std::string::npos)
        {
            std::cerr << "ANALYZER ERROR, could not find colon in provided param";
            return a;
        }

        //find type
        if(input.find("requires")==0)
        {
            a.type = varTyp::REQ;
        }
        else if(input.find("ensures")==0)
        {
            a.type = varTyp::ENS;
        }
        else
        {
            std::cerr << "ANALYZER ERROR, could not find valid contract type for input: " << input.substr(0,pos) << std::endl;
            return a;
        }

        //parse in value / condition
        a.val = input.substr(pos+1);

        return a;
    }

    void addAnnotation(std::string input)
    {
        annotations.push_back(parseAnnotation(input));
    }
};

class myConsumer : public clang::ASTConsumer 
{
    std::vector<FunctionAnnotations> allFuncs;
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
                FunctionAnnotations funcData; // create our empty struct for storing info about functions annotation
                funcData.functionName = FD->getNameAsString();

                //check if it has any attributes (part we added)
                if( FD -> hasAttrs() )
                {
                    //std::cout << FD->getNameAsString() <<" has the attributes: " << std::endl;
                    //functions can have many attributes
                    for(const clang::Attr* attr : FD->attrs() )
                    {
                        // check if its an annotate attr (remove stuff like deprecated etc)
                        if(const clang::AnnotateAttr* anoAttr = clang::dyn_cast<clang::AnnotateAttr>(attr) )
                        {
                            std::string annotation = anoAttr->getAnnotation().str();
                            
                            funcData.addAnnotation(annotation);
                            //now we can basically parse through the possible annotations using annotation.find etc to match it to a certain action / construct z3 code with api calls

                            //std::cout << << std::endl;
                        }
                    }
                }
                else
                {
                    std::cout << FD->getNameAsString() <<" has no attributes " << std::endl;                    
                }

                //before moving onto next function node , push back into our list
                allFuncs.push_back(funcData);
            }
        }

        printSummary(); // before function ends, print out what has been analyzed
    }
    void printSummary()
    {
        for(const auto& func : allFuncs)
        {
            std::cout << func.functionName << " : " <<std::endl;
            for(const FunctionAnnotations::annotation& attr : func.annotations)
            {
                std::cout<< " - " << attr.toStr() << std::endl;
            }
            std::cout << std::endl;
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
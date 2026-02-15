#include <iostream>
#include "llvm/Support/CommandLine.h"
#include "clang/Tooling/CommonOptionsParser.h"

// this creates a label for grouping stuff
static llvm::cl::OptionCategory MyCategory ("my options");

int main(int argc , const char** argv) {

    auto ExpectedParser = clang::tooling::CommonOptionsParser::create(argc,argv,MyCategory);

    if(!ExpectedParser)
    {
        llvm::errs() << ExpectedParser.takeError();
        return 1;
    }
    else
    {
        std::cout << "Args passed in all right";
    }

    

    return 0;
}
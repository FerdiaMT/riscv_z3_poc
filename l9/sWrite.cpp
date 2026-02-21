#include <iostream>
#include <fstream>
#include <cstdlib>

int executeSmt(const char* fName)
{
    const char* execCmd;
    system("z3 hello.smt2");

    return 0;
}

int main()
{
    const char* fName = "hello.smt2";
    std::ofstream out(fName);


    out << "(declare-const x Int)" << std::endl;
    out << "(assert (> x 5))"<< std::endl;
    out << "(check-sat)"<< std::endl;
    out << "(get-model)"<< std::endl;

    out.close();

    int res = executeSmt(fName);


    

    return res;
}
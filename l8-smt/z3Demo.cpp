#include <iostream>
#include <fstream>
#include <array>
#include <memory>
#include <string>
int main()
{
    //Writing some hardcoded z3 to a file to verify it
    std::string filename = "testX.smt2";
    std::ofstream out(filename);
    out << "(declare-const x Int)\n";
    out << "(assert (> x 5))\n";
    out << "(assert (< x 10))\n";
    out << "(check-sat)\n";
    out << "(get-model)\n";
    out.close();

    //run the z3 command

    std::string cmd = "z3 "+filename;

    std::array<char,128> buffer;
    std::string res;

    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd.c_str(), "r"),pclose); //some stackoverflow junk

    if(!pipe)
    {
        std::cerr<< "ERROR, pipe not intitialized correctly";
    }

    while(fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr)
    {
        res += buffer.data();
    }

    std::cout<<res<<std::endl;

    if (res.find("sat") != std::string::npos) 
    {
        std::cout << "\n CODE IS SATISFIABLE" << std::endl;
    } 
    else if (res.find("unsat") != std::string::npos) 
    {
        std::cout << "\n CODE IS UNSATISFIABLE" << std::endl;
    }
}
#include <fstream>
#include <vector>
#include <memory>
#include <sstream>
#include <iostream>

int main()
{
    // std::ofstream out("output.txt");

    // out << "hello ";
    // out << "world" << std::endl;
    // out.close();

    // if (!out)
    // {
    //     std::cerr << "Failed to open stream" << std::endl;
    //     return 0;
    // }

    std::ifstream inputFileStream("output.txt");
    std::stringstream buffer;
    buffer << inputFileStream.rdbuf();
    std::string content = buffer.str();

    std::cout << content << std::endl;

    return 0;
}
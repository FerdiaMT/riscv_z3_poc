#include <iostream>
#include <vector>
#include <string>

int main()
{
    std::vector<int> numbers = {1, 2, 3, 4, 5};

    for(int i = 0 ; i < numbers.size(); i++)
    {
        std::cout<<numbers.at(i)<<std::endl;
    }

    std::cout<<std::endl;

    for(int num : numbers)
    {
        std::cout << num << std::endl;
    }

    std::cout<<std::endl;

    for(auto num : numbers)
    {
        std::cout<< num << std::endl;
    }

    //auto looping through a vector of strings

    std::vector<std::string> words = {"hello", "world", "andstuff"};

    for (auto word : words) //causes a copy
    {
        std::cout<< word << std::endl;
    }

    std::cout<<std::endl;

    for(const auto& word : words) // this is the best way to do it
    {
        std::cout<< word << std::endl;
    }

    // how come this isnt dereferenced

    std::string str= "helloworld3";
    std::string& str2  = str;

    std::cout<< *str2 << std::endl;

    return 0;
}
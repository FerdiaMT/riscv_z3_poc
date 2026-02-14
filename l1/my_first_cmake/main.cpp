#include <iostream>
#include <optional>

std::optional<int> divide(int a, int b) 
{
    if ( b==0 ) return std::nullopt;
    return a/b;
}

int main() {
    std::cout << "My first project" << std::endl;
    auto result = divide (10,2);
    if ( result ) {
        std::cout << "Result: " << *result << std::endl;
    };

    auto bad_res = divide(10,0);
    if (!bad_res) {
        s
    }
    return 0;
}
#include <iostream>
#include <string>
#include <vector>

struct Annotation {
    std::string type;   // "requires" or "ensures"
    std::string value;  // Tcondition
};

Annotation parseAnnotation(const std::string& annotation) {
    Annotation result;
    
    // first find colon
    size_t colonPos = annotation.find(":");
    
    // If no colon, invalid
    if (colonPos == std::string::npos) {
        result.type = "INVALID";
        result.value = "";
        return result;
    }
    
    // type is everything before colon
    result.type = annotation.substr(0, colonPos);
    
    // val is everything after
    result.value = annotation.substr(colonPos + 1);
    
    return result;
}

void testParsing() {
    std::cout << "\n=== Parsing Test ===" << std::endl;
    
    std::vector<std::string> annotations = {
        "requires:x > 0",
        "ensures:result > x",
        "requires:index < array.size()",
        "invalid_annotation"  // error here
    };
    
    for (const auto& ann : annotations) {
        Annotation parsed = parseAnnotation(ann);
        std::cout << "Input: " << ann << std::endl;
        std::cout << "  Type: " << parsed.type << std::endl;
        std::cout << "  Value: " << parsed.value << std::endl;
    }
}

int main()
{
    testParsing();
    return 0;
}
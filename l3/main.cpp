#include <map>
#include <iostream>
#include <string>
#include <vector>

struct TreeNode
{
    std::string type;
    std::string value;
    std::vector<TreeNode> children;

    TreeNode(std::string t, std::string v="") : type(t) , value(v) {}

    void addChild(const TreeNode& child)
    {
        children.push_back(child);
    }
};

void printTree(const TreeNode& node, int depth = 0)
{
    for(int i = 0 ; i < depth; i++)
    {
        std::cout << "  "; // 2 spaces per depth
    }

    std::cout<< node.type;
    if(!node.value.empty())
    {
        std::cout << " '" << node.value << "'";
    }

    std::cout << std::endl;

    for(const auto& child : node.children)
    {
        printTree(child, depth+1);
    }


}

class SimpleVisitor {
    public:
        void visitFunction(const TreeNode& node)
        {
            std::cout << "Found Function" << node.value << std::endl;
            for (const auto& child : node.children)
            {
                visit(child);
            }
        }
        void visitBinaryOp(const TreeNode& node)
        {
            std::cout << "Found binaryOp " << node.value << std::endl;
            for(const auto& child : node.children)
            {
                visit(child);
            }
        }

        void visit(const TreeNode& node)
        {
            if (node.type == "FunctionDecl") 
            {
                visitFunction(node);
            } 
            else if (node.type == "BinaryOperator") 
            {
                visitBinaryOp(node);
            } 
            else //generic case, just skip to the next one
            {
                for (const auto& child : node.children) 
                {
                    visit(child);
                }
            }
        }
};

class ASTAnalyzer {
    private:
        int functionCount = 0;
        int binaryOpCount = 0;
        int literalCount = 0;
    public:
        void visit(const TreeNode& node)
        {
            if(node.type == "FunctionDecl")
            {
                functionCount++;
            }
            else if (node.type == "BinaryOperator")
            {
                binaryOpCount++;
            }
            else if (node.type == "IntegerLiteral")
            {
                literalCount++;
            }

            for(const auto& child : node.children)
            {
                visit(child);
            }
        }
        void printStats()
        {
            std::cout << "========= VISITOR ANALYZER ========" << std::endl;
            std::cout<< "functions " << functionCount << std::endl;
            std::cout << "binaryOps " << binaryOpCount << std::endl;
            std::cout << "literals: " << literalCount << std::endl;
        }
};

void testVisitor() {
    
    TreeNode root("FunctionDecl", "calculate");
    
    TreeNode body("CompoundStmt");
    
    TreeNode varDecl("VarDecl", "result");
    TreeNode binOp("BinaryOperator", "+");
    binOp.addChild(TreeNode("IntegerLiteral", "5"));
    binOp.addChild(TreeNode("IntegerLiteral", "3"));
    varDecl.addChild(binOp);
    
    body.addChild(varDecl);
    root.addChild(body);

    printTree(root);
    
    // now test the visitor
    ASTAnalyzer analyzer;
    analyzer.visit(root);
    analyzer.printStats();
}


void treeBuilder()
{
    std::cout << "TREE PARSING TEST ==========================" << std::endl;
    //build the AST for int x = 5 + 3
    TreeNode varDecl("VarDecl" , "x");
    TreeNode binaryOperator("BinaryOperator", "+");

    TreeNode integerLiteral("integerLiteral" , "3");
    TreeNode integerLiteral2("integerLiteral" , "5");

    binaryOperator.addChild(integerLiteral);
    binaryOperator.addChild(integerLiteral2);

    varDecl.addChild(binaryOperator);



    printTree(varDecl);
}


int main() // this is our AST style program
{
    testVisitor();
    return 0;
}
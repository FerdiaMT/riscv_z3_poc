[[clang::annotate("requires: x > 0")]]
[[clang::annotate("ensures: result > x")]]
int add(int x)
{
    int result = x+1;
    return result;
}
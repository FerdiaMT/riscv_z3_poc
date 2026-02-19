[[clang::annotate("requires: x > 0")]]
[[clang::annotate("ensures: result > x")]]
int add(int x)
{
    int result = x+1;
    result -=1;
    result +=1;
    return result;
}

[[clang::annotate("requires: x > 0")]]
[[clang::annotate("ensures: result > x")]]
int add_quick(int x)
{
    return x+1;
}

// Can i generate an smt in the most optimal way ??

// arxiv.org/abs/2411.11469 arvix
// ^ look at this f ei feeeeeeel like this
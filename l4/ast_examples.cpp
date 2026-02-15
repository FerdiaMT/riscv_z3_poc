[[clang::annotate("test_annotation")]]
void foo() {}

[[clang::annotate("requires:x > 0")]]
[[clang::annotate("ensures:result >= x")]]
int increment(int x) {
    return x + 1;
}

void bar() {}  // No annotations
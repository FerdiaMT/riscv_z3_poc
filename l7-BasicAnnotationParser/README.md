Ferdia Treacy - 15/2/2026 - FYP prototying

to try this code yourself, run the following

first: ```mkdir build``` and ```cd build```

then:

```cmake .. && make && ./annotationParser ../src/test_annotated.cpp --```

I am using test_annotated.cpp as a file to test out the functionality, but you can pass in any file

currently all this is doing is parsing, but the plan is to feed the struct which contains

- function name
- contract (type : condition)

into a z3 api, which should be able to (once i can also parse in the body code as it wants) verify that the function properly fits to the valid pre + postcondition

I expect that to be next weeks work.
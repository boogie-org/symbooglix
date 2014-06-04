// RUN: %symbooglix %s | %OutputCheck %s
procedure main(p1:bv8)
requires p1 == 0bv8;
{
    // CHECK-L: State 0 terminated with an error
    // CHECK-NEXT-L: The following assertion failed
    // CHECK-NEXT-L: ${CHECKFILE_NAME}:${LINE:+1}: assert p1 == 1bv8;
    assert p1 == 1bv8; // Effectively assert false
}

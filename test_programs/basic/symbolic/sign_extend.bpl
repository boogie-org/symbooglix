// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
procedure main(p1:int, p2:bv8);

// Use the different syntax supported by Boogie
function {:bvbuiltin "sign_extend 8"} se0(bv8) returns(bv16);
function {:bvbuiltin "(_ sign_extend 8)"} se1(bv8) returns(bv16);


implementation main(p1:int, p2:bv8)
{
    var a:bv8;
    assert se0(a) == se1(a);
}

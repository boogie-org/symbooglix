// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
function {:builtin "div"} my_div(int, int) returns(int);

procedure main()
{
    assert my_div(5,2) == 2;
    assert 5 div 2 == 2;
}

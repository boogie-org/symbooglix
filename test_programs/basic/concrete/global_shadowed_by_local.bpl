// RUN: %symbooglix %s /useCallSequencePrinter 2>&1 | %OutputCheck %s
var g:bv8;

procedure main()
modifies g;
{
    var x:bv8;
    g := 12bv8;
    // CHECK: Calling: ov()
    call x := ov();
    // CHECK: Leaving: ov()

    // FIXME: Boogie cannot verify this assertion
    // CHECK-NEXT: Assert : 12bv8 != 99bv8
    assert g != x; // Should be 12bv8 != 99bv8 which is trivially true
}

// For Boogie to verify this we need a specification or just inline it
// Eurgh.. Why do you do {:inline 1} for procedures but {:inline true} for functions?
// Have to inline due to Boogie doing modular verification. What would a good spec be?
procedure ov() returns (ret:bv8)
{
    var g:bv8; // Shadow global g. Language reference says this is allowed
    g := 99bv8;
    ret := g;
}

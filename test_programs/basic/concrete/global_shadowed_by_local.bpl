// RUN: %symbooglix %s --print-call-seq 2>&1 | %OutputCheck %s
var g:bv8;

procedure main()
modifies g;
{
    var x:bv8;
    g := 12bv8;
    // CHECK-L: Calling: ov()
    call x := ov();
    // CHECK-L: Leaving: ov()

    // FIXME: Boogie cannot verify this assertion
    // CHECK-NEXT-L: Mutating tree: '12bv8 != 99bv8' => 'true'
    // CHECK-NEXT-L: Assert : true
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

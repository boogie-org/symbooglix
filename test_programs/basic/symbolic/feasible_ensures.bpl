// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
var g:bv8;

function {:bvbuiltin "bvadd"} BVADD(bv8,bv8) returns (bv8);
function {:bvbuiltin "bvugt"} BVUGT(bv8,bv8) returns (bool);

procedure main(a:bv8) returns (b:bv8)
requires BVUGT(10bv8,a);
// CHECK-L: State 0: Terminated without error
ensures BVUGT(g,b);
modifies g;
{
    g := BVADD(a, 2bv8);
    b := BVADD(a, 1bv8);
}

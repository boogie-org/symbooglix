// RUN: %symbooglix %s 2>&1 | %OutputCheck %s
var g:bv8;

function {:bvbuiltin "bvadd"} BVADD(bv8,bv8) returns (bv8);
function {:bvbuiltin "bvugt"} BVUGT(bv8,bv8) returns (bool);

procedure main(a:bv8) returns (b:bv8)
requires BVUGT(10bv8,a);
// CHECK-L: State 0 terminated with an error
// CHECK-L: The following requires failed
// CHECK-L: ${CHECKFILE_NAME}:${LINE:+1}: BVUGT(g, b)
ensures BVUGT(g,b);
modifies g;
{
    g := a;
    b := BVADD(a, 1bv8);
}

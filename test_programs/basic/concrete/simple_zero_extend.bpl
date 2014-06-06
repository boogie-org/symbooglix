// RUN: %symbooglix %s 2>&1 | %OutputCheck %s
function {:bvbuiltin "zero_extend 8"} BV4_ZEXT8(bv4) : bv8;
function {:bvbuiltin "bvugt"} BV8_UGT(bv8, bv8) : bool;
procedure main(a:bv4) returns (r:bv8)
// CHECK-L: Concretising  a := 15bv4
requires a == 15bv4;
{
    // CHECK-L: Mutating tree: 'BV4_ZEXT8(15bv4)' => '15bv8'
    r := BV4_ZEXT8(a);
    // CHECK-L: Mutating tree: 'BV8_UGT(15bv8, 14bv8)' => 'true'
    assert BV8_UGT(r, 14bv8);
}

// RUN: %symbooglix %s 2>&1 | %OutputCheck %s
function {:bvbuiltin "sign_extend 4"} BV4_SEXT8(bv4) : bv8;
function {:bvbuiltin "bvugt"} BV8_UGT(bv8, bv8) : bool;
procedure main(a:bv4) returns (r:bv8)
// CHECK-L: Concretising  a := 15bv4
requires a == 15bv4;
{
    // CHECK-L: Mutating tree: 'BV4_SEXT8(15bv4)' => '255bv8'
    r := BV4_SEXT8(a);
    // CHECK-L: Mutating tree: '255bv8 == 255bv8' => 'true'
    assert r == 255bv8;
}

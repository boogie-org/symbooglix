// RUN: %symbooglix %s 2>&1 | %OutputCheck %s
procedure main()
{
    // CHECK-L: Creating Symbolic symbolic_0:[bv8][bv16]bv32
    var m:[bv8][bv16]bv32;
    // CHECK-L: Assume : (forall x: bv8, y: bv16 :: symbolic_0[x][y] == 0bv32)
    assume (forall x:bv8, y:bv16 :: m[x][y] == 0bv32);
    // CHECK-L: Assert : (forall a: bv8, b: bv16 :: symbolic_0[a][b] == 0bv32)
    assert (forall a:bv8, b:bv16 :: m[a][b] == 0bv32);
}

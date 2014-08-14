// RUN: %symbooglix %s 2>&1 | %OutputCheck %s
var g:bv8;

procedure main()
// CHECK-L: Concretising  g := 0bv8
requires g == 0bv8;
modifies g;
// CHECK-L: Mutating tree: '2bv8 == 2bv8' => 'true'
// CHECK-L: State 0: Terminated without error
ensures g == 2bv8;
{
    g := 2bv8;
}

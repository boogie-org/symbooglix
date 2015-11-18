// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --human-readable-smtlib=0 --log-queries=%t.smt2 --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAssume 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 0
// RUN: %OutputCheck --file-to-check=%t.smt2 %s

function f(x:int, y:int) returns (int);
// FIXME: This is fragile
// CHECK-L: (assert (forall (  (x Int) (y Int) ) (! (= (f x y  ) (+ x y ) ) :pattern ( (f x y  ) (f y x  ) ) ) ) )
axiom (forall x:int, y:int :: { f(x,y), f(y, x) } f(x, y) == x + y);

procedure main()
{
    var x:int;
    var y:int;
    assert x + y == f(x, y);
}

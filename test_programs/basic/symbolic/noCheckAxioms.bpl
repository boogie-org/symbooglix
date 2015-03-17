// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out --check-entry-axioms=0 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAxiom 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 0
// These declarations are taken from a SMACK generated boogie program
type float;
function $foeq(f1:float, f2:float) returns (bool);
function $fp2si(f:float) returns (int);
function $fp2ui(f:float) returns (int);
function $si2fp(i:int) returns (float);
function $ui2fp(i:int) returns (float);
axiom (forall f1, f2: float :: f1 != f2 || $foeq(f1,f2));
axiom (forall f: float :: $si2fp($fp2si(f)) == f);
axiom (forall f: float :: $ui2fp($fp2ui(f)) == f);
axiom (forall i: int :: $fp2si($si2fp(i)) == i);
axiom (forall i: int :: $fp2ui($ui2fp(i)) == i);

procedure main()
{
    var x:float;
    assert $si2fp($fp2si(x)) == x;
}

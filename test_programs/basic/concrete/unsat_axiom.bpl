// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s
axiom true;
axiom false;

procedure main()
{
    assert true;
}

// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 10 %symbooglix --output-dir %t.symbooglix-out --max-depth=1 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedExplicitBranchDepth 2
procedure main(bound: int);
  requires bound >= 0 && bound < 3;


implementation main(bound: int)
{
  var counter: int;

  entry:
    counter := 0;
    goto loopHead;

  loopHead:
    goto loopDone, loopBody;

  loopBody:
    assume {:partition} counter < bound;
    counter := counter + 1;
    goto loopHead;

  loopDone:
    assume {:partition} bound <= counter;
    goto exit;

  exit:
    assert counter == bound;
    return;
}

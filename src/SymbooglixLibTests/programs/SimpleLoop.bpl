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



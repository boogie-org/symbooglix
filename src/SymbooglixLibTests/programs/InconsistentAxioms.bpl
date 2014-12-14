const g:int;
axiom g > 0;
axiom g < 0;

procedure main(x:int)
requires g > 0; // Necessary, otherwise GDDE will remove g and the axioms
{
    assert true;
}

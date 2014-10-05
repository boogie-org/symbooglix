procedure main()
{
    entry:
        assume true;
        goto thing1, thing2;

    thing1:
        assume true;
        assume true;
        goto entry, thing1;

    thing2:
        assume true;
        assume true;
        return;
}

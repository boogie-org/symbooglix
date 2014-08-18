// RUN: %symbooglix --gpuverify-entry-points %s
procedure {:kernel} $foo()
{
    assert true;
}

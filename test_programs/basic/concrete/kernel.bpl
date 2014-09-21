// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --gpuverify-entry-points %s
procedure {:kernel} $foo()
{
    assert true;
}

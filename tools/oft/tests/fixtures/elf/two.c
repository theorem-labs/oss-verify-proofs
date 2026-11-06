/* The program of tools/oft/tests/test_symbols.py (README.md says how it is built): f has a loop, a branch and a
   call, g calls f, and h is an alias of g.  _start is written in assembly with a function type and no size, as
   musl's is, so the symbol table's functions are f, g, h and _start, of size 0.  seed and counter are its data
   objects, one with a value (in a section with file contents) and one zero (in .bss, with none); no code reads them,
   so `retain` keeps them through the link's --gc-sections.  The program is never run. */
__attribute__((used, retain)) int seed = 0x5eed;
__attribute__((used, retain)) int counter;

int g(int n);

__attribute__((noinline)) int f(int n)
{
    int s = 0;
    for (int i = 0; i < n; i++) {
        if (i & 1)
            s += g(i - 1);
        else
            s ^= i;
    }
    return s;
}

__attribute__((noinline)) int g(int n)
{
    return n > 0 ? f(n) + 1 : 0;
}

int h(int n) __attribute__((alias("g")));

__asm__(".globl _start\n"
        ".type _start, %function\n"
        "_start:\n"
        "\tli a0, 7\n"
        "\tcall g\n"
        "1:\tj 1b\n");

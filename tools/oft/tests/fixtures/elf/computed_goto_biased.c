/* GNU C label differences with reversible integer encoding of the entry address. */
static unsigned long volatile encoded;
static void *volatile saved;

__attribute__((noinline, noclone))
int computed_goto_biased(int dispatch, unsigned int which, const int *p)
{
start:
    if (dispatch) {
        static const long offsets[] = { &&start - &&start, &&target - &&start };
        encoded = (unsigned long)&&start + 8192UL;
        saved = (void *)(encoded - 8192UL + offsets[which]);
        goto *saved;
    }
    return 0;
target:
    return p[4];
}

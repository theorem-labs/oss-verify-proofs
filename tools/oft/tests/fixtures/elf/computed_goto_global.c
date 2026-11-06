/* GNU C relative labels with a volatile global target, so no stack frame is needed. */
static void *volatile saved;

__attribute__((noinline, noclone))
int computed_goto_global(int dispatch, unsigned int which, const int *p)
{
start:
    if (dispatch) {
        static const long offsets[] = { &&start - &&start, &&target - &&start };
        saved = (char *)&&start + offsets[which];
        goto *saved;
    }
    return 0;
target:
    return p[4];
}

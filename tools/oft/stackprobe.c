/* stackprobe CEILING: how deep this process's main stack goes before it faults.
 *
 * oft check compiles and runs it (check.py, measure_stack) after it sets its stack limit, so that the stack it prints is
 * the one the runtime gives, not the one the limit names: gVisor reports an unlimited limit and gives 8 MiB, and gives
 * about 128 MiB under a limit of 1 GiB or more.  It recurses with a 64 KiB frame, writes each frame's pages from the
 * top down, and stores the depth reached (the entry frame's address less this frame's) before each call.  A SIGSEGV,
 * handled on an alternate stack, prints "stackprobe: fault at <depth>"; reaching CEILING bytes prints
 * "stackprobe: no fault below <ceiling>".  Both exit 0.  It measures; it decides nothing. */
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define FRAME (64 * 1024)
#define PAGE 4096

static char *entry;
static unsigned long ceiling;
static volatile unsigned long reached;
static char altstack[64 * 1024];

static void say(const char *what, unsigned long n) {
    /* write(2) and a hand-made decimal: the handler may call nothing that is not async-signal-safe */
    char buf[96], digits[24];
    size_t len = strlen(what), k = 0;
    memcpy(buf, what, len);
    do {
        digits[k++] = (char)('0' + n % 10);
        n /= 10;
    } while (n);
    while (k)
        buf[len++] = digits[--k];
    buf[len++] = '\n';
    (void)!write(1, buf, len);
}

static void on_fault(int sig) {
    (void)sig;
    say("stackprobe: fault at ", reached);
    _exit(0);
}

static void dive(void) {
    volatile char frame[FRAME];
    for (long i = FRAME - 1; i >= 0; i -= PAGE)
        frame[i] = 1;
    frame[0] = 1;
    reached = (unsigned long)(entry - (char *)frame);
    if (reached >= ceiling) {
        say("stackprobe: no fault below ", ceiling);
        _exit(0);
    }
    dive();
    frame[1] = frame[0]; /* work after the call: no tail call */
}

int main(int argc, char **argv) {
    char here;
    stack_t ss;
    struct sigaction sa;
    if (argc != 2)
        return 2;
    ceiling = strtoul(argv[1], NULL, 10);
    entry = &here;
    ss.ss_sp = altstack;
    ss.ss_size = sizeof altstack;
    ss.ss_flags = 0;
    if (sigaltstack(&ss, NULL) != 0)
        return 3;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_fault;
    sa.sa_flags = SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGSEGV, &sa, NULL) != 0 || sigaction(SIGBUS, &sa, NULL) != 0)
        return 4;
    dive();
    return 0;
}

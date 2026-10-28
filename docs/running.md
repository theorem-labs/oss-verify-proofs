# Running the binaries

Each binary is a static riscv64 (RV64G) Linux program linked against musl. Run it
under qemu-user 10.0.11, which the runner image pins and CI uses. Earlier qemu
releases fail on the AddressSanitizer builds.

    ./oft fetch zlib                                  # into projects/zlib/bin/, every file SHA-256 checked
    qemu-riscv64 projects/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain input.bin

## The input file

Every build is run as `<file> <input-file>`. A small driver linked into every
build reads the input file whole and splits it as

    [u16 config word][config bytes][u32 allocation mask][payload]

with both integers little-endian. The low 15 bits of the config word are the
config length. The driver calls the fuzz target (`LLVMFuzzerTestOneInput`) on the
payload `(config[0] & 3) + 1` times, once when there is no config, and prints
each return value. A Go fuzz target's driver, written in Go, reads the same
format and calls the Go fuzz function instead (a `testing.F` test's `f.Fuzz`
function, which returns nothing; a go-fuzz `Fuzz` function's return value is
printed and does not change the status). A fuzz testcase therefore needs the six bytes
`00 00 00 00 00 00` in front of it: no config, no allocation mask.

The fuzz-target harness binaries ignore the allocation mask. The mask is for API
drivers that make chosen allocations fail, and no API driver is in this
release. Bit 15 of the config word turns on counting mode
([theories/Driver.v](../theories/Driver.v)). The fuzz-target harness binaries
count no allocations, so in counting mode they exit with status 0.

[theories/Driver.v](../theories/Driver.v) writes this format down in Rocq.

## Exit statuses

| status | meaning |
|---:|---|
| 0 | every harness call returned 0 or -1 |
| 2 | the driver refused the input without calling the harness: a wrong argument count, a missing or unreadable input file, a file shorter than its header or of 64 MiB or more, or no memory before the first call; in a Rust fuzz target, also a failed allocation at any point, which the port's allocation-error hook ends with one line on standard error; in a Python fuzz target, also an uncaught `MemoryError` at any point, which the port's interpreter host ends with one line on standard error |
| 77 | the harness called `exit()` during a call of the harness, and no handler that linked code registered after the driver's exit guard ended the process first (below); in a Python fuzz target, an uncaught `SystemExit` in a call of the harness |
| 78 | a harness call returned a value other than 0 or -1; a halts statement with `exits: any` allows it, and a halts statement with a finite exit set allows it only where the harness lists the places where its fuzz target turns an input away (`rejects`) ([statements.md](statements.md#halting-build_halts-build_halts_may_fail)) |
| 79 | a Rust fuzz target panicked: a failed `assert!`, an `unwrap` of an error, an overflow check or a failed rustc UB check. The port's panic hook writes the panic's source location on standard error and exits, where a libFuzzer build would `abort()`. Or a Python fuzz target raised an exception that nothing caught, a failed check of the harness included: the port's interpreter host writes its type and source line on standard error and exits, where atheris would report a crash |
| 80 | a Python fuzz target's interpreter, or the harness module it runs before the first call, failed to start (status 2 when the failure is an uncaught `MemoryError`) |
| 134 | `abort()`: a failed `assert()`, an AddressSanitizer report, or an uncaught C++ exception |
| 132 | `SIGILL`: a failed UndefinedBehaviorSanitizer check, which traps in these builds |
| 139 | `SIGSEGV`: a crash |

AddressSanitizer reports are not printed: a detection aborts with status 134
and no text.

A Go fuzz target reads these statuses differently, by the port's patched Go
runtime ([building.md](building.md#go-fuzz-targets)): 0 when every call
returned, whatever it returned (it never exits with 78); 2 also when the
system refused the runtime memory at any point (for its heap, a stack or its
own data); 77 for `os.Exit` during a call of the fuzz target; 79 for a panic
on the goroutine the driver calls it on (a runtime error included) or
`t.Fatal`, `t.Error` or `t.Fail` in a fuzz test, where OSS-Fuzz's build would
crash; 80 for any other fatal runtime error that is not out of memory (a panic
on another goroutine, a deadlock, a stack overflow); and 139 also for a load
through a nil pointer, since the runtime installs no signal handler. It has no
C library: Go 1.27.1 builds all of its code.

### What status 77 needs

A handler the driver registers with `atexit()` gives status 77. The driver
registers it once, before it calls `LLVMFuzzerInitialize`, and the handler ends
the process with 77 only while a call of the harness runs (`oft_exit_guard` and
`target_run` in the driver's `ossfuzz_adapter.h`: `src/` of the release recipe,
or `infra/base-builder/driver/` of an OSS Verify port). So:

- an `exit()` in `LLVMFuzzerInitialize` is not 77: unless a handler ends the
  process first, it ends with the low 8 bits of the argument the source passed;
- exit handlers run last-registered-first, so a handler that the harness or the
  library registers later, in `LLVMFuzzerInitialize` or during a call, runs
  before the guard. If that handler ends the process itself (`_exit`, `_Exit`,
  `quick_exit`, `abort`, a jump out of it, or the `exit_group` system call),
  the guard is never reached and the status is that handler's, which may be 0.

The driver intercepts `exit()` only. `_exit`, `_Exit` and `quick_exit` run no
`atexit` handler, so a harness that calls one of them ends the process with the
status it passed.

A check records where its `exit()` runs in `exit_reaches_guard`, and the
harness records whether its code installs a handler that takes over a failed
check in `failure_handlers` ([facts.md](facts.md), "A check" and "Failure
handlers"). A halts statement proves a check only when both show that the
failure ends with the status the statement excludes.

## AddressSanitizer builds need address space

At start-up the AddressSanitizer runtime reserves about 14 TiB of address space
for its shadow memory and 128 GiB for its allocator. If a reservation is
refused, for example under a shell limit set with `ulimit -v`, the runtime
spins forever and uses CPU, rather than exit. So a run that seems to hang may be
a starved start-up. Run the ASan builds with no address-space limit, and with a
timeout. LPS defines which resource limits a valid input may set
([semantics.md](semantics.md)).

## What differs from a libFuzzer build

- The target is riscv64, statically linked against musl. The recipe compiles
  with `-Os`; a library's own build system may add flags, for example `-O3
  -DNDEBUG` in a CMake `Release` build ([building.md](building.md#compiler-and-flags)).
  The Rust code of a Rust fuzz target is compiled with its cargo release
  profile ([building.md](building.md#rust-fuzz-targets)). The Python code of a
  Python fuzz target is CPython bytecode frozen into the binary, run by a static
  CPython ([building.md](building.md#python-fuzz-targets)).
- The sanitizer runtimes are configured differently ([building.md](building.md)):
  UndefinedBehaviorSanitizer runs in trap mode with clang's `undefined` checks
  except `function` and `vptr`; AddressSanitizer is a sealed static runtime that ignores
  `ASAN_OPTIONS`, returns NULL from `malloc` when memory is refused
  (`allocator_may_return_null=1`), aborts silently on a detection, and has leak
  detection off. A leak is a finding in OSS-Fuzz and not an error here.
- A small driver, not libFuzzer, reads the input file and calls the fuzz target.
- Where a library would read the environment, the process id or a random file
  name, its builds replace `getenv()` (it returns NULL), `getpid()` (it returns 1)
  or `mkstemp()` (it uses a fixed name), so that the program depends only on its
  input file.

Each harness page says which of these its builds use, and lists anything else
that differs from a libFuzzer build of its fuzz target.

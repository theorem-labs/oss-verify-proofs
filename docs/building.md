# How the binaries are built

This page describes the binaries of this release: the ones that the statements
under `projects/` and the proofs under `proofs/` are about.

## Where a binary comes from

Each proof has a build record:
`proofs/<project>/<harness>/provenance/PROVENANCE.md`, written from
`PROVENANCE.yaml` beside it. It gives:

- the upstream repository and commit of the library;
- the OSS-Fuzz project directory and its commit;
- the entry point (the function that the driver calls, normally
  `LLVMFuzzerTestOneInput`) and the harness source file, with its origin and
  licence;
- the recipe (the recipe archive that the binaries were built with, with its
  SHA-256, and the target in it), and a copy of the files that this build uses,
  in `recipe/`; for a port-built project (`build.oss_verify` in its
  `project.yaml`), in place of the recipe, the OSS Verify port's build manifest
  (`port/manifest.yaml`) and its files for the project
  (`port/projects/<project>/`);
- where the proofs of this fuzz target came from (`proofs.origin` in
  `PROVENANCE.yaml`); when they came from a package, `proofs.written_here`
  names the statements whose proofs were written in this repository, so the
  record credits the package with no proof that it does not have;
- the build system, the compiler, the builder image digest and the static
  AddressSanitizer commit;
- the file name, size and SHA-256 of each of the four builds;
- the licence of every component linked into the binaries, with the licence
  texts in `LICENSES/`;
- the result of an independent rebuild;
- the compiler and linker flags, as the recipe writes them, with the file and
  line of each.

For the statements without a proof, the harness page
(`projects/<project>/<harness>/README.md`) and the project page give the
library commit, the build system, the builder image and the SHA-256 of each
build. [reproducing.md](reproducing.md) tells you how to rebuild a binary.

Every build is run as `<file> <input-file>` ([running.md](running.md)).

## Compiler and flags

Every binary is a static riscv64 Linux program, compiled for RV64G
(`-march=rv64g -mabi=lp64d`) by clang 20.1.8 against musl, and linked with lld.
The four builds of a harness differ only in the sanitizer flags below. The
recipe gives these compile flags to all four builds:

    -march=rv64g -mabi=lp64d -Os -g -ffunction-sections -fdata-sections
    -fno-stack-protector -fno-plt -Wdate-time
    -fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-reallocarray
    -fno-builtin-free -fno-builtin-aligned_alloc -fno-builtin-posix_memalign
    -fno-builtin-memalign -fno-builtin-valloc -fno-builtin-strdup -fno-builtin-strndup

The `-fno-builtin-*` flags keep the allocation functions ordinary calls in every
build, so that the optimiser cannot remove or merge an allocation in one build
and keep it in another.

Two more sets of flags are added:

- **The library's own build system** adds its flags after these. For example,
  a CMake `Release` build adds `-O3 -DNDEBUG`, so that library is optimised at
  `-O3` and its own `assert()` checks are compiled out. coturn, libpcap and
  boost-json build their libraries with CMake. The recipe compiles the fuzz
  target itself, with its own flags (`oft_build_harness`).
- **Release builds** (`OFT_RELEASE=1`, which the recipe's `tools/build-env.tsv`
  sets) add `-DOFT_RELEASE_BUILD=1`, and pairs of `-fmacro-prefix-map` and
  `-fdebug-prefix-map` flags that map each build directory to a fixed path
  under `/src/`. So `__FILE__` has the same spelling in all four builds, and a
  program that prints its own file names writes the same bytes in each. They
  also replace any `-march=rv*` flag that a library's build adds with
  `-march=rv64g`. The recipe's `tools/build-body.sh` writes these flags
  (lines 265-351).

Each proof's build record quotes the flags as the recipe writes them, with the
file and line of each, and the pin of its library.

## Which code is instrumented

The sanitizer flags are on the compile lines of the library and of the fuzz
target. The driver linked into every build (it reads the input file and calls
the fuzz target; [running.md](running.md)) is compiled the same way in all four
builds, without sanitizer flags. In the AddressSanitizer builds the driver still
allocates through the AddressSanitizer allocator, like everything else in the
process.

## The builds

| build | flags | a detected error |
|---|---|---|
| `plain` | none | - |
| `ubsan` | `-fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function` | an illegal instruction (SIGILL, status 132); there is no UBSan runtime and nothing is printed |
| `asan` | `-fsanitize=address`, and the statically linked AddressSanitizer runtime described below | `abort()` (SIGABRT, status 134); nothing is printed |
| `asan-ubsan` | both of the above | either |

### UndefinedBehaviorSanitizer checks

With the flags above, clang 20.1.8 enables exactly these checks, all in trap
mode (measured from the compiler's own expansion of the flags, for C and for
C++):

    alignment, array-bounds, bool, builtin, enum, float-cast-overflow,
    integer-divide-by-zero, nonnull-attribute, null, object-size,
    pointer-overflow, return, returns-nonnull-attribute, shift-base,
    shift-exponent, signed-integer-overflow, unreachable, vla-bound

Not included: `function` (switched off: unlike the others it needs type
metadata rather than an inline test), `vptr` (it needs a runtime, which trap
mode does not have), and the checks clang leaves out of `undefined` by default:
`unsigned-integer-overflow`, `implicit-conversion`, `local-bounds`,
`float-divide-by-zero` and the `nullability` checks. OSS-Fuzz's own UBSan list
differs: it includes `function`, `unsigned-integer-overflow` and `vptr`, and
leaves out `alignment`, `float-cast-overflow`, `nonnull-attribute` and
`pointer-overflow`.

### The AddressSanitizer runtime

The ASan builds link a modified, sealed AddressSanitizer runtime (compiler-rt
20) so that a run depends only on the program and its input:

- **It does not read `ASAN_OPTIONS`** or any other environment variable. Its
  options are fixed at build time.
- **`allocator_may_return_null=1`**, set by the driver: when the environment
  refuses memory to the allocator, `malloc` returns NULL, as it does in the plain
  build, instead of the runtime ending the process. `operator new` then behaves
  as libc++'s does on a refusal (it throws `std::bad_alloc`).
- **A detection aborts silently**: `abort_on_error` is on and reports are not
  printed, so a detected error ends the process by SIGABRT (status 134) with no
  output.
- **Leak detection is off** (`detect_leaks=0`). LeakSanitizer's exit-time check
  cannot run in this sealed configuration, so a leak is not an error in these
  builds, unlike in OSS-Fuzz's.
- The runtime installs no signal handlers and does not return memory to the
  system on a timer.
- At start-up it reserves address space: about 14 TiB for its shadow memory
  and 128 GiB for its allocator. If a reservation is refused, the runtime spins
  forever and uses CPU, instead of exiting ([running.md](running.md)). That is
  why no ASan build has a `_halts_may_fail` statement.

The runtime also leaves core dumps to the process's limits (`disable_coredump=0`;
compiler-rt's default on 64-bit is 1). Every other runtime option has its
compiler-rt 20 default.

The runtime and the C library of every ASan binary of this release were built
from the source that [static-asan](https://github.com/theorem-labs/static-asan)
publishes at commit
[`b05061352064`](https://github.com/theorem-labs/static-asan/commit/b05061352064fa2be1813ac5429149f3de5f057d).
Upstream LLVM cannot link ASan into a fully static musl binary. static-asan
has two parts: a patch series against musl and LLVM's compiler-rt that makes
this link work, and a Dockerfile that builds the toolchain. The Dockerfile
builds musl and the LLVM runtimes (compiler-rt, libunwind, libc++ and libc++abi)
from pinned sources (musl at a pinned commit, llvm-project `llvmorg-20.1.8`).
The compiler itself (clang, lld and llvm 20.1.8) comes from Alpine packages,
pinned by version series. A build of commit `b05061352064` gives the same musl
`libc.a` and compiler-rt builtins, byte for byte, as the toolchain that built
these binaries. Its ASan runtime archives differ only in their DWARF line
tables, and the link removes those (`--strip-all`). static-asan's README lists
each patch and the pinned versions, and shows this comparison. The release's
`toolchain-src.tar.zst` holds the same source.

### Code the sanitizers do not instrument

As in OSS-Fuzz's sanitizer builds, every build also links code that no
sanitizer instruments: ASan checks no load or store made inside it, and UBSan
inserts no check there. It is of three kinds:

- **The toolchain's runtimes**, in every build: the C library (musl) and its
  start-up objects, compiler-rt, the sanitizer runtime itself, the C++ runtime
  (libc++, libc++abi, libunwind) and, for Fortran code, the Fortran runtime.
- **Libraries from the build image** that a harness links as a dependency
  (for example zlib or OpenSSL from the image's sysroot), built once without
  instrumentation.
- **Hand-written assembly and Fortran** in a library: a compiler cannot add
  sanitizer checks to either. Such a member would be listed by name with its
  source file; no build of this release has one.

The `uninstrumented` list of each build in `harness.yaml`, shown in the
harness's README, says which of these its link took. A build without the list
has not recorded it in this release.

## Rust fuzz targets

The OSS Verify port builds a Rust fuzz target, a cargo-fuzz `[[bin]]`, in its
Rust toolchain image (`ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain-rust`,
pinned in the port's `infra/toolchains.tsv`; release.yaml lists it in
`images.builder` once a release holds a Rust build): the C and C++ toolchain
image with rustc 1.90.0-nightly (2025-07-15) added. The fuzz target and every
crate it uses, the Rust standard library included (`-Zbuild-std`), are compiled
into one static library with the project's cargo release profile and
`panic = "abort"`, and linked with the driver as a C fuzz target is. A crate's
C code is compiled by clang with the flags of the build. The Rust flags of each
build are:

| build | Rust flags | a detected error |
|---|---|---|
| `plain` | `-Zub-checks=no` | - |
| `ubsan` | `-Zub-checks=yes` | a failed rustc UB check exits with status 79, below; UBSan in the C code traps, as above |
| `asan` | `-Zub-checks=no -Zsanitizer=address` | `abort()` (SIGABRT, status 134); nothing is printed |
| `asan-ubsan` | `-Zub-checks=yes -Zsanitizer=address` | either |

rustc's UB checks are the standard library's checks of the preconditions of its
unsafe functions (for example that the pointer given to
`slice::from_raw_parts` is aligned and not null), not clang's `undefined`
group. A failed one panics without unwinding. `panic = "abort"` means a panic
never unwinds, in every build, and the port's adapter (its `oft-rust-rt` crate
and `plugin_rust.h`) installs two hooks before `main`. A panic, a failed UB
check included, writes its source location on standard error and exits with
status 79; an allocation failure writes its size on standard error and exits
with status 2. A libFuzzer build would `abort()` in both cases; the hooks keep
SIGABRT the signal of an AddressSanitizer report. A project can
also turn on `-Cdebug-assertions` in all four builds; its harness page says
so. The standard library is compiled with each build's flags, so
AddressSanitizer instruments it like the rest of the Rust code.

The standard library compiled is not the stock one: it is the toolchain image's
sealed copy (its `seal-std.sh`), with two edits that remove a dependence on
state the process model does not describe. std's `HashMap` keys come from
`getrandom` with `GRND_NONBLOCK` rather than `GRND_INSECURE`, and
`available_parallelism()` returns 1 without reading cgroup files or CPU
affinity. A third edit, to standard output, is compiled in only for a build
that asks for it; each harness page lists the edits its builds carry.

## Python fuzz targets

The OSS Verify port builds a Python fuzz target, an atheris harness, in its
Python toolchain image (`ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain-python`,
pinned in the port's `infra/toolchains.tsv`; release.yaml lists it in
`images.builder` once a release holds a Python build): the C and C++ toolchain
image with the CPython 3.11.13 source tarball and a native CPython 3.11.13 added.
Each build compiles CPython 3.11.13 from that tarball, with one patch (`import
signal` takes the signal dispositions of a new process without asking the
kernel for them), as a static library, with the build's compiler and flags:
the sanitizers instrument the interpreter, its built-in extension modules and
the port's interpreter host (`atheris_host.c`) as they instrument a C library.
The Python code is not compiled: the harness, the library's modules and every
standard-library module they import are marshalled CPython bytecode, frozen
into the binary, and an `atheris` stand-in keeps the harness's `TestOneInput`
for the host to call. Libraries that some built-in modules link (zlib, bzip2,
XZ, SQLite and others) come from the build image's sysroot, uninstrumented.

The interpreter runs isolated: its configuration reads no environment
variable (`os.environ` still holds the process's environment), it imports
nothing from the file system, hashes strings with seed 0 and allocates every
object with `malloc` (no pymalloc arenas), so AddressSanitizer sees each
object. The driver starts it after it reads the input file, before the first
call of the fuzz target. Python code does not access memory directly, so the
sanitizers look for errors only in the C code. The host ends a failure with an
exit status, never with `abort()`:

| what happens | status |
|---|---|
| an uncaught exception in a call of the harness, a failed property check included | 79 |
| an uncaught `MemoryError` | 2 |
| an uncaught `SystemExit` in a call of the harness | 77 |
| the interpreter or the harness module fails before the first call | 80 (2 when the failure is an uncaught `MemoryError`) |

Each writes one line on standard error, with the exception's type and the
source line where it was raised. atheris would report each of these as a crash.
A failed `assert` in Python code is an uncaught `AssertionError`: status 79.
CPython's own fatal errors still end with `abort()`: for example, it aborts when
some allocations it makes while it starts are refused. So a Python fuzz target
has no `_halts_may_fail` statement, and its agreement statements are read
alloc-forced-only ([statements.md](statements.md)).

## Go fuzz targets

The OSS Verify port builds a Go fuzz target, an OSS-Fuzz Go fuzz target as it
is, in its Go toolchain image (`ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain-go`,
pinned in the port's `infra/toolchains.tsv`; release.yaml lists it in
`images.builder` once a release holds a Go build): the C and C++ toolchain image
with Go 1.27.1 and OSS-Fuzz's Go helpers (`compile_go_fuzzer` for a go-fuzz
`Fuzz(data []byte) int` function, `compile_native_go_fuzzer` for a
`testing.F` fuzz test), changed to build a static riscv64 program. The program
is the fuzz target, the library, Go's standard library and runtime, and a
driver written in Go, all built by Go's own compiler, assembler and linker,
for RV64G, with no cgo: no clang, no musl and no C code. The project's
`project.yaml` names the Go version in `build.go` and has no `build.clang`. A
`go.lock` in the port's project directory pins every module; the build reads
them from those files, with no network. Go's `-asan` needs cgo, which the
port's build turns off (`CGO_ENABLED=0`), and `-msan` does not target riscv64,
so a Go fuzz target has the plain build only.

The build uses a patched Go runtime: an overlay of the standard library (`go
build -overlay`) and a rebuilt compiler; the Go toolchain's own files do not
change. The patches remove system calls and files the process model does not
have: signal handlers, the sysmon thread and the main goroutine's thread lock,
the CPU-affinity and cgroup reads, reads of the environment, the
transparent-huge-page read under `/sys` and the `MADV_NOHUGEPAGE` advice, the
checks of file descriptors 0-2, the open-file limit's read and raise, and the
riscv64 hardware probe (so no vector code); the driver also sets `//go:debug
containermaxprocs=0 updatemaxprocs=0 decoratemappings=0`. So the program runs on one CPU,
`os.Getenv` returns `""` for every variable, and `GOGC`, `GODEBUG`,
`GOMAXPROCS` and `GOMEMLIMIT` have no effect. The patches also give a failure
its own exit status, where OSS-Fuzz's build would crash:

| what happens | status |
|---|---|
| a panic on the fuzz target's goroutine, a runtime error included, or `t.Fatal`, `t.Error` or `t.Fail` in a fuzz test | 79 |
| `os.Exit` during a call of the fuzz target | 77 |
| any other fatal runtime error that is not out of memory: a panic on another goroutine, a deadlock, a stack overflow, a write to a map from two goroutines | 80 (the stock runtime exits with 2) |
| the system refused the runtime memory: an `mmap` for the heap, a stack or the runtime's own data failed | 2 |
| a load through a nil pointer | 139 (`SIGSEGV`): the runtime installs no signal handler, so this is not a recoverable panic, and code that recovers it as control flow (`fmt` does, for a nil `Stringer`) ends with 139 where stock Go goes on |

A request larger than the runtime's limit for one allocation (2^48 bytes), a
`make()` that is too large for one, panics without asking the system: status 79.
`t.Skip` in a fuzz test ends the call normally, as OSS-Fuzz's testing shim
makes it; a call on the `*testing.F` itself (`f.Fatal`, `f.Error`, `f.Fail`)
does nothing under that shim. A `testing.F` test's function gets arguments the
shim decodes from the payload (go-fuzz-headers), and is not called when the
payload is too short to decode them. A go-fuzz `Fuzz` function's return value does not change the exit status (so a
Go fuzz target never exits with 78); the driver writes it on standard output.
The patches do not remove everything the model lacks: a timer, which the
runtime's scavenger can start, starts the network poller (`epoll_create1`,
`epoll_ctl`, `epoll_pwait`), which the process model does not cover, so a run
that reaches it is blocked by the model.
So a Go fuzz target's statements are
halts statements about the plain build that allow exactly the statuses 0 and 2
(the Go driver gives no status 3), with no `_halts_may_fail` statement and no
agreement statements; a check that ends with `panic` or with `fail` (`t.Fatal`,
`t.Error`, `t.Fail`) exits with status 79 on the fuzz target's goroutine (80 on
another), which such a statement excludes
([facts.md](facts.md), [statements.md](statements.md)). The project page lists
the runtime patches.

In a Go project's facts ([facts.md](facts.md)), `project.yaml` names
`build.system: go`, the Go version in `build.go` and no `build.clang`; its
`build.builder` is the port's Go toolchain image and `build.oss_verify` is
required, since only the port builds Go fuzz targets. A Go harness's `entry` is
its Go fuzz function (`FuzzDecode`, say), not `LLVMFuzzerTestOneInput`, and its
`builds` hold `plain` only. In a Go harness's
checks, `os.Exit` is `stops_with: exit`, which the patched runtime ends with
status 77 during a call of the fuzz target (`exit_reaches_guard: true`); a
deferred function that calls `recover()` while a panic unwinds and then
returns, or ends the process, without panicking again is a failure handler
that takes over `panic` and `fail` (the driver's own recover is not one); and `oft lint`
refuses the stops `abort`, `assert`, `trap`, `throw` and `raise`.

## What this means for a statement

"Trips its sanitizer" in a statement means one of the checks above fails, in
the code they instrument. An error the configuration does not check (an
unsigned overflow, a leak, a use of uninitialised memory) does not falsify a
statement by itself.

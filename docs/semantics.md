# LPS: the Linux process semantics

Every statement and every proof in this repository is about LPS,
[rocq-linux-process-semantics](https://github.com/theorem-labs/rocq-linux-process-semantics).
LPS is a formal model, written in Rocq, of a Linux process that runs a static
64-bit RISC-V binary. It gives the semantics of the RISC-V instructions and of
the system calls that these programs make. A statement here applies LPS's
definitions to the memory images of specific binaries.

## Status: best effort, not complete

LPS is work in progress. It describes part of Linux, not all of it. It makes
some assumptions that it does not check. A proof is only as good as LPS.

LPS's own [SCOPE.md](https://github.com/theorem-labs/rocq-linux-process-semantics/blob/c0dd863a0f8f307beca7f2ee5cb4d7686a875779/SCOPE.md)
says which system LPS describes. It lists where LPS is narrower than that
system, and the assumptions that LPS does not check. It lists the known cases
where LPS allows a behaviour that Linux does not give. It also says what
the proofs inside LPS do not check. Read it before you use a proof as evidence
about a real program.

LPS changes from version to version. A proof about one LPS version says
nothing about another version. [release.yaml](../release.yaml) names the one
LPS commit that every statement and proof of this release uses
(`semantics.commit`).

## Design principles

These are LPS's own design priorities, from its
[README](https://github.com/theorem-labs/rocq-linux-process-semantics/blob/c0dd863a0f8f307beca7f2ee5cb4d7686a875779/README.md#design-priorities).

LPS describes one system: stable Linux v6.18.46 on riscv64, with the RISC-V
specification (RV64GC) for instructions. Bugs in Linux do not count. QEMU user
mode is not a supported system. Where Linux and QEMU user mode give different
answers, LPS gives the Linux answer. So a proof in LPS does not cover a QEMU
run that depends on such a difference. SCOPE.md lists each known difference
("Where QEMU user mode differs").

**Known divergence.** On a shrinking `mremap` with `MREMAP_MAYMOVE`, QEMU user
mode can move the mapping to a new address. Linux keeps a shrink in place. LPS
allows only a shrink in place or an error. So LPS does not describe this QEMU
behaviour. We saw it in one recorded run. A statement proved in LPS is
therefore not shown for a QEMU run that takes this path.

LPS has three priorities, in this order:

1. **Sound (required).** A statement that you prove in LPS is true of Linux
   v6.18.46, under the assumptions in SCOPE.md. Where LPS cannot be sound, it
   says `unmodeled`. The cases where it does neither are open bugs. SCOPE.md
   lists them ("Soundness gaps").
2. **Precise (goal).** LPS includes no behaviour that Linux v6.18.46 does not
   give.
3. **Covered (goal).** LPS has no `unmodeled` case.

Priority 2 matters for the statements here. They compare the sets of
behaviours of two builds. If LPS includes a behaviour that Linux does not
give, a comparison can be true in LPS and false on Linux. SCOPE.md lists the
known cases.

Three consequences of these priorities show in every statement:

- **LPS allows every answer that Linux can give**, except in the soundness
  gaps that SCOPE.md lists. For example, `read` may return any nonempty prefix
  of the available bytes. A proof must cover each answer. An `mmap` that LPS
  places itself, with neither `MAP_FIXED` nor `MAP_FIXED_NOREPLACE`, gets one
  address only: the address that Linux gives in that state. A free hint that
  ends above `State.alloc_top` less the stack guard gap is the exception.
  There LPS cannot tell which address Linux gives, so the call is
  `unmodeled`.
- **A step that LPS does not interpret is an error.** An instruction or a
  system call outside LPS has no rule (`unmodeled`). Every agreement and halts
  statement forbids it, so none of them is proved about a run that reaches such
  a step. A bound or decidability statement counts such an input as one on
  which the builds disagree.
- **The environment may refuse calls.** By default, LPS lets the environment
  make some system calls fail even when the process's state does not force the
  failure (for example, `mmap` may return `ENOMEM`). Each statement says which
  failures it allows ([statements.md](statements.md)).

## The LPS version of this release

Every statement and every proof in this release uses one LPS version:
commit [`c0dd863a`](https://github.com/theorem-labs/rocq-linux-process-semantics/commit/c0dd863a0f8f307beca7f2ee5cb4d7686a875779)
of rocq-linux-process-semantics, opam package
`rocq-linux-process-semantics-core`. [release.yaml](../release.yaml) names it
(`semantics.commit`), and the checker image is built from it
([checking.md](checking.md#rocq)).

## Vocabulary

These terms are from LPS. [theories/Shapes.v](../theories/Shapes.v) lists them
at the top, with the LPS names.

- **Image** (`MemImageType.Image`): what the Linux loader maps from a static
  riscv64 ELF file. This is its loadable segments, its entry point and the
  location of its program headers. Each harness's `Images.v` names one image
  per build. The images are made from the ELF files at build time and are not
  stored.
- **Entry** (`Run.ExecEntry`): what the kernel chooses at `execve` and the
  program does not control. This is the stack address, the end of the stack
  mapping, the initial program break, the mmap base, the `AT_RANDOM` bytes,
  and what a call to the vDSO leaves in the registers and on the stack.
  Statements quantify over every valid entry, independently for each build.
- **Input** (`State.ProcInput`): everything the environment supplies. This is
  the arguments, the environment variables, the starting file system (so the
  input file, its contents or its absence) and a private `/tmp`, standard
  input, the user and group IDs, the network peers, the open-file limit, the
  blocked-signal mask, the bytes that `/dev/urandom` returns, the machine
  capabilities that the auxiliary vector advertises, the address-space size,
  the kernel build that the process runs on (`in_kernel`), and the exec file
  name (`in_execfn`). One field says whether file descriptors 1 and 2 still
  have a reader (`in_channel_reader`). One field says whether SIGPIPE is at
  its default action when the program starts (`in_sigpipe_default`). Two more
  fields say whether `abort()` is read as death by SIGABRT
  (`in_abort_terminal`), and whether LPS follows a SIGPIPE at its default
  action into the death that it causes (`in_sigpipe_terminal`).
  `Run.valid_input` says which inputs are valid.
- **Run**: what a process can do on one input, with a given memory budget. A
  run is a set of finite event traces, and a fact about whether some execution
  reaches an error. The events are bytes read and written on the standard
  streams and on connections, in order; a normal exit, with its status and the
  final contents of the files; and death by a fatal signal that LPS models. A
  write to a regular file is not an event. It is seen only in the final file
  contents.
- **Error**: a step that LPS does not interpret, or a fault that it treats as
  an error. This is an unmodeled system call or instruction, an invalid memory
  access, an illegal instruction (a failed UBSan check in these builds), or
  `abort()` (a failed `assert()`, an AddressSanitizer report, or an uncaught
  C++ exception). Some statements read `abort()` as death by SIGABRT instead.
  That is not an error in LPS, but those statements forbid it too.
- **Environment failures** (`Run.SpuriousCfg`): which system calls may fail when
  the process's state does not force the failure. LPS lets six kinds of call
  fail in this way: memory (`mmap`, `munmap`, `brk`, `mremap`, `mprotect`),
  file system calls such as `openat`, calls that create descriptors, network
  set-up, credentials, and `getrandom` and `nanosleep`. A `read` never fails
  without cause. A `write` fails without cause in one case only: a `write` to
  an empty pipe may return `ENOMEM`. LPS counts this failure as a file system
  failure. The statements use three settings: every one of these
  kinds may fail; the same, except that a memory request fails only when the
  budget is spent or no address range is free; and only what the process's
  state forces.

## How LPS counts memory

LPS charges memory as its `Mmap` rules say. A reservation made with
`PROT_NONE` is not charged to the budget. A `MAP_NORESERVE` mapping is charged
page by page, on first access. So the large start-up reservation of the
AddressSanitizer runtime does not count against a halts statement's 16 GiB.

## Where LPS is narrower than Linux

SCOPE.md has the full list. These limits matter most for the programs here:

- One thread. LPS has no scheduler. For a `fork`-like call, LPS describes the
  parent only.
- No signal handlers run.
- The stack limit is 8 MiB.
- An argument after the program name may not contain `/` and may not be `..`.
  So the input file is named relative to the working directory.
- The file system has no full directory tree, no symbolic links, no
  permissions, and no device files except `/dev/null` and `/dev/urandom`.
- The plain build may allocate 16 GiB and the sanitizer build 512 GiB, unless a
  statement sets a smaller budget.

A binary that makes a call LPS does not cover leaves LPS. Every agreement and
halts statement forbids that. A harness whose binaries were seen to leave LPS on
sample inputs has every statement marked "blocked by the model", with the
feature named in words (for example "opens files other than its input"). The
programs are not at fault. Sample inputs cannot reach every path, so this mark
is a lower bound ([status.md](status.md)).

The harness pages, the project pages and `Statements.v` call LPS "the model".

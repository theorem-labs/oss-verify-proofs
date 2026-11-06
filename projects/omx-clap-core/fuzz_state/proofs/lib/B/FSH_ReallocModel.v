(* fs.asan-ubsan (image B) entry of the ASan realloc model (a Theorem Labs lane, owner a Theorem Labs lane). STATEMENTS ONLY: definitions,
   no proofs.

   SPLIT 2026-10-29 (a Theorem Labs lane), for the closure rule (no lib/A file may Require a lib/B file, and no lib/B file may
   Require a lib/A file that holds a per-image address Definition or use an image-A term): FS_AREALLOC_PC_B,
   FS_AREALLOC_IPC_B and FS_AREALLOC_B moved verbatim from lib/A/FSH_ReallocModel.v, under the same names. This file
   Requires only the image-free model, lib/A/FSH_ReallocModelG.v (`Require Export`, as lib/A/FSH_ReallocModel.v does).
   lib/B/FSupoisonRealloc.v (FS_AREALLOC_BU) takes FS_AREALLOC_PC_B / FS_AREALLOC_IPC_B from here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YM05 YA0n YG00 YG01 YG0l YG0d YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Export FSH_ReallocModelG.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* ---- fs's realloc entry and trace site (MEASURED on the ORIGINAL images; sources below) ----
   A: __wrap_realloc 0x53078 (1-jal thunk) -> __interceptor_realloc 0x53474; trace ipc 0x535b0.
   B: __wrap_realloc 0x530e8; trace ipc 0x53620.
   Entry addresses: .symtab of the unstripped twins (a Theorem Labs lane FsBinMatch.data/fs-functions.<build>.tsv).
   TRACE IPC, CORRECTED 2026-10-28T21:3xZ (a Theorem Labs lane's retraction, verified here by disassembly of the original
   fs.asan, sha256 64b53ff86172...): __interceptor_realloc reads malloc_context_size and branches on it -
     +0xfc  jal GetMallocContextSize ; +0x100 addi a1, zero, 2 ; +0x104 bltu a1, a0, +0x34
   - so with mcs > 2 it skips to +0x138 `jal StackTrace::GetCurrentPc`, whose return pc +0x13c is what the
   stack trace records: A 0x535b0, B 0x53620 (B's body is identical modulo addresses, so the same +0x13c).
   The values this file USED to carry, 0x53594 (A) / 0x53604 (B), are +0x120, the return of the FIRST
   GetCurrentPc call on the mcs <= 2 branch, which only a toolchain-N image (mcs = 1) takes; fs's originals have
   mcs = 30. A contract stated over the old values would demand a trace the original binary never records. The
   donor uses the same second-call convention (cgif A malloc 0x52bcc / free 0x52a6c).
   The four realloc bodies are identical modulo address operands to cgif_rgb's in BOTH builds ((internal path)
   section 1 and section 6(a)), which is why cgif_rgb's set relocates. *)
Definition FS_AREALLOC_PC_B : Z := 0x530e8.
Definition FS_AREALLOC_IPC_B : Z := 0x53620.

(* The NAMED HYPOTHESIS the lane table requires (owner a Theorem Labs lane), stated so that it is never absent:
   every walk that calls fuzz_realloc takes it.
   DISCHARGE (corrected 2026-10-28T20:43Z, a Theorem Labs lane's premise check and a Theorem Labs lane): NOT cgif_rgb's released
   realloc set. That set proves arealloc_realizes only for 64513 <= n (YF78.v:553 and the YC5u / YC6* / YC70
   call sites), while fs reallocs at the pj_write growth sizes 4112 / 8208 / 16400 / 32784, every one of them
   BELOW 64513. The form here asks 1 <= n, which is strictly stronger than anything cgif_rgb proved, so this is
   an OPEN obligation owned by a Theorem Labs lane (arealloc_realizes_all, on
   a working branch). cgif_rgb supplies the model and the walk's shape, not a proof that closes it.
   U must also be instantiated with a universe that CONTAINS fs's realloc trace, [0x535b0] for A and [0x53620]
   for B (the corrected second-call pcs, see above); A/ACej.v still carries cgif_file's 190 traces until the RELOC
   lane re-points them.
   Precedent for the shape: cgif_rgb states it the same way at its own call sites, e.g.
   lib/YC5u.v:127 `Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640`. *)
Definition FS_AREALLOC_B {fx : YK11.FPState} {rc : YM05.RunCeil}
  (segs : list Segment) (B : asyms) (U : list (list Z)) : Prop :=
  arealloc_realizes_all segs B U FS_AREALLOC_PC_B FS_AREALLOC_IPC_B.

(* fs.asan-ubsan (image B) entry of the any-U (user-poison) ASan realloc contract (POISON-U lane, a Theorem Labs lane; asked by
   a Theorem Labs lane, 21:19Z).

   SPLIT 2026-10-29 (a Theorem Labs lane; ruled by a Theorem Labs lane, 08:41Z), for the closure rule (no lib/A file may
   Require a lib/B file, and no lib/B file may use an image-A term): FS_AREALLOC_BU moved from lib/A/FSupoisonRealloc.v,
   same name, same contract at image B's pcs. It is stated over the image-free contract lib/A/FSupoisonReallocG.v
   (`Require Export`, as lib/A/FSupoisonRealloc.v does) and image B's realloc pcs lib/B/FSH_ReallocModel.v. It Requires
   neither lib/A/FSupoisonRealloc.v nor lib/A/FSH_ReallocModel.v.
   STATEMENT only; no Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Export FSupoisonReallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_ReallocModel.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSRM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSH_ReallocModel.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* fs's image-B entry, as lib/B/FSH_ReallocModel states the plain one. *)
Definition FS_AREALLOC_BU (Un : list (list Z)) : Prop :=
  arealloc_realizesU segs B Un FSRM.FS_AREALLOC_PC_B FSRM.FS_AREALLOC_IPC_B.
End r.

(* fs.asan (image A) entry of the any-U (user-poison) ASan realloc contract (POISON-U lane, a Theorem Labs lane; asked by another Theorem Labs lane,
   21:19Z).

   SPLIT 2026-10-29 (a Theorem Labs lane; ruled by a Theorem Labs lane, 08:41Z), for the closure rule (no lib/A file may
   Require a lib/B file, and no lib/B file may use an image-A term): the image-free contract (astageU, arealloc_leafU,
   arealloc_realizesU) moved verbatim to lib/A/FSupoisonReallocG.v, which this file does `Require Export` of. Image B's
   entry FS_AREALLOC_BU moved to lib/B/FSupoisonRealloc.v. This file keeps image A's entry only.
   STATEMENT only; no Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Export FSupoisonReallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_ReallocModel.
Local Open Scope Z_scope.

Module FSRM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSH_ReallocModel.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* fs's image-A entry, as FSH_ReallocModel states the plain one. *)
Definition FS_AREALLOC_AU (Un : list (list Z)) : Prop :=
  arealloc_realizesU segs B Un FSRM.FS_AREALLOC_PC_A FSRM.FS_AREALLOC_IPC_A.
End r.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (keeps only the decoder facts Spec/PTotal.v uses (dec_mmap_err_errno, dec_mmap_none_err_errno, dec_mprotect_err_errno) and dec_mmap_fixed_err_errno, 4 of them with written proofs in place of recorded ones: the C-side simulation placed fresh mmaps at addresses the proof chose, which Linux's placement at this revision forbids, and nothing outside this file read that simulation; the same cut as zstd/zstd_frame_info's and zstd/simple_decompress's Spec/EKSim.v). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc KInv KStep PState KLink KEv JLedger Relim StepB EquivK_iface EKPlace.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Local Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS 727298f3: this file keeps only the decoder facts Spec/PTotal.v uses.  Its C-side simulation placed
   fresh mmaps at addresses the proof chose, which linux_place forbids, and nothing outside it referenced that
   simulation (the same cut as zstd/zstd_frame_info's and zstd/simple_decompress's Spec/EKSim.v). *)

Lemma dec_mmap_err_errno : forall atop len avoid rsp e,
  dec_mmap atop len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); congruence.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

Lemma dec_mmap_none_err_errno : forall atop len avoid rsp e,
  dec_mmap_none atop len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap_none in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|]].
  - destruct cs; [|discriminate]. destruct (errno_of r); congruence.
  - destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

Lemma dec_mmap_fixed_err_errno : forall addr len rsp x,
  dec_mmap_fixed addr len rsp = Some x -> match x with FxKept e | FxLost e => errno_of (eff_ret rsp) = Some e | FxDone => True end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mmap_fixed in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|]].
  - destruct cs; [|discriminate]. destruct (errno_of r); [|discriminate]. injection H as <-. reflexivity.
  - destruct cs; [|discriminate]. destruct (_ && _); [|discriminate].
    destruct (errno_of r); [injection H as <-; reflexivity|]. destruct (bv_eqb r _); [|discriminate]. injection H as <-. exact I.
  - discriminate.
Qed.

Lemma dec_mprotect_err_errno : forall addr len rsp e,
  dec_mprotect addr len rsp = Some (RgErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros addr len [r ws zs us cs ci] e H. unfold dec_mprotect in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); [congruence|]. destruct (_ =? _); discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

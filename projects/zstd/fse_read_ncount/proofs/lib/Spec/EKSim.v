(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc KInv KStep PState KLink KEv Relim StepB EquivK_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
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
Lemma dec_mprotect_err_errno : forall addr len rsp e,
dec_mprotect addr len rsp = Some (RgErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
intros addr len [r ws zs us cs ci] e H. unfold dec_mprotect in H. cbn [eff_ret].
destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); [congruence|]. destruct (_ =? _); discriminate.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
- discriminate.
Qed.
Section EvPaths.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Context (atop : Z).
End EvPaths.

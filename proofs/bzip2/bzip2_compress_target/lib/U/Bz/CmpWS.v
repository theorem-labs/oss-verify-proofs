(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec S3Spec U.S3FdStmt U.S3FdUnits.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Frame Arr Step.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocLayout3 AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import StdioIface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpSess CmpSess2 DecTac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record wsimg := WI {
  wi_bzalloc : Z;    (* [comment removed for export] *)
  wi_bzfree : Z      (* [comment removed for export] *)
}.
Definition S3W : wsimg := WI 0x13e24 0x13e3c.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bzw_run (fuel : nat) (e : est) (z : zstrm) : Prop :=
  match fuel with
  | O => False
  | S f => let '(ret, e', z') := bzCompress znew e (z_reset z) BZ_RUN in
           ret = BZ_RUN_OK /\ e_mode e' = BZ_M_RUNNING /\ (z_avail_in z' <> 0 -> bzw_run f e' z')
  end.
(* [comment removed for export] *)
Fixpoint bzc_run (fuel : nat) (e : est) (z : zstrm) : Prop :=
  match fuel with
  | O => False
  | S f => let '(ret, e', z') := bzCompress znew e (z_reset z) BZ_FINISH in
           z_avail_in z' = 0 /\ (ret = BZ_STREAM_END \/ (ret = BZ_FINISH_OK /\ bzc_run f e' z'))
  end.

Definition ws_fuel (len : Z) : nat := Z.to_nat (len / 1000 + 16).
Definition z_init (pl : list Z) : zstrm := ZS pl (Z.of_nat (length pl)) [] 0 0 0 0 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ws_laws (HCX : cctx -> eg -> est -> zstrm -> Prop) : Prop := WL {
  (* [comment removed for export] *)
  wl_init : forall cx pl, cctx_ok cx -> cctx_sep cx -> Z.of_nat (length pl) < 2 ^ 26 -> Forall (fun c => 0 <= c < 256) pl ->
            HCX cx (eg_init (Z_to_bv 64 0)) est0 (z_reset (z_init pl));
  (* [comment removed for export] *)
  wl_write : forall pl, pl <> [] -> Z.of_nat (length pl) < 2 ^ 26 -> Forall (fun c => 0 <= c < 256) pl ->
            bzw_run (ws_fuel (Z.of_nat (length pl))) est0 (z_init pl);
  (* [comment removed for export] *)
  wl_close : forall pl, Z.of_nat (length pl) < 2 ^ 26 -> Forall (fun c => 0 <= c < 256) pl ->
            let '(cw, errw, e1, z1) := write_phase znew est0 pl in
            bzc_run (ws_fuel (Z.of_nat (length pl))) e1 z1
}.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WS.
  Variable segs : list Segment.
  Variable Im : cimg.
  Variable SI : StdioImg.
  Variable WIm : wsimg.
  Variable HCX : cctx -> eg -> est -> zstrm -> Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W A n A' n',
  disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros A n A' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transport.
  Variable segs : list Segment.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.

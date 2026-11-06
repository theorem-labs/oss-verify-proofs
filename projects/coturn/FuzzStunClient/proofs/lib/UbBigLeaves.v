(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymDriveX Spec UbReadBase UbWorld UbReadStage UbReadErr UbOomTail UbRefused.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma pres_cell : forall M0 M sp0 a n v,
  pres M0 M sp0 -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x58000)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> ~ rd_cell i) ->
  cell M0 a n v -> cell M a n v.
Proof.
  intros M0 M sp0 a n v P Ha Hn Hrd C. unfold cell in *. rewrite <- C.
  apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply P. left. rewrite u_small by lia.
  split; [lia|]. apply Hrd. lia.
Qed.

Lemma pres_img_clear : forall M0 M sp0 lo hi,
  pres M0 M sp0 -> (0x10000 <= lo)%Z -> (hi <= 0x58000)%Z ->
  (forall i, (lo <= i < hi)%Z -> ~ rd_cell i) ->
  img_clear M0 lo hi -> img_clear M lo hi.
Proof.
  intros M0 M sp0 lo hi P Hlo Hhi Hrd C i Hi. rewrite (P (Z_to_bv 64 i)); [apply C; exact Hi|].
  left. rewrite u_small by lia. split; [lia|]. apply Hrd. exact Hi.
Qed.

Lemma re_ivs_pres : forall M0 M sp0,
  pres M0 M sp0 ->
  Forall (fun iv => img_clear M0 (fst iv) (snd iv)) re_ivs ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Proof.
  intros M0 M sp0 P H. unfold re_ivs in *.
  repeat (apply Forall_cons_iff in H as [?C H]).
  repeat (apply Forall_cons; [eapply pres_img_clear; [exact P | cbn; lia | cbn; lia | unfold rd_cell, RSTAGE; cbn; intros; lia | assumption] |]).
  apply Forall_nil.
Qed.

Section BigLeaves.
  Context {AMB : Amb}.
  Variables (sp0 gm : word) (area brkv mas : Z) (tid : word) (M0 : word -> option byte).
  Variables (path : list byte) (stdin0 : InputStream) (fs0 : Fs).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis W : world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) M0.

  Lemma leaf_facts : forall R M, oom_leaf sp0 M0 R M ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) /\ getr R 3 = Z_to_bv 64 0x10800 /\ getr R 4 = Z_to_bv 64 0x36c60
    /\ stack_writable M sp0
    /\ Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs
    /\ cell M 0x36bb8 4 (bv_unsigned tid) /\ (0 < bv_unsigned tid < 2 ^ 22)%Z
    /\ cell M 0x36b98 8 0x36b98 /\ (exists cn, cell M 0x56ca0 8 cn) /\ cell M 0x56f18 8 4096.
  Proof.
    intros R M (Rsp & Rgp & Rtp & P & STK).
    repeat split; try assumption.
    - eapply re_ivs_pres; [exact P|]. apply re_ivs_of_world. exact (w_img _ _ _ _ _ _ W).
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell, RSTAGE; cbn; intros; lia | exact (w_tid _ _ _ _ _ _ W)].
    - pose proof (w_tidr _ _ _ _ _ _ W). lia.
    - pose proof (w_tidr _ _ _ _ _ _ W). lia.
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell, RSTAGE; cbn; intros; lia | exact (w_self _ _ _ _ _ _ W)].
    - destruct (w_canary _ _ _ _ _ _ W) as [cn Ccn]. exists cn.
      eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell, RSTAGE; cbn; intros; lia | exact Ccn].
    - eapply pres_cell; [exact P | lia | cbn; lia | unfold rd_cell, RSTAGE; cbn; intros; lia | exact (w_pagesz _ _ _ _ _ _ W)].
  Qed.

  (* [comment removed for export] *)
  Theorem big_oom_branch : oom_branch sp0 path stdin0 fs0 tid M0 (t_die msg_oom fs0).
  Proof.
    intros R M off V HL.
    destruct (leaf_facts R M HL) as (Rsp & Rgp & Rtp & STK & IMG & Ctid & Htid & Cself & (cn & Ccan) & Cpg).
    change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
    apply (ref_oom_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) R M
             Rsp Rgp Rtp STK IMG Ctid Htid Cself cn Ccan Cpg 0x13d28).
    left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem big_refused_leaf : forall R M off V, oom_leaf sp0 M0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13d08) M (seg_rom RSEGS)) (modelG path stdin0 fs0 tid off V))
               (t_die msg_refused fs0).
  Proof.
    intros R M off V HL.
    destruct (leaf_facts R M HL) as (Rsp & Rgp & Rtp & STK & IMG & Ctid & Htid & Cself & (cn & Ccan) & Cpg).
    change fs0 with (m_fs (modelG path stdin0 fs0 tid off V)).
    apply (ref_refused_tail sp0 [] (modelG path stdin0 fs0 tid off V) Hvsp eq_refl eq_refl eq_refl (bv_unsigned tid) R M
             Rsp Rgp Rtp STK IMG Ctid Htid Cself cn Ccan Cpg).
  Qed.
End BigLeaves.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

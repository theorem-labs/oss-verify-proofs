(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_ok_intro : forall E (sr : list expr) (R : bvmap 5 word),
  length sr = 32%nat ->
  (forall i : nat, (1 <= i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R Hlen H r. unfold sr_get, getr.
  destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|].
  pose proof (ridx_roundtrip r) as Hr. symmetry in Hr.
  pose proof (u5_range r) as Hu5.
  assert (Hnz : ridx r <> 0%nat).
  { intros Hz. unfold ridx in Hz. assert (H00 : bv_unsigned r = 0) by lia.
    assert (r = 0%bv) by (apply bv_eq; rewrite H00; reflexivity). subst r. rewrite bv_eqb_refl in Hr0. discriminate. }
  pose proof (ridx_range r) as Hrg.
  specialize (H (ridx r) ltac:(lia)). rewrite <- Hr in H. unfold getr in H. rewrite Hr0 in H. exact H.
Qed.




(* [comment removed for export] *)
Lemma kentry_ok_KRange : forall SEGS E M e lo hi,
  lo <= bv_unsigned (edenot E e) <= hi -> kentry_ok SEGS E M (KRange e lo hi).
Proof. intros SEGS E M e lo hi [H1 H2]. cbn. split; assumption. Qed.
Lemma kentry_ok_KAlign : forall SEGS E M e m,
  0 < m -> bv_unsigned (edenot E e) mod m = 0 -> kentry_ok SEGS E M (KAlign e m).
Proof. intros. cbn. split; assumption. Qed.




Lemma kentry_ok_KWr_wview : forall SEGS E M a n,
  flat E a (elenZ E n) ->
  (forall x : word, estart E a <= bv_unsigned x < estart E a + elenZ E n -> wview SEGS M x <> None) ->
  kentry_ok SEGS E M (KWr a n).
Proof.
  intros SEGS E M a n Hfl Hw. cbn. split; [exact Hfl|]. intros d m Hd Hdm.
  destruct m as [|m]; [reflexivity|].
  destruct Hfl as (F1 & F2 & F3 & F4).
  assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (apply u64_lit; lia).
  apply store_ok_of_all; [rewrite Hu; lia|]. intros x Hx. rewrite Hu in Hx. apply Hw. lia.
Qed.





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cs_ok_intro :
  forall SEGS {RC : run_ceil} {SFL : stk_floor} (PERMc : list (Z * Z)) (SPTOPc : Z) (FS0 : Fs.Fs) (SHC VSH : list (Z * Z))
         (AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) (KCAP FTOPc : Z)
         (FXOK : FX -> Prop) (UINV : env -> Prop)
         (E : env) (cs : acs) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    regs_ok E (s_regs (a_ss cs)) R ->
    s_log (a_ss cs) = [] ->
    know_ok SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) ->          (* [comment removed for export] *)
    m_halted model = None ->
    m_fs model = FS0 -> APS.fds_ok E (a_fd cs) model ->
    AINV (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M model ->
    UINV E -> FXOK fx ->
    wins_den E (a_ghost cs) = PERMc -> sptop_den E (a_brk cs) = SPTOPc ->
    uE E (a_meter cs) <= KCAP ->
    Z.of_nat (length (a_fake cs)) + uE E (a_fbud cs) <= FTOPc ->      (* [comment removed for export] *)
    floor_sem E (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ->     (* [comment removed for export] *)
    GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV E cs fx R M model.
Proof. intros. constructor; assumption. Qed.







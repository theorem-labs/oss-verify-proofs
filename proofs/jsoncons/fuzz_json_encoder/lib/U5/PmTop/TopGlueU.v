(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg SymDriveX HeapIface LibIface LibIfaceFp L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Pm6DrvLibL_u5 Pm6DrvG_u5 Pm6LayInst_u5 Pm6ExitAx_u5 Pm6ExitHandlers_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU HeapInstU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require PmHeapInst6_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TopGlueU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation SS := PML.STRTOD_SCR_V.
Abbreviation WD := PMES.WD_SCR_X.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma footx_in_envelope : Pm6LayInst_u5.foot_in_envelope PML.ll_footx_xsrc.
Proof. intros iv H. unfold PML.ll_footx_xsrc, PML.ll_foot_xsrc in H. cbn [app] in H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

Definition Lay0U (sptop : Z) : lib_layout :=
  Pm6LayInst_u5.PmLay (L0U sptop) (LCU.pm_creditxU (L0U sptop)) PML.ll_footx_xsrc.

Lemma Lay0U_credit : forall sptop, LCU.lay_creditU (L0U sptop) (Lay0U sptop).
Proof. intros sptop n. reflexivity. Qed.

Lemma Lay0U_drv : forall sptop, Pm6DrvLibL_u5.drv_lib_layout (Lay0U sptop) (L0U sptop).
Proof.
  intros sptop. apply Pm6LayInst_u5.drv_lib_layout_PmLay; [exact footx_in_envelope|].
  intros n Hn. unfold LCU.pm_creditxU.
  rewrite (LCU.kenc_g0 (L0U sptop)), (LCU.benc_g0 (L0U sptop)).
  cbn [fst snd]. rewrite L0U_kpm, L0U_bov, KPM_val, BOV_val. unfold PMES.CLU. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a H. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma rdn_same : forall (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
Proof.
  intros M M' a n Ha Hn H. apply rdn_agree. intros j Hj. rewrite u_lit by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Definition in_footx (a : Z) : Prop := exists iv, In iv PML.ll_footx_xsrc /\ fst iv <= a < snd iv.
Definition foot_same (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> in_footx a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma in_footx_iv : forall lo hi a, In (lo, hi) PML.ll_footx_xsrc -> lo <= a < hi -> in_footx a.
Proof. intros lo hi a Hin Ha. exists (lo, hi). split; [exact Hin | exact Ha]. Qed.
Lemma in_foot11_footx : forall a, PML.in_foot11 a -> in_footx a.
Proof. intros a (iv & Hiv & Hr). exists iv. split; [|exact Hr]. unfold PML.ll_footx_xsrc. apply in_or_app. left. exact Hiv. Qed.

Ltac foot_cell :=
  lazymatch goal with
  | |- in_footx ?a =>
      first [ apply (in_footx_iv 0xdb5c0 0xdb5c2); [cbn; tauto | lia]
            | apply (in_footx_iv 0xdb840 0xdb842); [cbn; tauto | lia]
            | apply (in_footx_iv 0xdb850 0xdba48); [cbn; tauto | lia]
            | apply (in_footx_iv 0xdbaf8 0xdbf78); [cbn; tauto | lia]
            | apply (in_footx_iv 0xdc6a8 0xdc708); [cbn; tauto | lia]
            | apply (in_footx_iv 0xfd058 0xfd278); [cbn; tauto | lia]
            | apply (in_footx_iv 0xdb5c8 0xdb610); [cbn; tauto | lia] ]
  end.

Lemma u8_same : forall M M' a v, foot_same M M' -> (forall i, a <= i < a + 1 -> in_footx i) -> 0 <= a < 2 ^ 63 -> PML.u8 M a v -> PML.u8 M' a v.
Proof. intros M M' a v FS HF Ha H. unfold PML.u8, L5.u8_at in *. rewrite (rdn_same M M' a 1) by (first [cbn; lia | intros i Hi; apply FS; [cbn in Hi; lia | apply HF; cbn in Hi; lia]]). exact H. Qed.
Lemma u32_same : forall M M' a v, foot_same M M' -> (forall i, a <= i < a + 4 -> in_footx i) -> 0 <= a < 2 ^ 63 -> PML.u32 M a v -> PML.u32 M' a v.
Proof. intros M M' a v FS HF Ha H. unfold PML.u32, L5.u32_at in *. rewrite (rdn_same M M' a 4) by (first [cbn; lia | intros i Hi; apply FS; [cbn in Hi; lia | apply HF; cbn in Hi; lia]]). exact H. Qed.
Lemma u64_same : forall M M' a v, foot_same M M' -> (forall i, a <= i < a + 8 -> in_footx i) -> 0 <= a < 2 ^ 63 -> PML.u64 M a v -> PML.u64 M' a v.
Proof. intros M M' a v FS HF Ha H. unfold PML.u64, L5.u64_at in *. rewrite (rdn_same M M' a 8) by (first [cbn; lia | intros i Hi; apply FS; [cbn in Hi; lia | apply HF; cbn in Hi; lia]]). exact H. Qed.

Ltac cell_same FS :=
  first [ eapply (u8_same _ _ _ _ FS); [intros i Hi; foot_cell | lia | eassumption]
        | eapply (u32_same _ _ _ _ FS); [intros i Hi; foot_cell | lia | eassumption]
        | eapply (u64_same _ _ _ _ FS); [intros i Hi; foot_cell | lia | eassumption] ].

Lemma loc_done_same : forall M M', foot_same M M' -> PML.loc_done M -> PML.loc_done M'.
Proof. intros M M' FS (A & B & C). unfold PML.loc_done. repeat split; cell_same FS. Qed.
Lemma errcat_same : forall M M' b, foot_same M M' -> PML.errcat_guard M b -> PML.errcat_guard M' b.
Proof. intros M M' b FS (A & B). unfold PML.errcat_guard. split; cell_same FS. Qed.
Lemma atexit_cells_same : forall M M' hs, foot_same M M' -> PML.atexit_cells M hs -> PML.atexit_cells M' hs.
Proof.   (* [comment removed for export] *)
  intros M M' hs FS H. apply (PML.atexit_cells_agree M M' hs); [|exact H]. intros a Ha. unfold PML.AX in Ha. apply FS; [lia | foot_cell].
Qed.
Lemma lits_ok_same : forall M M', foot_same M M' -> PML.lits_ok M -> PML.lits_ok M'.
Proof. intros M M' FS H. apply (PML.lits_ok_agree M M'); [|exact H]. intros a Ha. unfold PML.LIT_LO, PML.LIT_HI in Ha. apply FS; [lia | foot_cell]. Qed.
Lemma lits_pristine_same : forall M M', foot_same M M' -> PML.lits_pristine M -> PML.lits_pristine M'.
Proof. intros M M' FS H a Ha. unfold PML.LIT_LO, PML.LIT_HI in Ha. rewrite (FS a) by (first [lia | foot_cell]). apply H. unfold PML.LIT_LO, PML.LIT_HI. exact Ha. Qed.

Lemma ls_ok_same : forall sptop g M M', foot_same M M' ->
  (forall a : word, bv_unsigned a < ll_rw_lo (Lay0U sptop) -> M a = None -> M' a = None) ->
  (forall a, 0 <= a < 2 ^ 64 -> in_initc (Lay0U sptop) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PML.ls_ok g M -> PML.ls_ok g M'.
Proof.
  intros sptop g M M' FS HRO HC OK.
  destruct OK as (RO & (Q1 & Q2) & OK). split; [|split].
  - intros i Hi. apply HRO; [| apply RO; exact Hi]. rewrite u_lit by (unfold PML.IMG_RO_HI in Hi; lia).
    unfold Lay0U, Pm6LayInst_u5.PmLay. cbn [ll_rw_lo]. unfold PML.IMG_RO_HI in Hi. lia.
  - (* [comment removed for export] *)
    assert (IC : forall a, 0xfd2a3 <= a < 0xfd2a4 \/ 0xfd378 <= a < 0xfd37c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply HC; [lia|]. left. unfold Lay0U, Pm6LayInst_u5.PmLay. cbn [ll_initc].
      destruct Ha as [Ha|Ha]; [exists (0xfd2a3, 0xfd2a4) | exists (0xfd378, 0xfd37c)]; (split; [cbn; tauto | cbn [fst snd]; lia]). }
    unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK, PML.u8, PML.u32, L5.u8_at, L5.u32_at in *.
    split; [rewrite (rdn_same M M' 0xfd2a3 1) by (first [cbn; lia | intros i Hi; apply IC; cbn in Hi; lia]); exact Q1
           | rewrite (rdn_same M M' 0xfd378 4) by (first [cbn; lia | intros i Hi; apply IC; cbn in Hi; lia]); exact Q2].
  - destruct g.
    + (* [comment removed for export] *)
      destruct OK as (FP & AC0). split; [| eapply atexit_cells_same; eassumption].
      intros a Hin. assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hin as (iv & Hiv & Hr). unfold PML.ll_prist_xsrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn in Hr; lia|]). destruct Hiv. }
      rewrite (FS a Ha (in_foot11_footx a (PML.in_prist_foot11 a Hin))). apply FP. exact Hin.
    + destruct OK as (A & B & C). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption | eapply atexit_cells_same; eassumption].
    + destruct OK as (A & B & C). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption | eapply atexit_cells_same; eassumption].
Qed.

Lemma pm_statics_frame : forall sptop, lib_statics_frame (Lay0U sptop) PMX.pm_staticsx.
Proof.
  intros sptop g M M' OK HF HRO HC.
  assert (FS : foot_same M M') by (intros a Ha Hin; apply HF; [exact Ha | exact Hin]).
  destruct OK as (OK & LITS). split; [exact (ls_ok_same sptop g M M' FS HRO HC OK)|].
  destruct g; [exact (lits_pristine_same M M' FS LITS) | exact (lits_ok_same M M' FS LITS) | exact (lits_ok_same M M' FS LITS)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma atexit_state_of_cells0 : forall M, PML.atexit_cells M [] -> Pm6ExitAx_u5.atexit_state M [Pm6DrvLibL_u5.DRV_ATEXIT].
Proof.
  intros M (C0 & C4 & C8 & C16 & C24 & C32 & C288 & _). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f a Hn. destruct i as [|i]; [| destruct i; discriminate]. cbn in Hn. injection Hn as <- <-. split; [exact C32 | exact C288].
Qed.
Lemma atexit_state_of_cells1 : forall M, PML.atexit_cells M (PML.ls_atexit PML.LS2) -> Pm6ExitAx_u5.atexit_state M [Pm6DrvLibL_u5.DRV_ATEXIT; (0x69bec, 0xcb278)].
Proof.
  intros M (C0 & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f a Hn. destruct i as [|[|i]]; [| | destruct i; discriminate]; cbn in Hn; injection Hn as <- <-; [split; [exact C32 | exact C288] | split; [exact C40 | exact C296]].
Qed.

(* [comment removed for export] *)
Lemma rdn_img : forall (M : word -> option byte) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof. intros M a n Ha Hn H. apply rdn_same; [exact Ha | exact Hn |]. intros i Hi. apply H. exact Hi. Qed.

Lemma pm_exit_ok : Pm6DrvLibL_u5.lib_exit_ok PMX.pm_staticsx.
Proof.   (* [comment removed for export] *)
  apply Pm6ExitHandlers_u5.lib_exit_ok_of_cells. intros g M ((RO & _ & OK) & _). destruct g.
  - left. apply atexit_state_of_cells0. apply OK.
  - left. apply atexit_state_of_cells0. apply OK.
  - right. apply atexit_state_of_cells1. apply OK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pm_statics_init : forall sptop, lib_statics_init (Lay0U sptop) PMX.pm_staticsx.
Proof.
  intros sptop av uid rnd tid canary hw M HI.
  pose proof HI as CELLS. unfold lib_init_facts in CELLS. cbv zeta in CELLS. repeat match type of CELLS with _ /\ _ => apply proj2 in CELLS end.     (* [comment removed for export] *)
  destruct HI as (IMG & _).
  unfold Lay0U, Pm6LayInst_u5.PmLay in IMG, CELLS. cbn [ll_init_img] in IMG. cbn [ll_init_cells ll_heap] in CELLS.
  split; [split; [|split]|].
  - intros i Hi. unfold PML.IMG_RO_HI in Hi. apply (IMG (0x10000, 0xcb538) i); [cbn; tauto | cbn; lia].
  - (* [comment removed for export] *)
    unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK, PML.u8, PML.u32, L5.u8_at, L5.u32_at.
    rewrite (rdn_img M 0xfd2a3 1), (rdn_img M 0xfd378 4)
      by (first [cbn; lia | intros i Hi; cbn in Hi; first [apply (IMG (0xfd2a3, 0xfd2a4) i); [cbn; tauto | cbn; lia] | apply (IMG (0xfd378, 0xfd37c) i); [cbn; tauto | cbn; lia]]]).
    split; vm_compute; reflexivity.
  - split.
    + (* [comment removed for export] *)
      intros a (iv & Hiv & Hr). unfold PML.ll_prist_xsrc in Hiv.
      repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; apply (IMG (0xdb595, 0xdcf40) a); [cbn; tauto | cbn; lia]|]). destruct Hiv.
    + (* [comment removed for export] *)
      unfold PML.atexit_cells, PML.u8, PML.u32, PML.u64, L5.u8_at, L5.u32_at, L5.u64_at, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD.
      rewrite (rdn_img M 0xfd058 1), (rdn_img M 0xfd05c 4), (rdn_img M 0xfd070 8)
        by (first [cbn; lia | intros i Hi; cbn in Hi; first [apply (IMG (0xfd058, 0xfd060) i); [cbn; tauto | cbn; lia] | apply (IMG (0xfd070, 0xfd078) i); [cbn; tauto | cbn; lia]]]).
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [exact (CELLS (0xfd060, 4%nat, 1) ltac:(cbn; tauto))|]. split; [exact (CELLS (0xfd068, 8%nat, 0xfd070) ltac:(cbn; tauto))|].
      split; [vm_compute; reflexivity|].
      split; [exact (CELLS (0xfd078, 8%nat, 0xad8c0) ltac:(cbn; tauto))|]. split; [exact (CELLS (0xfd178, 8%nat, 0x3a598) ltac:(cbn; tauto)) | exact I].
  - (* [comment removed for export] *)
    intros a Ha. unfold PML.LIT_LO, PML.LIT_HI in Ha. apply (IMG (0xdb595, 0xdcf40) a); [cbn; tauto | cbn; lia].
Qed.

End TopGlueU.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg SymDriveX HeapIface LibIface LibIfaceFp L5Defs L5Core PmLibDefs PmLibSpecs PmEncSpecs PmLibSpecsX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm6DrvLibL Pm6DrvG Pm6LayInst Pm6ExitAx Pm6ExitHandlers.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmPhiX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import LibIfaceFpW PmTopSpecsXW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require PmHeapInst6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TopGlueXW.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation SS := PML.STRTOD_SCR_V.
Abbreviation WD := PMES.WD_SCR_X.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma footx_in_envelope : Pm6LayInst.foot_in_envelope PML.ll_footx_xsrc.
Proof. intros iv H. unfold PML.ll_footx_xsrc, PML.ll_foot_xsrc in H. cbn [app] in H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

Definition Lay0 (sptop : Z) : lib_layout := Pm6LayInst.PmLay (PmHeapInst6.L0 sptop) (PMX.pm_creditx (PmHeapInst6.L0 sptop)) PML.ll_footx_xsrc.

Lemma Lay0_drv : forall sptop, Pm6DrvLibL.drv_lib_layout (Lay0 sptop) (PmHeapInst6.L0 sptop).
Proof.
  intros sptop. apply Pm6LayInst.drv_lib_layout_PmLay; [exact footx_in_envelope|].
  intros n Hn. unfold PMX.pm_creditx. cbn [fst snd hl_k_per_malloc hl_b_overhead PmHeapInst6.L0].
  replace PmHeapInst6.BOV with 3609042 by vmc_refl. replace PmHeapInst6.KPM with 8 by vmc_refl. lia.
Qed.

Lemma Lay0_pm : forall sptop, PMX.pm_layout_okx (PmHeapInst6.L0 sptop) SS WD (Lay0 sptop).
Proof.
  intros sptop. unfold PMX.pm_layout_okx, Lay0, Pm6LayInst.PmLay. cbn [ll_heap ll_entry ll_gp ll_stack ll_foot ll_credit ll_rw_lo].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - unfold PMX.LIB_SCRX, PMX.READX_SCR, PMX.READNEXTX_SCR, PMX.PSOMEX_SCR, PMX.PFX_SCR, PMX.VIS_SCR, PMES.VIS_SCR, PMES.STRX_SCR, PMES.ENC_CTOR_SCR, PMES.WD_SCR_X,
      PMS.RCTOR_SCR, PMS.ISS_SCR, PMS.CTOR_SCR, PMS.ISLAND_SCR, PMS.OPNEW_SCR, PMS.STR_SCR, PML.STRTOD_SCR_V, PML.HEAP_STACK.
    unfold PMES.STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK. lia.
  - split; [reflexivity|]. split; [intros n; reflexivity|]. unfold PML.IMG_RO_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma Lay0_budget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    Pm6DrvG.cred (PmHeapInst6.L0 (bv_unsigned sp))
      (PmHeapInst6.KPM + 4 * fst (ll_credit (Lay0 (bv_unsigned sp)) n)) (n + PmHeapInst6.BOV + 4 * snd (ll_credit (Lay0 (bv_unsigned sp)) n)) 0
      (debit (PmHeapInst6.L0 (bv_unsigned sp)) (PmHeapInst6.K0, PmHeapInst6.B0) 65536).
Proof.
  intros sp n Hsp Hn. unfold Lay0, Pm6LayInst.PmLay, PMX.pm_creditx, Pm6DrvG.cred, Pm6DrvG.CAPk, debit.
  cbn [ll_credit fst snd hl_k_per_malloc hl_b_overhead PmHeapInst6.L0].
  replace PmHeapInst6.BOV with 3609042 by vmc_refl. replace PmHeapInst6.KPM with 8 by vmc_refl.
  replace PmHeapInst6.K0 with 3840 by vmc_refl. replace PmHeapInst6.B0 with (2 ^ 33) by vmc_refl. lia.
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
      first [ apply (in_footx_iv 0xd7bd0 0xd7bd2); [cbn; tauto | lia]
            | apply (in_footx_iv 0xd7e50 0xd7e52); [cbn; tauto | lia]
            | apply (in_footx_iv 0xd7e60 0xd8058); [cbn; tauto | lia]
            | apply (in_footx_iv 0xd8108 0xd8588); [cbn; tauto | lia]
            | apply (in_footx_iv 0xd8cb8 0xd8d18); [cbn; tauto | lia]
            | apply (in_footx_iv 0xf9668 0xf9888); [cbn; tauto | lia]
            | apply (in_footx_iv 0xd7bd8 0xd7c20); [cbn; tauto | lia] ]
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
  (forall a : word, bv_unsigned a < ll_rw_lo (Lay0 sptop) -> M a = None -> M' a = None) ->
  (forall a, 0 <= a < 2 ^ 64 -> in_initc (Lay0 sptop) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PML.ls_ok g M -> PML.ls_ok g M'.
Proof.
  intros sptop g M M' FS HRO HC OK.
  destruct OK as (RO & (Q1 & Q2) & OK). split; [|split].
  - intros i Hi. apply HRO; [| apply RO; exact Hi]. rewrite u_lit by (unfold PML.IMG_RO_HI in Hi; lia).
    unfold Lay0, Pm6LayInst.PmLay. cbn [ll_rw_lo]. unfold PML.IMG_RO_HI in Hi. lia.
  - (* [comment removed for export] *)
    assert (IC : forall a, 0xf98b3 <= a < 0xf98b4 \/ 0xf9988 <= a < 0xf998c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply HC; [lia|]. left. unfold Lay0, Pm6LayInst.PmLay. cbn [ll_initc].
      destruct Ha as [Ha|Ha]; [exists (0xf98b3, 0xf98b4) | exists (0xf9988, 0xf998c)]; (split; [cbn; tauto | cbn [fst snd]; lia]). }
    unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK, PML.u8, PML.u32, L5.u8_at, L5.u32_at in *.
    split; [rewrite (rdn_same M M' 0xf98b3 1) by (first [cbn; lia | intros i Hi; apply IC; cbn in Hi; lia]); exact Q1
           | rewrite (rdn_same M M' 0xf9988 4) by (first [cbn; lia | intros i Hi; apply IC; cbn in Hi; lia]); exact Q2].
  - destruct g.
    + (* [comment removed for export] *)
      destruct OK as (FP & AC0). split; [| eapply atexit_cells_same; eassumption].
      intros a Hin. assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hin as (iv & Hiv & Hr). unfold PML.ll_prist_xsrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn in Hr; lia|]). destruct Hiv. }
      rewrite (FS a Ha (in_foot11_footx a (PML.in_prist_foot11 a Hin))). apply FP. exact Hin.
    + destruct OK as (A & B & C). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption | eapply atexit_cells_same; eassumption].
    + destruct OK as (A & B & C). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption | eapply atexit_cells_same; eassumption].
Qed.

Lemma pm_statics_frame : forall sptop, lib_statics_frame (Lay0 sptop) PMX.pm_staticsx.
Proof.
  intros sptop g M M' OK HF HRO HC.
  assert (FS : foot_same M M') by (intros a Ha Hin; apply HF; [exact Ha | exact Hin]).
  destruct OK as (OK & LITS). split; [exact (ls_ok_same sptop g M M' FS HRO HC OK)|].
  destruct g; [exact (lits_pristine_same M M' FS LITS) | exact (lits_ok_same M M' FS LITS) | exact (lits_ok_same M M' FS LITS)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma atexit_state_of_cells0 : forall M, PML.atexit_cells M [] -> Pm6ExitAx.atexit_state M [Pm6DrvLibL.DRV_ATEXIT].
Proof.
  intros M (C0 & C4 & C8 & C16 & C24 & C32 & C288 & _). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f a Hn. destruct i as [|i]; [| destruct i; discriminate]. cbn in Hn. injection Hn as <- <-. split; [exact C32 | exact C288].
Qed.
Lemma atexit_state_of_cells1 : forall M, PML.atexit_cells M (PML.ls_atexit PML.LS2) -> Pm6ExitAx.atexit_state M [Pm6DrvLibL.DRV_ATEXIT; (0x662a0, 0xc7888)].
Proof.
  intros M (C0 & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f a Hn. destruct i as [|[|i]]; [| | destruct i; discriminate]; cbn in Hn; injection Hn as <- <-; [split; [exact C32 | exact C288] | split; [exact C40 | exact C296]].
Qed.

(* [comment removed for export] *)
Lemma rdn_img : forall (M : word -> option byte) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof. intros M a n Ha Hn H. apply rdn_same; [exact Ha | exact Hn |]. intros i Hi. apply H. exact Hi. Qed.

Lemma pm_exit_ok : Pm6DrvLibL.lib_exit_ok PMX.pm_staticsx.
Proof.   (* [comment removed for export] *)
  apply Pm6ExitHandlers.lib_exit_ok_of_cells. intros g M ((RO & _ & OK) & _). destruct g.
  - left. apply atexit_state_of_cells0. apply OK.
  - left. apply atexit_state_of_cells0. apply OK.
  - right. apply atexit_state_of_cells1. apply OK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pm_statics_init : forall sptop, lib_statics_init (Lay0 sptop) PMX.pm_staticsx.
Proof.
  intros sptop av uid rnd tid canary hw M HI.
  pose proof HI as CELLS. unfold lib_init_facts in CELLS. cbv zeta in CELLS. repeat match type of CELLS with _ /\ _ => apply proj2 in CELLS end.     (* [comment removed for export] *)
  destruct HI as (IMG & _).
  unfold Lay0, Pm6LayInst.PmLay in IMG, CELLS. cbn [ll_init_img] in IMG. cbn [ll_init_cells ll_heap] in CELLS.
  split; [split; [|split]|].
  - intros i Hi. unfold PML.IMG_RO_HI in Hi. apply (IMG (0x10000, 0xc7b48) i); [cbn; tauto | cbn; lia].
  - (* [comment removed for export] *)
    unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK, PML.u8, PML.u32, L5.u8_at, L5.u32_at.
    rewrite (rdn_img M 0xf98b3 1), (rdn_img M 0xf9988 4)
      by (first [cbn; lia | intros i Hi; cbn in Hi; first [apply (IMG (0xf98b3, 0xf98b4) i); [cbn; tauto | cbn; lia] | apply (IMG (0xf9988, 0xf998c) i); [cbn; tauto | cbn; lia]]]).
    split; vm_compute; reflexivity.
  - split.
    + (* [comment removed for export] *)
      intros a (iv & Hiv & Hr). unfold PML.ll_prist_xsrc in Hiv.
      repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; apply (IMG (0xd7ba5, 0xd9550) a); [cbn; tauto | cbn; lia]|]). destruct Hiv.
    + (* [comment removed for export] *)
      unfold PML.atexit_cells, PML.u8, PML.u32, PML.u64, L5.u8_at, L5.u32_at, L5.u64_at, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD.
      rewrite (rdn_img M 0xf9668 1), (rdn_img M 0xf966c 4), (rdn_img M 0xf9680 8)
        by (first [cbn; lia | intros i Hi; cbn in Hi; first [apply (IMG (0xf9668, 0xf9670) i); [cbn; tauto | cbn; lia] | apply (IMG (0xf9680, 0xf9688) i); [cbn; tauto | cbn; lia]]]).
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [exact (CELLS (0xf9670, 4%nat, 1) ltac:(cbn; tauto))|]. split; [exact (CELLS (0xf9678, 8%nat, 0xf9680) ltac:(cbn; tauto))|].
      split; [vm_compute; reflexivity|].
      split; [exact (CELLS (0xf9688, 8%nat, 0xa9f74) ltac:(cbn; tauto))|]. split; [exact (CELLS (0xf9788, 8%nat, 0x39d18) ltac:(cbn; tauto)) | exact I].
  - (* [comment removed for export] *)
    intros a Ha. unfold PML.LIT_LO, PML.LIT_HI in Ha. apply (IMG (0xd7ba5, 0xd9550) a); [cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cfg0P : ScfgP := {| SCFG := PmPhiX.cfg0 |}.

Lemma Lay0_ifacew : forall (PHI : list byte -> Prop) sptop,
  @PMXW.lib_specxw cfg0P (PmHeapInst6.L0 sptop) (PmHeapInst6.HI0 sptop) SS WD PHI (Lay0 sptop) ->
  lib_iface_ok_fpw (Lay0 sptop) PmPhiX.cfg0 (PmHeapInst6.HI0 sptop) PMX.pm_staticsx PHI.
Proof.
  intros PHI sptop LIB. constructor.
  - exact (LIB (Lay0_pm sptop)).
  - exact (pm_statics_init sptop).
  - exact (pm_statics_frame sptop).
Qed.

(* [comment removed for export] *)
Lemma Lay0_iface : forall sptop,
  @PMX.lib_specx cfg0P (PmHeapInst6.L0 sptop) (PmHeapInst6.HI0 sptop) SS WD (Lay0 sptop) ->
  lib_iface_ok_fp (Lay0 sptop) PmPhiX.cfg0 (PmHeapInst6.HI0 sptop) PMX.pm_staticsx.
Proof.
  intros sptop LIB. constructor.
  - exact (LIB (Lay0_pm sptop)).
  - exact (pm_statics_init sptop).
  - exact (pm_statics_frame sptop).
Qed.
End TopGlueXW.

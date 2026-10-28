(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec StoreOk ShapeAlg SpinAlg SymDriveX HeapIface LibIface LibIfaceFp L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Pm10DrvLibL_u Pm10LayInst_u Pm10ExitAx_u Pm10ExitHandlers_u Pm10ExitHandlersC_u PmFinal_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmCurSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TopGlueC.
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma foot11_in_envelope : Pm10LayInst_u.foot_in_envelope PML.ll_foot_csrc.
Proof. intros iv H. unfold PML.ll_foot_csrc in H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

Definition Lay0 (sptop : Z) : lib_layout := Pm10LayInst_u.PmLay (PmHeapInst10_u.L0 sptop) (PMCS.pm_credit_c (PmHeapInst10_u.L0 sptop)) PML.ll_foot_csrc.

Lemma Lay0_drv : forall sptop, Pm10DrvLibL_u.drv_lib_layout (Lay0 sptop) (PmHeapInst10_u.L0 sptop).
Proof.
  intros sptop. apply Pm10LayInst_u.drv_lib_layout_PmLay; [exact foot11_in_envelope|].
  intros n Hn. unfold PMCS.pm_credit_c. cbn [fst snd hl_k_per_malloc hl_b_overhead PmHeapInst10_u.L0].
  replace PmHeapInst10_u.BOV with 6350523 by vmc_refl. replace PmHeapInst10_u.KPM with 8 by vmc_refl. lia.
Qed.

Lemma Lay0_pm : forall sptop STRTOD_SCR, STRTOD_SCR <= 54208 -> PMCS.pm_layout_ok_c (PmHeapInst10_u.L0 sptop) STRTOD_SCR (Lay0 sptop).
Proof.
  intros sptop SS HSS. unfold PMCS.pm_layout_ok_c, Lay0, Pm10LayInst_u.PmLay. cbn [ll_heap ll_entry ll_gp ll_stack ll_foot ll_credit ll_rw_lo].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - unfold PMCS.LIB_SCR_C, PMCS.CCTOR_SCR, PMCS.CCTOR_MAIN_SCR, PMCS.RN_SCR, PMCS.GETSTR_SCR, PMS.ISS_SCR, PMS.READNEXT_SCR, PMS.PSOME_SCR, PMS.PF_SCR, PMS.CTOR_SCR, PMS.ISLAND_SCR, PMS.OPNEW_SCR, PMS.OPDEL_SCR, PML.HEAP_STACK. lia.
  - split; [reflexivity|]. split; [intros n; reflexivity|]. unfold PML.IMG_RO_HI. lia.
Qed.

Lemma Lay0_budget : PmFinal_u.budget0_ok (fun sp => Lay0 (bv_unsigned sp)).
Proof.
  apply PmFinal_u.budget0_of_bounds. intros sp n Hn. unfold Lay0, Pm10LayInst_u.PmLay, PMCS.pm_credit_c. cbn [ll_credit fst snd hl_k_per_malloc hl_b_overhead PmHeapInst10_u.L0].
  replace PmHeapInst10_u.BOV with 6350523 by vmc_refl. replace PmHeapInst10_u.KPM with 8 by vmc_refl. lia.
Qed.

Lemma u_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a H. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact H. Qed.

Lemma rdn_same : forall (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
Proof.
  intros M M' a n Ha Hn H. apply rdn_agree. intros j Hj. rewrite u_lit by lia. apply H. lia.
Qed.

Definition foot_same (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> PML.in_foot11 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma in_foot11_iv : forall lo hi a, In (lo, hi) PML.ll_foot_csrc -> lo <= a < hi -> PML.in_foot11 a.
Proof. intros lo hi a Hin Ha. exists (lo, hi). split; [exact Hin | exact Ha]. Qed.

Ltac foot_cell :=
  lazymatch goal with
  | |- PML.in_foot11 ?a =>
      first [ apply (in_foot11_iv 0xd4df0 0xd4df2); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd4df8 0xd4dfa); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd5030 0xd5032); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd5040 0xd5238); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd52e8 0xd5768); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd5e98 0xd5ef8); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xf6848 0xf6a68); [cbn; tauto | lia] ]
  end.

Lemma u8_same : forall M M' a v, foot_same M M' -> (forall i, a <= i < a + 1 -> PML.in_foot11 i) -> 0 <= a < 2 ^ 63 -> PML.u8 M a v -> PML.u8 M' a v.
Proof. intros M M' a v FS HF Ha H. unfold PML.u8, L5.u8_at in *. rewrite (rdn_same M M' a 1) by (first [cbn; lia | intros i Hi; apply FS; [cbn in Hi; lia | apply HF; cbn in Hi; lia]]). exact H. Qed.
Lemma u32_same : forall M M' a v, foot_same M M' -> (forall i, a <= i < a + 4 -> PML.in_foot11 i) -> 0 <= a < 2 ^ 63 -> PML.u32 M a v -> PML.u32 M' a v.
Proof. intros M M' a v FS HF Ha H. unfold PML.u32, L5.u32_at in *. rewrite (rdn_same M M' a 4) by (first [cbn; lia | intros i Hi; apply FS; [cbn in Hi; lia | apply HF; cbn in Hi; lia]]). exact H. Qed.
Lemma u64_same : forall M M' a v, foot_same M M' -> (forall i, a <= i < a + 8 -> PML.in_foot11 i) -> 0 <= a < 2 ^ 63 -> PML.u64 M a v -> PML.u64 M' a v.
Proof. intros M M' a v FS HF Ha H. unfold PML.u64, L5.u64_at in *. rewrite (rdn_same M M' a 8) by (first [cbn; lia | intros i Hi; apply FS; [cbn in Hi; lia | apply HF; cbn in Hi; lia]]). exact H. Qed.

Ltac cell_same FS :=
  first [ eapply (u8_same _ _ _ _ FS); [intros i Hi; foot_cell | lia | eassumption]
        | eapply (u32_same _ _ _ _ FS); [intros i Hi; foot_cell | lia | eassumption]
        | eapply (u64_same _ _ _ _ FS); [intros i Hi; foot_cell | lia | eassumption] ].

Lemma loc_done_same : forall M M', foot_same M M' -> PML.loc_done M -> PML.loc_done M'.
Proof. intros M M' FS (A & B & C). unfold PML.loc_done. repeat split; cell_same FS. Qed.
Lemma errcat_same : forall M M' b, foot_same M M' -> PML.errcat_guard M b -> PML.errcat_guard M' b.
Proof. intros M M' b FS (A & B). unfold PML.errcat_guard. split; cell_same FS. Qed.
Lemma convcat_same : forall M M' b, foot_same M M' -> PML.convcat_guard M b -> PML.convcat_guard M' b.
Proof. intros M M' b FS (A & B). unfold PML.convcat_guard. split; cell_same FS. Qed.
Lemma atexit_cells_same : forall M M' hs, foot_same M M' -> PML.atexit_cells M hs -> PML.atexit_cells M' hs.
Proof.
  intros M M' hs FS H. apply (PML.atexit_cells_agree M M' hs); [|exact H]. intros a Ha. unfold PML.AX in Ha. apply FS; [lia | foot_cell].
Qed.

Lemma pm_statics_frame : forall sptop, lib_statics_frame (Lay0 sptop) PMS.pm_statics.
Proof.
  intros sptop g M M' OK HF HRO HC.
  assert (FS : foot_same M M') by (intros a Ha Hin; apply HF; [exact Ha | exact Hin]).
  destruct OK as (RO & (Q1 & Q2) & OK). split; [|split].
  - intros i Hi. apply HRO; [| apply RO; exact Hi]. rewrite u_lit by (unfold PML.IMG_RO_HI in Hi; lia).
    unfold Lay0, Pm10LayInst_u.PmLay. cbn [ll_rw_lo]. unfold PML.IMG_RO_HI in Hi. lia.
  -
    assert (IC : forall a, 0xf6a93 <= a < 0xf6a94 \/ 0xf6b68 <= a < 0xf6b6c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply HC; [lia|]. left. unfold Lay0, Pm10LayInst_u.PmLay. cbn [ll_initc].
      destruct Ha as [Ha|Ha]; [exists (0xf6a93, 0xf6a94) | exists (0xf6b68, 0xf6b6c)]; (split; [cbn; tauto | cbn [fst snd]; lia]). }
    unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK, PML.u8, PML.u32, L5.u8_at, L5.u32_at in *.
    split; [rewrite (rdn_same M M' 0xf6a93 1) by (first [cbn; lia | intros i Hi; apply IC; cbn in Hi; lia]); exact Q1
           | rewrite (rdn_same M M' 0xf6b68 4) by (first [cbn; lia | intros i Hi; apply IC; cbn in Hi; lia]); exact Q2].
  - destruct g.
    +
      destruct OK as (FP & AC0). split; [| eapply atexit_cells_same; eassumption].
      intros a Hin. assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hin as (iv & Hiv & Hr). unfold PML.ll_prist_csrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn in Hr; lia|]). destruct Hiv. }
      rewrite (FS a Ha (PML.in_prist_foot11 a Hin)). apply FP. exact Hin.
    + destruct OK as (A & B & C & D). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption|].
      split; [eapply convcat_same; eassumption | eapply atexit_cells_same; eassumption].
    + destruct OK as (A & B & C & D). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption|].
      split; [eapply convcat_same; eassumption | eapply atexit_cells_same; eassumption].
    + destruct OK as (A & B & C & D). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption|].
      split; [eapply convcat_same; eassumption | eapply atexit_cells_same; eassumption].
    + destruct OK as (A & B & C & D). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption|].
      split; [eapply convcat_same; eassumption | eapply atexit_cells_same; eassumption].
    + destruct OK as (A & B & C & D). split; [eapply loc_done_same; eassumption|]. split; [eapply errcat_same; eassumption|].
      split; [eapply convcat_same; eassumption | eapply atexit_cells_same; eassumption].
Qed.

Lemma atexit_state_of_cells0 : forall M, PML.atexit_cells M [] -> Pm10ExitAx_u.atexit_state M [Pm10DrvLibL_u.DRV_ATEXIT].
Proof.
  intros M (C0 & C4 & C8 & C16 & C24 & C32 & C288 & _). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f a Hn. destruct i as [|i]; [| destruct i; discriminate]. cbn in Hn. injection Hn as <- <-. split; [exact C32 | exact C288].
Qed.
Lemma atexit_state_of_cells1 : forall M f a, PML.atexit_cells M [(f, a)] -> Pm10ExitAx_u.atexit_state M [Pm10DrvLibL_u.DRV_ATEXIT; (f, a)].
Proof.
  intros M f a (C0 & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f' a' Hn. destruct i as [|[|i]]; [| | destruct i; discriminate]; cbn in Hn; injection Hn as <- <-; [split; [exact C32 | exact C288] | split; [exact C40 | exact C296]].
Qed.
Lemma atexit_state_of_cells2 : forall M f a f2 a2, PML.atexit_cells M [(f, a); (f2, a2)] -> Pm10ExitAx_u.atexit_state M [Pm10DrvLibL_u.DRV_ATEXIT; (f, a); (f2, a2)].
Proof.
  intros M f a f2 a2 (C0 & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & C48 & C304). split; [exact C4|]. split; [cbn; lia|]. split; [exact C16|]. split; [exact C8|]. split; [exact C24|].
  intros i f' a' Hn. destruct i as [|[|[|i]]]; [| | | destruct i; discriminate]; cbn in Hn; injection Hn as <- <-;
    [split; [exact C32 | exact C288] | split; [exact C40 | exact C296] | split; [exact C48 | exact C304]].
Qed.

Lemma rdn_img : forall (M : word -> option byte) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof. intros M a n Ha Hn H. apply rdn_same; [exact Ha | exact Hn |]. intros i Hi. apply H. exact Hi. Qed.

Lemma pm_exit_ok : Pm10DrvLibL_u.lib_exit_ok PMS.pm_statics.
Proof.
  apply Pm10ExitHandlersC_u.lib_exit_ok_of_cells_c. intros g M (RO & _ & OK). unfold Pm10ExitHandlersC_u.lib_hs_ok, Pm10ExitHandlersC_u.REG_J, Pm10ExitHandlersC_u.REG_C.
  destruct g; cbn [PML.ls_atexit PML.jreg PML.creg PML.ATEXIT_HANDLER PML.OBJ_JSON_CATEGORY PML.OBJ_CONV_CATEGORY] in OK.
  - exists []. split; [left; reflexivity | apply atexit_state_of_cells0; apply OK].
  - exists []. split; [left; reflexivity | apply atexit_state_of_cells0; apply OK].
  - exists [(0x63404, 0xc4aa8)]. split; [right; left; reflexivity | apply atexit_state_of_cells1; apply OK].
  - exists [(0x63404, 0xc4aa0)]. split; [right; right; left; reflexivity | apply atexit_state_of_cells1; apply OK].
  - exists [(0x63404, 0xc4aa8); (0x63404, 0xc4aa0)]. split; [right; right; right; left; reflexivity | apply atexit_state_of_cells2; apply OK].
  - exists [(0x63404, 0xc4aa0); (0x63404, 0xc4aa8)]. split; [right; right; right; right; reflexivity | apply atexit_state_of_cells2; apply OK].
Qed.

Lemma pm_statics_init : forall sptop, lib_statics_init (Lay0 sptop) PMS.pm_statics.
Proof.
  intros sptop av uid rnd tid canary hw M HI.
  pose proof HI as CELLS. unfold lib_init_facts in CELLS. cbv zeta in CELLS. repeat match type of CELLS with _ /\ _ => apply proj2 in CELLS end.
  destruct HI as (IMG & _).
  unfold Lay0, Pm10LayInst_u.PmLay in IMG, CELLS. cbn [ll_init_img] in IMG. cbn [ll_init_cells ll_heap] in CELLS.
  split; [|split].
  - intros i Hi. unfold PML.IMG_RO_HI in Hi. apply (IMG (0x10000, 0xc4d70) i); [cbn; tauto | cbn; lia].
  -
    unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK, PML.u8, PML.u32, L5.u8_at, L5.u32_at.
    rewrite (rdn_img M 0xf6a93 1), (rdn_img M 0xf6b68 4)
      by (first [cbn; lia | intros i Hi; cbn in Hi; first [apply (IMG (0xf6a93, 0xf6a94) i); [cbn; tauto | cbn; lia] | apply (IMG (0xf6b68, 0xf6b6c) i); [cbn; tauto | cbn; lia]]]).
    split; vm_compute; reflexivity.
  - split.
    +
      intros a (iv & Hiv & Hr). unfold PML.ll_prist_csrc in Hiv.
      repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; apply (IMG (0xd4dc5, 0xd6730) a); [cbn; tauto | cbn; lia]|]). destruct Hiv.
    +
      unfold PML.atexit_cells, PML.u8, PML.u32, PML.u64, L5.u8_at, L5.u32_at, L5.u64_at, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD.
      rewrite (rdn_img M 0xf6848 1), (rdn_img M 0xf684c 4), (rdn_img M 0xf6860 8)
        by (first [cbn; lia | intros i Hi; cbn in Hi; first [apply (IMG (0xf6848, 0xf6850) i); [cbn; tauto | cbn; lia] | apply (IMG (0xf6860, 0xf6868) i); [cbn; tauto | cbn; lia]]]).
      split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [exact (CELLS (0xf6850, 4%nat, 1) ltac:(cbn; tauto))|]. split; [exact (CELLS (0xf6858, 8%nat, 0xf6860) ltac:(cbn; tauto))|].
      split; [vm_compute; reflexivity|].
      split; [exact (CELLS (0xf6868, 8%nat, 0xa710c) ltac:(cbn; tauto))|]. split; [exact (CELLS (0xf6968, 8%nat, 0x39674) ltac:(cbn; tauto)) | exact I].
Qed.

Definition cfg0P : ScfgP := {| SCFG := PmFinal_u.cfg0 |}.

Lemma Lay0_iface : forall sptop STRTOD_SCR, STRTOD_SCR <= 54208 ->
  @PMCS.lib_spec_c cfg0P (PmHeapInst10_u.L0 sptop) (PmHeapInst10_u.HI0 sptop) STRTOD_SCR (Lay0 sptop) ->
  lib_iface_ok_fp (Lay0 sptop) PmFinal_u.cfg0 (PmHeapInst10_u.HI0 sptop) PMS.pm_statics.
Proof.
  intros sptop SS HSS LIB. constructor.
  - exact (LIB (Lay0_pm sptop SS HSS)).
  - exact (pm_statics_init sptop).
  - exact (pm_statics_frame sptop).
Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

End FPX_1.
End TopGlueC.


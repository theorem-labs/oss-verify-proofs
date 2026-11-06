(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel AsanMainU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP AMalloc_iface ADepot_iface ADepot
     ADepot_init ADepotW F_adepotW ADepot_initW AFake_iface AFake_arep AInstance AInstanceM AInstanceF AInstanceW0 AInstanceFW AInstanceW
     ASec ARepQ ARepQP ARepInit_kit ARepInit_glue ARepInit ARepInit_S AU_iface ADriver_iface AMain_asm AD_handoff ATsafeMain.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Keyed Unification.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma AHk_rng_mono : forall k L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP_P (AHI_k k) L RNG st LB m -> AHEAP_P (AHI_k k) L RNG' st LB m.
Proof.
  intros k L RNG RNG' st LB m LE (ALO & ARNG & XB & HFK).
  split; [exact ALO|]. split; [eapply arng_mono; [exact LE| exact ARNG]|]. split; [exact XB| exact HFK].
Qed.
Lemma AHk_perm : forall k L RNG st LB LB' m, Permutation LB LB' -> AHEAP_P (AHI_k k) L RNG st LB m -> AHEAP_P (AHI_k k) L RNG st LB' m.
Proof.
  intros k L RNG st LB LB' m P (ALO & ARNG & [X [AR (B1 & B2 & B3 & B4)]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [exact AR|]. split; [| split; [| split]].
    + intros p A n Hin. apply (B1 p A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + intros cls A n Hin. apply (B2 cls A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + eapply Permutation_NoDup; [apply hb_ids_perm; exact P| exact B3].
    + eapply Permutation_NoDup; [exact P| exact B4].
  - cbn [AHI_k ah_fake] in *. eapply afake_blocks; [exact HFK|]. intros c F n. split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact P| exact P].
Qed.

Definition AI_k (k : Z) : AMallocIface :=
  {| aci := aci_I;
     AHEAP := AHEAP_P (AHI_k k);
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AHk_rng_mono k;
     AI_perm := AHk_perm k;
     AI_frame := AHIk_frame k;
     AI_block := fun L RNG st LB m p A n H Hin => AHI_block L RNG st LB m p A n (AHEAP_k_weak k _ _ _ _ _ H) Hin;
     AI_block_bounds := fun L RNG st LB m b H Hin => AHI_block_bounds L RNG st LB m b (AHEAP_k_weak k _ _ _ _ _ H) Hin;
     AI_blocks_disjoint := fun L RNG st LB m b1 b2 H H1 H2 NE => AHI_blocks_disjoint L RNG st LB m b1 b2 (AHEAP_k_weak k _ _ _ _ _ H) H1 H2 NE;
     AI_blocks_nodup := fun L RNG st LB m H => AHI_blocks_nodup L RNG st LB m (AHEAP_k_weak k _ _ _ _ _ H);
     AI_hb_ids := fun L RNG st LB m H => AHI_hb_ids L RNG st LB m (AHEAP_k_weak k _ _ _ _ _ H);
     AI_layout := fun L RNG st LB m H => AHI_layout L RNG st LB m (AHEAP_k_weak k _ _ _ _ _ H);
     AI_relro := fun L RNG st LB m H => AHI_relro L RNG st LB m (AHEAP_k_weak k _ _ _ _ _ H);
     AI_rtcells := fun L RNG st LB m H => AHI_rtcells L RNG st LB m (AHEAP_k_weak k _ _ _ _ _ H);
     AI_malloc := AHk_malloc k;
     AI_free := AHk_free k;
     AI_free_null := AHk_free_null k;
     AI_xr := fun L RNG st LB m H => AHI_xr L RNG st LB m (AHEAP_k_weak k _ _ _ _ _ H);
     AI_xr_blocks := fun L RNG st LB m p A n H Hin => AHI_xr_blocks L RNG st LB m p A n (AHEAP_k_weak k _ _ _ _ _ H) Hin |}.

(* [comment removed for export] *)
Definition AI_W : AMallocIface :=
  {| aci := aci_I;
     AHEAP := AHEAP_W;
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AHW_rng_mono;
     AI_perm := AHW_perm;
     AI_frame := AHW_frame;
     AI_block := fun L RNG st LB m p A n H Hin => AHI_block L RNG st LB m p A n (AHW_weak _ _ _ _ _ H) Hin;
     AI_block_bounds := fun L RNG st LB m b H Hin => AHI_block_bounds L RNG st LB m b (AHW_weak _ _ _ _ _ H) Hin;
     AI_blocks_disjoint := fun L RNG st LB m b1 b2 H H1 H2 NE => AHI_blocks_disjoint L RNG st LB m b1 b2 (AHW_weak _ _ _ _ _ H) H1 H2 NE;
     AI_blocks_nodup := fun L RNG st LB m H => AHI_blocks_nodup L RNG st LB m (AHW_weak _ _ _ _ _ H);
     AI_hb_ids := fun L RNG st LB m H => AHI_hb_ids L RNG st LB m (AHW_weak _ _ _ _ _ H);
     AI_layout := fun L RNG st LB m H => AHI_layout L RNG st LB m (AHW_weak _ _ _ _ _ H);
     AI_relro := fun L RNG st LB m H => AHI_relro L RNG st LB m (AHW_weak _ _ _ _ _ H);
     AI_rtcells := fun L RNG st LB m H => AHI_rtcells L RNG st LB m (AHW_weak _ _ _ _ _ H);
     AI_malloc := AHW_malloc;
     AI_free := AHW_free;
     AI_free_null := AHW_free_null;
     AI_xr := fun L RNG st LB m H => AHI_xr L RNG st LB m (AHW_weak _ _ _ _ _ H);
     AI_xr_blocks := fun L RNG st LB m p A n H Hin => AHI_xr_blocks L RNG st LB m p A n (AHW_weak _ _ _ _ _ H) Hin |}.

Lemma AI_W_E : AHEAP AI_W = AHEAP_W. Proof. reflexivity. Qed.
Lemma AI_k_E : forall k, AHEAP (AI_k k) = AHEAP_P (AFake_arep.AH (DI_of k) AQUAR ASEC_of). Proof. reflexivity. Qed.
Lemma AI_W_CI_OK : forall iv, In iv (aci AI_W) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Proof. intros iv H. exact (aci_ok1 iv H). Qed.
Lemma AI_W_DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI_W).
Proof. intros iv H. exact (drv_aci iv H). Qed.
Lemma AI_W_URI_CI : forall iv, In iv uri_img_ranges -> In iv (aci AI_W).
Proof. intros iv H. exact (uri_aci iv H). Qed.

(* [comment removed for export] *)
Lemma UDRV_lenW : (length UDRV <= 2976)%nat.
Proof. cbn. lia. Qed.
Lemma UDRV_len4 : (length UDRV <= 4096)%nat.
Proof. cbn. lia. Qed.
Lemma UDRV_tracesW : Forall (fun u => (length u <= 254)%nat) UDRV.
Proof. unfold UDRV. repeat constructor. Qed.

Theorem aheap_init_W : aheap_init_stmt AI_W ATsafeMain.A0.
Proof.
  intros en inp w V m ms mo HV HI HM HA. cbn [AHEAP AI_W]. unfold AHEAP_W.
  split.
  { change (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) with (ainit (a_space_beg0 V) (a_ptr_array0 V)).
    apply afresh_init. }
  exists 0. split.
  { change (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) with (ainit (a_space_beg0 V) (a_ptr_array0 V)).
    rewrite dk_ainit. lia. }
  assert (H0 : AHEAP_P AHI (LDRV V w) (RNG0 ATsafeMain.A0 V mo) (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m).
  { unfold AHI, LDRV.
    apply (aheapP_at_main ATsafeMain.A0 ATsafeMain.A0_init ATsafeMain.A0_ash UDRV UDRV_len4 UDRV_tracesW ASEC_of en inp w V m ms mo HV HI HM HA).
    pose proof HM as (_ & _ & PIN & HMF & HPF & _ & _ & _ & SH0 & _). apply Forall_app in HMF as [HMF _]. apply Forall_app in HPF as [HPF _].
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
    { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    apply (ASEC_of_init V w UDRV m HMF HPF); first [exact HAT | exact SH0 | unfold AUMAX; cbn; lia]. }
  destruct H0 as (ALO & ARNG & [X [AR BL]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK]. exists X. split; [| exact BL].
  apply AREP_k_strong; [exact AR|].
  pose proof HM as (_ & _ & PIN & HMF & HPF & _). apply Forall_app in HMF as [HMF HMW]. apply Forall_app in HPF as [HPF _].
  assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
  { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
  unfold LDRV. exact (adepotk_init V w UDRV m HMF HMW HPF UDRV_len4 UDRV_tracesW HAT UDRV_lenW).
Qed.
End CANSEC1.

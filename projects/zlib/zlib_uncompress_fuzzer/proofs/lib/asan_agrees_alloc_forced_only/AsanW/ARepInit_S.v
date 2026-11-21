(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import MainExport MainFactsAsan MainEntry PrimaryShadow0.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg ABase ABytes ALayout ARep ARepFrame AHeapP APoisonR_iface ASec ARepInit_kit ARepInit_A ARepInit_D.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
  Hypothesis SH0 : ashadow0 V m.
  Let L := mkALayout (LV V) w U.

  Lemma premap_cells_init : premap_cells m.
  Proof.
    unfold premap_cells.
    aimg V m HM 0xcfe10 [C8 (Z_to_bv 64 0x1680e0)] I1.
    mf V m HM (MCell (ZLit 1474784) 8 (ZLit 4096)) F1.
    mf V m HM (MCell (ZLit 1483256) 8 (ZLit 0)) F2.
    mf V m HM (MCell (ZLit 1483328) 8 (ZLit 1103823372544)) F3.
    assert (F3' : rw_cells asegs m 1483328 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F3.
    mf V m HM (MCell (ZLit 1483352) 8 (ZLit 72339073309605888)) F4.
    assert (F4' : rw_cells asegs m 1483352 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F4.
    mf V m HM (MCell (ZLit 6798008) 8 (ZLit 4096)) F6.
    split; [exact I1|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3'|]. split; [exact F4'|]. split; [apply premap_canary_any| exact F6].
  Qed.

  Lemma asec_inst_init : asec_inst L m.
  Proof.
    unfold asec_inst.
    mf V m HM (MCell (ZLit 872488) 8 (ZMul (ZLit 4096) (ZV 226))) F1.
    aimg V m HM 0xd5058 [C1 (Z_to_bv 8 0)] I2.
    aimg V m HM 0xd5060 [CB 32 (repeat (Z_to_bv 8 0) 32)] I3.
    aimg V m HM 0xd5080 [CB 512 (repeat (Z_to_bv 8 0) 512)] I4.
    mf V m HM (MZeroC (ZLit 873089) 3) F5.
    assert (F5' : rw_cells asegs m 873089 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F5.
    aimg V m HM 0xd5298 [CB 16 (repeat (Z_to_bv 8 0) 16)] I6.
    split; [exact F1|]. split; [exists (Z_to_bv 8 0); exact I2|]. split; [exists (repeat (Z_to_bv 8 0) 32); exact I3|].
    split; [exists (repeat (Z_to_bv 8 0) 512); exact I4|]. split; [exact F5'|]. exists (repeat (Z_to_bv 8 0) 16); exact I6.
  Qed.

  Lemma asec_arr_init : asec_arr L (ST0 V) [] m.
  Proof.
    pose proof (ao_ptr _ (alayout_ok_init V w U HP HU HAT)) as (_ & P1 & P2). atop_facts. change (mkALayout (LV V) w U) with L in P1, P2.
    exists []. split; [apply Permutation_refl|]. cbn [map a_nsec a_nres ST0 ainit].
    split; [apply u64arr_nil; lia|]. split; [| intros i ch Hi; destruct i; discriminate].
    exists []. rewrite Z.add_0_r. change (Z.to_nat (8 * (0 - 0))) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  Lemma asec_wf_init : asec_wf L (ST0 V) [].
  Proof.
    unfold asec_wf. split; [exact (alayout_ok_init V w U HP HU HAT)|]. cbn. split; [reflexivity|]. split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|].
    split; [constructor| exact sec_disjoint_nil].
  Qed.

  Lemma aprim0_init : aprim0 L m.
  Proof.
    unfold aprim0. destruct (primary_shadow0 V m SH0 HP) as [Z0 W0]. rewrite (sb_eq' V w U HU) in Z0, W0. change (mkALayout (LV V) w U) with L in Z0, W0.
    unfold K_REGION. rewrite ARepFrame.shlen_div. change (2 ^ 32 / 8) with 536870912. change (2^34) with 17179869184 in Z0, W0.
    split; [intros i Hi; apply Z0; lia|].
    destruct W0 as (W1 & W2 & W3). split; [exact W1|]. split; [lia|]. intros i Hi. apply W3. lia.
  Qed.

  Lemma ashz_init : ashz L [] m.
  Proof.
    intros x Hx HF _. pose proof SH0 as SZ. unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.
    pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 6 0 255) P6.
    unfold astartup_hulls in HF. cbv [al_V L LV Nat.eqb] in HF.
    unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HF. cbv [al_V L LV Nat.eqb] in HF.
    repeat lazymatch type of HF with
           | Forall _ (_ :: _) => let H1 := fresh "NH" in pose proof (Forall_inv HF) as H1; cbn [fst snd] in H1; apply Forall_inv_tail in HF
           | _ => clear HF
           end.
    assert (SX : shad x = ASHOFF + x / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity). unfold ASHOFF in SX.
    destruct (Z.lt_ge_cases x (32768 * V 0%nat + 4096 * V 10%nat - 8388608)) as [LOW|WIN].
    - apply SZ.
      + unfold ashadow. rewrite SX. clear -Hx HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
      + intros (bn & Hin & Hr). rewrite SX in Hr. unfold ASHOFF in Hr. unfold asan_vis_app in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [<- | Hin];
          [ cbn [fst snd zv] in Hr;
            first [ match reverse goal with NHk : ~ _ |- _ => solve [clear -Hr NHk P208 P209 P0 P10 Hx LOW; Z.div_mod_to_equations; lia] end
                  | solve [clear -Hr P208 P209 P0 P10 Hx LOW; Z.div_mod_to_equations; lia]
                  | match goal with NHk : ~ _ |- _ => solve [clear -Hr NHk P208 P209 P0 P10 Hx LOW; Z.div_mod_to_equations; lia] end ]
          | try (match reverse goal with NHk : ~ _ |- _ => clear NHk end) ]).
        exact Hin.
    - mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
      rewrite SX.
      replace (2147450880 + x / 8) with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (x / 8 - 4096 * V 0%nat - 512 * V 10%nat + 1048576))
        by (clear; lia).
      apply ZW. clear -Hx WIN HAT P0 P6 P10. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  Theorem ASECc_init : ASECc [] L (ST0 V) X0 m.
  Proof.
    split; [exact asec_wf_init|]. split; [exact asec_arr_init|]. split; [exact asec_inst_init|]. split; [exact aprim0_init| exact ashz_init].
  Qed.

  Lemma sec_chunks_of_ST0 : sec_chunks_of (ST0 V) = [].
  Proof. unfold sec_chunks_of, achunks, ST0, ainit. cbn. rewrite ?map_to_list_empty. reflexivity. Qed.

  Theorem ASEC_of_init : ASEC_of L (ST0 V) X0 m.
  Proof. unfold ASEC_of. rewrite sec_chunks_of_ST0. exact ASECc_init. Qed.
End S.
End CANSEC1.

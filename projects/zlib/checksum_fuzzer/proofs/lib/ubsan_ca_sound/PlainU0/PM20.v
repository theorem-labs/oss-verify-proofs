(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM21.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM06.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM07.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RF_free_B.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM01. Import MM01. Import MM01.F_free_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM21. Import PM21.RF_get_meta.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
  conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof.
  intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
  destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.

Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except C m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rmrep st' m'.

Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
  let mr := get_meta_rec st g in
  let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g ->
  s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
  0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
  Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
  m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
               (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x50250) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16254) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  clearbody gw.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  unfold RNEED_LOCKS in *. atop_facts.
  step. step. rewrite !sx32_wz_sxv by lia.
  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
  step. if_true.
  st1.
  step. if_cases K2; zify_cond K2.
  { exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
  clear K2.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
  pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
  step. if_cases K3; zify_cond K3.
  { exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
  clear K3 RSUM.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
  rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
  step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
  clear K4 RL.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep st' mX) end.
  { unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    rewrite HG in MM.
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
    - reflexivity.
    - cbn. tauto. }
  clear MUg MM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
    pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMs end.
  step. step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply rfree_fp_stack. lia.
      - intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
  finish.
Qed.

Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g ->
  0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
  Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
  (m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists x2 x3 x4 x5 x6 x7,
       ms' = MS (mkR (Z_to_bv 64 0x162c4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
                     (Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1642c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
               (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x50250) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16254) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
  replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  clearbody gw.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
  pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
  pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
  unfold RNEED_LOCKS in *. atop_facts.
  step. step. rewrite !sx32_wz_sxv by lia.
  step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
  rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
  step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
  rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
  rewrite (Z.land_comm _ (sxv (2 ^ idx))).
  rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
  step. if_true. st1.
  step. if_cases K2; zify_cond K2.
  -
    st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
    st1. st1.
    apply evt_done. do 6 eexists. reflexivity.
  -
    step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
    rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
    rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
    pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
    step. if_cases K3; zify_cond K3.
    + st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
      st1. st1.
      apply evt_done. do 6 eexists. reflexivity.
    + exfalso. destruct HNT as [Hz|Hall].
      * apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
      * apply K3. rewrite ?wz_unsigned by apply sxv_range.
        apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
        unfold bit, mask_upto in Hall. exact Hall.
Qed.
End CANSEC1.
End RF_free_B.

Module RF_ntf_A.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM06. Import MM06. Import MM06.F_ntf_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
  [CB 48 junk; C8 CAN; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

End CANSEC1.
Ltac rmeta_open cq MUq WMq :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
    pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMq end.

Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; ftauto]);
    clear MUq WMq CH end.

Ltac rmeta_chunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
  rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section CANSEC2.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rntf_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (raw s0o s1o s2o s3o : word) st st' (lo : Z),
  rmrep st' m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  munch ((bv_unsigned sp - 96, bv_unsigned sp) :: W) m0 m -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 m ->
  ivs_covered (rfree_fp st lo (bv_unsigned sp)) W ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st' a2 a1)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x167d4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RSSP_GUARD, rntf_frame in *. atop_facts. subst s1.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WMs.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
  finish.
Qed.

Lemma rntf_aor : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (i lo : Z),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g ->
  a1 = wz (sxv (2 ^ i)) -> 0 <= i < 32 ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  0 <= m_freed (get_meta_rec st g) < 2^32 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (aor_st st g i) (wz 0) (wz 0))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x167ac) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
  destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
  assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
  unfold NSLOTS in *. atop_facts.
  assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
  set (mr := get_meta_rec st g) in *.
  pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
  { apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
  subst a1.
  st1. rewrite sx32_wz_sxv by lia. st1.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  st1. if_false.
  amo_step AMO.
  st1. if_false.
  st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep (aor_st st g i) mX) end.
  { unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
      rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
      split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
    - reflexivity.
    - cbn. ftauto. }
  clear MUg MM.
  st1. st1.
  eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | atop_facts; lia | lia | exact MU | exact WM |].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed.

Lemma rntf_frame_remerge : forall m A (j0 : list byte) (z1 z2 z3 z4 z5 : word) rest,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A (CB 8 j0 :: C8 z1 :: C8 z2 :: C8 z3 :: C8 z4 :: C8 z5 :: rest) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A (CB 48 (j0 ++ le8 z1 ++ le8 z2 ++ le8 z3 ++ le8 z4 ++ le8 z5) :: rest).
Proof.
  intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
  eapply rw_cells_congr; [| | | exact H].
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
  - reflexivity.
  - split; [| destruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.

Lemma rntf_fm : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (lo : Z),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a2 a1)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16710) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  unfold RCTX, rntf_frame in *. atop_facts.
  rmeta_chunk MR MSL CH.
  pose proof MR as (_ & (C1 & _) & _). unfold rctx_head_cells, rsecw, RCTX in C1.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRf : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  clear MUs.
  rmeta_open (conc st g) MUg WMg.
  st1. st1.
  st1. st1.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
    assert (CH' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
      by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; ftauto]);
    clear CH; rename CH' into CH
  end end.
  st1. st1.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
    assert (CH' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
      by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; ftauto]);
    clear CH; rename CH' into CH
  end end.
  rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
  set (st0 := put_meta g meta0 st) in MR0.
  assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).
  rmeta_chunk MR0 MSL0 CH0.
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  clear CH0 K1 K2.
  st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
  -
    destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
    pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
    unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR0 MSL0 CH.
    st1.
    rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
    set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
    assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
    assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
    rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
    unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1.
    clear CHh.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH.
    st1.
    rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
    assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
    munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
    st1. clear CH.
    rmeta_open (conc st head) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
    assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
    { unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
      rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
      rewrite get_meta_rec_put_same.
      rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
      reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
    eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | atop_facts; lia | lia | exact MU | exact WM |].
    cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
    + eapply rfree_fp_meta; [exact MR | exact MSh | lia].
    + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
    + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
    + apply rfree_fp_ctx. unfold RCTX. lia.
  -
    unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR0 MSL0 CH.
    st1. st1.
    rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.
    clear C1. pose proof MRb as (_ & (C1 & _) & _). unfold rctx_head_cells, rsecw, RCTX in C1. rewrite FMH in C1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
    unfold RCTX in MUc.
    st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
    { eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
    { unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
    eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | atop_facts; lia | lia | exact MU | exact WM |].
    cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
    + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
    + apply rfree_fp_ctx. unfold RCTX. lia.
Qed.
End CANSEC2.
End RF_ntf_A.

Module RF_ntf_C.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM06. Import MM06. Import MM06.F_ntf_C.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import RF_ntf_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; ftauto]);
    clear MUq WMq CH end.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a0 a2 a3 a5 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x167ac) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -96)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof.
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

Lemma rntf_qpath : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g -> 0 <= sc < 48 ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  (active st sc <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
  qa_facts st sc g ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rqpath_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc lo st g m (qpath_st st sc g) fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (Z_to_bv 64 sc) a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16590) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  unfold RCTX in *. atop_facts.
  st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
  st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
  replace (Z_to_bv 64 (327816 + sc * 8 + 80)) with (wa (327816 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
  st1. clear RDA.
  st1. if_cases K; zify_cond K.
  {
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
    unfold qpath_st. rewrite HA, optr_eqb_refl.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
  assert (HA : active st sc <> Some g).
  { intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
  destruct (GNP HA) as [GN GP].
  assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
  { unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
    replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
  rewrite QS. clear QS K.
  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  clear CH.
  st1. destruct (active st sc) as [hd|] eqn:HD.
  -
    destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
    assert (NEh : hd <> g) by congruence.
    pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
    set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
    assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).
    rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1. clear CHh.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
    assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
    st1. clear CH. st1.
    rmeta_open (conc st hd) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
    assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
      rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
      unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
  -
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (327816, 327816 + 928)]%Z m) as MU.
    st1.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.
    pose proof MRb as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ (actives stB) sc (Z_to_bv 64 (327816 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
        by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
      pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
    end.
    assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3 SOK.
    pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
      pose proof (length_le8 (pw stB (Some g))) as L8;
      apply (rw_cells_frame (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
      apply (stk_write (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
      apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
      apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa A) bs) in WM;
      lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
        apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa A) bs) in HI;
        [| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
      end;
      remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
    end.
    apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.
End CANSEC1.
End RF_ntf_C.

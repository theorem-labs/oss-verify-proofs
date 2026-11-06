(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_lkitB Od_bodyB Od_beginB Od_top_defsB
  Od_proB Od_splitintoB Od_setup_defsB Od_setupkB Od_setupw1B Od_setupw2B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section PhaseACalls.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis SPL : splitinto_cps0A RT.
Hypothesis EMPS : empls_cpsA RT.

Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma LIB_agree' : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Lemma aevt_splitinto :
  forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (RV FD D : Z) (d : list Z) (jv : list byte) (lo : Z),
  a0 = Z_to_bv 64 RV -> a1 = Z_to_bv 64 FD -> tp = Z_to_bv 64 0x656e70 ->
  bytes_at bsegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> zlength d < 2^26 -> 0 <= D ->
  ((exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + zlength d <= p + k) \/ (d = [] /\ D < SEGTOP_A)) ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  fobj RT Σ m RV 24 -> rw_cells bsegs m RV [CB 24 jv] ->
  bv_unsigned sp <= FD -> FD + 24 <= USTACK_TOP -> FD mod 8 = 0 ->
  rw_cells bsegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength d))] ->
  Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX -> 1 + vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX2)%nat ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_SPLITINTO_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  (forall (Σ' : rts RT) (A' : Z) v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(RV, RV + 24); (FD, FD + 16)] m m' ->
     vrepA m' RV A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (map (pview D) (poffs d)) ->
     rw_cells bsegs m' FD [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0)] ->
     vliveA (rt_live RT Σ') A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (rt_live RT Σ) ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - 1 - vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ' ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ATPA_SPLITINTO) fc None m (seg_rom bsegs)).
Proof using FDO MST SPL.
  intros until lo. intros E0 E1 ETP PB LBYT LL D0 INLV LPOS FOBJ0 VJ UFD FDT FD8 FDC LVB CRB FRB ART0 MI0 ST0 LOW LOR SPT SPA F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (SPL Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RV FD D d jv lo
             FDO MST E0 E1 ETP PB LBYT LL D0 INLV LPOS FOBJ0 VJ UFD FDT FD8 FDC LVB CRB FRB ART0 MI0 ST0 LOW LOR SPT SPA F0).
  - intros c (Σ' & A' & HQ & E2 & E3 & E4 & E5). eexists Σ', _. split; [exact HQ|].
    intros ms' (v & m' & RS & RA & PR & VR & FDC') F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'.
    exact (HK Σ' A' v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR VR FDC' E2 E3 E4 E5).
Qed.

Lemma aevt_empls :
  forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V A cap size : Z) (els : list (Z * Z)) (L0 : list (Z * Z)) (lo : Z),
  a0 = Z_to_bv 64 V -> tp = Z_to_bv 64 0x656e70 ->
  vrepA m V A cap size els -> vliveA (rt_live RT Σ) A cap size L0 -> (forall p n, In (p, n) L0 -> 0 < n) ->
  size = cap -> size + 1 <= 2^24 -> fobj RT Σ m V 24 ->
  Z.of_nat (length L0) + 4 <= LIVE_MAX -> vcost_push cap size <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_PUSH_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  (forall (Σ' : rts RT) (A' : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' ->
     rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(V, V + 24)] m m' ->
     vrepA m' V A' (vcap_after cap size) (size + 1) (els ++ [(0, 0)]) ->
     vliveA (rt_live RT Σ') A' (vcap_after cap size) (size + 1) L0 ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - vcost_push cap size <= rt_credit RT Σ' ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (A' + 16 * (size + 1))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ATPA_EMPLS) fc None m (seg_rom bsegs)).
Proof using FDO MST EMPS.
  intros until lo. intros E0 ETP VR VL LP SC SZ FO LVB CRB ART0 MI0 ST0 LOW LOR SPT SPA F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (EMPS Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V A cap size els L0 lo
             FDO MST E0 ETP VR VL LP SC SZ FO LVB CRB ART0 MI0 ST0 LOW LOR SPT SPA F0).
  - intros c (Σ' & A' & HQ & E2 & E3 & E4 & E5). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & VR') F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'.
    exact (HK Σ' A' q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR VR' E2 E3 E4 E5).
Qed.

End PhaseACalls.

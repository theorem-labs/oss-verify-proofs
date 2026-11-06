(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Atp_h_defsA Od_hkit0A Od_deldtorA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac rt_transport_nw m m' AG side :=
  repeat match goal with
  | H : bytes_at asegs m ?A ?bs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => bytes_at_agree asegs m m' A bs X Q) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  | H : rw_cells asegs m ?A ?cs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => rw_cells_agree_nw asegs m m' A cs X Q) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  | H : ro_cells asegs m ?A ?cs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => ro_cells_agree asegs m m' A cs X Q) in H; clear Q
            | clear H ]
  | H : wr_at asegs m ?A ?n |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + n) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => wr_at_agree_nw asegs m m' A n X Q) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  | H : stk asegs m ?lo ?hi |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => lo <= x < hi) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => stk_agree_nw asegs m m' lo hi X Q) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  end.

Section BodyKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Notation aevt := (aevt RT PMc).

Lemma aevt_switch : forall (Σ Σ' : rts RT) (K : config -> Prop) ms,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> aevt Σ' K ms -> aevt Σ K ms.
Proof using.
  intros Σ Σ' K ms AL AM H T c Hc Hk. apply (H T c); [| exact Hk].
  exact (ASTA_switch RT Σ Σ' PMc _ c Hc AL AM).
Qed.

Lemma aevt_deldtor : deldtor_cps RT ->
  forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (THIS idx oc ia nidx noc nia : Z) (vptr : word) (pre8 mid rest : list byte) (lo : Z),
  a0 = Z_to_bv 64 THIS -> tp = Z_to_bv 64 0x6488f0 ->
  In (THIS, 96) (rt_live RT Σ) -> THIS mod 8 = 0 ->
  rw_cells asegs m THIS (dl_cells vptr pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 oc) (Z_to_bv 64 ia) rest) ->
  In (ia, nia) (rt_live RT Σ) -> In (oc, noc) (rt_live RT Σ) -> In (idx, nidx) (rt_live RT Σ) ->
  ia <> oc -> ia <> idx -> ia <> THIS -> oc <> idx -> oc <> THIS -> idx <> THIS -> 0 <= nia -> 0 <= noc -> 0 <= nidx ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  (forall (Σ' : rts RT) v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m' ->
     rt_live RT Σ' = live_remove THIS (live_remove idx (live_remove oc (live_remove ia (rt_live RT Σ)))) ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ' = rt_credit RT Σ ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_deldtor) fc None m (seg_rom asegs)).
Proof using FDO MST.
  intros DT. intros until lo. intros E0 ETP INT T8 TH INA INO INI N1 N2 N3 N4 N5 N6 NA0 NO0 NI0 ART0 MI0 ST0 LOW LOR SPT SPA UOK F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (DT Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              THIS idx oc ia nidx noc nia vptr pre8 mid rest lo FDO MST E0 ETP INT T8 TH INA INO INI N1 N2 N3 N4 N5 N6 NA0 NO0 NI0
              ART0 MI0 ST0 LOW LOR SPT SPA UOK F0).
  - intros c (Σ' & v & HQ & E1 & E2 & E3 & E4). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'.
    exact (HK Σ' v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR E1 E2 E3 E4).
Qed.

Lemma aevt_vdestroy : vdestroy_cpsA RT ->
  forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (C V A cap size : Z) (els : list (Z * Z)) (L0 : list (Z * Z)) (lo : Z),
  a0 = Z_to_bv 64 C -> tp = Z_to_bv 64 0x6488f0 ->
  bv_unsigned sp <= C -> C + 8 <= USTACK_TOP -> C mod 8 = 0 -> rw_cells asegs m C [C8 (Z_to_bv 64 V)] ->
  vrepA m V A cap size els -> vliveA (rt_live RT Σ) A cap size L0 -> (forall p n, In (p, n) L0 -> 0 < n) -> 1 <= cap -> fobj RT Σ m V 24 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_DESTROY_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  (forall (Σ' : rts RT) v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' -> rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(V, V + 24)] m m' ->
     rt_live RT Σ' = L0 -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ' = rt_credit RT Σ ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ATPA_DESTROY) fc None m (seg_rom asegs)).
Proof using FDO MST.
  intros VD. intros until lo. intros E0 ETP C1 C2 C3 CC VR VL LP CAP1 FO ART0 MI0 ST0 LOW LOR SPT SPA UOK F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (VD Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              C V A cap size els L0 lo FDO MST E0 ETP C1 C2 C3 CC VR VL LP CAP1 FO ART0 MI0 ST0 LOW LOR SPT SPA UOK F0).
  - intros c (Σ' & HQ & E1 & E2 & E3 & E4). eexists Σ', _. split; [exact HQ|].
    intros ms' (v & m' & RS & RA & PR) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'.
    exact (HK Σ' v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR E1 E2 E3 E4).
Qed.

Lemma aevt_delarr : del_cps RT e_delarr ->
  forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x6488f0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp -> frm0 fc ->
  (forall (Σ' : rts RT) v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_delarr) fc None m (seg_rom asegs)).
Proof using FDO MST.
  intros DL. intros until lo. intros INP E0 ETP ART0 MI0 COK UOK F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (DL Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
              FDO MST INP E0 ETP ART0 MI0 COK UOK F0).
  - intros c (Σ' & v & HQ & E1 & E2 & E3 & E4). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'.
    exact (HK Σ' v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR E1 E2 E3 E4).
Qed.

Lemma aevt_newarr : new_cps RT e_newarr_nt ->
  forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  1 <= n <= 0x20001000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x6488f0 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  (forall (Σ' : rts RT) p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at asegs m' p n -> acc asegs m' p n ->
     rt_live RT Σ' = (p, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - mcost n -> 0 < p -> p mod 16 = 0 -> p + n < USTACK_TOP ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 p) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_newarr_nt) fc None m (seg_rom asegs)).
Proof using FDO MST.
  intros NW. intros until lo. intros N E0 ETP LV CR ART0 MI0 ST0 LOW LOR SPT SPA F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (NW Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
              FDO MST N E0 ETP LV CR ART0 MI0 ST0 LOW LOR SPT SPA F0).
  - intros c (Σ' & p & HQ & E1 & E2 & E3 & E4 & P0 & P16 & PT). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & WR & AC) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'.
    exact (HK Σ' p q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR WR AC E1 E2 E3 E4 P0 P16 PT).
Qed.

End BodyKit.

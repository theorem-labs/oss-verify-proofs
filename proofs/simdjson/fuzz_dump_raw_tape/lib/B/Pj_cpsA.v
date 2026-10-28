(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_rtkA Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.

Lemma newarr_jump : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt bsegs (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc OPNEW_A m))
    (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc OPNEWARR_A m).
Proof. intros. unfold entry_st, OPNEWARR_A, OPNEW_A. zstep. apply evt_done. cbv delta [mkR]. reflexivity. Qed.

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis SM0W : stack_malloc0w_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma live_remove_head : forall Σ m p n l, ART RT Σ m -> rt_live RT Σ = (p, n) :: l -> 0 < n -> (forall q k, In (q, k) l -> 0 < k) ->
  live_remove p (rt_live RT Σ) = l.
Proof using AF.
  intros Σ m p n l ART0 EL NP LP. rewrite EL. apply live_remove_hd.
  intros [q k] Hin E. cbn [fst] in E. subst q. pose proof (LP p k Hin) as KP.
  destruct (af_live_disj RT AF Σ m p n p k [] l ART0 ltac:(rewrite EL; reflexivity) Hin); lia.
Qed.

Lemma sbchunk_grown : forall st NEW z, sbchunkA (sb_grownA st NEW z) = [(NEW, z)].
Proof. intros. reflexivity. Qed.
Lemma sbchunk_sized : forall st n, sbchunkA (sb_sized st n) = sbchunkA st.
Proof. intros. reflexivity. Qed.

Lemma SBINVA_acc : forall Σ E m st, pjenvA_ok E -> pa_live RT Σ E st -> ART RT Σ m -> SBINVA E m st -> acc bsegs m (sa_buf st) (sa_cap st).
Proof using AF.
  intros Σ E m st OK (LV & _ & _) ART0 (_ & _ & _ & _ & SH & _ & HB).
  destruct (sa_heap st) eqn:HP.
  - apply (proj2 (af_acc_live RT AF Σ m (sa_buf st) (sa_cap st) ART0 ltac:(rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity))).
  - destruct HB as (-> & -> & _). pose proof (ok_sb E OK) as (A32 & B1 & _). pose proof (ok_frame E OK) as (_ & FS & _).
    eapply (acc_sub bsegs); [apply (acc_zero_run bsegs m (pa_SB E) 11); [Z.div_mod_to_equations; lia| unfold SEGTOP_A in FS; lia| exact SH]| lia| lia].
Qed.

Lemma SBINVA_shz : forall E m st, pjenvA_ok E -> SBINVA E m st -> shz m (pa_SB E) 88.
Proof.
  intros E m st OK (_ & _ & _ & _ & SH & _). pose proof (ok_sb E OK) as (A32 & B1 & _). pose proof (ok_frame E OK) as (_ & FS & _).
  apply (shz_of_zero_run m (pa_SB E) 11); [Z.div_mod_to_equations; lia| unfold SEGTOP_A in FS; lia| exact SH].
Qed.

Lemma aevt_smalloc0w : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6abde8 ->
  fcount 0 (rt_frames RT Σ) < FRAMES_MAX0 -> Z.of_nat (length (rt_frames RT Σ)) < FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 0 - 8) -> wr_at bsegs m' (shad f) (fs_size 0 / 8) ->
     rt_frames RT Σ' = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 0 < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_stack_malloc 0)) fc None m (seg_rom bsegs)).
Proof using SM0W FDO MST.
  intros until lo. intros ETP FR3 FRL CR ART0 MI0 COK HK.
  eapply (aevt_icall RT PMc).
  - exact (SM0W Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST ETP FR3 FRL CR ART0 MI0 COK).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.

Lemma aevt_smalloc4 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6abde8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 4 - 8) -> wr_at bsegs m' (shad f) (fs_size 4 / 8) ->
     rt_frames RT Σ' = (f, 4%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 4 < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_stack_malloc 4)) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK TOPC HK.
  eapply (aevt_icall RT PMc).
  - exact (rc_stack_malloc_4 RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST ltac:(right; left; reflexivity) ETP FRL CR ART0 MI0 COK TOPC).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.

Lemma aevt_setshadow : forall Σ K v (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d n : Z) (lo : Z),
  In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at bsegs m d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall v0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' ->
     bytes_at bsegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n)) ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_set_shadow v)) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros HV E0 E1 Hn SHD WR ART0 MI0 COK HK.
  eapply (aevt_icall RT PMc).
  - exact (rc_set_shadow RT RC v HV Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d n lo FDO MST HV E0 E1 Hn SHD WR ART0 MI0 COK).
  - intros c (v0 & HQ). unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK v0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR BY).
Qed.

Lemma aevt_newarr : forall Σ K (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (usp n lo : Z),
  1 <= n <= 0x20001000 -> tp = Z_to_bv 64 0x6abde8 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  (forall (Σ' : rts RT) (p : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> wmono bsegs m m' -> stk bsegs m' lo usp ->
     rt_pres (rt_live RT Σ) (rt_frames RT Σ) usp m m' ->
     wr_at bsegs m' p n -> acc bsegs m' p n ->
     rt_live RT Σ' = (p, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - mcost n -> 0 < p -> p mod 16 = 0 -> p + n < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 p) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 OPNEWARR_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until lo. intros N ETP LV CR ART0 MI0 ST0 LOR SPT SPA SP16 HK.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (newarr_jump ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)|].
  cbv beta. intros ms <-. apply evt_done. unfold entry_st.
  exact (aevt_opnew RT AF RC PMc FDO MST Σ K ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp n lo
           N ETP LV CR ART0 MI0 ST0 LOR SPT SPA SP16 HK).
Qed.

Lemma aevt_delarr : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n lo : Z),
  In (p, n) (rt_live RT Σ) -> tp = Z_to_bv 64 0x6abde8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  (forall (Σ' : rts RT) (v : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after_f RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 OPDELARR_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until lo. intros HIN ETP ART0 MI0 COK UOK HK.
  apply (aevt_evt RT AF PMc MST).
  change OPDELARR_A with e_delarr.
  eapply evt_cut; [apply (delarr_walk ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)|].
  cbv beta. intros ms <-. apply evt_done.
  unfold aevt. eapply cps_seq.
  { exact (rc_free RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
             FDO MST HIN eq_refl ETP ART0 MI0 COK UOK). }
  intros T c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1) Hk.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & RA2 & PRES2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
  exact (HK Σ1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 RA2 PRES2 LV1 FRS1 SP1 CR1 T c2 Hc2' Hk).
Qed.

Lemma aevt_free0 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6abde8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  (forall (v : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_free) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros ETP ART0 MI0 COK UOK HK.
  eapply (aevt_icall RT PMc).
  - exact (rc_free_null RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST eq_refl ETP ART0 MI0 COK UOK).
  - intros c (v0 & HQ). unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK v0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR).
Qed.

End Kit.

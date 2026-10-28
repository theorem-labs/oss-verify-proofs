(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition NUM_LITS : list (Z * Z) := [(0x28c20, 10416); (0x2b5a0, 640)].
Definition num_lits_acc (RT : rt_sig) : Prop :=
  forall Σ m, ART RT Σ m -> Forall (fun r => acc bsegs m (fst r) (snd r)) NUM_LITS.

Section AEvt.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition aevt (Σ : rts RT) (K : config -> Prop) (ms : machine_state) : Prop :=
  cps bsegs (ASTA RT Σ PMc (eq ms)) K.

Lemma aevt_evt : forall Σ K ms, evt bsegs (fun ms' => aevt Σ K ms') ms -> aevt Σ K ms.
Proof using AF MST.
  intros Σ K ms H. unfold aevt. eapply cps_seq.
  - apply (asta_evt_c RT AF Σ PMc (eq ms) (fun ms' => aevt Σ K ms') MST). intros ms0 <-. exact H.
  - intros T c Hc Hk. destruct (ASTA_unpack RT Σ PMc _ c Hc) as (ms1 & H1 & Hc1). exact (H1 T c Hc1 Hk).
Qed.

Lemma aevt_done : forall Σ (K : config -> Prop) ms, (forall c, ASTA RT Σ PMc (eq ms) c -> K c) -> aevt Σ K ms.
Proof. intros Σ K ms H T c Hc Hk. exact (Hk c (H c Hc)). Qed.

Lemma cps_of_aevt : forall Σ ms (Q : config -> Prop), aevt Σ Q ms -> cps bsegs (ASTA RT Σ PMc (eq ms)) Q.
Proof. intros Σ ms Q H. exact H. Qed.

Lemma aevt_rt : forall Σ K ms (Q : config -> Prop),
  cps_f (ASTA RT Σ PMc (eq ms)) Q -> frm0 (ms_fcsr ms) ->
  (forall c, Q c -> exists Σ' (Pm : machine_state -> Prop), ASTA RT Σ' PMc Pm c /\ forall ms', Pm ms' -> frm0 (ms_fcsr ms') -> aevt Σ' K ms') ->
  aevt Σ K ms.
Proof.
  intros Σ K ms Q HF F0 HC. unfold aevt. eapply (cps_of_f RT Σ PMc ms Q K HF F0).
  intros T c [HQ Fc] Hk. destruct (HC c HQ) as (Σ' & Pm & HA & HP).
  destruct (ASTA_unpack_f RT Σ' PMc Pm c HA Fc) as (ms' & H1 & H2 & H3). exact (HP ms' H1 H2 T c H3 Hk).
Qed.

Lemma ret_st_inv : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms (P : machine_state -> Prop),
  ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms ->
  (forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc',
     P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  P ms.
Proof.
  intros until P. intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & ->) H. apply H.
Qed.

Lemma aevt_memset : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d n : Z) (cb : byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned cb) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst RT Σ m sp d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> frm0 fc ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' ->
     bytes_at bsegs m' d (repeat cb (Z.to_nat n)) ->
     aevt Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x7f338) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hn CD ART0 MI0 COK F0 HK.
  eapply aevt_rt; [| exact F0 |].
  - exact (rf_asan_memset RT RTF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d n cb lo FDO MST E0 E1 E2 Hd Hn CD ART0 MI0 COK).
  - intros c HQ. unfold icpt_post in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR BY).
Qed.

Lemma aevt_memcpy : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> frm0 fc ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d (Z.of_nat (length bs)) m m' ->
     bytes_at bsegs m' d bs ->
     aevt Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x7ee9c) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hs Hn SRC CS CD DJ ART0 MI0 COK F0 HK.
  eapply aevt_rt; [| exact F0 |].
  - exact (rf_asan_memcpy RT RTF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d s bs lo FDO MST E0 E1 E2 Hd Hs Hn SRC CS CD DJ ART0 MI0 COK).
  - intros c HQ. unfold icpt_post in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR BY).
Qed.

Lemma aevt_memmove : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> frm0 fc ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d (Z.of_nat (length bs)) m m' ->
     bytes_at bsegs m' d bs ->
     aevt Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x7f578) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros E0 E1 E2 Hd Hs Hn SRC CS CD ART0 MI0 COK F0 HK.
  eapply aevt_rt; [| exact F0 |].
  - exact (rf_asan_memmove RT RTF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d s bs lo FDO MST E0 E1 E2 Hd Hs Hn SRC CS CD ART0 MI0 COK).
  - intros c HQ. unfold icpt_post in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR BY).
Qed.

Lemma aevt_set_shadow : forall Σ K v (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d n : Z) (lo : Z),
  In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at bsegs m d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> frm0 fc ->
  (forall v0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' ->
     bytes_at bsegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n)) ->
     aevt Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_set_shadow v)) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros HV E0 E1 Hn SHD WR ART0 MI0 COK F0 HK.
  eapply aevt_rt; [| exact F0 |].
  - exact (rf_set_shadow RT RTF v HV Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m d n lo FDO MST HV E0 E1 Hn SHD WR ART0 MI0 COK).
  - intros c (v0 & HQ). unfold icpt_post in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & BY) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK v0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR BY).
Qed.

Lemma aevt_stack_malloc : forall Σ K (k : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  (k = 0 \/ k = 4 \/ k = 5)%nat -> tp = Z_to_bv 64 0x6abde8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) -> frm0 fc ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size k - 8) -> wr_at bsegs m' (shad f) (fs_size k / 8) ->
     rt_frames RT Σ' = (f, k) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size k < USTACK_TOP ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_stack_malloc k)) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros HKK ETP FRL CR ART0 MI0 COK TOPC F0 HK.
  assert (SM : stack_malloc_contract_f RT k).
  { destruct HKK as [->|[->| ->]]; [exact (rf_stack_malloc_0 RT RTF)| exact (rf_stack_malloc_4 RT RTF)| exact (rf_stack_malloc_5 RT RTF)]. }
  eapply aevt_rt; [| exact F0 |].
  - exact (SM Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST HKK ETP FRL CR ART0 MI0 COK TOPC).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.

Lemma aevt_stack_free5 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo : Z),
  a0 = Z_to_bv 64 f -> tp = Z_to_bv 64 0x6abde8 -> rt_frames RT Σ = (f, 5%nat) :: fr ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> frm0 fc ->
  (forall (Σ' : rts RT) (v : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) fr (bv_unsigned sp) m m' ->
     rt_frames RT Σ' = fr -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ' = rt_credit RT Σ ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x654f0) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros E0 ETP FRS ART0 MI0 COK F0 HK.
  eapply aevt_rt; [| exact F0 |].
  - exact (rf_stack_free_5 RT RTF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m f fr lo FDO MST eq_refl E0 ETP FRS ART0 MI0 COK).
  - intros c (Σ' & v & HQ & E1 & E2 & E3 & E4). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK Σ' v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RA PR E1 E2 E3 E4).
Qed.
End AEvt.

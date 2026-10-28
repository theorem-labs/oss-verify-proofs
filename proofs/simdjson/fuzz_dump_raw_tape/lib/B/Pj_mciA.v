(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PJ_MEMCMP_STUB_A : Z := 0x6a588.

Section Contract.
Variable RT : rt_sig.

Definition memcmp_inner_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> 0 < p <= 2^47 -> 0 < q <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^40 ->
  bytes_at bsegs m p bp -> bytes_at bsegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc PJ_MEMCMP_STUB_A m)))
    (fun c => exists r : word, (r = Z_to_bv 64 0 <-> bp = bq)
       /\ icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r lo 0 0 m (fun _ => True) c).
End Contract.

Section Rule.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Lemma mci_icall : forall Σ K ms (Q : config -> Prop),
  cps bsegs (ASTA RT Σ PMc (eq ms)) Q ->
  (forall c, Q c -> exists (Σ' : rts RT) (Pm : machine_state -> Prop), ASTA RT Σ' PMc Pm c /\ forall ms', Pm ms' -> aevt RT PMc Σ' K ms') ->
  aevt RT PMc Σ K ms.
Proof.
  intros Σ K ms Q HC HK. unfold aevt. eapply cps_seq; [exact HC|].
  intros T c Hc Hk. destruct (HK c Hc) as (Σ' & Pm & HA & HP).
  destruct (ASTA_unpack RT Σ' PMc Pm c HA) as (ms' & H1 & H2). exact (HP ms' H1 T c H2 Hk).
Qed.

Lemma mci_retF : forall fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms (P : machine_state -> Prop),
  ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms ->
  (forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F',
     P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  P ms.
Proof.
  intros until P. intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & ->) H. apply H.
Qed.

Hypothesis MCI : memcmp_inner_icontract RT.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma aevt_memcmpI : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> 0 < p <= 2^47 -> 0 < q <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^40 ->
  bytes_at bsegs m p bp -> bytes_at bsegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     (r = Z_to_bv 64 0 <-> bp = bq) ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PJ_MEMCMP_STUB_A) fc None m (seg_rom bsegs)).
Proof using MCI FDO MST.
  intros until lo. intros E0 E1 E2 LEN Hp Hq NZ LS BP BQ CP CQ ART0 MI0 COK HK.
  eapply mci_icall.
  - exact (MCI Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m p q bp bq lo FDO MST E0 E1 E2 LEN Hp Hq NZ LS BP BQ CP CQ ART0 MI0 COK).
  - intros c (r & HR & HQ). unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _).
    apply (mci_retF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK r q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' HR RA PR).
Qed.
End Rule.

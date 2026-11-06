(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState Mem Frame Cells Step Arr Exec ImageA RzCPS FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_fuzz : Z := 0x96ab0.

Definition LIB_FP : list (Z * Z) :=
  [(0x11c1e0, 0x11c4e0); (0x652f40, 0x652f70); (0x652fa0, 0x652fa8); (0x652fc0, 0x652fc8); (0x652fe0, 0x652fe8); (0x653000, 0x653010); (0x653020, 0x653028); (0x653040, 0x653048); (0x653060, 0x653090); (0x6530c0, 0x6530c8)].

Definition FUZZ_COST : Z := 3 * 2^31.

Definition FUZZ_LIVE : Z := 16.

Definition FUZZ_STACK : Z := 0x80000.

Section LibIface.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.

Definition fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x653c30 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)   ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ -> frm0 fc ->

  cps bsegs (fun c => ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)) c /\ frm0 (ms_fcsr (cfg_ms c)))
    (fun c => (exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ') /\ frm0 (ms_fcsr (cfg_ms c))).

End LibIface.

Lemma asta_cfrm0 : forall RT Σ PMc (Pm : machine_state -> Prop) c,
  ASTA RT Σ PMc Pm c -> (forall ms, Pm ms -> frm0 (ms_fcsr ms)) -> frm0 (ms_fcsr (cfg_ms c)).
Proof. intros RT Σ PMc Pm [ms mo] (H1 & H2 & H3 & H4) HF. exact (HF _ H2). Qed.
Lemma asta_eq_fcsr : forall RT Σ PMc ms c, ASTA RT Σ PMc (eq ms) c -> ms_fcsr (cfg_ms c) = ms_fcsr ms.
Proof. intros RT Σ PMc ms [ms0 mo] (H1 & H2 & H3 & H4). rewrite H2. reflexivity. Qed.

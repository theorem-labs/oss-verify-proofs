(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_kit D_auxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_fuzz : Z := 0xb4c70.

Definition LIB_FP : list (Z * Z) :=
  [(0x6bc060, 0x6bc090); (0x6bc0c0, 0x6bc0c8); (0x6bc120, 0x6bc128); (0x6bc140, 0x6bc148); (0x6bc160, 0x6bc170); (0x6bc180, 0x6bc188); (0x6bc1a0, 0x6bc1a8); (0x6bc1c0, 0x6bc1f0); (0x6bc220, 0x6bc228); (0x6bcc28, 0x6bdad8); (0x6de758, 0x6de75c); (0x6be310, 0x6be318); (0x6bc258, 0x6bc264); (0x6be3b8, 0x6be3c0)].

Definition FUZZ_COST : Z := 3 * 2^31.

Definition FUZZ_LIVE : Z := 16.

Definition FUZZ_STACK : Z := 0x80000.

Definition LIBC_A : Z := 0x6de678.
Definition LIBC_NL : Z := 0x6de67b.
Definition libc_nl (m : mem) : Prop := ro_cells bsegs m LIBC_NL [C1 (Z_to_bv 8 0)].
Lemma libc_nl_of_libc : forall (m : mem) (cdt thr sec : byte) (tm1 : word),
  rw_cells bsegs m LIBC_A [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] -> libc_nl m.
Proof.
  intros m cdt thr sec tm1 [[Hwf Hb] _]. unfold libc_nl, ro_cells, cells_at.
  change [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] with ([C1 cdt; C1 thr; C1 sec] ++ ([C1 (Z_to_bv 8 0)] ++ [C4 tm1])) in Hwf, Hb.
  rewrite cells_wf_app in Hwf. destruct Hwf as [W1 W23]. pose proof W23 as W23'. rewrite cells_wf_app in W23. destruct W23 as [W2 W3].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite (cells_bytes_length _ W1) in Hb.
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _].
  split; [exact W2|]. unfold LIBC_NL. unfold LIBC_A in Hb. exact Hb.
Qed.
Lemma libc_nl_agree : forall m m' : mem, libc_nl m -> agree_on (fun a => LIBC_NL <= a < LIBC_NL + 1) m m' -> libc_nl m'.
Proof.
  intros m m' H AG. unfold libc_nl in *. apply (ro_cells_agree bsegs m m' _ _ H). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.

Definition FUZZ_SP0GAP : Z := 0x1000.

Lemma auxc_outside_LIB : forall x, auxc x -> outside LIB_FP x.
Proof.
  intros x Hx. pose proof (auxc_range x Hx) as R. unfold LIB_FP. cbn. repeat (split; [lia|]). exact I.
Qed.

Section LibIface.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.

Definition fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x6be3e8 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)   ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> libc_nl m -> el_xdataA m -> el_auxvA (bv_unsigned sp) m -> rt_sp0 RT Σ <= bv_unsigned sp + FUZZ_SP0GAP ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ -> frm0 fc ->

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

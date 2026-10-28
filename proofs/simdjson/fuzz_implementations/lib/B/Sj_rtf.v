(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition cfrm0 (c : config) : Prop := frm0 (ms_fcsr (cfg_ms c)).
Definition cps_f (P Q : config -> Prop) : Prop :=
  cps bsegs (fun c => P c /\ cfrm0 c) (fun c => Q c /\ cfrm0 c).

Lemma cps_f_seq : forall P Q R, cps_f P Q -> cps_f Q R -> cps_f P R.
Proof. intros P Q R H1 H2. unfold cps_f in *. eapply cps_seq; eassumption. Qed.

Section RTFKit.
Variable RT : rt_sig.

Lemma cfrm0_of_asta : forall Σ PMc (Pm : machine_state -> Prop) c,
  ASTA RT Σ PMc Pm c -> (forall ms, Pm ms -> frm0 (ms_fcsr ms)) -> cfrm0 c.
Proof. intros Σ PMc Pm [ms mo] (H1 & H2 & H3 & H4) HF. exact (HF _ H2). Qed.

Lemma ASTA_unpack_f : forall Σ PMc (Pm : machine_state -> Prop) c, ASTA RT Σ PMc Pm c -> cfrm0 c ->
  exists ms, Pm ms /\ frm0 (ms_fcsr ms) /\ ASTA RT Σ PMc (eq ms) c.
Proof.
  intros Σ PMc Pm [ms mo] (H1 & H2 & H3 & H4) HF. exists (restrict (HID (rt_allow RT Σ) mo) ms). split; [exact H2|].
  split; [exact HF|]. split; [exact H1|]. split; [reflexivity|]. split; [exact H3| exact H4].
Qed.

Lemma cps_of_f : forall Σ PMc ms (Q K : config -> Prop),
  cps_f (ASTA RT Σ PMc (eq ms)) Q -> frm0 (ms_fcsr ms) ->
  cps bsegs (fun c => Q c /\ cfrm0 c) K -> cps bsegs (ASTA RT Σ PMc (eq ms)) K.
Proof.
  intros Σ PMc ms Q K HF F0 HK. eapply cps_seq; [| exact HK]. unfold cps_f in HF.
  eapply cps_conseq; [exact HF| | intros c Hc; exact Hc].
  intros c Hc. split; [exact Hc|]. apply (cfrm0_of_asta Σ PMc (eq ms) c Hc). intros ms0 <-. exact F0.
Qed.

Lemma cps_f_of_post : forall Σ Σ' PMc ms (Pm : machine_state -> Prop),
  (frm0 (ms_fcsr ms) -> cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ' PMc Pm)) -> (forall ms', Pm ms' -> frm0 (ms_fcsr ms')) ->
  cps_f (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ' PMc Pm).
Proof.
  intros Σ Σ' PMc ms Pm H HF. unfold cps_f. intros T c [Hc Fc] Hk.
  assert (F0 : frm0 (ms_fcsr ms)).
  { destruct c as [ms0 mo]. destruct Hc as (_ & E & _). rewrite E. exact Fc. }
  apply (H F0 T c Hc). intros c' Hc'. apply Hk. split; [exact Hc'|]. exact (cfrm0_of_asta Σ' PMc Pm c' Hc' HF).
Qed.

Definition malloc_contract_f : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x20001000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x6be3e8 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Definition free_contract_f : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x6be3e8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Definition free_null_contract_f : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x6be3e8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Definition memcpy_icontract_f (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at bsegs m' d bs)).

Definition memset_icontract_f (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst RT Σ m sp d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
               (fun m' => bytes_at bsegs m' d (repeat c (Z.to_nat n)))).

Definition memmove_icontract_f : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src RT Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m sp d (Z.of_nat (length bs)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memmove m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at bsegs m' d bs)).

Definition memcmp_icontract_f : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> 0 < p <= 2^47 -> 0 < q <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^20 ->
  bytes_at bsegs m p bp -> bytes_at bsegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)))
    (fun c => exists r : word, (r = Z_to_bv 64 0 <-> bp = bq)
       /\ icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r lo 0 0 m (fun _ => True) c).

Definition stack_malloc_contract_f (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 4 \/ k = 5)%nat -> tp = Z_to_bv 64 0x6be3e8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' f (fs_size k - 8) /\ wr_at bsegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

Definition stack_free_contract_f (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> k = 5%nat -> a0 = Z_to_bv 64 f -> tp = Z_to_bv 64 0x6be3e8 ->
  rt_frames RT Σ = (f, k) :: fr ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stack_free_5 m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) fr (bv_unsigned sp) m m') c
       /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Definition set_shadow_contract_f (v : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at bsegs m d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_set_shadow v) m)))
    (fun c => exists v0, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
               (fun m' => bytes_at bsegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

Record rt_contracts_f : Prop := mkRTCF {
  rf_malloc : malloc_contract_f;
  rf_free : free_contract_f;
  rf_free_null : free_null_contract_f;
  rf_asan_memcpy : memcpy_icontract_f e_asan_memcpy;
  rf_asan_memset : memset_icontract_f e_asan_memset;
  rf_asan_memmove : memmove_icontract_f;
  rf_memcmp : memcmp_icontract_f;

  rf_stack_malloc_4 : stack_malloc_contract_f 4;
  rf_stack_malloc_5 : stack_malloc_contract_f 5;
  rf_stack_free_5 : stack_free_contract_f 5;
  rf_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract_f v
}.

End RTFKit.

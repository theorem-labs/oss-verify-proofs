(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_letf2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fixunstfsi_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_floatsitf_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_floatunsitf_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_extenddftf2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fe_getround_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_addtf3_A_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_addtf3_E_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_subtf3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_multf3_tail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_multf3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_frexpl_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_signbitl_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fpclassifyl_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memset_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memcpy_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fwritex_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition rsegs := Ubsan.Ubsan_loaded_segments.
Ltac norm_rsegs :=
  cbv delta [F_letf2_u5.rsegs F_fixunstfsi_u5.rsegs F_floatsitf_u5.rsegs F_floatunsitf_u5.rsegs F_extenddftf2_u5.rsegs F_fe_getround_u5.rsegs
             F_multf3_core_u5.rsegs F_divtf3_u5.rsegs F_signbitl_u5.rsegs F_fpclassifyl_u5.rsegs F_memset_u5.rsegs F_memcpy_u5.rsegs] in *;
  fold rsegs in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope Z_scope.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.

Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof.
  intros. unfold mk128, canon. pose proof (lo64_range x). pose proof (hi64_range x).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_disjoint_add; [lia|].
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + replace (Z.testbit (lo64 x) i) with false; [apply Bool.andb_false_r|].
      symmetry. destruct (Z.eq_dec (lo64 x) 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof.
  intros x Hx. unfold canon, lo64, hi64, wrap64, ONES64. rewrite !land_W64, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (x / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. intros. unfold canon. pose proof (lo64_range x). pose proof (hi64_range x). lia. Qed.

Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. intros. unfold f128_mul. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. intros. unfold f128_div. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. intros. unfold f128_sub. rewrite !lo64_canon, !hi64_canon. apply f128_add_canon_l. Qed.
Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. intros. unfold f128_le. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. intros. unfold fixunstfsi_a0. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. intros. apply unsigned_lit. apply lo64_range. Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. intros. apply unsigned_lit. apply hi64_range. Qed.

Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition leaf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

(* [comment removed for export] *)
Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma letf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
  mem_inv rsegs m ->
  evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6300) fc None m (seg_rom rsegs)).
Proof.
  intros until Y. intros MI. eapply evt_mono. { eapply letf2_spec. exact MI. }
  intros ms' P. unfold letf2_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_le_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma letf2_callv0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv rsegs m ->
  evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6300) fc None m (seg_rom rsegs)).
Proof. intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 0)) at 1. change (Z_to_bv 64 0) with (Z_to_bv 64 (hi64 0)) at 1. apply letf2_callv. assumption. Qed.

Lemma fixunstfsi_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv rsegs m ->
  evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb74a4) fc None m (seg_rom rsegs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply fixunstfsi_spec. exact MI. }
  intros ms' P. unfold fixunstfsi_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fixunstfsi_a0_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma floatsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
  mem_inv rsegs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
  evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6b84) fc None m (seg_rom rsegs)).
Proof.
  intros until i. intros MI Hv Hi. eapply evt_mono. { eapply floatsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hi. }
  intros ms' P. exact P.
Qed.
(* [comment removed for export] *)
Lemma floatsitf_callp : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv rsegs m -> (0 <= i < 2^31)%Z ->
  evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6b84) fc None m (seg_rom rsegs)).
Proof. intros until i. intros MI Hi. apply floatsitf_callv; [exact MI | lia |]. rewrite sext32_small by lia. reflexivity. Qed.

Lemma floatunsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
  mem_inv rsegs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
  evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7538) fc None m (seg_rom rsegs)).
Proof.
  intros until u. intros MI Hv Hu. eapply evt_mono. { eapply floatunsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hu. }
  intros ms' P. exact P.
Qed.

(* [comment removed for export] *)
Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.
Lemma floatunsitf_callfix : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
  mem_inv rsegs m ->
  evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7538) fc None m (seg_rom rsegs)).
Proof.
  intros until Y. intros MI. apply floatunsitf_callv; [exact MI | |].
  - unfold fixunstfsi_a0. apply sext32_range.
  - unfold f128_to_u32, M32. rewrite sext32_landM32. unfold fixunstfsi_a0. symmetry. apply sext32_idem.
Qed.

(* [comment removed for export] *)
Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
  mem_inv rsegs m -> (0 <= D < 2^64)%Z ->
  evt rsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 0xb604c) fc None m (seg_rom rsegs)).
Proof.
  intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
  intros ms' P. unfold extenddftf2_post in P. rewrite freg_get_same, unsigned_lit in P by lia. exact P.
Qed.

(* [comment removed for export] *)
Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - K, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - K) q.

Lemma multf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk rsegs m (q - 80) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
  evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6484) fc None m (seg_rom rsegs)).
Proof.
  intros until Y. intros ST MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (multf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
  intros ms' P. unfold multf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_mul_canon in P. exact P.
Qed.

Lemma divtf3_callq : divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk rsegs m (q - 112) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
  evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb76cc) fc None m (seg_rom rsegs)).
Proof.
  intros DS. intros until Y. intros ST MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (DS ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
  intros ms' P. unfold divtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_div_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition calla_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch [(q - 48, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc'
    /\ stk rsegs m' (q - 48) q.

Lemma addtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6c9c) fc None m (seg_rom rsegs)).
Proof.
  intros until Y. intros ST MI FRM Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (addtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
  intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_add_canon in P. exact P.
Qed.

Lemma subtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6c8c) fc None m (seg_rom rsegs)).
Proof.
  intros until Y. intros ST MI FRM Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (subtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
  intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_sub_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Definition frexpl_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E : Z) (rest : list cell) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - 32) q
    /\ rw_cells rsegs m' P (C4 (Z_to_bv 64 e') :: rest)
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Lemma frexpl_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
  stk rsegs m (q - 32) q -> mem_inv rsegs m ->
  rw_cells rsegs m P (C4 (Z_to_bv 64 E) :: rest) ->
  (P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
  evt rsegs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6228) fc None m (seg_rom rsegs)).
Proof.
  intros until rest. intros ST MI CE SEP Hq HP PRE.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ep : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  pose proof (rw_cells_bound _ _ _ _ CE) as BR. cbn [cells_size csize] in BR.
  apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in CE. destruct CE as [CE CR]. cbn [cells_size csize Nat.add] in CR.
  change (Z.of_nat 4) with 4%Z in CR.
  eapply evt_mono.
  { eapply (frexpl_spec ra (Z_to_bv 64 q)); rewrite ?Eq, ?Ep, ?ulit_lo64, ?ulit_hi64; eauto; try lia.
    cbv zeta. change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X). rewrite hi64_canon.
    unfold F128_ZERO in *. rewrite <- (f128_le_canon X 0) in PRE. replace (canon 0) with 0%Z in PRE by reflexivity. exact PRE. }
  intros ms' Q. unfold frexpl_post in Q. rewrite !Eq, !Ep, !ulit_lo64, !ulit_hi64 in Q.
  destruct Q as (x' & e' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & CE' & HF).
  unfold frexpl_postq. exists x', e'. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact HF].
  apply (proj2 (rw_cells_app rsegs _ _ [_] _)). split; [exact CE'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4%Z.
  eapply rw_cells_transport; [exact CR | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia|]. split; [lia|exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma signbitl_canon : forall x, signbitl (canon x) = signbitl x.
Proof. intros. unfold signbitl. rewrite hi64_canon. reflexivity. Qed.
Lemma fpclassifyl_canon : forall x, fpclassifyl (canon x) = fpclassifyl x.
Proof. intros. unfold fpclassifyl. rewrite lo64_canon, hi64_canon. reflexivity. Qed.

Definition signbitl_postv (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma signbitl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv rsegs m ->
  evt rsegs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb61dc) fc None m (seg_rom rsegs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply signbitl_spec. exact MI. }
  intros ms' P. unfold signbitl_post, signbitl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite signbitl_canon in P. exact P.
Qed.

Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.
Lemma fpclassifyl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv rsegs m ->
  evt rsegs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb61e4) fc None m (seg_rom rsegs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply fpclassifyl_spec. exact MI. }
  intros ms' P. unfold fpclassifyl_post, fpclassifyl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fpclassifyl_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma lo64_flip_sign : forall x, lo64 (Z.lxor x F128_SIGNBIT) = lo64 x.
Proof.
  intros. unfold lo64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
  change 0x80000000000000000000000000000000%Z with (2^127)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 127 i); [lia|]. now rewrite Bool.xorb_false_r.
  - rewrite Z.ones_spec_high by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma hi64_flip_sign : forall x, hi64 (Z.lxor x F128_SIGNBIT) = Z.lxor (hi64 x) 9223372036854775808.
Proof.
  intros. unfold hi64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
  change 0x80000000000000000000000000000000%Z with (2^127)%Z. change 9223372036854775808%Z with (2^63)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !Z.land_spec, !Z.shiftr_spec, Z.lxor_spec, !Z.pow2_bits_eqb by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite !Bool.andb_true_r.
    destruct (Z.eqb_spec 127 (i + 64)), (Z.eqb_spec 63 i); try lia; reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite !Bool.andb_false_r. destruct (Z.eqb_spec 63 i); [lia|reflexivity].
Qed.

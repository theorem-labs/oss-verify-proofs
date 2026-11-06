(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_letf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fixunstfsi.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_floatsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_subtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_multf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_divtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require FmtFp_facts2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_signbitl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fpclassifyl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
Module F_fmt_fp_calls.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fixunstfsi OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_floatunsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_subtf3.F_fe_getround OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_subtf3.F_addtf3_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_subtf3.F_addtf3_E OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_subtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_multf3.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_signbitl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fpclassifyl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Ltac norm_rsegs := idtac.

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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

(* [comment removed for export] *)
Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma letf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
  mem_inv bsegs m ->
  evt bsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8ff1c) fc None m (seg_rom bsegs)).
Proof.
  intros until Y. intros MI. eapply evt_mono. { eapply letf2_spec. exact MI. }
  intros ms' P. unfold letf2_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
  rewrite f128_le_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma letf2_callv0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv bsegs m ->
  evt bsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8ff1c) fc None m (seg_rom bsegs)).
Proof. intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 0)) at 1. change (Z_to_bv 64 0) with (Z_to_bv 64 (hi64 0)) at 1. apply letf2_callv. assumption. Qed.

Lemma fixunstfsi_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv bsegs m ->
  evt bsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9669c) fc None m (seg_rom bsegs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply fixunstfsi_spec. exact MI. }
  intros ms' P. unfold fixunstfsi_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fixunstfsi_a0_canon in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma floatsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
  mem_inv bsegs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
  evt bsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x911e4) fc None m (seg_rom bsegs)).
Proof.
  intros until i. intros MI Hv Hi. eapply evt_mono. { eapply floatsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hi. }
  intros ms' P. exact P.
Qed.
(* [comment removed for export] *)
Lemma floatsitf_callp : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv bsegs m -> (0 <= i < 2^31)%Z ->
  evt bsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x911e4) fc None m (seg_rom bsegs)).
Proof. intros until i. intros MI Hi. apply floatsitf_callv; [exact MI | lia |]. rewrite sext32_small by lia. reflexivity. Qed.

Lemma floatunsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
  mem_inv bsegs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
  evt bsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96730) fc None m (seg_rom bsegs)).
Proof.
  intros until u. intros MI Hv Hu. eapply evt_mono. { eapply floatunsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hu. }
  intros ms' P. exact P.
Qed.

(* [comment removed for export] *)
Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.
Lemma floatunsitf_callfix : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
  mem_inv bsegs m ->
  evt bsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96730) fc None m (seg_rom bsegs)).
Proof.
  intros until Y. intros MI. apply floatunsitf_callv; [exact MI | |].
  - unfold fixunstfsi_a0. apply sext32_range.
  - unfold f128_to_u32, M32. rewrite sext32_landM32. unfold fixunstfsi_a0. symmetry. apply sext32_idem.
Qed.

(* [comment removed for export] *)
Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
  mem_inv bsegs m -> (0 <= D < 2^64)%Z ->
  evt bsegs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 0x86e14) fc None m (seg_rom bsegs)).
Proof.
  intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
  intros ms' P. unfold extenddftf2_post in P. rewrite freg_get_same, unsigned_lit in P by lia. exact P.
Qed.

(* [comment removed for export] *)
Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - K, q)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (q - K) q.

Lemma multf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk bsegs m (q - 80) q -> mem_inv bsegs m -> (4096 <= q < 2^64)%Z ->
  evt bsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x900a0) fc None m (seg_rom bsegs)).
Proof.
  intros until Y. intros ST MI Hq.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (multf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
  intros ms' P. unfold multf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_mul_canon in P. exact P.
Qed.

Lemma divtf3_callq : divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk bsegs m (q - 112) q -> mem_inv bsegs m -> (4096 <= q < 2^64)%Z ->
  evt bsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x912ec) fc None m (seg_rom bsegs)).
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
             F (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ munch [(q - 48, q)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ frm0 fc'
    /\ stk bsegs m' (q - 48) q.

Lemma addtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
  stk bsegs m (q - 48) q -> mem_inv bsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt bsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x909cc) fc None m (seg_rom bsegs)).
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
  stk bsegs m (q - 48) q -> mem_inv bsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
  evt bsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x911d4) fc None m (seg_rom bsegs)).
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (q - 32) q
    /\ rw_cells bsegs m' P (C4 (Z_to_bv 64 e') :: rest)
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Lemma frexpl_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
  stk bsegs m (q - 32) q -> mem_inv bsegs m ->
  rw_cells bsegs m P (C4 (Z_to_bv 64 E) :: rest) ->
  (P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
  evt bsegs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8fe44) fc None m (seg_rom bsegs)).
Proof.
  intros until rest. intros ST MI CE SEP Hq HP PRE.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ep : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  pose proof (rw_cells_bound _ _ _ _ CE) as BR. cbn [cells_size csize] in BR.
  apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in CE. destruct CE as [CE CR]. cbn [cells_size csize Nat.add] in CR.
  change (Z.of_nat 4) with 4%Z in CR.
  eapply evt_mono.
  { eapply (frexpl_spec ra (Z_to_bv 64 q)); rewrite ?Eq, ?Ep, ?ulit_lo64, ?ulit_hi64; eauto; try lia.
    cbv zeta. change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X). rewrite hi64_canon.
    unfold F128_ZERO in *. rewrite <- (f128_le_canon X 0) in PRE. replace (canon 0) with 0%Z in PRE by reflexivity. exact PRE. }
  intros ms' Q. unfold frexpl_post in Q. rewrite !Eq, !Ep, !ulit_lo64, !ulit_hi64 in Q.
  destruct Q as (x' & e' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & CE' & HF).
  unfold frexpl_postq. exists x', e'. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact HF].
  apply (proj2 (rw_cells_app bsegs _ _ [_] _)). split; [exact CE'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4%Z.
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
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.
Lemma signbitl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv bsegs m ->
  evt bsegs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96694) fc None m (seg_rom bsegs)).
Proof.
  intros until X. intros MI. eapply evt_mono. { eapply signbitl_spec. exact MI. }
  intros ms' P. unfold signbitl_post, signbitl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
  change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite signbitl_canon in P. exact P.
Qed.

Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.
Lemma fpclassifyl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv bsegs m ->
  evt bsegs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x90988) fc None m (seg_rom bsegs)).
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


End CeilWrap.
(* [comment removed for export] *)
Ltac norm_rsegs := idtac.
End F_fmt_fp_calls.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.FmtFp_facts2.F_frexpl.
Import F_fmt_fp_calls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AFREXPL_T : Z := 0x42518.
Definition AFREXPL_ICPT : Z := 0x444d4.
Definition FREXPL_ICPT_DEPTH : Z := 2176.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sh_zero_read8 : forall m lo hi w,
  sh_zero m lo hi -> 0 <= lo -> hi <= 2^47 ->
  lo <= 8 * (w - SHADOW_OFFSET) -> 8 * (w + 8 - SHADOW_OFFSET) <= hi ->
  ov_read_bytes bsegs m (wa w) 8 = Some (zeros 8).
Proof.
  intros m lo hi w SZ Hlo Hhi H1 H2.
  assert (BA : bytes_at bsegs m w (zeros 8)).
  { apply bytes_at_pointwise; [unfold SHADOW_OFFSET in *; lia| cbn; unfold SHADOW_OFFSET in *; lia|].
    intros i b Hb. unfold zeros in Hb.
    assert (Hi : (i < 8)%nat).
    { destruct (Nat.lt_ge_cases i 8) as [Hc|Hc]; [exact Hc|]. exfalso.
      rewrite (proj2 (nth_error_None _ _)) in Hb; [discriminate| rewrite repeat_length; exact Hc]. }
    rewrite nth_error_repeat in Hb by exact Hi. injection Hb as <-.
    pose proof (SZ (8 * (w + Z.of_nat i - SHADOW_OFFSET)) ltac:(lia)) as S. unfold shb, SH in S.
    replace (SHADOW_OFFSET + 8 * (w + Z.of_nat i - SHADOW_OFFSET) / 8) with (w + Z.of_nat i) in S by (Z.div_mod_to_equations; lia).
    exact S. }
  replace w with (w + 0) by lia.
  rewrite (bytes_at_read bsegs m w (zeros 8) 0 8 BA ltac:(lia) ltac:(unfold zeros; rewrite repeat_length; lia)).
  reflexivity.
Qed.

Definition frexpl_icpt_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E : Z) (rest : list cell) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 2176, q); (P, P + 4)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ rw_cells bsegs m' P (C4 (Z_to_bv 64 e') :: rest)
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Local Ltac ulia := unfold SHADOW_OFFSET, alloc_ceiling, sp_window_lo, stack_max_size; Z.div_mod_to_equations; lia.

Section FrexplIcpt.
  Variables (rae gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (q P X E lo : Z) (rest : list cell).
  Hypothesis SEP : (P + 4 + Z.of_nat (cells_size rest) <= lo \/ q <= P)%Z.
  Hypothesis PRE : Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis SPB : (lo + FREXPL_ICPT_DEPTH <= q)%Z.
  Hypothesis QHI : (q < 2^64)%Z.
  Hypothesis PLO : (alloc_ceiling + 128 <= P)%Z.
  Hypothesis PHI : (P + 132 <= 2^47)%Z.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (frexpl_icpt_postq rae q gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 F fc P (canon X) E rest lo m).

  Definition afr_frame (mm : word -> option byte) : Prop :=
    mem_inv bsegs mm /\ MRT mm /\ stk bsegs mm lo (q + -2144)
    /\ rw_cells bsegs mm (q + -64) [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ rw_cells bsegs mm P (C4 (Z_to_bv 64 E) :: rest)
    /\ munch [(q - 2176, q); (P, P + 4)]%Z m mm /\ wmono bsegs m mm
    /\ stk bsegs mm (q + -2144) (q + -64).

  (* [comment removed for export] *)
  Lemma afr_body : forall x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x22 x28 x29 x30 x31,
    afr_frame m1 ->
    evt bsegs POST
      (MS (mkR rae (Z_to_bv 64 (q + -2144)) gp tp x5 x6 x7 (Z_to_bv 64 q) x9 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P)
               x13 x14 x15 x16 x17 x18 x19 s4e s5e x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x44500) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until x31. intros (MI' & MR' & ST' & FR' & PE' & MU' & WM' & ST2).
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold FREXPL_ICPT_DEPTH in SPB.
    pose proof PLO as PLO'. unfold alloc_ceiling, sp_window_lo, stack_max_size in PLO'.
    pose proof (rw_cells_bound _ _ _ _ PE') as BR. cbn [cells_size csize] in BR.
    pose proof (MRT_icpt _ MR') as IC2.
    zstep. zstep. zstep.
    pose proof (munch_refl [(q - 2144 - 16, q - 2144)]%Z m1) as MU1.
    zstep. callq try_init_ok; [exact IC2| exact MI'| exact ST'| exact CEIL| lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with MUc : munch _ m1 mm2 |- _ =>
        assert (MR2 : MRT mm2)
          by (eapply MRT_munch; [exact MR'| exact MUc|]; apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]);
        clear MUc
      end end.
    match goal with H : stk bsegs _ lo _ |- _ => rename H into ST3 end.
    pose proof (MRT_icpt _ MR2) as IC3. pose proof IC3 as IC4. icpt_split IC4.
    zstep. sh_if_false.
    zstep. zstep. zstep. fold_lits. zstep. if_cases Kov; zify_cond Kov. { exfalso. revert Kov. lia. }
    (* [comment removed for export] *)
    do 8 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    zstep. zstep. rewrite !land_m8 by lia.
    pose proof (proj1 (MRT_ssz _ MR2)) as SZ.   (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      assert (W1 : ov_read_bytes bsegs mm2 (wa ((2147450880 + P / 8) / 8 * 8)) 8 = Some (zeros 8));
      [ apply (sh_zero_read8 mm2 alloc_ceiling (2^47)); [exact SZ| ulia | ulia | ulia | ulia] |];
      assert (W2 : ov_read_bytes bsegs mm2 (wa ((2147450880 + (P + 3) / 8) / 8 * 8)) 8 = Some (zeros 8));
      [ apply (sh_zero_read8 mm2 alloc_ceiling (2^47)); [exact SZ| ulia | ulia | ulia | ulia] |]
    end.
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. }
    (* [comment removed for export] *)
    destruct (MRT_icpt2 _ MR2) as [RFX RSN].
    do 5 zstep.
    destruct (stk_split bsegs _ lo (q + -2144 - 32) (q + -2144) ST3 ltac:(lia)) as [STlo STf]. clear ST3.
    zstep. call frexpl_callq; [exact STf| | exact PE'| lia| lia| lia| exact PRE|]. { assumption. }
    match goal with X : stk bsegs _ (q + -2144 - 32) _ |- _ =>
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge bsegs mm _ _ _ STlo X ltac:(lia)) as ST4 end;
      clear STlo X end.
    (* [comment removed for export] *)
    do 11 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with FR3 : rw_cells bsegs mm (q + -64) _ |- _ =>
      lazymatch goal with STm : stk bsegs mm (q + -2144) (q + -64) |- _ =>
        pose proof (stk_merge bsegs mm _ _ _ ST4 STm ltac:(lia)) as ST5;
        release_frame FR3 ST5 q
      end end end.
    apply evt_done. unfold frexpl_icpt_postq.
    lazymatch goal with HF : frexpl _ _ _ = Some (?x', ?e') |- _ => exists x', e' end.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End FrexplIcpt.

Lemma frexpl_icpt_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell) (lo : Z),
  stk bsegs m lo q -> mem_inv bsegs m ->
  rw_cells bsegs m P (C4 (Z_to_bv 64 E) :: rest) ->
  (P + 4 + Z.of_nat (cells_size rest) <= lo \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling <= lo)%Z -> (lo + FREXPL_ICPT_DEPTH <= q)%Z ->
  (alloc_ceiling + 128 <= P)%Z -> (P + 132 <= 2^47)%Z ->
  evt bsegs (frexpl_icpt_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREXPL_T) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST MI PE SEP Hq HP PRE MR CEIL SPB PLO PHI.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof SPB as SPB'. unfold FREXPL_ICPT_DEPTH in SPB'.
  pose proof (munch_refl [(q - 2176, q); (P, P + 4)]%Z m) as MU.
  pose proof (munch_refl [(lo, q)]%Z m) as MUs.
  pose proof (wmono_refl bsegs m) as WM.
  unfold AFREXPL_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 11 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (MR1 : MRT m0)
      by (eapply MRT_munch; [exact MR| exact MUs|]; apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]);
    destruct (stk_split bsegs m0 lo (q + -2144) (q + -64) ST ltac:(lia)) as [ST1 ST2]
  end.
  clear MUs.
  eapply afr_body; try eassumption; try lia.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); eassumption.
Qed.


End CeilWrap.

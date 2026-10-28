(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Arr Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import FmtFp_split FmtFp_splitR.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_divtf3_main F_fmt_fp_lib F_fmt_fp_calls F_fmt_fp_pre.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ROUND0 : Z := f128_div (f128_of_i32 2) K_LDBL_EPSILON.
Definition ROUND1 : Z := f128_add ROUND0 (f128_of_i32 2).
Lemma ROUND0_val : ROUND0 = 85652128978390516560239067446814703616%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma ROUND1_val : ROUND1 = 85652128978390516560239067446814703617%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma rup_half : forall prefix pl R, (R = ROUND0 \/ R = ROUND1) ->
  f128_le (f128_add (fst (ffp_flip prefix pl R (f128_of_d D_0_5))) (snd (ffp_flip prefix pl R (f128_of_d D_0_5))))
          (fst (ffp_flip prefix pl R (f128_of_d D_0_5))) = 0%Z.
Proof.
  intros prefix pl R HR. unfold ffp_flip.
  destruct (negb (pl =? 0)%Z && (znth PREFIX_STR prefix =? CHR_minus)%Z); cbn [fst snd];
    destruct HR as [-> | ->]; rewrite ?ROUND0_val, ?ROUND1_val; vm_compute; reflexivity.
Qed.
Lemma ffp_small_x0 : forall z d i, (2 <= i)%Z -> ffp_small z d i 0 = f128_of_d D_0_5.
Proof. intros z d i Hi. unfold ffp_small. rewrite (proj2 (Z.ltb_lt 0 (Z.quot i 2))); [reflexivity|]. apply Z.quot_str_pos; lia. Qed.

Lemma divtf3_callk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q X : Z),
  stk usegs m (q - 112) q -> mem_inv usegs m -> (4096 <= q < 2^64)%Z ->
  evt usegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X K_LDBL_EPSILON) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 4579879346059083776) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc9d6c) fc None m (seg_rom usegs)).
Proof.
  intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 K_LDBL_EPSILON)).
  change (Z_to_bv 64 4579879346059083776) with (Z_to_bv 64 (hi64 K_LDBL_EPSILON)).
  apply (divtf3_callq divtf3_spec); assumption.
Qed.

Lemma unsigned_b8 : forall z, bv_unsigned (Z_to_bv 8 z) = (z mod 256)%Z.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Inductive zboxed : Z -> Z -> Prop := ZBoxed : forall a : Z, zboxed a a.
Lemma zboxed_intro : forall b : Z, exists a, zboxed a b.
Proof. intros b. exists b. constructor. Qed.
Lemma zboxed_eq : forall a b, zboxed a b -> a = b.
Proof. intros a b H. destruct H. reflexivity. Qed.

Lemma divuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
  v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
  intros v i Hv Hi. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite !Z.mod_small by lia. destruct (Z.eqb_spec i 0); [lia|].
  f_equal. rewrite swrap32_eq. pose proof (Z.div_pos v i ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound v i v ltac:(lia) ltac:(nia)). mlia.
Qed.

Lemma fmt_fp_cnt_res9 : forall k v n e i' e',
  fmt_fp_cnt k v (10 ^ n, e)%Z = Some (i', e') -> (1 <= n <= 9)%Z -> (0 <= v < 1000000000)%Z -> (e <= e' <= e + 9 - n)%Z.
Proof.
  induction k as [|k IH]; intros v n e i' e' H Hn Hv; [discriminate H|].
  rewrite fmt_fp_cnt_step in H. destruct (Z.leb_spec0 (10 ^ n) v).
  - assert (n <= 8)%Z.
    { destruct (Z.le_gt_cases n 8); [assumption|]. replace n with 9%Z in l by lia. change (10^9)%Z with 1000000000%Z in l. lia. }
    cbn [fmt_fp_cnt_body] in H.
    replace (10 ^ n * 10)%Z with (10 ^ (n + 1))%Z in H by (rewrite Z.pow_add_r by lia; change (10^1)%Z with 10%Z; lia).
    apply IH in H; lia.
  - injection H as <- <-. lia.
Qed.

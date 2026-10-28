(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition fpclassifyl_entry := 0x153f30%Z.

Definition fpclassifyl_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Lemma fpc_exp_field : forall h, (0 <= h < 2^64)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 1) 18446744073709551615) 49 = Z.land (Z.shiftr h 48) 32767.
Proof.
  intros h Hh. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec, Z.shiftr_spec by lia.
  change 18446744073709551615%Z with (Z.ones 64). change 32767%Z with (Z.ones 15).
  destruct (Z.lt_ge_cases i 15).
  - rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 15) by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma fpc_mant_field : forall h, (0 <= h < 2^64)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 16) 18446744073709551615) 16 = Z.land h 281474976710655.
Proof.
  intros h Hh. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
  change 18446744073709551615%Z with (Z.ones 64). change 281474976710655%Z with (Z.ones 48).
  destruct (Z.lt_ge_cases i 48).
  - rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 48) by lia. now rewrite !Bool.andb_false_r.
Qed.

Lemma fpclassifyl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv bsegs m ->
  evt bsegs (fpclassifyl_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
               (fpclassifyl (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153f30) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM. pose_word_ranges.
  unfold fpclassifyl. rewrite hi64_words, lo64_words by lia. cbv zeta. rewrite ?b2z_Zb2z.
  rewrite (Z.lor_comm (bv_unsigned a0)).
  do 3 zstep. zstep. rewrite ?fpc_exp_field by lia. name_reg 12%Z e.
  zstep. zstep. rewrite ?fpc_mant_field by lia. name_reg 11%Z mant.
  zstep. if_cases Ki; zify_cond Ki; decide_tests_b.
  -   zstep. zstep. rewrite (ltb1_eqb0 (Z.lor mant (bv_unsigned a0))) by zrange_nonneg.
    destruct (Z.lor mant (bv_unsigned a0) =? 0)%Z; cbn [negb Z.b2z]; zstep; sf_finish.
  - zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
    +   zstep. zstep. sf_finish.
    +   zstep. zstep. rewrite (ltb1_eqb0 (Z.lor mant (bv_unsigned a0))) by zrange_nonneg.
      zstep. destruct (Z.lor mant (bv_unsigned a0) =? 0)%Z; cbn [negb Z.b2z Z.lxor];
        [change (Z.lxor 1 3) with 2%Z | change (Z.lxor 0 3) with 3%Z]; zstep; sf_finish.
Qed.

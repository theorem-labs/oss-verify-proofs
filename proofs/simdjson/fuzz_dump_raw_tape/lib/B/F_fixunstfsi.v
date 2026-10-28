(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import ImageA.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition fixunstfsi_entry := 0x15aee0%Z.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma fixunstfsi_a0_split : forall a_lo a_hi,
  (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
  fixunstfsi_a0 (a_lo + 2^64 * a_hi) = sext32 (fixunstfsi_a2 a_hi a_lo).
Proof. intros. unfold fixunstfsi_a0. rewrite lo64_words, hi64_words by assumption. reflexivity. Qed.

Definition fixunstfsi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma fixunstfsi_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv bsegs m ->
  evt bsegs (fixunstfsi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (fixunstfsi_a0 (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15aee0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose_word_ranges.
  rewrite fixunstfsi_a0_split by lia.
  unfold fixunstfsi_a2.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
  do 2 zstep. if_cases K1; zify_cond K1.
  -
    decide_tests_b. rewrite (sext32_small 0) by lia. zstep. zstep. finish.
  - do 3 zstep. name_reg 13%Z e.
    assert (He15 : (0 <= e < 2^(64-49))%Z)
      by (apply shiftr_bound; [change (inr64 (Z.land (Z.shiftl (bv_unsigned a1) 1) 18446744073709551615)); zrange| lia]).
    do 2 zstep. if_cases K2; zify_cond K2.
    +
      decide_tests_b. rewrite (sext32_small 0) by lia. zstep. zstep. finish.
    + do 5 zstep. if_cases K3; zify_cond K3; decide_tests_b.
      *
        assert (He : (16383 <= e <= 16414)%Z) by (clear -K2 K3 He15; revert K3; zb_masks; intros K3; mlia).
        clear K2 K3.

        rewrite (land_W64_small (16495 - e)) by lia. rewrite (sext32_small (16495 - e)) by lia.
        rewrite (zext32_small (16495 - e)) by lia. rewrite (land_W64_small (16495 - e - 64)) by lia.
        rewrite (shiftr63_small (16495 - e - 64)) by lia. cbn [Z.eqb negb].
        rewrite (land63_64_128 (16495 - e)) by lia.
        do 7 zstep. rewrite (swrap32_small (16495 - e)) by lia.
        do 2 zstep. rewrite (land_M32_small (16495 - e)) by lia.
        do 3 zstep. if_cases K4; zify_cond K4.
        --
          exfalso. clear -K4 He. lia.
        -- zstep. rewrite (land63_64_128 (16495 - e)) by lia.
           zstep. rewrite ?Z.add_0_r. rewrite Z_to_bv_swrap32.
           zstep. finish.
      *
        do 2 zstep.
        replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (sext32 18446744073709551615)) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
        zstep. finish.
Qed.

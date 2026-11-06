(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SumsLib AsanMaxVAK Pm9_code_94000_95000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma Zlor_lt_pow2 (ua ub n : Z) : (0 <= ua < 2 ^ n)%Z -> (0 <= ub < 2 ^ n)%Z -> (0 <= n)%Z -> (0 <= Z.lor ua ub < 2 ^ n)%Z.
Proof.
  intros Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec ua 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec ub 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (Hpos : (0 < Z.lor ua ub)%Z).
  { pose proof (Z.lor_nonneg ua ub). assert (Z.lor ua ub <> 0%Z) by (rewrite Z.lor_eq_0_iff; lia). lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor ua ub) n Hpos)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 ua n ltac:(lia)))| apply (proj1 (Z.log2_lt_pow2 ub n ltac:(lia)))]; lia.
Qed.
Lemma v_or_unsigned_t (a b : word) : bv_unsigned (v_or a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof.
  unfold v_or. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 b) as Hb.
  unfold bv_modulus in *. apply Zlor_lt_pow2; lia.
Qed.
Lemma v_srli_unsigned_t (a : word) s : (0 <= s)%Z -> bv_unsigned (v_srli a s) = Z.shiftr (bv_unsigned a) s.
Proof.
  intros Hs. unfold v_srli. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in *.
  split; [apply Z.shiftr_nonneg; lia|].
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  pose proof (Z.pow_pos_nonneg 2 s). nia.
Qed.

Lemma u_smw (s : Z) (v : word) : (0 <= s)%Z -> bv_unsigned (v_or v (v_srli v s)) = smear_step s (bv_unsigned v).
Proof. intros Hs. unfold smear_step. rewrite v_or_unsigned_t, v_srli_unsigned_t by lia. reflexivity. Qed.
Lemma smear_word (x : word) : (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
  (v_or (v_or (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) 16)) (v_srli (v_or (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) (v_srli (v_or (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) (v_srli (v_or (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) (v_srli (v_or (v_or x (v_srli x 1)) (v_srli (v_or x (v_srli x 1)) 2)) 4)) 8)) 16)) 32)) = Z_to_bv 64 (2 ^ 47 - 1).
Proof.
  intros Hx. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite (u_smw 32) by lia. rewrite (u_smw 16) by lia. rewrite (u_smw 8) by lia.
  rewrite (u_smw 4) by lia. rewrite (u_smw 2) by lia. rewrite (u_smw 1) by lia.
  change (bv_wrap 64 (2 ^ 47 - 1)) with (2 ^ 47 - 1)%Z.
  exact (smear6_eq (bv_unsigned x) Hx).
Qed.

Definition maxva_words : list (bv 32) :=
  [W_9401c; W_94020; W_94024; W_94028; W_9402c; W_94030; W_94034; W_94038; W_9403c; W_94040; W_94044; W_94048; W_9404c; W_94050; W_94054; W_94058; W_9405c; W_94060; W_94064; W_94068; W_9406c; W_94070; W_94074; W_94078; W_9407c; W_94080; W_94084; W_94088; W_9408c; W_94090; W_94094; W_94098; W_9409c; W_940a0; W_940a4; W_940a8; W_940ac; W_940b0; W_940b4; W_940b8; W_940bc; W_940c0; W_940c4; W_940c8; W_940cc].
Definition maxva_clob : list reg := [10; 11; 12; 13; 14; 15].
Section MAXVA.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 maxva_words.
  Lemma smearva_run : forall regs (x : word),
    getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' (at_ base 180) mem rom)
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
      /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
      /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
      /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
      /\ regs_agree (fun r => In r maxva_clob) regs regs'.
  Proof.
    intros regs x Hx Hr.
    pose proof HCODE as HC; cbv [code_at maxva_words] in HC.
    repeat match type of HC with context [at_ base (?a + ?b)%Z] => let c := eval vm_compute in (a + b)%Z in change (a + b)%Z with c in HC end.
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112 & C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & C156 & C160 & C164 & C168 & C172 & C176 & _).
    eexists. split.
      an C0 D_9401c.
      an C4 D_94020.
      an C8 D_94024.
      an C12 D_94028.
      an C16 D_9402c.
      an C20 D_94030.
      an C24 D_94034.
      an C28 D_94038.
      an C32 D_9403c.
      an C36 D_94040.
      an C40 D_94044.
      an C44 D_94048.
      an C48 D_9404c.
      an C52 D_94050.
      an C56 D_94054.
      an C60 D_94058.
      an C64 D_9405c.
      an C68 D_94060.
      an C72 D_94064.
      an C76 D_94068.
      an C80 D_9406c.
      an C84 D_94070.
      an C88 D_94074.
      an C92 D_94078.
      an C96 D_9407c.
      an C100 D_94080.
      an C104 D_94084.
      an C108 D_94088.
      rewrite (smear_word x Hr).
      an C112 D_9408c.
      an C116 D_94090.
      an C120 D_94094.
      an C124 D_94098.
      an C128 D_9409c.
      an C132 D_940a0.
      an C136 D_940a4.
      an C140 D_940a8.
      an C144 D_940ac.
      an C148 D_940b0.
      an C152 D_940b4.
      an C156 D_940b8.
      an C160 D_940bc.
      an C164 D_940c0.
      an C168 D_940c4.
      an C172 D_940c8.
      an C176 D_940cc.
      apply mst_refl.
    - repeat match goal with |- _ /\ _ => split end;
        [gres; apply bv_eq; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity
        | unfold maxva_clob; solve_regs_agree].
  Qed.
End MAXVA.

From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Definition asan_maxva_entry : word := 0x94064.
Lemma asan_maxva_code : code_at AsanUbsan.M.loaded_segments asan_maxva_entry 0 maxva_words.
Proof. unfold maxva_words. code_at_vm. Qed.

Theorem asan_smearva : forall mem rom regs (x : word),
  getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments (mkst regs asan_maxva_entry mem rom) (mkst regs' (at_ asan_maxva_entry 180) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
    /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
    /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
    /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
    /\ regs_agree (fun r => In r maxva_clob) regs regs'.
Proof. intros mem rom regs x Hx Hr. pose proof (smearva_run _ _ mem rom asan_maxva_code regs x Hx Hr) as R. rewrite at_0 in R. exact R. Qed.

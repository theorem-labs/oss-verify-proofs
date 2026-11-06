(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import SumsLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanMaxVAK AsanMaxVA_codeKB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec.
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
  [W_8dc20; W_8dc24; W_8dc28; W_8dc2c; W_8dc30; W_8dc34; W_8dc38; W_8dc3c; W_8dc40; W_8dc44; W_8dc48; W_8dc4c; W_8dc50; W_8dc54; W_8dc58; W_8dc5c; W_8dc60; W_8dc64; W_8dc68; W_8dc6c; W_8dc70; W_8dc74; W_8dc78; W_8dc7c; W_8dc80; W_8dc84; W_8dc88; W_8dc8c; W_8dc90; W_8dc94; W_8dc98; W_8dc9c; W_8dca0; W_8dca4; W_8dca8; W_8dcac; W_8dcb0; W_8dcb4; W_8dcb8; W_8dcbc; W_8dcc0; W_8dcc4; W_8dcc8; W_8dccc; W_8dcd0].
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
      an C0 D_8dc20.
      an C4 D_8dc24.
      an C8 D_8dc28.
      an C12 D_8dc2c.
      an C16 D_8dc30.
      an C20 D_8dc34.
      an C24 D_8dc38.
      an C28 D_8dc3c.
      an C32 D_8dc40.
      an C36 D_8dc44.
      an C40 D_8dc48.
      an C44 D_8dc4c.
      an C48 D_8dc50.
      an C52 D_8dc54.
      an C56 D_8dc58.
      an C60 D_8dc5c.
      an C64 D_8dc60.
      an C68 D_8dc64.
      an C72 D_8dc68.
      an C76 D_8dc6c.
      an C80 D_8dc70.
      an C84 D_8dc74.
      an C88 D_8dc78.
      an C92 D_8dc7c.
      an C96 D_8dc80.
      an C100 D_8dc84.
      an C104 D_8dc88.
      an C108 D_8dc8c.
      rewrite (smear_word x Hr).
      an C112 D_8dc90.
      an C116 D_8dc94.
      an C120 D_8dc98.
      an C124 D_8dc9c.
      an C128 D_8dca0.
      an C132 D_8dca4.
      an C136 D_8dca8.
      an C140 D_8dcac.
      an C144 D_8dcb0.
      an C148 D_8dcb4.
      an C152 D_8dcb8.
      an C156 D_8dcbc.
      an C160 D_8dcc0.
      an C164 D_8dcc4.
      an C168 D_8dcc8.
      an C172 D_8dccc.
      an C176 D_8dcd0.
      apply mst_refl.
    - repeat match goal with |- _ /\ _ => split end;
        [gres; apply bv_eq; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity| gres; reflexivity
        | unfold maxva_clob; solve_regs_agree].
  Qed.
End MAXVA.

From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Definition asan_maxva_entry : word := 0x8dc70.
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

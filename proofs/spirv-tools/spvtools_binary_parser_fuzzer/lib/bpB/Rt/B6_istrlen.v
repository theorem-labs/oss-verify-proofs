(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BBytes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Definition istrlen_entry := 0xcbea4%Z.

Definition istrlen_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (len : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) (Z_to_bv 64 (len + 1)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (istrlen_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc len m).

  Notation ST pc x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma istrlen_loop : forall (k : nat) (i : Z) (x12 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evt asegs POST (ST 0xcbea8 (Z_to_bv 64 i) x12).
  Proof.
    induction k as [|k IH]; intros i x12 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. do 2 zstep.
      replace (len + 1 + -1)%Z with len by lia. apply evt_done. reflexivity.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      pose proof (u8ro_read asegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      apply (IH (i + 1)%Z); lia.
  Qed.

  Lemma istrlen_body : forall x11 x12, evt asegs POST (ST istrlen_entry x11 x12).
  Proof.
    intros x11 x12. unfold istrlen_entry. zstep.
    apply (istrlen_loop (Z.to_nat len) 0); lia.
  Qed.
End Proofs.

Lemma istrlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  evt asegs (istrlen_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
               (Z.of_nat (length str)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 istrlen_entry) fc None m (seg_rom asegs)).
Proof. intros. eapply istrlen_body; eassumption. Qed.

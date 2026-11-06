(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AISTRLEN : Z := 0x65994.

Definition istrlen_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (L : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 L) (Z_to_bv 64 (L + 1)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m (seg_rom bsegs).

Section IStrlen.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (S : Z) (str slack : list byte).
  Hypothesis BY : bytes_at bsegs m S (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NZ : ~ In (Z_to_bv 8 0) str.
  Hypothesis HS : 0 <= S /\ S + Z.of_nat (length str) + 1 < 2^64.
  Let L : Z := Z.of_nat (length str).

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (istrlen_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc L m).

  Lemma str_byte : forall i, 0 <= i < L -> exists b, nth_error (str ++ Z_to_bv 8 0 :: slack) (Z.to_nat i) = Some b /\ bv_unsigned b <> 0.
  Proof.
    intros i Hi. subst L.
    destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split; [rewrite nth_error_app1 by lia; exact E|].
      intros Z0. apply NZ. apply (nth_error_In _ (Z.to_nat i)). rewrite E. f_equal. apply bv_eq. rewrite Z0. reflexivity.
    - exfalso. apply nth_error_None in E. lia.
  Qed.

  Lemma nul_byte : nth_error (str ++ Z_to_bv 8 0 :: slack) (Z.to_nat L) = Some (Z_to_bv 8 0).
  Proof. subst L. rewrite nth_error_app2 by lia. rewrite Nat2Z.id, Nat.sub_diag. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma istrlen_loop : forall (K : nat) (i : Z) (x12 : word),
    Z.to_nat (L - i) = K -> 0 <= i <= L ->
    evt bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 i) x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x65998) fc None m (seg_rom bsegs)).
  Proof using BY NZ HS.
    induction K as [K IH] using lt_wf_ind; intros i x12 HK Hi.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    destruct (Z.eq_dec i L) as [->|NE].
    - (* [comment removed for export] *)
      pose proof (u8ro_read bsegs m S (str ++ Z_to_bv 8 0 :: slack) L (Z_to_bv 8 0) _ (proj1 (proj1 (conj (conj BY I) I))) nul_byte ltac:(subst L; lia) eq_refl) as RD.
      step. step. step. step. if_cases Kz; zify_cond Kz.
      { exfalso. apply Kz. reflexivity. }
      step. step.
      apply evt_done. unfold istrlen_post. unfold zxb. subst L.
      repeat f_equal; apply bv_eq; rewrite ?unsigned_lit by lia; cbn; rewrite ?unsigned_lit by lia; try reflexivity; lia.
    - destruct (str_byte i ltac:(lia)) as (b & Hb & Hb0).
      pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
      pose proof (u8ro_read bsegs m S (str ++ Z_to_bv 8 0 :: slack) i b _ (proj1 (proj1 (conj (conj BY I) I))) Hb ltac:(lia) eq_refl) as RD.
      step. step. step. step. if_cases Kz; zify_cond Kz.
      2:{ exfalso. revert Kz. unfold zxb. rewrite ?unsigned_lit by lia. lia. }
      eapply (IH (Z.to_nat (L - (i + 1))) ltac:(lia) (i + 1)); [reflexivity| lia].
  Qed.

  Lemma istrlen_spec : forall (x11 x12 : word),
    evt bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 AISTRLEN) fc None m (seg_rom bsegs)).
  Proof using BY NZ HS.
    intros x11 x12. unfold AISTRLEN. step.
    apply (istrlen_loop (Z.to_nat (L - 0)) 0 x12 eq_refl). subst L; lia.
  Qed.
End IStrlen.


End CeilWrap.

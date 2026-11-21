(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (19 recorded proofs replaced by written proofs (sx32_lit, zx32_lit, sx16_lit and 16 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AKit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6NArith6BinNat1N3subC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx16C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC59OSSVerify5KrLib3Lib3Mem3sxbC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commc59OSSVerify5KrLib5BothW4AKit;land_ones_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z8land_0_lC56Stdlib6ZArith6BinInt1Z7mod_0_lC56Stdlib6ZArith6BinInt1Z7sub_0_rK47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib5BothW4AKitCnth_error_upd_otherC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib5Lists4List6nth_okc59OSSVerify5KrLib5BothW4AKitBnth_error_upd_hereC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW4AKit>skipn_upd_hereC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW4AKit;skipn_S_nthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv5Instr6awidth02K4ELinuxProcessSemantics5Riscv5Instr6awidth01".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma sx32_lit : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2^64) with 18446744073709551616.
  replace (Z.of_N (32 - 1)) with 31 by reflexivity. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. nia.
Qed.
Lemma zx32_lit : forall e, 0 <= e < 2^32 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e He. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx16_lit : forall e, -2^15 <= e < 2^15 -> sx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx16. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 16) with 65536. change (2^64) with 18446744073709551616.
  replace (Z.of_N (16 - 1)) with 15 by reflexivity. change (2^15) with 32768 in *.
  Z.div_mod_to_equations. nia.
Qed.
Lemma zx16_lit : forall e, 0 <= e < 2^16 -> zx16 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e He. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma zxb_lit : forall e, 0 <= e < 2^8 -> zxb (Z_to_bv 8 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold zxb. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
  change (bv_modulus 8) with 256. change (2^8) with 256 in He. clear -He. lia.
Qed.
Lemma sxb_lit : forall e, 0 <= e < 2^7 -> sxb (Z_to_bv 8 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sxb. rewrite Z_to_bv_signed, bv_swrap_small; [reflexivity|].
  change (bv_half_modulus 8) with 128. change (2^7) with 128 in He. clear -He. lia.
Qed.

Lemma zx32_small : forall w : word, bv_unsigned w < 2^32 -> zx32 w = w.
Proof.
  intros w Hw. unfold zx32. pose proof (bv_unsigned_in_range 64 w) as R.
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac lits :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_lit e) by lia
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (zx32_lit e) by lia
  | |- context [sx16 (Z_to_bv 64 ?e)] => rewrite (sx16_lit e) by lia
  | |- context [zx16 (Z_to_bv 64 ?e)] => rewrite (zx16_lit e) by lia
  | |- context [zxb (Z_to_bv 8 ?e)] => rewrite (zxb_lit e) by lia
  | |- context [sxb (Z_to_bv 8 ?e)] => rewrite (sxb_lit e) by lia
  end.
(* [comment removed for export] *)
Ltac lstep := step; lits.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma land_ones_l : forall y, 0 <= y < 2^64 -> Z.land 18446744073709551615 y = y.
Proof. intros. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_ones_r : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551615 = y.
Proof. intros. rewrite Z.land_comm. apply land_ones_l. assumption. Qed.
(* [comment removed for export] *)
Lemma sel_mask_true : forall (c : bool) x, c = true -> 0 <= x < 2^64 ->
  Z.land ((0 - Z.b2z c) mod 18446744073709551616) x = x.
Proof. intros c x -> Hx. cbn [Z.b2z]. replace ((0 - 1) mod 18446744073709551616) with 18446744073709551615 by reflexivity. apply land_ones_l. exact Hx. Qed.
Lemma sel_mask_false : forall (c : bool) x, c = false ->
  Z.land ((0 - Z.b2z c) mod 18446744073709551616) x = 0.
Proof. intros c x ->. cbn [Z.b2z]. rewrite Z.sub_0_r, Z.mod_0_l by lia. apply Z.land_0_l. Qed.

(* [comment removed for export] *)
Lemma bytes_at_read8 : forall m a (v : word),
  bytes_at bsegs m a (le8 v) -> ov_read_bytes bsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  assert (L : length (le8 v) = 8%nat) by apply length_le8.
  pose proof (bytes_at_ov_read bsegs m a (le8 v) 0 8 H ltac:(rewrite L; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal.
Qed.

Lemma bytes_at_agree : forall m m' a bs,
  bytes_at bsegs m a bs -> (forall i, a <= i < a + Z.of_nat (length bs) -> m' (wa i) = m (wa i)) ->
  bytes_at bsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & HB) HM. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd. rewrite HM by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nth_error_upd_other : forall {X} (l : list X) k i x, i <> k -> nth_error (upd l k x) i = nth_error l i.
Proof.
  induction l as [|y l IH]; intros [|k] [|i] x Hne; cbn; try reflexivity; try congruence.
  apply IH. congruence.
Qed.
Lemma nth_error_upd_here : forall {X} (l : list X) k x, (k < length l)%nat -> nth_error (upd l k x) k = Some x.
Proof. induction l as [|y l IH]; intros [|k] x Hk; cbn in *; try lia; auto. apply IH. lia. Qed.
Lemma skipn_upd_here : forall {X} (l : list X) k x, (k < length l)%nat -> skipn k (upd l k x) = x :: skipn (S k) l.
Proof. induction l as [|y l IH]; intros [|k] x Hk; cbn in *; try lia; auto. apply IH. lia. Qed.
Lemma skipn_S_nth : forall {X} (l : list X) k x, nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

(* [comment removed for export] *)
End CANSEC2.
Tactic Notation "callp" uconstr(SPEC) :=
  eapply evtF_cut;
  [ eapply SPEC
  | let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; cbv beta in PO;
    repeat (lazymatch type of PO with
            | @ex _ _ => let x := fresh "x" in destruct PO as [x PO]
            end);
    subst ms';
    try (lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
             replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
         end) ];
  try (lazymatch goal with |- rng _ _ _ => solve_rng end).

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Inductive boxed (P : Prop) : Prop := Box (p : P).
End CANSEC3.
Ltac box H := apply Box in H.
Ltac unbox H := destruct H as [H].

(* [comment removed for export] *)
Ltac fold_closed pat :=
  match goal with |- context [?e] => unify e pat; let v := eval vm_compute in e in change e with v end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma amo_alignedD_intro : forall a : Z, 0 <= a < 2^64 -> a mod 8 = 0 -> amo_aligned AD (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Lemma amo_alignedW_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

End CANSEC4.
Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_stepA AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
Ltac word_range w H := pose proof (bv_unsigned_in_range 64 w) as H; unfold bv_modulus in H; cbn in H.

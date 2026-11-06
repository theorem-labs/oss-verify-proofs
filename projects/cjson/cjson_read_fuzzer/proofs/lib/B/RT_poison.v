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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow ICPT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icpt_split IC :=
  let SB := fresh "SB" in
  destruct IC as (SB & G38 & K70 & G40 & K78 & G48 & K68 & G99 & INI & G20 & CF245 & CF251 & RMC & RMS & RSL & RMCH);
  shbase_split SB.

(* [comment removed for export] *)
Ltac is_closed_arith e :=
  lazymatch e with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac | true => idtac | false => idtac
  | Z.add ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.sub ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.mul ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.div ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.modulo ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.land ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lxor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftr ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftl ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.opp ?a => is_closed_arith a
  | Z.b2z ?a => is_closed_arith a
  | Z.ltb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.leb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.eqb ?a ?b => is_closed_arith a; is_closed_arith b
  | negb ?a => is_closed_arith a
  | andb ?a ?b => is_closed_arith a; is_closed_arith b
  | orb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.pow ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.to_nat ?a => is_closed_arith a
  | Z.of_nat ?a => is_closed_arith a
  | O => idtac | S ?a => is_closed_arith a
  | @bv_unsigned _ ?a => is_closed_arith a
  | @bv_signed _ ?a => is_closed_arith a
  | Z_to_bv _ ?a => is_closed_arith a
  | sxb ?a => is_closed_arith a
  | zxb ?a => is_closed_arith a
  end.
Ltac fold_lits :=
  cbn beta;
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
        lazymatch e with
        | Z0 => fail | Zpos _ => fail | Zneg _ => fail
        | _ => is_closed_arith e;
               let v := eval vm_compute in e in
               progress change (Z_to_bv 64 e) with (Z_to_bv 64 v)
        end
  | |- context [sxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_signed (Z_to_bv 8 z)) in
        progress change (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  | |- context [zxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_unsigned (Z_to_bv 8 z)) in
        progress change (zxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma memtoshadow_ok : memtoshadow_spec.
Proof.
  unfold memtoshadow_spec. intros until p. intros IC MI -> AR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  icpt_split IC.
  assert (R47 : 0 <= p < 2^47) by (destruct AR; unfold KHIGHMEM_BEG, KHIGHMEM_END in *; lia).
  unfold AMEMTOSHADOW.
  do 8 zstep. fold_lits.
  (if_cases K; zify_cond K).
  - (* [comment removed for export] *) zstep. zstep. zstep.
    apply evt_done. do 8 eexists. split; [| split; [exact MU| split; [exact WM| exact MI]]].
    unfold mkR. rewrite <- SH_shiftr, (Z.add_comm (Z.shiftr p 3)). reflexivity.
  - (* [comment removed for export] *)
    destruct AR as [AR|AR]; [exfalso; lia|].
    unfold KHIGHMEM_BEG, KHIGHMEM_END in AR.
    do 8 zstep. fold_lits. sh_if_true.
    do 6 zstep. fold_lits.
    sh_if_false. zstep. fold_lits. sh_if_false.
    zstep. zstep. zstep.
    apply evt_done. do 8 eexists. split; [| split; [exact MU| split; [exact WM| exact MI]]].
    unfold mkR. rewrite <- SH_shiftr, (Z.add_comm (Z.shiftr p 3)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zeros (k : nat) : list byte := repeat (Z_to_bv 8 0) k.

Lemma skipn_repeat : forall {A} (x : A) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat : forall {A} (x : A) k n, firstn k (repeat x n) = repeat x (Nat.min k n).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma zeros_read1 : forall m b N i,
  bytes_at bsegs m b (zeros N) -> 0 <= i -> i < Z.of_nat N ->
  ov_read_bytes bsegs m (wa (b + i)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m b N i H Hi HN. rewrite (bytes_at_read bsegs m b (zeros N) i 1 H Hi).
  2:{ unfold zeros. rewrite repeat_length. lia. }
  unfold zeros. f_equal.
  rewrite skipn_repeat, firstn_repeat. replace (Nat.min 1 (N - Z.to_nat i)) with 1%nat by lia. reflexivity.
Qed.

Lemma zeros_read8 : forall m b N i,
  bytes_at bsegs m b (zeros N) -> 0 <= i -> i + 8 <= Z.of_nat N ->
  ov_read_bytes bsegs m (wa (b + i)) 8 = Some (zeros 8).
Proof.
  intros m b N i H Hi HN. rewrite (bytes_at_read bsegs m b (zeros N) i 8 H Hi).
  2:{ unfold zeros. rewrite repeat_length. lia. }
  unfold zeros. f_equal.
  rewrite skipn_repeat, firstn_repeat. replace (Nat.min 8 (N - Z.to_nat i)) with 8%nat by lia. reflexivity.
Qed.

Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx.
  replace 18446744073709551608 with (Z.lxor (Z.ones 64) (Z.ones 3)) by reflexivity.
  replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 3) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 3)) by lia.
    rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 3 + 3) with i by lia.
    rewrite (Z.ones_spec_high 3 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Section MemIsZero.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (b n lo : Z) (junk : list byte).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv bsegs m1.
  Hypothesis ST : stk bsegs m1 lo (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1.
  Hypothesis WM : wmono bsegs m m1.
  Hypothesis Z0 : bytes_at bsegs m1 b (zeros (Z.to_nat n)).
  Hypothesis HN : 0 < n <= 2^40.
  Hypothesis SEP : b + n <= bv_unsigned sp - 16 \/ bv_unsigned sp <= b.
  Hypothesis SPB : lo + 16 <= bv_unsigned sp.

  Hypothesis BN : b + n + 16 <= 2^64.
  Variables end_ AB AE : Z.
  Hypothesis Hend : end_ = b + n.
  Hypothesis HAB : AB = (b + 7) / 8 * 8.
  Hypothesis HAE : AE = (b + n) / 8 * 8.

  #[warnings="-notation-for-abbreviation"] Notation POST := (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Notation ST_ pc x10 x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs)).

  Lemma b_bound : 0 <= b /\ b + n <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ Z0) as B. unfold zeros in B. rewrite repeat_length in B. lia. Qed.

  (* [comment removed for export] *)
  Lemma miz_ret : forall x10 x12 x13 x14 x15 x16,
    evt bsegs POST (ST_ 0x65e18 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16).
  Proof.
    intros. pose proof b_bound as BB. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof FR as FR'. pose proof ST as ST'.
    zstep. fold_lits. zstep. zstep. zstep.
    release_frame FR' ST' (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma miz_tail : forall (k : nat) (i : Z) x10 x13 x15 x16,
    Z.to_nat (end_ - AE - i) = k -> 0 <= i < end_ - AE -> b <= AE ->
    evt bsegs POST (ST_ 0x65e04 x10 (Z_to_bv 64 0) (Z_to_bv 64 (AE + i)) x13 (Z_to_bv 64 (end_ - AE - i)) x15 x16).
  Proof.
    induction k as [|k IH]; intros i x10 x13 x15 x16 Hk Hi HbAE; pose proof b_bound as BB; [lia|].
    pose proof (zeros_read1 m1 b (Z.to_nat n) (AE + i - b) Z0 ltac:(Z.div_mod_to_equations; lia)
                  ltac:(Z.div_mod_to_equations; lia)) as RD.
    replace (b + (AE + i - b)) with (AE + i) in RD by lia.
    zstep. zstep. zstep. fold_lits. zstep.
    zstep.
    if_cases K; zify_cond K.
    - replace (AE + i + 1) with (AE + (i + 1)) by lia.
      replace (end_ - AE - i + -1) with (end_ - AE - (i + 1)) by lia.
      apply (IH (i + 1)); lia.
    - apply miz_ret.
  Qed.

  (* [comment removed for export] *)
  Lemma miz_after_words : forall x13 x15 x16,
    evt bsegs POST (ST_ 0x65df8 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 end_) x15 x16).
  Proof.
    intros. pose proof b_bound as BB.
    zstep. if_cases K1; zify_cond K1; [apply miz_ret|].
    zstep. if_cases K2; zify_cond K2; [apply miz_ret|].
    zstep.
    replace (end_ - AE) with (end_ - AE - 0) by lia.
    replace (Z_to_bv 64 AE) with (Z_to_bv 64 (AE + 0)) by (f_equal; lia).
    apply (miz_tail (Z.to_nat (end_ - AE - 0)) 0); Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma miz_words : forall (k : nat) (j : Z) x13 x16,
    Z.to_nat ((AE - AB) / 8 - j) = k -> 0 <= j -> AB + 8 * j < AE ->
    evt bsegs POST (ST_ 0x65de8 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 end_) (Z_to_bv 64 (AB + 8 * j)) x16).
  Proof.
    induction k as [|k IH]; intros j x13 x16 Hk Hj Hlt; pose proof b_bound as BB.
    { exfalso. Z.div_mod_to_equations. lia. }
    pose proof (zeros_read8 m1 b (Z.to_nat n) (AB + 8 * j - b) Z0 ltac:(Z.div_mod_to_equations; lia)
                  ltac:(Z.div_mod_to_equations; lia)) as RD.
    replace (b + (AB + 8 * j - b)) with (AB + 8 * j) in RD by lia.
    cbn [zeros repeat] in RD.
    zstep. zstep. zstep. fold_lits. zstep.
    if_cases K; zify_cond K.
    - replace (AB + 8 * j + 8) with (AB + 8 * (j + 1)) by lia.
      apply (IH (j + 1)); Z.div_mod_to_equations; lia.
    - replace (AB + 8 * j + 8) with AE by (Z.div_mod_to_equations; lia).
      apply miz_after_words.
  Qed.

  (* [comment removed for export] *)
  Lemma miz_W0 : forall x13 x16,
    evt bsegs POST (ST_ 0x65de4 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 end_) (Z_to_bv 64 AB) x16).
  Proof.
    intros. pose proof b_bound as BB.
    zstep. if_cases K; zify_cond K; [apply miz_after_words|].
    replace (Z_to_bv 64 AB) with (Z_to_bv 64 (AB + 8 * 0)) by (f_equal; lia).
    apply (miz_words (Z.to_nat ((AE - AB) / 8 - 0)) 0); Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma miz_pro : forall (k : nat) (c : Z) x16,
    Z.to_nat (AB - c) = k -> b <= c -> c < AB -> c < end_ ->
    evt bsegs POST (ST_ 0x65dcc (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE) (Z_to_bv 64 (c + 1)) (Z_to_bv 64 end_) (Z_to_bv 64 AB) x16).
  Proof.
    induction k as [|k IH]; intros c x16 Hk Hbc HcAB Hce; pose proof b_bound as BB; [lia|].
    pose proof (zeros_read1 m1 b (Z.to_nat n) (c - b) Z0 ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as RD.
    replace (b + (c - b)) with c in RD by lia.
    zstep. zstep.
    replace (c + 1 + -1) with c by lia.
    zstep. fold_lits. zstep.
    if_cases K1; zify_cond K1; [apply miz_W0|].
    zstep. zstep.
    if_cases K2; zify_cond K2.
    - replace (c + 2) with ((c + 1) + 1) by lia.
      apply (IH (c + 1)); lia.
    - apply miz_W0.
  Qed.

  (* [comment removed for export] *)
  Lemma miz_body : forall x12 x13 x14 x15 x16,
    evt bsegs POST (ST_ 0x65d94 (Z_to_bv 64 b) (Z_to_bv 64 n) x12 x13 x14 x15 x16).
  Proof.
    intros. pose proof b_bound as BB.
    do 5 zstep. fold_lits.
    if_cases K0; zify_cond K0; [exfalso; lia|].
    do 5 zstep.
    rewrite !land_m8 by lia. rewrite <- Hend, <- HAB. replace (end_ / 8 * 8) with AE by (rewrite HAE, Hend; reflexivity).
    zstep. if_cases K1; zify_cond K1; [apply miz_W0|].
    zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep.
    apply (miz_pro (Z.to_nat (AB - b)) b); Z.div_mod_to_equations; lia.
  Qed.
End MemIsZero.

Lemma mem_is_zero_ok : mem_is_zero_spec.
Proof.
  unfold mem_is_zero_spec. intros until lo. intros MI ST SPB -> -> HN Z0 BN SEP.
  pose proof (bytes_at_bound _ _ _ _ Z0) as BB. rewrite repeat_length in BB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold AMEM_IS_ZERO.
  pose proof (conj Z0 I) as Z0'.
  carve_frame 16%nat ST.
  zstep. zstep.
  destruct Z0' as [Z1 _].
  assert (Z2 : bytes_at bsegs m0 b (zeros (Z.to_nat n))).
  { eapply bytes_at_transport; [exact Z1| exact MU|]. unfold zeros. rewrite repeat_length. cbn. lia. }
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in MU by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in SEP by lia.
  refine (miz_body ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m0 b n lo (firstn 8 junk)
            _ _ _ _ _ _ _ _ _ (b + n) ((b + 7) / 8 * 8) ((b + n) / 8 * 8) _ _ _ _ _ _ _ _);
    first [exact MI| exact ST| exact FR| exact MU| exact WM| exact Z2| exact HN| exact SPB| exact BN| reflexivity].
Qed.



End CeilWrap.
(* [comment removed for export] *)
Ltac icpt_split IC :=
  let SB := fresh "SB" in
  destruct IC as (SB & G38 & K70 & G40 & K78 & G48 & K68 & G99 & INI & G20 & CF245 & CF251 & RMC & RMS & RSL & RMCH);
  shbase_split SB.
Ltac is_closed_arith e :=
  lazymatch e with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac | true => idtac | false => idtac
  | Z.add ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.sub ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.mul ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.div ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.modulo ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.land ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.lxor ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftr ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.shiftl ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.opp ?a => is_closed_arith a
  | Z.b2z ?a => is_closed_arith a
  | Z.ltb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.leb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.eqb ?a ?b => is_closed_arith a; is_closed_arith b
  | negb ?a => is_closed_arith a
  | andb ?a ?b => is_closed_arith a; is_closed_arith b
  | orb ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.pow ?a ?b => is_closed_arith a; is_closed_arith b
  | Z.to_nat ?a => is_closed_arith a
  | Z.of_nat ?a => is_closed_arith a
  | O => idtac | S ?a => is_closed_arith a
  | @bv_unsigned _ ?a => is_closed_arith a
  | @bv_signed _ ?a => is_closed_arith a
  | Z_to_bv _ ?a => is_closed_arith a
  | sxb ?a => is_closed_arith a
  | zxb ?a => is_closed_arith a
  end.
Ltac fold_lits :=
  cbn beta;
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
        lazymatch e with
        | Z0 => fail | Zpos _ => fail | Zneg _ => fail
        | _ => is_closed_arith e;
               let v := eval vm_compute in e in
               progress change (Z_to_bv 64 e) with (Z_to_bv 64 v)
        end
  | |- context [sxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_signed (Z_to_bv 8 z)) in
        progress change (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  | |- context [zxb (Z_to_bv 8 ?z)] =>
        is_closed_arith z;
        let v := eval vm_compute in (bv_unsigned (Z_to_bv 8 z)) in
        progress change (zxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word)
  end.

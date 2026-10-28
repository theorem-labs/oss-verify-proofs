(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BSeqExec BStoreOk BAgentLib BFrame BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BLibKnowFrame BLibTail.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsPrintfFirst.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition shx (o : Z) : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit o)) (ELit 3)) (ELit 2147450880)) (ELit (-8)).
Definition shw (spz o : Z) : Z := (8 * (((spz + o) / 8 + 2147450880) / 8))%Z.

Lemma shx_denot : forall E (sp : word) o,
  ev E 0 = sp -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z -> (-65536 <= o <= 0)%Z ->
  bv_unsigned (edenot E (shx o)) = shw (bv_unsigned sp) o.
Proof.
  intros E sp o E0 Hlo Hhi Ho. unfold ASP_LO, ASP_HI in *. unfold shx, shw. cbn [edenot]. rewrite E0.
  cbn [alu64 alu].
  rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  change (3 mod 2 ^ 64)%Z with 3%Z. change (63 mod 2 ^ 64)%Z with 63%Z.
  change (Z.land 3 63) with 3%Z. change (2147450880 mod 2 ^ 64)%Z with 2147450880%Z.
  change ((-8) mod 2 ^ 64)%Z with 18446744073709551608%Z.
  replace ((bv_unsigned sp + o mod 2 ^ 64) mod 2 ^ 64)%Z with (bv_unsigned sp + o)%Z.
  2:{ rewrite Zplus_mod_idemp_r. symmetry. apply Z.mod_small. lia. }
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
  rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
  rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma shw_range : forall spz o, (ASP_LO <= spz <= ASP_HI)%Z -> (-4032 <= o <= -64)%Z ->
  (shw ASP_LO o <= shw spz o <= shw ASP_HI o)%Z
  /\ (2147450880 + (spz - 4096) / 8 <= shw spz o)%Z /\ (shw spz o + 8 <= 2147450880 + spz / 8)%Z.
Proof.

  intros spz o H Ho. unfold ASP_LO, ASP_HI in *.
  assert (M8 : forall a b, (a <= b -> a / 8 <= b / 8)%Z) by (intros; apply Z.div_le_mono; lia).
  assert (MONO : forall s1 s2, (s1 <= s2 -> shw s1 o <= shw s2 o)%Z).
  { intros s1 s2 Hs. unfold shw. pose proof (M8 (s1 + o) (s2 + o))%Z.
    pose proof (M8 ((s1 + o) / 8 + 2147450880) ((s2 + o) / 8 + 2147450880))%Z. lia. }
  split; [split; apply MONO; lia|]. unfold shw.
  set (q := ((spz + o) / 8)%Z). assert (8 * q <= spz + o < 8 * q + 8)%Z by (subst q; Z.div_mod_to_equations; lia).
  set (r := ((q + 2147450880) / 8)%Z). assert (8 * r <= q + 2147450880 < 8 * r + 8)%Z by (subst r; Z.div_mod_to_equations; lia).
  set (t := ((spz - 4096) / 8)%Z). assert (8 * t <= spz - 4096 < 8 * t + 8)%Z by (subst t; Z.div_mod_to_equations; lia).
  set (u := (spz / 8)%Z). assert (8 * u <= spz < 8 * u + 8)%Z by (subst u; Z.div_mod_to_equations; lia).
  lia.
Qed.

Fixpoint shkn (offs : list Z) : list kentry :=
  match offs with
  | [] => []
  | o :: r => KRange (shx o) (shw ASP_LO o) (shw ASP_HI o) :: KZero (SA (shx o) 0) (ELit 8) :: shkn r
  end.

Lemma shkn_ok : forall E mem (sp : word) offs,
  ev E 0 = sp -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z ->
  Forall (fun o => -4032 <= o <= -64)%Z offs ->
  (forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
             mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
  know_ok RSEGS E mem (shkn offs).
Proof.
  intros E mem sp offs E0 Hlo Hhi Hoffs Qsh0. induction offs as [|o r IH]; [constructor|].
  inversion Hoffs as [|o' r' Ho Hr]; subst o' r'.
  pose proof (shx_denot E sp o E0 Hlo Hhi ltac:(lia)) as SHX.
  pose proof (shw_range (bv_unsigned sp) o (conj Hlo Hhi) Ho) as (SR1 & SR2 & SR3).
  cbn [shkn]. constructor; [|constructor; [|apply IH; exact Hr]].
  - apply krange_intro. rewrite SHX. exact SR1.
  - eapply (kzero_intro RSEGS E mem (shx o) (edenot E (shx o)) 0 (ELit 8) 8);
      [reflexivity | reflexivity | rewrite SHX; unfold ASP_LO in *; clear - SR2 Hlo; Z.div_mod_to_equations; lia | lia
      | rewrite SHX; unfold ASP_HI in *; clear - SR3 Hhi; Z.div_mod_to_equations; lia |].
    intros i Hi. rewrite SHX. apply Qsh0. lia.
Qed.

Fixpoint outside_zb (a : Z) (w : Z) (rs : list (Z * Z)) : bool :=
  match rs with
  | [] => true
  | (lo, len) :: r => ((a + w <=? lo) || (lo + len <=? a))%Z && outside_zb a w r
  end.

Fixpoint kbytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kread RSEGS kn b k 1, kbytes kn b (k + 1) n' with
            | Some (ELit v), Some r => Some (v :: r)
            | _, _ => None
            end
  end.
Definition zbytes (vs : list Z) : list byte := map (fun v => Z_to_bv 8 v) vs.

Lemma word_to_le_bytes_1 : forall v, word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate.
Qed.

Lemma kbytes_rdn : forall E M kn b n k vs,
  know_ok RSEGS E M kn -> kbytes kn b k n = Some vs ->
  flat E (SA b k) (Z.of_nat n) -> (estart E (SA b k) + Z.of_nat n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (estart E (SA b k))) n = Some (zbytes vs).
Proof.
  intros E M kn b n. induction n as [|n IH]; intros k vs HK Hb Hf Hlt.
  - cbn in Hb. injection Hb as <-. reflexivity.
  - cbn [kbytes] in Hb. destruct (kread RSEGS kn b k 1) as [[v| | | | | | |]|] eqn:Hr; try discriminate.
    destruct (kbytes kn b (k + 1) n) as [r|] eqn:Hr2; [|discriminate]. injection Hb as <-.
    change (S n) with (1 + n)%nat. cbn [zbytes map].
    change (Z_to_bv 8 v :: map (fun v0 => Z_to_bv 8 v0) r) with ([Z_to_bv 8 v] ++ zbytes r).
    assert (Hf1 : flat E (SA b k) (Z.of_nat 1)) by (unfold flat in *; cbn [Z.of_nat] in *; lia).
    pose proof (kread_rdn RSEGS E M kn b k 1 (ELit v) HK Hr ltac:(lia) ltac:(lia) Hf1) as R1.
    assert (R1' : rdn RSEGS M (Z_to_bv 64 (estart E (SA b k))) 1 = Some [Z_to_bv 8 v]).
    { rewrite <- (flat_u E _ _ Hf1), Z_to_bv_bv_unsigned. cbn [edenot] in R1. rewrite word_to_le_bytes_1 in R1. exact R1. }
    apply rdn_app_Z; [exact R1' | | unfold flat in Hf1; lia | lia].
    assert (Hf2 : flat E (SA b (k + 1)) (Z.of_nat n)) by (unfold flat, estart in *; cbn [a_base a_off Z.of_nat] in *; lia).
    replace (estart E (SA b k) + Z.of_nat 1)%Z with (estart E (SA b (k + 1))) by (unfold estart; cbn [a_base a_off]; lia).
    apply IH; [assumption | assumption | assumption | unfold estart in *; cbn [a_base a_off] in *; lia].
Qed.

Lemma kbytes_rdn_sp : forall E M kn i (sp : word) k n vs,
  know_ok RSEGS E M kn -> ev E i = sp -> kbytes kn (EVar i) k n = Some vs ->
  (0 <= bv_unsigned sp + k)%Z -> (bv_unsigned sp + k + Z.of_nat n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp + k)) n = Some (zbytes vs).
Proof.
  intros E M kn i sp k n vs HK Ei Hb H0 H1.
  assert (ES : estart E (SA (EVar i) k) = (bv_unsigned sp + k)%Z) by (unfold estart; cbn [a_base a_off edenot]; rewrite Ei; reflexivity).
  rewrite <- ES. apply (kbytes_rdn E M kn (EVar i) n k vs HK Hb); [unfold flat; rewrite ES; lia | rewrite ES; lia].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

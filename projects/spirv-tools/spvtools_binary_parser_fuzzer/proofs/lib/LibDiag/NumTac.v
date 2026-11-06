(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff ZStores SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumMemsetLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac DiagPins.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac kdjx H1 H2 b1 l1 b2 l2 :=
  eapply (kdisj_ok _ _ _ _ _ _ _ b1 l1 b2 l2);
  [ evs; first [exact H1 | reflexivity] | evs; reflexivity | evs; first [exact H2 | reflexivity] | evs; reflexivity
  | lia | lia | lia | lia | cbn [a_off] ].

Lemma stores_in_join : forall (W1 W2 W : Z -> Prop) M M1 M2,
  stores_in W1 M M1 -> stores_in W2 M1 M2 -> (forall a, W1 a -> W a) -> (forall a, W2 a -> W a) -> stores_in W M M2.
Proof.
  intros W1 W2 W M M1 M2 S1 S2 H1 H2. apply (stores_in_trans W M M1 M2).
  - eapply stores_in_weaken; [exact S1 | exact H1].
  - eapply stores_in_weaken; [exact S2 | exact H2].
Qed.

Lemma fld_via_stores : forall segs W M M' a (n : nat) v,
  stores_in W M M' -> (forall x, a <= x < a + Z.of_nat n -> ~ W x) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  CRep.fld segs M a n v -> CRep.fld segs M' a n v.
Proof.
  intros segs W M M' a n v ST HW H0 H1 HF. eapply CRep.fld_agree; [lia | lia | exact HF |].
  eapply stores_in_agree; [exact ST|]. intros x Hx. split; [unfold zwin in Hx; lia | apply HW; unfold zwin in Hx; lia].
Qed.

Lemma ro_clear_stores : forall L W M M',
  LibEff.ro_clear L M -> stores_in W M M' -> (forall a, W a -> ~ in_ranges (ly_img L) a) -> LibEff.ro_clear L M'.
Proof.
  intros L W M M' ROC [A D] HW w Hro. rewrite (A w); [exact (ROC w Hro)|]. intros Hw. exact (HW _ Hw (proj1 Hro)).
Qed.

Ltac kwz HF Hreg :=
  lazymatch type of Hreg with
  | _ = Z_to_bv 64 ?b =>
    eapply (kword_var _ _ _ _ b);
    [ cw_fix HF
    | cbn; lia
    | evs; first [exact Hreg | reflexivity]
    | lia | lia | cbn; lia
    | evs; cbn [nth]; regsub; znorm; rewrite ?Z.mod_small by lia; rewrite ?u64_of_Z by lia;
      first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned | f_equal; lia | apply Z_to_bv_eqm; mlia] ]
  end.

Tactic Notation "kept_chain9" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) constr(H8) constr(H9) :=
  lazymatch goal with |- getr _ ?rr = _ =>
    khop H1 rr; try khop H2 rr; try khop H3 rr; try khop H4 rr; try khop H5 rr; try khop H6 rr; try khop H7 rr; try khop H8 rr; try khop H9 rr; kept_close end.
Tactic Notation "kept_chain11" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) constr(H8) constr(H9) constr(H10) constr(H11) :=
  lazymatch goal with |- getr _ ?rr = _ =>
    khop H1 rr; try khop H2 rr; try khop H3 rr; try khop H4 rr; try khop H5 rr; try khop H6 rr; try khop H7 rr; try khop H8 rr; try khop H9 rr; try khop H10 rr; try khop H11 rr; kept_close end.

Ltac srs_ok :=
  apply regs_ok_srs; [apply regs_ok_seed|]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (split; [ let E0 := fresh in intros E0; discriminate E0
          | evs; regsub; znorm; rewrite ?Z.mod_small by lia;
            first [reflexivity | assumption | f_equal; lia | apply Z_to_bv_eqm; mlia] ]).

Lemma fld_zero_of_repeat : forall segs M p (N : nat) d (n : nat),
  0 <= p -> p + Z.of_nat N < 2 ^ 64 -> 0 <= d -> d + Z.of_nat n <= Z.of_nat N -> (n = 8 \/ n = 4 \/ n = 1)%nat ->
  CRep.fld segs (wbytes M (Z_to_bv 64 p) (repeat (SumMemsetLib.cbyte (Z_to_bv 64 0)) N)) (p + d) n 0.
Proof.
  intros segs M p N d n Hp HN Hd Hdn Hn. unfold CRep.fld. rewrite (StrLib.rdn_repeat_sub segs M _ p N d n) by lia.
  destruct Hn as [-> | [-> | ->]]; (first [reflexivity | f_equal; apply DiagPins.byte_list_eq; vm_compute; reflexivity]).
Qed.

Lemma stores_in_shrink : forall (W W' : Z -> Prop) M M',
  stores_in W' M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> W' a -> ~ W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  stores_in W M M'.
Proof.
  intros W W' M M' [A D] H. split; [|exact D].
  intros x Hx. destruct (Classical_Prop.classic (W' (bv_unsigned x))) as [Hw'|Hn'].
  - pose proof (u64_range x) as Hr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply H; assumption.
  - apply A. exact Hn'.
Qed.

Lemma rdn_of_pointwise : forall segs M (bs : list byte) a,
  0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall k, (k < length bs)%nat -> M (Z_to_bv 64 (a + Z.of_nat k)) = Some (nth k bs (Z_to_bv 8 0))) ->
  rdn segs M (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros segs M bs. induction bs as [|b bs IH]; intros a Ha Hn HP; [reflexivity|].
  cbn [length] in Hn, HP. cbn [rdn length]. rewrite Nat2Z.inj_succ in Hn.
  pose proof (HP 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth] in H0. rewrite H0.
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  - rewrite (IH (a + 1)); [reflexivity | lia | lia |]. intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. exact (HP (S k) ltac:(lia)).
  - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned (1%bv : bv 64)) with 1.
    rewrite (Z.mod_small a), (Z.mod_small (a + 1)) by lia. rewrite ?Z.mod_small by lia. reflexivity.
Qed.

Lemma fld8_sub1 : forall segs M a v (k : nat) b,
  0 <= a -> a + 8 <= 2 ^ 64 -> (k < 8)%nat -> CRep.fld segs M a 8 v ->
  RefMemcpyLib.sub (word_to_le_bytes 8 (Z_to_bv 64 v)) k 1 = word_to_le_bytes 1 (Z_to_bv 64 b) ->
  CRep.fld segs M (a + Z.of_nat k) 1 b.
Proof.
  intros segs M a v k b Ha Ha8 Hk H E. unfold CRep.fld in *.
  pose proof (RefMemcpyLib.rdn_sub segs M 8 (Z_to_bv 64 a) _ k 1 H ltac:(lia)) as X. unfold Hoare.at_ in X. rewrite u64_of_Z in X by lia.
  rewrite X, E. reflexivity.
Qed.

Lemma rdn_wbytes8_byte : forall segs M a v (k : nat) b,
  0 <= a -> a + 8 <= 2 ^ 64 -> (k < 8)%nat ->
  RefMemcpyLib.sub (word_to_le_bytes 8 (Z_to_bv 64 v)) k 1 = word_to_le_bytes 1 (Z_to_bv 64 b) ->
  rdn segs (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))) (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 b)).
Proof.
  intros segs M a v k b Ha Ha8 Hk E. apply (fld8_sub1 segs _ a v k b Ha Ha8 Hk); [|exact E].
  unfold CRep.fld. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
Qed.

Ltac wnorm2 H :=
  wnorm_in H; cbn [Z.of_N] in H;
  repeat match goal with G : getr ?R ?r = ?v |- _ =>
    let z := eval vm_compute in (bv_unsigned r) in
    progress (change (getr R (Z_to_bv 5 z)) with (getr R r) in H; rewrite G in H) end;
  revert H; znorm; intros H; rewrite ?Z.add_0_r in H; repeat rewrite Z.mod_small in H by lia.

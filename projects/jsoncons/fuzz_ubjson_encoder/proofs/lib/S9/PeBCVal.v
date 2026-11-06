(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PmModelFactsA PeStepAB0 PmStep PmParStep PeBSrcKit PmCertKitG PeBImgGap AxSymExec3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCValSpecA PeCValK PeBCValP1 PeBCValP2 PeBCValP3 PeBCValP4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_rb1068_b106c Eb0_code_rb1258_b125c.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import Utf8FactsS9.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVALB.
Import UTF8F. Import PECVK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac kks KS := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; apply KS; revert k Hk; kin.

Lemma land7_le x w : 0 <= x < 2 ^ 64 -> x mod 8 <= w -> 0 <= Z.land (x mod 2 ^ 64) 7 <= w.
Proof.
  intros H1 H2. rewrite (Z.mod_small x) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  pose proof (Z.mod_pos_bound x 8). lia.
Qed.
Lemma land7_le' x w : 0 <= x -> x mod 8 <= w -> 0 <= Z.land x 7 <= w.
Proof. intros H1 H2. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. pose proof (Z.mod_pos_bound x 8). lia. Qed.

Lemma e6 : Z_to_bv 64 18446744073709551551 = Z_to_bv 64 (-65). Proof. apply bv_eq. reflexivity. Qed.
Lemma e17 : Z_to_bv 64 18446744073709551554 = Z_to_bv 64 (-62). Proof. apply bv_eq. reflexivity. Qed.
Lemma e15 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1). Proof. apply bv_eq. reflexivity. Qed.
Lemma e19 : Z_to_bv 64 18446744073709405538 = Z_to_bv 64 (-146078). Proof. apply bv_eq. reflexivity. Qed.

Lemma table_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (146077 + Z.of_nat k)) 1 with
                                    | Some [x] => Z.eqb (bv_unsigned x) (utf8_trail (Z.of_nat k)) | _ => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_ok k : 0 <= k < 256 -> exists b, rdn RSEGS (fun _ => None) (Z_to_bv 64 (146077 + k)) 1 = Some [b] /\ bv_unsigned b = utf8_trail k.
Proof.
  intros Hk. pose proof table_all as T. rewrite forallb_forall in T. specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in T by lia. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (146077 + k)) 1) as [[|b [|]]|]; try discriminate.
  exists b. split; [reflexivity|]. apply Z.eqb_eq. exact T.
Qed.

Section Loop.
Variable Mv : word -> option byte.
Variables (S p e : Z).
Variable l : list Z.
Hypothesis IMG : L5.img_clear Mv 65536 1306624.
Hypothesis HS : 140735332487280 <= S <= 2 ^ 47.
Hypothesis Hp : 1 <= p.
Hypothesis Hpe : p <= e.
Hypothesis He : e <= 2 ^ 47.
Hypothesis Hn : e - p <= 2 ^ 26.
Hypothesis BY : L5.bytes_at RSEGS Mv p l.
Hypothesis LEN : blen l = e - p.
Hypothesis LB : Forall (fun b => 0 <= b < 256) l.
Hypothesis SH : forall c, p <= c < e -> L5KA.zeros_at Mv (c / 8 + 2147450880) 1 \/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS Mv (c / 8 + 2147450880) v /\ c mod 8 < v).
Hypothesis GAP1 : L5KA.zeros_at Mv 2147469139 33.

Definition vconst (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 112) /\ getr R (reg 5) = Z_to_bv 64 245 /\ getr R (reg 6) = Z_to_bv 64 2 /\ getr R (reg 7) = Z_to_bv 64 (-65)
  /\ getr R (reg 8) = Z_to_bv 64 159 /\ getr R (reg 9) = Z_to_bv 64 240 /\ getr R (reg 13) = Z_to_bv 64 e /\ getr R (reg 14) = Z_to_bv 64 8
  /\ getr R (reg 15) = Z_to_bv 64 (-1) /\ getr R (reg 16) = Z_to_bv 64 1 /\ getr R (reg 17) = Z_to_bv 64 (-62) /\ getr R (reg 18) = Z_to_bv 64 146077
  /\ getr R (reg 19) = Z_to_bv 64 (-146078) /\ getr R (reg 20) = Z_to_bv 64 2147450880 /\ getr R (reg 21) = Z_to_bv 64 144 /\ getr R (reg 22) = Z_to_bv 64 244
  /\ getr R (reg 23) = Z_to_bv 64 143 /\ getr R (reg 24) = Z_to_bv 64 3 /\ getr R (reg 28) = Z_to_bv 64 239 /\ getr R (reg 29) = Z_to_bv 64 224
  /\ getr R (reg 30) = Z_to_bv 64 160 /\ getr R (reg 31) = Z_to_bv 64 237.
Definition VC : list nat := [2; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%nat.
Lemma vconst_keep R R' : vconst R -> (forall k, In k VC -> getr R' (reg k) = getr R (reg k)) -> vconst R'.
Proof.
  intros (C2 & C5 & C6 & C7 & C8 & C9 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C28 & C29 & C30 & C31) K.
  unfold vconst. rewrite !K by (cbn; tauto). repeat split; assumption.
Qed.

Definition KL : list nat := [3; 4]%nat.

Definition goal_from (c : Z) (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
  exists fx' R' v, msteps RSEGS (L5SAR.st fx R pc Mv) (L5SAR.st fx' R' 0xb46fc Mv) /\ getr R' (reg 2) = Z_to_bv 64 (S - 112)
    /\ (forall k, In k KL -> getr R' (reg k) = getr R (reg k))
    /\ getr R' (reg 11) = Z_to_bv 64 v /\ 0 <= v < 7 /\ (v = 0 <-> utf8_valid (skipn (Z.to_nat (c - p)) l) = true).

Lemma lbyte a j : a = p + j -> 0 <= j < blen l -> exists b, b = bat l j /\ 0 <= b < 256 /\ L5.u8_at RSEGS Mv a b.
Proof.
  intros Ha Hj. exists (bat l j). split; [reflexivity|]. split; [apply bat_range; exact LB|].
  unfold bat. subst a. rewrite <- (Z2Nat.id j) at 1 by lia. apply BY. unfold blen in Hj. lia.
Qed.

Lemma goal_pre c fx R pc fx2 R2 pc2 : msteps RSEGS (L5SAR.st fx R pc Mv) (L5SAR.st fx2 R2 pc2 Mv) -> (forall k, In k KL -> getr R2 (reg k) = getr R (reg k)) ->
  goal_from c fx2 R2 pc2 -> goal_from c fx R pc.
Proof.
  intros MS KS (fx3 & R3 & v & MS3 & SP3 & KS3 & REST). exists fx3, R3, v. split; [eapply msteps_trans; [exact MS| exact MS3]|]. split; [exact SP3|].
  split; [| exact REST]. intros k Hk. rewrite (KS3 k Hk). apply KS. exact Hk.
Qed.

Lemma goal_same c d fx R pc : utf8_valid (skipn (Z.to_nat (c - p)) l) = utf8_valid (skipn (Z.to_nat (d - p)) l) -> goal_from d fx R pc -> goal_from c fx R pc.
Proof.
  intros EQ (fx3 & R3 & v & MS3 & SP3 & KS3 & A11 & Hv & IFF). exists fx3, R3, v. rewrite EQ. repeat split; try assumption; tauto.
Qed.

Lemma goal_err c fx R v : getr R (reg 2) = Z_to_bv 64 (S - 112) -> getr R (reg 11) = Z_to_bv 64 v -> 1 <= v < 7 ->
  utf8_valid (skipn (Z.to_nat (c - p)) l) = false -> goal_from c fx R 0xb46fc.
Proof.
  intros SP A11 Hv NV. exists fx, R, v. split; [apply mst_refl|]. split; [exact SP|]. split; [intros k Hk; reflexivity|].
  split; [exact A11|]. split; [lia|]. rewrite NV. split; [lia| discriminate].
Qed.

Ltac sc := first [ assumption | lia | (rewrite Zplus_minus; assumption) | (apply land7_le; lia) | (apply land7_le'; lia) ].
Ltac vfacts V := let C2 := fresh "C2" in
  pose proof V as (C2 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C13 & ?C14 & ?C15 & ?C16 & ?C17 & ?C18 & ?C19 & ?C20 & ?C21 & ?C22 & ?C23 & ?C24 & ?C28 & ?C29 & ?C30 & ?C31).

Ltac runp X fx R VAL :=
  let PP := fresh "PP" in let fx1 := fresh "fx" in let R1 := fresh "R" in let M1 := fresh "M" in let FR := fresh "FR" in
  pose proof (X fx R Mv VAL) as PP; cbn beta iota in PP; L5SAR.feed PP ltac:(sc);
  destruct PP as (fx1 & R1 & M1 & _ & FR & _ & EX); (assert (M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1.

Ltac runpk X fx R VAL K :=
  let PP := fresh "PP" in let fx1 := fresh "fx" in let R1 := fresh "R" in let M1 := fresh "M" in let FR := fresh "FR" in let EX := fresh "EX" in
  pose proof (X fx R Mv VAL) as PP; cbn beta iota in PP; L5SAR.feed PP ltac:(sc);
  destruct PP as (fx1 & R1 & M1 & _ & FR & _ & EX); (assert (M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1; K EX.

Ltac msks EX := let MS := fresh "MS" in let KS := fresh "KS" in
  lazymatch type of EX with
  | _ /\ _ /\ _ => destruct EX as (MS & KS & EXR); lazymatch type of EXR with _ /\ _ => decompose [and] EXR; clear EXR | _ => idtac end
  | _ /\ _ => destruct EX as (MS & KS)
  end; raws.
Ltac gpre := lazymatch goal with
  | MS : msteps _ (L5SAR.st ?fx ?R _ _) (L5SAR.st ?fx1 ?R1 _ _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- goal_from _ ?fx ?R _ =>
      apply (goal_pre _ fx R _ fx1 R1 _ MS ltac:(kks KS))
  end.
Ltac vk V := lazymatch goal with
  | KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x), V0 : vconst ?R |- vconst ?R1 => exact (vconst_keep R R1 V0 ltac:(kks KS))
  end.
Ltac kept k H := lazymatch goal with KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- getr ?R1 _ = _ => rewrite (KS k) by inl; exact H end.
Ltac vsplit v Hv := let HV := fresh "HV" in assert (HV : v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia;
  destruct HV as [->|[->|[->|[->|[->|[->| ->]]]]]].

Ltac epi_err d0 V := lazymatch goal with
  | A11 : getr ?R1 (reg 11) = Z_to_bv 64 ?v |- goal_from _ _ ?R1 0xb46fc =>
      apply (goal_err d0 _ R1 v ltac:(kept 2%nat (proj1 V)) A11 ltac:(clear; lia))
  end.

Section IH.
Variable c : Z.
Hypothesis IH : forall fx R c', c < c' < e -> vconst R -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from c' fx R 0xb4400.

Lemma back_case fx R c' : p <= c < c' -> c' <= e -> vconst R -> getr R (reg 26) = Z_to_bv 64 c' -> goal_from c' fx R 0xb4630.
Proof using All.
  intros Hc Hc' V R26. vfacts V.
  set (a0 := bv_unsigned (getr R (reg 10))). pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as Ha0. change (bv_modulus 64) with (2 ^ 64) in Ha0.
  assert (R10 : getr R (reg 10) = Z_to_bv 64 a0) by (symmetry; apply Z_to_bv_bv_unsigned).
  runp PECVALBP1.bvlB_conc fx R (fun j => match j with 2%nat => S | 10%nat => a0 | 33%nat => c' | 35%nat => e - c' | _ => 0 end).
  destruct EX as [EX|EX]; msks EX.
  - lazymatch goal with EQ : _ < 1 |- _ =>
      assert (c' = e) by (rewrite Zplus_minus in EQ; rewrite (Z.mod_small e) in EQ by lia;
                          destruct (Z.eq_dec c' e) as [->|X]; [reflexivity| exfalso; rewrite <- (Z.mod_add _ 1), Z.mod_small in EQ by lia; lia]) end.
    subst c'. lazymatch goal with MS : msteps _ _ (L5SAR.st ?fx1 ?R1 _ _), A11 : getr _ (reg 11) = Z_to_bv 64 0 |- _ =>
      exists fx1, R1, 0; split; [exact MS|]; split; [kept 2%nat (proj1 V)|]; split; [kks KS|]; split; [exact A11|] end.
    split; [lia|]. split; [intros _| reflexivity]. rewrite skipn_all2; [apply utf8_valid_nil|]. unfold blen in LEN. lia.
  - assert (LT : c' < e).
    { destruct (Z.eq_dec c' e) as [Ec|Ec]; [| lia]. exfalso.
      lazymatch goal with NE : 1 <= _ |- _ => rewrite Zplus_minus, (Z.mod_small e), Ec, Z.sub_diag, Z.mod_0_l in NE by lia; lia end. }
    gpre. apply (IH _ _ c' ltac:(lia)); [vk V| assumption].
Qed.

Local Ltac lexit d0 nx b0 t Eb0 Et WIN PASS V R26 := lazymatch goal with
  | MS : msteps _ _ (L5SAR.st _ _ 0xb46fc _) |- _ =>
      gpre; epi_err d0 V;
      apply (valid_bad_bt l (d0 - p) b0 t ltac:(lia) Eb0 Et ltac:(lia)); rewrite WIN; legal_false
  | _ => gpre; apply (goal_same d0 nx);
      [ apply (valid_step_bt l (d0 - p) b0 t (nx - p) ltac:(lia) Eb0 Et ltac:(lia) ltac:(lia)); rewrite WIN;
        apply PASS; [unfold second_ok; lia| unfold lead_ok; lia]
      | apply (back_case _ _ nx ltac:(lia) ltac:(lia)); [vk V| kept 26%nat R26] ]
  end.

Lemma lead_case fx R d0 t b0 b1 rest :
  p <= c <= d0 -> 1 <= t <= 3 -> d0 + t + 1 <= e -> b0 = bat l (d0 - p) -> t = utf8_trail b0 -> 0 <= b1 < 256 ->
  firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat (d0 - p)) l) = b0 :: b1 :: rest ->
  (second_ok b0 b1 -> lead_ok b0 -> utf8_legal (b0 :: b1 :: rest) = true) ->
  vconst R -> getr R (reg 10) = Z_to_bv 64 d0 -> getr R (reg 26) = Z_to_bv 64 (d0 + t + 1) ->
  getr R (reg 25) = Z_to_bv 64 b0 -> getr R (reg 11) = Z_to_bv 64 (sx8u b1) -> goal_from d0 fx R 0xb45e4.
Proof using All.
  intros Hc Ht Hd Eb0 Et Hb1 WIN PASS V R10 R26 R25 R11. vfacts V.
  pose proof (bat_range l (d0 - p) LB) as Hb0. rewrite <- Eb0 in Hb0.
  pose proof (sx8u_range b1 Hb1) as Ha1.
  assert (WL : d0 - p + (t + 1) <= blen l) by (clear - Hd LEN Hc; lia).
  runp PECVALBP1.bvlL_conc fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => d0 + t + 1 | 35%nat => e - d0 | 37%nat => b0 | 39%nat => sx8u b1 | _ => 0 end).
  rewrite (sx8u_land b1 Hb1) in EX.
  repeat (destruct EX as [EX|EX]; [msks EX; lexit d0 (d0 + t + 1) b0 t Eb0 Et WIN PASS V R26|]); msks EX; lexit d0 (d0 + t + 1) b0 t Eb0 Et WIN PASS V R26.
Qed.

Local Ltac cexit_err d0 b0 t Eb0 Et WIN V :=
  gpre; epi_err d0 V; apply (valid_bad_bt l (d0 - p) b0 t ltac:(lia) Eb0 Et ltac:(lia)); rewrite WIN; legal_false.

Local Ltac r1v X d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25 :=
  lazymatch goal with |- goal_from _ ?fx ?R _ =>
    runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => d0 + t + 1 | 35%nat => e - d0 | 37%nat => b0 | 39%nat => b1 | _ => 0 end)
      ltac:(fun EX =>
    destruct EX as [EX|EX]; msks EX;
    [ cexit_err d0 b0 t Eb0 Et WIN V
    | gpre; lazymatch goal with A11 : getr _ (reg 11) = Z_to_bv 64 (sx8u b1), CB : 128 <= b1 < 192 |- _ =>
        apply (lead_case _ _ d0 t b0 b1 rest ltac:(lia) ltac:(lia) ltac:(lia) Eb0 Et ltac:(assumption) WIN (PASS CB));
        [vk V| kept 10%nat R10| kept 26%nat R26| kept 25%nat R25| exact A11] end ])
  end.
Lemma r1_case fx R d0 t b0 b1 rest :
  p <= c <= d0 -> 1 <= t <= 3 -> d0 + t + 1 <= e -> b0 = bat l (d0 - p) -> t = utf8_trail b0 -> b1 = bat l (d0 - p + 1) ->
  firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat (d0 - p)) l) = b0 :: b1 :: rest ->
  (128 <= b1 < 192 -> second_ok b0 b1 -> lead_ok b0 -> utf8_legal (b0 :: b1 :: rest) = true) ->
  vconst R -> getr R (reg 10) = Z_to_bv 64 d0 -> getr R (reg 12) = Z_to_bv 64 (d0 + 2) -> getr R (reg 26) = Z_to_bv 64 (d0 + t + 1) ->
  getr R (reg 25) = Z_to_bv 64 b0 -> goal_from d0 fx R 0xb45c4.
Proof using All.
  intros Hc Ht Hd Eb0 Et Eb1 WIN PASS V R10 R12 R26 R25. vfacts V.
  pose proof (bat_range l (d0 - p) LB) as Hb0. rewrite <- Eb0 in Hb0.
  assert (WL : d0 - p + (t + 1) <= blen l) by lia.
  destruct (lbyte (d0 + 1) (d0 - p + 1) ltac:(lia) ltac:(lia)) as (b1' & Eb1' & Hb1 & U1). rewrite <- Eb1 in Eb1'. subst b1'.
  destruct (SH (d0 + 1) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
  - r1v PECVALBP4.bvlR1Z_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
  - vsplit v Hv.
    + r1v PECVALBP4.bvlR1P1_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
    + r1v PECVALBP4.bvlR1P2_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
    + r1v PECVALBP4.bvlR1P3_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
    + r1v PECVALBP4.bvlR1P4_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
    + r1v PECVALBP4.bvlR1P5_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
    + r1v PECVALBP4.bvlR1P6_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
    + r1v PECVALBP4.bvlR1P7_conc d0 t b0 b1 rest Eb0 Et WIN PASS V R10 R26 R25.
Qed.

Local Ltac r2v X d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25 :=
  lazymatch goal with |- goal_from _ ?fx ?R _ =>
    runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => d0 + t + 1 | 35%nat => e - d0 | 37%nat => b0 | 39%nat => b2 | _ => 0 end)
      ltac:(fun EX =>
    destruct EX as [EX|EX]; msks EX;
    [ cexit_err d0 b0 t Eb0 Et WIN V
    | gpre; lazymatch goal with CB : 128 <= b2 < 192 |- _ =>
        apply (r1_case _ _ d0 t b0 b1 (b2 :: rest) ltac:(lia) ltac:(lia) ltac:(lia) Eb0 Et Eb1 WIN (PASS CB));
        [vk V| kept 10%nat R10| assumption| kept 26%nat R26| kept 25%nat R25] end ])
  end.
Lemma r2_case fx R d0 t b0 b1 b2 rest :
  p <= c <= d0 -> 2 <= t <= 3 -> d0 + t + 1 <= e -> b0 = bat l (d0 - p) -> t = utf8_trail b0 -> b1 = bat l (d0 - p + 1) -> b2 = bat l (d0 - p + 2) ->
  firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat (d0 - p)) l) = b0 :: b1 :: b2 :: rest ->
  (128 <= b2 < 192 -> 128 <= b1 < 192 -> second_ok b0 b1 -> lead_ok b0 -> utf8_legal (b0 :: b1 :: b2 :: rest) = true) ->
  vconst R -> getr R (reg 10) = Z_to_bv 64 d0 -> getr R (reg 1) = Z_to_bv 64 (d0 + 3) -> getr R (reg 26) = Z_to_bv 64 (d0 + t + 1) ->
  getr R (reg 25) = Z_to_bv 64 b0 -> goal_from d0 fx R 0xb45a4.
Proof using All.
  intros Hc Ht Hd Eb0 Et Eb1 Eb2 WIN PASS V R10 R1 R26 R25. vfacts V.
  pose proof (bat_range l (d0 - p) LB) as Hb0. rewrite <- Eb0 in Hb0.
  assert (WL : d0 - p + (t + 1) <= blen l) by lia.
  destruct (lbyte (d0 + 2) (d0 - p + 2) ltac:(lia) ltac:(lia)) as (b2' & Eb2' & Hb2 & U2). rewrite <- Eb2 in Eb2'. subst b2'.
  destruct (SH (d0 + 2) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
  - r2v PECVALBP4.bvlR2Z_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
  - vsplit v Hv.
    + r2v PECVALBP4.bvlR2P1_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
    + r2v PECVALBP4.bvlR2P2_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
    + r2v PECVALBP4.bvlR2P3_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
    + r2v PECVALBP4.bvlR2P4_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
    + r2v PECVALBP4.bvlR2P5_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
    + r2v PECVALBP4.bvlR2P6_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
    + r2v PECVALBP4.bvlR2P7_conc d0 t b0 b1 b2 rest Eb0 Et Eb1 WIN PASS V R10 R26 R25.
Qed.

Local Ltac r3v X d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25 :=
  lazymatch goal with |- goal_from _ ?fx ?R _ =>
    runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | 39%nat => b3 | _ => 0 end)
      ltac:(fun EX =>
    destruct EX as [EX|EX]; msks EX;
    [ cexit_err d0 b0 3 Eb0 Et WIN V
    | gpre; lazymatch goal with CB : 128 <= b3 < 192 |- _ =>
        apply (r2_case _ _ d0 3 b0 b1 b2 [b3] ltac:(lia) ltac:(lia) ltac:(lia) Eb0 Et Eb1 Eb2 WIN (PASS CB));
        [vk V| kept 10%nat R10| assumption| replace (d0 + 3 + 1) with (d0 + 4) by (clear; lia); kept 26%nat R26| kept 25%nat R25] end ])
  end.
Lemma r3_case fx R d0 b0 b1 b2 b3 :
  p <= c <= d0 -> d0 + 4 <= e -> b0 = bat l (d0 - p) -> 3 = utf8_trail b0 -> b1 = bat l (d0 - p + 1) -> b2 = bat l (d0 - p + 2) -> b3 = bat l (d0 - p + 3) ->
  firstn (Z.to_nat (3 + 1)) (skipn (Z.to_nat (d0 - p)) l) = [b0; b1; b2; b3] ->
  (128 <= b3 < 192 -> 128 <= b2 < 192 -> 128 <= b1 < 192 -> second_ok b0 b1 -> lead_ok b0 -> utf8_legal [b0; b1; b2; b3] = true) ->
  vconst R -> getr R (reg 10) = Z_to_bv 64 d0 -> getr R (reg 12) = Z_to_bv 64 (d0 + 3) -> getr R (reg 26) = Z_to_bv 64 (d0 + 4) -> getr R (reg 1) = Z_to_bv 64 (d0 + 4) ->
  getr R (reg 25) = Z_to_bv 64 b0 -> goal_from d0 fx R 0xb4584.
Proof using All.
  intros Hc Hd Eb0 Et Eb1 Eb2 Eb3 WIN PASS V R10 R12 R26 R1 R25. vfacts V.
  pose proof (bat_range l (d0 - p) LB) as Hb0. rewrite <- Eb0 in Hb0.
  assert (WL : d0 - p + 4 <= blen l) by lia.
  destruct (lbyte (d0 + 3) (d0 - p + 3) ltac:(lia) ltac:(lia)) as (b3' & Eb3' & Hb3 & U3). rewrite <- Eb3 in Eb3'. subst b3'.
  destruct (SH (d0 + 3) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
  - r3v PECVALBP4.bvlR3Z_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
  - vsplit v Hv.
    + r3v PECVALBP4.bvlR3P1_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
    + r3v PECVALBP4.bvlR3P2_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
    + r3v PECVALBP4.bvlR3P3_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
    + r3v PECVALBP4.bvlR3P4_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
    + r3v PECVALBP4.bvlR3P5_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
    + r3v PECVALBP4.bvlR3P6_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
    + r3v PECVALBP4.bvlR3P7_conc d0 b0 b1 b2 b3 Eb0 Et Eb1 Eb2 WIN PASS V R10 R26 R25.
Qed.

Definition L2 : list nat := [2; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31; 3; 4; 10; 25]%nat.

Local Ltac win1 t k n := replace (t + 1) with k by lia; change (Z.to_nat k) with n.
Lemma tbl_case fx R d0 b0 : p <= c <= d0 -> d0 < e -> b0 = bat l (d0 - p) -> vconst R -> getr R (reg 10) = Z_to_bv 64 d0 ->
  getr R (reg 11) = Z_to_bv 64 (b0 + 146077) -> getr R (reg 25) = Z_to_bv 64 b0 -> goal_from d0 fx R 0xb4544.
Proof using All.
  intros Hc Hd Eb0 V R10 R11 R25.
  pose proof (bat_range l (d0 - p) LB) as Hb0. rewrite <- Eb0 in Hb0.
  destruct (table_ok b0 Hb0) as (tb & TB & TV).
  assert (L1 : (27%bv : bv 5) <> 0%bv) by discriminate.
  assert (LL2 : getr R (11%bv : bv 5) = Z_to_bv 64 (b0 + 146077)) by exact R11.
  assert (L3 : rdn RSEGS Mv (Z_to_bv 64 (b0 + 146077 + bv_signed (0%bv : bv 12))) 1 = Some [tb]).
  { change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, Z.add_comm. rewrite (PMCG.rdn_img RSEGS Mv 65536 1306624 _ 1 IMG) by lia. exact TB. }
  pose proof (PMCG.lbu_img_run RSEGS fx R Mv 0xb4544 W_b44f4 27%bv 11%bv 0%bv (b0 + 146077) tb F_b44f4 eq_refl D_b44f4 L1 ltac:(lia) ltac:(lia) LL2 ltac:(lia)
                ltac:(change (bv_signed (0%bv : bv 12)) with 0; lia) L3) as MSl.
  set (R2 := regupd R 27%bv (Z_to_bv 64 (bv_unsigned tb))) in MSl.
  assert (RU : forall k, k <> 27%nat -> (k < 32)%nat -> getr R2 (reg k) = getr R (reg k)).
  { intros k Hk Hk32. unfold R2. replace (27%bv : bv 5) with (reg 27) by (apply bv_eq; reflexivity). apply PMPX.regupd_other_idx; lia. }
  assert (R27 : getr R2 (reg 27) = Z_to_bv 64 (bv_unsigned tb)).
  { unfold R2. replace (27%bv : bv 5) with (reg 27) by (apply bv_eq; reflexivity). apply PMPX.regupd_same_idx. lia. }
  rewrite TV in R27.
  assert (KS2 : forall k, In k L2 -> getr R2 (reg k) = getr R (reg k)).
  { intros k Hk. unfold L2 in Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite RU by lia; reflexivity|]). destruct Hk. }
  assert (V2 : vconst R2) by exact (vconst_keep R R2 V ltac:(kks KS2)).
  assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 d0) by (rewrite KS2 by inl; exact R10).
  assert (R2_25 : getr R2 (reg 25) = Z_to_bv 64 b0) by (rewrite KS2 by inl; exact R25).
  apply (goal_pre d0 fx R 0xb4544 fx R2 (0xb4544 + 4)).
  { exact MSl. }
  { kks KS2. }
  change (0xb4544 + 4) with 0xb4548.
  clear MSl KS2 RU L1 LL2 L3 TB TV.
  vfacts V2.
  remember (utf8_trail b0) as t eqn:Tt. pose proof (utf8_trail_range b0) as TR. rewrite <- Tt in TR.
  assert (Hi : 0 <= d0 - p < blen l) by lia.
  assert (CASES : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ 4 <= t) by lia.

  Local Ltac t0exit d0 b0 t Eb0 Tt Hi V2 := lazymatch goal with
    | MS : msteps _ _ (L5SAR.st _ _ 0xb46fc _) |- _ =>
        gpre; epi_err d0 V2; apply (valid_bad_bt l (d0 - p) b0 t Hi Eb0 Tt ltac:(lia)); win1 t 1 1%nat; rewrite firstn_skipn_1 by lia; rewrite <- Eb0; legal_false
    | _ => gpre; apply (goal_same d0 (d0 + 1));
        [ rewrite (valid_step_bt l (d0 - p) b0 t (d0 + 1 - p) Hi Eb0 Tt ltac:(lia) ltac:(lia)); [reflexivity|];
          win1 t 1 1%nat; rewrite firstn_skipn_1 by lia; rewrite <- Eb0; apply legal1_true; [assumption| lia]
        | apply (back_case _ _ (d0 + 1) ltac:(lia) ltac:(lia)); [vk V2| assumption] ]
    end.
  destruct CASES as [Et|[Et|[Et|[Et|Et]]]].
  -
    rewrite Et in R27.
    runp PECVALBP1.bvlT0_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
    repeat (destruct EX as [EX|EX]; [msks EX; t0exit d0 b0 t Eb0 Tt Hi V2|]); msks EX; t0exit d0 b0 t Eb0 Tt Hi V2.
  -
    rewrite Et in R27. destruct (Z_le_gt_dec (e - d0) 1) as [LE|GT].
    + runp PECVALBP1.bvlT1a_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
      msks EX. gpre. epi_err d0 V2. apply (valid_short_bt l (d0 - p) b0 t Hi Eb0 Tt ltac:(lia)).
    + destruct (lbyte (d0 + 1) (d0 - p + 1) ltac:(lia) ltac:(lia)) as (b1 & Eb1 & Hb1 & _).
      assert (WIN : firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat (d0 - p)) l) = [b0; b1]).
      { win1 t 2 2%nat. rewrite firstn_skipn_2 by lia. rewrite <- Eb0, <- Eb1. reflexivity. }
      assert (PASS : 128 <= b1 < 192 -> second_ok b0 b1 -> lead_ok b0 -> utf8_legal [b0; b1] = true).
      { intros C1 SO LO. apply (proj2 (legal2_iff b0 b1)). exact (conj C1 (conj SO LO)). }
      runp PECVALBP1.bvlT1b_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
      msks EX. gpre.
      apply (r1_case _ _ d0 t b0 b1 [] ltac:(lia) ltac:(lia) ltac:(lia) Eb0 Tt Eb1 WIN PASS);
        [vk V2| kept 10%nat R2_10| assumption| replace (d0 + t + 1) with (d0 + 2) by lia; assumption| kept 25%nat R2_25].
  -
    rewrite Et in R27. destruct (Z_le_gt_dec (e - d0) 2) as [LE|GT].
    + runp PECVALBP1.bvlT2a_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
      msks EX. gpre. epi_err d0 V2. apply (valid_short_bt l (d0 - p) b0 t Hi Eb0 Tt ltac:(lia)).
    + destruct (lbyte (d0 + 1) (d0 - p + 1) ltac:(lia) ltac:(lia)) as (b1 & Eb1 & Hb1 & _).
      destruct (lbyte (d0 + 2) (d0 - p + 2) ltac:(lia) ltac:(lia)) as (b2 & Eb2 & Hb2 & _).
      assert (WIN : firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat (d0 - p)) l) = [b0; b1; b2]).
      { win1 t 3 3%nat. rewrite firstn_skipn_3 by lia. rewrite <- Eb0, <- Eb1, <- Eb2. reflexivity. }
      assert (PASS : 128 <= b2 < 192 -> 128 <= b1 < 192 -> second_ok b0 b1 -> lead_ok b0 -> utf8_legal [b0; b1; b2] = true).
      { intros C2' C1 SO LO. apply (proj2 (legal3_iff b0 b1 b2)). exact (conj C2' (conj C1 (conj SO LO))). }
      runp PECVALBP1.bvlT2b_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
      msks EX. gpre.
      apply (r2_case _ _ d0 t b0 b1 b2 [] ltac:(lia) ltac:(lia) ltac:(lia) Eb0 Tt Eb1 Eb2 WIN PASS);
        [vk V2| kept 10%nat R2_10| assumption| replace (d0 + t + 1) with (d0 + 3) by lia; assumption| kept 25%nat R2_25].
  -
    rewrite Et in R27. destruct (Z_le_gt_dec (e - d0) 3) as [LE|GT].
    + runp PECVALBP1.bvlT3a_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
      msks EX. gpre. epi_err d0 V2. apply (valid_short_bt l (d0 - p) b0 t Hi Eb0 Tt ltac:(lia)).
    + destruct (lbyte (d0 + 1) (d0 - p + 1) ltac:(lia) ltac:(lia)) as (b1 & Eb1 & Hb1 & _).
      destruct (lbyte (d0 + 2) (d0 - p + 2) ltac:(lia) ltac:(lia)) as (b2 & Eb2 & Hb2 & _).
      destruct (lbyte (d0 + 3) (d0 - p + 3) ltac:(lia) ltac:(lia)) as (b3 & Eb3 & Hb3 & _).
      rewrite Et in Tt.
      assert (WIN : firstn (Z.to_nat (3 + 1)) (skipn (Z.to_nat (d0 - p)) l) = [b0; b1; b2; b3]).
      { change (Z.to_nat (3 + 1)) with 4%nat. rewrite firstn_skipn_4 by lia. rewrite <- Eb0, <- Eb1, <- Eb2, <- Eb3. reflexivity. }
      assert (PASS : 128 <= b3 < 192 -> 128 <= b2 < 192 -> 128 <= b1 < 192 -> second_ok b0 b1 -> lead_ok b0 -> utf8_legal [b0; b1; b2; b3] = true).
      { intros C3 C2' C1 SO LO. apply (proj2 (legal4_iff b0 b1 b2 b3)). exact (conj C3 (conj C2' (conj C1 (conj SO LO)))). }
      runp PECVALBP1.bvlT3b_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end).
      msks EX. gpre.
      apply (r3_case _ _ d0 b0 b1 b2 b3 ltac:(lia) ltac:(lia) Eb0 Tt Eb1 Eb2 Eb3 WIN PASS);
        [vk V2| kept 10%nat R2_10| assumption| assumption| assumption| kept 25%nat R2_25].
  -
    runp PECVALBP1.bvlTbig_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | 38%nat => t | _ => 0 end).
    destruct EX as [EX|EX]; msks EX.
    + gpre. epi_err d0 V2. apply (valid_bad_bt l (d0 - p) b0 t Hi Eb0 Tt ltac:(lia)).
      rewrite legal_long; [reflexivity| rewrite length_firstn, length_skipn; unfold blen in *; lia].
    + gpre. epi_err d0 V2. apply (valid_short_bt l (d0 - p) b0 t Hi Eb0 Tt ltac:(lia)).
Qed.

Local Ltac sv X d0 b0 Eb0 V R10 :=
  lazymatch goal with |- goal_from _ ?fx ?R _ =>
    runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b0 | _ => 0 end) ltac:(fun EX =>
    msks EX; gpre; apply (tbl_case _ _ d0 b0 ltac:(lia) ltac:(lia) Eb0); [vk V| kept 10%nat R10| assumption| assumption])
  end.
Lemma slow fx R d0 : p <= c <= d0 -> d0 < e -> vconst R -> getr R (reg 10) = Z_to_bv 64 d0 -> goal_from d0 fx R 0xb4514.
Proof using All.
  intros Hc Hd V R10. vfacts V.
  destruct (lbyte d0 (d0 - p) ltac:(lia) ltac:(lia)) as (b0 & Eb0 & Hb0 & U0).
  destruct (SH d0 ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
  - sv PECVALBP1.bvlSZ_conc d0 b0 Eb0 V R10.
  - vsplit v Hv.
    + sv PECVALBP1.bvlSP1_conc d0 b0 Eb0 V R10.
    + sv PECVALBP1.bvlSP2_conc d0 b0 Eb0 V R10.
    + sv PECVALBP1.bvlSP3_conc d0 b0 Eb0 V R10.
    + sv PECVALBP1.bvlSP4_conc d0 b0 Eb0 V R10.
    + sv PECVALBP1.bvlSP5_conc d0 b0 Eb0 V R10.
    + sv PECVALBP1.bvlSP6_conc d0 b0 Eb0 V R10.
    + sv PECVALBP1.bvlSP7_conc d0 b0 Eb0 V R10.
Qed.

Local Ltac asc_close ASC Eb := let Hm := fresh in intros Hm; first [ apply ASC; lia | rewrite <- Eb; assumption | exfalso; lia ].
Local Ltac to_slow k b Eb V :=
  gpre; apply (goal_same c (c + k));
  [ replace (c + k - p) with (c - p + k) by lia;
    lazymatch goal with ASC : forall j, 0 <= j < _ -> bat l (c - p + j) < 128 |- _ =>
      apply (ascii_pref l (c - p) k LB); [lia| lia| lia| asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb
                                         | asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb] end
  | lazymatch goal with A10 : getr _ (reg 10) = Z_to_bv 64 (c + k) |- _ =>
      apply (slow _ _ (c + k) ltac:(lia) ltac:(lia)); [vk V| exact A10] end ].
Local Ltac fnext FN k V R10 := gpre;
  lazymatch goal with ASC : forall j, 0 <= j < _ -> bat l (c - p + j) < 128, Eb : ?b = bat l (c - p + k), Hlt : ?b < 128 |- _ =>
    apply (FN _ _ ltac:(lia) ltac:(lia) ltac:(intros j Hj; destruct (Z.eq_dec j k) as [->|NE]; [rewrite <- Eb; exact Hlt| apply ASC; clear - Hj NE; lia]));
    [vk V| kept 10%nat R10] end.
Local Ltac fback V := gpre; apply (goal_same c (c + 8));
  [ replace (c + 8 - p) with (c - p + 8) by lia;
    lazymatch goal with ASC : forall j, 0 <= j < _ -> bat l (c - p + j) < 128, Eb : ?b = bat l (c - p + 7), Hlt : ?b < 128 |- _ =>
      apply (ascii_pref l (c - p) 8 LB); [lia| lia| lia| asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb
                                         | asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb| asc_close ASC Eb] end
  | apply (back_case _ _ (c + 8) ltac:(lia) ltac:(lia)); [vk V| assumption] ].
Local Ltac fv X k NEXT b Eb V R10 :=
  lazymatch goal with |- goal_from _ ?fx ?R _ =>
    runpk X fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b | _ => 0 end) ltac:(fun EX =>
    destruct EX as [EX|EX]; msks EX; [ to_slow k b Eb V | NEXT ])
  end.
Local Ltac fcases Z P1 P2 P3 P4 P5 P6 P7 k NEXT :=
  lazymatch goal with V : vconst ?R, R10 : getr ?R (reg 10) = _ |- goal_from _ _ ?R _ =>
    vfacts V;
    let b := fresh "b" in let Eb := fresh "Eb" in let Hb := fresh "Hb" in let U := fresh "U" in
    destruct (lbyte (c + k) (c - p + k) ltac:(lia) ltac:(lia)) as (b & Eb & Hb & U);
    destruct (SH (c + k) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)];
    [ fv Z k NEXT b Eb V R10
    | vsplit v Hv; [ fv P1 k NEXT b Eb V R10 | fv P2 k NEXT b Eb V R10 | fv P3 k NEXT b Eb V R10 | fv P4 k NEXT b Eb V R10
                   | fv P5 k NEXT b Eb V R10 | fv P6 k NEXT b Eb V R10 | fv P7 k NEXT b Eb V R10 ] ]
  end.
Lemma fast7 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 7 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb44e8.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP3.bvlF7Z_conc PECVALBP3.bvlF7P1_conc PECVALBP3.bvlF7P2_conc PECVALBP3.bvlF7P3_conc PECVALBP3.bvlF7P4_conc PECVALBP3.bvlF7P5_conc
         PECVALBP3.bvlF7P6_conc PECVALBP3.bvlF7P7_conc 7 ltac:(fback V).
Qed.
Lemma fast6 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 6 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb44c8.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP3.bvlF6Z_conc PECVALBP3.bvlF6P1_conc PECVALBP3.bvlF6P2_conc PECVALBP3.bvlF6P3_conc PECVALBP3.bvlF6P4_conc PECVALBP3.bvlF6P5_conc
         PECVALBP3.bvlF6P6_conc PECVALBP3.bvlF6P7_conc 6 ltac:(fnext fast7 6 V R10).
Qed.
Lemma fast5 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 5 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb44a8.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP3.bvlF5Z_conc PECVALBP3.bvlF5P1_conc PECVALBP3.bvlF5P2_conc PECVALBP3.bvlF5P3_conc PECVALBP3.bvlF5P4_conc PECVALBP3.bvlF5P5_conc
         PECVALBP3.bvlF5P6_conc PECVALBP3.bvlF5P7_conc 5 ltac:(fnext fast6 5 V R10).
Qed.
Lemma fast4 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 4 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb4488.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP2.bvlF4Z_conc PECVALBP2.bvlF4P1_conc PECVALBP2.bvlF4P2_conc PECVALBP2.bvlF4P3_conc PECVALBP2.bvlF4P4_conc PECVALBP2.bvlF4P5_conc
         PECVALBP2.bvlF4P6_conc PECVALBP2.bvlF4P7_conc 4 ltac:(fnext fast5 4 V R10).
Qed.
Lemma fast3 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 3 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb4468.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP2.bvlF3Z_conc PECVALBP2.bvlF3P1_conc PECVALBP2.bvlF3P2_conc PECVALBP2.bvlF3P3_conc PECVALBP2.bvlF3P4_conc PECVALBP2.bvlF3P5_conc
         PECVALBP2.bvlF3P6_conc PECVALBP2.bvlF3P7_conc 3 ltac:(fnext fast4 3 V R10).
Qed.
Lemma fast2 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 2 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb4448.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP2.bvlF2Z_conc PECVALBP2.bvlF2P1_conc PECVALBP2.bvlF2P2_conc PECVALBP2.bvlF2P3_conc PECVALBP2.bvlF2P4_conc PECVALBP2.bvlF2P5_conc
         PECVALBP2.bvlF2P6_conc PECVALBP2.bvlF2P7_conc 2 ltac:(fnext fast3 2 V R10).
Qed.
Lemma fast1 fx R : p <= c -> c + 8 <= e -> (forall j, 0 <= j < 1 -> bat l (c - p + j) < 128) -> vconst R -> getr R (reg 10) = Z_to_bv 64 c ->
  goal_from c fx R 0xb4428.
Proof using All.
  intros Hc Hce ASC V R10.
  fcases PECVALBP2.bvlF1Z_conc PECVALBP2.bvlF1P1_conc PECVALBP2.bvlF1P2_conc PECVALBP2.bvlF1P3_conc PECVALBP2.bvlF1P4_conc PECVALBP2.bvlF1P5_conc
         PECVALBP2.bvlF1P6_conc PECVALBP2.bvlF1P7_conc 1 ltac:(fnext fast2 1 V R10).
Qed.
End IH.

Lemma granule0 c : p <= c -> c + 8 <= e -> L5KA.zeros_at Mv (c / 8 + 2147450880) 1.
Proof using All.
  intros H1 H2. set (a := c + (7 - c mod 8)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod c 8 ltac:(lia)) as Dm.
  assert (Ea : a / 8 = c / 8).
  { unfold a. replace (c + (7 - c mod 8)) with (7 + (c / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Ma : a mod 8 = 7).
  { unfold a. replace (c + (7 - c mod 8)) with (7 + (c / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  destruct (SH a ltac:(unfold a; lia)) as [Z0 | (v & Hv & _ & Hav)]; [rewrite Ea in Z0; exact Z0| lia].
Qed.

Lemma loop_head : forall (n : nat) fx R c, Z.of_nat n = e - c -> p <= c < e -> vconst R -> getr R (reg 10) = Z_to_bv 64 c -> goal_from c fx R 0xb4400.
Proof using All.
  intros n. induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf). intros fx R c Hn' Hc V R10.
  assert (IH : forall fx R c', c < c' < e -> vconst R -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from c' fx R 0xb4400).
  { intros fx' R' c' Hc' V' R10'. apply (IHn (Z.to_nat (e - c')) ltac:(lia) fx' R' c'); [lia| lia| exact V'| exact R10']. }
  vfacts V.
  destruct (Z_le_gt_dec 8 (e - c)) as [GE|LT].
  - destruct (lbyte c (c - p) ltac:(lia) ltac:(lia)) as (b0 & Eb0 & Hb0 & U0).
    pose proof (granule0 c ltac:(lia) ltac:(lia)) as Z0.
    runp PECVALBP1.bvlHf_conc fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | _ => 0 end).
    destruct EX as [EX|EX]; msks EX; gpre.
    + apply (slow c IH _ _ c ltac:(lia) ltac:(lia)); [vk V| first [kept 10%nat R10 | assumption]].
    + lazymatch goal with Hlt : b0 < 128 |- _ =>
        apply (fast1 c IH _ _ ltac:(lia) ltac:(lia) ltac:(intros j Hj; replace j with 0 by lia; rewrite Z.add_0_r, <- Eb0; exact Hlt)); [vk V| kept 10%nat R10] end.
  - runp PECVALBP1.bvlHs_conc fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | _ => 0 end).
    msks EX. gpre. apply (slow c IH _ _ c ltac:(lia) ltac:(lia)); [vk V| first [kept 10%nat R10 | assumption]].
Qed.
End Loop.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis GAP : PMBGAP.rt_img_gap HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma u8_of_byte (M : word -> option byte) a v : byte_at M a v -> L5.u8_at RSEGS M a v.
Proof. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.

Theorem validate_fun_ok : PECVSA.validate_fun_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb4350.
Proof.
  unfold PECVSA.validate_fun_spec.
  intros fx R M model K LB FF LK Aw cr p n sp r l HH AM K0 ENT FRM FRS A10 A11 Hn Hp Hp0 Hpn DEF ACC VIS LOC BASE BYl LENl LBl KONT.
  change (PMSTA.base_okA RSEGS PMB.AD M) in BASE.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  change (PMSPA.pm_scr 0) with 12288 in *.
  pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 12288 112 HH ASTK ltac:(lia)) as (SL112 & SH112 & V3).
  pose proof (PMBGAP.gap_vis HI GAP LB FF LK cr Aw M model HH) as GZ.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (V0' : L5.img_clear MV 1273856 1306624) by (intros i Hi; apply V0; lia).
  set (P := fun a => sp - 104 <= a < sp - 104 + 104).

  assert (FIN : forall fx2 R2 M1v, mem_grows MV M1v -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
                  msteps RSEGS (L5SAR.st fx R 0xb4350 MV) (L5SAR.st fx2 R2 0xb4734 M1v) -> getr R2 (reg 1) = Z_to_bv 64 r ->
                  regs_preserved R R2 -> forall v, getr R2 (reg 11) = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
                  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb4350 M model) K).
  { intros fx2 R2 M1v MG1 AG1 MSA B1 RP v Av Hv IFF. unfold PMSPA.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xb4350 R2 0xb4734 M1v P K HH AM MSA MG1 AG1).
    { intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    apply (PMBSK.ret_exit L ar C HI LY HIok fx2 R2 M1 model1 K _ FF LK cr Aw 0xb4734 r W_b46e4 HH1 AM1 F_b46e4 eq_refl D_b46e4 B1 ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx2 R2 M1 model2 v).
    - exact RP.
    - intros x Ox. rewrite <- (Z_to_bv_bv_unsigned _ x). apply FR1; [apply bv_unsigned_in_range|].
      intros Px. unfold P in Px. apply (Ox (sp - 12288, 12288)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. lia.
    - exact MGM1.
    - eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    - exact AM2.
    - exact HH2.
    - rewrite L5SAR.r11. exact Av.
    - exact Hv.
    - exact IFF. }

  assert (EPIL : forall fx3 R3 M1v, mem_grows MV M1v -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
      getr R3 (reg 2) = Z_to_bv 64 (sp - 112) ->
      L5.u64_at RSEGS M1v (sp - 104) (bv_unsigned (getr R (reg 27))) ->
      L5.u64_at RSEGS M1v (sp - 96) (bv_unsigned (getr R (reg 26))) -> L5.u64_at RSEGS M1v (sp - 88) (bv_unsigned (getr R (reg 25))) ->
      L5.u64_at RSEGS M1v (sp - 80) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M1v (sp - 72) (bv_unsigned (getr R (reg 23))) ->
      L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21))) ->
      L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20))) -> L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19))) ->
      L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18))) -> L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9))) ->
      L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8))) -> L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1))) ->
      (forall k, In k [3; 4]%nat -> getr R3 (reg k) = getr R (reg k)) ->
      forall v, getr R3 (reg 11) = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
      msteps RSEGS (L5SAR.st fx R 0xb4350 MV) (L5SAR.st fx3 R3 0xb46fc M1v) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb4350 M model) K).
  { intros fx3 R3 M1v MG1 AG1 R32 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8 K3 v Av Hv IFF MS3.
    pose proof (PECVALBP1.bvlX_conc fx3 R3 M1v (fun j => match j with 2%nat => sp | 40%nat => bv_unsigned (getr R (reg 1)) | 41%nat => bv_unsigned (getr R (reg 8))
        | 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18)) | 44%nat => bv_unsigned (getr R (reg 19)) | 45%nat => bv_unsigned (getr R (reg 20))
        | 46%nat => bv_unsigned (getr R (reg 21)) | 47%nat => bv_unsigned (getr R (reg 22)) | 48%nat => bv_unsigned (getr R (reg 23)) | 49%nat => bv_unsigned (getr R (reg 24))
        | 50%nat => bv_unsigned (getr R (reg 25)) | 51%nat => bv_unsigned (getr R (reg 26)) | 52%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) as PX. cbn beta iota in PX.
    L5SAR.feed PX ltac:(first [assumption | apply bv_unsigned_in_range | unfold PECVALBP1.aligned; lia | lia]).
    destruct PX as (fx4 & R4 & M4 & _ & FR4 & _ & (MS4 & KS4 & X1 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27)).
    assert (EM : M4 = M1v) by (apply functional_extensionality; exact FR4). subst M4.
    eapply (FIN fx4 R4 M1v MG1 AG1 ltac:(eapply msteps_trans; [exact MS3| exact MS4])); [| | rewrite (KS4 11%nat) by inl; exact Av| exact Hv| exact IFF].
    - rewrite X1, Z_to_bv_bv_unsigned. exact Rra.
    - apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx. cbn [In] in Hx.
      destruct Hx as [<-|Hx]; [rewrite X2, Rsp; reflexivity|].
      destruct Hx as [<-|Hx]; [rewrite (KS4 3%nat) by inl; apply K3; cbn; tauto|].
      destruct Hx as [<-|Hx]; [rewrite (KS4 4%nat) by inl; apply K3; cbn; tauto|].
      destruct Hx as [<-|Hx]; [rewrite X8; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X9; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X18; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X19; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X20; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X21; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X22; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X23; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X24; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X25; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X26; apply Z_to_bv_bv_unsigned|].
      destruct Hx as [<-|Hx]; [rewrite X27; apply Z_to_bv_bv_unsigned|].
      destruct Hx. }
  destruct (Z.eq_dec n 0) as [N0|N0].
  -
    revert LENl. subst n. intros LENl.
    assert (NIL : 0 = 0 <-> utf8_valid l = true).
    { split; [intros _| reflexivity]. destruct l; [apply utf8_valid_nil| exfalso; cbn [length] in LENl; lia]. }
    destruct (Z.eq_dec p 0) as [P0|P0].
    + pose proof (PECVALBP1.bvlE00_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | _ => 0 end)) as PP. cbn beta iota in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PECVALBP1.aligned; lia | lia | (rewrite A11; reflexivity)]).
      destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS & KS & E2 & E12 & E13 & E14 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)).
      eapply (EPIL fx1 R1 M1v MG1 ltac:(intros a Ha Na; apply FRZ1; [exact Ha| exact Na]) E2 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8);
        [intros k Hk; apply KS; revert k Hk; kin| rewrite (KS 11%nat) by inl; exact A11| clear; lia| exact NIL| exact MS].
    + pose proof (PECVALBP1.bvlE01_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | _ => 0 end)) as PP. cbn beta iota in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PECVALBP1.aligned; lia | lia | (rewrite A11; reflexivity)]).
      destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS & KS & E2 & E12 & E13 & E14 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)).
      eapply (EPIL fx1 R1 M1v MG1 ltac:(intros a Ha Na; apply FRZ1; [exact Ha| exact Na]) E2 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8);
        [intros k Hk; apply KS; revert k Hk; kin| rewrite (KS 11%nat) by inl; exact A11| clear; lia| exact NIL| exact MS].
  -
    assert (P1 : 1 <= p) by (destruct Hp0; lia).
    pose proof (PECVALBP1.bvlEn_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) as PP. cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | unfold PECVALBP1.aligned; lia | lia]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS & KS & E2 & E5 & E6 & E7 & E8 & E9 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22
                                                     & E23 & E24 & E28 & E29 & E30 & E31 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)).
    assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
    assert (NPs : forall c, 0 <= c < 2 ^ 47 -> ~ P (c / 8 + 2147450880)).
    { intros c Hc. unfold P. assert (c / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). assert (0 <= c / 8) by (apply Z.div_pos; lia). lia. }
    assert (NPb : forall c, p <= c < p + n -> ~ P c).
    { intros c Hc. unfold P. destruct LOC as [X|[X|X]]; lia. }

    assert (IMG1 : L5.img_clear M1v 65536 1306624).
    { intros i Hi. rewrite AG1 by (unfold P; lia). apply V0. exact Hi. }
    assert (BY1 : L5.bytes_at RSEGS M1v p l).
    { intros i Hi. pose proof (BYl i Hi) as U. set (c := p + Z.of_nat i) in *.
      assert (Hc : p <= c < p + n) by (subst c; clear - Hi LENl; lia). destruct (VIS c Hc) as (Vc & _).
      assert (AV : L5A.avis H c 1) by (intros j Hj; replace (c + j) with c by lia; exact Vc).
      apply (L5C.u8_at_agree RSEGS MV M1v); [intros j Hj; rewrite AG1; [reflexivity| lia| apply NPb; lia]| lia| lia|].
      apply (proj2 (L5A.u8_at_vis H M c _ AV ltac:(lia) ltac:(lia))). exact U. }
    assert (SH1 : forall c, p <= c < p + n -> L5KA.zeros_at M1v (c / 8 + 2147450880) 1
                    \/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS M1v (c / 8 + 2147450880) v /\ c mod 8 < v)).
    { intros c Hc. destruct (VIS c Hc) as (_ & Vs). unfold HeapIfaceA.S, HeapIfaceA.SB in Vs.
      assert (AVs : L5A.avis H (c / 8 + 2147450880) 1) by (intros i Hi; replace (c / 8 + 2147450880 + i) with (c / 8 + 2147450880) by lia; exact Vs).
      assert (Bc : 0 <= c / 8 + 2147450880 < 2 ^ 64) by (assert (c / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); assert (0 <= c / 8) by (apply Z.div_pos; lia); lia).
      destruct (ACC c Hc) as [B0|(v & Bv & Hv & Hcv)]; unfold HeapIfaceA.S, HeapIfaceA.SB in *.
      - left. intros j Hj. replace (c / 8 + 2147450880 + j) with (c / 8 + 2147450880) by lia. rewrite AG1 by (first [lia| apply NPs; lia]).
        unfold MV. rewrite (mrestrict_visible H M (Z_to_bv 64 (c / 8 + 2147450880))) by (exact Vs). exact B0.
      - right. exists v. split; [exact Hv|]. split; [|exact Hcv].
        apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; replace i with (c / 8 + 2147450880) by lia; rewrite AG1; [reflexivity| lia| apply NPs; lia]| lia| lia|].
        apply (proj2 (L5A.u8_at_vis H M _ v AVs ltac:(lia) ltac:(lia))). apply u8_of_byte. exact Bv. }
    assert (GZ1 : L5KA.zeros_at M1v 2147469139 33).
    { intros j Hj. rewrite AG1 by (unfold P; lia). pose proof (GZ (j + 3) ltac:(lia)) as Gj. replace (2147469136 + (j + 3)) with (2147469139 + j) in Gj by lia. exact Gj. }
    rewrite e6 in E7. rewrite e17 in E17. rewrite e15 in E15. rewrite e19 in E19.
    assert (E10 : getr R1 (reg 10) = Z_to_bv 64 p) by (rewrite (KS 10%nat) by inl; exact A10).
    assert (VC1 : vconst sp (p + n) R1) by (unfold vconst; repeat split; assumption).
    destruct (loop_head M1v sp p (p + n) l IMG1 ltac:(lia) P1 ltac:(lia) Hpn ltac:(lia) BY1 ltac:(unfold blen; lia) LBl SH1 GZ1 (Z.to_nat n) fx1 R1 p
                ltac:(lia) ltac:(lia) VC1 E10) as (fx2 & R2 & v & MS2 & SP2 & KS2 & Av & Hv & IFF).
    rewrite Z.sub_diag in IFF. cbn [Z.to_nat skipn] in IFF.
    eapply (EPIL fx2 R2 M1v MG1 AG1 SP2 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8); [| exact Av| exact Hv| exact IFF|].
    + intros k Hk. rewrite (KS2 k ltac:(revert k Hk; kin)). apply KS. revert k Hk. kin.
    + eapply msteps_trans; [exact MS| exact MS2].
Qed.

End Stage.

End PECVALB.

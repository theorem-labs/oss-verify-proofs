(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsBXJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMBPQ.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Definition pushq_spec_at (pc : Z) (Q : Z -> Z -> list PM.pstate -> list (Z * Z) -> Prop) (A0 : bvmap 5 word -> Z -> list PM.pstate -> Prop)
    (cells : list fframe -> Z -> Z -> (word -> option byte) -> bvmap 5 word -> PM.pstate -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b k : Z) (stk : list PM.pstate) (own : list (Z * Z))
         (c : PM.pstate) (sp r : Z),
    Q b k stk own ->
    ri_inv HI (own ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PMSAX.vec_pre segs M v b k stk own -> ((own = [] \/ Z.of_nat (length stk) = 2 ^ k) -> k <= 10) ->
    cells FF sp v M R c ->
    ((own = [] \/ Z.of_nat (length stk) = 2 ^ k) -> acredit_ok L cr (32 * 2 ^ (if Z.eqb b 0 then 0 else k + 1))) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (b' k' : Z) (cr' : credit),
        regs_preserved R R' -> PM.vec_at segs PMSPA.accA PMSPA.annA M' v b' k' (stk ++ [c]) -> PMSPA.accA M' v 24 ->
        PMSAX.push_out L false b k stk own b' k' cr cr' -> A0 R' b' (stk ++ [c]) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PM.vec_own b' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition Qcone : Z -> Z -> list PM.pstate -> list (Z * Z) -> Prop := fun b k stk own => own = PM.vec_own b k /\ Z.of_nat (length stk) < 2 ^ k.
Definition A0none : bvmap 5 word -> Z -> list PM.pstate -> Prop := fun _ _ _ => True.

Definition Qslow : Z -> Z -> list PM.pstate -> list (Z * Z) -> Prop := fun b k stk own => own = [] \/ Z.of_nat (length stk) = 2 ^ k.
Definition A0end : bvmap 5 word -> Z -> list PM.pstate -> Prop := fun R' b' stk' => getr R' 10%bv = Z_to_bv 64 (b' + 32 * Z.of_nat (length stk')).

Lemma cone_pushq pc cells : PMSBX.cone_spec_at segs A L ar HI pc cells -> pushq_spec_at pc Qcone A0none cells.
Proof.
  intros CONE fx R M model K LBX FF LK Aw cr v b k stk own c sp r (Eown & Hlen) HH AM K0 ENT FRS A10 AOB V8 ACC VP K10 CELLS CRD NEXT.
  subst own.
  assert (VA : PM.vec_at segs PMSPA.accA PMSPA.annA M v b k stk).
  { destruct VP as [(_ & _ & _ & _ & _ & _ & E)|(VA & _)]; [discriminate E| exact VA]. }
  apply (CONE fx R M model K LBX FF LK Aw cr v b k stk c sp r HH AM K0 ENT FRS A10 AOB V8 ACC VA Hlen CELLS).
  intros fx' R' M' model' LK' Aw' RP VA' ACC' HP MRT ILK IAW AM' HH'.
  apply (NEXT fx' R' M' model' LK' Aw' b k cr RP VA' ACC'); try assumption.
  - left. split; [discriminate|]. split; [exact Hlen|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - exact I.
Qed.

Lemma slow_pushq pc cells : PMSBX.slow_spec_at segs A L ar HI pc cells -> pushq_spec_at pc Qslow A0end cells.
Proof.
  intros SLOW fx R M model K LBX FF LK Aw cr v b k stk own c sp r HQ HH AM K0 ENT FRS A10 AOB V8 ACC VP K10 CELLS CRD NEXT.
  apply (SLOW fx R M model K LBX FF LK Aw cr v b k stk own c sp r HH AM K0 ENT FRS A10 AOB V8 ACC VP HQ (K10 HQ) CELLS (CRD HQ)).
  intros fx' R' M' model' LK' Aw' b' k' cr' RP VA' ACC' Ek Ecr A0' HP MRT ILK IAW AM' HH'.
  apply (NEXT fx' R' M' model' LK' Aw' b' k' cr' RP VA' ACC'); try assumption.
  right. split; [exact HQ|]. split; [exact Ek| exact Ecr].
Qed.

Lemma rdn_nth (M : word -> option byte) : forall (n : nat) a bs, rdn segs M (Z_to_bv 64 a) n = Some bs ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) <> None -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs E i Hi D; [lia|].
  cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
  - rewrite L5C.add1_lit in E. destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. exact Ea.
    + cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
  - destruct i as [|i]; [rewrite Z.add_0_r in D; exfalso; apply D; exact Ea|].
    destruct (seg_rom segs (Z_to_bv 64 a)) as [y|]; [|discriminate E]. rewrite L5C.add1_lit in E.
    destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
Qed.
Lemma u64_same_agree M M1 a v : 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at segs M a v -> L5.u64_at segs M1 a v -> L5.defined M a 8 -> L5.defined M1 a 8 ->
  forall i, a <= i < a + 8 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros H1 H2 U U1 D D1 i Hi. unfold L5.u64_at in U, U1.
  pose proof (rdn_nth M 8 a _ U (Z.to_nat (i - a)) ltac:(lia)) as E.
  pose proof (rdn_nth M1 8 a _ U1 (Z.to_nat (i - a)) ltac:(lia)) as E1.
  rewrite Z2Nat.id in E, E1 by lia. replace (a + (i - a)) with i in E, E1 by lia.
  assert (Di : M (Z_to_bv 64 i) <> None) by (replace i with (a + (i - a)) by lia; apply D; lia).
  assert (Di1 : M1 (Z_to_bv 64 i) <> None) by (replace i with (a + (i - a)) by lia; apply D1; lia).
  rewrite (E Di), (E1 Di1). reflexivity.
Qed.

End Specs.
End PMBPQ.

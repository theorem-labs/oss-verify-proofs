(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
L5KnA L5LazyA L5DefsA L5CoreA PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsBX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBPushQ () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBPushQ.PMBPQ.Specs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMSBX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2not"; "3lt"; "4Z"; "0HI"; "0L"; "5bvmap"; "0M"; "0M1"]; ["6fframe"; "7defined"; "7u64_at"; "8A0end"; "8A0none"; "8Qcone"; "8Qslow"; "8pushq_spec_at"; "9pstate"; ":cone_spec_at"; ":slow_spec_at"; ";rdn"; "0SCFG_P"; "<nth_error"; "=add"; "=le"]; ["=lt"; "=of_nat"; "=pow"; "0a"; "0ar"; "0bs"; "0cells"; "0i"; "0n"; "0pc"; "0segs"; ">Z_to_bv"; ">bv"; "0v"]]).
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
Lemma cone_pushq : ltac2:(TCodec.tc2 tcn__PmBPushQ "Q9':'3&@%211'Q<yR0%211'5y8%511%311p051&=y5%2218'H!p021p041p081p0D1p0E1p0C1&IvLvQ:v0v<vQ4v;r2r1%9887654321&Gr3&E&D%443217p061pR>A1pRDQ81").
Proof. intros pc cells.
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
Lemma slow_pushq : ltac2:(TCodec.tc2 tcn__PmBPushQ "Q9':'3&@%211'Q<yR0%211'5y8%511%311p051&=y5%2218'H!p021p041p081p0D1p0E1p0C1&JvLvQ:v0v<vQ4v;r2r1%9887654321&Gr3&F&C%443217p061pR>A1pRDQ81").
Proof. intros pc cells.
intros SLOW fx R M model K LBX FF LK Aw cr v b k stk own c sp r HQ HH AM K0 ENT FRS A10 AOB V8 ACC VP K10 CELLS CRD NEXT.
apply (SLOW fx R M model K LBX FF LK Aw cr v b k stk own c sp r HH AM K0 ENT FRS A10 AOB V8 ACC VP HQ (K10 HQ) CELLS (CRD HQ)).
intros fx' R' M' model' LK' Aw' b' k' cr' RP VA' ACC' Ek Ecr A0' HP MRT ILK IAW AM' HH'.
apply (NEXT fx' R' M' model' LK' Aw' b' k' cr' RP VA' ACC'); try assumption.
right. split; [exact HQ|]. split; [exact Ek| exact Ecr].
Qed.
Lemma rdn_nth : ltac2:(TCodec.tc2 tcn__PmBPushQ "QJ'Q<yR0%211'5y8%511%311p051'4':'3%116'7%:12&KvQ:r4&Q;r2%22B1r3%746521(2r1%22=1%=3<41&9r5%2251&8r7&N&Q1%11?%3271%B2Q21%611(1%11Q1%K3Q131%;11r8r6%;1G%=221%L2Q<1%511&M%13Q;EL%Q53Q;31p0:1p0G1pR@Q<1p0L1pR<Q;1pR8Q>1pRBQ@1pNQB1").
Proof. intros M.
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
Lemma u64_same_agree : ltac2:(TCodec.tc2 tcn__PmBPushQ "QN'Q<yR0%211'5y8%511%311p051':&Ozr2%3221&Nr3+8%3221&Q2+2+R0%3221%<251&BvQ:r6r4%44321<r5%645413&Ar8%2317@r7%4331B'6r9r1%L221&Q0%J24H%2241%7241'7r;&Q;%12Q<Q2%311r<%113%73Q;31p091pR@Q;1p0C1p0F1p0J1p0M1p0Q31p0Q=1pRLQB1pR8QC1pQ0QE1pNQF1").
Proof. intros M M1 a v.
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

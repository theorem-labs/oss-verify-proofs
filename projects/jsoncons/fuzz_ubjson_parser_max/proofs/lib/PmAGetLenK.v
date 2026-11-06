(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAGlP1 PmAGlP2 PmAGlP3 PmAGlP4 PmAGlP5
Ja0_code_b02e8_b02ec Ja0_code_aff7c_aff80.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAGetLenK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAGetLenK.PMAGLK."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2and"; "2eq"; "2or"; "3Z"; "0E"; "0F"; "4bvmap"; "0M"; "0M1"; "0M1'"; "0R"; "5aacc"; "5byte_at"; "6XS"; "6XVU"]; ["6ocell"; "6orun"; "6own"; "6zrun"; "7add"; "7div"; "7le"; "7modulo"; "7mul"; "7pow"; "7sub"; "0a"; "0k"; "0off"; "8Z_to_bv"; "8bv"]; ["0v"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMAGLK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
/\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
/\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
/\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
/\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
/\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26))).
Definition ocell (E : Z) (a : Z) : Prop := E - 96 <= a < E.
Lemma own_agree : ltac2:(TCodec.tc2 tcn__PmAGetLenK "QD'4&7y5'OyR0%211%5241'0y8%611%311p061pR472&Fz&Jr4+S0%3221%6251r5&I+2+R0%3221%<251&Br6%2318<&@r8r1%3221'2&Nr2%22Q01%:11r7%113%73N31p091pQHQ:1%A3=5Gp021p0A1p0E1p0L1pFQ41pDQ61pHQ<1p<QC1").
Proof. intros E R M1 M1'.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold own, ocell in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Lemma aacc_local : ltac2:(TCodec.tc2 tcn__PmAGetLenK "R2'OyR0%211'0y8%511%311p051'4'2&H&Er4+8%3221%5212%73814&G%1265z%;3<21&Fr5%2241r7%4261'3'1r6%D3E1@%E3F8;%4221+1%<215+7%>271%9231%L3M?9%;221%=281&=r:&Dr9%Q121Or8%Q321Q1%5231+QoooPP0%7221%:391F&<r;%;2<:%33219p051p0A1p0Q01p0Q31p0Q71p0Q<1pR2QE1pQJQF1pQLQG1p>QH1pBQJ1").
Proof. intros M F off k v.
intros F8 O8 O0 F0 Hk B a Ha. unfold S, SB.
assert (E : a / 8 = F / 8 + off / 8) by (destruct Hk as [(-> & _)|(Hk & _)]; lia).
rewrite E. destruct Hk as [(-> & ->)|(Hk & ->)]; [left; exact B| right; exists k; split; [exact B| split; [exact Hk| lia]]].
Qed.
Definition zrun (pc0 : Z) : Prop :=
forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op oec F fl : Z),
0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F ->
getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 (op + 24) ->
getr R (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 F -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 -> 6885376 <= op <= 140737488354944 ->
op mod 8 = 0 -> (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 -> L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 ->
L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M op 384 -> ((E - 128) + 128 <= op \/ op + 384 <= (E - 128)) ->
6885376 <= F <= 140737488355072 -> F mod 32 = 0 -> L5.defined M F 256 -> L5.writable RSEGS M F 256 -> (2147446784 + 17592186048512 <= F \/ F + 256 <= 2147446784) ->
L5.writable RSEGS M ((F / 8) + 2147450880) 32 -> L5.u64_at RSEGS M (F + 248) fl -> 4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 ->
(2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) -> (F + 256 <= fl \/ fl + 1 <= F) -> ((E - 128) + 128 <= F \/ F + 256 <= (E - 128)) ->
((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) -> (op + 384 <= F \/ F + 256 <= op) -> (op + 384 <= fl \/ fl + 1 <= op) ->
(((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 32 <= ((op / 8) + 2147450880)) ->
own E R0 M ->
exists fx' R' M', mem_grows M M'
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 32) -> i <> fl ->
M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb02e8) M' (seg_rom RSEGS))
/\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
/\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
/\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0 /\ L5.u8_at RSEGS M' (op + 8) 0.
Ltac bvr R0 := pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))); pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8)));
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))); pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18)));
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))); pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20)));
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))); pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22)));
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))); pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24)));
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 25))); pose proof (bv_unsigned_in_range 64 (getr R0 (reg 26)));
change (bv_modulus 64) with (2 ^ 64) in *.
Ltac zrun_tac Z_conc :=
intros fx R R0 M E op oec F fl; intros; bvr R0;
match goal with OW : own _ _ _ |- _ => destruct OW as (?S8 & ?S16 & ?S24 & ?S32 & ?S40 & ?S48 & ?S56 & ?S64 & ?S72 & ?S80 & ?S88 & ?S96) end;
let P := fresh "P" in
pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
| 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
| 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
| 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
cbn beta iota in P;
L5SAR.feed P ltac:(first [assumption | unfold PMAGL5.aligned; assumption]);
let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
& _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ?MO0 & _);
exists fx', R', M';
split; [assumption|];
split; [intros i Hi N1 N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
[exact Hi| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia| intros X; apply N1; lia]|];
split; [assumption|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
split; [assumption|]; split; assumption.
Lemma zi_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+eonH%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZiR_conc. Qed.
Lemma zT_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+fPP<%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZTR_conc. Qed.
Lemma zD_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+fP\L%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZDR_conc. Qed.
Lemma zl_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+fPgL%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZlR_conc. Qed.
Lemma zL_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+fPiH%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZLR_conc. Qed.
Lemma zU_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+fPk<%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZUR_conc. Qed.
Lemma zI_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "3&C+fPm0%211"). Proof. unfold zrun. zrun_tac PMAGL5.aglZIR_conc. Qed.
Definition orun (pc0 : Z) (X : bvmap 5 word -> (word -> option byte) -> Z -> Prop) : Prop :=
forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op oec F fl : Z),
X R M F ->
0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F ->
getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 (op + 24) ->
getr R (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 F -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 ->
6885376 <= F <= 140737488355072 -> F mod 32 = 0 -> L5.defined M F 256 -> L5.writable RSEGS M F 256 -> (2147446784 + 17592186048512 <= F \/ F + 256 <= 2147446784) ->
L5.writable RSEGS M ((F / 8) + 2147450880) 32 -> L5.u64_at RSEGS M (F + 248) fl -> 4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 ->
(2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) -> (F + 256 <= fl \/ fl + 1 <= F) -> ((E - 128) + 128 <= F \/ F + 256 <= (E - 128)) ->
((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) ->
own E R0 M ->
exists fx' R' M', mem_grows M M'
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 32) -> i <> fl ->
M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb02e8) M' (seg_rom RSEGS))
/\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
/\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
/\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0.
Ltac orun_fin :=
let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
match goal with P : exists _ _ _, _ |- _ =>
destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
& _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) end;
exists fx', R', M';
split; [assumption|];
split; [intros i Hi N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
[exact Hi| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia]|];
split; [assumption|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
split; assumption.
Definition XVU (R : bvmap 5 word) (M : word -> option byte) (F : Z) : Prop :=
getr R (reg 10) = Z_to_bv 64 1 /\ getr R (reg 22) = Z_to_bv 64 (F + 64) /\ L5.defined M (F + 64) 1.
Definition XS (o22 o23 : Z -> Z) (R : bvmap 5 word) (M : word -> option byte) (F : Z) : Prop :=
exists v, 0 <= v <= 9223372036854775807 /\ getr R (reg 10) = Z_to_bv 64 v /\ getr R (reg 22) = Z_to_bv 64 (o22 F) /\ getr R (reg 23) = Z_to_bv 64 (o23 F).
Ltac orun_open Z_conc v fx R R0 M E op oec F fl :=
intros; bvr R0;
match goal with OW : own _ _ _ |- _ => destruct OW as (?S8 & ?S16 & ?S24 & ?S32 & ?S40 & ?S48 & ?S56 & ?S64 & ?S72 & ?S80 & ?S88 & ?S96) end;
let P := fresh "P" in
pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => v
| 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
| 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
| 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
| 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
cbn beta iota in P;
L5SAR.feed P ltac:(first [assumption | unfold PMAGL3.aligned; assumption | lia]).
Lemma vu_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "4&A+fPW@&?%3221").
Proof. unfold orun. intros fx R R0 M E op oec F fl XX. destruct XX as (X10 & X22 & XD). revert X10 X22 XD. orun_open PMAGL3.aglVUR_conc 0 fx R R0 M E op oec F fl. orun_fin. Qed.
Lemma si_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "=&A+eon4&>'4+1q021&Dr1+Q@%3221q>71%9261%<2;1").
Proof. unfold orun. intros fx R R0 M E op oec F fl XX. destruct XX as (v & Hv & X10 & X22 & X23). revert Hv X10 X22 X23. orun_open PMAGL3.aglSiP_conc v fx R R0 M E op oec F fl. orun_fin. Qed.
Lemma sl_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "=&A+fPZ<&>'4+4q021&Dr1+S0%3221q>71%9261%<2;1").
Proof. unfold orun. intros fx R R0 M E op oec F fl XX. destruct XX as (v & Hv & X10 & X22 & X23). revert Hv X10 X22 X23. orun_open PMAGL3.aglSlP_conc v fx R R0 M E op oec F fl. orun_fin. Qed.
Lemma sI_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "=&A+fP\4&>'4&Dr1+R@%3221q>51+2q071%9231%<2;1").
Proof. unfold orun. intros fx R R0 M E op oec F fl XX. destruct XX as (v & Hv & X10 & X22 & X23). revert Hv X10 X22 X23. orun_open PMAGL3.aglSIP_conc v fx R R0 M E op oec F fl. orun_fin. Qed.
Lemma sL_run : ltac2:(TCodec.tc2 tcn__PmAGetLenK "=&A+fPV8&>'4&Dr1+S@%3221q>51+8q071%9231%<2;1").
Proof. unfold orun. intros fx R R0 M E op oec F fl XX. destruct XX as (v & Hv & X10 & X22 & X23). revert Hv X10 X22 X23. orun_open PMAGL3.aglSLP_conc v fx R R0 M E op oec F fl. orun_fin. Qed.
End PMAGLK.

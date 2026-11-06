(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmASrcRead1 PmAParKit PmAReset1 PmAUarK PmAUar PmARdKeyP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARdKey () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARdKey.PMARDK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2eq"; "3Z"; "0E"; "0HI"; "0L"; "4bvmap"; "0M1"; "0M1'"; "0R"; "5krun"; "5ocell"; "5own"; "5zrun"; "6get_length_spec"; "6make_ec_spec"]; ["6read_key_spec"; "6read_span_spec"; "6validate_spec"; "0SCFG_P"; "7le"; "7pow"; "7sub"; "0a"; "0ar"; "8Z_to_bv"; "8bv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMARDK.
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
Lemma own_agree : ltac2:(TCodec.tc2 tcn__PmARdKey "QD'2&6y5'JyR0%211%5241'0y8%611%311p061pQH72&Dz&Fr4+S0%3221%6251r5&E+2+R0%3221%<251&<r6%2318<&;r8r1%3221'1&Ir2%22Q01%:11r7%113%73N31p091pQ@Q:1%A3=5Gp021p0A1p0E1p0L1pBQ41p@Q61pDQ<1p8QC1").
Proof. intros E R M1 M1'.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold own, ocell in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Definition zrun (pc0 : Z) : Prop :=
forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op ov oec F fl : Z),
0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 1))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 8))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 9))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 18))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 19))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 20))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 21))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 22))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 23))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 24))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 25))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 26))) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F -> getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 24) = Z_to_bv 64 F -> getr R (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 -> 6885376 <= op <= 140737488354944 ->
op mod 8 = 0 -> (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 -> L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 ->
L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M op 384 -> ((E - 128) + 128 <= op \/ op + 384 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
(op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> 6885376 <= F <= 140737488355264 -> F mod 32 = 0 ->
L5.defined M F 64 -> L5.writable RSEGS M F 64 -> (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) -> L5.writable RSEGS M ((F / 8) + 2147450880) 8 ->
L5.u64_at RSEGS M (F + 56) fl -> 4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) ->
(F + 64 <= fl \/ fl + 1 <= F) -> ((E - 128) + 128 <= F \/ F + 64 <= (E - 128)) -> ((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
(op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R0 (reg 1))) -> L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R0 (reg 8))) ->
L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R0 (reg 9))) -> L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R0 (reg 19))) -> L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R0 (reg 20))) ->
L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R0 (reg 21))) -> L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R0 (reg 23))) -> L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R0 (reg 24))) ->
L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R0 (reg 25))) -> L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R0 (reg 26))) ->
exists fx' R' M', mem_grows M M'
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 8) -> i <> fl ->
M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xaeea4) M' (seg_rom RSEGS))
/\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
/\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
/\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0 /\ L5.u8_at RSEGS M' (op + 8) 0.
Ltac zrun_tac Z_conc :=
intros fx R R0 M E op ov oec F fl; intros;
let P := fresh "P" in
pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
| 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
| 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
| 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
cbn beta iota in P;
L5SAR.feed P ltac:(first [assumption | unfold PMARKP.aligned; assumption]);
let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
& _ & _ & _ & _ & _ & _ & _ & _ & _ & ?MO0 & _);
exists fx', R', M';
split; [assumption|];
split; [intros i Hi N1 N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
[exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia]|];
split; [assumption|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
split; [assumption|]; split; assumption.
Lemma z1_run : ltac2:(TCodec.tc2 tcn__PmARdKey "3&=+ek_D%211"). Proof. unfold zrun. zrun_tac PMARKP.arkZ1_conc. Qed.
Lemma z7_run : ltac2:(TCodec.tc2 tcn__PmARdKey "3&=+ek^8%211"). Proof. unfold zrun. zrun_tac PMARKP.arkZ7_conc. Qed.
Lemma z12_run : ltac2:(TCodec.tc2 tcn__PmARdKey "3&=+ekj<%211"). Proof. unfold zrun. zrun_tac PMARKP.arkZ12_conc. Qed.
Definition krun : Prop :=
forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op ov oec F fl : Z),
0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 1))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 8))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 9))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 18))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 19))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 20))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 21))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 22))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 23))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 24))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 25))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 26))) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F -> getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 ov -> getr R (reg 24) = Z_to_bv 64 F -> getr R (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 -> 6885376 <= op <= 140737488354944 ->
op mod 8 = 0 -> (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 -> L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 ->
L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M op 384 -> ((E - 128) + 128 <= op \/ op + 384 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
(op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> 6885376 <= F <= 140737488355264 -> F mod 32 = 0 ->
L5.defined M F 64 -> L5.writable RSEGS M F 64 -> (2147446784 + 17592186048512 <= F \/ F + 64 <= 2147446784) -> L5.writable RSEGS M ((F / 8) + 2147450880) 8 ->
L5.u64_at RSEGS M (F + 56) fl -> 4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) ->
(F + 64 <= fl \/ fl + 1 <= F) -> ((E - 128) + 128 <= F \/ F + 64 <= (E - 128)) -> ((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) -> (op + 384 <= F \/ F + 64 <= op) ->
(op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 8 <= ((op / 8) + 2147450880)) -> L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R0 (reg 1))) -> L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R0 (reg 8))) ->
L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R0 (reg 9))) -> L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R0 (reg 19))) -> L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R0 (reg 20))) ->
L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R0 (reg 21))) -> L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R0 (reg 23))) -> L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R0 (reg 24))) ->
L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R0 (reg 25))) -> L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R0 (reg 26))) -> L5.u8_at RSEGS M (op + 16) 0 ->
exists fx' R' M', mem_grows M M'
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (op + 8 <= i < op + 9) -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 8) -> i <> fl ->
M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0xaeef8) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xaeea4) M' (seg_rom RSEGS))
/\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
/\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
/\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0 /\ L5.u8_at RSEGS M' (op + 8) 1.
Ltac krun_tac Z_conc :=
intros fx R R0 M E op ov oec F fl; intros;
let P := fresh "P" in
pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
| 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
| 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
| 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
cbn beta iota in P;
L5SAR.feed P ltac:(first [assumption | unfold PMARKP.aligned; assumption]);
let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & _ & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
& _ & _ & _ & _ & _ & _ & _ & _ & _ & ?MO0 & _);
exists fx', R', M';
split; [assumption|];
split; [intros i Hi N1 N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
[exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia]|];
split; [assumption|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
split; [assumption|]; split; assumption.
Lemma k2_run : ltac2:(TCodec.tc2 tcn__PmARdKey "1&:"). Proof. unfold krun. krun_tac PMARKP.arkK2_conc. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Theorem read_key_ok : ltac2:(TCodec.tc2 tcn__PmARdKey "B&>vCv5vHv4%544321&A%146543&B%148765&?%14:987&@%14<;:9p031p061p091p0<1").
Proof.
intros GL RS VAL MKE. unfold PMA.read_key_spec, PMSPA.read_key_spec, PMSPA.run_spec, PMSPA.run_spec_r.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11 & A12).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 26624 HH FOK IA ASTK) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI & IOS).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 26624 128 HH ASTK ltac:(lia)) as (SL128 & SH128 & SWR).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *. set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
cfeed P (PMARKP.arkA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PMARKP.aligned; assumption | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - O1 Eop Eov; lia | clear - O1 Eop Eoec; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T19 & T20 & T21 & T26
& C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
unfold PMSPA.cfg. cbn [pa_read_key PMA.AD ADDR_A].
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xaec6c R1 0x5d22c M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
set (LB := PM.parser_own s ++ LBX) in *.
assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 26624 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH SPT Hc) as [Y|Y].
- clear - Xa Y; lia.
- clear - Xa Y SL128; lia. }
assert (EK01f : L5SAR.ek L ar LB FF sp 26624 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
assert (DK01f : L5SAR.dk L ar LB FF sp 26624 M M1) by (apply L5SAR.dk_grows; exact MGM1).
pose proof (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M1 INCX EK01f) as EK01.
pose proof (PMKA.dk_sublb L ar LB LBX FF sp 26624 M M1 INCX DK01f) as DK01.
assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. exact X. }
assert (OWN1 : own sp R M1).
{ unfold own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
split; [apply SV1; [clear; lia| clear; lia| exact C88]|]. apply SV1; [clear; lia| clear; lia| exact C96]. }
clear C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C128 SV1.
assert (FRk0 : ff_room 0 FF LK) by (apply (PMAUAR.ff_room_of 7 FF LK 0 FRM); [clear; lia| left; reflexivity]).
change 0x5d22c with (PMA.SM_PC 0).
apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PM.parser_own s) FF LK cr Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R)
fx1 R1 M M1 model model1 K 0xaece0 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. exact T2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1. }
{ reflexivity. }
{ clear; lia. }
{ replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
{ exact FRk0. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 0) with 64 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M1 M2 EK01f EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 26624 M M1 M2 DK01f DK12f) as DK02f.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (HH2 : ri_inv HI LB ((F, 0, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
set (FF' := (F, 0, sp - 128 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 0 (sp - 128 + 32) FOK).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 26624 128 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
{ intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
assert (B21R : getr R2 (reg 21) = Z_to_bv 64 ov) by (rewrite (R2c 21%nat) by inl; exact T21).
assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= ois < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
by (clear - SL128 SHI SPT O1 Eop Eov Eoec Eois GFR GFLR; lia).
destruct Q0 as (Q0a & Q0b & Q0c & Q0d & Q0e & Q0f & Q0g).
assert (Q1 : 140735332487296 <= sp <= 140737488355328) by (clear - SL128 SHI SPT; lia).
assert (Q3 : 6885376 <= F <= 140737488355264) by (clear - GFR; lia).
assert (Q4 : (sp - 128) + 128 <= F \/ F + 64 <= (sp - 128)) by (clear - GFCEIL SL128; lia).
assert (Q5 : (sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128)) by (clear - GFLR SL128; lia).
assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
cfeed P (PMARKP.arkB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMARKP.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & _ & _ & Y18 & Y24 & Y25 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YD).
set (W3 := fun a => (sp - 104 <= a < sp - 104 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8)).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xaece0 R3 0xafe2c M3v W3 K HH2 AM2 MS3 MG3).
{ intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; left; clear - X; lia| intros X; apply Hn; right; right; clear - X; lia]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|X]].
+ unfold aclientw, aclient_g. right; left. split; [clear - X SL128 SHI SPT; lia| intros Y; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
- destruct Wa as [X|[X|X]]; clear - X GFR SL128 SPT; lia. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23f : L5SAR.ek L ar LB FF sp 26624 [] M2 M3).
{ apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
- apply (NCS0 a); [clear - X; lia| exact Hc].
- destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
- destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M2 M3 EK02f EK23f) as EK03f.
assert (OWN3 : own sp R M3).
{ apply (own_agree sp R M1 M3 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL128 SHI SPT; lia| intros [X|[X|X]]; clear - X Ha GFCEIL GFR SL128 SPT; unfold SB in *; lia]. }
assert (WAPPR : PMKA.wapp (PMSPA.W_run PMA.AD fb)).
{ unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
set (WR := PMSPA.W_run PMA.AD fb) in *.
assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s) M3 model3 LK2 cr Aw).
{ unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 26624 ASTK2 MGM3)|].
split; [apply (L5SAR.ek_W L ar LBX FF sp 26624 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M3 INCX EK03f)); intros a _ r0 []|].
split; [apply (L5SAR.dk_trans L ar LBX FF sp 26624 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
split; [exact OWN3|].
change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 26624 WR M Mc -> sp - 26624 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
{ intros Mc lo g EKc H1' H2' H3' H4'. apply (PMKA.stksh_keepA L ar LBX FF sp 26624 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
apply (PMKA.shadow_zero_sub M (sp - 26624) 3328); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
apply PMKA.mod16_8'. replace (sp - 26624) with (sp + (-1664) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
assert (ASTK3 : L5CA.astk ar M3 sp 26624) by exact (L5SAR.astk_grows ar M2 M3 sp 26624 ASTK2 MGM3).
assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [clear - X1 X2 Hi; lia| intros Y; clear - X1 X2 Hi Y; lia]. }
destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & AiSF & AiFL).
assert (CLsh : forall a n, fb / 8 + SB <= a -> a + n <= fb / 8 + SB + 128 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 5 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. unfold in_shadow_of, S. unfold SB in *.
assert (D1 : (fb + 1024 - 1) / 8 = fb / 8 + 127).
{ pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 1024 - 1) with (7 + (128 * (fb / 1024) + 127) * 8) by (clear; lia). rewrite Z.div_add by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
rewrite D1. clear - X1 X2 Hi. lia. }
assert (SHop : op / 8 + SB = fb / 8 + SB + 58).
{ rewrite Eop. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 464) with ((128 * (fb / 1024) + 58) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
assert (SHis : ois / 8 + SB = fb / 8 + SB + 12).
{ rewrite Eois. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 96) with ((128 * (fb / 1024) + 12) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(clear - SHop; lia) ltac:(clear - SHop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
unfold SB in ApSF, AsopSF.
assert (R1c : forall j, In j [3; 4; 22; 23; 24; 25; 27]%nat -> getr R1 (reg j) = getr R (reg j)).
{ intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 22; 23; 24; 25; 27]%nat). vm_compute. reflexivity. }
assert (ERRP : forall (pcz v : Z) (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (LK5 : list fframe) (Aw5 : list (Z * Z))
(cr5 : credit) (s5 : PM.pst) (sm5 : PM.strm) (e5 : bool) (v0 c0 : Z),
zrun pcz -> L5.ra_ok pcz -> 1 <= v <= 64 ->
PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s5) M5 model5 LK5 cr5 Aw5 ->
PMSPA.run_pre RSEGS PMA.AD PMA.AAD M5 fb s5 str sm5 e5 -> PMSPA.ec_at RSEGS M5 oec v0 c0 ->
PMSPA.src_step (PM.p_src s) (PM.p_src s5) sm sm5 -> (e = true -> e5 = true) ->
PMSPA.credit_keep cr cr5 (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s5)) ->
getr R5 (reg 1) = Z_to_bv 64 pcz -> getr R5 (reg 10) = Z_to_bv 64 oec -> getr R5 (reg 11) = Z_to_bv 64 v ->
getr R5 (reg 2) = Z_to_bv 64 (sp - 128) -> getr R5 (reg 8) = Z_to_bv 64 sp -> getr R5 (reg 9) = Z_to_bv 64 (sp - 128) ->
getr R5 (reg 18) = Z_to_bv 64 F -> getr R5 (reg 19) = Z_to_bv 64 op -> getr R5 (reg 20) = Z_to_bv 64 oec -> getr R5 (reg 21) = Z_to_bv 64 ov ->
getr R5 (reg 24) = Z_to_bv 64 F -> getr R5 (reg 25) = Z_to_bv 64 (F / 8 + 2147450880) -> getr R5 (reg 26) = Z_to_bv 64 2147450880 ->
(forall j, In j [3; 4; 27]%nat -> getr R5 (reg j) = getr R (reg j)) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx5 R5 0xae974 M5 model5) K).
{ intros pcz v fx5 R5 M5 model5 LK5 Aw5 cr5 s5 sm5 e5 v0 c0 ZR RApc Hv BI5 RP5 EC5 ST5 EE5 CK5 J1 J10 J11 J2 J8 J9 J18 J19 J20 J21 J24 J25 J26 J34.
destruct RP5 as (PA5 & IA5 & VIS5 & VREF5 & BASE5 & ERR5 & TB5).
pose proof BI5 as (HH5 & AM5 & _ & _ & _ & ASTK5 & EKb5 & _).
pose proof EC5 as (_ & _ & ECD5 & ECA5).
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH5) as BRB5.
unfold PMA.make_ec_spec, PMSPA.make_ec_spec in MKE.
apply (MKE fx5 R5 M5 model5 K (PM.parser_own s5 ++ LBX) FF' LK5 Aw5 cr5 oec v (sp - 128) pcz e5 HH5 AM5 K0).
{ split; [rewrite L5K.rl1; exact J1|]. split; [exact RApc|]. split; [rewrite L5K.rl2; exact J2|].
split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
split; [apply (L5SAR.astk_sub ar M5 M5 sp 26624 128 14336 ASTK5 (mem_grows_refl M5)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact EKb5| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
pose proof BI5 as (_ & _ & _ & _ & INCL5 & _).
apply (PMAUAR.ffroomA_push 7 1 FF LK LK5 _ FRM INCL5); [exact NDF5| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
{ rewrite L5K.rl10. exact J10. }
{ rewrite L5K.rl11. exact J11. }
{ exact Hv. }
{ apply PMAUAR.aobjA_push. apply AOF; clear - Eoec; lia. }
{ rewrite Eoec. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by (clear; lia). apply Z_mod_mult. }
{ exact ECD5. }
{ exact ECA5. }
{ exact BASE5. }
{ exact ERR5. }
intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
change (PMSPA.pm_scr 1) with 14336 in HP6.
set (Wc6 := (oec, 16) :: (if e5 then [] else PMSPA.err_W PMA.AD)) in HP6.
assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct e5; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s5) M6 model6 LK6 cr5 Aw6).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s5) (PM.parser_own s5) (PM.parser_own s5) M5 model5 LK5 cr5 Aw5 M6 model6 LK6 cr5 Aw6 14336 Wc6 BI5 HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
[clear; lia| clear; lia| | | intros a X; exact X].
- intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
destruct (Wc6R rr a Hin Hr) as [X|X]; (split; [clear - X OCE SL128 SPT Eop Eoec F2 FSCEIL; lia|]).
+ destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2 Eoec; lia.
+ clear - X DF1; lia.
- intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X].
+ apply (Ho (PMSPA.o_ec PMA.AD fb, 16)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng; fold oec; cbn [fst snd]; clear - X; lia].
+ unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W in Ho. cbn [app pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Ho.
unfold Wc6, PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin.
destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X Eoec O1 Eop; lia|].
destruct e5; [destruct Hin|]. destruct Hin as [<-|[<-|[]]].
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact Hr.
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))); exact Hr. }
pose proof (L5SAR.ek_callee L ar (PM.parser_own s5 ++ LBX) [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 14336 Wc6 Wc6 M5 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK56.
assert (WAPP6 : PMKA.wapp Wc6).
{ intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
- pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - Y F1 F2 Eoec; lia.
- destruct e5; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
assert (OUT6 : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside Wc6 i).
{ intros a n X1 X2 X3 i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [clear - Hi Y X3; lia| clear - Hi Y X1 Eop O1; lia]. }
assert (OUTB6 : forall q m, In (q, m) (PM.parser_own s5 ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wc6 i).
{ intros q m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH5 Hq (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z|Z]; clear - Hi Y Z; lia.
- pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH5 Hq) as Z. destruct Z as [Z|Z]; clear - Hi Y Z; lia. }
assert (PA6 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M6 op ois s5).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF sp 26624 Wc6 M5 M6 EK56 WAPP6 FRB BRB5 _ _ _ AOP); [| | | | | exact PA5].
- apply incl_appl, incl_refl.
- apply OUT6; clear - Eop Eoec; lia.
- unfold PMKA.blk_out. apply OUTB6. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
- unfold PMKA.blk_out. apply OUTB6. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
- intros c0' n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity. }
assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm5).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF sp 26624 Wc6 M5 M6 EK56 WAPP6 FRB BRB5 ois str sm5 AOI); [| | | exact IA5].
- apply incl_appr. exact INCS.
- apply OUT6; clear - Eois Eoec; lia.
- intros c0' n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
assert (VIS6 : PMSPA.visitor_at RSEGS PMA.AD M6 ov).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF sp 26624 Wc6 M5 M6 EK56 WAPP6 FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS5].
apply OUT6; clear - Eov Eoec; lia. }
assert (VREF6 : L5.u64_at RSEGS M6 (op + 384) ov).
{ apply (PMKA.u64_keepA RSEGS L ar (PM.parser_own s5 ++ LBX) FF sp 26624 Wc6 M5 M6 EK56 WAPP6 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF5].
apply OUT6; clear - Eop Eoec; lia. }
assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
{ apply (PMAPAR.base_keepW L ar C LY (PM.parser_own s5 ++ LBX) FF sp 26624 Wc6 M5 M6 EK56); [| | | | exact BASE5].
- intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X]; [clear - Ha X Eoec O1 Eop; lia|].
unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e5; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
- intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e5; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
- intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct e5; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
- intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e5; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia. }
set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s5) M6 model6 LK6 cr5 Aw6 BI6) as ((WS6 & _ & _ & _ & _) & OWN6 & (FD6 & FW6 & FSW6 & FLC6 & FLW6) & (FLCc6 & FLV6 & VF6 & VS6 & VSH6)).
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (sp - (sp - 128)) with 128 in WS6 by (clear; lia).
replace (F + 64 - 8) with (F + 56) in FLC6 by (clear; lia).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK6 cr5 Aw6 M6 model6 fb _ s5 HH6 FOK' PA6) as ((_ & _ & _) & Zop6 & Z326 & Z206 & OWR6 & _ & OVIS6 & _ & _).
assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R5 (reg j)).
{ intros j Hj. exact (L5SAR.cs_of_preserved R5 R6 j RP6 Hj). }
pose proof OWN6 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
change (bv_modulus 64) with (2 ^ 64) in *.
pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
destruct (ZR fx6 R6 R MV6 sp op ov oec F fl) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & K347 & REG7 & E72 & FL0 & MO0);
first [assumption | (rewrite R6c by inl; assumption) | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - GF1 GF2; lia
| clear - GL1 GL2; lia | clear - OCE SL128; lia | clear - GFCEIL SL128; lia | clear - GL4 SL128; lia | clear - Eop Eov Eoec O1; lia
| (replace (sp mod 32) with 0 by (symmetry; exact SP32); reflexivity) | exact SP32 | exact O8 | exact GF32 | idtac].
assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xaeea4 (ltac:(oW' 0xaeea4%Z)) r (ltac:(oF' 0xaeea4%Z)) eq_refl (ltac:(oD' 0xaeea4%Z)) R7ra Hr1 Hr2) as MSr.
apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s5) M6 model6 LK6 cr5 Aw6 (fun a => op + 8 <= a < op + 9) fx6 fx7 R6 pcz R7 r M7v K BI6).
{ intros a X. split.
- apply (L5SAR.fframe_client L ar (PM.parser_own s5 ++ LBX) FF' 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - X Eop; lia].
- intros O. apply (O (PMSPA.o_p PMA.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - X; lia]. }
{ intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X|X]; [left; exact X| right; exact X]. }
{ exact (msteps_trans _ _ _ _ MS7 MSr). }
{ exact MG7. }
{ intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
apply FRZ7; [exact Ha| intros X; apply Nw; right; clear - X; lia| intros X; apply Nw; left; left; left; clear - X; lia
| intros X; apply Nw; left; left; right; unfold SB; clear - X; lia| intros X; apply Nw; left; right; clear - X; lia]. }
{ exact FL0. }
intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict H6 Mf = M7v) in VISf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s5 ++ LBX) FF 0 0 [(op + 8, 1)] M6 Mf).
{ apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s5 ++ LBX) LK6 cr5 Aw6 M6 Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HH6).
- intros a X O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
- exact FZf. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6) as BRB6.
assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 0).
{ apply (proj1 (L5A.u8_at_vis H6 Mf (op + 8) 0 (OVIS6 (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VISf. exact MO0. }
pose proof BI6 as (_ & _ & _ & INCA6 & INCL6 & _).
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q m, In (q, m) (PM.parser_own s5 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(op + 8, 1)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH6 Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (Ivb : In (PM.p_b s5, 32 * 2 ^ PM.p_k s5) (PM.parser_own s5 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s5), PM.CHUNK) (PM.parser_own s5 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
apply (KONT fx7 R7 Mf modelf LK6 Aw6 (PMPK.set_more s5 0) sm5 true cr5).
- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl
| rewrite (K347 _) by inl; rewrite (R6c _) by inl; apply J34; inl ] |]).
destruct Hj.
- unfold PMSPA.run_post, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
+ destruct (BRB6 _ Iqc) as (Xq1 & Xq2). destruct (BRB6 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (PMAPAR.parser_more_updA M6 Mf op ois s5 0 PA6).
* clear - O1; lia.
* clear - O1; lia.
* apply (PMKA.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* apply (PMKA.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* exact (PMKA.agsh_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 384 AOP).
* pose proof PA6 as (_ & PD6 & _). apply (L5.defined_grows M6 Mf _ _ MGf PD6).
* exact MO0f.
* left; reflexivity.
* exact Xq1.
* clear - Xq2; lia.
* apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Iqc). apply OUTB8. exact Iqc.
* exact Xb1.
* clear - Xb2; lia.
* apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ivb). apply OUTB8. exact Ivb.
* intros c0' n0 p0 E0. assert (Ip : In (p0, c0') (PM.parser_own s5 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ip). apply OUTB8. exact Ip.
+ apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB BRB6 ois str sm5 AOI); [| | | exact IA6].
* apply incl_appr. exact INCS.
* apply OUT8. clear - Eop Eois; lia.
* intros c0' n0 p0 E0. unfold PMKA.blk_out. apply (OUTB8 p0 c0'). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
+ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS6].
apply OUT8. clear - Eop Eov; lia.
+ apply (PMKA.u64_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF6].
apply OUT8. clear; lia.
+ apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M6 Mf EKf); [| exact BASE6]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
+ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF 0 0 _ M6 Mf EKf true PMA.addrs_wf_A); [| exact ERR6].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
+ unfold PMPK.set_more. cbn [PM.p_tb PM.p_tg]. exact TB5.
+ split; [unfold PMPK.set_more; cbn [PM.p_src]; exact ST5|].
split; [intros _; reflexivity|]. left. exists v. split; [exact Hv|]. split; [| split; [reflexivity| reflexivity]].
apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB _ v _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC6].
apply OUT8. clear - Eop Eoec; lia.
- exact AHf.
- unfold PMPK.set_more, PM.pot_parser in *. cbn [PM.p_k PM.p_tb PM.p_tg] in *. exact CK5.
- exact MRTf.
- exact INCL6.
- exact INCA6.
- exact AMf.
- unfold PMPK.set_more. change (PM.parser_own (PM.PST 0 (PM.p_done s5) (PM.p_depth s5) (PM.p_src s5) (PM.p_tb s5) (PM.p_tg s5) (PM.p_b s5) (PM.p_k s5) (PM.p_stk s5)))
with (PM.parser_own s5). exact HHf. }
assert (EC3 : PMSPA.ec_at RSEGS M3 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [intros i _ r0 []| exact EC0]. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
unfold PMA.get_length_spec, PMSPA.get_length_spec, PMSPA.run_spec_rd in GL.
apply (GL 0 ltac:(clear; lia) fx3 R3 M3 model3 K LBX FF' LK2 Aw cr (sp - 128) 0xaed78 fb cat s str sm e HH3 AM3 K0).
{ split; [rewrite L5K.rl1; exact Y1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact B2R|].
split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; rewrite (R1c 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; rewrite (R1c 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 5) with 22528. change (22528 / 8) with 2816.
split; [apply (L5SAR.astk_sub ar M3 M3 sp 26624 128 22528 ASTK3 (mem_grows_refl M3)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 BI3)))))))| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 128 - 22528) with (sp + (-1416) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ apply (PMAUAR.ffroomA_push 7 5 FF LK LK2 _ FRM GLKI2); [exact NDF3| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
{ exact FOK'. }
{ replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
{ split; [rewrite L5K.rl10; exact Y10| rewrite L5K.rl11; exact Y11]. }
{ unfold PMSPA.run_pre. split; [|split; [|split; [|split; [|split; [|split]]]]].
- apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl.
- apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
unfold LB. apply incl_appr. exact INCS.
- apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS].
- apply (PMKA.u64_keepA RSEGS L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF].
- apply (PMASK.base_keep L ar C LY LB FF sp 26624 [] M M3 EK03f); [intros a _ r0 []| exact BASE].
- apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB FF sp 26624 [] M M3 EK03f e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| intros r0 []].
- exact TBOK. }
{ exact INCS. }
{ apply (proj1 (PM.inv_d0 s)). exact INV. }
{ exact EC3. }
{ exact UNR. }
{ exact CRED. }
intros fx4 R4 M4 model4 LK4 Aw4 s4 sm4 e4 cr4 RP4 RPOST4 HP4 CK4 MRT4 INCLK4 INCAw4 AM4 HH4.
change (PMSPA.pm_scr 5) with 22528 in HP4.
assert (WRR : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 1016) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr a Hin Hr. unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
assert (WAVR : forall rr a, In rr WR -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 0 / 8)).
{ intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
pose proof FSAPP as (FA0 & FA1 & FA2).
destruct (WRR rr a Hin Hr) as [X|X]; (split; [clear - X OCE SL128 SPT Eop F2 FSCEIL; lia|]).
- unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia.
- clear - X DF1; lia. }
assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s4) M4 model4 LK4 cr4 Aw4).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s) [] (PM.parser_own s4) M3 model3 LK2 cr Aw M4 model4 LK4 cr4 Aw4 22528 WR BI3 HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
[clear; lia| clear; lia| exact WAVR| intros a _ X; exact X| intros a X; exact X]. }
destruct RPOST4 as (RP4' & STEP4 & EE4 & ALT4).
assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
assert (G2' : getr R4 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R4c 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
assert (G8' : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (R4c 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
assert (G9' : getr R4 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R4c 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
assert (G18' : getr R4 (reg 18) = Z_to_bv 64 F) by (rewrite (R4c 18%nat) by inl; exact Y18).
assert (G19' : getr R4 (reg 19) = Z_to_bv 64 op) by (rewrite (R4c 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R).
assert (G20' : getr R4 (reg 20) = Z_to_bv 64 oec) by (rewrite (R4c 20%nat) by inl; rewrite (KS3 20%nat) by inl; exact B20R).
assert (G21' : getr R4 (reg 21) = Z_to_bv 64 ov) by (rewrite (R4c 21%nat) by inl; rewrite (KS3 21%nat) by inl; exact B21R).
assert (G24' : getr R4 (reg 24) = Z_to_bv 64 F) by (rewrite (R4c 24%nat) by inl; exact Y24).
assert (G25' : getr R4 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R4c 25%nat) by inl; exact Y25).
assert (G26' : getr R4 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R4c 26%nat) by inl; rewrite (KS3 26%nat) by inl; exact B26R).
assert (G34' : forall j, In j [3; 4; 27]%nat -> getr R4 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
apply R1c. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity. }
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
destruct ALT4 as [(v & Hv & EC4 & MO4 & E4)|(EC4 & INV4 & PL4)].
-
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK4 cr4 Aw4 M4 model4 fb v _ HH4 FOK' EC4) as ((QE1 & QE8 & QENSH) & ZE4 & EW4 & ECE & EU4 & _ & _).
pose proof (bv_unsigned_in_range 64 (getr R4 (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
assert (G10' : getr R4 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (QEF : (sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128)) by (clear - ECE SL128; lia).
cfeed P (PMARKP.arkCe_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F
| 49%nat => bv_unsigned (getr R4 (reg 10)) | 50%nat => v | _ => 0 end)) ltac:(first [assumption | unfold PMARKP.aligned; assumption | clear - Hv; lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11 & _).
assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 model4 fx4 fx5 R4 0xaed78 R5 0xae974 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s4) M4 model4 LK4 cr4 Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
assert (R5c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat -> getr R5 (reg j) = getr R4 (reg j)).
{ intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
apply (ERRP 0xaef4c 12 fx5 R5 M4 model5 LK4 Aw4 cr4 s4 sm4 e4 v (pa_errcat_obj PMA.AD) z12_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI5 RP4' EC4 STEP4).
{ intros X. exact E4. }
{ exact CK4. }
{ exact Z1. } { exact Z10. } { exact Z11. }
all: first [ (rewrite R5c by inl; assumption) | (intros j Hj; rewrite (R5c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply G34'; exact Hj) ].
-
destruct PL4 as (STK4 & UN4 & (len & Hlen & Rlen)). rewrite L5K.rl10 in Rlen.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK4 cr4 Aw4 M4 model4 fb 0 _ HH4 FOK' EC4) as ((QE1 & QE8 & QENSH) & ZE4 & EW4 & ECE & EU4 & _ & _).
assert (QEF : (sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128)) by (clear - ECE SL128; lia).
cfeed P (PMARKP.arkC0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => len | _ => 0 end)) ltac:(first [assumption | unfold PMARKP.aligned; assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z22).
assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr4 Aw4 M4 model4 fx4 fx5 R4 0xaed78 R5 0xb0428 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s4) M4 model4 LK4 cr4 Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
assert (R5c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%nat -> getr R5 (reg j) = getr R4 (reg j)).
{ intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
destruct RP4' as (PA4 & IA4 & VIS4 & VREF4 & BASE4 & ERR4 & TB4).
pose proof INV4 as (IM4 & ID4 & IDP4 & ISH4 & ITB4).
assert (HK4 : 0 <= PM.p_k s4 <= 11) by (destruct PA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hk4 & _) & _); exact Hk4).
assert (CR4 : PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s4)) cr4) by exact (PMAPAR.credit_le_keepA _ _ _ _ CRED CK4).
pose proof BI5 as (_ & _ & _ & _ & INCL5 & ASTK5 & EKb5 & _).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
unfold PMA.read_span_spec, PMSPA.read_span_spec in RS.
apply (RS fx5 R5 M4 model5 K LBX FF' LK4 Aw4 cr4 (sp - 128) 0xaeda4 fb len s4 str sm4 HH5 AM5 K0).
{ split; [rewrite L5K.rl1; exact Z1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (R5c 2%nat) by inl; exact G2'|].
split; [rewrite L5K.rl3; rewrite (R5c 3%nat) by inl; rewrite (G34' 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (R5c 4%nat) by inl; rewrite (G34' 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 6) with 24576. change (24576 / 8) with 3072.
split; [apply (L5SAR.astk_sub ar M4 M4 sp 26624 128 24576 ASTK5 (mem_grows_refl M4)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact EKb5| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 128 - 24576) with (sp + (-1544) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ apply (PMAUAR.ffroomA_push 7 6 FF LK LK4 _ FRM INCL5); [exact NDF5| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
{ exact FOK'. }
{ replace (sp - 128) with (sp + (-4) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
{ rewrite L5K.rl10. unfold PMSPA.o_src. fold op. exact Z10. }
{ rewrite L5K.rl11. exact Z11. }
{ rewrite L5K.rl12. unfold PMSPA.o_tb. fold op. exact Z12. }
{ exact Hlen. }
{ exact PA4. }
{ exact IA4. }
{ exact BASE4. }
{ exact ITB4. }
{ exact INCS. }
{ clear - UN4 UNR. lia. }
{ exact (PMAPAR.pot_text_le_parserA L ar C LY s4 cr4 HK4 CR4). }
intros fx6 R6 M6 model6 LK6 Aw6 s6 sm6 cr6 ptr n RP6 Rptr Rn Hn Hn26 LOC6 DEF6 ACC6 PA6 IA6 TB6 MO6 DO6 DP6 B6 K6 STK6 STEP6 HP6 CK6 MRT6 INCLK6 INCAw6 AM6 HH6.
change (PMSPA.pm_scr 6) with 24576 in HP6.
set (Wc6 := PMSPA.W_srcf PMA.AD fb ++ [(PMSPA.o_tb PMA.AD fb, 24)]) in HP6.
assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> fb + 32 <= a < fb + 1016).
{ intros rr a Hin Hr. unfold Wc6, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M6 model6 LK6 cr6 Aw6).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s4) [] (PM.parser_own s6) M4 model5 LK4 cr4 Aw4 M6 model6 LK6 cr6 Aw6 24576 Wc6 BI5 HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
[clear; lia| clear; lia| | | intros a X; exact X].
- intros rr a Hin Hr. apply (WAVR rr a); [| exact Hr]. unfold WR, PMSPA.W_run. cbn [app]. unfold Wc6 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
+ right. apply in_or_app. left. exact Hin.
+ right. apply in_or_app. right. left. reflexivity.
- intros a Hc Ho rr Hin Hr. apply (Ho rr); [| exact Hr]. unfold WR, PMSPA.W_run. cbn [app]. unfold Wc6 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
+ right. apply in_or_app. left. exact Hin.
+ right. apply in_or_app. right. left. reflexivity. }
pose proof (L5SAR.ek_callee L ar LBX [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 24576 Wc6 Wc6 M4 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK46.
assert (OUT6 : forall a n0, (a + n0 <= fb + 32 \/ fb + 1016 <= a) -> forall i, a <= i < a + n0 -> L5.outside Wc6 i).
{ intros a n0 X i Hi rr Hin Hr. pose proof (Wc6R rr i Hin Hr) as Y. clear - X Hi Y. lia. }
assert (OUTc6 : forall a n0, fb + 32 <= a -> a + n0 <= fb + 1016 -> (a + n0 <= op + 280 \/ op + 320 <= a) -> (a + n0 <= ois + 40 \/ ois + 48 <= a) ->
(a + n0 <= ois + 152 \/ ois + 156 <= a) -> (a + n0 <= op + 336 \/ op + 360 <= a) -> forall i, a <= i < a + n0 -> L5.outside Wc6 i).
{ intros a n0 X1 X2 X3 X4 X5 X6 i Hi rr Hin Hr. unfold Wc6, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; clear - Hr Hi X3 X4 X5 X6 Eop Eois; lia. }
assert (INW6 : forall rr, In rr Wc6 -> In rr WR).
{ intros rr Hin. unfold WR, PMSPA.W_run. cbn [app]. unfold Wc6 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
+ right. apply in_or_app. left. exact Hin.
+ right. apply in_or_app. right. left. reflexivity. }
assert (WAPP6 : PMKA.wapp Wc6) by (intros rr Hin; apply WAPPR; apply INW6; exact Hin).
rewrite L5K.rl10 in Rptr. rewrite L5K.rl11 in Rn.
assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R5 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R5 R6 j RP6 Hj)).
assert (H6r : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R4 (reg j)).
{ intros j Hj. rewrite (R6c j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
exact (R5c j Hj). }
assert (K62 : getr R6 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (H6r 2%nat) by inl; exact G2').
assert (K68 : getr R6 (reg 8) = Z_to_bv 64 sp) by (rewrite (H6r 8%nat) by inl; exact G8').
assert (K69 : getr R6 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (H6r 9%nat) by inl; exact G9').
assert (K618 : getr R6 (reg 18) = Z_to_bv 64 F) by (rewrite (H6r 18%nat) by inl; exact G18').
assert (K619 : getr R6 (reg 19) = Z_to_bv 64 op) by (rewrite (H6r 19%nat) by inl; exact G19').
assert (K620 : getr R6 (reg 20) = Z_to_bv 64 oec) by (rewrite (H6r 20%nat) by inl; exact G20').
assert (K621 : getr R6 (reg 21) = Z_to_bv 64 ov) by (rewrite (H6r 21%nat) by inl; exact G21').
assert (K622 : getr R6 (reg 22) = Z_to_bv 64 len) by (rewrite (R6c 22%nat) by inl; exact Z22).
assert (K624 : getr R6 (reg 24) = Z_to_bv 64 F) by (rewrite (H6r 24%nat) by inl; exact G24').
assert (K625 : getr R6 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (H6r 25%nat) by inl; exact G25').
assert (K626 : getr R6 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (H6r 26%nat) by inl; exact G26').
assert (K634 : forall j, In j [3; 4; 27]%nat -> getr R6 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (H6r j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
apply G34'. exact Hj. }
clear R6c H6r.
assert (PLOC : (ptr = 0 /\ n = 0) \/ (4096 <= ptr /\ ptr + n <= ahl_ceil ar)).
{ destruct LOC6 as [X|[(Bq & mq & Hin & X1 & X2)|(X1 & X2)]]; [left; exact X| right| right].
- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB6 & _).
destruct (WB6 (Bq, mq) (in_or_app _ _ _ (or_introl Hin))) as ((Yb1 & _ & _ & _ & Yb5 & _) & _). cbn [fst snd] in Yb1, Yb5. clear - X1 X2 Yb1 Yb5; lia.
- unfold PMSPA.o_tb in X1, X2. fold op in X1, X2. clear - X1 X2 F1 F2 FSCEIL Eop O1; lia. }
assert (QP : 0 <= ptr < 2 ^ 64) by (clear - PLOC SLO SHI SPT Hn; destruct PLOC as [(X & _)|(X & Y)]; [subst ptr|]; lia).
assert (QN : 0 <= n < 2 ^ 64) by (clear - Hn Hlen; lia).
assert (FB0 : 6885376 <= fb) by (clear - O1 Eop Fal; lia).
assert (VIS6 : PMSPA.visitor_at RSEGS PMA.AD M6 ov).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LBX FF sp 26624 Wc6 M4 M6 EK46 WAPP6 FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS4].
apply OUTc6; clear - Eov Eop Eois; lia. }
assert (VREF6 : L5.u64_at RSEGS M6 (op + 384) ov).
{ apply (PMKA.u64_keepA RSEGS L ar LBX FF sp 26624 Wc6 M4 M6 EK46 WAPP6 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF4].
apply OUTc6; clear - Eop Eois; lia. }
assert (EC6 : PMSPA.ec_at RSEGS M6 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar LBX FF sp 26624 Wc6 M4 M6 EK46 WAPP6 FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC4].
apply OUTc6; clear - Eoec Eop Eois; lia. }
assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
{ apply (PMASK.base_keep L ar C LY LBX FF sp 26624 Wc6 M4 M6 EK46); [| exact BASE4].
intros a Ha rr Hin Hr. pose proof (Wc6R rr a Hin Hr) as Y. clear - Ha Y FB0; lia. }
assert (ERR6 : PMSTA.err_okA RSEGS PMA.AD PMA.AAD M6 e4).
{ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LBX FF sp 26624 Wc6 M4 M6 EK46 e4 PMA.addrs_wf_A); [| exact ERR4].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr Hin Hr. pose proof (Wc6R rr a Hin Hr) as Y. clear - DI Y FB0; lia. }
assert (RP6' : PMSPA.run_pre RSEGS PMA.AD PMA.AAD M6 fb s6 str sm6 e4) by (split; [exact PA6| split; [exact IA6| split; [exact VIS6| split; [exact VREF6| split; [exact BASE6| split; [exact ERR6| exact TB6]]]]]]).
assert (ST6 : PMSPA.src_step (PM.p_src s) (PM.p_src s6) sm sm6) by exact (PMAPAR.src_step_transA _ _ _ _ _ _ STEP4 STEP6).
assert (CK6' : PMSPA.credit_keep cr cr6 (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s6)))
by exact (PMAPAR.credit_keep_transA _ _ _ _ _ _ CK4 (PMAPAR.credit_keep_textA L ar C LY s4 s6 cr4 cr6 CK6 K6)).
set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
cfeed P (PMARKP.arkF_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => len
| 51%nat => ptr | 52%nat => n | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & A71 & A711 & A723 & C70)|(MS7 & KS7 & A71 & A710 & A711 & C70)]).
--
assert (E7 : M7v = MV6) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M6 model6 fx6 fx7 R6 0xaeda4 R7 0xafa88 MV6 K HH6 AM6 MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M6 model6 LK6 cr6 Aw6 model7 BI6 HH7 AM7 MRT7) as BI7.
assert (NL : n = len).
{ change (2 ^ 64) with 18446744073709551616 in C70, QN, Hlen. clear - C70 QN Hlen. Z.to_euclidean_division_equations. lia. }
subst n.
pose proof BI7 as (_ & _ & _ & INCA7 & INCL7 & ASTK7 & EKb7 & _).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF7 & _).
assert (ASTKv : L5CA.astk ar M6 (sp - 128) 12288).
{ apply (L5SAR.astk_sub ar M6 M6 sp 26624 128 12288 ASTK7 (mem_grows_refl M6)); [clear; lia| clear; lia| clear; lia|].
replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
unfold PMA.validate_spec, PMSPA.validate_spec, PMSPA.scan_spec in VAL.
apply (VAL fx7 R7 M6 model7 K (PM.parser_own s6 ++ LBX) FF' LK6 Aw6 cr6 ptr len (sp - 128) 0xaedb4 HH7 AM7 K0).
{ split; [rewrite L5K.rl1; exact A71|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS7 2%nat) by inl; exact K62|].
split; [rewrite L5K.rl3; rewrite (KS7 3%nat) by inl; rewrite (K634 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (KS7 4%nat) by inl; rewrite (K634 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536.
split; [exact ASTKv|].
apply SZK; [exact EKb7| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 128 - 12288) with (sp + (-776) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ apply (PMAUAR.ffroomA_push 7 0 FF LK LK6 _ FRM INCL7); [exact NDF7| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 0 (sp - 128 + 32) FRS); clear; lia. }
{ rewrite L5K.rl10. rewrite (KS7 10%nat) by inl. exact Rptr. }
{ rewrite L5K.rl11. exact A711. }
{ clear - Hn Hn26. lia. }
{ clear - QP. lia. }
{ clear - PLOC. destruct PLOC as [(_ & X)|(X & _)]; [left; exact X| right; lia]. }
{ clear - PLOC SLO SHI SPT Hn. destruct PLOC as [(X & Y)|(X & Y)]; [subst ptr; lia| lia]. }
{ exact DEF6. }
{ exact ACC6. }
{ intros a Ha. apply (PMASR1.vis_scan L ar C HI LY HIok _ FF' LK6 cr6 Aw6 M6 model7 ptr len HH7); [| exact Ha].
destruct LOC6 as [(_ & X)|[(Bq & mq & Hin & X1 & X2)|(X1 & X2)]]; [left; exact X| right; right; exists Bq, mq; split; [apply in_or_app; left; exact Hin| split; [exact X1| exact X2]]| right; left].
unfold PMSPA.o_tb in X1, X2. fold op in X1, X2. unfold FS_BYTES. clear - X1 X2 F1 F2 Eop. Lia.lia. }
{ change (PMSPA.pm_scr 0) with 12288. clear - PLOC SLO Hn. destruct PLOC as [(_ & X)|(_ & X)]; [left; exact X| right; right; lia]. }
{ exact BASE6. }
intros fx8 R8 M8 model8 RP8 FB8 MG8 MRT8 AM8 HH8.
assert (AH8 : L5CA.ahpres L ar (PM.parser_own s6 ++ LBX) FF' (sp - 128) 12288 [] M6 M8).
{ apply (PMAUAR.ahpres_of_frame_but L ar C HI LY HIok (PM.parser_own s6 ++ LBX) FF' LK6 cr6 Aw6 M6 M8 (vml_of model7) (sp - 128) 12288 HH7);
[clear - SPT; lia| clear - SLO; lia| clear; lia| exact FB8| exact MG8|].
pose proof ASTKv as (_ & _ & _ & _ & X & _). exact X. }
assert (BI8 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M8 model8 LK6 cr6 Aw6).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s6) (PM.parser_own s6) (PM.parser_own s6) M6 model7 LK6 cr6 Aw6 M8 model8 LK6 cr6 Aw6 12288 [] BI7 AH8 HH8 AM8 MRT8 (incl_refl _) (incl_refl _));
[clear; lia| clear; lia| intros rr a []| intros a _ _ rr []| intros a X; exact X]. }
pose proof (L5SAR.ek_callee L ar (PM.parser_own s6 ++ LBX) [] FF [(F, 0, sp - 128 + 32)] sp 26624 (sp - 128) 12288 [] [] M6 M8 AH8 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK68.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6) as BRB6.
assert (RP8' : PMSPA.run_pre RSEGS PMA.AD PMA.AAD M8 fb s6 str sm6 e4).
{ split; [|split; [|split; [|split; [|split; [|split]]]]].
- apply (PMKA.parser_keepA RSEGS PMA.AD L ar (PM.parser_own s6 ++ LBX) FF sp 26624 [] M6 M8 EK68 PMKA.wapp_nil FRB BRB6 _ _ _ AOP);
[apply incl_appl, incl_refl| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA6].
- apply (PMKA.iss_keepA RSEGS PMA.AD L ar (PM.parser_own s6 ++ LBX) FF sp 26624 [] M6 M8 EK68 PMKA.wapp_nil FRB BRB6 ois str sm6 AOI);
[apply incl_appr; exact INCS| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA6].
- apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF sp 26624 [] M6 M8 EK68 PMKA.wapp_nil FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS6].
- apply (PMKA.u64_keepA RSEGS L ar _ FF sp 26624 [] M6 M8 EK68 PMKA.wapp_nil FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF6].
- apply (PMASK.base_keep L ar C LY _ FF sp 26624 [] M6 M8 EK68); [intros a _ r0 []| exact BASE6].
- apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF sp 26624 [] M6 M8 EK68 e4 PMA.addrs_wf_A); [| exact ERR6].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| intros r0 []].
- exact TB6. }
assert (EC8 : PMSPA.ec_at RSEGS M8 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar _ FF sp 26624 [] M6 M8 EK68 PMKA.wapp_nil FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [intros i _ r0 []| exact EC6]. }
assert (R8c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (reg j) = getr R7 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R7 R8 j RP8 Hj)).
assert (K82 : getr R8 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R8c 2%nat) by inl; rewrite (KS7 2%nat) by inl; exact K62).
assert (K88 : getr R8 (reg 8) = Z_to_bv 64 sp) by (rewrite (R8c 8%nat) by inl; rewrite (KS7 8%nat) by inl; exact K68).
assert (K89 : getr R8 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R8c 9%nat) by inl; rewrite (KS7 9%nat) by inl; exact K69).
assert (K818 : getr R8 (reg 18) = Z_to_bv 64 F) by (rewrite (R8c 18%nat) by inl; rewrite (KS7 18%nat) by inl; exact K618).
assert (K819 : getr R8 (reg 19) = Z_to_bv 64 op) by (rewrite (R8c 19%nat) by inl; rewrite (KS7 19%nat) by inl; exact K619).
assert (K820 : getr R8 (reg 20) = Z_to_bv 64 oec) by (rewrite (R8c 20%nat) by inl; rewrite (KS7 20%nat) by inl; exact K620).
assert (K821 : getr R8 (reg 21) = Z_to_bv 64 ov) by (rewrite (R8c 21%nat) by inl; rewrite (KS7 21%nat) by inl; exact K621).
assert (K822 : getr R8 (reg 22) = Z_to_bv 64 len) by (rewrite (R8c 22%nat) by inl; rewrite (KS7 22%nat) by inl; exact K622).
assert (K823 : getr R8 (reg 23) = Z_to_bv 64 ptr) by (rewrite (R8c 23%nat) by inl; exact A723).
assert (K824 : getr R8 (reg 24) = Z_to_bv 64 F) by (rewrite (R8c 24%nat) by inl; rewrite (KS7 24%nat) by inl; exact K624).
assert (K825 : getr R8 (reg 25) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R8c 25%nat) by inl; rewrite (KS7 25%nat) by inl; exact K625).
assert (K826 : getr R8 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R8c 26%nat) by inl; rewrite (KS7 26%nat) by inl; exact K626).
assert (K834 : forall j, In j [3; 4; 27]%nat -> getr R8 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R8c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS7 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K634. exact Hj. }
clear R8c.
pose proof (bv_unsigned_in_range 64 (getr R8 (reg 11))) as B811. change (bv_modulus 64) with (2 ^ 64) in B811.
assert (K811 : getr R8 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
set (H8 := ahid Aw6 model8) in *. set (MV8 := mrestrict H8 M8) in *.
cfeed P (PMARKP.arkW_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => len
| 51%nat => ptr | 53%nat => bv_unsigned (getr R8 (reg 11)) | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & [(MS9 & KS9)|(MS9 & KS9 & A91 & A910 & A911)]).
++
assert (E9 : M9v = MV8) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M8 model8 fx8 fx9 R8 0xaedb4 R9 0xaeea8 MV8 K HH8 AM8 MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (E9 : M9 = M8) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M8 model8 LK6 cr6 Aw6 model9 BI8 HH9 AM9 MRT9) as BI9.
set (H9 := ahid Aw6 model9) in *. set (MV9 := mrestrict H9 M8) in *.
pose proof RP8' as (PA8 & IA8 & VIS8 & VREF8 & BASE8 & ERR8 & TB8).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF' LK6 cr6 Aw6 M8 model9 HH9 BASE8) as (VM90 & VM91 & VM92).
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s6) M8 model9 LK6 cr6 Aw6 BI9) as ((WS9 & _ & _ & _ & _) & OWN9 & (FD9 & FW9 & FSW9 & FLC9 & FLW9) & (FLCc9 & FLV9 & VF9 & VS9 & VSH9)).
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (F + 64 - 8) with (F + 56) in FLC9 by (clear; lia).
pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ FF' LK6 cr6 Aw6 M8 model9 fb HH9 FOK' VIS8) as ((V91 & V98 & VNSH) & Zov9 & Wov9 & OVCE & VT9 & _ & _).
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK6 cr6 Aw6 M8 model9 1231264 1 HH9 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(right; left; clear; lia)) as VTS9.
change (1231264 / 8 + 2147450880) with 2147604788 in VTS9.
destruct (APART ov 8 0 0 (CLfb ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AvF & AvSF & AvFL).
unfold SB in AvSF.
assert (QvF : ov + 8 <= F \/ F + 64 <= ov) by (clear - AvF; lia).
assert (SHov : ov / 8 + SB = fb / 8 + SB + 54).
{ rewrite Eov. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 432) with ((128 * (fb / 1024) + 54) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
destruct (APART (ov / 8 + SB) 1 0 0 (CLsh (ov / 8 + SB) 1 ltac:(clear - SHov; lia) ltac:(clear - SHov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & QvS & _).
unfold SB in QvS.
assert (QFS : ((F / 8) + 2147450880) + 8 <= 2147604788 \/ 2147604788 + 1 <= ((F / 8) + 2147450880)) by (right; clear - GF8 Q3; lia).
assert (QvR : (sp - 128) + 128 <= ov \/ ov + 8 <= (sp - 128)) by (clear - OVCE SL128; lia).
assert (Qv : 6885376 <= ov <= 140737488355320) by (clear - V91; lia).
pose proof GF8 as (GF8a & _).
cfeed P (PMARKP.arkK1_conc fx9 R9 MV9 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 49%nat => len | 51%nat => ptr | _ => 0 end)) ltac:(idtac; lazymatch goal with
| |- getr _ _ = _ => rewrite (KS9 _) by inl; assumption
| |- PMARKP.aligned _ _ => unfold PMARKP.aligned; assumption
| _ => assumption
end).
destruct P as (fx10 & R10 & M10v & MG10 & _ & FRZ10 & MS10 & KS10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
set (W10 := fun a => (F + 32 <= a < F + 32 + 16) \/ ((F / 8) + 2147450880 + 4 <= a < (F / 8) + 2147450880 + 4 + 2)).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M8 model9 fx9 fx10 R9 0xaeea8 R10 0xaeef8 M10v W10 K HH9 AM9 MS10 MG10).
{ intros a Ha Nn. apply FRZ10; [exact Ha| intros X; apply Nn; left; clear - X; lia| intros X; apply Nn; right; clear - X; lia]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|X].
+ apply (L5SAR.fframe_client L ar _ FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
+ apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 0 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
- destruct Wa as [X|X]; clear - X GFR GF8a; lia. }
intros M10 model10 HH10 AM10 MRT10 HID10 VIS10 MGM10 FR10 VV10. change (mrestrict H9 M10 = M10v) in VIS10.
assert (BI10 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M10 model10 LK6 cr6 Aw6).
{ apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s6) M8 model9 LK6 cr6 Aw6 M10 model10 W10 BI9 HH10 AM10 MRT10 MGM10 FR10).
intros a Wa. right. change (ff_bytes 0) with 64. change (64 / 8) with 8. unfold SB. destruct Wa as [X|X]; [left| right]; clear - X; lia. }
assert (EK810 : L5SAR.ek L ar (PM.parser_own s6 ++ LBX) FF 0 0 [] M8 M10).
{ apply (PMAUAR.wfr_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s6 ++ LBX) LK6 cr6 Aw6 M8 M10 _ [] (fun _ => False) G HH9 (fun a X => match X with end)).
intros a Ha N. apply FR10; [exact Ha|]. intros X. apply N. unfold PMAUAR.Wfr. change (ff_bytes 0) with 64. change (64 / 8) with 8. unfold SB.
left. left. unfold W10 in X. destruct X as [X|X]; [left| right]; clear - X; lia. }
assert (PA10 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M10 op ois s6).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar (PM.parser_own s6 ++ LBX) FF 0 0 [] M8 M10 EK810 PMKA.wapp_nil FRB BRB6 _ _ _ AOP);
[apply incl_appl, incl_refl| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA8]. }
set (H10 := ahid Aw6 model10) in *. set (MV10 := mrestrict H10 M10) in *.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK6 cr6 Aw6 M10 model10 fb _ s6 HH10 FOK' PA10) as ((_ & _ & _) & Zop10 & Z3210 & Z2010 & OWR10 & _ & OVIS10 & _ & _).
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s6) M10 model10 LK6 cr6 Aw6 BI10) as ((WS10 & _ & _ & _ & _) & OWN10 & (FD10 & FW10 & FSW10 & FLC10 & FLW10) & (FLCc10 & FLV10 & VF10 & VS10 & VSH10)).
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (sp - (sp - 128)) with 128 in WS10 by (clear; lia).
replace (F + 64 - 8) with (F + 56) in FLC10 by (clear; lia).
assert (CM10 : L5.u8_at RSEGS MV10 (op + 16) 0).
{ apply (proj2 (L5A.u8_at_vis H10 M10 (op + 16) 0 (OVIS10 (op + 16) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
pose proof PA10 as (_ & _ & _ & _ & _ & _ & X & _). exact X. }
pose proof OWN10 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
change (bv_modulus 64) with (2 ^ 64) in *.
pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
destruct (k2_run fx10 R10 R MV10 sp op ov oec F fl) as (fx11 & R11 & M11v & MG11 & FRZ11 & MS11 & K3411 & REG11 & E112 & FL0 & MO1);
first [assumption | (rewrite (KS10 _) by inl; rewrite (KS9 _) by inl; assumption) | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - GF1 GF2; lia
| clear - GL1 GL2; lia | clear - OCE SL128; lia | clear - GFCEIL SL128; lia | clear - GL4 SL128; lia | clear - Eop Eov Eoec O1; lia
| (replace (sp mod 32) with 0 by (symmetry; exact SP32); reflexivity) | exact SP32 | exact O8 | exact GF32 | idtac].
assert (R11ra : getr R11 (reg 1) = Z_to_bv 64 r) by (rewrite (REG11 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx11 R11 M11v 0xaeea4 (ltac:(oW' 0xaeea4%Z)) r (ltac:(oF' 0xaeea4%Z)) eq_refl (ltac:(oD' 0xaeea4%Z)) R11ra Hr1 Hr2) as MSr.
apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s6) M10 model10 LK6 cr6 Aw6 (fun a => op + 8 <= a < op + 9) fx10 fx11 R10 0xaeef8 R11 r M11v K BI10).
{ intros a X. split.
- apply (L5SAR.fframe_client L ar (PM.parser_own s6 ++ LBX) FF' 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - X Eop; lia].
- intros O. apply (O (PMSPA.o_p PMA.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - X; lia]. }
{ intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X|X]; [left; exact X| right; exact X]. }
{ exact (msteps_trans _ _ _ _ MS11 MSr). }
{ exact MG11. }
{ intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
apply FRZ11; [exact Ha| intros X; apply Nw; right; clear - X; lia| intros X; apply Nw; left; left; left; clear - X; lia
| intros X; apply Nw; left; left; right; unfold SB; clear - X; lia| intros X; apply Nw; left; right; clear - X; lia]. }
{ exact FL0. }
intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict H10 Mf = M11v) in VISf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s6 ++ LBX) FF 0 0 [(op + 8, 1)] M8 Mf).
{ apply (PMAUAR.wfr_ek L ar C HI LY HIok LBX FF LK Aw sp 26624 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s6 ++ LBX) LK6 cr6 Aw6 M8 Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HH9).
- intros a X O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
- intros a Ha N. rewrite FZf; [| exact Ha|].
+ apply FR10; [exact Ha|]. intros X. apply N. unfold PMAUAR.Wfr. change (ff_bytes 0) with 64. change (64 / 8) with 8. unfold SB.
left. left. unfold W10 in X. destruct X as [X|X]; [left| right]; clear - X; lia.
+ intros X. apply N. unfold PMAUAR.Wfr. unfold PMAUK.WretX, PMAUK.Wret in X. change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
destruct X as [[[X|X]|X]|X]; [left; left; left; clear - X; lia| left; left; right; exact X| left; right; exact X| right; exact X]. }
assert (MO1f : L5.u8_at RSEGS Mf (op + 8) 1).
{ apply (proj1 (L5A.u8_at_vis H10 Mf (op + 8) 1 (OVIS10 (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VISf. exact MO1. }
pose proof BI10 as (_ & _ & _ & INCA10 & INCL10 & _).
assert (OUTk : forall a n0, (a + n0 <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n0 -> L5.outside [(op + 8, 1)] i).
{ intros a n0 X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTBk : forall q m, In (q, m) (PM.parser_own s6 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(op + 8, 1)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH6 Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPPk : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (Ivb : In (PM.p_b s6, 32 * 2 ^ PM.p_k s6) (PM.parser_own s6 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s6), PM.CHUNK) (PM.parser_own s6 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IM6 : PM.p_more s6 = 1) by (rewrite MO6; exact IM4).
assert (SM6 : PMPK.set_more s6 1 = s6) by (clear - IM6; destruct s6; unfold PMPK.set_more; cbn [PM.p_more] in IM6; subst; reflexivity).
apply (KONT fx11 R11 Mf modelf LK6 Aw6 s6 sm6 e4 cr6).
** apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E112; exact (eq_sym Rsp) | apply REG11; inl
| rewrite (K3411 _) by inl; rewrite (KS10 _) by inl; rewrite (KS9 _) by inl; apply K834; inl ] |]).
destruct Hj.
** unfold PMSPA.run_post, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
--- destruct (BRB6 _ Iqc) as (Xq1 & Xq2). destruct (BRB6 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
rewrite <- SM6.
apply (PMAPAR.parser_more_updA M8 Mf op ois s6 1 PA8).
+++ clear - O1; lia.
+++ clear - O1; lia.
+++ apply (PMKA.agA_obj L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUTk. clear; lia.
+++ apply (PMKA.agA_obj L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUTk. clear; lia.
+++ exact (PMKA.agsh_obj L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB op 384 AOP).
+++ pose proof PA8 as (_ & PD8 & _). apply (L5.defined_grows M10 Mf _ _ MGf (L5.defined_grows M8 M10 _ _ MGM10 PD8)).
+++ exact MO1f.
+++ right; reflexivity.
+++ exact Xq1.
+++ clear - Xq2; lia.
+++ apply (PMKA.agA_blk L ar _ FF 0 0 _ M8 Mf EKf WAPPk BRB6 _ _ Iqc). apply OUTBk. exact Iqc.
+++ exact Xb1.
+++ clear - Xb2; lia.
+++ apply (PMKA.agA_blk L ar _ FF 0 0 _ M8 Mf EKf WAPPk BRB6 _ _ Ivb). apply OUTBk. exact Ivb.
+++ intros c0' n0 p0 E0. assert (Ip : In (p0, c0') (PM.parser_own s6 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF 0 0 _ M8 Mf EKf WAPPk BRB6 _ _ Ip). apply OUTBk. exact Ip.
--- apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB BRB6 ois str sm6 AOI); [| | | exact IA8].
+++ apply incl_appr. exact INCS.
+++ apply OUTk. clear - Eop Eois; lia.
+++ intros c0' n0 p0 E0. unfold PMKA.blk_out. apply (OUTBk p0 c0'). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
--- apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS8].
apply OUTk. clear - Eop Eov; lia.
--- apply (PMKA.u64_keepA RSEGS L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF8].
apply OUTk. clear; lia.
--- apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M8 Mf EKf); [| exact BASE8]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
--- apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF 0 0 _ M8 Mf EKf e4 PMA.addrs_wf_A); [| exact ERR8].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
--- exact TB8.
--- split; [exact ST6|]. split; [exact EE4|]. right.
split; [apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M8 Mf EKf WAPPk FRB _ 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [apply OUTk; clear - Eop Eoec; lia| exact EC8]|].
split.
+++ unfold PM.inv. rewrite MO6, DO6, DP6, STK6. split; [exact IM4|]. split; [exact ID4|]. split; [rewrite IDP4; clear; lia|]. split; [exact ISH4| exact TB6].
+++ cbv beta. unfold PMSPA.prog_key. split; [rewrite STK6; exact STK4|]. destruct STEP6 as (_ & _ & _ & _ & U6). clear - U6 UN4; lia.
** exact AHf.
** exact CK6'.
** exact MRTf.
** exact INCL10.
** exact INCA10.
** exact AMf.
** exact HHf.
++
assert (E9 : M9v = MV8) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M8 model8 fx8 fx9 R8 0xaedb4 R9 0xae974 MV8 K HH8 AM8 MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (E9 : M9 = M8) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M8 model8 LK6 cr6 Aw6 model9 BI8 HH9 AM9 MRT9) as BI9.
apply (ERRP 0xaedc8 7 fx9 R9 M8 model9 LK6 Aw6 cr6 s6 sm6 e4 0 cat z7_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI9 RP8' EC8 ST6 EE4 CK6').
all: first [ exact A91 | exact A910 | exact A911 | (rewrite (KS9 _) by inl; assumption)
| (intros j Hj; rewrite (KS9 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K834; exact Hj) ].
--
assert (E7 : M7v = MV6) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ7; exact Ha). subst M7v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK6 cr6 Aw6 M6 model6 fx6 fx7 R6 0xaeda4 R7 0xae974 MV6 K HH6 AM6 MS7 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7.
assert (E7 : M7 = M6) by (apply L5SAR.mem_eq_of_agree; exact FR7). subst M7.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 26624 (sp - 128) (own sp R) F 0 WR (PM.parser_own s6) M6 model6 LK6 cr6 Aw6 model7 BI6 HH7 AM7 MRT7) as BI7.
apply (ERRP 0xaedf4 1 fx7 R7 M6 model7 LK6 Aw6 cr6 s6 sm6 e4 0 cat z1_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI7 RP6' EC6 ST6 EE4 CK6').
all: first [ exact A71 | exact A710 | exact A711 | (rewrite (KS7 _) by inl; assumption)
| (intros j Hj; rewrite (KS7 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K634; exact Hj) ].
Qed.
End WithHeap.
End PMARDK.

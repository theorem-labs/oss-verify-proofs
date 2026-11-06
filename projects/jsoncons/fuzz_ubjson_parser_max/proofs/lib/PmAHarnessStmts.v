(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA LibIface LibIfaceAJ L5Defs L5Core PmTopAL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAHarnessStmts () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "3Z"; "0F"; "0KSL"; "4bvmap"; "0M1"; "0M1'"; "0R"; "0R0"; "0Ra"]; ["0Rb"; "5regs_preserved"; "6HIDX"; "6U"; "6rinvH"; "6tfrk"; "6tocell"; "7getr"; "0S"; "8eqb"; "9In"; "9existsb"; "9forallb"; ":le"; ":lt"; ":of_nat"]; [":pow"; ":sub"; "0V2"; "0a"; "0cls"; "0k"; ";Z_to_bv"; ";bv"; "0x"; "0z"]]).
Local Ltac lia := L5FastLia.plia.
Module PMHAS.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "H&:y5'Q7yR0%211%5241'2'5&Mz&Cr2r1%3221%6251&N&Q0+2+R0%3221%5271%>271pR<@1pLB1").
Proof. intros R k. unfold U. pose proof (bv_unsigned_in_range 64 (getr R (reg k))) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma U_of : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "Q9&:y5'Q7yR0%211%5241'2'7'6&Gr3&Q6&Or2%211%42>1%7261r1%72?1%;3?31'5&Mz%221:&N&Q0+2+R0%3221%52@1%:271&Cr5r4%3221%K3L1Ip061p0B1pRDO1pR<Q11pLQ31").
Proof. intros R k z. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "F&:y5'Q7yR0%211%5241'2'6&Gr2&Q6&Or1%211%42=1%7261&C%1285%82?1%<3?41pR<>1pL@1"). Proof. intros R k. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Definition STK : Z := 36864.
Definition FRAMES (k : Z) : Z := 14.
Definition LEAK (k : Z) : Z := 0.
Definition CREDIT (n : Z) : credit := (512, 3 * (2 ^ 29 + 8 * n)).
Definition Lay (L : asan_layout) : lib_layoutA := PMTAL.TopLayA_a STK FRAMES LEAK CREDIT L.
Definition tfrk (S : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (U R 1) /\ L5.u64_at RSEGS M (S - 16) (U R 8) /\ L5.u64_at RSEGS M (S - 24) (U R 9) /\ L5.u64_at RSEGS M (S - 32) (U R 18) /\
L5.u64_at RSEGS M (S - 40) (U R 19) /\ L5.u64_at RSEGS M (S - 48) (U R 20) /\ L5.u64_at RSEGS M (S - 56) (U R 21) /\ L5.u64_at RSEGS M (S - 64) (U R 22) /\
L5.u64_at RSEGS M (S - 72) (U R 23) /\ L5.u64_at RSEGS M (S - 80) (U R 24) /\ L5.u64_at RSEGS M (S - 88) (U R 25) /\ L5.u64_at RSEGS M (S - 96) (U R 26).
Definition tocell (S : Z) (a : Z) : Prop := S - 96 <= a < S.
Lemma tfrk_agree : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "QD'7&:y5'Q7yR0%211%5241'3y8%611%311p061pRB72&M+TP0&Q1r4+S0%3221%6251r5&Q0+2+Q?%3221%<251&Er6%2318<&Fr8r1%3221'6&Q6r2%22Q01%:11r7%113%73N31p091pR8Q:1%A3=5Gp021p0A1p0E1p0L1pJQ41pHQ61pLQ<1pQBQC1").
Proof. intros S R M1 M1'.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold tfrk, tocell in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Definition rinvH (R0 Rc : bvmap 5 word) (V2 cls F : Z) : Prop :=
getr Rc (reg 2) = Z_to_bv 64 (V2 - 128) /\ getr Rc (reg 8) = Z_to_bv 64 (V2 + cls) /\ getr Rc (reg 9) = Z_to_bv 64 (V2 - 128) /\
getr Rc (reg 18) = Z_to_bv 64 F /\ getr Rc (reg 19) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 20) = Z_to_bv 64 (F + 32) /\
getr Rc (reg 24) = Z_to_bv 64 F /\ getr Rc (reg 25) = Z_to_bv 64 2147450880 /\
getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4) /\ getr Rc (reg 27) = getr R0 (reg 27).
Definition HIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 27]%nat.
Lemma rinvH_keep : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "Q9&:y5'Q7yR0%211%5241'7&Dr6r5r3r2r1%6554321'2&J&B%23351'6&Gr7&Q6&O%11<%32G1%6251r8%8213%:3H31p0<1pR<@1r4%I56HG1Fp031p0E1pBM1pR:N1pR6O1pQ2Q11pQ0Q21pNQ31").
Proof. intros R0 Ra Rb V2 cls F.
intros (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27) KS. unfold rinvH.
rewrite !KS by (cbn; tauto). repeat split; assumption.
Qed.
Lemma rinvH_ks : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "QI&:y5'Q7yR0%211%5241'7'1'2%211&Dr7r6r4r3r2%6554321&Jr1%23;15'6&Gr8&Q6&O%11:%32I1%6251r9%8213%:3J31p0<1pR<H1'0&L&K&I%11C%33N1IqR<O1&B%73Q121(4%G3:21r:r5%Q452HQ3Q21p041p0@1p0Q11pDQ91pBQ=1pR:Q>1pR6Q?1pQ2QA1pQ0QB1pNQC1").
Proof. intros R0 Ra Rb V2 cls F KSL.
intros RI KS HB. apply (rinvH_keep R0 Ra Rb V2 cls F RI). intros k Hk. apply KS.
rewrite forallb_forall in HB. specialize (HB k Hk). apply existsb_exists in HB. destruct HB as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma rinvH_pres : ltac2:(TCodec.tc2 tcn__PmAHarnessStmts "K&:y5'Q7yR0%211%5241'7&Dr6r5r3r2r1%6554321&A%1276r8r4%;52:918p041p071pB?1pR:@1pR6A1pQ2C1pQ0D1pNE1").
Proof. intros R0 Ra Rb V2 cls F.
intros RI RP. apply (rinvH_keep R0 Ra Rb V2 cls F RI). intros k Hk. apply RP. unfold callee_saved_idx.
unfold HIDX in Hk. repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.
Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) PMTAL.foot_a.
End PMHAS.

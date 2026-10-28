(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4spa () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<rw_cells_appK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_z4s3_iface3SPAc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_z4spa8rwc_consK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C47Corelib4Init5Logic6eq_ind".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma rwc_cons : forall m A c cs, rw_cells bsegs m A (c :: cs) <->
  rw_cells bsegs m A [c] /\ rw_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4spa ()) [] "h01Ah11Hh22H0h32H1h41ch52csh65lemmah71mh81np;1p;3p;2p;9p;5p;4p;6p-1R0g0000R1p4p710p9P0p1000\R2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g001:R0p4p710p9g0024j13Tg002Yj1<Tg0037j1:Tg003Zj1=Tg004<j1GTg004\j1ETg005<j36Tg005\j3;Tg0069j18Tg0072j12Tg007Rj21Tg007oj24Tg008JR2j27Tg008cj15TP1j2FTP0l9DTg009Wj5CTg00:Uj49Tg00;0j5@Tg00;Mj2ATg00;mj1BTg00<Qj6?Tg00<oj4>Tg00=eR0f2R1f1R3f0R4C>p=0g00>Z#3#3#3R5#3#3#3#<#:%<5#:#=[g00??g00?]R5%G5f3R6%E5R79653R8=;54701A0618R9%88#2,11=064'4R:'7p-0R;P2g00@Rf4R2A6517R<=;53706A026<R=%8<#2,16=023'4P4%51#2,16=023R<,4=R>P>1F;>M9DW6P0P6P1P8P4DCg00ACR8%53R0%24,16=023,4=/7>X88%20,11=064,49R9P>[R8P8P=P<P>f5R>%56#2,12;01f6R1A652770>%52#2,1>=016P3P4C9W3X2=P4D@X19R4P4C9g00Ab,A0%B0E?17:9eO2W5W4W0W7o"). Qed.

Ltac rwc_norm H :=
  lazymatch type of H with
  | rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
      let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) in H by lia
  | rw_cells _ _ (?a + Z.of_nat ?k) _ =>
      let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H
  | _ => idtac
  end.
Ltac rwc_peel H :=
  lazymatch type of H with
  | rw_cells _ ?m ?A (?c :: ?cs) =>
      let H1 := fresh "RC" in apply rwc_cons in H as [H1 H]; cbn [csize] in H; rwc_norm H
  end.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_enframe MallocTree MallocKit_B.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocKit_B2 () := "C35stdpp4base6LookupC69OSSVerify5KrLib2CJ1A:MallocTree>pans_mem_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introC69OSSVerify5KrLib2CJ4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2CJ1A:MallocTree3memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B2 ()) ["AC_1"] "h04__p1h14__x1h21mh31nh42H0h57__arithh64__ffh78__varmaph85__with91Hh:1ch;1hh<1oh=1pp;4p;2p;1p;6p;3p;7p;8p-1R0p10000R1p4p710p8P0P1p4p7210p8g000Dj4TTg001Gj46Tg002Dj23Tg002`j11Tg003Ej1STg003cj22Tg004?R1j27Tg004Zj24Tg0057j25Tg005Tj2@Tg0064j1>Tg006Tj1=Tg0074j2RTg007Rj1QTg0080j1KTg008[j2<Tg009>j2FTg009aj4;Tg00:Lj6ETg00;0j1DTg00;Rj2CTg00<4j2BTg00<Nj2GTg00=:j3HTg00=Yj4ATg00>Kj2ITg00>kj4JTg00?Fj3?Tg00?oj1LTg00A1j3MTg00AKj7NTg00Aoj7OTg00BSj8PTg00C7R0f0R2g00CWR33Mp=0f1R4g00D7R5g00DVR6P6g00E6R7P2g00EVFNp=:f2R8P5P6P6P7P4P2FOp=9f3R9P5P6P6P7P8P4P2GPp=8g00F6g00Fng00GfR:P9P8P4P2CTg00HDR;P9P8P4P2C6R<'3g00HbR=#1#1#1#1#1#1#1#1#SR>,2<'7f4R<P9P8P4C6R?,4;R@15?>RA%0@%0AP11442#01384RA[13421484#0[R@1498#0\A1@42P2n2001000000120000000X2:X3:P@^2:^3:P2P;f5R@P<P9P8C6RAp-0RBg00IGRC#>RD%=CRC1R:4RE%Q:RF%K:RGP:1<:;g00J31F:=R=C;,:GRHPGP5P6P6P7P9EER559G%D6R6PHC81CG7R7P2P81B031G28#0dAH:;4CAR3b6b7b8X1:W013;2/7413;4[^1:^0BP2f6P@P<P9C6R</2>P<P8O3b5O3b4P11542#01284R1[12421584#0[R@1598#0\11I42P2n2001000000120000000X2:X3:P@^2:^3:P2PAP>PDPCPEPFPGP:P=g00JZ1<:>C;,:GR=99G5P6P=C8P7P3b6b7b8X1:X0B122>,74124>[^1:^0BP213;<P<P8O3b5O3b4CJ3?%L?#0eb9X;:W:W=W<o"). Qed.

Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

End AC_1.

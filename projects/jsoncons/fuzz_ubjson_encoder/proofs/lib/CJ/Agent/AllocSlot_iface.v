(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp Malloc_iface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AllocSlot_iface () := "C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z4succK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init5Logic8eq_ind_rc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent?AllocSlot_iface8AS_STACKC13~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition AS_STACK (fuel : nat) : Z := 128 + 96 * Z.of_nat fuel.

Lemma AS_STACK_S f : AS_STACK (S f) = AS_STACK f + 96.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSlot_iface ()) ["CEIL_WRAP_1"] "h04__x1h11fh27__arithh34__ffh48__varmaph55__with64cstrh71zp;1p;2p;3p;4p;7p;6g0000j15Tg000Pj1NTg000nj14Tg001Sj18Tg0021j1FTg002Vj26Tg0033j20Tg003Pj32Tg003jj1>Tg004Oj2=Tg004kj1<Tg005Kj1;Tg005kj2MTg006Ij1LTg006gj1KTg007Rj27Tg0085j2ETg008Xj33Tg009;j39Tg009^j4CTg00:Ij7BTg00:mj2ATg00;Oj2@Tg00;ij2DTg00<Uj3?Tg00=4j4GTg00=fj1HTg00>Ej1ITg00>ij6JTg00?Gj1:Tf0R0#4#4p=1g00@cR1g00ABR2%50R3#Ng00A`R4#4#1#1#1#8R5%F4#4#1#1#8R6/60'0R7f1R8#5,66,05/06522X72%>0g00BER9/=3g00BcR3#<%;31M28%L2%K2R3g00COg00CnR:P:g00DNR:P21725R;1726R<1E24R=%84R4,72532592532g00DnA92<=932;=32<CCg00EUFB1A3:P0f2R:g00F5R3g00FUR<'@1D0:=23<dA?298CGb3b4b5X021004,66,051076522^02P0%5:O1b2b6%H0R:#5%I0EJ%::%:0/06522eX11P0O1W1o"). Qed.
Lemma AS_STACK_ge f : 128 <= AS_STACK f.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSlot_iface ()) ["CEIL_WRAP_1"] "h04__x1h11fh27__arithh34__ffh48__varmaph55__with64cstrp;1p;2p;3p;4p;8p;7g003jj1STg0000j15Tg004Oj22Tg00G5j28Tg00=fj19Tg00G^j3LTg00HGj2BTg00I3j2ATg004kj1?Tg00I_j3>Tg005Kj1=Tg005kj2;Tg006Ij1:Tg006gj1RTg007Rj23Tg0085j2QTg009^j47Tg00J?j1KTg000nj11Tg001Sj16Tg0021j1@Tg009;j3CTg008Xj3DTg00Jaj8ETg00:mj2FTg00;Oj2GTg00;ij2HTg003Pj3ITg00<Uj3JTg00=4j4<Tg002Vj2MTg0033j2NTg00?Gj1OTg00:Ij7PTf1R0g00COR1g00CnR2P2g00DNR3f0R4g00EUFPp=4%14#1p=0g00@cR5%S4g00BER6%54'2g00ABR7g00BcR8g00KER9,87R:%99#9,879L7:g00Kd'B'A%?83>%=81;70%:7%R7R8P1P2P2P3P71376g00LPR1g00A`R:,Q7R9C7,48%K2P7%1:#0#0#0#6R2,37R;P1%@:#1#0#0#6R:,37=C799D7;C7,48GE1F83P4f2R8g00F5R3g00FUR;'G1H48=I3;dAJ760C<b3b4b5W012641M:0,N2,22[^07P4%58P0O2b2b6%O4,22eX15P4O1W1o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1MemcpyBase () := "C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxK47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib<RefMemcpyLib:sub_lengthC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib<U1MemcpyBase3sb_C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions=bv_wrap_smallC47Corelib4Init5Logic6eq_symC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Record mcH (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn RSEGS mem0 src (length bs) = Some bs;
  Hdst : store_ok RSEGS mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
Context {fx : FPState}.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  Let Hn := Hn _ _ _ _ _ HOK.
  Let Hlen := Hlen _ _ _ _ _ HOK.
  Let Hsrc := Hsrc _ _ _ _ _ HOK.
  Let Hdst := Hdst _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ HOK.
  Let Hnws := Hnws _ _ _ _ _ HOK.
  Let Hnwd := Hnwd _ _ _ _ _ HOK.

  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).

  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.

  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
Proof.
ltac2:(KReplay.run1 (kr_t_U1MemcpyBase ()) ["MC"] "h01xh12Hah24__p1h34__p2h44__p3h54__x1h64__x2h74__x3h84__x4h94__x5h:1Hh;2H0h<2H1h=2H2h>2Hjh?5Hlen0h@2HmhA7__arithhB4__ffhC6__sat3hD6__sat4hE8__varmaphF5__withG1ahH4cstrhI5cstr0hJ1jhK1mhL1nhM1yhN2z1hO2z2p;1p;2p;3p;<p;4p;6p;5p;Bp;7p;8g0000R0j15Tg000PR1j2?Tg000mR2j20Tg001Ij1:Tg001nj1qTg002Lj1gTg002oR3j1ITg003Oj2PTg003fR4j2NTg004@j2>Tg004]j2<Tg0057j2UTg005Wj37j1STg0061j2fTg006Tj3eTg0071l<QTg007Vj4cTg008=j1MTg008bj2VTg009Dj29Tg009`R5j22Tg00:;j2@Tg00:Uj1OTg00;3j2^Tg00;[j2]Tg00<8j3\Tg00<\j1;Tg00=;j28Tg00=dj1[Tg00>Bj2ZTg00>cj3YTg00?Lj2FTg00@8j1zTg00@Xj3GTg00A8j1yTg00AXj2JTg00B6j4XTg00BTj1wTg00C2j1sTg00C]j2=Tg00D@j1KTg00Dej2pTg00EHj1oTg00Ejj3RTg00FMj2hTg00Foj2iTg00G[j3jTg00H:j4kTg00Hlj4lTg00IWj6dTg00J5j5mTg00K1j2nTg00Kfl<bTg00LKlBaTg00M1j3rTg00MZj6`Tg00N>j4WTg00Nij7tTg00OMj7_Tg00P1j7uTg00PUj8vTg00Q9R6f0R7'0p=4g00QWR8g00R5R9P8P8P3f4R3P0f3R:g00RTf2R;f1R<P7M<bp=LP9P9P9P8P8P8g00SAP0P0P0P1g00Saf5R1P3P:P;P<P7MBap={P9P8P4P0P2g00TDP1P3P:P;P<P7M<Qp=xA78<7p=6A7876p=AAr8<7p=1P<g00TfR2g00UER4P4g00UeR=P7E`p=HP8P<g00VEP7CWp=BP<P2P4P4P=P7g00VlFtp=3P;P2P4P4P=P<P7F_p=CP;P2P4P4P=P<P7Fup=TP8P<g00WLP7CWp=DP:P2P4P4P=P;P<P7Gvp=E%4<%5<R2,?;p,1nR>'0g00X3R?#:R@#:#:RA#q#gRBp,2bsRC%I:RDP;P9%I>RE%I3/P:/N7XL91PD;RF/NE1>6:RG%5;RH'?RI1>6>RJ'0PFPIPDPGP7X08RG1>67X08RDP:P:1<8:DLP;PH1<8HE{PEPJPGPDP>P>1<8>DLRGEx1UBCRC=79E%5CRH/6JRIP9P8%S9P0%S8%57,62A79<71f<73eXM9X09PCPH1<8HPEPDP>O1PGM<Qp,4HlenRGCcPI%MC%4H%M3%53#41V6>196>RH16J>'210>6%AJ'2'@PJP8f8RJ,V6196J1>6JRI/6J'210J6%AI'2'@f9RI,>6P8%O@RD%:A#:#:#ORA'^196D%4A1]DARE,96[[%4DR2g00XXR0A\DA<UW1%4E\0^12p,2Hn%4>R219>ERE'2P5P2PEf=#5,?3f6R5'0P7p-0R0g00Y4RAg00Y`RD#;RF#;RK#;RL#;RM#;,88RN188MRM%[?,Z8188L5Y8RL188KRK188F188DRD'1'1'1'1RF'1g00Z?RO'F1FFO11KD,1L,1MRM/FO11NM/FO%zA5GA5GA5GA3G%yAP81J8;P<P81J83P:1J81CXCX%w8%s8RAf7RO,HA1=8?RM%K?R?#K,=8RN'B,3A5CA1HAJ1p86RL,BM,3A5CA5TA%o4R4PA1HAI1=8?R?%K@,=8RD'B,3A5CA1DDL,3A1B?L,3A5CA5TAP4PA1=8@R@9R8N/DD,3AP4PA1DLN,3AP4AR8M@/D?,3ACECECECE1hA=P7P;g00ZkRAg00[KR='<1i7;=7A=dAj86<CkbBbEbFX58X68X78X88X98X20X30W41673,21%A7,25'@16:3,2J1036%A:'2'@1?5:/01%4O1?31/05[[[[^58^68^78^88^98^20^30^40P7PHfBRH/06196HPHP>f:fA#5PJPIf;f?f@O<bAX;EX:2P<P7O2n2001000000121000000bGbCbDbOb=bNb<bIbHb?ClPCPGEdDm1n:;,UB=79;eW@W>XK9XJ8o"). Qed.

End MC.

Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

Ltac cond_lia :=
  rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

Lemma u_andi : forall (x : word) imm, (0 <= imm < 2 ^ 64)%Z ->
  bv_unsigned (v_andi x imm) = Z.land (bv_unsigned x) imm.
Proof.
ltac2:(KReplay.run1 (kr_t_U1MemcpyBase ()) [] "h04__x1h11Hh22H0h32Hah47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1zh;2Hih<3immh=1xp;1p;2p;3p;4p;7p;6p;8g001Ij12Tg001nj1[Tg002Lj1ETg00:Uj1=Tg00;[j2NTg009Dj21Tg009`R0j28Tg00[kj23Tg00\Uj26Tg00];j24Tg005Wj35Tg00;3j2>Tg00<8j3ZTg00@8j1UTg00A8j1TTg00AXj2MTg00BTj1LTg00C2j1KTg00C]j2GTg00Dej2:Tg00]Yj3FTg00N>j49Tg00EHj1DTg00OMj7CTg00FMj2HTg004]j2BTg00Foj2ITg00G[j3JTg00H:j4ATg00^<j3;Tg00^hj4@Tg00_Dj1?Tg00`;j4OTg00a5j6PTg00aQj2QTg00b7j2RTg00IWj6STg00bfj2YTg000mj2XTg00Nij7WTg00PUj8VTg00Q9R1f0R2'Xp=0f1R3g00TfR4g00UER5P5g00UeR6P2g00VlFWp=<f3R7P4P5P5P6f2R8P3P2GVp=7g00X3R9#2R:#2#2#2#2#2R;#[R<#Eg00QWR=%02R>%=:R:%=;R;'NR?,12R@'8P=13<8RA16<3RB'4RC,6<13<7RD/48RE95=2X:=P=PBP31>:;RF111:%0;111?[[RG%0:RHg00XXRIAZ:;3UW3R;%0?\I^3HRHP0%07117?f4RI#0RJ11I?RK'8P8f5#0RLf6RM/1?g00Y4RN#URO%TNRN1M=3RP%L=RQ%K=RRP=1G=9R9g00cZ1:=:=F=<C9,<RR:%D5RSPRP=1:=1g00WLP9C9,<RR9PSPRP4P5P5P6P9P:FCC7C71HR6R6P2P8g00ZkR:g00[KR5'B1I28=5:5dAJ=13CAR1b5b8b9X0=%03R5%08118?'8[\@^0=P2f8P3P8O3b4W2W1P3P2O2n2001000000121000000b6b79;<3C@A5=3BP=P813<IRI/42,6<14I755=X:=PDP8%?7PFPGP;PHP0PJPKPLP7%0Mf7/1?POPNPPPQPRP9PSP9C7P6P1b5b8b9X0=P5\>^0=P2f9P8O2b4W2W1P3P2O2n2001000000120000000b6b7CO9;<E16<8P2EPb11Q<C,3<1R<CES1Y83,3<14A355=eW;W<W=o"). Qed.


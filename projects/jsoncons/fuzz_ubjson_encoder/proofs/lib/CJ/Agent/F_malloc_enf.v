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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_malloc_enf () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~C47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree5implTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree:implT_peekC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:bad_answerC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3rd8C13~~~C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula08C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframe3rdvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree8pans_memC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev05C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>peek_answer_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree>pans_mem_rangeC13~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introC47Corelib4Init5Logic6eq_symI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6PState00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_enf9implT_rd8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4rd16C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q)) s Q ms -> implT o (rd8 st q k) s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_F_malloc_enf ()) ["CEIL_WRAP_1"] "p'0h01Hh14__p1h24__x1h31mh41nh52H0h61vi001vh71Qh81Rh97__arithh:4__ffh;8__varmaph<5__with=1kh>2msh?1oh@1qhA1shB2sthC2RGhD1bhE1ci011chF1hi021hi034hinti041xp;1p;5p;7p;3p;2p;4p;6p;;p;8g0000R0p4p70R1g001>R2p4p710p8P1g002NR3p4p710R4p8P1P3p4p7210p8p1002kp4p70P4p8p200R4g0049R1p4p710p8P4g005DR5p4p7210p8P4g006XR6p4p7210p8P4g0081R7p4p710p8P4g009ER8p4p710p8g00:RR9p4p711g00;1R:p4p73101p8P1j1CTg00;Uj5dTP5j72TP3j3GTg00<mj2cTg00>Aj3UTg00>^j2PTg00@1j25Tg00A?R3j46Tg00BVj3HTg00Cdj3ATg00E4j19TP7j2:TP2j5bTg00FLj4ZTg00Gij24Tg00HEj11Tg00Hjj1QTg00IHj23Tg00IdR2j2;Tg00J?j28Tg00J\j27Tg00K9j2OTg00KYj1NTg00L9j1MTg00LYj2LTg00M7j1KTg00MUj1ITg00N@j2<Tg00Ncj2JTg00OFj4=Tg00P1j6FTg00PUj1ETg00Q7j2DTg00QYj2RTg00R3j2STg00R_j3aTg00S>j4`Tg00T0j2\Tg00TPj4YTg00Tkj3WTg00UTj4XTg00V0j3BTg00VJj6VTP6l;[TP8j4TTg00Vfj7]Tg00WJj7^TP:j8_Tg00WnR:f0R8g00XNR63Bp=0f1R7P9g00XnR5P5g00YNR1P8g00YnF]p=>f2R;P9P5P5P1P7P8F^p=?f3R<P9P5P5P1P;P7P8G_p=@g00ZNR=g00[`R>g00]2R?f4R@#C[RAg00]PRBf5RCg00^`RDp-0RE[\B[RFp,4RUNpRGf7RHf6RIP<P=P3PIPCP@DdO1P;P7P8F2g00_gR3?G?C,cIAU3?C'Pg00`ER3P3PGf:RJf9RKPIP3P?P8P8PJf8RL15KLP8C6RMn0110400021010010102O1PCP@P<F2PGf;RNPJP3f<R3#CP7PLP8O1g00aXROP?P315JKRP=HK8P:f>RQ9AO?RR%98RSPKP8O1RTf=RUPKP7O1':n0100000020000X6?Dbn0110400021010010103PIPCP@F2]0P8PGPNPJPHP8O1PIPCP@F2P8W0X6?P8O1PGPNPJPHPMO1PIPCP@F2PGP3PNPKPPP7P:PRPSPTPKP;O1,:Un0100000020000X6?PHPIPCPNPKPPP7CZg00bfRTPNPKPPP7C6RP'4g00cDRS#1#1#1#1#1#1#1#1#QRR,3P';P:P3PJ15NJP;C6RP#9RMP618TPRV17PRRP%0V%0PP21878#014;7RP[147818;7#0[RV18<;#0\P1O78P8n2001000000120000000X3?X4?PV^3?^4?P8PTPUPN153NP<C6RVg00ciRP#NRW%MPRP1L?7RX%K?RY%I?RZP?1<?Tg00dU1J?SRSC=,>ZR[PZP9P5P5P1P<EFR95?Z%E5R5P[C@1DZ1R1P8P;1R:61S8;#0dAa?T7C`R[b:b;b<X2?X1E14T8/;714T7[^2?^1EP8PQP315U3P@C6RU/3RPUP;O3b9O3b5P21778#013;7R2[137817;7#0[R317<;#0\21\78P8n2001000000120000000X3?X4?P3^3?^4?P8PVPRPWPPPXPYPZP?PSg00e<1<?RC=,>ZRS9?Z9P5PSC@P1P[b:b;b<X2?X1E138R,;7137R[^2?^1EP814TUPUP;O3b9O3b5CY3W%0MeCXAB:6MP:P6PGf?R6PQP:f@9AO?P8PNPUO1PNP@O1,:6n0100000020000PJPKPLF2XD:P;%9VP8EVb5bCM;[W0XF?P8O1n0110100021010011103P7O1bEPGPLPHPLPIPCP@CTP<P;P7F2eW0X>DX7FXABX=AX@0XB>X?=X84PHPIPCP@P<P;P7P8O8X>DW7WAW=X@0WBW?X84o"). Qed.

Lemma implT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> implT o (rd16 st q k) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_enf ()) ["CEIL_WRAP_1"] "h01Qh11Rh22b1h31kh42msh51oh61qh71sh82sth91Hh:2b0p;1p;2p;7p;4p;9p;5p200R0g00ecR1p60921001p8P0g0049R2p4p710p8P0g005DR3p4p7210p8P0g00g=R4p4p710p8P2j1;Tg00HEj10Tg00Hjj15Tg00hKj23Tg00iYj27Tg00j6j22TP3j76Tg009Ej4:TP1l94TP4j48Tg00;Uj59Tg00ZNR4g00A?f2R1f1R3f0R2D9p=1g00[`R5g0000R6g00]2R7f4R8#;[R9g00]PR:f5R;g00^`R<p-0[\:[R=p,4RUNpR>f7R?f6R@f3RAA1@;8g00cDRB#0#0#0#0#0#0#0#0#5RC%5BRB,3891@;'7'2O1P1P3P2F6f8RDP?P@P;f9P?13@BP@17C2RC,23O1X27C:X:7PAP1P3PDP?P@13;BP;A1D?@/2CO1X27PAP1P3P2M94M94P>PDP?PDP@P;P8C8PAP1P3F6eW9X4<X0=X7:X39X66X85X54X10P?P@P;P8PAP1P3P2O8X4<W0W7W3W6W8X54X10o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enf_off0 (o : mem) (st1 : mstate) (b : aptr) (stride idx : Z) : Z :=
  let q := snd b + (16 + stride * idx) in
  if rdv pans_mem o st1 (fst b, q + -3) =? 0 then Z.land (c_mmap_counter (ctx st1)) 255
  else Z.land (rdv pans_mem o st1 (fst b, q + -2) + 256 * rdv pans_mem o st1 (fst b, q + -2 + 1) + 1) 255.

Definition enf_leaf (o : mem) (st1 : mstate) (g b : aptr) (idx n : Z) (st' : mstate) (p : aptr) : Prop :=
  exists off, 0 <= off /\ 16 * off + n + 4 <= get_stride (get_meta_rec st1 g)
    /\ p = (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx + 16 * off)
    /\ st' = havoc p n (fst (enframe_at st1 g idx n off))
    /\ p = snd (enframe_at st1 g idx n off)
    /\ off = fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx) ((get_stride (get_meta_rec st1 g) - 4 - n) / 16).
(* [comment removed for export] *)

Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_enf ()) ["CEIL_WRAP_1"] "p'0h01Ah11Bh22C'h31ei001eh41fh51ai011ah61bi021bi031pi041xi051yp;2p;3p;4p200R0g002NR1p4p710p8p201R2P1p4p7210p8g00jSR3j25TP1j31Tg00>Aj30Tg00V0j32Tg00k3j44Tg00QYj23Tp202R1f2R4f1R5'5R6f3R7P7\7[R8P3f4R9P7P3f5R3P9P9f0R:P7P5P:O2n2001100000120104105P5A139:A039:O2527P5f6R3P9f8R;f7R<P;P<P5P:C4R=31A0;<=O2,33X63W5P5P:O2n2001103000120101102X48X36X21X12X00P9P7P4P5P:O5W4W3W2X12X00o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)

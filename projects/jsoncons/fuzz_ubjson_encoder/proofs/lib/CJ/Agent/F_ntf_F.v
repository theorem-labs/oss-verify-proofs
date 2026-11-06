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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_ntf_F () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_B8fm_factsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc?sc_in_seq_rangeC13~~~C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specK46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init9Datatypes4andbK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega5Tauto4kind02K47Corelib4Init5Logic4True01I45stdpp9bitvector;definitions2bv00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5zerosC13~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition seq_st (ns sc : Z) (st : mstate) : mstate := record_seq sc (upd_ctx (set_seq ns) st).
(* [comment removed for export] *)

Lemma fm_facts_ctx : forall st f g,
  c_free_meta_head (f (s_ctx st)) = c_free_meta_head (s_ctx st) -> fm_facts st g -> fm_facts (upd_ctx f st) g.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_F ()) ["CEIL_WRAP_1"] "h02Hhh11Eh21Hh31fh41gh52hdh61oh72pvh82sth91xp;1p;3p;2p;6g0000j18Tg001?j11Tg002Yj30Tg0033j25Tg004Gj23Tg005Xj1<Tg006ej24Tg007Gj6;Tg007cj16Tg008<j27Tg009Sj2:Tg00:ij19Tg00<9j22Tg00<Tj2=Tg00<ng00>@R0P0]9g00?PR0g00@^R1f1R2f2R3#8R4O1#1%1430f3R4/52f4R5f5R6'3#<#1f0R7,40R8501P1P6f6R9#8R:O1#114039017X61P7%1:R:P4E;1402901:P4P3P7O2b0A0025#61369/72f7,39R9/:3#9=018A0076#61797'2'2X70,=0'2'2eW0X501345/53eW2W1W4W3W8o"). Qed.

Lemma seq_range_test sc : 0 <= sc <= 63 ->
  (31 < Z.land (sc + -7) 18446744073709551615 <-> sc_in_seq_range sc = false).
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_F ()) ["CEIL_WRAP_1"] "p'0h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with62H0h76__sat1h86__sat3h91bi001bh:2b0h;1Hh<1zh=6__sat0h>6__sat2h?2Hah@2schA2GEhB2H2hC3HschD1LhE1ehF1op%0p;1p;2p;3p;4p;6p;5p;7p;8g00Alj18Tg00BQj1;Tg00Boj21Tg00<9j2ATg00CKj1fTg00Cij24Tg00DFj1@Tg00Dkj2ZTg00EHj2BTg00Ehj20Tg00FDj1LTg00G]j22Tg00H6j2uTg00H[R0j2kTg00I5j2FTg00IRj2?Tg00Ioj2bTg002Yj37Tg00JLj2_Tg00K4j3^Tg00KXj2[Tg00L9j2GTg00LSj1YTg00M3j1XTg00MSj2WTg00N1j1VTg00NOj1UTg00O:j2TTg00O]j1STg00P?j2KTg00Pbj3NTg00QEj1wTg00Qcj3vTg00RFj2tTg00Rhj2sTg00STj3oTg00T3j4jTg00Tej3QTg00UHj1iTg00Ufj4ITg00VQj6eTg00W5j4dTg007Gj6HTg00WVj4cTg00X2j2PTg00XTR1j3ETg00Y8j2OTg00YZj5aTg00Z>j5gTg00Zbj6hTg00[Fj4CTg00[aj2`Tg00\@j6RTg00\^j1lTg00]<j2mTg00]Zj3nTg00^=j2]Tg00^[j7\Tg00_?j6pTg00_cj7qTg00`Gj8rTg00`kR2f0R3'1p=9g00aIR4g00aiR5773p=Jf1R6/]3=745p=6g00bIR7/K3p=<P7P6g00bgP3CIp=>P6g00cNR8g00cmR9P9g00dMR:P3g00dmF\p=3P7P6g00eMP3CIp==P6P8P9P9P:P3Epp=Mf2R;P8P9P9P:P6P3Fqp=Df3R<P8P9P9P:P;P6P3Grp=51463,0;p=:%93R=g00f4R>#8#8R?#8#8R@#8#;RA,13'AP7%f?RB,46RC%@>RD#;RE%@DRD#@#@#@#@RF#;RG'ZRH'BRI%;@R@/03RJ%L;#J'2X<7%;?R?,u6106?RK11?6RL'kP010;?11?;14<B/BH,0@1F?<%8D#8#8#;RD,?<'6'2P310<?P7f4R0/4BRM/BHRN14MHROP7%;>RP/bH,4M/BHf5RQ/4BRR/4HRS9773X<71_EGRT102ERU%9GS00102H[RV[RW%9ERXg00fYRYA^EG6UW?RZ%9H\Y^?XRXP6g00g51[2E'GPUeO1RUPVp-0R[g00g[R\#YR]%X\R\1W76R^%V7R_%U7R`1T7>R>%<?Ra'>,3`Rb%S9RcP`1K72Rd/=>,3`1M`<Re5D`S01Pc%<B9N7>Rf%<E%wF5v7RF5N7RE,=d,3`1>EF,3`5D`C5C51t`:RgP3P;g00hGRh,G41s3;=74hdAo726CjRib3b4b5X17W0103?Rj%96/A;14;BRk/4HRl#910lH'A[[^17^0[P3f8Rl/1APlP0f7RmO4b2b7b=b79QOHPNPMPPPHPTPWPZPXPUPVP]P\%i7RPP_P`P8P9P9P:P7PFg00hgPdCI,3`EePgPib3b4b5A77H2g00iNR2[P3b2b7b=b7CdEHCcA77ONP7PSf6RS,F?RO1?SD'6,2JX<71P?Q11?Q10Q?1F?QR:3EPOP4P111?mRO10m?Rnf9Ro/4B=:@H1?oDRp,66'2P611?l1OoDS0210oD11Do;EpS03f:Rq/?DRrP4P1f;Rs/0DRt11DsRsf=/4BRu=:@HRv16h6Rw'2P6f<Rx/0DRyA74h5Rz\vf>R{/4BR|=:@HR}\zPTPWPZPXPUPVP]P\P^P_P`1=a>,3`RaPcP`PbPcPeC5C5PgPib3b4b5X17X0[11?3R~P<\K[^17^0[P3PzfBRKPoP{O4b2b8b>b8VvPTPWPZPXPUPVP]P\PPP_P`P`P8P9P9P`P8P9P9g00ikRoDaP`P8P9P9PoDgEhPc1M`;C5PgPib3b4b5X0[P6\z^0[P314KB=:@HP0O2b2b8b>b8VzCC16hhRo,2veW6P3O111DxR9A7455R8\vP}\81G45S04VvPTPWPZPXPUPVP]P\P^P_P`Q01Pc%<@R}/>E,3`C5PgPib3b4b5X17X0[1A=6A:@CH[^17^0[P311KAPKfAO3b2b8b>b8V8CCRK16h5R=,2veW6P3O1n200210000000021100011000b:b9W;P3O110l?Q02Q03PrP4P1PtPs1656Rr,2vP6PK165hRE,2veX6yP3O1PK1655RK,2veX69P3O1n200210000000021100011000b:b9W;P3O1n200210000000021100011000b:b91BRHP3EHb;WDP3O111?<P7PM1?QD,6:,2JX<71P?011?0100?1F?03EP:P4P111?S10S?A:@lB1?lDR?,66'2P61OlDR:10lD11Dl;E?R?PpP4P110qDRJ11DqRQA:@xBRx/2wP6Pz\x10@uRu\zP]P\P^P_P`1>}f,3`R}PcP`%<DRw,>>,3`PcPeC5C5PgPib3b4b5X17X0[A:@3B106DP<[[^17^0[P3PzP{P6P;O4b2VxP4PhP4P[P3PYP2n0110000020000XE4g00jKP5P3EHP210@|R|/`3bBVzCC12xoeX6tP3O1P8\xRoPu\8RuQ04VxRzP]P\P^P_P`1=w>,3`PcP}C5PgPib3b4b5X1711D310@C[^17P3P{P;O2b2V8CC12x=eX6sP3O1n200210000000021100011000b:b9X;OP3O1P:P?PpP4P1PJPQ12xrP6PoPuPzP]P\P^P_P`PbPcP`PaPcPeC5C5PgPib3b4b5X17X0[P<\L\j^17^0[P3P|P{PSPqO4b2V8CCR812xEeX6tP3O1P812xKeX6sP3O1n200210000000021100011000b:b9X;nP3O1n200210000000021100011000b:b9PNPTPWPZPXPUPVP]P\P^P_P`PaPcP`%<A,=>,3`9D`ePc1=df,3`1>fF,3`5D`C5C5PgPib3b4b5X17X0[116A,A;%9k10kH'A[\~^17^0[P3%9lPlP0PmO4b2b7b=b79QMHERWAP3O1n200100000021100011000bF10@I%L6#J'2e%lG,mCP]P\PPP_%<G,=d,3`PgPib3b4b5Q00P3b29nCGERWCX@7P3O1X@7o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_F ()) ["CEIL_WRAP_1"] "h02stp;1p;2g00DFj12Tg00QEj17Tg00jgj14Tg00M3j13Tg00kJj16Tg00L9j25Tg00l]j11Tf0R0#1#1#1#1p=0g00<nR1g00f4#2#2#2#7#4#3g00m<#0#0#0#0#0#0#0#0#6'5X01P0O1W0o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)


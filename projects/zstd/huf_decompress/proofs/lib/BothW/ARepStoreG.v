(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (KG_img, KG_hi, KG_shad and 5 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit ARepFrame
     AKit AModelFacts APrimFacts F_aalloc2 F_aalloc F_amalloc_icpt F_amalloc_arep F_amalloc_tailg ARepStore.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepStoreG () := "C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2geC59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula01K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ARepStoreG7kfactsGC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op204K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aalloc2:hdr_b1_midC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW8F_aalloc@hdr_b1_mid_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib5BothW8F_aalloc?lt_pow2_of_log2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic5proj1C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_lt".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wn sp t c AB UB PGE n nodes store :=
  ([(sp - 4096, sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + n); (AB, AB + 16); (shad UB, PGE);
    (ADEPOT_LO, ADEPOT_HI); (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStoreG ()) ["CANSEC1"] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62H1h77__arithh84__ffh98__varmaph:5__with;2H0h<2hih=2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7P1p8P7P3p8P7P2p8P7p1004^R1p4p710p8P7p1005;p4p710p8p1005WR7p4p73101R8p10061R9p4p73110p8P8p1006JR:p4p73110p8P8p1006fp4p710p8P8p10079R;p4p7201p8P8p1007Kp4p7201p8P8P0p4p73110p8P8p1007]R<p4p73110p8P8p10081R=p4p73110p8P8p1008Kp4p7201p8P7p4p710R8P9p4p710p8P8P:p4p710p8P8P6p8P8P5p8P8P0p4p710p8P8P<p4p710p8P8P=p4p710p8p1008^R=p4p710R8P4p8P8P6p8P8P5p8P8p10092p4p73110p8P=p4p741110R=p1009Dp4p73101R8p8p1009`p4p7210P2p8P1p4p7210P3p8P;p4p7200R;P8p8p100:Lp4p7<111111111110P2p8p100:np4p7<111111111110P2p8p100;Pp4p741110R2P7p4p7511100R8p8P8P2p8p100;ip4p741110R2P7p4p76111100R8p8P8P2p8p100<Ap4p741110R2P7p4p771111100R8p8P8P2p8p100<ap4p741110R2P7p4p7:1111111100R7p8P7P2p8P;P=p8P=P;p8g00=8j3bTg00=mj1aTg00>kj15Tg00?Pj11Tg00@5j1:Tg00@Sj1OTg00AIj20Tg00AeR;j2<Tg00B@j2=Tg00B]j2DTg00C:j2ITg00CTj1CTg00D3j2BTg00D\j3HTg00EEj2VTg00F1j1UTg00FQj3TTg00G1j1STg00GQj2ETg00Goj4RTg00HMj1QTg00Hkj1PTg00IVj2ATg00J9j6NTg00J]j1MTg00K?j2GTg00Kbj3@Tg00LEj3FTg00Lhj2LTg00MJj2`Tg00Mdj2_Tg00NPj3^Tg00Njj3[Tg00OIj4ZTg00P;j4JTg00PUj4YTg00Q@j7\Tg00Qdj7WTg00RHj8]Tf0R=#5#5#5#5p=7%5=#5p=X%1=#1p=?%1=#1#1#1p=9%1=#1#1#1#1#1#1#1p=3f2R2f1R7'0/<=p=21<7=,<2p=>g00RlR8/G=p=8P2g00SJR3g00SiR1P1g00TIR5P8P7g00TiP=CYg00UPF\p=4P2P3P1P1P5P7P=FWp=6f3R6P3P1P1P5P2P7P=G]p=;107=,<2p=Kp,2rcR4?b7=%a4g00V0R<#5R0#5#7#7#7R:#1#5#XR9#5#7#1#?#9#3#3#:R>%O4R4'0R?%5:#7#7#1#?#9#3#3#:R:,04R@'<g00VU%5<#1#9#7#9#3#:RA/06RB%99#3#:R9,02RC'<%1<RD#9#3RE#7#7#7#7#1#?#9#3#:RF1024726g00VoRG%:<RH,0=72=RIf5RJ,0ARK1=F=RLf4RM%1E#?#3#3#3#3#3#3#:RE,==,D9RN10M4RO3272J3>X58,I8P7106992AMP;PK10M9f7RK,0ARPf6RQ10Q472N92LK5>IX58,I8RQP=10K9P8f:RR,0Af9RS10S472N92LR5>IX58RIPGp-0RLg00WMRNg00X9RT#C#CRU#C,B81B8U1B8T5H85H8g00XX'V%UN3TRT%SNRNP81E82P71E86CRRU%Q8RV%P8RW%8>1A80R054WPWP3P1P1P5PJENR356W%M1R1PW1A8DRD%89RX54WP1PW%8A1A8<R<54WRYP11G8GRZ=4WZ%8HR[94WZR\56W%8FR]=@8Z=4W<%8ER^9@8Z9F8X94WDA4WD0RZ56W56W96WY56WC;C;C;1LW5R5P=P2g00YDR_g00YdR`'`1_=2=^_`dA[8G7CZR`b8b9b:X28X38X48W1A2>2610A210GHRA92GG1=FG1=GE,D910MJRG52M7267>B[\C[^28^38^48^1LP=P@P4PSPRPKP7P2O7b7CJW6X0PP7P=O2n2001000010121000000W0P=O1106492FMP;10FJPOPQP=10FK10K4P8PIPHPTPNPUPVPW%8:94W096W3P1PWPZP1PWA4W]<P1A4W[[96W\A@8][=4W<A@8[^9F8X94WD=6WZ56W96WY56WC;C;C;P5P`b8b9b:X28X38X48X1LAK62:102610F2AKAHH1=FH1=HE,D9=2MG7267>B[[[^28^38^48^1LP=P?P4PSPRPKP7P2O7b7CJW6W0P7P=O2n2001000010121000000W0P=O1n200100001021100011000b;W0X<8X=8o"). Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6352896 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStoreG ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h94__p1h:2H0h;2H1h<3H10h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7P1p8P7P3p8P7P2p8P7p1004^R1p4p710p8P7p1005;p4p710p8p1005WR7p4p73101R8p10061R9p4p73110p8P8p1006JR:p4p73110p8P8p1006fp4p710p8P8p10079R;p4p7201p8P8p1007Kp4p7201p8P8P0p4p73110p8P8p1007]R<p4p73110p8P8p10081R=p4p73110p8P8p1008Kp4p7201p8P7p4p710R8P9p4p710p8P8P:p4p710p8P8P6p8P8P5p8P8P0p4p710p8P8P<p4p710p8P8P=p4p710p8p1008^R=p4p710R8P4p8P8P6p8P8P5p8P8p10092p4p73110p8P=p4p741110R=p1009Dp4p73101R8p8p1009`p4p7210P2p8P1p4p7210P3p8P;p4p7200R;P8p8p100:Lp4p7<111111111110P2p8p100:np4p7<111111111110P2p8p100;Pp4p741110R2P7p4p7511100R8p8P8P2p8p100;ip4p741110R2P7p4p76111100R8p8P8P2p8p100<Ap4p741110R2P7p4p771111100R8p8P8P2p8p100<ap4p741110R2P7p4p7:1111111100R7p8P7P2p8P;P=p8P=P;p8g00ZDj3yTg00?Pj12Tg00@5j1;Tg00AIj20Tg00=mj1oTg00>kj17Tg00@Sj1^Tg00[;j2BTg00B]j21Tg00B@j2?Tg00AeR;j28Tg00[[j2dTg00\Lj2cTg00\mj1aTg00]Fj2STg00NPj3LTg00]cj2`Tg00^Jj2KTg00^fj2_Tg00_Mj2]Tg00`3j2\Tg00`Yj2[Tg00CTj1JTg00D3j2GTg00D\j3NTg00EEj2ZTg00F1j1xTg00FQj3YTg00G1j1wTg00aUj1vTg00GQj2XTg00Goj4HTg00HMj1uTg00Hkj1tTg00IVj2PTg00J]j1rTg00LEj3MTg00b3j7qTg00Lhj2pTg00MJj2nTg00Mdj2mTg00Njj3lTg00OIj4kTg00K?j2UTg00Kbj3OTg00P;j4VTg00J9j6iTg00bWj4TTg00VUR=j2WTg00C:j2hTg00PUj4gTg00Q@j7fTg00Qdj7sTg00RHj8eTf0R2#2#2p=D%22#2#2#2#2#2#2#2p=5%72#7#7#7p=9%72#7p=b%22#2#2#2p=@f2R7f1R8/02'8p=Eg00RlR3g00VoR17L2p=Qf3R5/071082'Wp=31882,87p=R1078/82,85p=:1012p=C1178/02p=F1082,87,85p=I1h32p=A1078/82p=61U32p==P7g00SJR6g00SiR4P4g00TIR<P3P8g00TiP2Cgg00UPFfp=4P7P6P4P4P<P8P2Fsp=>P5P6P4P4P<P7P8P2Gep=<1W82,87p=jp,2rcR0?y82g00V0R:#2R9#2R>#D#5R?#2R@#2#DRA#;RB/08RC%o0%7:RD#7#9#9#9RE#2#7#bRF#7#9#2#D#@#5#5#;%^0R0'0RG%7E#9#9#2#D#@#5#5#;RE7E0P;f4RH%;?R?'B#Q10?HRI11H5RJP0PJ%@F#5#;RF%9@#9#9#9#2#D#@#5#;R@PHC3PJPB%7:#2#@#9#@#5#;RJPHC37RIC:f5RI11IH%C2%;:RK7E2RLf6RM%5A#5#5#5#5#5#;RA,?2,1FRN7FI1?@2ROPMCIX33#A76056JP71BM?#Qf7RP,0?RQ11PMRRP0PRPFP@PPC3PRPBPJPPC37RQC:P;f8RQ,0?RR11QPRPPPPFP@PQC3PPPBPJPQC37RR760f9RR11RQPLf:RP?FRNPOPPCIX33#A76056JP210?Pf;RR/1PRPPPPFP@PRC3P?PRPPPBPJPRC3C:760P;f<RP/1RRR/00PRPFP@PPC3P?PPPRPBPJPPC3C:f=RR11RPPLf>RS/1RRRPN10OSC:X33#A76056JP210R0f?RR/1SRSPFP@PRC3P?PRPSPBPJPRC3C:P;f@R;/1RRRPFP@P;C3PRPBPJP;C396?;fARR11R;PLfBR;/1RRSPN10O;C:X33#A76056JP2PSPFP@P;C3fCRS11S;PBPJPSC356?fDR;,0J11;SRT/00RUPLfERV/1;RWPN10OVC:X33#ARX'81d;?%C;%C?fFRY/B?RZ#C[[1cV?%Q?R[#a1SY?,??/1Z9L3Y[1`Y?1K1?fGRZ/B?R\#C1K\?'8[1_Z?1K?1fHR\/B?R],K??E]1[1]\?fIR\/S?#Q\[1\\?fJR]/B?=L3]\[g00c21[]?R]eP]g00WMR]g00X9R[#JR^#JR_#JR`#J,G31G3^R^1G3_5N35N3g00XXR_'Z%x]Ra3Y%w]RbP3%v3RcP81X37RdCH%u3Re%t3Rf%=BRg1P3DRD54f%r4RhPf%=?1P3:R:54fRiPfP6P4P4P<AM3:D=4fg%=J=4f:RgFq5>fPhPfPiPhPgC<C<C<1pf<RgP2P7g00YDRjg00YdRk'n1m27=LjkdAl318CkRkb5b6b7X03X1310?8Rj1187Rl/0B10J83j10?710J5[[\C^03^13P2fKRCfLP\PQPRO5b410JCeb<bDbCbBbAb2bFPUPXPaPbP3PdP81X35RXCHPePf1P399M3:R9=4fDRDPhPDC<PgPkb5b6b7X03X13X831128RD/0710l5[^03^13^83P2P0P;PVPMO4b4P=10TF10@;PLAFYVNPOPYCIX33#AP810WFP3PLAFZYNPOPZCIX33ROP1PaPbP3PdP8PcCHPePf%=FRd94f9PhPfPiPh1U31Ri=4fi%=KRN94fiRL5>f%=ARW9O3i9M3d94f9%=@R;=O3i=4f:5>f5>fC<C<PgPkb5b6b7X03X1310DF%CKRD96111175Ri1?1A,1F1?@1/07C:\j[^03^13P2PYPZP8PPO4b4CVW2P2O110@VP3POPKp-0RO1G3`1G3[9N3^5N3/Z_=Y]aPbP3P3PXP7PcCHP8PcCHPePfPfP6P4P4P<PIEi1P3>R>%=E54f5>fPhPfA4f;:PhPfA4f9>PhA4fNN9>fLAO3NW9M3d94f9AO3;N=4f:5>f5>fC<C<C<PgPkb5b6b7X03X13X83W9AE57E10@810iHAEDKK1?KA,1F9F5H1?@KP5CI[[[^03^13^83^9OP2PGP0PYPZPSP8PQO7b4CVW2P2O1n200100001021100011000CTCTW@W?P8P2O2n2001000010121000000W2W>P8P2O2n2001000010121000000W2W=P8P2O2n2011000010121000000W2W;P8P2O2n2011000010121000000b:WEW2XH3XG3o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6352896 * j <= a).
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStoreG ()) ["CANSEC1"] "h04__x1h11jh21Hh31kh47__arithh54__ffh68__varmaph75__with84__x2h94__p1h:2H5h;2H0h<2H1h=2H2h>2H3h?2H4h@2_HhA1ap;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7P1p8P7P3p8P7P2p8P7p1004^R1p4p710p8P7p1005;p4p710p8p1005WR7p4p73101R8p10061R9p4p73110p8P8p1006JR:p4p73110p8P8p1006fp4p710p8P8p10079R;p4p7201p8P8p1007Kp4p7201p8P8P0p4p73110p8P8p1007]R<p4p73110p8P8p10081R=p4p73110p8P8p1008Kp4p7201p8P7p4p710R8P9p4p710p8P8P:p4p710p8P8P6p8P8P5p8P8P0p4p710p8P8P<p4p710p8P8P=p4p710p8p1008^R=p4p710R8P4p8P8P6p8P8P5p8P8p10092p4p73110p8P=p4p741110R=p1009Dp4p73101R8p8p1009`p4p7210P2p8P1p4p7210P3p8P;p4p7200R;P8p8p100:Lp4p7<111111111110P2p8p100:np4p7<111111111110P2p8p100;Pp4p741110R2P7p4p7511100R8p8P8P2p8p100;ip4p741110R2P7p4p76111100R8p8P8P2p8p100<Ap4p741110R2P7p4p771111100R8p8P8P2p8p100<ap4p741110R2P7p4p7:1111111100R7p8P7P2p8P;P=p8P=P;p8g00?Pj12Tg00@5j1>Tg00ZDj3mTg00=mj1lTg00>kj1:Tg00@Sj1\Tg00AIj20Tg00[;j2TTg00NPj3ITg00B]j21Tg00B@j2?Tg00AeR;j26Tg00F1j1aTg00G1j1_Tg00GQj2OTg00HMj1^Tg00Hkj1]Tg00IVj2JTg00J]j1[Tg00Lhj2ZTg00MJj2YTg00Mdj2XTg00Njj3WTg00OIj4VTg00aUj1UTg00Goj4STg00LEj3ETg00K?j2RTg00P;j4GTg00CTj1NTg00D3j2KTg00D\j3QTg00EEj2kTg00FQj3jTg00J9j6iTg00bWj4MTg00VUR=j2gTg00C:j2fTg00PUj4eTg00Q@j7dTg00RHj8cTg00Qdj7hTg00Kbj3bTf0R2#2#2p=F%22#2#2#2#2#2#2#2p=8%:2#:#:#:p=<%:2#:p=`%22#2#2#2p=Bf2R7f1R8/02'6p=Hf3R3/071082'gp=41682,67p=L1078/62,63p=D1078/62p=7f4R110371082'6'6p=5g00RlR5/f2p=91R52p=@P7g00SJR6g00SiR4P4g00TIR<P5P8g00TiP2Ceg00UPFdp=3P3P6P4P4P<P7P8P2Gcp=;1178/02p=CP7P6P4P4P<P8P2Fhp==Ab582p=A1082,67,63p=Pp,2rcR0g00V0R:#2R9#2#F#8R>#>R?7m2%l0%::R@#:#<#<#<RA#2#:#`RB#:#<#2#F#B#8#8#>%\0R0'0RC%:A#<#<#2#F#B#8#8#>RA7H0P;1T7?g00VoRD5I510?7RE117?RFP0PF%BB#8#>RB%2>R>#<#<#<#<#2#F#B#8#>RGP7C4PF%2>#FR>#>RH%::#2#B#<#B#8#>RIP7C47LECD113?RE%>:RJ,0297D2RK111?RL%8>#8#8#8#8#8#>R>,?2RM,1BRN1?G2ROP1D5X35#9PKPL11HMRM1?I2RLP1D5X15#9'677097?3P81T1?=I5Df5RP,0?RQ11P?RRP0PRPBPGPPC4PRPHPIPPC47LQCDP;f6RQ,0?RP11Q?RRPRPBPGPQC4PRPHPIPQC47LP770f7RP11P?PKf8RP/1?RRPNPOPPD5X35#9PKPRPMPLPPD5X15#9'677057?P210?Pf9RR/1?RSPSPBPGPRC4P?PRPSPHPIPRC4CD770P;f:RR/1?RS/00PSPBPGPRC4P?PRPSPHPIPRC4CDf;RS11S?PKf<RS/1?RTPNPOPSD5X35#9PKPTPMPLPSD5X15#9'677057?P210T0f=RT/1?RUPBPGPTC4P?PTPUPHPIPTC4CDP;f>RT/1?RUPBPGPTC4PUPHPIPTC497?Tf?RT11T?PKf@RT/1?RUPNPOPTD5X35#9PKPUPMPLPTD5X15#9'677057?P2PUPBPGPTC4fARU11U?PHPIPUC457?fBRU,0?RV11U?RW/00RXPKfCRY/1?RZPNPOPYD5X35#9R[PKPZPMPLPYD5X15#9R\'6R]'6g00WMR^#aR_%_^R`1O58Ra%^5Rb%]5Rc%@?Rd1J5:R:53cRe%[4RfPeC;1Zc<RgP2P7g00YDRhg00YdRi'Y1X27=IhidAW5D8CVRib5b6b7X0510?210?8Rh[^05P2PYPRO2b4PXP]P_P`P51O57R]P8%U5RXCSPbPcAE5:dRd1J5953cR9PfP9C;PgPib5b6b7X05X85112?R9/08AC8?7[^05^85P2P0PYPQO3b4P[P\P=10WB10GUPKfDR\/1?R[PNPOP\D5X35#9P810ZBP5PKfERZ/1?RQPNPOPZD5X35ROPDP_P`PaPbPc%@BRN93cdPfPcPePf1R5DRR=3cR%@JRj93cRRk5=cRl%@>Rm,ARRn9E5N93cd%@GRo/AR=3c:5=c5=cC;C;PgPib5b6b7X05109B10DJRp97DDRqPF1?D>Rr,1B1?GDP7D5\h[^05P2PZP8PSO3b4CGW2P2O110GYP5POPJp-0ROg00X9Rs#NRt#N#N,K51K5t1K5s5Q55Q5g00XX'k=j^_R^P`P5PXP8P]CSR]PbPcPcP6P4P4P<P1Ei1J5@R@%@A53c5=cR1PfPcA3co:PfPcA3cd@R@PfA3cjj9=ckRk1AjmRm9E5N93cd1Aoj=3c:5=c5=cC;C;C;PgPib5b6b7X05X85W9AH78ARA10G810F3RoAHpJJRpPE1?J>R>,1B1?GJP3D5[[[^05^85^9OP2PCP0PZPYP8PPO6b4CGW2P2O1n200100001021100011000P;PVPWPHPIPUC4PKP[PMPLP\D5X15#9P210?\PQPHPIPZC4P=fFR=?C?H10I=PKfHR=?C?MPLP=CPX15#9P2fGR=?C?HP5PKfIRK?C?MPLPKCPX15RLPDP_P`PaPbPc%@HRa93cdPfPcPePfAE5an93cd%@IRn/AR=3c:5=c9=clC;C;PgPib5b6b7X05109HPqPF11Hr1?IDP7D5\h[^05P2PKP8PTO3b4CGW:P2O110I=P5PLPJP^P`P]PbPcP1PfPcA3cn:PfPcP@PfAE5am93cd1Anj=3c:5=c9=ckC;C;C;PgPib5b6b7X05X85X9O10I8PpPE11H>1?IJP3D5\o[\A^05^85^9OP2PCP0PKP=P8PSO6b4CGW:P2O1n200100000021100011000W2W@P8P2O2n2001000000121000000CMCMCMW:W?P8P2O2n2001000010121000000W2W>P8P2O2n2011000010121000000W2W=P8P2O2n2011000010121000000W2W<P8P2O2n2011000010121000000b;W2XA5o"). Qed.
Section KindsG.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
(* [comment removed for export] *)
Definition kfactsG : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (1 <= c <= 30)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6352896 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6352896 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6352896 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfactsG.

Ltac kind := pose proof KF as KF'; unfold kfactsG, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_res & F_slot & F_sh & F_ns & F_ctx);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma KG_img : forall A k, 0x10000 <= A -> 0 <= k -> (A + k <= ADEPOT_LO \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI)) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_low : forall A k, 2147450880 <= A -> A + k <= 2148244992 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ PGE <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_ctx : 
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 208 + c * 80 \/ t + 208 + c * 80 + 4 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= AB \/ (AB + 16 <= A /\ A + k <= UB - 16) \/ UB + n <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma KG_obj : forall A k, ((6352896 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStoreG ()) ["CANSEC1"; "KindsG"] "h04__x1h14__x2h24__x3h32H6h44__p1h57__arithh64__ffh78__varmaph85__with94__p2h:4__x4h;4__x5h<4__p3h=4__p4h>4__x6h?4__x7h@4__p5hA4__p6hB5__x10hC4__x8hD4__x9hE4__p7hF5__x11hG1AhH3F_chI5F_ctxhJ4F_lohK4F_nshL5F_reshM4F_shhN6F_slothO3F_thP3KF'hQ1kp%0p%1p&0p;1p;2p;3p;4p;5p;7p;6p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7P1p8P7P3p8P7P2p8P7p1004^R1p4p710p8P7p1005;p4p710p8p1005WR7p4p73101R8p10061R9p4p73110p8P8p1006JR:p4p73110p8P8p1006fp4p710p8P8p10079R;p4p7201p8P8p1007Kp4p7201p8P8P0p4p73110p8P8p1007]R<p4p73110p8P8p10081R=p4p73110p8P8p1008Kp4p7201p8P7p4p710R8P9p4p710p8P8P:p4p710p8P8P6p8P8P5p8P8P0p4p710p8P8P<p4p710p8P8P=p4p710p8p1008^R=p4p710R8P4p8P8P6p8P8P5p8P8p10092p4p73110p8P=p4p741110R=p1009Dp4p73101R8p8p1009`p4p7210P2p8P1p4p7210P3p8P;p4p7200R;P8p8p100:Lp4p7<111111111110P2p8p100:np4p7<111111111110P2p8p100;Pp4p741110R2P7p4p7511100R8p8P8P2p8p100;ip4p741110R2P7p4p76111100R8p8P8P2p8p100<Ap4p741110R2P7p4p771111100R8p8P8P2p8p100<ap4p741110R2P7p4p7:1111111100R7p8P7P2p8P;P=p8P=P;p8g00>kj16Tg00?Pj13Tg00@Sk10GTg00AIj21Tg00B]j22Tg00@5j1MTg00cNj2^Tg00AeR;j24Tg00ckj2lTg00dGj1yTg00NPj3kTg00e?k20:Tg00B@j2vTg00F1j1xTg00e_j3STg00=mk102Tg00CTj1?Tg00D3j2rTg00G1j1~Tg00aUk10FTg00HMk10ETg00Hkk10DTg00f[j3qTg00J]k10CTg00IVj2}Tg00Lhk20BTg00MJk20ATg00Mdk20@Tg00Njk30?Tg00OIk40>Tg00g>k20=Tg00ggj3mTg00K?j2zTg00Kbk30;Tg00VUj2UTg00PUj4PTg00hPk107Tg00hnk206Tg00iOk305Tg00j8k504Tg00j\j4wTg00FQj3ZTg00D\j3[Tg00EEj2tTg00GQk203Tg00Goj4dTg00Q@j7`Tg00LEj3|Tg00J9k601Tg00b3j7aTg00RHj8bTg00Qdj7hTg00bWj4sTf0R=#3#3#3#3p=Y%3=#6p=X%6=#6p=T%6=#3p=O%3=#3#3#3#3#3#3#3p=V%3=#3#3#Mp=>%6=#6#6#6p=Gf2R2f1R7'2/1=p=K1127/4=p=7%3=#3p=i117=,U2p=Lf3R8/12117='Up=:%6=#3#3#3p=o147=,42p=D1U27/4=p=F%3=#Mp>0<f6R3g00RlR1P1f5R5f4R6CwP1P1P2P7Cw=Z8=3Zp=g1r1=p==A[17=9[129[18g00XXR4'tp=Jg00WMR<?Z7=p>002031=p=IP1P2P7P=Cdp=WP1P1P6P8P2CdP7P=Cdp=E1}1=p=@P2g00SJR0g00SiR:P:g00TIR9P1P7g00TiR>P=CPg00UPR?F`p=51z1=p=9A|17=p=8P7P0P:P:P9P=J01p=AP5P0P:P:P9P6P8P2P0P:P:P9P7P=FaGbp=pP5P0P:P:P9P6P0P:P:P9P8P2FhP7P=Gbp=C1127/U=p=nA[17=p=;A[17=/t4p=<AZ<7=9Z<29Z<89Z<6p=0P1P6P8P1P2P7P=CdCdp={P3P0P:P:P9P5P0P:P:P9P1P6P>P8CPP?F`P2P0P:P:P9P1P7P>P=CPP?F`Fap=RP1P7P>P=CPp=QP8P0P:P:P9P2P0P:P:P9P7P?F`P=Fhp=HP6P0P:P:P9P8P2P0P:P:P9P7P=FhFhp=fP8P0P:P:P9P2P7P0P:P:P9P=P?F`Fap=_P2P0P:P:P9P7P=Fhp=\P5P0P:P:P9P6P0P:P:P9P8P2FaP7P=Gbp=]P3P0P:P:P9P5P6P8P0P:P:P9P2P7P=GbGbp=N11681227/1='Up=BA[17=9[12p=jP1A|127P>P=CPp=cP6P0P:P:P9P8P0P:P:P9P1P2P>P7CPP?F`P=Fap>09P2P0P:P:P9P7P=Fap>08P8P0P:P:P9P2P7P=Gbp=uP3P5P6P8P2P7P=CsCsp=eg00V0R?#6#Y#X#T#O#V#>R>%6?R4#6S00#6S01#6#T#G#GR@#X#TRA#3#V#>RB9K7=777%3?RC#3RD#3S02#3S03#3#YRE#3#iRF#3RG#G#G#G#G#Y#V#>RH;L7p,2rcRI$0GRJ9K27g00VoRK/121268p,1tRL%MFRF,2LRMP6C:1256p,3resRN%3G#iRG#YRO#o#O#V#>RP,2NRQP5C:1235p,5nodesRR%MORS,2RRTP3C:f7RU/23p,5storeRV%>ORO,2VRWPUC:p,2KFg00l4P;p,2loRXp,2spRY/^FRZ,1X57JS0411MB11HL11FLR[PM%MGRGP>PLC:'411MJ7D[S053FS06%M?R[p,1cRMQ01$0<R\,1M37S0711QJS0897HNS0912NFp,2ABR]p,1SS0:,2]R^p,2UBR_Q03#MR`'^Ra/l]p,1nS0;,1[S0<Q0;,2_Rb/1^3D77Q37S0=%6E#i#X#T#G#G#O#T#O#V#>S0>%y]S0?%y_S0@Q0?p,3grzS0A'25k1%MCS0BQ0A'1Q0@p,3PGES0C7K[S0DQ0CQ0?p,3sszS0E'2RE'111EH3D3D37S0F11TB11HR11>RS0G11TJS0H11WB11HV11WJS0I97>VS0J3F3D3FS0Kp,3ctxRE/2GRG/1B11HE11GJ97>E3FS0L'4S0M'4S0N'4S0O'4S0P'4S0Q'4S0R20:11REPZPYPE%34RG#O#>RQ,2L%6CS0S#3S0T#>R^,vM'2Rc%MDS0U,2cRdPEQ0T#6#TRe#3Rf#3#>Rg,2LRh%6f#>S0V,2LRfPE%Oe#>S0W,2LRe%3GS0X#X#o#X#MS0Y,2LRGPEPaPbPEP]12]`RiPEQ0@Q0CPE%6?#i#X#O#Y#T#O#X#>S0Z%3?#T#O#T#o#X#Y#O#>S0[PEPRPTPEPVPW%xEFgFgFgFgFgREf:Rjf9Rk3SP=Q04Q0RP;Q06Q0Qf>Rlf=Rm5SEP=Q06Q0QP;Q07Q0PfBS0\fARn5SEP=Q07Q0PP;Q09Q0OfFfE5SEP=Q09Q0OP;Q0=Q0NfJfIS0]5SEP=Q0=Q0NP;Q0FQ0MfNfM5SEP=Q0FQ0MP;Q0KQ0LfRS0^fQS0_5SEP=Q0KQ0LfUR;fTS0`'2RoPZPYP;C:PoPcPdP;C:RdPoPhPfP;C:S0aPoPePGP;C:S0bPoPaPbP;C:S0cPoP]PiP;C:S0dPoQ0@Q0CP;C:S0ePoQ0ZQ0[P;C:S0fPoPRPTP;C:S0gPoPVPWP;C:S0hg00m1S0i'4S0j'4S0k'4S0l'4S0m'4S0n'4S0o'4S0p'4RW'4&02IRI%6A#G#Y#V#V#>%6@#G#G#Y#V#V#>,1J77JR@p-0RAg00X9Ro#?RT#?Ri#?Rb#=Ra%=iS0q%=TRT1r1oS0rCJ%x<Ro+00%~<R<%I6P2&0F1RiP7%I5RG?W8iDE&0E1Re&0D1RfPf%@DRhQ0S#@Rc55f%@4R4%9FRZ5q1Rp95fc&0C:RcPf1}1?Rq%@CS0s'8RC=5fhPcPfA5fCp1AfUEpEC20Bf9RpP=P2g00YDRrg00YdRs+0A20@=2=krsdB0?1K7H0>Rsb6b7b8X01X11X21X:1X;1W41^2F,1697861272S0t/1612281^6F;nU[[^01^11^21^:1^;1^4AP=fWRr,1YPXPJPYfVRYPrfKQ0`O8b5b3PdPWPIP@20=1^RW%?bRb#?Rd#?RJ#?RX#?Rt#?Ru#=Rv5m1Rw%=dRdQ0r';S0u'<Rx%=tRt9m1W%=bRbQ0r';'<Ry1;bTS0v,<wRw%?uRu#=S0w9m1W1;dTS0x'<RWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPx%?uS0y#?Ru#=Rz%=JRJQ0q,;aR{';S0z'<R|P|PWPWP|P|PxPxP|P|PWPWP|P|PxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxP|P|PW%?uRu#?S0{#?#=S0|%=uRu%=XRX1;JbCJR}P|P|P}P}P|P|P}PWP|P|PxPxPyPwPWPWPwPyPxPoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P<AWG6iP2%I3PUPiPUPiDEP7PiP8%IUS0}?WUiPUPiD{DEPePfPfPfPf%6DS0~#3#@RD%9SS10'8S11%9BRxPf%9HRyPDFRS12PfPf%9>Rw/QDPf1AfkPfPfPfQ0~#6#@RW%9OS13'8S14PxPfPyPWFRS15PfPf1QwW1AfjCHDfCHPcPfPfQ02#@S1695fyS17f;R|,AfPcPfPf%9[S18=5fh%9\95fhPcPfPfPfPf184ZR}PxPfPyP4FRf<R~,AfS19PcPfPfPfPCPWPfQ14PqFRS14PcPfPfPfPCPDPfQ11PqFRS11PcPfPfA5fC4S1:Pf1Q}qC_S1;PcPf1z1KQ0s55fS0sPcPfPfA5fwqS1<A5fCxRw5\fA5fyqR}PcPfPfPC%9Q,84%9^:0;1h'8RDPfQ0U#9,8DPqFRE]FNFNECECECECPpPsb6b7b8X01X11X21X:1X;1X>1X?1X4AX9AX<AX=AAK5SB11H5RD123O11H3S1=7nBf8RW97>35DU97>53F14Dj115\97[5125FS1>/1B?FDm1265S1?Pj12jOS1@P6C:1253S1APjPjPSP5DB123US1BPWPWPFP3DB11KWS1CAKWkBS1D97>W11HWS1E'U12kjS1F12|Q1v~^'2R^P^Q0UPkDB[[[[[[[[[^01^11^21^:1^;1^>1^?1^4A^9A^<A^=AP=Q05Q08Q0IQ0HPVPRPNPMPLPYPrP8f?RMfCS0IfGS0UfOS1GfPS1HQ0^fSS1IP;ODb5b3Q0aQ0pPIP@PoP<%I2%I87W7S0pPePfQ1;PcPf%9g,8495fCQ0V#9,84=5fqEpPpPsb6b7b8X01X11X21AK=72S0a122F;L=R^Q0t128gP8Q0VP7DB[^01^11^21P=PLPYPrQ0^O4Rgb5b3Q0bQ0oPIP@PoP<Q0pPePfQ1;PcPfQ0W#9,8495fCQ0Y#9,84=5fqEpPpPsb6b7b8X01X11X21Q0tQ0W,28P8Q0YP7DB\^^01^11^21Pgb5b3Q0cQ0nPIP@Q0wQ0u';S0u,<zRgPgPgPgQ0y#=R^Q0q/;TS0y,;vS0n';,<uRQQ0x,;^,<uRDPDPQPQPDPDPQPgPgPgPgPgPgPgPgPQPDPDPQPQPDPDPQPgPgPgPgPgPgPgPgQ0v9jvtS0c,;^,<uR\1;b{S0Y,<tRtPDPQPQPDPtP\PgPgPgPgPgPgPgPgP\PtPDPQPQPDPtP\PgPgPgPgPgPgPgPgPQPDPDPQPQPDPDPQPgPgPgPgQ0{#=RbPvPX1;daS0{CJRd1;X{,<bR{P{PdPbPuP^AjvXTS0WCJRaP{P{PaPaP{P{PaPdP{P{PdPdP{P{PdPaP{P{PaPaP{P{PaPdP{P{PdPgPgPgPgP\PtPDPQPQPDPtP\PgPgPgPgPgPgPgPgP\PtPDPQPQPDPtP\PgPgPgPgPgPgPgPgP\PtPDPQPQPDPtP\PgPgPgPgPgPgPgPgPQPDPDPQPQPDPDPQPgPgPgPgPgPgPgPgPQPDPDPQPQPDPDPQPgPgPgPgPgPgPgPgP\PtPDPQPQPDPtP\PgPgPgPgPdP{P{PdPaP{P{PaPaP{P{PaPdP{P{PdPdP{P{PdPaP{P{PaPaP{P{PaPdP{P{PdPgPgPgPgPQPDPDPQPQPDPDPQPgPgPgPgPoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P<%IWS1;9WG6P2%IkS0oP3PiPjPiDES0bP7PiP8%IjS0V?WUiS1JPjPiD{DEPePfPfQ12PfQ19Pf1AfmS19PfQ151AflS1KDfDfS1LPcPfPfPfQ0T#@RgQ0S#6#@RQ7cZPfPfQ0X#@S0X,8QS0S%9PS0T,8gRD'QPfPfP1%9`S1M9q14Rdg00mMS1NPQCP1AfMS1O184hR{Q0S55f5\fCHCHCHPcPfPfA5fygS1Pf@Ra,AfS1QPcPfPfPfPfQ16/8ZR\PxQ17I09S171AfnS1RPcPfQ14PcPfQ11PcPfPfA5fCgA5fDqPcPfPfPfPCQ16PfP\PqFRS16PcPfQ0sPcPfPfQ0\,AfS1S=\fwP}PcPfPfPCPdPfP{PqFRE]FNE]FNECECFNPpPsb6b7b8X01X11X21X:1X;1X>1X?1XC1XD1XB1X4AX9AX<AX=AX@AXAAXEAAKWSBQ1EAKkOB11HkR{;F~9Dj|3FS1T123FS1U12UWRd123P1^8`/lUAK86d7Dl3777U11HUS1V/4a12UFQ1V7nBS1WQ0\'4Q1?PmPmPOP6DBS0\Q1APmPmPSP5DBS1XQ1BP|P|PPP3DBPdP|P|PFPUDB11KkS1YQ0]Q1F/1BS1Z'4/U{12j|S1[1^~`P~PmPjDB[[[[[[[[[[^01^11^21^:1^;1^>1^?1^C1^D1^B1^4A^9A^<A^=A^@A^AA^EAP=11>rS1\Q05Q08Q0<Q0JQ0HQ0GPVPRQ0:P]PNPLQ0;P_PYPrP8P|PMQ0UQ1GQ1HQ0_Q0^Q1IP;OKb5b3Q0dQ0mPIP@PuPzP^Q0uCJRKPKPKPKQ0n,<bRaQ0x,<bR\P\PaPaP\P\PaPKPKPKPKPKPKPKPKPaP\P\PaPaP\P\PaPKPKPKPKPKPKPKPKQ0c,<bRDPDP\PaPaP\PDPDPKPKPKPKPKPKPKPKPDPDP\PaPaP\PDPDPKPKPKPKPKPKPKPKPaP\P\PaPaP\P\PaPKPKPKPKQ0|Q0W,;b'<RtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPKPKPKPKPDPDP\PaPaP\PDPDPKPKPKPKPKPKPKPKPDPDP\PaPaP\PDPDPKPKPKPKPKPKPKPKPDPDP\PaPaP\PDPDPKPKPKPKPKPKPKPKPaP\P\PaPaP\P\PaPKPKPKPKPKPKPKPKPaP\P\PaPaP\P\PaPKPKPKPKPKPKPKPKPDPDP\PaPaP\PDPDPKPKPKPKPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPKPKPKPKPaP\P\PaPaP\P\PaPKPKPKPKPoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P<Q1;9WijP2Q0bP7PGPjPiP8Q1J?W6iDEDEPePfQ1LPcPfPfPfQ0~#@RG?cZ4PfPf184gRgQ0T,8GRK'QPfPfP1Q1M9q1QQ1NP4CPPfPfQ18Q0X'QQ0S=5fgCHCHCHCHPcPfPfA5fyGQ1OPcPfPfPfPfQ00#@Rg/8ZRZPxPfPyPgFRQ1QPcPfQ14PcPfQ11PcPfPfA5fCGA5fKqPcPfPfA5fCgA5fZqPcPfQ0sPcPfQ1R=\fw>08f}PcPfQ1:PfQ1M=c4qC_FNE]E]FNECECFNPpPsb6b7b8X01X11X21X:1X;1X>1X?1XC1XD1XB1X4AX9AX<AX=AX@AXAAQ1TQ1>1283RZ125P1^U`/l811[W11dZ3D37778Q1=/4MQ1U/1BQ1=;FnQ0\Q1XQ1B/1jRZ12jP;L3PdPj12jFRFPUC:Q1YfHQ1Z'4/U{Q1[P~P~P`PjDB[[[[[[[[[[^01^11^21^:1^;1^>1^?1^C1^D1^B1^4A^9A^<A^=A^@A^AAP=Q1\Q05Q08Q0JQ0HQ0GPVPRQ0;P_Q0:PNPLP]PYPrP8P|PMQ0UQ1GQ1HQ0_Q0^Q1IP;OJb5b3Q0eQ0lPIP@Pu&07?-061>051zRzP^Q0yCJR?Q0wPvQ0qQ0rCJRvPvP?P?PvPvP?P?PvPvP?P?PvPvP?P?PvQ0Y,<XR]PuPzP^Q0v,;XCJRXPXP]PvP?P?PvP]PXPXP]PvP?P?PvPvP?P?PvPvP?PbPuPzAj^JTCJR^Q0z,<bRTPTP^P^PTPTP^P^PTPTP^P^PTPTP^P?PvP]PXPXP]PvP?P?PvP]PXPXP]PvP?P?PvP]PXPXP]PvP?P?PvPvP?P?PvPvP?P?PvPvP?P?PvPvP?P?PvP]PXPXP]PvP?P^PTPTP^Q0|PbPJQ0{CJRJPTPTPJPJPTPTPJP^PTPTP^P?PvPvP?P?PvPvP?PoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P<Q1;P5PiP6PiDEP2Q0VP3PiP|PiDEP7Q0o?W|iP|PiP8%I|P|PiP|Q0}DEDEDEPePfPfQ12PfQ19PfQ1KQ15Q1O5\fDfPcPfPfQ0>#9Q01#@R?55fPfPfP1P4g00n4Q03#@Rv,8?CPPfPfQ0B#9/QvPfQ1QPfQ02#6#@,8?R?95fhA5f?yDfCHCHPcPfPfQ1PQ1RPcPfPfQ17Q1SPcPfQ14PcPfQ11PcPfQ16PcPfQ0sPcPfPfQ0I,Af=\fwP}PcPfQ1:Pf1QhqC_E]FNFNECECECECPpPsb6b7b8X01X11X21X:1X;1X>1X?1XC1XD1XB1XF1X4AX9AX<AX=AX@AXAAXEAAKkSBQ1@/1B11Hj;Fm9D|~7F{Q0>Ak18dQ0B/1W12UkRd,1611dH5DM3D77UQ1V/4nQ1WQ0I'4Q1?PlPlPOP6DBQ1APlPlPSP5DBALZF3Q1CQ0]Q1D'4Q1E'UQ1FP|P~PkC:[[[[[[[[[^01^11^21^:1^;1^>1^?1^C1^D1^B1^F1^4A^9A^<A^=A^@A^AA^EAP=Q1\Q05Q08Q0DQ0JQ0HQ0GPVPRQ0EQ0AQ0?PNPLQ0CQ0@PYPrP8PUPMQ0UQ1GQ1HQ0^Q1IP;OKb5b3Q0fQ0kPIP@PoP<%I7PePfPfQ1<1Af85\fP}PcPf1Af6PfQ0[#9/QqC_E]PpPsb6b7b8X01X4AX9AA7>=7?LH=Q0[=L87[^01^4A^9AP=12rYRAQ0Z'111ABPrP;O4b5b3Q0gQ0jPIP@PoP<Q0pPePfPfQ1:PfQ10=c4qC_RAPcPACuPpPsb6b7b8X01X11X21Q0a122S;L=Q0t/18RA128S;L7[^01^11^21P=PRPYPrQ1HO4b5b3Q0hQ0iPIP@PoP<Q0pPePfPfQ1:PfQ13=c4qC_RqPcPqCuPpPsb6b7b8X01X11X21Q0a122O;L=128O=LA7[^01^11^21P=PVPYPrQ1GO4b5b3PIP@PoP<PiPePfP0P:P:P9I04PpPsb6b7b8Q0iP=b5b3FeFeFeFeFeQ0`9SE;eWIWKP7P=O2n2101000010121000000W3WMP7P=O2n2011000010121000000W3WNP7P=O2n2011000010121000000W3WLP7P=O2n2011000010121000000W3WHP7P=O2n2011000010121000000W3WOP7P=O2n2111000010121000000W3WJP7P=O2n2011000010121000000ASEkWebPUUUUUUUXQ1XG1o"). Qed.
End KindsG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aheap_pres_prim : forall (CI : list (Z * Z)) sp t c AB S UB PGE n nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfactsG sp t c AB S UB PGE n nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI ->
  munch (Wn sp t c AB UB PGE n nodes store) m m' -> wmono bsegs m m' ->
  (forall b, In b LB -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->
  PGE <= shad ATOP ->
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t c AB S UB PGE n nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  pose proof KF as KF'. destruct KF' as (F_lo & F_t & F_c & F_res & F_slot & F_sh & F_ns & F_ctx).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KG_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KG_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - destruct BLK as (b & Hb & R). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - destruct SH as (a' & Ha' & ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KG_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: clear -ST SD SDs F_sh PSP; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KG_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
    + destruct FK as (cls & FA & sz & Hin & R). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

Lemma b1'_range : forall b1, 0 <= b1 -> 0 <= Z.lor (Z.land (hdr_b1_mid b1) 243) 0 < 256.
Proof.
  intros b1 Hb. rewrite Z.lor_0_r. pose proof (hdr_b1_mid_range b1 Hb) as [R0 R1].
  assert (A0 : 0 <= Z.land (hdr_b1_mid b1) 243) by (apply Z.land_nonneg; right; lia).
  split; [exact A0|].
  destruct (Z.eq_dec (Z.land (hdr_b1_mid b1) 243) 0) as [->|NZ]; [lia|].
  change 256 with (2^8). apply lt_pow2_of_log2; [lia|].
  pose proof (Z.log2_land (hdr_b1_mid b1) 243 R0 ltac:(lia)) as L1.
  replace (Z.log2 243) with 7 in L1 by reflexivity. lia.
Qed.

Lemma b1'_at1 : forall b1, 0 <= b1 < 256 -> Z.land (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) 3 = 1.
Proof.
  intros b1 Hb.
  assert (C : forallb (fun i => Z.land (Z.lor (Z.land (hdr_b1_mid (Z.of_nat i)) 243) 0) 3 =? 1) (seq 0 256) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C (Z.to_nat b1) ltac:(apply in_seq; lia)) as C1. cbn beta in C1.
  rewrite Z2Nat.id in C1 by lia. apply Z.eqb_eq. exact C1.
Qed.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_prim_stmt (DI : ADepotIface) (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop)
    (CI : list (Z * Z)) : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (n lo c cnt k b1 : Z) (maxc csz : word) (uj : list byte),
  let S := size_of_class c in let AB := aslot_addr L c k in let UB := AB + rz_size n in let PG := shad UB + shlen (n - n mod 8) in
  alayout_ok L -> arng L RNG st -> AREP (AH DI AQ ASEC AFK) L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None -> 0 <= k < ndist st c ->
  maxc = Z_to_bv 64 (max_count st c) -> csz = Z_to_bv 64 S -> 0 <= b1 < 256 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  (16 < rz_size n -> junk_at m (AB + 16) (rz_size n - 32)) ->
  junk_at m (UB + n) (S - rz_size n - n) ->
  fill_at m (shad AB + 1) (shlen (rz_size n) - 1) 0xfa ->
  fill_at m (PG + (if n mod 8 =? 0 then 0 else 1)) (shlen S - shlen (rz_size n) - shlen (n - n mod 8) - (if n mod 8 =? 0 then 0 else 1)) 0xfa ->
  junk_at m (al_t L + 2768) 16 -> junk_at m (al_t L + 2792) 8 ->
  forall ms',
    malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG (if n mod 8 =? 0 then 0 else 1) lo b1 maxc csz uj m ms' ->
    amalloc_post CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m
      (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
         (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)), Some (a_next st)) RNG ms'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Theorem store_prim : store_prim_stmt DI AQ ASEC AFK CI.
Proof.
  unfold store_prim_stmt. intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X n lo c cnt k b1 maxc csz uj. cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM HC0 HCNT POS NK NB KR HMX HCSZ B1 CEIL LO LHJ TL SHpre SHsuf CSa CSc ms' PM.
  clear SHpre SHsuf. unfold AMALLOC_STACK in LO.
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC0) as (C16 & NSZ & SZM16 & SMALL & MCB).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5). clear CL5.
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10). clear DL9 DL10.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT TBND] & [jT TIMG]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (_ & _ & [kC CBND]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (_ & _ & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (_ & _ & [kS SBND]). unfold AIMG_HI in DL3, DL6, CL3.
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t.
  word_range sp SPR.
  assert (CIN : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite HCNT in CNTB. clear -CNTB POS. lia. }
  assert (MC16 : max_cached c <= 16) by (clear -MCB; lia).
  assert (CNT16 : 0 < cnt <= 16) by (unfold max_count in CNTB; rewrite CIN, HCNT in CNTB; clear -CNTB POS MC16; lia).
  pose proof (cls_facts c C16) as (SZB & SZM & _ & _).
  set (S := size_of_class c) in *.
  pose proof (slot_in_region L st c k ltac:(clear -SZB; subst S; lia) (proj1 A1) KR) as (G5 & G4 & KS0). fold S in G5, G4, KS0.
  set (AB := aslot_addr L c k) in *.
  assert (G1 : al_space_beg L <= AB) by (unfold aregion, K_REGION in G5; clear -G5 C16; lia).
  assert (G2 : AB + S <= al_space_beg L + K_SPACE_SIZE).
  { unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. generalize G4 A1 A2 C16; clear; intros. change (2^37) with 137438953472. lia. }
  assert (G3 : AB mod 16 = 0) by (subst AB; apply slot_aligned; [exact SAL| exact HCK]).
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  set (grz := shlen (rz_size n)) in *. set (g := shlen (n - n mod 8)) in *. set (room := if n mod 8 =? 0 then 0 else 1) in *.
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8) by (subst grz g; rewrite !shlen_div; split; reflexivity).
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  assert (RMQ : room = (if n mod 8 =? 0 then 0 else 1)) by reflexivity. clearbody room.
  assert (GR5 : 0 <= room <= 1) by (rewrite RMQ; clear; destruct (n mod 8 =? 0); lia).
  assert (SS8 : shlen S = S / 8) by (rewrite shlen_div; reflexivity).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2, SS8, RMQ. generalize NSZ NS RSR RSM SZM RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. rewrite !shad_div. generalize G3 RZM RZR. clear. intros. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000 /\ shad AB + shlen S = shad (AB + S)).
  { rewrite SS8, !shad_div. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 G3 SP1 SP2 SZB SZM ES. clear. intros. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  destruct GR89 as (GR8 & GR9 & GR10).
  set (PG := shad UB + g) in *.
  assert (PGE_ : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (ROOM : granules n = g + room) by (subst g; rewrite RMQ; apply granules_eq; clear -N; lia).
  assert (GR11 : 1 <= g + room).
  { subst g. rewrite RMQ, shlen_div. generalize N; clear; intros. destruct (Z.eqb_spec (n mod 8) 0); first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  assert (BB : forall b, In b (x_busy X) ->
      al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104
      /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ UB + n <= xb_alloc L b)
      /\ xb_alloc L b mod 16 = 0 /\ 16 <= size_of_class (xb_class b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. split; [| split; [| split; [| split; [apply slot_aligned; [exact SAL| exact CLB] | clear -QS; lia]]]].
    - unfold aregion, K_REGION in P5. clear -P5 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - unfold aregion, K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    -
      destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
      + rewrite EC in *. assert (NKb : xb_slot b <> k).
        { intros EK. enough (busy_of X c k <> None) by congruence. unfold busy_of.
          destruct (List.find _ _) eqn:FE; [discriminate|]. exfalso.
          apply (find_none _ _ FE) in Hb. rewrite EC, EK, !Z.eqb_refl in Hb. discriminate. }
        destruct (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -KR; lia) NKb ltac:(clear -SZB; lia)) as [D|D];
          rewrite <- EAB in D; fold S in D; [left; exact D| right].
        clear -D EUB RZR N NSZ NS RSR ES. subst S. lia.
      + assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
        unfold K_REGION, K_FREEARR_OFF in *.
        destruct (proj1 (Z.lt_gt_cases (xb_class b) c) NC) as [LT|GT]; [left | right].
        * specialize (RC _ _ LT). clear -RC P4 Q1 Q2 G5. lia.
        * specialize (RC _ _ GT). clear -RC P5 G4 A1 A2 EUB N NSZ NS RSR RZR ES. subst S. lia. }
  destruct PM as (id & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & stj'
                  & -> & MU & WM & MI' & ST' & IDR & CR' & STS' & STATS' & LSJ' & UW' & HDR' & UF' & LH' & SHU' & SHP' & DEP').
  assert (MUn : munch (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. subst PG. generalize GR3 GR4 GR5 GR7. clear. intros. lia. }
  clear MU.
  assert (KF : kfactsG (bv_unsigned sp) (al_t L) c AB S UB (PG + room) n (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo grz (shlen S)).
  { unfold kfactsG. subst PG. unfold AMALLOC_STACK, K_SPACE_SIZE in *. change (2^37) with 137438953472 in G2.
    generalize CEIL LO TL1 TL2 TL4 C16 RES RHI RSP G1 G2 EUB RZR N NSZ NS RSR ES GR8 GR7 GR3 GR4 GR5 GR6 GR9 GR11 DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.
    repeat split; first [lia | assumption | match goal with |- ?G => idtac "KF-LEFT" G end]. }
  pose proof (KG_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KG_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KG_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KG_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KG_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_c_t) (unbx D_c_res) (unbx D_c_n) (unbx D_c_s)) as Kctx.
  pose proof (KG_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx DL7) (unbx DL8)) as Kt.
  pose proof (KG_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx D_n_res) (unbx D_s_res)) as Kres.
  pose proof (KG_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  change (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st)) (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)))
    with (st_fast st c n cnt).
  set (b1' := Z.lor (Z.land (hdr_b1_mid b1) 243) 0) in *.
  pose proof (b1'_range b1 ltac:(clear -B1; lia)) as B1R. fold b1' in B1R.
  set (X' := xfast X c k n (a_next st) b1' id).
  pose proof (st_fast_fields st c n cnt) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (WF' : awf L (st_fast st c n cnt) X').
  { apply awf_fast; [exact WF | exact HCK | exact HCNT | exact POS | exact NK | exact NB | clear -N NS NSR RSR RZR; unfold AREQMAX; lia | | exact B1R | apply b1'_at1; clear -B1; lia | clear -IDR; lia].
    fold S. clear -NS NSZ. lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L (st_fast st c n cnt) m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact E3 | exact E4 | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (THR' : athread L (st_fast st c n cnt) X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      + destruct (CACHES c HCK) as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        pose proof (st_fast_counters st c n cnt c) as (_ & _ & _ & _ & EC5). rewrite Z.eqb_refl in EC5.
        rewrite EC5, st_fast_max_count, E5, CIN. unfold X'. rewrite xfast_cls, Z.eqb_refl. cbn [xc_cache].
        exists (Z_to_bv 64 (acompact c k) :: tail).
        assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
        { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC HCNT. lia. }
        split; [| split].
        * unfold acache_addr. rewrite HMX, HCSZ in CR'. fold S. exact CR'.
        * eapply u32arr_frame; [| exact MUn | exact WM |].
          -- rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
          -- rewrite length_app, length_map. cbn [length]. unfold acache_addr.
             assert (LRL : (length (removelast (xc_cache (x_cls X c))) + Datatypes.S (length tail) = 16)%nat).
             { rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia. }
             rewrite LRL. apply Kt; clear -C16; lia.
        * cbn [length]. rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | | exact E5 | |].
        * pose proof (st_fast_counters st c n cnt c') as (_ & _ & _ & _ & EC5). rewrite EC5. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold acache_addr. unfold K_NUM_CLASSES in Hc'. apply Kt; clear -C16 Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact CSa | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [exact CSc | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (UBN : AB + 16 <= UB /\ UB + n <= AB + S) by (clear -EUB RZR N NSZ NS RSR; lia).
  assert (PGB : PG + room <= shad (AB + S)) by (subst PG; rewrite GR7, <- GR10; clear -GR6; lia).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L (st_fast st c n cnt) m' c'' /\ afreearray L (st_fast st c n cnt) X' m' c''
      /\ aslots L (st_fast st c n cnt) X' m' c'' /\ aslot_shadow L (st_fast st c n cnt) X' m' c'').
  { intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (st_fast_counters st c n cnt c'') as (EC1 & EC2 & EC3 & EC4 & EC5).
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC3 | exact EC4 | exact EC2 | exact EC1 |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; clear -Hc'' RSP G2 EUB NSZ NS RSR RZR N; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC3 | exact EC4 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c'' c) as [->|_]; reflexivity.
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *.
        * clear -RI1. lia.
        * clear -RI2 RI3 Q6. lia.
        * clear -Q5 Q6; lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right; right. clear -G4 A1 A2 UBN. lia.
          -- destruct (SIDE NE) as [D|D]; [left; clear -D Q6; lia | right; right; clear -D UBN; lia].
      + apply Kshad.
        * rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF in *. clear -RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -RI2 RI3 Q6 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2. lia.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM''; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
                unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q6 UBN. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D. lia.
    -
      eapply (aslots_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SLOTS | apply st_fast_ndist | exact EC2 | exact EC1 | | |].
      + intros k'' Hk'' NEk. pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as (P5 & P4 & P0).
        split; [| split].
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kres; [clear -P5 RI1; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -QS; lia |].
          destruct (Z.eqb_spec c'' c) as [->|NE].
          -- destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D;
               [left; exact D | right; right; clear -D EUB RZR N NSZ NS RSR ES; subst S; lia].
          -- destruct (SIDE NE) as [D|D]; [left; clear -D P4 Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D P5 UBN; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|].
          exact (awf_fits L st X b WF IB).
      + intros POS''. apply Kres; [clear -Q1 RI1; unfold aregion in *; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -POS''; lia |].
        destruct (Z.eqb_spec c'' c) as [->|NE]; [right; right; clear -G4 UBN; lia|].
        destruct (SIDE NE) as [D|D]; [left; clear -D Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D Q1 UBN; lia].
      +
        destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb].
        unfold aslot_busy, bnew. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot xb_alloc xb_user xb_hdr].
        unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n]. rewrite <- EAB. fold S. rewrite <- EUB.
        split; [| split].
        * intros R16. split.
          -- replace (UB - 16) with (UB + -16) by (clear; lia). unfold AMAGIC. exact (LH' R16).
          -- eapply junk_frame; [exact (LHJ R16) | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; clear -Hp R16 RZR G1 RSP G2 EUB RI3 N NSZ NS RSR; lia.
        * exists 2. split; [reflexivity|]. replace (UB - 16) with (UB + -16) by (clear; lia). exact HDR'.
        * replace (S - rz_size n) with (n + (S - rz_size n - n)) by (clear; lia).
          apply (junk_merge m' UB n (S - rz_size n - n)); [| | clear -N; lia | clear -NSZ NS RSR N; lia].
          -- pose proof (junk_of_cells m' _ _ UF') as J. cbn [cells_size csize] in J. rewrite Nat.add_0_r, Z2Nat.id in J by (clear -N; lia). exact J.
          -- eapply junk_frame; [exact TL | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; [| | clear -Hp; lia | right; right; clear; lia].
             ++ clear -G1 RSP EUB RZR N. lia.
             ++ clear -G2 RI3 EUB NSZ NS RSR N RZR. lia.
    -
      eapply (aslot_shadow_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SHADOW | apply st_fast_ndist | exact EC2 | exact EC1 | | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk'' NEk. pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as (P5 & P4 & P0).
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        split.
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P5 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
          -- rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -P4 Q1 Q2 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
          -- apply shlen_nonneg. clear -QS; lia.
          -- destruct (Z.eqb_spec c'' c) as [->|NE].
             ++ destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D.
                ** left. apply shad_sep; [clear -D UBN; lia| clear -AL''; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact D.
             ++ destruct (SIDE NE) as [D|D].
                ** left. apply shad_sep; [| clear -AL''; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]]. unfold K_FREEARR_OFF, K_REGION in *. clear -D P4 Q1 Q2 UBN. lia.
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D P5. lia.
      + intros POS''. apply Kshad.
        * rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * clear -POS''; lia.
        * destruct (Z.eqb_spec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact G4.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep.
                ** unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
                ** pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM. clear -AM RM''. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb]. rewrite <- EAB. fold S.
        unfold slot_shadow_bytes, bnew. cbn [xb_n xb_st]. unfold block_shadow_bytes.
        change (shlen (rz_size n)) with grz. rewrite <- (shlen_floor n). change (shlen (n - n mod 8)) with g. rewrite ROOM.
        destruct SHADOW as [SHK _]. specialize (SHK k KR). rewrite NB in SHK. rewrite <- EAB in SHK. fold S in SHK. cbn [slot_shadow_bytes] in SHK.
        change (rw_cells bsegs m (shad AB) [CB (Z.to_nat (shlen S)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S)))]) with (fill_at m (shad AB) (shlen S) 250) in SHK.
        destruct (fill_split m (shad AB) grz (shlen S - grz) 250 ltac:(replace (grz + (shlen S - grz)) with (shlen S) by (clear; lia); exact SHK)
                    ltac:(clear -GR3; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [F1 R1].
        destruct (fill_split m (shad AB + grz) (g + room) (shlen S - grz - (g + room)) 250
                    ltac:(replace (g + room + (shlen S - grz - (g + room))) with (shlen S - grz) by (clear; lia); exact R1)
                    ltac:(clear -GR4 GR5; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [_ F2].
        eapply fill_frame in F1; [| exact MUn | exact WM | intros _; apply Kshad; [clear -GR8; lia | clear -GR9 GR6 GR4 GR5 GR3; lia | clear -GR3; lia | left; clear -GR7; lia]].
        replace (shad AB + grz + (g + room)) with (PG + room) in F2 by (subst PG; clear -GR7; lia).
        eapply fill_frame in F2; [| exact MUn | exact WM | intros Hp; apply Kshad; [subst PG; clear -GR8 GR7 GR3 GR4 GR5; lia | clear -GR9 GR6 GR7 GR3 GR4 GR5 Hp; subst PG; lia | clear -Hp; lia | right; clear; lia]].
        unfold fill_at in F1, F2. change (shlen (n - n mod 8)) with g in SHU'.
        replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat grz)) in SHU' by (clear -GR7 GR3; lia).
        destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
        * assert (R0 : room = 0) by (rewrite RMQ; reflexivity). clearbody PG. subst room. rewrite app_nil_r.
          replace (PG + 0) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' F2)) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + Z.to_nat (shlen S - grz - (g + 0))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          exact FIN.
        * assert (RM1 : room = 1) by (rewrite RMQ; reflexivity). clearbody PG. subst room. specialize (SHP' M0). apply cb_of_C1 in SHP'.
          replace PG with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in SHP' by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          replace (PG + 1) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g) + Z.of_nat 1) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' (cb_app m' _ _ _ _ _ SHP' F2))) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + (1 + Z.to_nat (shlen S - grz - (g + 1)))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          rewrite <- app_assoc. cbn [app] in FIN. exact FIN. }
  assert (HQ' : AQ L (st_fast st c n cnt) X' m').
  { eapply (hq_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HQ | exact MUn | exact WM | |].
    - unfold quar_untouched. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      do 10 (apply Forall_cons; [cbn [fst snd];
        split; [clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N UBN GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 D_t_res DL7 DL8 TBND TIMG NBND DL3 SBND DL6 RHI; unbox D_t_res; unbox DL7; unbox DL8; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5); destruct (xb_st b); [exact I| |];
        clear -Bb1 Bb2 Bb3 CEIL LO RES C16 EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 G2 DL1 DL2 DL4 DL5 D_t_res D_n_res D_s_res UBN NBND DL3 SBND DL6 RHI;
        unbox D_t_res; unbox D_n_res; unbox D_s_res; lia |]).
      apply Forall_nil.
    - unfold quar_same. rewrite E1, E8, E9, E10, E11. repeat (split; [reflexivity|]). split.
      + intros b Hb. destruct (xb_st b); [exact I| right; exact Hb | right; exact Hb].
      + intros b [<-|Hb]; [exact I|]. destruct (xb_st b); [exact I| exact Hb | exact Hb]. }
  assert (HS' : ASEC L (st_fast st c n cnt) X' m').
  { eapply (hs_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad AB).
      { rewrite !shad_div. unfold aregion, K_REGION in G5. change (2^32) with 4294967296 in G5. clear -G5 C16. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
      assert (SHB2 : shad (AB + S) <= shad (al_space_beg L) + 17179869184).
      { rewrite !shad_div. clear -G2. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL2 C16 TBND TIMG; lia |]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G1 G2 UBN N RSP; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha GR7 GR3 PGB SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; unfold AIMG_HI; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - unfold sec_same. rewrite E2, E3, E4, E6. repeat (split; [reflexivity|]).
      assert (NONE : (a_live st) !! (a_next st) = None).
      { destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as FF. clear -FF. lia. }
      split.
      + intros p mb ms n'. destruct (N.eq_dec p (a_next st)) as [->|NE].
        * rewrite lookup_insert_eq. split; [intros HH; discriminate| intros HH]. exfalso. rewrite NONE in HH. discriminate.
        * rewrite lookup_insert_ne by congruence. tauto.
      + eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [exact NONE| exact E6| exact E8| exact E10]. }
  assert (AR' : AREP (AH DI AQ ASEC AFK) L (st_fast st c n cnt) X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|].
    split; [eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUn | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
    split; [| eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
    intros c'' Hc''. pose proof (st_fast_counters st c n cnt c'') as (EC1 & EC2 & EC3 & EC4 & EC5).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof (aregion_mod L c'' SAL) as RM''. unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    eapply (ashadow_avail_frame L _ m m' MUn WM st); [exact (AVL c'' ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) | exact EC1 | exact EC4 | |].
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_FREEARR_OFF in *. clear -G4 A1. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| clear -RM'' Q4; unfold K_USER_MAP in *; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]]. unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, aregion in *. clear -Q5 Q6 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2 Q5 Q6. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM'' Q7; unfold K_FREEARR_MAP in *; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
             unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q5 Q6 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D Q1 Q5 Q6. lia. }
  pose proof (ablocks_fast L st X LB c k n cnt b1' id WF BL) as BL'. rewrite <- EAB, <- EUB in BL'. fold X' in BL'.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & _ & [kF FKs]). unfold aobj in FKO.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HBK : forall b, In b LB -> disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (ab_addr b) (ab_size b)).
  { intros [[p|cls] A n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL p A n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EUA & Gs)].
      + destruct (BB b Hb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5).
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
        apply Kres; clear -Bb1 Bb2 Bb3 FIT; lia.
      +
        cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
        destruct (ablk_int _ _ Gs2) as [kB GB].
        apply Kobj; clear -GB Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - destruct (FKD cls A n' Hin) as (K1 & K2 & K3). atop_facts.
      apply Kobj; [clear -K1 K3 FKO FKi FKs; lia | clear -K3 FKO FKi FKs; lia | exact K2 | clear -K1 K3 D_t_f; unbox D_t_f; lia
                  | clear -K1 K3 D_f_res; unbox D_f_res; lia | clear -K1 K3 D_n_f; unbox D_n_f; lia | clear -K1 K3 D_s_f; unbox D_s_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO Ha' FKi FKs; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO Ha' FKi FKs; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ] | clear; lia |].
    pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
    - left. rewrite GR7, (shad_div a'), (shad_div AB). clear -D Ha' K3 RSP G1 GR3. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
    - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G2. lia. }
  assert (HFK' : AFK L (HB (a_next st) UB n :: LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO. pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD DTs] & [jD DTi]).
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ PG + room <= shad (al_fake L))
                    /\ 2148244992 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; clear -FKO FKi FKs; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
        pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
        - left. rewrite GR7, shlen_div, (shad_div (al_fake L)), (shad_div AB). clear -D RSP G1 GR3. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D RSP G2. lia. }
      destruct SHF as (SHF1 & SHF2 & SHF3).
      do 10 (apply Forall_cons; [cbn [fst snd];
        clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 FKO DTO D1 D2 D3 D4 D_t_f D_f_res D_n_f D_s_f SHF1 SHF2 SHF3 UBN TBND TIMG NBND DL3 SBND DL6 RHI FKi FKs DTs DTi;
        first [ lazymatch goal with
                | |- context [al_t _] => unbox D_t_f; clear D_f_res D_n_f D_s_f
                | |- context [al_nodes _] => unbox D_n_f; clear D_t_f D_f_res D_s_f
                | |- context [al_store _] => unbox D_s_f; clear D_t_f D_f_res D_n_f
                | |- _ => unbox D_f_res; clear D_t_f D_n_f D_s_f
                end; unfold AIMG_HI in *; repeat (split; [lia|]); lia
              | unbox D_t_f; unbox D_f_res; unbox D_n_f; unbox D_s_f; unfold AIMG_HI in *; repeat (split; [lia|]); lia ] |]).
      apply Forall_nil.
    - intros cls FA sz. cbn. split; [intros [E|Hin]; [discriminate| exact Hin] | intros Hin; right; exact Hin]. }
  assert (PSP : PG + room <= shad ATOP).
  { eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -G2 SP2. lia. }
  split; [apply fp_le_refl|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_prim CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP]. }
  cbn [fst snd]. exists UB, (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj).
  split; [reflexivity|]. split.
  { unfold ablock_range. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    split; [unfold ablk; right; clear -G1 SP1 EUB RZR UBN G2 SP2 N; lia|]. split; [clear -N; lia|]. split; [clear -UBN G2 SP2; lia|].
    rewrite EUB. clear -G3 RZM RZR. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  split.
  { split; [exact ALO|]. split; [eapply arng_fast; [exact WF| exact ARNG]|]. split; [| exact HFK']. exists X'. split; [exact AR' | exact BL']. }
  split; [exact UF'|].
  destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _). destruct (RCLS c HCK) as (RREG & RSREG & _ & _).
  lazymatch type of RSREG with rng ?R (?X - 4096) (?M + 8192) =>
    pose proof (rng_sub' R (X - 4096) (M + 8192) X M RSREG ltac:(clear; lia)) as RSREG_; clear RSREG; rename RSREG_ into RSREG end.
  split; [| split].
  - eapply rng_sub'; [exact RREG|]. clear -G5 G4 A1 UBN. lia.
  - eapply rng_sub'; [exact RSREG|]. pose proof (aregion_mod L c SAL) as RM.
    split; [apply shad_mono; clear -G5 UBN; lia|].
    rewrite <- (shad_add_shlen (aregion L c) (c_mapped_user (get_cls st c))) by (clear -RM; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
    rewrite (shad_div UB), shlen_div, (shad_div (aregion L c + c_mapped_user (get_cls st c))).
    pose proof (size_of_class_facts c HCK) as [_ S16]. fold S in S16.
    clear -UBN G4 A1 G3 S16. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
  - intros NP. exfalso. rewrite PRIM in NP. discriminate.
Qed.

End S.

End CANSEC1.

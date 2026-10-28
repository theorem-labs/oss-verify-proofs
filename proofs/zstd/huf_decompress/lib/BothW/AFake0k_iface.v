(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFake0k_iface () := "C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init5Logic8eq_transI47Corelib4Init9Datatypes4list00K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C47Corelib4Init5Logic3notI46Stdlib5Lists4List5NoDup00I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indc5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface9fake0_lekC46Stdlib9micromega;ZifyClasses5mkrelI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic2ex01c5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface>fake0_lek_inclI47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6in_decI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List8in_splitC46Stdlib5Lists4List>NoDup_remove_1C46Stdlib5Lists4List>NoDup_remove_2C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith6BinInt1Z6eq_decC46Stdlib5Lists4List8nil_consI47Corelib4Init5Logic3and00c5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface>fake0_lek_nonec5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface?fake0_lek_push0C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula05C46Stdlib5Lists4List;ForallPairsC46Stdlib5Lists4List9seq_NoDupC46Stdlib5Lists4ListKNoDup_map_NoDup_ForallPairsC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_seqK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List2hdc5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_ifaceDstack_malloc_0k_stmtK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngc5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface>fake0_lek_monoI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsc5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface:SM0K_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATP".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fake0_lek (k : nat) (LB : list ablock) : Prop :=
  forall l : list Z, List.NoDup l -> (forall F, In F l -> exists n, In (mkABlock (ABFake 0) F n) LB) -> (length l <= k)%nat.

Lemma fake0_lek_none : forall LB, (forall F n, ~ In (mkABlock (ABFake 0) F n) LB) -> fake0_lek 0 LB.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "p'0h01nh11Fh22HLh32NDh41Hh52Hnh62LBh77__arithh84__ffh98__varmaph:5__with;1eh<1li001lh=2l0i011xi021zp;1p;3p;2p;4p;7p;<p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2p1001>p4p710p8g001\R2j18Tg002<j1NTg0035j32Tg003nj1MTg004Gj25TP0j31Tg004cR0j23Tg005=j26Tg005]R1j24Tg0067j19Tg006WR3j2<Tg0073j27Tg007Mj1KTg007kj1HTg008Ij1FTg0094j2ETg009Wj4DTg00:Bj7CTg00:fj2BTg00;Hj2ATg00<4j3:Tg00<Nj3@Tg00<mj4?Tg00=_j4>Tg00>Jj3;Tg00>jj3GTg00?Dj2=Tg00?cj2ITg00@el<JTg00AJR4f1R5f0R631p=0g00BCg00BbR7P1g00C@P3g00C`g00DBR3g00DaR1P5P3P1P6M<Jp=L%84%N1R4?256f2R8'0#M^07^17%87R9P2P71576A1768A2486R2f7R:'0X07,37[^171678/43[[P6%97R;,57A176;f6,02X07,37[^1714331<11R<1771R=/L=g00E?R=#9%8=%K7%H7%F7R=g00Ekg00FJR>P>g00FjR>P71E71R?g00GJP?CDg00H1FC1B=>P6P8g00HQR>g00I1R='71A68=:>=dA@715C?b8b9b:P<P6b7C>167;/43eW2W3A;756,57f3R;=;78R<9176f:R1,02X07,37[^17167</43P6P;A:7;;A17;8177;3GO2f4=246f9'0X07,37P0P7f5=246/01X07g00IQP6A24:6f<R:'0P:f8P5P6O3W5X07P5P6O2n2001000000120101000b;'=W2W3X<9X17P5P6O2n10110000020020102100W=1I35eW4W6o"). Qed.

Lemma fake0_lek_mono : forall k k' LB, (k <= k')%nat -> fake0_lek k LB -> fake0_lek k' LB.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "h01Hh14__x1h24__x2h34__x3h41Fh52H0h62HLh72Hkh83Hk0h92LBh:2NDh;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA5cstr1hB1khC2k'hD1lhE1np;1p;2p;3p;4p;<p;7p;8p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2p1001>p4p710p8g001\j18Tg005]R2j22Tg00?cj2<Tg004Gj2FTP0j3ATg002<j1WTg0035j3UTg004cj2MTg005=j24Tg00C@R0j10Tg006WR1j21Tg0073j23Tg00Inj4BTg00JUj1:Tg00K:j1?Tg00KYj29Tg00LBj3>Tg00Lkj2VTg0067j1TTg00>Jj3QTg00MWj2=Tg00N5j4LTg007kj1KTg008Ij1JTg00NSj1ITg00O8j26Tg00O[j1HTg00P@j1GTg00:fj2ETg00;Hj2NTg00<4j3DTg00<Nj3OTg00<mj4PTg00=_j4CTg00@el<RTg009Wj4STg00:Bj7YTg00Pbj8XTg00BCR3g00BbR4P2P0P1g00C`f5R1f4R0f3R2f2R5f1R6f0R7M<Rp=;P4P6g00GJP7CSp=7P6g00EkR8g00FJR9P9g00FjR:P7g00H1FYp=5P2P8P9P9P:P5P6P7GXp=@g00AJR8#812561<26%841F47AA475g00DaR;#W?U57f7R<5A8XE4,M4[^44P2P5P6P7O31445/2<1442R8/2<%08R=%0<R>'1P8P=134=R?P<P>134>E;f8R>,28%0>R<,1=R@P8P=P?P>P<134<R?E;P7CBP@f9R@/2>%0@R=/1<R8P@P=134=P>P<P?E;f6R?CBP8f:R8#:%08,1;144?R?#:%0?,1;f;R?#:%0?,1;g00E?R?g00DBR8#?R<#?,94194<19485>45>4g00QF'V%T?3Q%8?P41=45P61=42CL%K4%J4R?g00R2R8#I,64R<%H8,64R>'7,5?%G9R9P?1648R8/7<,5?P9178>,5?C@C@1E?:P7P5g00HQR?g00I1R:'31N75=D?:dAO4;6CPb<b=b>X14X24X34115611621152[[^14^24^34P7f>#0f=#0144@#0P0P1O5b;bAb@b?b8b5CCb0W6W:WD1<25eW0W7W9XC3XB3o"). Qed.

Lemma fake0_lek_incl : forall k LB LB',
  (forall F n, In (mkABlock (ABFake 0) F n) LB' -> In (mkABlock (ABFake 0) F n) LB) -> fake0_lek k LB -> fake0_lek k LB'.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "p'0h01nh11Fh21Hh32HFh42HLh52Hnh61Ih72LBh83LB'h92NDh:1eh;1kh<1li001xp;1p;3p;2p;4p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2p1001>p4p710p8g001\j14Tg002<j18Tg0035j31Tg00?cj25Tg004Gj27TP0j33Tg004cR0j22Tg00RWj46Tg00AJR2f1R1f0R333p=0g00BC%42R2g00BbR4g00Da#8R5?113f2R6'0A1561f4R7'0[^04]1f3R8/56%441743A3436A1563R9f7R:'0X04,24[^14P8P6P1A3438P6P1P3O2f8,09X04,24P0P4A1583f9'0X04A1573f;R8'0X04,24P3f5=153/08P4A15:3f>'0X04P1P8f6P1P3O3C6W5X04P1P3O2n2001000000120100000b:W3X14O3W4W9W<1576eW2W6X82W7W;o"). Qed.

(* [comment removed for export] *)
Lemma fake0_lek_push : forall k b LB, (forall F n, b <> mkABlock (ABFake 0) F n) -> fake0_lek k LB -> fake0_lek k (b :: LB).
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "h01Fh11nh21Eh31Hh42H0h53Hinh62LBh72NBh81bh91kp;1p;3p;2p;5p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2p1001>p4p710p8g001\j19Tg002<j18Tg0035j31Tg00<4j32Tg003nj17Tg00?cj25Tg00>Jj33TP0j30Tg00?Dj24Tg00S1j56Tg00BCg00AJR0%90g00BbR2f3R1g00Da#8R3f1R4f0R531R6520#7^12]01514f4R7f2R8A3018f5R9=3079006g00T8f6R6A1384R4520A0049A1318R8=006R4P5f7R9=208A1371=009P6P7P1P5O3'4W2P5O1P5X54P5O1n200100000021000010000W4X12X02P5D6W3W7W6W8W9o"). Qed.

(* [comment removed for export] *)
Lemma fake0_lek_push0 : forall k F n LB, fake0_lek k LB -> fake0_lek (S k) (mkABlock (ABFake 0) F n :: LB).
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "p'0h01ni001nh12H0h22l'h31lh41xi011xh51Fh62l2h71Ah82Hxh94__x1h:4__x2h;1ai021ah<1eh=2HLh>2INh?2NDh@4RESThA2l1hB1EhC3LENhD3ND'hE2NIhF7__arithhG4__ffhH8__varmaphI5__withJ4__x3hK4cstrhL5cstr0hM1HhN2H1hO3HinhP2LBhQ4LEN0hR3NI'hS3SUBhT2_HhU5cstr1hV1khW2n'hX1si031si047ab_addri057ab_kindi067ab_sizei071ip;1p;2p;3p;6p;4p;5p;:p;<p;Bp;7p;8p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2g00TRR2p4p710p8g001\j1CTg00?cj2ZTg004Gj2MTg002<j1|Tg0035j31Tg003nj1?Tg00<4j39TP2j6RTg00Toj6[l:gTg00?Dj2{Tg00RWj4zTg005]R2j23Tg00UMj4qTg00UhR1j2oTg00K:R3j1:Tg00VHj4hTg004cR4j2GTg00Vej5bTg00WHj5aTg00Wkj3ETP0j36Tg00T8R0j2;Tg00XHj4`Tg00>jj3_Tg00Xgj3STg00YAj6^Tg00Y]j2DTg00Z4j3QTg00ZSj6]Tg00C@R5j14Tg00Zoj1\Tg00[MR6j28Tg006WR7j25Tg0073j2ATg00Inj4XTg00JUj1BTg0067j1yTg00MWj2WTg00N5j4VTg007kj1vTg008Ij1uTg00O8j2NTg00O[j1tTg00[jj3JTg00NSj1pTg00P@j1nTg0094j2mTg00:fj2iTg00;Hj2jTg00<Nj3kTg00<mj4lTg00=_j4TTg007Mj1fTg00>Jj3LTg005=j2eTg00\Ml<rTg00]2lBsTg00@el<dTg009Wj4wTg00:Bj7xTg00Pbj8cTg00BbR8f1R9f0R:36p=0g00AJR;?L9:p==A6;9:p=71G8:p=>A989:p=@1e8:p=2f2R<AL89:5E8p=<AL89:p=PAE89:p=Fg00BCR=P=P8P8P3P5P5f3R3g00]XP<P9P:M<rp=OP=P=P=P8P8P8g00^<P5P5P5P6g00^\f5R6f4R>P3P<P9P:MBsp=YP=P8P2P5P7g00C`P6P>P3P<P9P:M<dp=HP8P9g00GJP:Cwp=KP9g00EkR7g00FJR5P5g00FjR2P:g00H1Fxp=IP3P7P5P5P2P<P9P:Gcp=U%C;1Z3:%C8R71M8:R?10:<R@g00DaRA#|RB?1<:RCf8RDf7RE51Bf6RF'='7X08#>[^5810D9#?RG10:3RH109E[^48RIPEP3P<10:>PFP9P<P9P:O2O2f=RJf<RK51Bf;RL'=,7CX08#>P4P8A1B3:f>RM=1BJ/=K'7X08A1B>:/7JX08#>P:A1B6:f@RNf?RO51B/=M'7P0fAR0=1BNA1BF9RP59;17POA1BD:/70X08#>P:fBRP=1B0A1BE<RQ59;f9RR=1B:/7PX08RS#>P;P8P;P8P:P:n01102000130105104106X<;fCRT=1BPA1BD3P:ER1@P3P;P8P;P8P:P9n01102000130105104106X<;fDR;=1BTA1BR>P9ER1@;RfER;f:RU'@1@;FPMP8PK10:0X58PLfGRVP9E[O1WTWBP:O1b1P:O1b1'{WBP:O117QNP8PSP3P:CzWOP:O1n200100000021000010000W1XW8P9P:O2n2001000000120101000b<W8X48O3WSWEXD?X27%23RS/3L\I\G\?^27P8g00_?PEP3Cq10E3RG%?G'oP110D>R1%?1%26%:U'3P:10R6R1P8PUPFP:ChA<9K:997DX67,G7XA7,G7P4P7A<9J:997RX67,G7XA7%2DRG%:J'3P:A<9O:997LX67,G7P4P7A<<N:997KX67%2KR4%:0'3P:A<>P:997MP7A<6T9RTfHRQ=1BVfFRW'=,7CX08#>\@^5810Q9#?fKR@,3S\I[\?^2710V3%2>fI#:'3]>]@]=^??X371M8TA<E;3,0:A1BVW/=;,7CX08#>[^5810V9#?fJRC/PDR;,FKRT,09\H^4813SC[[\?^27A<DW>,0WP8PRP6PVP3Db1FR6,M8P8PUPFPQP>Da1FUF,0Q#?P31FLERQP9P:1FKDRV,0:g00__p4p710RW%C:R?%C9RSg00`<RHAE3<9963:A6>93A6>9<';RI[RXA63:<A63:9';AE>3<96>9RY[RZA66<>A66<3';\YP3P<P9P:C`RYP9n2001000000120000000X;<W2W3W7PX^;<^2S^3?^7WP:P8PMPUP<P9O510<M10<U';PHPXPZAE6>3966<\IPYP:n2001000000120000000X;<X2SX3?X7WPZ^;<^2S^3?^7WP:P8PNfNRW/PKR?P>10>NRS10>KRZ1@W>/;Z,;S1060R0fORW/@6RY106JRI';RX;_:X1SASYI:9S0XX1ZP9E^10>?,;SeO5b1b8b1W8X48O4%2Q/3CP=%2;,D4fLRC#:RQ,3:X0=P=%2V13:CX0=P:1D4GR4AQ8KDE]134@%2JR4%2RRD#:RG'DRV/3Q%44RS%4DR?g00R2RZ#\RX'8R0'8RI%4CRY/8XRH'5PVPIP4PS1A8SRIPGP018:XX48R0PDP?1A8?RGCOEYPQPHP0PCPY1A8YRHCOEH1D4DRV/3C18S?R[/5YR\PVP[P4PSPIPDP?PGEYPCPYPHEHP:CXP\%2URU#B%4U,5A%2ORU#B%4U,5A%BW%4W,5Ag00E?RW#yRU%CWRWP81W8<R\P91W83CV%v8RH%u8RY1N8ZRC%tZ,N8RG5J8%pZ,N8RZ'K,IY%n5R51m8XRI9J8GRS9J8CAJ8ZI'K,IYCU1iY2R2P:P<g00HQRIg00I1RZ'A1j:<=9IZdAk8A9ClRZbGbHbIX98X:8XJ818:9/5<18<XRI,89183X'5[^98^:8^J8P:fQ#4%2M#4%2P#4P>O4bFbUbLbKbQCT1P@R#2,D4/3QebC%2TAQ8K;E[bCbRbDW>W@W=W?POP:PMPJPKPRM:gW1X67P9P:O2n2001000000121101000W1XA7P9P:O2n2001000000121101000b<W>P:O1%?1P3PFP6P:10:EP:W8X48O4%2F/3L%2ERE%:KRF'3%4ER6%4KR1/8XRX'5PEP61A86R7PFPXP0PKP11A81R0COEH13EK1561RXPEP6P7PKP1P0EHP:CXPX%BJ%4J,5A%BD15A?PUPWP8P\P9%f8CVPHPY1KCG,IYP51KCS,IYCUP2PZbGbHbIX98X:815:9159I[^98^:8P:%4N%2L#4P3O3bFbLbKbNCTb1WEP:O1n200110300021110711100bXb@W=W?W3%:>A1B3</=9'ZeWMWPX08X58XV=o"). Qed.

Lemma fake0_lek_push0_none : forall F n LB, (forall F' n', ~ In (mkABlock (ABFake 0) F' n') LB) ->
  fake0_lek 1 (mkABlock (ABFake 0) F n :: LB).
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "h01Fh12F'h21Hh32LBh41nh52n'p;1p;3p;2p;5p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2p1001>p4p710p8g001\j16Tg002<j15Tg0035j30TP0j31Tg003nj14Tg00`Wj22Tg00a^j53Tg00BbR0g00AJR2#6g00Da#5f1R1f0R330f2R4512#4^50^10g00DBf3P4P11213D3W2W3X40W0o"). Qed.

(* [comment removed for export] *)
Lemma fake0_lek_pigeon : forall k LB (fr : nat -> Z),
  fake0_lek k LB ->
  (forall i j, (i < S k)%nat -> (j < S k)%nat -> fr i = fr j -> i = j) ->
  (forall i, (i < S k)%nat -> exists n, In (mkABlock (ABFake 0) (fr i) n) LB) -> False.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) [] "p'0h01nh11xi001xh22H0h37__arithh44__p1h54__x1h64cstrh71yh81Fh93LENh:5cstr0h;1ih<1Ah=1Bh>2HFh?2Hih@2HxhA3Hx0hB2HyhC3Hy0hD4__ffhE8__varmaphF5__withG4__x2hH5cstr1hI1fhJ1lhK3lenhL5starthM3ALLhN1EhO1HhP2HLhQ3Hi0hR3INJhS2LBhT4LEN0hU2NDhV2frhW1jhX1kp;1p;2p;3p;6p;4p;7p;5p;<p;Bp;8p-1g0000R0p4p710R1p8p1000Gp4p70R2P1p8P2p1001>p4p710p8g001\j1STg00?cj2xTg00K:R2j12Tg00bfR1j21Tg00<4j3?Tg002<j1hTg0035j3GTP0j35Tg004cR0j2:Tg00c>j2HTg005]R3j24Tg00Y]j2FTg00`<R4j20Tg00cZj3rTg00C@R5j13Tg00Zoj1gTg00[MR6j2;Tg00d5R7j26Tg0073j2LTg00dQj6KTg00Inj4DTg00JUj1BTg0067j1`Tg00MWj2WTg007Mj1_Tg00N5j4^Tg007kj1]Tg008Ij1\Tg00O8j2[Tg0094j2ZTg00O[j1wTg00[jj3UTg009Wj4TTg00e:j7vTg00P@j1uTg00:fj2qTg00;Hj2pTg00<Nj3oTg00<mj4mTg00=_j4PTg00e^j3lTg00f>j2kTg00f\j6jTg004Gj2fTg00gLj4QTg00ghj5iTg00ZSj6NTg005=j2ETg00hGj4eTg00hfj2dTg006WR8j2RTg00\Ml<cTg00@el<MTg00]2lBbTg00iEj6aTg00:Bj7sTg00Pbj8tTg00BbR9f1R:f0R;3?p=<g00DBR</H;p=8g00BCR=?5:;p=71F<;p=A1L9;p=>P=P=P9P9P2P5P5f3R2g00]Xf2R>P:P;M<cp=CP=P9P1P5P7g00iif5R7f4R1P2P>P:P;M<Mp=@g00DaR?/R;p=91;?;p==P=P9P3P5P8g00C`R@P<P?P2P>P:P;M<Mp=XP=P=P=P9P9P9g00^<P5P5P5P6g00^\P<P?P2P>P:P;MBbp=JP:g00EkR6g00FJRAPAg00FjRBP;Eap=VP:P6PAPAPBP;g00H1Fsp=IP2P6PAPAPBP>P:P;Gtp=YP=P9P:P;CQp=OP=P9P3P5P8P@P7P1P2P>P:P;M<Mp=ng00AJR@#SP9\=1x>:%27R8,1:f6R5#2,1:P7P2O1P7P>O1R3'<A?=12[[[^W=^;=11;8%h?RC?G3;=5@5X09,:9[^;=P=P9P2%88R3f7RD#2#8RE,7:f8RF#2#8RG,7:PDP2O1PDP>O1'<P41H:>,7;14>:1F>2,1:'0[RH14:;1F:>,1;'01H>2,7:RI[142>1F21,1>'0\IAr>:;P:n2001000000120000000X0=XL=XK=RIPH^0=^L=^K=RHP;f;RJ#2RKP<P7P2O414<7%AK,17'0PIPHP;f=RL#2RMP<P5P1O414<5RN%AM,15'0f:ROPFPDf>RP#2RQ,1F%3FRR%3PRSg00R2RT#gRU';RV'6PFPR%>RPQPV1;;URWX19RXPPPS%>SCCRYE@14<DRZ%AQR[,1DR\'0%3DR]#9R^%=V,6]'0R_PZP\P^PXPSO1R\#=R`,6]1L9?RaPDP]%>]RbCXRcPDP]PbP[P`PaPQP\PYCJE@EKP;CDR\P_f9R`,4<R[f?Rd#2Re#ARf,1`Rg'0%3`Rh#9Ri%3dRj/;U#=,6h'0RkP[PgPiPXPjO1Rg#=R[,6hPaP`Ph%>hRlCXP`PhPlPfP[PaPePgPXPdPj%>jCCCJE@EKP2CDRjPk%B`RgPifARe#BR[%3e#9Rff<Rl#BRh%3l#9Rmp-0Rng00E?Ro#`Rp%SoRoP91W9>P:%_9C^%]9Rq%\9RrPrP6PAPAPB1Vr1P91[9TR6g00jKRs1Z9?%wT,[91Z9URT5U9Rt5U9CT,IrFv%uARAP9P6PsPtCT,IrCY1qrBRBP;P>g00HQRtg00I1Rs'L1p;>=?tsdAo9?:CmR?bDbEbFX59XG9W4Rs1;:U#=,6;,0>1;>U,6:[^59^G9^4nRtP;%9SfDRu#3RvPSP1O4b3bHb:b6bAbCCP11DQ16]VPDP]PbPQPVPYE@P\P_PjPkPgPiP[PfPhPmPsPtP;%3LRL#9PvPLP7O4b3bHb:b6bAbCCPP1O5bBb2b@b2WNWBW@X7=X1=P7P:O1P7P;O1Rm'<A?=>:[X7=X1==l=3e1k8<Ej1O23,f91O7ERE959;R3g00k2R8p4p710RhP8p4p7210R8P:\:Rf%S>R[P4P1P2P>P:CQ952;P1P;O1=?7>A55;2'0X17,:7[RiP2P;O1=?1:A57;>'0X11,:1P7P1P2P>CQ951:Rg[A?5m2A5D;1'0X15,:5\gP1P2P>P:P;DiP:n2001000000120000000X7>WJWIW=W<Pi^7>^J[^If^=8^<hP;P=P9PD%2`Rh#8R8P>P:O6PFP;O1/<2%2ORf#8,7;'0X1=,:=P0P=P`P;O1/<1%8K,7;'0X1=AGC7;=5@JX09,:9P;PJP;O1/<5%8M,7;'0P4PlP:O1/<D%8Q,7:AGC`;=5@dX09,:9P;PPP2O1/<`P9PdP1O1fB#2#8,77AGC>;RCfCR755@X09,:9[X89%2e#8,71PIPHP;%27R7P<P5P:O4%A7,15,0NPdPD%2uRd,1D1;vURN,6]PDP]PbPdPNPXPuPv%>vCCRuE@%AdR7,1DRH,0Z%=N,6],0^RNPZPHP^PXPvO1Rv#=R^,6]PcPDP]PbP7P^PaPdPvPuCJE@EKP;CDPN%BF%9RfFRR#B%3R#9PsPtP;%3JRt#9RsfH#3PtP2O4b3b:b6bQCPO2b?b2W?POP;ENW2P:P;O2n2001000000121000000W2X;=P:P;O2n2001000000121100000b>b2W>X89A5@CFX09,:9\3^89P1PEP:P;O31E9E/4DP=1O5G,E914;`X0=P;1E=GRDP=P9P5PGCeEN14DFP=1E=814;OX0=P;Ph1dh<EN14h`14fO%3ORh/;U/RhRUPfPXPhO1PXPOPh%>hRXCCPOPhPXEnP;CDPU%BJPsPpPo1W9:PqPrP9AU96Tg00GJP6CT,IrPA1Vr2CYPBP?bDbEbFX59X4n1RW;P>[^59^4nP;g00IQPLP>O3b3b6bTb9b9b9bPbUWMWRWOWVWSXX=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ASM0K_ENTRY : Z := 0x3cc38.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SM0K_STACK : Z := 4096.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.        (* [comment removed for export] *)
Variable rng_fs : alayout -> footprint -> Prop.  (* [comment removed for export] *)

Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Definition fake_flag_law : Prop :=
  forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Definition fake_release_law : Prop :=
  forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

(* [comment removed for export] *)
Definition sm0k_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (FB0 F :: LB) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8.

(* [comment removed for export] *)
Definition stack_malloc_0k_stmt (k : nat) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  fake0_lek k LB ->                                        (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM0K_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm0k_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASM0K_ENTRY) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma stack_malloc_0k_mono : forall k k', (k' <= k)%nat -> stack_malloc_0k_stmt k -> stack_malloc_0k_stmt k'.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake0k_iface ()) ["CANSEC1"; "Stmts"] "h02AHh12B1h22B2h32FRh41Hh52Hkh61Lh72LBh82LEh92MIh:2R1h;2R2h<2R3h=3RNGh>3SPTh?2STh@2TPhA2a0hB2a1hC2a2hD2a3hE2a4hF2a5hG2a6hH2a7hI2fchJ2gphK1khL2k'hM2lohN1mhO2rahP2s0hQ2s1hR3s10hS3s11hT2s2hU2s3hV2s4hW2s5hX2s6hY2s7hZ2s8h[2s9h\2sph]2sth^2t0h_2t1h`2t2ha2t3hb2t4hc2t5hd2t6he2tpp;2p;1p;7p;4p;3p;5p-1p100kOp4p710R0p8p1000Gp4p70R1P0p8P1p1001>p4p710p8g005]j2JTg00kfj1ITg00O[j10Tg00m3j14Tg00mQj17Tg00NSj13Tg00n4j2CTg00n`j1ATg001\j1@Tg00oBj7?Tg00?cj2>Tg010@j2=Tg0114j29Tg011^j4HTg012Pj1GTg00Zoj18Tg00[Mj2ETg006Wj26Tg013Fj2:Tg013cj1;Tg014Zj2BTg00<4j3DTg015@j3<Tg0163j5FTf0R1#0#0p=5%01#0#0#0p=1%31#3p=2g00BCR0f1R2,J1f2R3#IR4g017:g0184g00R2R5#0R6#5R7#5R8#0R9#4R:#7R;%36#4/C;%48#7%47#7#A\;g018mg00AJ#@g00Bbp,2rcR7p,2AIfVR8fUR6P3P2f3R<F?fZR=/>3g019hR>f5R?'=P>f6R>P<19:8CH%G7%59#1R9#8'Ef4R7'6fXR@,9:g01:]':,6?fYRA,9:f\RB#;'6g01;`,B:9D;@f]R:f8RCf^RD#;/:C3<%19#8%05#3#2#2#2#2#1#1#1#85<Dp,6rng_fsf`R5f_R9O2fbfaP5P9PDP:PBf[P=PAP@fWP8P6fTfSfRfQfPfOfNfMfLfKfJfIfHfGfFfEfDfCfBfAf@f?f>f=f<R6f;f:fdfeP6fcf9DFPCf7P>P?P7P<P3P2P1ObW<W;W:W@W>W2W1W?W9W8W0WMW7W]WNWIW3Xd;Xc;Xb;Xa;XS;XR;X[;XZ;XY;XX;XW;XV;XU;XT;XH;XG;XF;XE;XD;XC;XB;XA;XQ;XP;X`;X_;X^;Xe;XJ;X\;WOW=W6P4eW4W5XL0WKo"). Qed.
End Stmts.
End CANSEC1.

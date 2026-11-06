(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocSites () := "C47Corelib7Classes?RelationClasses9ReflexiveK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6to_posC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt5Pos2Z:pos_is_posK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3oppc69OSSVerify5KrLib6Common5Reloc:RelocSites4up25C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums8positive00C45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions>bv_wf_in_rangeK47Corelib7Numbers7BinNums1N02c69OSSVerify5KrLib6Common5Reloc:RelocSites7up25_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02c69OSSVerify5KrLib6Common5Reloc:RelocSites4app7C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203i69OSSVerify5KrLib6Common5Reloc:RelocSites3sop00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01k69OSSVerify5KrLib6Common5Reloc:RelocSites3sop01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common5Reloc:RelocSites3sop02C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common5Reloc:RelocSites3sop03C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common5Reloc:RelocSites3sop04C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common5Reloc:RelocSites3sop05C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common5Reloc:RelocSites3sop06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites4rl_wC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI69OSSVerify5KrLib6Common5Reloc5Reloc5Reloc00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2Inc69OSSVerify5KrLib6Common5Reloc:RelocSites7site_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List<nth_error_InI47Corelib4Init9Datatypes3nat00i69OSSVerify5KrLib6Common5Reloc:RelocSites5csite00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites;site_nth_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites7cs_addrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites6cs_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyc69OSSVerify5KrLib6Common5Reloc:RelocSites8cs_shapeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites9shape_insC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidable;bool_decidec69OSSVerify5KrLib6Common5Reloc:RelocSites7cs_kindC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites7kind_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib6Common5Reloc9RelocCode>fetch_is_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites5cs_opC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocCode8fetch_isC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites6rl_rawC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decC35stdpp9decidableEbool_decide_eq_true_1C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions5bv_eqk69OSSVerify5KrLib6Common5Reloc:RelocSites5skind02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites5rl_hiC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c69OSSVerify5KrLib6Common5Reloc:RelocSites8rl_imm12C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc69OSSVerify5KrLib6Common5Reloc:RelocSites;bv_eqb_trueC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common5Reloc:RelocSites5skind00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common5Reloc:RelocSites5skind03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:RelocSites8rl_imm21C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4btgtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sop := OP_AUIPC | OP_IMM | OP_LOAD | OP_STORE | OP_FLOAD | OP_JAL.

(* [comment removed for export] *)
Definition app7 (o : sop) (u : positive) : positive :=
  match o with
  | OP_AUIPC => (u~0~0~1~0~1~1~1)%positive   (* [comment removed for export] *)
  | OP_IMM   => (u~0~0~1~0~0~1~1)%positive   (* [comment removed for export] *)
  | OP_LOAD  => (u~0~0~0~0~0~1~1)%positive   (* [comment removed for export] *)
  | OP_STORE => (u~0~1~0~0~0~1~1)%positive   (* [comment removed for export] *)
  | OP_FLOAD => (u~0~0~0~0~1~1~1)%positive   (* [comment removed for export] *)
  | OP_JAL   => (u~1~1~0~1~1~1~1)%positive   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition up25 (z : Z) : positive := Z.to_pos ((z / 128) mod 33554432).

Lemma up25_lt : forall z, Zpos (up25 z) < 33554432.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) [] "p'0h02H1h12H6h21Hh31Eh42H7h52H8h66__sat0h76__sat1h81ah92H0h:3H10h;2H2h<2H3h=2H4h>2H5h?2H9h@7__arithhA4__ffhB8__varmaphC5__withD1qhE2q0hF1rhG2r0hH3H11hI3H12hJ4__x1hK4cstrhL1pi001phM1zi011zhN2z0p%0p;1p;2p;3p;4p;8p;7p-1p10000p4p710p9g000\j19Tg001Aj14Tg001_j23Tg002<j1YTg002\j1UTg003<j1STg003Zj1QTg0048j1PTg004cj2?Tg005Fj2bTg005hj2NTg006Bj2ZTg006nj3FTg007Hj3WTg007gj4VTg008Yj20Tg0095j3Tj2ITg009\j22Tg00:<j1=Tg00:\j28Tg00;8R0j2:Tg00;Sj2MTg00<Dj2LTg00=5j2BTg00=Vj1KTg00=oj2ATg00>Lj2CTg00>ij2DTg00?Pj2ETg00@6j2JTg00@\j1aTg00ADj2`Tg00Abj2_Tg00BEj1^Tg00Bgj8\Tg00CKj1GTg00Cij1HTg00DFj1[Tg00EGj4XTg00F2j7]Tf0R1#9#9p=O%91#9#9#9p=<g00FVR2f1R3g00G4P1CXp=@P3g00G[S00g00H:R4P4g00HZR5P1g00I:F]p=>g00IZR6f2R7'81031':p=7AF231p=51863/:1p=R%43/01p=6AF216p=;1861p=1g00J8R8#9#O#<R9#4R:,31R;%O9#<#<#<#<#4R9g00J]R<#YR=%U<R<%S2R>%Q2R?%P2R@1?261?29RA'@'>1b@5RBP1P7g00KIRCg00KiRD'N1Z17=FCDdAW263CVRDbAbBbC1069RCP1b@3T12;9R;?7;9133:/29P21N21137:/29/51P2f4R;/3:/29/511039S01,R3%=7/69]2]3P3f3RE/3:/29#;1866RF/:Cf5RG/M:%1G%1:RHf7RI/3:#1[[f6RJ/3:RK/L9%1K%19RKf8RL/3:RM/29#1[[1BI:%;:RN#KRO1A:M12L:'C,5L[1IL:106:RMf9RP/2:RQ?7Q:[1DP:10:6RQf:RR/2:RS,0:18S6':[1ER:f;RS/3:RT#;\N1JS:f<RU/2:RV/5U\N13U:P2f=RW/2:RXP21B39RY%;9RZ#K1379,A91279'C,57[R[1I79R\12E9R]?7]9\CR]1DE9R^109612;9R_,0918_6':[R_1E;9R`13G9#;\ZRa1JG9Rb12J9/5J\ZRZ13J9RcP212I9RdP2P0PFPC%48Re/09Rff@RgPPP1O1A7;;9RhfARiP3O1A7UU:RjP0%1JS0210J9S03PfP3%1LRk10P9RlP0%1iS0410i:RmPfP;fCRn#1RofDRp/0:RqP=P<P>P?1?2e/@A,>@PBPDbAbBbCPfP1b@ReW5W0P3P1O2n2001000000120000000W4W1P3P1O2n2001000000121000000b0b1X:CX2FP3P1O2n2001000000121000000bGbEb?b5b4b1b>bFbDb=b<b;b0b9b6b7%=6/69eW2W3g00LIRF13G:/29RC%41'5%43R>?7>9%a7R>%47Rr,06Rs1ML:Rt13R:#1\H\kRH13P:Ru/L9Rv%1u12T9#1\K[RK1BR:Ru1A:T12S:'C,5S\ORO1IS:RTA7VV:\MRM1DU:RU10:X18X6':\QRQ1EW:RXf>R6/3:#;\NRV1J6:Rwf?Rx/2:/5x\NRN13x:RxP212g:RyP2PYP[P\P]P^P_P`PaPbPZPcP2PdP2P0%4nRz#110z916p9PifER{#4R|#1fFR}#4R~/09PPPpO1RpPhPiP{O1RPPj%16R6P{P1P;O2W8%1I^86fO#1R6fGP1PGO2W8%1g^86P0Pk10L9fL/69PE%1R10S9P0Po10n:fP/69PJ%1{10}:P=P<1`23P?P@Q00P4P4P51_28/@A,>@R@%^4P@G\PBPDbAbBbCXJ21019Q01[^J2P1fT#4PWO2b@WIW0P3P1O2n2001000000121000000WHW1P3P1O2n2001000000121000000b7b6b0b1W:W2P3P1O2n2001000000121000000bGbEb?b5b4b1b>bFbDb=b<b;b0b9b6b7bK%=r/69eW2W3WLP1O1%G1,5C%G3RC?7C9P>PsPtPHPvPKPuPOPTPMPUPQPXPVPwPNPxP2PyP2PYP[P\P]P^P_P`PaPbPZPcP2PdP2P0%HzRz#110z9PfPi%H|#1%H~/09PpPhPPPjP0Q02Q03PfP3P0Q04PmPfP;PeXIqX0oP3P1O2n2001000000120000000XHlX1kP3P1O2n2001000000121000000b0b1W:W2P3P1O2n2001000000121000000bGbEb?b5b4b1b>bFbDb=b<b;b0b9b6b7bK%G7#=/69eW2W3XLFP1O1n011010003011110011100P1P7O2b3bNb2%[1/69eXM2o"). Qed.

Lemma app7_wf : forall o z, BvWf 32 (Zpos (app7 o (up25 z))).
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54cstrh61zh71Hh81nh91oi001sp;2p;1p;3p;4p;7p;8g00Lnj2HTg00MQj1PTg00N:j2RTg000\j13Tg00Ngj1^Tg00DFj1CTg00OEj1WTg001Aj17Tg008Yj2>Tg00@\j1gTg00PIj2GTg00Q2j1FTg00QQj3MTg00R:j2NTg00Rfj2OTg002<j1]Tg00SRj3JTg002\j1\Tg00ADj2[Tg003Zj1ZTg0048j1YTg004cj2?Tg00Abj2XTg00BEj1VTg005Fj2STg005hj2TTg006Bj2UTg006nj3fTg007Hj3eTg007gj4dTg00=oj22Tg00>Lj2@Tg00:\j2cTg00;8R0j2bTg00T2j2aTg00EGj4KTg00F2j7LTg00U3j3ATg00UVj3DTg00V9j7`Tg00Bgj8_Tg00IZR1f2R2'cf1R3f0R4'>'bp=0%34#3#3#3p=91a34#7p=6%34#3p=QP2g00G[R5g00H:R6P6g00HZR7g00FVR8P3g00G4P4CKg00I:R9FLp=5AA834p=4AD8349A82p=EAD834p=If4R:f3R;=A82=D835A8=D84p=:P8P3g00V]P4CKp=<P3P5P6P6P7P4P9FLp==P2P5P6P6P7P3P4F`p=;P;P5P6P6P7P2P3P4G_p=11@34,22p=B12;2/@3,2:/@4p=8g00WDR5g00XFR9P01H34%P29033R0[%P390441H23[R<1H;2\01R34P4n2001000000120000000X68W8P<^68^89P4g00J8R9#3R<#9R0#^%C3R=,62%W3%7=%90#9#9#9#9R0#7R='>P5%C;,64R5%30#Q#9#7R0705P;%C2R;#gR5%7;,>1R>g00J]R?g00XdR@,G8RA%F@#FR@#F,G89M8Ag00YCRB'N'O1G8@9M8A/NB,OA%]?5J?3JRA%\?R?1[83RB%Z8R@%Y8RC1?81RD1X89RE55CRF%V6R6PC1?8=95CERGP6%7<R<,?8RHPH14HERE,4HRI,4HRJ%79R9,?8RK5EH,4HRL/IKPKPKD:RM,<D,=C1?80RN95CM5;CC1C11SC7R7P4P2g00KIRMg00KiRO'T1U42=fMOdAe813CdROb2b3b4X081>14R11>3=R=P<P<12<2RM,2<RP,2<RQ=B<9,2<RR/@9P9P9D8RS?0S0[[^08P4%C:#7P3P2O3R2b1b5g00Yo/6;R3?030eP5P>PAP?PBP@PCPFP6PCPGP6PHPHPLPKPKD:RL,<D,=CA5CLN5;CC1C1P7POb2b3b4X08P<P<PRP9P9D8RR?0R0\=\1^08P2b1b5g00[1/6;RR?0R0eP5P>PAP?PBP@PCPFP6PCPGP6PHPH14HJ,4HRJPKPKD:RR,<D,=CA5CRN5;CC1C1P7POb2b3b4X08P<P<12<Q,2<RQP9P9D8RR?0R0\=\1^08P2b1b5g00\3/6;RR?0R0eP5P>PAP?PBP@PCPFP6PCPGP6PHPHAEHIK,4H,4HPKPKD:RI,<D,=CA5CIN5;CC1C1P7POb2b3b4X08P<P<AB<P9,2<,2<P9P9D8RP?0P0\=\1^08P2b1b5g00]5/6;RP?0P0eP5P>PAP?PBP@PCPFP6PCPGP6PHPH1IJKPKPKD:RJ,<D,=CA5CJN5;CC1C1P7POb2b3b4X08P<P<1@Q9P9P9D8RQ?0Q0\=\1^08P2b1b5g00^7/6;RQ?0Q0eP5P>PAP?PBP@PCPFP6PCPGP6PHPHPHPHAEHEK=EHKPKPKD:PKPKD:RK,<D,=CA5CKN5;CC1C1P7POb2b3b4X08P<P<P<P<AB<M9=B<9P9P9D8P9P9D8R9?090\=\1^08P2b1b5g00_9/6;R;?0;0en011000006010101010101b7O3b7X68W9o"). Qed.

Section Defs.
Context {RL : Reloc}.

(* [comment removed for export] *)
Definition rl_raw (c : Z) : bv 32 := Z_to_bv 32 (slookup rl_stab c).
Definition rl_w (o : sop) (c : Z) : bv 32 := @BV 32 (Zpos (app7 o (up25 (slookup rl_stab c)))) (app7_wf o _).

(* [comment removed for export] *)
Definition rl_ins (c : Z) : instr :=
  match decode_any (rl_raw c) with Some (i, _) => i | None => Ebreak end.
Definition rl_imm20 (c : Z) : bv 20 :=
  match rl_ins c with Auipc _ imm | Lui _ imm => imm | _ => Z_to_bv 20 0 end.
Definition rl_imm12 (c : Z) : bv 12 :=
  match rl_ins c with
  | OpImm _ _ _ imm | Load _ _ _ _ imm | Store _ _ _ imm | FLoad _ _ _ imm | FStore _ _ _ imm
  | Jalr _ _ imm | OpImm32 _ _ imm => imm
  | _ => Z_to_bv 12 0
  end.
Definition rl_imm21 (c : Z) : bv 21 :=
  match rl_ins c with Jal _ imm => imm | _ => Z_to_bv 21 0 end.

(* [comment removed for export] *)
Definition rl_hi (b : positive) (c : Z) : word :=
  v_auipc (rl (rl_delta b) c) (Z.shiftl (bv_signed (rl_imm20 c)) 12).

End Defs.
Arguments rl_raw : simpl never.
Arguments rl_w : simpl never.
Arguments rl_ins : simpl never.
Arguments rl_imm20 : simpl never.
Arguments rl_imm12 : simpl never.
Arguments rl_imm21 : simpl never.
Arguments rl_hi : simpl never.

(* [comment removed for export] *)
Lemma rl_w_not_ecall : forall {RL : Reloc} o c, is_ecall (rl_w o c) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) [] "p'0h02RLh11ch21oi001sp;3p;1p;2g00`;j33Tg00a<j12Tg006nj30Tg005hj21Tg00b<g00WDR0g00FVP0g00KIR0f3f0f1R133#2g00c;R230P11102R2P2P2P2P2P2n011000006000000000000W1W2W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sshape :=
| SH20 (f : bv 20 -> instr)        (* [comment removed for export] *)
| SH12 (f : bv 12 -> instr)        (* [comment removed for export] *)
| SH21 (f : bv 21 -> instr).       (* [comment removed for export] *)

Inductive skind :=
| SK_auipc
| SK_lo12 (ca : Z) (X : positive) (t : Z)   (* [comment removed for export] *)
| SK_jal (X : positive) (t : Z).            (* [comment removed for export] *)

Record csite := mkSite { cs_addr : Z; cs_blk : positive; cs_op : sop; cs_shape : sshape; cs_kind : skind }.

Section Check.
Context {RL : Reloc}.

Definition shape_ins (c : Z) (sh : sshape) : instr :=
  match sh with
  | SH20 f => f (rl_imm20 c)
  | SH12 f => f (rl_imm12 c)
  | SH21 f => f (rl_imm21 c)
  end.

Definition kind_ok (b : positive) (c : Z) (k : skind) : bool :=
  match k with
  | SK_auipc => true
  | SK_lo12 ca X t => bv_eqb (v_addi (rl_hi b ca) (bv_signed (rl_imm12 c))) (rl (rl_delta X) t)
  | SK_jal X t => bv_eqb (btgt (rl (rl_delta b) c) (bv_signed (rl_imm21 c))) (rl (rl_delta X) t)
  end.

Definition site_ok (s : csite) : bool :=
  fetch_is rl_segs (cs_addr s + rl_delta (cs_blk s)) (bv_unsigned (rl_w (cs_op s) (cs_addr s)))
  && bv_eqb (rl_w (cs_op s) (cs_addr s)) (rl_raw (cs_addr s))
  && bool_decide (decode_any (rl_w (cs_op s) (cs_addr s)) = Some (shape_ins (cs_addr s) (cs_shape s), 4%Z))
  && kind_ok (cs_blk s) (cs_addr s) (cs_kind s).

Definition sites_check (tbl : list csite) : bool := forallb site_ok tbl.

Section Sound.
Variable tbl : list csite.
Hypothesis Hok : sites_check tbl = true.

Lemma site_nth_ok : forall i s, nth_error tbl i = Some s -> site_ok s = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) ["Check"; "Sound"] "h02Hih13Hokh21ih35lemmah41sh51xp;1p;3p;2p;5g00c[j1:Tg00d=j39Tg00d[j22Tg006nj30Tg00e=j38Tg00eYj37Tg00f0R0j13Tg00g4j24Tg00gMj35Tg00h>j36Tg00haj51Tg00iBg00iaR1%:1p,3tblR2f1R3591f0R4,2130g00KIR5A8102g00KiR630R7A7142%33=056[^51R6'4A5764W3A6102p,3HokO2P6P4f2R4P1P2f3P4P3D1O2b1W0W4W2o"). Qed.

Theorem site_F : forall i s, nth_error tbl i = Some s ->
  fetch_word rl_segs (rl (rl_delta (cs_blk s)) (cs_addr s)) = Some (rl_w (cs_op s) (cs_addr s)).
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) ["Check"; "Sound"] "h01Hh12_Hh22Hih31ih41sp;1p;3p;2p;4p;6g00c[j1HTg00d=j3]Tg00d[j25Tg006nj33j1OTg00jej3\Tg00f0j1UTg00kmj1PTg00llj11Tg00n0j1@Tg00o3j2GTg000\j1?Tg00Ngj1KTg0103j26Tg010Qj2TTg0111j1=Tg011bj1<Tg012gj29Tg001Aj1QTg013mj4NTg014Kj2MTg014hj6:Tg015@j2>Tg015^j1ETg016bj3CTg017fj3FTg00;8R0j2DTg018Ij1LTg018lj2BTg019fj2ATg00>Lj2ITg01:hj2JTg005hj2RTg01;Rj6STg01<\j1[Tg00`;j3ZTg01=^j3YTg01>bj2VTg01?ej3WTg01@Rj4XTg00KIf0R1g00Ki33p=0f2R2f1R3#[;Z1p=2f4R4f3R5/I21J313Yp=81V319W52p=7g01A2R6g00FVR7P3P1CXp=;%@1,G3p=4g00iBg00iaR8%H8p,3tbl=]83158133A\231%U3#0p,2RLR8#PR9%12R:%@2R;,G8g00J8#?#?R<#?#?#?#KR=A282:R>D8P=P>P8P:C7'61T67R?#HR@%=>R>%<2,9:%Q<R<';,5?RA33P@P@%O@RBP6g01A^P7g01BOCN,M?R6P>PAE:'>'6RA%E29C;:R;;F1%0A%0;'DP0P9%15R;%@5RA,G8P=A285;R:D8P=P:P8P;C7'6%=:R:%<5,9;/;<,5?R253@P@P@PBP6P:P2E:'>'6#0%E59CA;#0%L=RA#HR;1484%14R5'B,A9A2845,5A33P1P9f5R5#1R41485P=A2854R2D8P=P2P8P4C7'6%=2R2%<5,94/;<,5?R453@P@P@PBP6P2P4E:'>'6#0f6R4#@%14%E43C#0P9f7R4#1R21484P=A2842R5D8P=P5P8P2C7'6R:%=5R5%<4,92/;<,5?R253@P@P@PBP6P5P2E:'>R2;F3%0:%02'DP0P9f8R2#1R:1482P=A282:R5D8P=P5P8P:C7'6#0%=5R5%<2,9:/;<,5?R:53@P@P@PBP6P5P:E:'>#0f9R:,48%1:R5'B,A9A28:5,5A53;P1P9f:R5#1R:1485P=A285:R5D8P=P5P8P:C7'6#0f;R:%1:R5528#=R2%<:,95/;<,5?R?53@P@P@PBP6P2P?E:'>#0P9f<R?#1R2148?P=A28?2R?D8R6P=P?P8P2C7R2;F3%06%02'DP0P9f=R0#1R21480P=A2802R0D8#0P=P0P8P2C7#0f>R2,48%12R0'B,A9A2820,5A53;P1P9f?R0#1R21480P=A2802D8#0P=f@R2%12R2528P8P2C7#0P9fAR2#1R01482R6'IA2820R2,J=R=P2P31R7=ES1B60,A915A253;eW1W0P3P1O2n2001000000120000000b0W1W0P3P1O2n2001000000121000000b0W1W0P3P1O2n2001000000121000000b0b0W2W4W3o"). Qed.

Theorem site_D : forall i s, nth_error tbl i = Some s ->
  decode_any (rl_w (cs_op s) (cs_addr s)) = Some (shape_ins (cs_addr s) (cs_shape s), 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) ["Check"; "Sound"] "h01Hh12_Hh22Hih31ih41sp;1p;3p;2p;4p;6g00c[j1FTg00d=j3VTg00d[j2DTg006nj31j1LTg00jej3UTg00f0j1RTg00kmj1NTg00llj12Tg00n0j17Tg00o3j2;Tg00>Lj2=Tg000\j1@Tg00Ngj1TTg01:hj2?Tg01=^j3<Tg01>bj2>Tg01?ej39Tg0103j25Tg010Qj2OTg0111j14Tg001Aj1MTg013mj4KTg014Kj2JTg014hj68Tg015@j2:Tg015^j1ATg016bj3BTg017fj3CTg00;8R0j2ETg01Bhj3ITg01<\j1HTg00`;j3PTg011bj1QTg012gj2GTg01@Rj4STg00KIf0R1g00Ki31p=0f2R2f1R3#H;P1p=3f3R4g01A2R5g00FVR6%Q3,G2P1CS'Dp=6g00iBg00iaR7%F7p,3tbl=V731D7131AU231%R3#0p,2RLR7#NR8%22R9%72R:,;7'=g00J8#@#@R;#@#@#@#TR<A3729R='?3<1>7999<='51O56R>#FR?%4=R=P>P9P2%M;R;C6R@31P?P?%L?RAP5g01A^P6g01BOCK,J>R6P=P@E8':'5R@%A29B:9R:;C1%0@%0:'EP0%24R:%74R@,;7'=A374:R9,?<5<81>7:99<9'5%49R9P>P:P4P;C6R251?P?P?PAP6P9P2E8':'5#0%A49B@:#0f4R@%2@R:537#4P>P:P@P;C651?P1f5R@#2R:%7@,;7'=A37@:R4,?<5<81>7:99<4'5%44R4P>P:P@P;C6R@51?P?P?PAP6P4P@E8':'5#0f6R@#7%2@%A@3B#0f7R@#2R4%7@,;7'=A37@4R:,?<5<81>7499<:'5R2%4:R:P>P4P@P;C6R@51?P?P?PAP6P:P@E8':R@;C3%02%0@'EP0f8R0#2R@%70,;7'=A370@R2,?<5<81>7@99<2'5#0%42R2P>P@P0P;C6R051?P?P?PAP6P2P0E8':#0f9R0%20R2537#4P>P2P0P;C651?P1f:R0#2R2%70,;7'=A3702R0,?<5<81>7299<0'5#0f;R0%20R<537#4R2P>P<P0P;C6R051?P?P?PAP6P2P0E8':#0f<R0%20R2537#4R7P>P2P0P;C6R;51?P?P?PAP6P7P;E8;I1W0W1P3P1O2n2001000000121000000b0W1W0P3P1O2n2001000000121000000b0b0W2W4W3o"). Qed.

Lemma bv_eqb_true : forall (n : N) (x y : bv n), bv_eqb x y = true -> x = y.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) ["Check"; "Sound"] "h01nh11Hh22H0h32b1h42b2h51mh61xh71yp;1p;3p;2g018Ij13Tg01?ej38Tg01CPj25Tg01Cmj27Tg01:hj20Tg006nj32Tg01DMj36Tg00KIf0R0g00Ki32p=4g00FVR1f1R2;20p=1g00XFR3%30R4%32R5f2R6?820#4g00;8R71520#41162[R811201562#4R9[f3R:/16\91720P2n2001000000120000000X51X01P8^51^01P0f4R1/0:R81016R9P2O31189P7%36?22010:610:2'1R7[10621060'1%3:?262[R9%31?2:6\7A6620P0n2001000000120000000X45X34X03P9^45^34^03P0f6f5P1P2O4b2b1b2W1W7W6W0o"). Qed.

Theorem site_V : forall i s ca X t, nth_error tbl i = Some s -> cs_kind s = SK_lo12 ca X t ->
  v_addi (rl_hi (cs_blk s) ca) (bv_signed (rl_imm12 (cs_addr s))) = rl (rl_delta X) t.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) ["Check"; "Sound"] "h01Hh11sh22Hih32Hkh41Xh52_Hh62cah71ih81tp;1p;3p;2p;4p;6g00c[j1KTg00d=j3^Tg00d[j29Tg006nj34j1UTg015^j17Tg01E1j3JTg00jej3ZTg00f0j1YTg00kmj1VTg00llj13Tg00n0j12Tg00o3j28Tg00>Lj2FTg000\j11Tg00Ngj1GTg01<\j1ETg00`;j3CTg01:hj2BTg01=^j3?Tg01>bj2@Tg01?ej3ATg0103j25Tg010Qj2XTg0111j1>Tg011bj1=Tg012gj2<Tg001Aj1WTg013mj4TTg014Kj2QTg014hj6;Tg015@j2:Tg016bj36Tg017fj3PTg00;8R0j2RTg018Ij1OTg01F5j3HTg01G7j1STg01G\j2NTg01Haj2MTg01IIj2LTg018lj2ITg01JDj6]Tg01J`j4\Tg01@Rj4[Tg00KIf0R1g00Ki34p=0g01A2R2g00FVR3f1R4P1C[p=Dg00iBg00iaR5g00LI%K5p,3tblf4R65^5f3R7,9534g01KhR5%76f2=J7434f6R7f5R6;Z4%Y6#0p,2RLR8#VR9%37R:%27R;,88'Fg00J8R<#1#1R=#1#1#1R>#GR?%E7=C8:R@'B3?1@8:9A?@'51X23RA#KRB%>@R@%=7,<:%W=R='D,9ARC34PBPB%UBRDP2g01A^P3g01BOCT,QAR2P@PCE;':'5RC%7796;:R;;P1%0C%0;'RP0f7R0#3R;%20RC,88'F%E0=C8;R:,B?5?91@8;9A?:'5%>:R:%=0,<;/D=,9AR@54BPBPBPDP2P:P@E;':'5#0%7096C;#0%1>#GR>#Of8RC#2=H80%S<#1#1#GR<%3C,N8'M'L1887/I634P1f9R6#3R0%26,88'F%E6=C80R;,B?5?91@809A?;'5%>;R;%=6,<0/D=,9ARA54BPBPBPDP2P;PAE;':'5#0f:RA#2%3A%7A36#0P5f;R;#7f<R2#2RD%32R2;61#0X15P1AJA6CRCP7E]%2;%3;;6C#0P>AH8D;1N82,M<'L188A/I6P1C\b0W0W5P4P1O2n2001000000121000000b0b0W3W2X83W4X63W1W7o"). Qed.

Theorem site_J : forall i s X t, nth_error tbl i = Some s -> cs_kind s = SK_jal X t ->
  btgt (rl (rl_delta (cs_blk s)) (cs_addr s)) (bv_signed (rl_imm21 (cs_addr s))) = rl (rl_delta X) t.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocSites ()) ["Check"; "Sound"] "h01Hh11sh22Hih32Hkh41Xh52_Hh61ih71tp;1p;3p;2p;4p;6g00c[j1KTg00d=j3]Tg00d[j29Tg006nj34j1TTg015^j18Tg01Llj2JTg00jej3YTg00f0j1XTg00kmj1UTg00llj15Tg00n0j12Tg00o3j21Tg00>Lj2ETg000\j13Tg00Ngj1HTg01<\j1GTg00`;j3FTg01:hj2DTg01=^j3CTg01>bj2BTg01?ej3ATg0103j26Tg010Qj2WTg0111j1@Tg011bj1>Tg012gj2?Tg001Aj1VTg013mj4STg014Kj2QTg014hj6<Tg015@j2;Tg016bj37Tg017fj3PTg00;8R0j2RTg018Ij1OTg018lj2:Tg01G7j1ITg01N0j2NTg01Haj2MTg01O5j2LTg01JDj6\Tg01J`j4[Tg01@Rj4ZTg00KIf0R1g00Ki34p=0g01A2R2g00FVR3f1R4P1CZp==g00iBg00iaR5g00LI%K5p,3tblf3R65]5f2R7,9534g01KhR5%861J7434f5R7f4R6;Y4%X6#0p,2RLR6#UR8%57R9%27R:,16'Eg00J8#3R;#3R<#3#3#3R=#HR>%G7=F69R?'D3C1B699A>?'61W23R@#KRA%@?R?%>7,?9%V<R<'=,9@RB34PAPA%TARCP2g01A^P3g01BOCS,Q@R2P?PBE<';'6RB%8797:9R:;P1%0B%0:'RP0f6R0#5R:%20RB,16'E%G0=F6:R9,D>5C81B6:9A>9'6%@9R9%>0,?:/=<,9@R?54APAPAPCP2P9P?E<';'6#0%8097B:#0%3=#HR=#Of7RB#2,16%5BRB':%I;#3#I#HR;1N6B'M'L1160/:734P1f8R7#5RB%27,16'E%G7=F6BR:,D>5C81B6B9A>:'6%@:R:%>7,?B/=<,9@R@54APAPAPCP2P:P@E<';'6#0f9R@#2%5@%8@37#0P5f:R:#8f;R2#2RC%52R2;71#0X15P11J@7R7P0E\%2:%5:;77#0P=116C/:21N62,M;'L116:/:@P1C[b0W0W5P4P1O2n2001000000121000000b0b0W3W2X73W4W1W6o"). Qed.
End Sound.
End Check.

(* [comment removed for export] *)
Fixpoint site_find (tbl : list csite) (i0 : nat) (c : Z) : option (nat * positive * skind) :=
  match tbl with
  | [] => None
  | s :: tbl' => if Z.eqb c (cs_addr s) then Some (i0, cs_blk s, cs_kind s) else site_find tbl' (S i0) c
  end.

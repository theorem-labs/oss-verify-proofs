(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP F_ammap F_apoison APoisonR_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASec () := "C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6LookupK47Corelib4Init9Datatypes4list01I46Stdlib5Lists4List5NoDup00I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC59OSSVerify5KrLib5AsanW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib5Lists4List5NoDup01K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4list00I46Stdlib7Sorting;Permutation;Permutation00c59OSSVerify5KrLib5AsanW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;Permutation>Permutation_inI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib5AsanW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib5AsanW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib5AsanW4ASec;granules_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appc59OSSVerify5KrLib5AsanW4ASec?sec_user_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition sec_live (st : astate) (ch : achunk) : Prop := exists p, (a_live st) !! p = Some ch.
Definition SEC_MAGIC : Z := 0xCC6E96B9CC6E96B9.  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_disjoint (cs : list achunk) : Prop :=
  List.NoDup cs /\
  forall ci cj, In ci cs -> In cj cs -> ci <> cj ->
    sec_mb ci + sec_ms ci <= sec_mb cj \/ sec_mb cj + sec_ms cj <= sec_mb ci.
Lemma sec_disjoint_nil : sec_disjoint [].
Proof.
ltac2:(KReplay.run1 (kr_t_ASec ()) ["CANSEC1"] "h02cih12cjh21Hp;1p;2p;3p;4p-1R0g0000R1p4p710p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER2p4p710p8P0P2p4p7210p8g001Yj1;Tg0029j2:TP1j35Tg002Uj36Tg002oj17Tg003Hj13Tg004@j12Tg0058j21Tg005Uj20Tg0061j24Tg006Kj18Tg006gj49Tg007BR1%;1R2':f1=512R0f3R3f2R4561#7f4R5#3R6%25'1R7%33R8'0%23,18/06'4[\0[^11^01%81g008=A5142A6153#7f5R5#3R3%25'1/061073'4[[f0n010000000X20X11X01C9o"). Qed.
Lemma sec_disjoint_perm : forall cs cs', Permutation cs cs' -> sec_disjoint cs -> sec_disjoint cs'.
Proof.
ltac2:(KReplay.run1 (kr_t_ASec ()) ["CANSEC1"] "h02cih12cjh21Dh31Hh42Hih52Hjh62NDh72NEh81Ph92csh:3cs'p;1p;3p;2p;5p;4p;6g008Zj1?Tg009:j3>Tg009ej13Tg0029j21Tg0000j30Tg002Uj3;Tg002oj1:Tg003Hj14Tg004@j15Tg0058j22Tg005Uj26Tg0061j28Tg00:aj59Tg00;Pj4=Tg00<=j67Tg006gj4<Tg007BR0#?R1f1R2f0R35>0f2R4#3g00<if3R5,10f5R69002f6R79002A;054#:R8f4R9#4R:%59'2%45R;'6%55,2;/6:'8[R:[[^10^00%35P31106f89002R;f99002R<P:[[^10^00R:1107P:P0f7P7P6P2D9P6P9P5P0f;R6f<R7P9P0P7P6f:C=R9P4E7P0P6P7P5P9P2E7P3O5X78X5<X4;X10X00C<W2W6P2P3O2n2001000000120000000W3W8X:1W9o"). Qed.

Definition asec_wf (L : alayout) (st : astate) (cs : list achunk) : Prop :=
     alayout_ok L                                                          (* [comment removed for export] *)
  /\ a_ptr_array st = al_ptr_array L
  /\ (a_nres st mod 16384 = 0 /\ 0 <= a_nres st <= 1048576) /\ Z.of_nat (length cs) = a_nsec st /\ 0 <= a_nsec st <= a_nres st
      (* [comment removed for export] *)
  /\ Forall (sec_wf1 L) cs /\ sec_disjoint cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_user_shadow (lv : bool) (n : Z) : list byte :=
  if lv then block_shadow_bytes n else repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)).

Lemma granules_eq : forall n, 0 <= n -> granules n = shlen n + (if n mod 8 =? 0 then 0 else 1).
Proof.
ltac2:(KReplay.run1 (kr_t_ASec ()) ["CANSEC1"] "p'0h04__x1h14__x2h24__x3h34__x4h44__x5h57__arithh64__ffh78__varmaph85__with91ri001rh:1Hh;2H0h<2H1h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD1qhE2q0hF2r0hG1zhH1NhI1bi011bhJ1ei021ehK1ni031nhL2n0p%0p;1p;2p;3p;4p;6p;7p;8g00=Dj1OTg00=ij1BTg0058j25Tg00>Gj1NTg00>lj2sTg00?Ij24Tg00?fj2MTg00@Fj20Tg00@fj2RTg00ACj2cTg00AeR0j2xTg00BHj2]Tg002oj1[Tg00Bij2?Tg00CFj2YTg00Cmj26Tg00<ij29Tg00DIj2WTg005Uj2JTg00E0j2TTg00EVj2^Tg00F<j1gTg00FZj2fTg00G;j1=Tg00GZj3GTg00HCj2eTg00Hlj2QTg00IUj3dTg00J>j2CTg00Jjj2bTg001Yj1aTg00KVj3ETg008Zj1`Tg00L6j2_Tg00LTj1wTg00M2j4LTg00MPj1vTg00Mnj1uTg00NYj2>Tg00O<j1rTg00O^j2ATg00PAj3ZTg00Pdj3@Tg00QGj2qTg00Qij2pTg00RCj2oTg002Uj3DTg00Roj3mTg00SNj4lTg00T@j3VTg00Tij6UTg00UGj1kTg00V?j1nTg00W8j3FTg00Waj4HTg00XLj7jTg00Y0j6iTg00YTj8hTg00Z8j7tTg00Z\R1f0R2'Jp=:g00[:R3f2R4f1R5/523Dp=3AD321p=7AD352p=S1Q32p=<AF3529F34p=8AF352p=PP3P5g00[XP2CHp=;P5g00\?R6g00\^R7P7g00]>R8P2g00]^Fjp=2P5P6P7P7P8P2Eip=\f3R9P6P7P7P8P4P5P2Ghp=1P3P5g00^>P2CHp=IP3P5g00^eP2CHp=KP4P6P7P7P8P5P2Ftp=X%:2P3g00_LR6#OR:#O#BR;,55R<%N6R=#B%B:R>'sR?'41M4>g00`1R@P3%N=RA#N#BRB,04/R1RCP1%B6RDn0100000020000RE532XG3P3145?154;/4??32EXG3105BRE/c1%7E1RE1S00'xPCP@P0109B#7f5R0/5;RC/4B140BP@P3P5P1PDn010000002000033P5f4RE/0B#7R?1]CBS01%7BRF#[RGf6RH/5;RI14IB,?B10IB33[RJ1YIBRK161BRLf7RM/5;RN/0BRO#:16OB'9[RO1WNBRN16B1RPf8RQ/5;RR/0BRS,6B1JS1'9[RS1TRBRRf9RT/5;RU/4B#7\FRV1^UBRUf:/5;RW/0B/SW\FRX14WBRWP3f;/5;/0BRYP3f</]BRZf=R[14[B,?B10[B33\GRG1Y[BR\f>R]/0BR^#:16^B'9\LR^1W]BR_f?R`/0BRa,6B1Ja1'9\PRP1T`BRaf@Rb/4B#7\FRc1^bBRbfARd/0B/Sd\FRe14dBRdP3fB/0BRfP3g00`QRg%g6,f3Rhg00a=Ri#=Rj#=Rk#=Rl#=Rm#=Rn#<Ro5G3Rp%<lRl%<kRk%<jRj9G3h1e3B1Q3iRi5d3Rq3838g00a\Rr'C%<mRmAG3hkRh/Pj58o1Pij/Cr'b%agRi5Eg3E%`gRsP3P31_3EP4%w3RtCLP5P31_30P9PtCLCLRu%v3Rv%u3RwPw1>3BRx1>31Ry';,2w,\wRz%r7R71A3:R:1A3=R{9Z3x1A3ARA5@3';,2wC1R|P7PwPw1Iyx,2wR}P7%O=,A3R=,Ky,2w1I=x,2w5XwC1R~P7PwPwPzP71>3;9@3:1A36R69Z3x=@3=';,2wC1R=P7Pw1;Ay,2wR:P7A@3{y,;6,2wC1C1C1C11qw8R8P2P4g00bHR;,p@1o24=D@;dAm315ClR;b6b7b8X03X13X23X33X43g008=Rz\FRF1?B4=39E[%:H16HB'9\L1?B9R9=3CM\F%7HA3E01[[[[^03^13^23^33^43P2PQP5fDRCP4PTPMP[P]P`O9b5bFbEbCbBbAb@b?b9bDb>b=b<b;b:WJP2O1%[?Q01PJPKPOPNPSPRPVPUPXPWP3PYP3PZPGP\P^P_PPPaPcPbPePdP3PfP3A8kjq98pl/Cr%=n#<A8mhq78o/Cr=Egi5EgPsPuPvPwPwP}P71KyA,2w1IAx,2w5XwC1P7PwP|P7PwP~P7PwP=P7Pw1\w:P71>3D9@3{,;6,2wC1C1C1C1C1P8P;b6b7b8X03X13X23X33X43%:E16EB'9\LA3E90\F%:M16MB'9\L1?BE=3IQ\F%7MPz[A30HD[[[[[^03^13^23^33^43P2PQP5PCP4PTPHPMP[P]P`O:b5bFbEbCbBbAb@b?b9bDb>b=b<b;b:WLP2O1n10210110000021110211103bIb91M5>PiPsPtPv1>3>,Ky,2wP8P;b6b7b8%:>P2b5R29V5>EU1M<>AV<>2EU%k5%n5P@P3Q00P1PDn010000002000033eWHXK3o"). Qed.
Lemma sec_user_shadow_length : forall lv n, 0 <= n -> length (sec_user_shadow lv n) = Z.to_nat (granules n).
Proof.
ltac2:(KReplay.run1 (kr_t_ASec ()) ["CANSEC1"] "p'0h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71nh81xh92H0h:2H1h;4__p1h<4__p2h=2z0h>2z1h?1Nh@1ShA1bi001bhB2lvi012lvhC1yhD1zp&0p;1p;2p;3p;4p;6p;<p;Bp;7p;8g00>Gj1RTg00bhj1|Tg00cFj1lTg008Zj1jTg00cij1cTg00=Dj1DTg00=ij1MTg00dkj2CTg00UGj1dTg00eQR0j14Tg00f1j3YTg00fPj27Tg00V?j1iTg00@Fj2PTg00@fj2fTg001Yj1bTg00KVj3JTg00g0j2:Tg0058R1j23Tg00?fj2=Tg00gGj2{Tg00gnj4xTg002Uj1[j3LTg00hIR2j1`Tg00hij2pTg00iLj3nTg00Qij2FTg00iij2STg00<ij21Tg0061j2?Tg00F<k10<Tg00FZk20;Tg00G;j1KTg00Hlj2ATg00GZj3QTg00L6j2gTg00LTk10:Tg00M2j4eTg00MPk109Tg00Mnk108Tg00NYj2aTg00O^j2XTg00O<k103Tg00Pdj3NTg00QGk202Tg00RCk201Tg00Roj3zTg00SNj4yTg00jKj4^Tg00k6j2vTg00Tij6UTg00l1j3\Tg00lSj3uTg00m0j3tTg00mOj2sTg005Uj2hTg00nNj2rTg00nkl<}Tg00oPlB_Tg0106l<qTg00Cmj2~Tg00W8k300Tg00J>j2oTg00Waj4WTg00XLk704Tg00Z8k705Tg010[k706Tg00YTk807Tg011?j6mTg00Z\R3f0R4'hp=Hg011cR5f1R6;L4p=21r34p=8g00[:R7?L64p=5P7P5P7P7P0f4R0P2f3R8g012Bf2R9P6P4M<}p=TP5P5P5P7P7P7g012oR:P2P2P2P1g013OR;P8P9P6g00a=R<P3P4MB_p=kP5P7P4P2P6P9P8P0f5R=f6R>f7f8R?M<qp=Z1~34p=;1h43p=@AL743p=GB00764p=6g00a\,o4p=Eg00`QR@?J64p=9P7P6g00^>P4CWp=VP6g00\?RAg00\^RBPBg00]>RCP4g00]^K04p=0P7P6g00[XP4CWp=<P9PAPBPBPCP6P4K05p=>P7P6g00^eP4CWp=IP9PAPBPBPCP6P4K06p=OP8PAPBPBPCP9P6P4L07p=BP5P5P5P7P7P7P:P2P2P2P1P;P=P0P8P9P6P4MB_p=wP6PAPBPBPCP4Emp=]g00`1RA%H4R;PAg00_LR1#RR2#RR:#RRD#|RE#lRFPA%jFRGP4%c9%D1RH#D#D#D#D#R#D#M,CERI%d9#4RJ5YFn0110100020000'7/2JP9P51CE3RK%i6RL#4RM5YFRN,7FROPAPG%MDRD,P6RP/f3RQ%bFRR1CEP=JFRn0100000020000RP,7F':124JX75P5PMPAPG1P9DRS/f3RTPR1CES=JFRn0100000020000,7FRS,:4/2JX75P7PAP7PQP3%M1RQn0100000020000,3L%i9RL#4/:SRS%44'2XD7%MHRH,=6#HRJ%H9[%H6RU1=9H#H[1{6HP4CxPJPTPAPA1=0HRJ#4PAPGP4PR1P0D,CE=JFRn0100000020000,7F':PAP7P4P3PQn0100000020000,3J#4'2P41=8HRG#4RV/:<RW13G3RX#4RY'2%8GRZ/33R[%8XR\'5%[5R]%[7R^%`6%`4'512641p643nXC5X85R5PWP[PVPZP4X87R[%84X87RWPGPG1F7GDTR_1F73CkPYP\P[PWPXPX1F7XDTM9Z1S3X%;X15\X'1%@X%G\'1'?13J3#8P71==HR\,S3RX%;\%8\R`/5\'1%@\%G`'1'?R`1=>H#8R\P7&0<1-0;7Ra%K<Rb#KRc#KRd,A7Re5Q71A7bRf1A7<R<'6'6#ERgAQ7af/6<,6e#ERe%b@Rh,9e,9g'9'9%j@R@P7P71g78P9&0:7RgCeP6PgCeRg&097Re&087Ri1a73Rj1X7:R:'V,0i1X71R1/<:,0iRk5>i1I:j,0i1<1j,0i5>iRl5Oi&03BRBPiAN7:jRm,Vj,0i1X72R2/<m,0i5>i1Imj,0i1<2j,0i5>i5OiPBAN71j/<2,0iCBCB202iCRCP4P9g00bHRm,FA20149=LAmdAz736CyRmb4b5b6X07X17X27%;91549Rn'1%@9%G4'1Ro'?1383Rp#;159p'1%@p%G9'1'?1393/58[[^07^17^27P41=?HRHP8P6P9P0O5b3b>b:b=b9C^17FR,:V/2Ye1:VbRY13GQRG#4R?'213ZQRp%8GRq'5P]P^P5PYPpPVPZP_PbPQ1F7QEwP?PqP[PWPGPG1F7GDTM9Z1S3G%;G15qG'1%@G%Gq'1'?13JQ#8P7PXP`P\P7p-0R\%KdRd#K,A71A7dRd9Q7a1A7cRc/6<'6R`'6#EAQ7ac/6<R<,6f,6d#E16d<#E%E`/9h'9'9'9P@PgPePi1]i==>ik=OilPBPi1a7QRl9N7:Rk,Vj,0i1<2k,0i5>i1Ikj,0i1]i>5>i5OiPBPi1Ij:,0iPBAN71l/<2,0iCBCBCBPCPmb4b5b6X07X17X27X;\W<118n/?o138QRo#;159o'1%@o/1='?%H015o0[[[^07^17^27^;\^<\P4%G8%;HPHP8P6P9P0P>O8b3b>b:b=b9C^1P8D,CE=JFR,7F,:V/2?en0110000020101bAPAP7PTP3PQn0100000020000,3L#4,2Seb@%d6RSPhP@1g76PePi1Ij1,0iRiPBPiCBPCPmb4b5b6X07PU\;^07P4P9P6O2b3,v6EUPOA\FKMEUAuFNP,7FAtFNPEU%c6,7F%4SRS'2eA\FISn01100000201001s96,7F/2SeW?X77WBo"). Qed.

(* [comment removed for export] *)
Definition asec_chunk (m : amem) (ch : achunk) (idx : Z) (lv : bool) : Prop :=
  match ch with
  | CSec mb ms n =>
      let res := mb + 4096 in let ub := mb + SEC_UOFF in
         rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)]
      /\ junk_at m (mb + 32) (4096 - 32)
      /\ rw_cells asegs m res [C8 (Z_to_bv 64 SEC_MAGIC); C8 (Z_to_bv 64 (ub - 16))]
      /\ junk_at m (res + 16) (2048 - 32)
      /\ (exists b1 ctx, rw_cells asegs m (ub - 16) [C1 (Z_to_bv 8 (if lv then 2 else 3)); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0);
                                                 C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
                        /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31)
      /\ junk_at m ub (ms - SEC_UOFF)
      /\ fill_at m (shad mb) 768 0xfa
      /\ rw_cells asegs m (shad ub) [CB (Z.to_nat (granules n)) (sec_user_shadow lv n)]
      /\ fill_at m (shad ub + granules n) (ms / 8 - 768 - granules n) 0xfa
  | CPrim _ _ => False
  end.

(* [comment removed for export] *)
Definition asec_arr (L : alayout) (st : astate) (cs : list achunk) (m : amem) : Prop :=
  exists order : list achunk,
       Permutation order cs
    /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
    /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
    /\ (forall i ch, nth_error order i = Some ch ->
          exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat i) lv).

(* [comment removed for export] *)
Definition asec_inst (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xb4368 [C8 (Z_to_bv 64 (al_ptr_array L))]        (* [comment removed for export] *)
  /\ (exists srt : byte, rw_cells asegs m 0xb4398 [C1 srt])              (* [comment removed for export] *)
  /\ junk_at m 0xb43a0 32                                                (* [comment removed for export] *)
  /\ junk_at m 0xb43c0 512                                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb45c1 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ junk_at m 0xb45d8 16.                                               (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition astartup_hulls (L : alayout) : list (Z * Z) :=
  let V := al_V L in
  [(4096 * V 584%nat, 4096 * V 584%nat + 4096); (4096 * V 503%nat, 4096 * V 503%nat + 4096);
   (al_store L, al_store L + 8388608); (al_nodes L, al_nodes L + 1048576); (al_fake L, al_fake L + 11571200);
   (al_dtls L, al_dtls L + 4096); (4096 * V 258%nat, 4096 * V 258%nat + 4096); (al_ctx L, al_ctx L + 65536);
   (al_t L, al_t L + 4096); (al_res L, al_res L + 137439023104);
   (4096 * V 220%nat, 4096 * V 220%nat + 0x38e000); (4096 * V 91%nat, 4096 * V 91%nat + 0x10000);
   (al_ptr_array L, al_ptr_array L + 8388608)].
(* [comment removed for export] *)
Definition ashz (L : alayout) (cs : list achunk) (m : amem) : Prop :=
  forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
    Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
    Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) cs ->
    m (wa (shad x)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition aprim0 (L : alayout) (m : amem) : Prop := azero m (shad (al_space_beg L)) (shlen K_REGION).

Definition ASECc (cs : list achunk) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  asec_wf L st cs /\ asec_arr L st cs m /\ asec_inst L m /\ aprim0 L m /\ ashz L cs m.

(* [comment removed for export] *)
Definition ASEC_of (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := ASECc (sec_chunks_of st) L st X m.

End CANSEC1.

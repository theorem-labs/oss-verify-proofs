(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocBlocksOL RelocImg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_CanonImgOL () := "c69OSSVerify5KrLib6Common5Reloc:CanonImgOL>rl_cells_ol_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common5Reloc8RelocImg9cell_factC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib6Common5Reloc8RelocImg6ce_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8RelocImg7ce_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8RelocImg4ce_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8RelocImg6ce_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8RelocImg:cell_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C69OSSVerify5KrLib6Common9Leptonica9RelocLept;rl_cell_valC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib6Common5Reloc:CanonImgOL>canon_cells_OLC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib6Common5Reloc:CanonImgOL=lceOL_1e3b0_8C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc8RelocImg5ccell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib6Common5Reloc:CanonImgOL=lceOL_1f420_4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonImgOL=lceOL_1e3e0_8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonImgOL=lceOL_1f430_8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonImgOL=lceOL_1f438_8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2ex01c69OSSVerify5KrLib6Common5Reloc:CanonImgOL=lceOL_2f848_8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonImgOL?lceOL_10a80_132C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonImgOL>rl_spans_ol_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib6Common9Leptonica9RelocLept9span_factC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonImgOL>canon_spans_OLC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition canon_strs_OL : list (positive * Z * Z) := [
  (300%positive, 0x10298, 17); (301%positive, 0x102aa, 11); (302%positive, 0x102b6, 16); (303%positive, 0x102c7, 14);
  (304%positive, 0x102d6, 16); (305%positive, 0x102f1, 36); (306%positive, 0x10316, 14); (307%positive, 0x10325, 15);
  (308%positive, 0x10335, 10); (309%positive, 0x10340, 14); (310%positive, 0x1034f, 47); (311%positive, 0x1037f, 55);
  (312%positive, 0x103b7, 13); (313%positive, 0x103c5, 14); (314%positive, 0x103d4, 14); (315%positive, 0x103e3, 24);
  (316%positive, 0x1040f, 38); (317%positive, 0x10436, 14); (318%positive, 0x10460, 15); (319%positive, 0x10470, 11);
  (320%positive, 0x1047c, 21); (321%positive, 0x104c3, 9); (322%positive, 0x104cd, 18); (323%positive, 0x104e0, 83);
  (324%positive, 0x10534, 15); (325%positive, 0x10544, 30); (326%positive, 0x10567, 10); (327%positive, 0x10572, 26);
  (328%positive, 0x1058d, 10); (329%positive, 0x10598, 13); (330%positive, 0x105a6, 36); (331%positive, 0x105cb, 24);
  (332%positive, 0x105e4, 45); (333%positive, 0x10612, 50); (334%positive, 0x10645, 14); (335%positive, 0x10654, 18);
  (336%positive, 0x10667, 13); (337%positive, 0x10675, 76); (338%positive, 0x106e7, 18); (339%positive, 0x106fa, 34);
  (340%positive, 0x1071d, 17); (341%positive, 0x1072f, 52); (342%positive, 0x10764, 15); (343%positive, 0x10774, 12);
  (344%positive, 0x10781, 57); (345%positive, 0x107bb, 16); (346%positive, 0x107cc, 12); (347%positive, 0x107ee, 23);
  (348%positive, 0x10806, 9); (349%positive, 0x10810, 21); (350%positive, 0x10826, 22); (351%positive, 0x1083d, 46);
  (352%positive, 0x1086c, 17); (353%positive, 0x108aa, 28); (354%positive, 0x108c7, 11); (355%positive, 0x108d3, 21);
  (356%positive, 0x108e9, 28); (357%positive, 0x10906, 46); (358%positive, 0x10935, 13); (359%positive, 0x10947, 51);
  (360%positive, 0x1097f, 36); (361%positive, 0x109d2, 7); (362%positive, 0x109eb, 16); (363%positive, 0x109fc, 21);
  (364%positive, 0x10a12, 19); (365%positive, 0x10a26, 13); (4000%positive, 0x102e7, 9); (4001%positive, 0x103fc, 18);
  (4002%positive, 0x10445, 19); (4003%positive, 0x10459, 3); (4004%positive, 0x1045d, 0); (4005%positive, 0x1045e, 1);
  (4006%positive, 0x10492, 16); (4007%positive, 0x104a3, 31); (4008%positive, 0x10563, 3); (4009%positive, 0x106e4, 3);
  (4010%positive, 0x106e8, 32); (4011%positive, 0x108b7, 20); (4012%positive, 0x108cc, 22); (4013%positive, 0x1097c, 3);
  (4014%positive, 0x109b4, 3); (4015%positive, 0x109eb, 31); (4016%positive, 0x10a13, 16); (4017%positive, 0x10a6d, 9);
  (4018%positive, 0x10a77, 6)].

Definition lceOL_1e3b0_8 : ccell := mkCell 5035%positive 0x1e3b0 8%nat (CV_rl 5013%positive 0x1f420).   (* [comment removed for export] *)
Definition lceOL_1f420_4 : ccell := mkCell 5013%positive 0x1f420 4%nat (CV_lit 3).   (* [comment removed for export] *)
Definition lceOL_1e3e0_8 : ccell := mkCell 5027%positive 0x1e3e0 8%nat (CV_rl 5031%positive 0x2f848).   (* [comment removed for export] *)
Definition lceOL_1f430_8 : ccell := mkCell 5028%positive 0x1f430 8%nat (CV_rl 1036%positive 0x15b3c).   (* [comment removed for export] *)
Definition lceOL_1f438_8 : ccell := mkCell 5028%positive 0x1f438 8%nat (CV_rl 1035%positive 0x15b38).   (* [comment removed for export] *)
Definition lceOL_2f848_8 : ccell := mkCell 5031%positive 0x2f848 8%nat (CV_bytes [0; 0; 0; 0; 0; 0; 0; 0]).   (* [comment removed for export] *)
Definition lceOL_10a80_132 : ccell := mkCell 5018%positive 0x10a80 132%nat (CV_bytes [0; 0; 0; 0; 1; 0; 0; 0; 3; 0; 0; 0; 7; 0; 0; 0; 15; 0; 0; 0; 31; 0; 0; 0; 63; 0; 0; 0; 127; 0; 0; 0; 255; 0; 0; 0; 255; 1; 0; 0; 255; 3; 0; 0; 255; 7; 0; 0; 255; 15; 0; 0; 255; 31; 0; 0; 255; 63; 0; 0; 255; 127; 0; 0; 255; 255; 0; 0; 255; 255; 1; 0; 255; 255; 3; 0; 255; 255; 7; 0; 255; 255; 15; 0; 255; 255; 31; 0; 255; 255; 63; 0; 255; 255; 127; 0; 255; 255; 255; 0; 255; 255; 255; 1; 255; 255; 255; 3; 255; 255; 255; 7; 255; 255; 255; 15; 255; 255; 255; 31; 255; 255; 255; 63; 255; 255; 255; 127; 255; 255; 255; 255]).   (* [comment removed for export] *)

Definition canon_cells_OL : list ccell := [lceOL_1e3b0_8; lceOL_1f420_4; lceOL_1e3e0_8; lceOL_1f430_8; lceOL_1f438_8; lceOL_2f848_8; lceOL_10a80_132].

Definition canon_spans_OL : list (bool * positive * Z * Z) := [(true, 5035%positive, 0x1e3b0, 8); (true, 5013%positive, 0x1f420, 4); (true, 5027%positive, 0x1e3e0, 8); (true, 5028%positive, 0x1f430, 8); (true, 5028%positive, 0x1f438, 8); (true, 5031%positive, 0x2f848, 8); (false, 5018%positive, 0x10a80, 132); (true, 5013%positive, 0x1f428, 8)].

Class RelocImgOL (RL : Reloc) := {
  rl_strs_ol_ok : strs_check canon_strs_OL = true;
  rl_cells_ol_ok : cells_check canon_cells_OL = true;
  rl_spans_ol_ok : RelocLept.spans_check canon_spans_OL = true }.

Section Facts.
Context {RL : Reloc} {RIF : RelocImgOL RL}.
Lemma limgOL_1e3b0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1e3b0 + dA_1e3b0)) 8%nat = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)).
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "h02Hah11Hh27__arithh34__ffh46__sat0h56__sat1h66__sat2h76__sat3h88__varmaph95__with:1lp;2p;1p;3p;6p;4p;7p;5g0000j2dTg001;j1FTg001]j3RTg002;j2HTg002Uj6cTg003Yj10Tg004>j19Tg004\j1CTg005?j1BTg005_j1QTg006^j1MTg007@j1KTg008Aj2<Tg009Aj1bTg00:Cj2>Tg00;=j1ZTg00<<j4ETg00=4j1WTg00>5j3VTg00?:j2=Tg00?\j3:Tg00@6j12Tg00@Uj13Tg00A:j17Tg00AXj2PTg00B`j2OTg00C=j2NTg00D:j2@Tg00Dbj28Tg00E>j24Tg00EZj2?Tg00F7j3ATg00F[j1LTg00G;j1STg00GYj1TTg00H7j1UTg00Hbj2JTg00IEj3ITg00Ihj4DTg00JSj7aTg00K7j2`Tg00KYj2]Tg00LEj3\Tg00Ldj4[Tg00MVj2YTg00N1j5^Tg00O<j6_Tg00OXj7XTf0R0#0#0p=1%30#3p=5%30#0p=6%00#3p=;f1R1g00P<R2g00P[R3P3g00Q;R4P0g00Q[FXp=Gp,2RLR5g00R;R6p,3RIF,d5g00SFR7g00SeR8g00ToR9#FAR967'HEcg00V1R9#0R6#0R:#0R;#9#CR<#BR=#FR>%Q5R?%0;R;#1#9#C%M<UR<%K8,<5%b8'>%Z8R@CE%W89V5@,==3:P=%27#2#2#2#2#2#2#2R7%5:#6R:#;#;#;R@,<5R8%39#5R9#3RA#;#1#1#6#1#1#7RB'>'PP?P<%6:#6#5,<5%09#1#5#6#5#1#1#7'>P7CER91==05:>X:=P01OB8,N7R8P5P7P@PB%76R6%3ARA#7R@'@g00VVR7/86R5147@1?6@R:,87[[1476R<g00W4R?AA6@1UW0147:\?^0<%7;R@,@6147@1?6@RC,87[\5AA6@1V?X0<147C\?^0<g00WPR<#L%B<g00X<R<#S%T<%U<R?P2P3P3P4P<1J<6R6%9;5I<g00XZ1J<BR;CD,G?P<P;g00YA%9A9I<6CD,G?Fa1`?4P0f2R?g00YhR4g00ZHR6'H1]0?=:46dA\<71C[b3b8b914CB18B:'YP0b2b4b5b6b7D^E_1==89:>9P0b1b1o"). Qed.
Lemma limgOL_1f420_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f420 + dA_1f3f8)) 4%nat = Some (Z_to_le_bytes 4 3).
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;3p;6g0000j25Tg00@6j14Tg001;j10Tg001]j31Tg002;j23Tg002Uj62Tp,2RLR0g00R;R1p,3RIF,50g00SF#4R0g00Zhg00ToR2#0A1210'3E2o"). Qed.
Lemma limgOL_1e3e0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1e3e0 + dA_1e3b8)) 8%nat = Some (Z_to_le_bytes 8 (0x2f848 + dA_2f848)).
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "h02Hah11Hh27__arithh34__ffh46__sat0h56__sat1h66__sat2h76__sat3h88__varmaph95__with:1lp;2p;1p;3p;6p;4p;7p;5g0000j2bTg00@6j14Tg001;j1=Tg001]j3LTg002;j2ETg002Uj6WTg003Yj10Tg004>j19Tg004\j1ATg005?j1?Tg005_j1KTg006^j1ITg007@j1aTg008Aj2<Tg009Aj1XTg00:Cj2;Tg00;=j1UTg00<<j4CTg00=4j1TTg00>5j3STg00?:j2:Tg00?\j38Tg00@Uj11Tg00A:j16Tg00AXj2OTg00B`j2NTg00C=j2MTg00D:j2>Tg00Dbj27Tg00E>j25Tg00EZj2@Tg00F7j3FTg00F[j1JTg00G;j1PTg00GYj1QTg00H7j1RTg00Hbj2BTg00IEj3DTg00Ihj4HTg00JSj7`Tg00K7j2_Tg00KYj2^Tg00LEj3\Tg00Ldj4YTg00MVj2ZTg00N1j5[Tg00O<j6VTg00OXj7]Tf0R0#0#0p=3%10#1p=2f1R1g00P<R2g00P[R3P3g00Q;R4P0g00Q[F]p=Gp,2RLR5g00R;R6p,3RIF,b5g00SF#4#4R7g00\2R8g00ToR9#=AL967'EEWg00V1R9#0R6#0R:#0R;#9#AR<#?R=#=R>%K5R?%0;R;#3#9#A%I<UR<%a8,<5%X8';%U8R@CC%T89S5@,:=38P=%47#4#4#4#4#4R7%1:#2#0#1#3R:#1#2R@,<5R8%16#2#2#3#3#1#3#1#0#3#6RA';'OP?P<%0:#2,<5%19#2R9#0#3#1#2#2#0#3#3#6';P7CCR:1:=058>X:=P01NA8,M7R8P5P7P@PA%66R6%29R9#6R@'>g00VVR7/76R5157@1@6@R<,77[[1576R?g00W4RBAF6@1UW0157<\B^0?%6;R@,>6157@1@6@RC,77[\5AF6@1VBX0?157C\B^0?g00WPR?#J%??g00X<R?#P%Q?%R?RBP2P3P3P4P?1B?6R6%9;5D?g00XZ1B?AR;CH,GBP?P;g00YA%999D?6CH,GBF`1_B4P0f2RBg00YhR4g00ZHR6'E1^0B=846dA\?71CYb3b8b915CA17A<'ZP0b2b4b5b6b7D[EV1:=898>:P0b1b1o"). Qed.
Lemma limgOL_1f430_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f430 + dA_1f430)) 8%nat = Some (Z_to_le_bytes 8 (0x15b3c + dF_15b3c)).
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "h02Hah11Hh27__arithh34__ffh46__sat0h56__sat1h66__sat2h76__sat3h88__varmaph95__with:1lp;2p;1p;3p;6p;4p;7p;5g0000j2cTg00@6j12Tg001;j1BTg001]j3MTg002;j2ITg002Uj6XTg003Yj11Tg004>j19Tg004\j1ATg005?j1@Tg005_j1LTg006^j1JTg007@j1bTg008Aj2=Tg009Aj1YTg00:Cj2<Tg00;=j1VTg00<<j4DTg00=4j1UTg00>5j3TTg00?:j2;Tg00?\j38Tg00@Uj13Tg00A:j16Tg00AXj2PTg00B`j2OTg00C=j2NTg00D:j2?Tg00Dbj27Tg00E>j25Tg00EZj2>Tg00F7j3GTg00F[j1KTg00G;j1QTg00GYj1RTg00H7j1STg00Hbj2CTg00IEj3HTg00Ihj4ETg00JSj7aTg00K7j2`Tg00KYj2_Tg00LEj3ZTg00Ldj4[Tg00MVj2\Tg00N1j5WTg00O<j6]Tg00OXj7^Tf0R0#1#1p=0%30#3p=4%30#1p=:f1R1g00P<R2g00P[R3P3g00Q;R4P0g00Q[F^p=Fp,2RLR5g00R;R6p,3RIF,c5g00SF#2#2#2R7g00]<R8g00ToR9#BAM967'IEXg00V1R9#1R6#1R:#1R;#9#AR<#@R=#BR>%L5R?%1;R;#0R@#9#A%J<UR<%b8,=5%Y8'<%V8RACD%U89T5A,;=38P=%27#2#2#2#2R7%4@#0R@,=5RA%:6#3#:#4#0#4#4#0#6R8'<'PP?P<%4:#:#3#0#3#0,=5%49#4R9#1#3#0#0#4#0#0#6'<P7CDR:1;=058>X:=P01O8A,N7RAP5P7P@P8%66R6%39R9#6R@'?g00VVR7/76R5157@1>6@R<,77[[1576R?g00W4RBAG6@1UW0157<\B^0?%6;R@,?6157@1>6@RC,77[\5AG6@1VBX0?157C\B^0?g00WPR?#K%@?g00X<R?#Q%R?%S?RBP2P3P3P4P?1C?6R6%9;5H?g00XZ1C?8R;CE,FBP?P;g00YA%999H?6CE,FBFa1`B4P0f2RBg00YhR4g00ZHR6'I1_0B=846dAZ?71C[b3b8b915C8178<'\P0b2b4b5b6b7DWE]1;=A98>:P0b1b1o"). Qed.
Lemma limgOL_1f438_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f438 + dA_1f430)) 8%nat = Some (Z_to_le_bytes 8 (0x15b38 + dF_15b38)).
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "h02Hah11Hh27__arithh34__ffh46__sat0h56__sat1h66__sat2h76__sat3h88__varmaph95__with:1lp;2p;1p;3p;6p;4p;7p;5g0000j2dTg00@6j10Tg001;j1?Tg001]j3NTg002;j2JTg002Uj6YTg003Yj11Tg004>j19Tg004\j1CTg005?j1BTg005_j1MTg006^j1KTg007@j1cTg008Aj2<Tg009Aj1]Tg00:Cj2>Tg00;=j1WTg00<<j4DTg00=4j1VTg00>5j3UTg00?:j2=Tg00?\j38Tg00@Uj15Tg00A:j17Tg00AXj2QTg00B`j2PTg00C=j2OTg00D:j2ATg00Dbj2:Tg00E>j24Tg00EZj2@Tg00F7j3HTg00F[j1LTg00G;j1RTg00GYj1STg00H7j1TTg00Hbj2ITg00IEj3ETg00Ihj4FTg00JSj7bTg00K7j2aTg00KYj2\Tg00LEj3ZTg00Ldj4[Tg00MVj2XTg00N1j5^Tg00O<j6_Tg00OXj7`Tf0R0#1#1p=2%50#1p=6%50#5p=3%10#5p=;f1R1g00P<R2g00P[R3P3g00Q;R4P0g00Q[F`p=Gp,2RLR5g00R;R6p,3RIF,d5g00SF#0#0#0#0R7g00^FR8g00ToR9#?AN967'JEYg00V1R9#1R6#1R:#1R;#9#CR<#BR=#?R>%M5R?%1;R;#2R@#9#C%K<UR<%c8,<5%]8'>%W8RACD%V89U5A,==38P=%07#0#0#0R7%6@#3R@,<5RA%56#;#6#3#2#3#6#2#7R8'>'QP?P<%3:#6#6#;#2,<5%39#3R9#;#2#2#3#6#2#7'>P7CDR:1==058>X:=P01P8A,O7RAP5P7P@P8%76R6%59R9#7R@'Ag00VVR7/:6R5147@1@6@R<,:7[[1476R?g00W4RBAH6@1UW0147<\B^0?%7;R@,A6147@1@6@RC,:7[\5AH6@1VBX0?147C\B^0?g00WPR?#L%B?g00X<R?#R%S?%T?RBP2P3P3P4P?1I?6R6%9;5E?g00XZ1I?8R;CF,GBP?P;g00YA%999E?6CF,GBFb1aB4P0f2RBg00YhR4g00ZHR6'J1\0B=846dAZ?71C[b3b8b914C81:8<'XP0b2b4b5b6b7D^E_1==A98>:P0b1b1o"). Qed.
Lemma limgOL_2f848_8 : exists T, rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x2f848 + dA_2f848)) 8%nat = Some T.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "h01Tp;1p;2p;4p;3p;6g003Yj11Tg004>j16Tg004\j15Tg005?j1;Tg001;j17Tg005_j1GTg006^j1>Tg00@Uj10Tg00A:j1:Tg008Aj28Tg00B`j29Tg00_Pj2ITg00@6j12Tg00<<j4HTg00?:j2FTg00?\j3ETg00;=j1BTg00=4j1?Tg00>5j3@Tg0000j2ATg001]j3=Tg002;j2CTg002Uj6DTg00`6j4<Tf0R0#1#1p=3%00#0p=4g00V1#1R1#1R2#1R3#6#5R4#;R5%75p,2RLR6#G%13#3#6R3#5%>4U%01#4#4#3#3#0#3#0#1#3#:%02#4#1#0#3#0#4,86'9,I3g00SF#2#2#2#2#2R3#2#2#2CH1F503EX05g00`PR5#B%?55@6P6g00R;R0p,3RIF,A6P3P5g00ToR5#7A=503'CEDC<o"). Qed.
Lemma limgOL_10a80_132 : exists T, rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x10a80 + dA_10a80)) 132%nat = Some T.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "h01Tp;1p;2p;4p;3p;6g003Yj11Tg004>j16Tg004\j15Tg005?j1LTg001;j17Tg005_j1FTg006^j1@Tg00@Uj12Tg00A:j1=Tg008Aj2<Tg00B`j2;Tg00_Pj2:Tg00<<j4JTg00?:j2ITg00?\j3ETg00;=j1BTg00=4j1ATg00>5j3?Tg0000j2CTg001]j3DTg002;j2>Tg002Uj6GTg00`6j4HTg00@6j10Tf0R0#1#1p=4%00#0p=9%00#0#0#0p=8%00#0#0#0#0#0#0#0p=K%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3g00V1#4R1#1R2#6#5R3#LR4%74p,2RLR5#F%12R2#4#6R6#5%@3U%22#1#2#1#2#1#4#4#4#=%21#2#2#4#2#2#1#2#1,<5';,:6g00SF#9#8R6#9#8#K#3#3#3#3#3#3#3CJ1I403EX04g00aZR4#B%A45?5P5g00R;R0p,3RIF,C5P6P4g00ToR4#7AD406'>EGCHo"). Qed.
Lemma lspanOL_1e3b0 : rl_rw_lo <= 0x1e3b0 + dA_1e3b0 /\ 0x1e3b0 + dA_1e3b0 + 8 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2:Tg00d1j23Tg003Yj10Tg00@Uj11Tg00dQj44Tg00A:j15Tg001;j19Tg001]j38Tg002;j27Tg00e1j66Tf0#1#1p=2p,2RLR0g00f:R1p,3RIF,:0g00SFR0g00YhR2g00gER3'3R4g00X<R5'3R6P5P4P5P2P3g00ZHg00V1R3#0#0R2#1#2#0#1#0#1#0#2C4%13#2#0#0#0#1#2#0#2#0#0#0#0#5C4%02#5C41365R6#9A8610'7E6o"). Qed.
Lemma lspanOL_1f420 : rl_rw_lo <= 0x1f420 + dA_1f3f8 /\ 0x1f420 + dA_1f3f8 + 4 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2;Tg00@6j1:Tg00d1j23Tg00@Uj10Tg003Yj12Tg00dQj44Tg00A:j15Tg001;j18Tg001]j37Tg002;j26Tg00e1j69Tf0#2#2p=1p,2RLR0g00f:R1p,3RIF,;0g00SF#:R0g00YhR2g00gER3'3R4g00X<R5'3R6P5P4P5P2P3g00ZHg00V1R3#1R2#0#0#0#1#0#2#0#2#0C4%03#0#0#0#2#0#1#1#0#2#1#1#5C4%52C41365R6#8A7610'6E9o"). Qed.
Lemma lspanOL_1e3e0 : rl_rw_lo <= 0x1e3e0 + dA_1e3b8 /\ 0x1e3e0 + dA_1e3b8 + 8 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2<Tg00@6j17Tg00d1j24Tg00@Uj11Tg003Yj10Tg00dQj45Tg00A:j16Tg001;j1;Tg001]j38Tg002;j29Tg00e1j6:Tf0R0#0#0p=2%10#1p=3p,2RLR0g00f:R1p,3RIF,<0g00SF#7#7R0g00YhR2g00gER3'4R4g00X<R5'4R6P5P4P5P2P3g00ZHg00V1R3#2R2#1#3#0#1#0#2#3C5%13#3#0#2#1#3#3#0#2#2#6C5%02#6C51465R6#;A8610'9E:o"). Qed.
Lemma lspanOL_1f430 : rl_rw_lo <= 0x1f430 + dA_1f430 /\ 0x1f430 + dA_1f430 + 8 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2;Tg00@6j15Tg00d1j23Tg00@Uj10Tg003Yj12Tg00dQj44Tg00A:j16Tg001;j1:Tg001]j39Tg002;j27Tg00e1j68Tf0#2#2p=1p,2RLR0g00f:R1p,3RIF,;0g00SF#5#5#5R0g00YhR2g00gER3'3R4g00X<R5'3R6P5P4P5P2P3g00ZHg00V1R3#1R2#0#0#0#2#0#1#0#1C4%03#0#0#0#2#0#1#1#0#0#1#1#6C4%22#6C41365R6#:A9610'7E8o"). Qed.
Lemma lspanOL_1f438 : rl_rw_lo <= 0x1f438 + dA_1f430 /\ 0x1f438 + dA_1f430 + 8 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2;Tg00@6j13Tg00d1j24Tg00@Uj10Tg003Yj11Tg00dQj45Tg00A:j16Tg001;j1:Tg001]j39Tg002;j27Tg00e1j68Tf0#1#1p=2p,2RLR0g00f:R1p,3RIF,;0g00SF#3#3#3#3R0g00YhR2g00gER3'4R4g00X<R5'4R6P5P4P5P2P3g00ZHg00V1R3#2R2#0#0#0#1#0#2#0#2C5%03#0#0#0#1#0#2#2#0#0#0#1#2#6C5%12#6C51465R6#:A9610'7E8o"). Qed.
Lemma lspanOL_2f848 : rl_rw_lo <= 0x2f848 + dA_2f848 /\ 0x2f848 + dA_2f848 + 8 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2;Tg00@6j12Tg00d1j24Tg003Yj10Tg00@Uj11Tg00dQj45Tg00A:j16Tg001;j1:Tg001]j39Tg002;j27Tg00e1j68Tf0#1#1p=3p,2RLR0g00f:R1p,3RIF,;0g00SF#2#2#2#2#2R0g00YhR2g00gER3'4R4g00X<R5'4R6P5P4P5P2P3g00ZHg00V1#0R3#0R2#1#3#0#1#0#0#1#3C5%13#3#3#0#0#0#0#1#0#0#1#0#0#0#6C5%02#6C51465R6#:A9610'7E8o"). Qed.
Lemma lspanOL_10a80 : rl_img_lo <= 0x10a80 + dA_10a80 /\ 0x10a80 + dA_10a80 + 132 <= rl_rw_lo.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2;Tg00@6j13Tg00d1j24Tg00@Uj10Tg003Yj11Tg00dQj45Tg00A:j16Tg001;j1:Tg001]j39Tg002;j27Tg00e1j68Tf0#1#1p=2p,2RLR0g00f:R1p,3RIF,;0g00SF#3#3#3#3#3#3R0g00YhR2g00gER3'4R4g00X<R5'4R6P5P4P5P2P3g00gjg00V1#2R3#0#0#0#2#0#0#1#0#1C5%23#0#1R3#0#1#0#1#2#2#2#6C5%13#6C51465R6#:A9610'7E8o"). Qed.
Lemma lspanOL_1f428 : rl_rw_lo <= 0x1f428 + dA_1f3f8 /\ 0x1f428 + dA_1f3f8 + 8 <= rl_img_hi.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonImgOL ()) ["Facts"] "p;2p;1p;4p;3p;6g00bfj2:Tg00@6j12Tg00d1j23Tg003Yj10Tg00@Uj11Tg00dQj44Tg00A:j15Tg001;j19Tg001]j38Tg002;j27Tg00e1j66Tp,2RLR0g00f:R1p,3RIF,:0g00SF#2#2#2#2#2#2#2R0g00YhR2g00gER3'3R4g00X<R5'3R6P5P4P5P2P3g00ZHg00V1R3#0#0R2#1#1#1#0#0#1#0#1#0#1C4%13#1#1#1#0#1#0#0#0#0#1#0#1#0#0#0#5C4%02#5C41365R6#9A8610'7E6o"). Qed.
End Facts.

(* [comment removed for export] *)
Ltac rl_lay_OL :=
  rl_lay;
  (let h := fresh "Hspan" in pose proof lspanOL_1e3b0 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f420 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1e3e0 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f430 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f438 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_2f848 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_10a80 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f428 as h).

(* [comment removed for export] *)
Ltac rl_str_far_OL a :=
  lazymatch a with
  | (?c + @rl_delta ?RL ?b)%Z =>
      let h := fresh "Hfar" in pose proof (@str_far_fact RL canon_strs_OL rl_strs_ol_ok b c (@eq_refl bool true)) as h
  end.
Ltac rl_str_tac_OL :=
  lazymatch goal with
  | |- _ (?c + @rl_delta ?RL ?b) ?k => exact (@str_fact RL canon_strs_OL rl_strs_ol_ok b c k (@eq_refl bool true))
  end.
Ltac rl_limg_OL :=
  lazymatch goal with
  | |- context [rdn _ _ (Z_to_bv 64 (0x1e3b0 + _)) 8%nat] => exact limgOL_1e3b0_8
  | |- context [rdn _ _ (rl _ 0x1e3b0) 8%nat] => exact limgOL_1e3b0_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f420 + _)) 4%nat] => exact limgOL_1f420_4
  | |- context [rdn _ _ (rl _ 0x1f420) 4%nat] => exact limgOL_1f420_4
  | |- context [rdn _ _ (Z_to_bv 64 (0x1e3e0 + _)) 8%nat] => exact limgOL_1e3e0_8
  | |- context [rdn _ _ (rl _ 0x1e3e0) 8%nat] => exact limgOL_1e3e0_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f430 + _)) 8%nat] => exact limgOL_1f430_8
  | |- context [rdn _ _ (rl _ 0x1f430) 8%nat] => exact limgOL_1f430_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f438 + _)) 8%nat] => exact limgOL_1f438_8
  | |- context [rdn _ _ (rl _ 0x1f438) 8%nat] => exact limgOL_1f438_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x2f848 + _)) 8%nat] => exact limgOL_2f848_8
  | |- context [rdn _ _ (rl _ 0x2f848) 8%nat] => exact limgOL_2f848_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x10a80 + _)) 132%nat] => exact limgOL_10a80_132
  | |- context [rdn _ _ (rl _ 0x10a80) 132%nat] => exact limgOL_10a80_132
  | _ => fail "rl_limg_OL: no family cell fact for this read"
  end.

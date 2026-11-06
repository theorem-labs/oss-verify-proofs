(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStep PmStepAB0 PmStepB2 PmCertKitG XIcptAs0B0 PmBIss1 PmBRd1 PmBRdStmts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan Require Import XIcptAB0 XIcptAs0KitB0 L5CoreBB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBRdKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBRdStmts.PMBRS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "1None"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0FF"; "0HI"; "0Kc"]; ["0L"; "0LB"; "0LK"; "4Model"; "4event"; "5bvmap"; "0M"; "0MV"; "0Ma"; "0Mb"; "0Ra"; "0Rb"; "6mrestrict"; "7credit"; "7regs_preserved"; "8aclient"]; ["8acredit_ok"; "8adebit"; "8ahid"; "8fframe"; "8hl_tp"; "8model_rt"; "8ri_inv"; "8vml"; "8vml_of"; ":defined"; ":img_clear"; ":u32_at"; ":u64_at"; ":u8_at"; ":writable"; "9SCFG"]; [";zeros_at"; "<cost"; "=pa_classic_imp"; "=pa_vp_nullbuf"; "=pa_vp_nullis"; "=pa_vp_nullis_ios"; "=pa_vp_parser"; ">ADDR_B"; "?CHUNK"; "?MAX_DEPTH"; "?MAX_ITEMS"; "?parser_at"; "?ps_root"; "?pstate"; "?vec_at"; "?zeros_at"]; ["@accA"; "@annA"; "@aobjA"; "@cfg"; "@cr0"; "@credit_keep"; "@credit_le"; "@frame_okA"; "@parser_init"; "AFPState"; "Agetr"; "Bsrealizes"; "Camodel_ok"; "Caobj"; "Castk"; "Ddk"]; ["Dek"; "Eloaded_segments"; "0SCFG_P"; "Fadd"; "Fdiv"; "Fle"; "Flt"; "Fmodulo"; "Fof_nat"; "Fpow"; "Fsub"; "0V"; "0a"; "0ar"; "0b"; "0cr"]; ["0d"; "0fb"; "0fr"; "0fx0"; "0l"; "0model"; "0modela"; "0modelb"; "0n"; "0o"; "0ois"; "0op"; "0q"; "0ra"; "0sp"; "GZ_to_bv"]; ["Gbv"; "0sz"; "0v"; "0x"; "0y"]]).
Module PMBRDK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma frame_aobj : ltac2:(TCodec.tc2 tcn__PmBRdKit "L'3&Q3%211'<&R7r4r3%3221&RE&RC+Q0%2261%4216%4287r5+oH%7221%9241&R2r7%2316?p041p0:1p0@1pVBE1pUJF1pV4G1pLI1").
Proof. intros FF fb a n. intros ((rs & Hfb) & FB8) H1 H2. exists (fb, 4, rs). split; [exact Hfb| cbn; change (ff_bytes 4) with 1024; lia]. Qed.
Lemma fb16 : ltac2:(TCodec.tc2 tcn__PmBRdKit "A'3&Q3%211'<&R7r2r1%3221'9&RG+@%2261z%53:21p071pV4<1pL>1").
Proof. intros FF fb. intros ((rs & Hfb) & FB8). apply Z.mod_divide; [lia|]. apply (Z.divide_trans 16 1024 fb); [exists 64; reflexivity| apply Z.mod_divide; [lia| exact FB8]]. Qed.
Lemma vfacts : ltac2:(TCodec.tc2 tcn__PmBRdKit "U5'3'7'<%2211%411&Q3%611&M'S@yR0%211'5y8%511%311p051'C&Q6v>r9r8r7r6r5r4&Q8r3%211%;8:9876541&R7r2%22<1&R>vRM+hP0%342=;1&R0&RC+^@%22?1+\0%53D21+S0%62D1+X@%93I21+m0%:2I1+Q0%=3N21&Q9r:%?2O>%3321=&L&Q2r<%2216r;%5221'8&Q>&RAr1&RJ+TP0%22?1%645412&Q:+QUdP0+QVhP0%33821&Q<+QWbaH+QoooPP0%34=<21&Q;+QWbb0+1%34A@21&Q@&RD%Q=2QOQ<+[@%D221+8%5221%QB21=+Q2%93J21%QE28QD%:216%QG21B+4%>3O21%Q24Q1Q0=QG%?2>;%QL21G+Q@%C3Q421+RPPSgX@+R0%F3Q721+RPPShoI%H3Q91QH&RE+Vb\P0%R62RHR1%3221+QP0%R92RK1%R:21Q>%R;21R>%821QN';+QoonlP0+`PPPPPTP0%R@221%=21;+n0%RC2S51%@216%8241'9&RG+@%22S;1z%53SN21&RI+2+Q?%3221%L2G1%R:261%R;2=1%R<2G1%R=2M1%R>2Q21%R?2Q51%R@2Q91%RA2Q>1%RB2Q@1%RC2QF1%RD2R11%RE2R61%RF2R;1%RG2R@1tQ@T5RI1p0S01p0S51p0S:1p0S?1p0SF1p0SK1p0SO1pV4TJ1pVNTK1pV<T>1pQ>T@1p2TL1pV0TJ1pQ6TL1pLTM1pQ4U01").
Proof. intros LB FF LK cr Aw M model sp fb.
intros HH FOK ASTK ACC ACCI ACCO ODEF MV.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (fb16 FF fb FOK) as F16. destruct FOK as ((rs & Hfb) & FB8).
assert (FOK : PMSPA.frame_okA FF fb) by (split; [exists rs; exact Hfb| exact FB8]).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn in F1, F2. change (ff_bytes 4) with 1024 in F2.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *.
assert (AOP : PMSPA.aobjA FF (fb + 464) 384) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
assert (AOO : PMSPA.aobjA FF (fb + 928) 32) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
assert (O8 : (fb + 464) mod 8 = 0) by lia. assert (OIS8 : (fb + 96) mod 8 = 0) by lia. assert (OO8 : (fb + 928) mod 8 = 0) by lia.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 464) 384 sp 24576 HH (PMKB.aobj_of_aobjA FF _ _ AOP O8) ltac:(lia) ltac:(reflexivity))
as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 32) 984 sp 24576 HH
(PMKB.aobj_of_aobjA FF _ _ (frame_aobj FF fb (fb + 32) 984 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity))
as (FR & FBIG & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
split. { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M sp 24576); [exact ASTK| lia| lia| lia]. }
split; [apply L5A.img_clear_mrestrict; exact GOT|].
split; [apply (proj2 (L5A.u64_at_vis H M 1296952 2147450880 (VIMG 1296952 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
split; [apply (proj2 (L5A.u32_at_vis H M 1296960 1 (VIMG 1296960 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
split. { replace (fb + 464 - 368) with (fb + 96) by lia.
exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 96) 272 HH AOIS OIS8 ltac:(lia) ltac:(reflexivity) ACCI). }
split. { replace (fb + 464 + 464) with (fb + 928) by lia.
exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 928) 32 HH AOO OO8 ltac:(lia) ltac:(reflexivity) ACCO). }
split. { apply (proj2 (L5A.writable_vis H M (fb + 464) 384 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
split; [exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 464) 384 HH AOP O8 ltac:(lia) ltac:(reflexivity) ACC)|].
split. { pose proof (PMBRD1.img_sh_vis L ar C IL HI LY ICok ILY LB FF LK cr Aw M model 0x12e880 512 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
split. { pose proof (PMBRD1.img_sh_vis L ar C IL HI LY ICok ILY LB FF LK cr Aw M model 0x131fc8 256 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact F16| lia].
Qed.
Lemma svis : ltac2:(TCodec.tc2 tcn__PmBRdKit "R2'3'7'<%2211%411&Q3%611&M'S@yR0%211'5y8%511%311p051'C&Q6v>r:r9r8r7r6r5&Q8r4%211%;8:9876541&R>vRM+hP0%342961&RE&RJ+TP0%22<1%421;&RC+8%22@1%821B&Q<&RA%241HED&L&Q2r;%221L%421N%8471LKp071p0;1p0@1p0F1p0K1pW6QF1pUJQG1pVNQH1pV<Q;1pQ>Q=1p2QI1pV0QG1pQ6QI1pLQJ1pQ4QM1").
Proof. intros LB FF LK cr Aw M model sp a v.
intros HH ASTK H1 H2 X. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & _).
apply (proj2 (L5A.u64_at_vis _ M a v (VIS a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X.
Qed.
Lemma fvis : ltac2:(TCodec.tc2 tcn__PmBRdKit "R1'3'7'<%2211%411&Q3%611&M'S@yR0%211'5y8%511%311p051'C&Q6v>r:r9r8r7r6r5&Q8r4%211%;8:9876541&R7%12;4&RE&RC+Q0%22:1%4219+8%52=1+oH%72@1%9231&Q<&RA%241GDC&L&Q2r;%221K%421M%8471KJp071p0;1p0A1p0G1p0J1pW6QE1pUJQF1pV4QG1pV<Q:1pQ>Q<1p2QH1pV0QF1pQ6QH1pLQI1pQ4QL1").
Proof. intros LB FF LK cr Aw M model fb a v.
intros HH FOK H1 H2 X. pose proof (fb16 FF fb FOK) as F16.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 32) 984 0 0 HH
(PMKB.aobj_of_aobjA FF _ _ (frame_aobj FF fb (fb + 32) 984 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity))
as (FR & FBIG & _ & FVIS & _).
apply (proj2 (L5A.u64_at_vis _ M a v ltac:(eapply L5A.avis_sub; [exact FVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X.
Qed.
Lemma amset : ltac2:(TCodec.tc2 tcn__PmBRdKit "XC'3'7'<%2211%411&Q3%611&M'R9&Ey5'S@yR0%211%5241'5y8%611%311p061'C'D%F11!pW821&R=r@r:r9%43321&REzr4%3221&RCr5%2214r;%8221'8&RF%12:6+Q@%=281%5231&Q6v>rErDrCrBrA&Q8%11I%98876543K1&R<%126M&R>vRMr<+hP0%4432;1&R0r=%231=Q6&Q9r>%231A@%Q62Q5D+R`0%Q42G1%Q921;'9&RG&RJrGrF%3221+@%6221%83R>1QA&R:&S?&RHu:%211%42R<1%62Q61r?%QG2=1%82R>1%C3R>41u;%:11%<2RD1%>2Q?1%>2RDR1%I3RD21u<%@11%B2RJ1%D2QF1%D2RJR<%O3RJ21u4%F11%H2S01%J2O1&Q4v@%211%M2S31%Q83S351u1%O11%Q12S91%Q32Q91%Q32S9R2%Q>3S921+2%Q?2R61%QA3SG1RJ%RL2RKR9&RI+R0%2261%RF2R=1%RH251rJu2%Q?11%QA2SI1%QC241rOrN%QM221%QF2SL1%R13SL51rH(4%11SG%311r3%QN21QIrQ2rK%S@221%R12T71%R<3T751&NrQ0%221SG&QOrQ4rM%SI221rL%53SM21r1%T12T01%SH22Q3%SJ221&OrQ>rQ=rQ9rQ8%RM221r2%77QLS?652S41&:rQ1%T:261%T?21O%T<22H%T72Q11%T9231%711%S02U6TB%TG11rQ5%113%S>3U431p061p0?1p0H1pUJUH1%SA2DSF%TN21N%TE2OF%TG221r8%S>2UDH%211(1%11UB%SL3UB31%K11p081pUJV51r7rQ7%U821QD%T:331R6&Q5rQ3%2216rQ<%TI21ArQArQ@rQ?%U78U6321QAQ@UITO'R;&RA&Q?vRB%211&R3%165QFU0R;UFV0%74631Q8p091p0>1p0A1p0E1p0J1p0Q81p0R61p0R=1p0RA1pV@VB1pQDVD1pQHVJ1+^ne8%@6DS4R@1R>RI%F4EB1S;p041p0S01p0S51p0S@1p0SG1p0SK1p0T21p0T<1p0TC1p0TJ1p0U61p0U@1p0UD1p0UF1p0UJ1p0UN1p0V41p0V71p0VB1p0VI1p0VO1p0W41pVLX01pVBX11pV2X21pQ0W=1pV>WB1pQBWD1pQFWJ1pV8X11pW4X81pVDX91pV6X:1pVNX;1p2X:1pV0X81pQ6X:1pLX;1pQ4X>1").
Proof. intros LB FF LK cr Aw sp fr o sz fx0 Ra Ma modela Kc d n ra.
intros AOB Hd Hdn Hn HHa AMa ASTKa ACCa DEFa Hfr Hfr' F16 Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 Ka KC.
pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
assert (U2 : bv_unsigned (getr Ra 2%bv) = sp - fr).
{ rewrite L5K.rl2, Ra2. pose proof ASTKa as (_ & SLO & SHI & SPT & _).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHa) as (_ & _ & FSAPP & FSCEIL & _). unfold app_mem, FS_BYTES in FSAPP, FSCEIL.
apply L5.unsigned_lit. lia. }
assert (OB : 0 <= o /\ o + sz <= 2 ^ 47).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHa) as (_ & WF & FSAPP & _). pose proof AOB as (f & Hf & X1 & X2 & _).
destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. lia. }
unfold PMSPA.cfg. apply (MS fx0 Ra Ma modela LB FF LK cr Aw (o + d) 0 n Kc); clear MS.
- split; [exact HHa|]. split; [exact (proj1 AMa)|]. split; [exact (proj2 AMa)|].
split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [lia|].
split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; exact Hra|].
split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Ma Ma sp 24576 fr 2560 ASTKa (fun x X => X)); [lia| lia| lia| exact F16]. }
split. { intros a Ha. apply ACCa. lia. }
split. { intros i Hi. rewrite U2. apply (L5SAR.obj_client L ar LB FF _ _ o sz (o + d + i) AOB). lia. }
split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Ma o sz DEFa ltac:(lia) ltac:(lia)) as W.
replace (o + d + i) with (o + (d + i)) by lia. apply W; lia. }
split; [exact Ka|]. apply (L5SAR.app_rng_aobj L ar C HI HIok LB FF LK cr Aw Ma _ o sz (o + d) n HHa AOB); lia.
- rewrite L5K.rl11. exact Ra11.
- intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
assert (ZB : PM.zeros_at Mb (o + d) n).
{ intros i Hi. destruct (BYTES i Hi) as (v & Ev & Bv). unfold byte_at in Bv. rewrite Bv. subst v. reflexivity. }
apply (KC Rb Mb modelb); [rewrite <- L5K.rl10; exact Rb10| exact RPb| exact ZB| exact PRES| exact SDEFb| | exact RTb| | exact HHb].
+ intros i Hi. rewrite (ZB i Hi). discriminate.
+ split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMa)| exact MIb].
Qed.
Lemma mset_post : ltac2:(TCodec.tc2 tcn__PmBRdKit "T@'3'7'<%2211%411&Q3%611&M'S@yR0%211'5y8%511%311p051pW862'C&Q6v>r>r=r<r;r:r5&Q8r3%211%;8:9876541&R>vRMr6+hP0%4432:1&R=r?r9r8%43321&REz%221C&RC+R`0%22G1%621=r7%8271%62;2%:21L'8r1%=2<1&RF&RI+2+R0%3221%5271%9271&Ov@rGrF&RJrBrA%3221r2%978Q7762J1&:%M25QB%Q121Q>%O22QC%E2Q@1%I231%611'9&S?r4%22R81%Q>11r@%113%73R731p091p0A1p0L1pUJRG1%I2FQ>%QC21Q7%Q62Q8H%Q:221%?2REI%R;11(1%11RD%D3RD31%L11p071pUJS31&Q9%QL2DR@%23RC1R@&R@rHrC(2(6%14S<S<Q;K(4%11S=%53S>31%99QDRC8QC7RA1R>RN&R?%18QFRE:QE9RCR@S0%RG4RFS1:RD%R3221%R4251p0@1p0D1p0Q11p0R91p0R<1p0R?1p0RD1p0RH1p0RN1p0S41pVBT01pV2T11pV>SC1pQDSE1pQBSG1pW4T51pVDT61pV6T71pVNT81p2T71pV0T51pQ6T71pLT81pQ4T;1").
Proof. intros LB FF LK cr Aw sp fr o sz Ma Mb modela d n.
intros HH ASTK AOB Hfr Hfr' Hd Hdn PRES SDEF DEF. pose proof ASTK as (A16 & SLO & SHI & SPT & SD & SUP).
assert (OB : 0 <= o /\ o + sz <= ahl_ceil ar).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _). pose proof AOB as (f & Hf & X1 & X2 & _).
destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. lia. }
split. { apply (L5SAR.ek_mem L ar LB FF sp 24576 (sp - fr) 2560 (fun a => o + d <= a < o + d + n) [(o, sz)] Ma Mb PRES); [lia| lia|].
intros a Hc Ho X. apply (Ho (o, sz)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
split. { apply (L5SAR.dk_mem L ar LB FF sp 24576 (sp - fr) 2560 (fun a => o + d <= a < o + d + n) Ma Mb PRES SDEF); [| | lia| lia].
- intros a Ha. replace a with (o + d + (a - (o + d))) by lia. apply DEF. lia.
- intros a. destruct (L5SAR.rng_dec a (o + d) (o + d + n)) as [X|X]; [left; exact X| right; exact X]. }
apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw Ma Ma Mb _ sp _ (sp - fr) 2560 HH ASTK (fun x X => X)).
- intros a Ha Hs Hns. apply PRES. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
- exact SDEF.
- lia. - lia. - lia.
Qed.
Lemma ri_swap12 : ltac2:(TCodec.tc2 tcn__PmBRdKit "Q>'7'<%2211'3%112&Q3%311&M'S@yR0%211'5y8%511%311p051&Q7&Q6v>(2r9r8r7%43E21%53F41r6r5r4r3r2r1%>8=7654321r:%>3O1<%?3Q0>1%B8A1=:9876p051pUHE1pQ>G1p2Q31pV0Q11pQ6Q31pLQ41pV:Q71pW:Q:1pW8Q;1").
Proof. intros x y l FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
apply (HAJ.aior_perm _ _ _ _ _ HIok _ (y :: x :: l) FF FF LK cr Aw M V HH).
- intros b. cbn [In]. tauto.
- cbn [map] in *. assert (P : y.1 :: x.1 :: map fst l ≡ₚ x.1 :: y.1 :: map fst l) by apply perm_swap. rewrite P. exact ND.
- intros f. tauto.
- rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
Lemma rd_credit : ltac2:(TCodec.tc2 tcn__PmBRdKit "I&M&R6&QAv@vRM%3221r1%6221'8&Q0r2+`P0%33921&Q1%13;43+Q0%73=21&R5%53?43&R4%34:2?1%=251%>2:1p0@1pV0H1").
Proof. intros cr.
unfold PMBRS.cost. intros (C1 & C2). destruct (PMB.ly_cost L C LY) as (K1 & K2 & K3).
unfold PMSPA.scA, PM.credit_add, PM.cost1, PMSPA.HV, LibIfaceAJ.heap_view, PM.CHUNK in *. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *.
unfold acredit_ok, adebit, PMSPA.credit_keep, PMSPA.cr0. cbn [fst snd]. rewrite K1, K2, K3 in *. lia.
Qed.
Lemma parser_init_at : ltac2:(TCodec.tc2 tcn__PmBRdKit "V@'S@yR0%211'5y8%511%311p051'<&Q<&RAr5r4&QF&QG%211%746541&Q9r6+\0%33291&R0r7%23154&Q=r8&RC+8%2261+1%64D521r9+9%7281z%;4I421&Q;r:+<%=281%44N316r;+@%A261%D4Q231:r<+D%E261%<4Q631>r=+Q0%I261&QD%11Q7%Q=4Q<531r>+Q@%O281&QC%11Q=%QC4QB531r?+QH%Q5281&QB%11QC%QI4QH531r@+S@%Q;281&QE%11QI%QO4QN531rA+T@%QA281%Q84R231Q:rB+TD%QE261%Q<4R631Q>rC+TH%QI261%QJ27L%R<4R;421rD+U0%QN271%R@4R?31H&QOrE+U8%R3271+R@%53421rF+X8%R8271%RJ4RI31=rG+X@%R<261%R=2<QM%RO4RN421rH+Y0%RA271%S34S231ArI+Y8%RE261&QH%S84S7421rJ+Y@%RJ271%S<4S;31ArK+YH%RN261%S@4S?31RG'9&RG%12?RB%33SE1RKrM%S>31=?rN%S<31;ArO+Z0%S:241&QI%S24SL421rQ0+Z8%S?271&QJ%T24T1421rQ1+Z@%SD271%SG4T531S=&QN&R1rQ2+[8%SJ281(2'QM&QL(4%113%53431%;8TAT6:97KSI1&RE%12SK;rQ3%T521T<&RI+2+R0%3221%8251&QKrQ5rQ4&R8%12GM%58U0TLTEI43<1p071p0?1p0B1p0O1p0Q41p0Q:1p0Q@1p0QC1p0QF1p0QK1p0R01p0R51p0R;1p0R@1p0RF1p0RK1p0S21p0S71p0S=1p0SB1p0SG1p0SN1p0T51p0T<1p0TC1p0TH1p0TM1p0U31p0U91p0UA1p0UE1p0UJ1pUNV31pVJV41pVFV51pVHV61pQ>V81").
Proof. intros M op ois q b.
intros P0 PD PA P8 P9 P12 P16 P20 P32 P48 P56 P112 P144 P148 P152 P160 P168 P264 P272 P288 P296 P304 P312 Q16 QD QA P320 P328 P336 VEC B0 B1.
assert (PAs : forall a n, op <= a -> a + n <= op + 384 -> PMSPA.accA M a n) by (intros a n H1 H2; unfold PMSPA.accA in *; apply (L5CB.aacc_sub M op 384); [exact PA| lia| lia]).
assert (PDs : forall a n, op <= a -> a + n <= op + 384 -> L5.defined M a n) by (intros a n H1 H2; apply (L5.defined_sub M op 384); [exact PD| lia| lia]).
unfold PM.parser_at, PMSPA.parser_init. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_b PM.p_k PM.p_stk].
split; [exact P0|]. split; [exact PD|]. split; [apply PAs; lia|].
split; [exact P8|]. split; [exact P9|]. split; [exact P12|]. split; [exact P16|]. split; [exact P20|].
split. { unfold PM.nullis_at, PM.iosb_at.
split; [exact P32|]. split; [apply PDs; lia|]. split; [apply PAs; lia|].
split; [replace (op + 32 + 16) with (op + 48) by lia; exact P48|]. split; [replace (op + 32 + 24) with (op + 56) by lia; exact P56|].
split; [replace (op + 32 + 80) with (op + 112) by lia; exact P112|].
split; [replace (op + 32 + 80 + 32) with (op + 144) by lia; exact P144|].
split; [replace (op + 32 + 80 + 36) with (op + 148) by lia; exact P148|].
split; [replace (op + 32 + 80 + 40) with (op + 152) by lia; replace (op + 32 + 16) with (op + 48) by lia; exact P152|].
split; [replace (op + 32 + 80 + 48) with (op + 160) by lia; exact P160|].
split; [replace (op + 32 + 80 + 56) with (op + 168) by lia; exact P168|].
split; [apply PDs; lia|]. split; [apply PAs; lia|]. left; reflexivity. }
split. { unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
split; [replace (op + 24 + 240) with (op + 264) by lia; exact P264|]. split; [replace (op + 24 + 248) with (op + 272) by lia; exact P272|].
split; [apply PDs; lia|].
split; [replace (op + 24 + 264) with (op + 288) by lia; exact P288|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact P296|].
split; [replace (op + 24 + 280) with (op + 304) by lia; exact P304|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact P312|].
split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact Q16|]. split; [exact QD|]. split; [exact QA|].
apply PAs; lia. }
split; [exact P320|]. split; [exact P328|]. split; [apply PAs; lia|].
split. { unfold PM.vstr_at. split; [apply PDs; lia|]. split; [apply PAs; lia|]. split; [lia| exact P336]. }
split; [exact VEC|]. split; [right; reflexivity|]. split; [left; reflexivity|]. unfold PM.MAX_DEPTH; lia.
Qed.
End Kit.
End PMBRDK.

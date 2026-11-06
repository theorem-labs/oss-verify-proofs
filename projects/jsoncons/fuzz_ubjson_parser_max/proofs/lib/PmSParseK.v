(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmParKit2 PmSParseD.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSParseK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecs.PMPS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSParseD.PMSLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3Z"]; ["0HI"; "0K"; "0L"; "0LBX"; "4Model"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "0M3"; "0Ma"; "0Mb"; "0R"; "0R3"]; ["6credit"; "6hi_heap"; "6hl_sptop"; "6model_but_vm"; "7agree_on"; "7hpres"; "7stk"; "9defined"; "9img_clear"; "9range"; "9u64_at"; "9u8_at"; "8SCFG"; ":ADDR_S"; ";PST"; ";SRC"]; [";inv"; ";iss_at"; ";mode_bottom"; ";p_src"; ";parser_at"; ";parser_own"; ";pot_parser"; ";ps_mode"; ";pst"; ";pstate"; ";pstate_at"; ";pstate_ok"; ";srcst"; ";strm"; ";unread"; ";vstr"]; ["<with_src"; "=lmem"; "=lrel"; "=pctx"; ">T3"; ">T4"; ">W_run"; ">W_src"; ">cfg"; ">credit_keep"; ">ec_at"; ">o_is"; ">o_p"; ">pm_scr"; ">run_pre"; ">src_step"]; ["?cs_all"; "?inW"; "@FPState"; "@getr"; "ATSet"; "Bsrealizes"; "Cmem_grows"; "Dloaded_segments"; "0SCFG_P"; "EIn"; "Fadd"; "Fle"; "Flt"; "Fmul"; "Fof_nat"; "Fpow"]; ["Fsub"; "0a"; "0c"; "0cat"; "0cr"; "0cr1"; "0cr2"; "0cr3"; "0crb"; "0de2"; "0dnb"; "0dpb"; "0e"; "0e1"; "0e2"; "0e3"]; ["0eb"; "0fb"; "0fx3"; "0h"; "0i"; "0mob"; "0model"; "0model1"; "0model2"; "0model3"; "0modelb"; "0n"; "0o"; "0p"; "0p1"; "0p2"]; ["0pre"; "0qc2"; "0r"; "0rem2"; "0s"; "0s1"; "0s2"; "0s3"; "0scr'"; "0sm"; "0sm1"; "0sm2"; "0sm3"; "0smb"; "0sp"; "0srcb"]; ["GZ_to_bv"; "Gbv"; "0str"; "0tbb"; "0tgb"; "0top'"; "0topb"; "0v"; "0vbb"; "0vkb"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMSLPK.
Import PMS.
Lemma credit_keep_trans : ltac2:(TCodec.tc2 tcn__PmSParseK "A&Q0&R9r6r5r3r2%544321r8%741654p031p041pX0;1pWN<1pWL=1pV>>1pV<?1pV:@1").
Proof. intros cr cr1 cr2 p p1 p2. unfold PMSP.credit_keep. lia. Qed.
Lemma RUNF2 : ltac2:(TCodec.tc2 tcn__PmSParseK "R8'TAyR0%211'7y8%511%311p051'?'QH'QO'QM'1&R>&RG&Q=r6r5r4r3r2r1%9887654321':&Q:r7&RJ+]@%22<1+el_8%64@521&Q;+Q8%72A1+@%9221z%64G<21&Q7+\0%23?71&Q8+RPP0+fhV@%33C21&QD&R4&R5+]H%G2Q11%58Q4Q343IA1Q1&QA%17Q6Q56K3Q2Q1&RK&QN&QC%11Q7%321Q6%52F1%Q4271%Q52:1%Q62A1%Q72F1%Q82J1%Q92Q21p0Q;1pVJQF1pXDQH1pY6QJ1pX:QL1pW4QN1pQ@R01").
Proof. intros M fb s str sm e.
intros (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA1, IA1, VIS1. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S] in PA1, IA1, VIS1.
split; [exact VIS1|]. split; [destruct PA1 as (_ & _ & _ & _ & _ & _ & X & _); exact X|].
split; [destruct PA1 as (_ & X & _); exact X|].
split; [destruct BASE1 as (X & _); cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in X; exact X|].
split; [exact PA1|]. split; [exact IA1|].
pose proof (PMPK.iss_size_lt RSEGS AD M _ _ _ IA1) as Z.
pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _) & _).
unfold PM.unread. lia.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma ec_agree_gen : ltac2:(TCodec.tc2 tcn__PmSParseK "Q9'TAyR0%211'7y8%511%311p051'?&Q4r5r4r3+@%544321&RKz%2216&RJ%1296&RO+2+R0%3221%9251&R:&RGr8r6%45321CBr7%655413Ep031p091p0A1p0E1pV6L1pY@M1pWJN1pQBQ01pQ@Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma wrun_where : ltac2:(TCodec.tc2 tcn__PmSParseK "R6'?&RA&R6&Q=r2%3221r1%6221'>':&RK&RJr3+8%3221%521;&RL+H%7261%32?1%;251+Q@%;2:1%=21C+QH%>2=1%:2F1%B241+Z0%B2A1%D21J+[8%E2D1%A2M1%I241+[H%I2H1%K21Q1+]8%L2K1%H2Q41%Q0241+_0%Q02O1%Q221Q8+_8%Q32Q21%O2Q;1%Q7241+b@%Q72Q61%Q921Q?+bD%Q:2Q91%Q62QB1%Q>241+hhc0%Q?21QE+lof8%Q;2QG1%QC231%QE261%QF2>1%QG2F1%QH2N1%QI2Q61%QJ2Q>1p0QL1pW:R41pW4R51").
Proof. intros fb i.
intros (r0 & Hin & Hr). unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Lemma lp_lift : ltac2:(TCodec.tc2 tcn__PmSParseK "UC&RD&Fy5'TAyR0%211%5241'7y8%611%311p061'D'4'8'?%2211%411&Q0'QH'QO'QM'1&R3vRHvBv@rKrJrIrHrGrFrErDrCrBrAr@r?r>%BAA@?>=<;:987654321&R2r=r<r;r:r9%6BGFEDCBA@><:9854321&RKzr3%3221&RJr4+T0%3221+QPP0%9221&Q5&S0%12Q06r5&R6&Q=%221Q2%77Q9Q7541ME&R?&QC%11O%21H%4421Q0H';(9%23QDQ31%33QEM2p021&R9&QF%12QFQ;%22QGQ4%44Q:Q221&Q3%12QAQ;&Q1&0&QE%11Q?rQ0%43R921&E%11QD%85R23Q?QF1':rQ4rQ3rQ2rQ1rOrM%QJBR;R:6543<21R9R7R6QOQNQMQLQIQH&Q6&Q2%11R>%341R36Q?%Q=28QBr2%QJ221%QG2QI2+8%QI2F1%QN231&Q4%14RFR@QKQNp031p081pWHS51pV4S61+H%R22E1%R721>+Q@%R52Q21%R:2?1p01;p051pWHS?1pV4S@1+]8%R<2O1%RA21H+]H%R?2Q<1%RD2I1p01Ep051pWHSI1pV4SJ1%Q=2;1%Q>2F1%Q?2Q41%Q@2Q91p0QB1p0QL1p0QO1p0R51p0R;1p0RA1p0RJ1p0S11p0S61p0S>1pXBT91pV>T71pVNT41pXHT61pX>T91pWBTA1pQFTC1pV<T=1pVLT:1pXFT<1pX<T?1pW@TG1pQDTI1pVJT?1pXDTA1pY6TC1pX:TE1pV8TJ1pW4TK1pX6TL1pXNTM1pV:TK1pQ8TM1pW>U31pQ@U51pQNU;1pQ4UB1").
Proof. intros K R M model LBX cr sp r fb cat s str sm e M1 model1 s1 sm1 e1 cr1 M2 model2 s2 sm2 e2 cr2 scr'.
intros CTX (STEP1 & EE1 & HP1 & CK1 & MB1 & HH1 & SL1) S0 S1 HP2 STEP2 EE2 CK2 MB2 HH2.
destruct CTX as (HH & MOK & K0 & ENT & FOK & _). destruct ENT as (_ & _ & _ & _ & _ & STK). destruct FOK as (F1 & F2 & F3).
cbn [pa_frame AD PmLayoutS.ADDR_S] in F2. change (PMSP.pm_scr 10) with 32768 in STK.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (BRX : PMFR.brange L LBX).
{ apply (PMFR.brange_incl L LBX (PM.parser_own s ++ LBX) (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH (incl_refl _))). apply incl_appr. apply incl_refl. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 32768 sp 32768 _ STK HP1); lia).
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 128) scr').
{ apply (PMK.stk_call L M1 sp 32768 (sp - 128) scr' STK1); [lia|lia|lia|]. replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M1 M2 sp 32768 (sp - 128) scr' _ STK1 HP2); lia).
pose proof STK2 as (_ & _ & _ & _ & SD2).
assert (AGx : forall a n, sp - 128 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW (PMSP.W_run AD fb) i) -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LBX (sp - 128) scr' (PMSP.W_run AD fb) M1 M2 (PMK.ek_of_hpres L LBX (sp - 128) scr' _ M1 M2 HP2) STKc S0 a n H1 H2 N). }
assert (AGs : forall a n, sp - 128 <= a -> a + n <= fb + 8 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply AGx; [lia|lia|]. intros i Hi I. apply wrun_where in I. clear - Hi I H1 H2 F1 SLO STOP. lia. }
assert (AGo : forall a n, fb + 24 <= a -> a + n <= fb + 48 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply AGx; [lia|lia|]. intros i Hi I. apply wrun_where in I. clear - Hi I H1 H2 F1 F2 SLO STOP. lia. }
assert (AGv : forall a n, fb + 424 <= a -> a + n <= fb + 440 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply AGx; [lia|lia|]. intros i Hi I. apply wrun_where in I. clear - Hi I H1 H2 F1 F2 SLO STOP. lia. }
split; [|split; [exact STK2| split; [exact AGs| split; [exact AGo| exact AGv]]]].
split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP1 STEP2)|].
split; [intros X; apply EE2, EE1, X|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M M2).
- apply (PMK.ek_trans L LBX sp 32768 _ M M1 M2 (PMK.ek_of_hpres L LBX sp 32768 _ M M1 HP1)).
apply (PMK.ek_callee_in' RSEGS L KL LBX LBX sp 32768 (sp - 128) scr' _ _ M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LBX BRX)|].
intros a I. right. exact I.
- exact SD2.
- apply (PMK.dk_trans L LBX sp 32768 M M1 M2 (PMK.dk_of_hpres L LBX sp 32768 _ M M1 HP1)).
apply (PMK.dk_callee L LBX LBX sp 32768 (sp - 128) scr' _ M1 M2 HP2 (incl_refl _)); lia. }
split; [apply (credit_keep_trans _ _ _ _ _ _ CK1 CK2)|].
split; [apply (L5C.model_but_vm_trans model model1 model2 MB1 MB2)|].
split; [exact HH2|].
unfold PMSLPD.lslots in *.
destruct SL1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
repeat split; (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGs; lia|lia|lia|]); assumption.
Qed.
Lemma lp_headw : ltac2:(TCodec.tc2 tcn__PmSParseK "UN&RD&Fy5'TAyR0%211%5241'7y8%611%311p061'D'4'8'?%2211%411&Q0'QH'QO'QM'1'QL'QI%<11&R3vRHvBv@rOrNrMrLrKrJrIrHrGrFrErDrCrB%BAA@?>=<;:987654321&R1rA(Q>r@r?r>r=r<r;r:r9&0r8(2r7(6%11Q5%43Q631%73Q761%A9@?>=<;:91r6r5r4%GDQ8Q7Q6Q5Q4Q3Q2Q1ONMLKJIF4321&Q@%<3Q>=9%?3Q?@1%I9JHGFEDCB1%411&RF%12Q29':&RKzr1%3221&RL&RO+2+R0%3221%5271%;271&=&RJ&RM+Q0&RN&3%12R6Q;%311%6251%82Q@1r2%F221%;239%D231%J231%?11';&T@r3%22S71%QE11%R812%63S421p081p0I1pW:S21&Q1&QE%QJ3RLQOQG%QM3RMR11%R79R=R<R;R8R6R5R4R31%411rQ0%R13S921&E%11RC%:5RO3R3R11&QJ&RG%241R6NR4&QK%11R8&<&QB&QG%11RC%311%31R@%511%7231%R@3SBRDR=%RC3SCRK1%RM9S7S6S5S4S3S2S1RN1%R811rQ7rQ6rQ5rQ4rQ3rQ2%S7DSHSG654321LSFSESDSCSBROS@8S2S1S0%R9281p0=1p0F1p0I1p0M1p0Q91p0R@1p0RC1p0RI1p0SB1pY<T71pQJTE1pVBT?1pW2T<1pXLT>1pY>T<1pX2T<1pYDTG1pYBTH1pY:TI1pY8TE1pY0TC1pVHTL1pVFTM1pW<TN1pWFU21pQLU41pVJTJ1pXDTL1pY6TN1pX:U01pV8U51pW4U61pX6U71pXNU81pV:U61pQ8U81pW>U>1pQ@U@1pQNUF1pQ4UM1").
Proof. intros K R M model LBX cr sp r fb cat s str sm e Mb modelb mob dnb dpb srcb tbb tgb vbb vkb pre topb smb eb crb Ma top'.
intros CTX LM INVb MG FR HHa PT OK EB.
destruct CTX as (HH & MOK & K0 & ENT & FOK & _ & _ & INCS & _). destruct ENT as (_ & _ & _ & _ & _ & STK). destruct FOK as (F1 & F2 & F3).
cbn [pa_frame AD PmLayoutS.ADDR_S] in F2. change (PMSP.pm_scr 10) with 32768 in STK.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
destruct LM as (RPREb & ECb & STEPb & EEb & HPb & CKb & MBb & HHb & SLb).
destruct RPREb as (PAb & IAb & VISb & VREFb & BASEb & ERRb & TBb).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PAb, IAb, VISb, VREFb. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S] in PAb, IAb, VISb, VREFb.
set (sb := PM.PST mob dnb dpb srcb tbb tgb vbb vkb (pre ++ [topb])) in *.
set (LBb := PM.parser_own sb ++ LBX) in *.
assert (BRb : PMFR.brange L LBb) by (apply (PMFR.brange_of_heap L HI HIok LBb LBb crb Mb _ HHb); apply incl_refl).
assert (NDb : NoDup (map fst LBb)) by exact (PMPK.heap_nodup L HI HIok LBb crb Mb _ HHb).
assert (VINb : In (vbb, 32 * 2 ^ vkb) LBb) by (unfold LBb, sb, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BRb _ _ VINb) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (VIb : forall a, vbb <= a < vbb + 32 * 2 ^ vkb -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
pose proof PAb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVECb & _).
cbn [sb PM.p_b PM.p_k PM.p_stk] in PVECb. pose proof PVECb as (_ & _ & _ & Hkb & Hlenb & _).
rewrite length_app in Hlenb. cbn [length] in Hlenb. rewrite Nat2Z.inj_add in Hlenb. cbn [Z.of_nat Pos.of_succ_nat] in Hlenb.
set (Tb := vbb + 32 * Z.of_nat (length pre)) in *.
assert (TB : 0 <= Tb /\ Tb + 32 <= vbb + 32 * 2 ^ vkb) by (unfold Tb; lia).
assert (AGa : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= Tb \/ Tb + 32 <= a) -> L5C.agree_on Mb Ma a n).
{ intros a n H1 H2 H3 i Hi. apply FR; [clear - H1 H2 Hi; lia| clear - H3 Hi; lia]. }
assert (STKb : L5C.stk (hl_sptop L) Mb sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M Mb sp 32768 sp 32768 _ STK HPb); lia).
assert (EKa : PMK.ek L LBb sp 32768 [(Tb, 32)] Mb Ma).
{ apply (PMK.ek_piece_in RSEGS L KL LBb sp 32768 [(Tb, 32)] Mb Ma (fun a => Tb <= a < Tb + 32) ltac:(intros a Ha N; apply FR; assumption)
STKb (PMFR.brange_hi L LBb BRb)).
intros a Ha. right. apply PMK.inW_here. exact Ha. }
assert (STKa : L5C.stk (hl_sptop L) Ma sp 32768) by (apply (PMK.stk_grows L Mb Ma sp 32768 MG STKb)).
pose proof STKa as (_ & _ & _ & _ & SDa).
split.
{ pose proof INVb as (I1 & I2 & I3 & I4 & I5). cbn [sb PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in I1, I2, I3, I4, I5.
unfold PM.inv. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [exact I1|]. split; [exact I2|]. split; [rewrite length_app in I3 |- *; cbn [length] in I3 |- *; exact I3|].
split; [apply (PMPK2.stack_shape_set_top pre topb top' I4 OK EB)| exact I5]. }
split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S].
split.
{ apply (PMPK2.parser_top_upd RSEGS AD Mb Ma (fb + 40) (fb + 440) sb pre topb top' PAb eq_refl); cbn [sb PM.p_src PM.p_b PM.p_k PM.p_tb].
- lia.
- lia.
- apply AGa; [lia|lia|clear - W4 F1 SLO STOP TB; unfold hl_ceil in *; lia].
- apply PMPK.dkr_grows. exact MG.
- lia.
- clear - W4 STOP. lia.
- apply AGa; [lia|lia|left; unfold Tb; lia].
- apply AGa; [lia|lia|right; unfold Tb; lia].
- apply PMPK.dkr_grows. exact MG.
- exact PT.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG. }
split.
{ apply (PMF.iss_at_agree RSEGS AD Mb Ma (fb + 440) str smb); [lia|lia| apply AGa; [lia|lia|clear - W4 F1 SLO STOP TB; lia]| |exact IAb].
intros c0 n0 q0 Es.
assert (HQ : In (q0, c0) LBX) by (apply INCS; rewrite Es; cbn; left; reflexivity).
assert (HQ' : In (q0, c0) LBb) by (unfold LBb; apply in_or_app; right; exact HQ).
assert (NE : vbb <> q0).
{ apply (PMPK.fst_neq_app (PM.parser_own sb) LBX vbb (32 * 2 ^ vkb) q0 c0 NDb); [unfold sb, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| exact HQ]. }
destruct (PMPK.blocks_apart_heap L HI HIok LBb crb Mb _ vbb (32 * 2 ^ vkb) q0 c0 HHb VINb HQ' NE) as [X|X].
- destruct (BRb _ _ HQ') as (Z0 & _ & _). apply AGa; [lia|pose proof (BRb _ _ HQ') as (_ & _ & Z4); unfold hl_ceil in Z4; clear - Z4 STOP; lia| right; lia].
- destruct (BRb _ _ HQ') as (Z0 & _ & _). apply AGa; [lia|lia| left; lia]. }
split; [apply (L5C.u64_at_agree RSEGS Mb Ma); [apply AGa; [lia|lia|clear - W4 F1 F2 SLO STOP TB; lia]|lia|lia| exact VISb]|].
split; [apply (L5C.u64_at_agree RSEGS Mb Ma); [apply AGa; [lia|lia|clear - W4 F1 F2 SLO STOP TB; lia]|lia|lia| exact VREFb]|].
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBb sp 32768 [(Tb, 32)] Mb Ma EKa); [| | | | exact BASEb].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; apply (VIb a); [lia| clear - Ha; lia]. }
split; [|exact TBb].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBb sp 32768 [(Tb, 32)] Mb Ma EKa); [| | exact ERRb].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha; apply (VIb a); [lia| clear - Ha; lia]. } }
split; [apply (ec_agree_gen Mb Ma); [apply AGa; [lia|lia|clear - W4 F1 SLO STOP TB; lia]|lia|lia| exact ECb]|].
split; [exact STEPb|]. split; [exact EEb|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M Ma).
- apply (PMK.ek_trans L LBX sp 32768 _ M Mb Ma (PMK.ek_of_hpres L LBX sp 32768 _ M Mb HPb)).
apply (PMPK.ek_drop_own L (PM.parser_own sb) LBX sp 32768 (PMSP.W_run AD fb) [(Tb, 32)] Mb Ma EKa).
+ intros B m Hin. assert (HB : In (B, m) LBb) by (unfold LBb; apply in_or_app; left; exact Hin). destruct (BRb B m HB) as (Z0 & Z1 & Z4).
split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
assert (HB' : In (B', m') LBb) by (unfold LBb; apply in_or_app; right; exact Hin').
assert (NE : B <> B') by (apply (PMPK.fst_neq_app (PM.parser_own sb) LBX B m B' m' NDb Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok LBb crb Mb _ B m B' m' HHb HB HB' NE).
+ intros a O. destruct (PMK.rng_dec a vbb (vbb + 32 * 2 ^ vkb)) as [IQ|NQ].
* right. exists vbb, (32 * 2 ^ vkb). split; [unfold sb, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| exact IQ].
* left. intros r0 Hr0 Hin. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply NQ. lia.
- exact SDa.
- apply (PMK.dk_trans L LBX sp 32768 M Mb Ma (PMK.dk_of_hpres L LBX sp 32768 _ M Mb HPb)). apply (PMK.dk_grows L LBX sp 32768 Mb Ma MG). }
split; [exact CKb|]. split; [exact MBb|]. split; [exact HHa|].
unfold PMSLPD.lslots in *.
destruct SLb as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
repeat split; (apply (L5C.u64_at_agree RSEGS Mb Ma); [apply AGa; [lia|lia|clear - W4 SLO STOP TB; lia]|lia|lia|]); assumption.
Qed.
Lemma lp_headw_mem : ltac2:(TCodec.tc2 tcn__PmSParseK "U7&RD&Fy5'TAyR0%211%5241'7y8%611%311p061'D'4'8'?%2211%411&Q0'QH'QO'QM'1'QL'QI%<11&R3vRHvBv@rOrNrMrLrKrJrIrHrGrFrErDrCrB%BAA@?>=<;:987654321&R1rA(Q>r@r?r>r=r<r;r:r9&0r8(2r7(6%11Q5%43Q631%73Q761%A9@?>=<;:91r6r5r4%GDQ8Q7Q6Q5Q4Q3Q2Q1ONMLKJIF4321&RF%12L3':&RKzr1%3221&RL&RO+2+R0%3221%5271%;271&=&RJ&RM+Q0&RN&3%12R1Q5%311%6251%82Q:1r2%F221%;239%D231%J231%?11';&T@r3%22S21%Q>11%R212%63RO21p081p0I1pW:RM1&Q1&QE%QE3RGQIQB%QH3RHQK1%R29R7R6R3R1R0QOQNQM1%411%QK3S31RE&E%11R<%95RI3QKQE1&QJ&RG%241QNMQHrQ4rQ3rQ2rQ1rQ0%R73S7R<R1%RA9RHRGRFRERBR@R?R>1%RDDS5S476543S3S1S0RORNRMRLR8RJ1R<R;R:p091p0=1p0H1p0QO1p0R21p0RK1pY<S@1pQJSN1pVBSH1pW2SE1pXLSG1pY>SE1pX2SE1pYDT01pYBT11pY:T21pY8SN1pY0SL1pVHT51pVFT61pW<T71pWFT;1pQLT=1pVJT31pXDT51pY6T71pX:T91pV8T>1pW4T?1pX6T@1pXNTA1pV:T?1pQ8TA1pW>TG1pQ@TI1pQNTO1pQ4U61").
Proof. intros K R M model LBX cr sp r fb cat s str sm e Mb modelb mob dnb dpb srcb tbb tgb vbb vkb pre topb smb eb crb Ma top'.
intros CTX LM MG FR HHa PT.
destruct CTX as (HH & MOK & K0 & ENT & FOK & _ & _ & INCS & _). destruct ENT as (_ & _ & _ & _ & _ & STK). destruct FOK as (F1 & F2 & F3).
cbn [pa_frame AD PmLayoutS.ADDR_S] in F2. change (PMSP.pm_scr 10) with 32768 in STK.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
destruct LM as (RPREb & ECb & STEPb & EEb & HPb & CKb & MBb & HHb & SLb).
destruct RPREb as (PAb & IAb & VISb & VREFb & BASEb & ERRb & TBb).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PAb, IAb, VISb, VREFb. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S] in PAb, IAb, VISb, VREFb.
set (sb := PM.PST mob dnb dpb srcb tbb tgb vbb vkb (pre ++ [topb])) in *.
set (LBb := PM.parser_own sb ++ LBX) in *.
assert (BRb : PMFR.brange L LBb) by (apply (PMFR.brange_of_heap L HI HIok LBb LBb crb Mb _ HHb); apply incl_refl).
assert (NDb : NoDup (map fst LBb)) by exact (PMPK.heap_nodup L HI HIok LBb crb Mb _ HHb).
assert (VINb : In (vbb, 32 * 2 ^ vkb) LBb) by (unfold LBb, sb, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BRb _ _ VINb) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (VIb : forall a, vbb <= a < vbb + 32 * 2 ^ vkb -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
pose proof PAb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVECb & _).
cbn [sb PM.p_b PM.p_k PM.p_stk] in PVECb. pose proof PVECb as (_ & _ & _ & Hkb & Hlenb & _).
rewrite length_app in Hlenb. cbn [length] in Hlenb. rewrite Nat2Z.inj_add in Hlenb. cbn [Z.of_nat Pos.of_succ_nat] in Hlenb.
set (Tb := vbb + 32 * Z.of_nat (length pre)) in *.
assert (TB : 0 <= Tb /\ Tb + 32 <= vbb + 32 * 2 ^ vkb) by (unfold Tb; lia).
assert (AGa : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= Tb \/ Tb + 32 <= a) -> L5C.agree_on Mb Ma a n).
{ intros a n H1 H2 H3 i Hi. apply FR; [clear - H1 H2 Hi; lia| clear - H3 Hi; lia]. }
assert (STKb : L5C.stk (hl_sptop L) Mb sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M Mb sp 32768 sp 32768 _ STK HPb); lia).
assert (EKa : PMK.ek L LBb sp 32768 [(Tb, 32)] Mb Ma).
{ apply (PMK.ek_piece_in RSEGS L KL LBb sp 32768 [(Tb, 32)] Mb Ma (fun a => Tb <= a < Tb + 32) ltac:(intros a Ha N; apply FR; assumption)
STKb (PMFR.brange_hi L LBb BRb)).
intros a Ha. right. apply PMK.inW_here. exact Ha. }
assert (STKa : L5C.stk (hl_sptop L) Ma sp 32768) by (apply (PMK.stk_grows L Mb Ma sp 32768 MG STKb)).
pose proof STKa as (_ & _ & _ & _ & SDa).
split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S].
split.
{ apply (PMPK2.parser_top_upd RSEGS AD Mb Ma (fb + 40) (fb + 440) sb pre topb top' PAb eq_refl); cbn [sb PM.p_src PM.p_b PM.p_k PM.p_tb].
- lia.
- lia.
- apply AGa; [lia|lia|clear - W4 F1 SLO STOP TB; unfold hl_ceil in *; lia].
- apply PMPK.dkr_grows. exact MG.
- lia.
- clear - W4 STOP. lia.
- apply AGa; [lia|lia|left; unfold Tb; lia].
- apply AGa; [lia|lia|right; unfold Tb; lia].
- apply PMPK.dkr_grows. exact MG.
- exact PT.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG. }
split.
{ apply (PMF.iss_at_agree RSEGS AD Mb Ma (fb + 440) str smb); [lia|lia| apply AGa; [lia|lia|clear - W4 F1 SLO STOP TB; lia]| |exact IAb].
intros c0 n0 q0 Es.
assert (HQ : In (q0, c0) LBX) by (apply INCS; rewrite Es; cbn; left; reflexivity).
assert (HQ' : In (q0, c0) LBb) by (unfold LBb; apply in_or_app; right; exact HQ).
assert (NE : vbb <> q0).
{ apply (PMPK.fst_neq_app (PM.parser_own sb) LBX vbb (32 * 2 ^ vkb) q0 c0 NDb); [unfold sb, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| exact HQ]. }
destruct (PMPK.blocks_apart_heap L HI HIok LBb crb Mb _ vbb (32 * 2 ^ vkb) q0 c0 HHb VINb HQ' NE) as [X|X].
- destruct (BRb _ _ HQ') as (Z0 & _ & _). apply AGa; [lia|pose proof (BRb _ _ HQ') as (_ & _ & Z4); unfold hl_ceil in Z4; clear - Z4 STOP; lia| right; lia].
- destruct (BRb _ _ HQ') as (Z0 & _ & _). apply AGa; [lia|lia| left; lia]. }
split; [apply (L5C.u64_at_agree RSEGS Mb Ma); [apply AGa; [lia|lia|clear - W4 F1 F2 SLO STOP TB; lia]|lia|lia| exact VISb]|].
split; [apply (L5C.u64_at_agree RSEGS Mb Ma); [apply AGa; [lia|lia|clear - W4 F1 F2 SLO STOP TB; lia]|lia|lia| exact VREFb]|].
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBb sp 32768 [(Tb, 32)] Mb Ma EKa); [| | | | exact BASEb].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; apply (VIb a); [lia| clear - Ha; lia]. }
split; [|exact TBb].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBb sp 32768 [(Tb, 32)] Mb Ma EKa); [| | exact ERRb].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha; apply (VIb a); [lia| clear - Ha; lia]. } }
split; [apply (ec_agree_gen Mb Ma); [apply AGa; [lia|lia|clear - W4 F1 SLO STOP TB; lia]|lia|lia| exact ECb]|].
split; [exact STEPb|]. split; [exact EEb|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M Ma).
- apply (PMK.ek_trans L LBX sp 32768 _ M Mb Ma (PMK.ek_of_hpres L LBX sp 32768 _ M Mb HPb)).
apply (PMPK.ek_drop_own L (PM.parser_own sb) LBX sp 32768 (PMSP.W_run AD fb) [(Tb, 32)] Mb Ma EKa).
+ intros B m Hin. assert (HB : In (B, m) LBb) by (unfold LBb; apply in_or_app; left; exact Hin). destruct (BRb B m HB) as (Z0 & Z1 & Z4).
split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
assert (HB' : In (B', m') LBb) by (unfold LBb; apply in_or_app; right; exact Hin').
assert (NE : B <> B') by (apply (PMPK.fst_neq_app (PM.parser_own sb) LBX B m B' m' NDb Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok LBb crb Mb _ B m B' m' HHb HB HB' NE).
+ intros a O. destruct (PMK.rng_dec a vbb (vbb + 32 * 2 ^ vkb)) as [IQ|NQ].
* right. exists vbb, (32 * 2 ^ vkb). split; [unfold sb, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| exact IQ].
* left. intros r0 Hr0 Hin. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply NQ. lia.
- exact SDa.
- apply (PMK.dk_trans L LBX sp 32768 M Mb Ma (PMK.dk_of_hpres L LBX sp 32768 _ M Mb HPb)). apply (PMK.dk_grows L LBX sp 32768 Mb Ma MG). }
split; [exact CKb|]. split; [exact MBb|]. split; [exact HHa|].
unfold PMSLPD.lslots in *.
destruct SLb as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
repeat split; (apply (L5C.u64_at_agree RSEGS Mb Ma); [apply AGa; [lia|lia|clear - W4 SLO STOP TB; lia]|lia|lia|]); assumption.
Qed.
Lemma lp_lift_src : ltac2:(TCodec.tc2 tcn__PmSParseK "U:&RD&Fy5'TAyR0%211%5241'7y8%611%311p061'D'4'8'?%2211%411&Q0'QH'QO'QM'1&R3vRHvBv@rJrIrHrGrFrErDrCrBrAr@r?r>r=%BAA@?>=<;:987654321&R1r<r;r:r9r8%6DGFEDCBA@>=<;:9854321&RKzr3%3221&RJ+\P0&RM+RP0r4%3221%6251+T0%8221+QPP0%>221&Q5&0&QE%11L%33QD1Q9&S0%12Q9:&R=r5%211&Q9&R7&Q=&QC%11Q7%433Q@1(6%117%A3831%C7QJ?=:1Q>Q6&QD&RG&R4&R5&R<%12=QK&R;%12?QM&R0(Q?%13QAQ@Q?%32QI1%<8;D:9QD751&QA%82FR5%27>G=QH1R3QD&R?%H1R1%93QKQJQI%3421R2QI&Q1%Q71R6rN%Q:3RK21&E%11R;%65RD3R8R71':rQ2rQ1rQ0rOrMrK%I3R?R>R;%K2RE1%R>DRORN8765>43RMRLRKRJRIRBRG1R<RDRC%QD26QMr2%R:221%R72R92+Z0%R92D1%R>231&Q4%14S5ROR8R>p031p081pWHSE1pV4SF1%G2>1p0I1p0Q11p0Q61p0Q:1p0QH1p0R=1p0RI1p0RN1p0S61pW8T11pXHSL1pX8T31pVDT41pX4T51pQFT:1pV<T41pVLT11pXFT31pX<T61pW@T>1pQDT@1pVJT61pXDT81pY6T:1pX:T<1pV8TA1pW4TB1pX6TC1pXNTD1pV:TB1pQ8TD1pW>TJ1pQ@TL1pQNU21pQ4U91").
Proof. intros K R M model LBX cr sp r fb cat s str sm e M1 model1 s1 sm1 e1 cr1 M2 qc2 de2 rem2 sm2 h.
intros CTX LM S0 S1 HP2 PA2 IA2 STEP2 HH2.
destruct CTX as (HH & MOK & K0 & ENT & FOK & _ & _ & INCS & _). destruct ENT as (_ & _ & _ & _ & _ & STK). destruct FOK as (F1 & F2 & F3).
cbn [pa_frame AD PmLayoutS.ADDR_S] in F2. change (PMSP.pm_scr 10) with 32768 in STK.
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
destruct LM as (RPRE1 & EC1 & STEP1 & EE1 & HP1 & CK1 & MB1 & HH1 & SL1).
destruct RPRE1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA1, IA1, VIS1, VREF1, PA2, IA2. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S] in PA1, IA1, VIS1, VREF1, PA2, IA2.
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1]. destruct src1 as [qc1 de1 rem1].
cbn [PM.p_src PM.sr_qc] in *.
assert (QC : qc2 = qc1) by (destruct STEP2 as (X & _); exact X). subst qc2.
set (LB1 := PM.parser_own (PM.PST mo1 dn1 dp1 (PM.SRC qc1 de1 rem1) tb1 tg1 vb1 vk1 stk1) ++ LBX) in *.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH1); apply incl_refl).
assert (NDL : NoDup (map fst LB1)) by exact (PMPK.heap_nodup L HI HIok LB1 cr1 M1 _ HH1).
assert (QIN : In (qc1, 16384) LB1) by (unfold LB1, PM.parser_own, PM.src_own; cbn; left; reflexivity).
destruct (BR1 _ _ QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
assert (QI : forall a, qc1 <= a < qc1 + 16384 -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. intros a Ha. clear - Ha Q1. lia. }
set (scr := PMSP.pm_scr h) in *. assert (SCR : scr = 12288 + 2048 * h) by reflexivity.
set (WS := PMSP.W_src AD fb (PM.SRC qc1 de1 rem1) ++ []) in HP2.
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc1 <= a < qc1 + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_src, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app PM.sr_qc] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; lia. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 32768 sp 32768 _ STK HP1); lia).
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 128) scr).
{ apply (PMK.stk_call L M1 sp 32768 (sp - 128) scr STK1); [lia|lia|lia|]. replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (EK2 : PMK.ek L LB1 (sp - 128) scr WS M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (AG2 : forall a n, sp - 128 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WS i) -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB1 (sp - 128) scr WS M1 M2 EK2 STKc ltac:(lia) a n H1 H2 N). }
assert (AGs : forall a n, sp - 128 <= a -> a + n <= fb + 320 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply AG2; [lia|lia|]. intros i Hi I. apply WCs in I. clear - Hi I H1 H2 Q4 SLO STOP. lia. }
assert (AGh : forall a n, fb + 360 <= a -> a + n <= fb + 480 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply AG2; [lia|lia|]. intros i Hi I. apply WCs in I. clear - Hi I H1 H2 Q4 SLO STOP F1. lia. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 32768) by (apply (PMK.stk_after RSEGS L KL LB1 M1 M2 sp 32768 (sp - 128) scr WS STK1 HP2); lia).
pose proof STK2 as (_ & _ & _ & _ & SD2).
split; [|exact AGs].
split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S].
split; [exact PA2|]. split; [exact IA2|].
split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGh; lia|lia|lia| exact VIS1]|].
split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGh; lia|lia|lia| exact VREF1]|].
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (sp - 128) scr WS M1 M2 EK2); [| | | | exact BASE1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCs in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha.
all: destruct I as [I|[I|[I|I]]]; [clear - I Ha SLO F1 STOP; lia ..| apply (QI a I); clear - Ha; lia]. }
split; [|exact TB1].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 (sp - 128) scr WS M1 M2 EK2); [| | exact ERR1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCs in I; cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha.
all: destruct I as [I|[I|[I|I]]]; [clear - I Ha SLO F1 STOP; lia ..| apply (QI a I); clear - Ha; lia]. } }
split; [apply (ec_agree_gen M1 M2); [apply AGs; lia|lia|lia| exact EC1]|].
split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP1 STEP2)|].
split; [exact EE1|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M M2).
- apply (PMK.ek_trans L LBX sp 32768 _ M M1 M2 (PMK.ek_of_hpres L LBX sp 32768 _ M M1 HP1)).
assert (EKs : PMK.ek L LB1 sp 32768 WS M1 M2).
{ apply (PMK.ek_callee_in' RSEGS L KL LB1 LB1 sp 32768 (sp - 128) scr WS WS M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB1 BR1)|].
intros a I. right. exact I. }
apply (PMPK.ek_drop_own L (PM.parser_own (PM.PST mo1 dn1 dp1 (PM.SRC qc1 de1 rem1) tb1 tg1 vb1 vk1 stk1)) LBX sp 32768 (PMSP.W_run AD fb) WS M1 M2 EKs).
+ intros B m Hin. assert (HB : In (B, m) LB1) by (unfold LB1; apply in_or_app; left; exact Hin). destruct (BR1 B m HB) as (Z0 & Z1 & Z4).
split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
assert (HB' : In (B', m') LB1) by (unfold LB1; apply in_or_app; right; exact Hin').
assert (NE : B <> B') by (apply (PMPK.fst_neq_app _ LBX B m B' m' NDL Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok LB1 cr1 M1 _ B m B' m' HH1 HB HB' NE).
+ intros a O. destruct (PMK.rng_dec a qc1 (qc1 + 16384)) as [IQ|NQ].
* right. exists qc1, 16384. split; [unfold PM.parser_own, PM.src_own; cbn; left; reflexivity| exact IQ].
* left. intros r0 Hr0 Hin. assert (I : PMK.inW WS a) by (exists r0; split; assumption). apply WCs in I.
destruct I as [I|[I|[I|I]]]; [| | | exact (NQ I)]; apply (PMK.inW_not_outside (PMSP.W_run AD fb) a); [|exact O| |exact O| |exact O].
all: unfold PMSP.W_run, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is; cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S app].
-- apply PMK.inW_next. apply PMK.inW_here. lia.
-- do 2 apply PMK.inW_next. apply PMK.inW_here. lia.
-- do 3 apply PMK.inW_next. apply PMK.inW_here. lia.
- exact SD2.
- apply (PMK.dk_trans L LBX sp 32768 M M1 M2 (PMK.dk_of_hpres L LBX sp 32768 _ M M1 HP1)).
apply (PMPK.dk_incl L LBX LB1 sp 32768 M1 M2); [|unfold LB1; apply incl_appr; apply incl_refl].
apply (PMK.dk_callee L LB1 LB1 sp 32768 (sp - 128) scr WS M1 M2 HP2 (incl_refl _)); lia. }
split; [exact CK1|]. split; [exact MB1|]. split; [exact HH2|].
unfold PMSLPD.lslots in *.
destruct SL1 as (Q1' & Q2 & Q3 & Q4' & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
repeat split; (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGs; lia|lia|lia|]); assumption.
Qed.
Lemma lp_fin : ltac2:(TCodec.tc2 tcn__PmSParseK "SJ&RD&Fy5'TAyR0%211%5241'7y8%611%311p061'D'4'8'?%2211%411&Q0'QH'QO'QM'1'RB&R3vRHvBv@rFrErDrCrBrAr@r?r>r=r<r;r:r9%BAA@?>=<;:987654321'5&RIr1&R@%33421';&RC&T@&RNr2%211%42QD1%62?1rH%8213%:3QE31p0<1pYFA1u1%;11%=2QM1%?2G1rG%A213%C3QN31&R>&RG&Q=r7r6r5%6854Q1Q93Q621&Q7&RJ+8%22Q>1+@%53Q821&R2rJrIr8%4BQKQJ32MDQIQHQFQDQBQAQ>Q=Q<1>='RE&Q<%11QO&R8+Vg\H%26FQGQF1QEQDrL%74H521p091p0?1p0F1p0N1p0Q61p0QI1pV@RB1pW0R?1pXJRA1pX@RD1pWDRL1pQHRN1pR0S41pW6RD1pVJRF1pXDRH1pY6RJ1pX:RL1pV8S11pW4S21pX6S31pXNS41pV:S21pQ8S41pW>S:1pQ@S<1pQNSB1pQ4SI1").
Proof. intros K R M model LBX cr sp r fb cat s str sm e fx3 R3 M3 model3 s3 sm3 e3 cr3.
intros CTX KS T1 RPRE3 ED3 (STEP3 & EE3 & HP3 & CK3 & MB3 & HH3 & _).
destruct CTX as (HH & MOK & K0 & ENT & FOK & _ & _ & _ & _ & _ & _ & _ & KONT). destruct ENT as (Rra & RAok & _ & _ & _ & _).
pose proof RAok as (Hr1 & Hr2). rewrite L5K.rl1 in Rra.
pose proof (PMFR.model_ok_but_vm model model3 MOK MB3) as MOK3. pose proof MOK3 as (Mh3 & Ml3 & _).
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh3| exact Ml3| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x35d98 (ltac:(oW' 0x35d98%Z)) r (ltac:(oF' 0x35d98%Z)) eq_refl (ltac:(oD' 0x35d98%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
pose proof RPRE3 as (PA3 & _ & _ & _ & _ & _ & TB3).
destruct (PMPK2.pot_parser_nonneg RSEGS AD L M3 _ _ s3 PA3 TB3 KPM0 BOV0) as (N1 & N2).
apply (KONT fx3 R3 M3 model3 s3 sm3 e3 cr3).
- apply PMK.preserved_by_index. exact KS.
- unfold PMSP.parse_post. split; [exact RPRE3|]. split; [exact STEP3|]. split; [exact EE3|].
unfold PMSP.o_ec. cbn [pa_off_ec AD PmLayoutS.ADDR_S]. exact ED3.
- change (PMSP.pm_scr 10) with 32768. exact HP3.
- exact (PMPK2.credit_keep_final _ _ _ _ CK3 N1 N2).
- exact MB3.
- exact HH3.
Qed.
End WithHeap.
End PMSLPK.

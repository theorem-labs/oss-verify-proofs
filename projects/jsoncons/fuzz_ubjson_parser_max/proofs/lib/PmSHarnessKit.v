(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmTopS PmSHarnessStmts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSHarnessKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessKit.PMHK.Kit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1bool"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"]; ["0HIok"; "0L"; "0LB0"; "0LBc"; "0LBf"; "4Model"; "4VmMaps"; "5bvmap"; "0M"; "0M'"; "0M0"; "0M1"; "0P"; "0R"; "0R'"; "0R0"]; ["0R1"; "6credit"; "6heap_iface_ok"; "6hi_heap"; "6hl_sptop"; "6model_but_vm"; "6regs_preserved"; "7agree_on"; "7hpres"; "7stk"; "9outside"; "9range"; "9u32_at"; "9u64_at"; "9writable"; "8SCFG"]; [":ADDR_S"; ";CHUNK"; ";iss_at"; ";nullis_at"; ";parser_at"; ";parser_own"; ";pst"; ";sr_qc"; ";src_fields_at"; ";srcst"; ";strm"; ";vs_own"; ";vstr"; ";vstr_at"; "<brange"; "<err_dom"]; ["<hobjs"; "<loc_dom"; "<sys_dom"; "=CSK"; "=FRAME"; "=SCR"; "=T3"; "=T4"; "=WF"; "=fb"; "=hcore"; "=hstat"; ">err_ok"; ">loc_ok"; ">sys_ok"; "?inW"]; ["@getr"; "Amem_grows"; "Bloaded_segments"; "0SCFG_P"; "CIn"; "Cincl"; "Dadd"; "Dle"; "Dlt"; "Dmodulo"; "Dof_nat"; "Dpow"; "Dsub"; "0VM"; "0W"; "0W'"]; ["0a"; "0b"; "0be"; "0bl"; "0bs"; "0cr"; "0i"; "0isp"; "0k"; "0m"; "0model"; "0model'"; "0model0"; "0n"; "0o"; "0ois"]; ["0op"; "0os"; "0p"; "0ra"; "0s"; "0s2"; "0sbp"; "0scr'"; "0sm"; "0sp"; "0src"; "EZ_to_bv"; "Ebv"; "0str"; "0v"]]).
Module PMHK.
Import PMS. Import PMH.
Abbreviation vstr_at := (PM.vstr_at RSEGS PMH.T3).
Abbreviation iss_at := (PM.iss_at RSEGS AD PMH.T3).
Abbreviation parser_at := (PM.parser_at RSEGS AD PMH.T3 PMH.T4).
Lemma inW_WF_hi : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "@'>&R?&R8r1%3221':&RG+RPP0r2%3221&RH+mPZ@%2241%8241p0:1pV2?1").
Proof. intros a.
intros (r & Hin & Hr). unfold WF, pm_foot in Hin. cbn in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma base_not_WF : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q5'>'=':&RG+RPP0r1%3221&RH+fhV@%2241%8241+lof@%9217+lofH%7291%=231+logC%>21<+logD%<2>1%B231+lon8%C21A+lon<%A2C1%G231%I261%J2<1%K2B1&<&R?&R8r2%3221%511p071pV2Q41").
Proof. intros a.
intros H (r & Hin & Hr). unfold WF, pm_foot in Hin. cbn in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_of_not_inW : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "@'4&Q;%211'>&<&R?r2r1%3221%511&Q:r3%2216p041pV2;1pUN=1").
Proof. intros W a. intros N r Hin Hr. apply N. exists r. split; assumption. Qed.
Section Kit.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra : Z).
Variable LB0 : list (Z * Z).
Abbreviation hcore := (PMH.hcore L R0 M0 model0 sp ra LB0).
Abbreviation fb := (PMH.fb sp).
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma hcore_facts : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "R=&Gy5'SLyR0%211%5241'6y8%611%311p061'E&R:vAvOvJvS<vSIvSCvBr3r2r1%;::987654321':&RGz%221:&RH&RK+2+R0%3221%52@1%:271';&R@r4&SK&RJu2%211%42Q91%7261&RL+g@%22M1%92Q<1%=3Q<51+SoomohPPg@%I21Q1+TPPPPPPPP0%K2Q31%M231'>&RI+@%22Q81%G341Q0&Q>&RB%241Q9?@&Q9&Q4%11QC+RPP0%F21E%543Q?E1%Q<271%Q=2;1%Q>2A1%Q?2G1%Q@2Q61p0QB1pVFQO1pQBR11pQLR71").
Proof. intros R M model.
unfold PMH.hcore. intros (Hsp & _ & _ & _ & STK & DFR & SPT & _). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold fb, PMH.fb, FRAME, SCR in *.
split; [lia|]. split; [exact Hsp|]. split; [lia|]. split. { replace sp with (sp - 752 + 47 * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
split; [|exact STK]. apply (L5C.writable_of_defined RSEGS M (sp - 752) 752 DFR); lia.
Qed.
Lemma hcore_piece : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "S7&Gy5'SLyR0%211%5241'6y8%611%311p061'E'>!p021&R:vAvOvJvS<vSIvSCvBr6r5r4%;::987654321&RAr3%2261':&RGzr1%3221&RH&RK+2+R0%3221%5271%;271&<r2%D11%311';r7&SK%12Q>E%311r:%113%73Q<31p091p0>1pV2Q<1%Q11H&R9%11Q7%M21A&RF+g0%2241%M2E1%Q3251p091pV2QG1&R@&RJu2%211%H2R71%52J1%J2R7?%M3R721'5&RD&R3%233Q>1%;1Q5%Q12R@1%>2O1r=%@213%Q73RA31p071pVB;1r9r8%R;:R:R9R8R7R6R5R421Q7p041p0A1p0J1p0Q61p0R21p0R61pQJRC1pQHRH1pR2RN1pVFRI1pQBRK1pQLS11").
Proof. intros R M model R1 M1 P.
unfold PMH.hcore. intros (Hsp & Hcs & Sra & Ss0 & STK & DFR & SPT & EK & LBhi & BASE & MB & MOK) MG FR FP Hsp1 Hcs1.
pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold fb, PMH.fb, FRAME, SCR in *.
assert (AG : forall a, sp - 752 + 736 <= a -> a < 2 ^ 64 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a H1 H2. apply FR; [lia|]. intros Pa. apply FP in Pa. lia. }
assert (EK1 : PMK.ek L LB0 sp 65536 [] M M1).
{ apply (PMK.ek_piece_in' RSEGS L KL LB0 sp 65536 [] M M1 P FR); [lia| lia| exact LBhi|]. intros a Pa. left. apply FP in Pa. lia. }
split; [exact Hsp1|]. split; [intros k Hk; rewrite (Hcs1 k Hk); apply Hcs; exact Hk|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply AG; lia| lia| lia| exact Sra]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply AG; lia| lia| lia| exact Ss0]|].
split; [apply (L5C.stk_grows _ M M1 _ _ MG STK)|].
split; [intros i Hi; apply MG; apply DFR; exact Hi|]. split; [exact SPT|].
split; [|split; [exact LBhi|]].
- intros a Ha. rewrite (EK1 a); [apply EK; exact Ha|]. destruct Ha as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|]. split; [exact H3| apply L5C.outside_nil].
- split; [|split; assumption].
apply (PMKP.base_ok_keep RSEGS AD L KL SF LB0 sp 65536 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil].
Qed.
Lemma hcore_call : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "RM&Gy5'SLyR0%211%5241'6y8%611%311p061'E'4'8'>%2211%411&Q;%611&R:vAvOvJvS<vSIvSCvBr9r8r7%;::987654321&Q6r:%2214&Q8r5&R9%11=r4r3%67D53218;&REr6%23LA1':&RGz%2215&RL&R5&R4%3221%72:1%9261&R?r1%22K1'=r2%>2F1&RH&RF+g0%22J1%4261%E261&R8%=219%;231p0=1pV2QH1&Q5r=%221Q9r<r;%QI:QHQGQFQEQDQCQB421p041p081p0J1p0Q51p0Q91p0QA1p0QE1pV0R21pW@R71pQ8R61pVHR<1pQDR>1pQNRD1pVFR?1pQBRA1pQLRG1").
Proof. intros R M model R' M' model' LBc scr' W'.
unfold PMH.hcore. intros (Hsp & Hcs & Sra & Ss0 & STK & DFR & SPT & EK & LBhi & BASE & MB & MOK) RP HP INC Hscr FP MB'.
pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold fb, PMH.fb, FRAME, SCR in *.
assert (OUT : forall a, sp - 752 + 736 <= a -> L5.outside W' a).
{ intros a Ha. apply outside_of_not_inW. intros I. destruct (FP a I) as [F|F]; [lia| apply inW_WF_hi in F; lia]. }
assert (EKc : PMK.ek L LBc (sp - 752) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
assert (STKc : L5C.stk (hl_sptop L) M (sp - 752) scr') by (apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) scr' STK); [lia|lia|lia|exact A16]).
split; [rewrite (PMK.cs_of_preserved R R' 2 RP ltac:(PMK.inl)); exact Hsp|].
split. { intros k Hk. rewrite <- (Hcs k Hk). apply (PMK.cs_of_preserved R R' k RP). unfold CSK in Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [PMK.inl|]). destruct Hk. }
split. { apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact Sra].
apply (PMKP.ek_agree_stack RSEGS L KL LBc (sp - 752) scr' W' M M' _ _ EKc STKc); [lia|lia|lia|].
intros i Hi. apply OUT. lia. }
split. { apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact Ss0].
apply (PMKP.ek_agree_stack RSEGS L KL LBc (sp - 752) scr' W' M M' _ _ EKc STKc); [lia|lia|lia|].
intros i Hi. apply OUT. lia. }
split. { apply (PMK.stk_after RSEGS L KL LBc M M' (sp - 752) (65536 - 752) (sp - 752) scr' W' STK HP); lia. }
split. { intros i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
apply (L5C.hpres_cdef L LBc (sp - 752) scr' W' M M' (sp - 752 + i) HP); [lia| right; left; lia| unfold in_errno; lia| apply DFR; exact Hi]. }
split; [exact SPT|].
split; [|split; [exact LBhi|]].
- apply (PMK.ek_trans L LB0 sp 65536 WF M0 M M' EK).
apply (PMK.ek_callee_in' RSEGS L KL LB0 LBc sp 65536 (sp - 752) scr' WF W' M M' HP INC); [lia|lia|lia|lia|exact LBhi|].
intros a I. destruct (FP a I) as [F|F]; [left; lia| right; exact F].
- split; [|split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|]].
+ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBc (sp - 752) scr' W' M M' EKc); first [exact BASE |
intros a Ha; apply outside_of_not_inW; intros I; (destruct (FP a I) as [F|F]; [cbn in Ha; lia| apply (base_not_WF a); [cbn in Ha; lia| exact F]])].
+ destruct MOK as (H1 & H2 & H3). unfold PMSP.model_ok.
rewrite (L5C.halted_but_vm _ _ MB'), (L5C.lazy_but_vm _ _ MB'), (L5C.materialized_but_vm _ _ MB'). auto.
Qed.
Definition loc_dom (a : Z) : Prop := 0xc6492 <= a < 0xc6bd0 \/ 0xc72f8 <= a < 0xc7350.
Definition sys_dom (a : Z) : Prop := 0xc6490 <= a < 0xc6492.
Definition err_dom (a : Z) : Prop := 0xc6260 <= a < 0xc6262 \/ 0xe7ca8 <= a < 0xe7ec8.
Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W M M'.
Lemma loc_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "H'2'>&R?vRNr1%3221&<&R1r2%211%411p061pV2;1&R=&RB&Q@vH%443219vIr3%746521p041p0:1pV4G1").
Proof. intros b.
intros N. apply (PMKP.loc_ok_keep RSEGS AD L KL SF LBc sp' scr' W M M' E). intros iv a Hin Hr. apply outside_of_not_inW. intros I. apply (N a I).
unfold loc_dom. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma sys_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "H'2'>&R?vRNr1%3221&<&R2r2%211%411p061pV2;1&R>&RB&Q@vH%443219vIr3%746521p041p0:1pV4G1").
Proof. intros b.
intros N. apply (PMKP.sys_ok_keep RSEGS AD L KL SF LBc sp' scr' W M M' E). intros a Ha. apply outside_of_not_inW. intros I. apply (N a I). unfold sys_dom. cbn in Ha. lia.
Qed.
Lemma err_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "H'2'>&R?vRNr1%3221&<&QOr2%211%411p061pV2;1&R<&RB&Q@vH%443219vIr3%746521p041p0:1pV4G1").
Proof. intros b.
intros N. apply (PMKP.err_ok_keep RSEGS AD L KL SF LBc sp' scr' W M M' E); intros a Ha; apply outside_of_not_inW; intros I; apply (N a I); unfold err_dom; cbn in Ha; lia.
Qed.
Lemma hstat_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "N'2'>&R?vRNr1%3221'=&RG+mPZ@r2%3221&RH+RPP0%2241%8241p0:1pV2?1&R;vHr4r3%44321<vIr5%742154p041p0:1pV6K1pV:L1pV8M1").
Proof. intros bl bs be.
intros N (H1 & H2 & H3). split; [|split].
- apply loc_keep; [|exact H1]. intros a I D. destruct (N a I); unfold loc_dom in D; lia.
- apply sys_keep; [|exact H2]. intros a I D. destruct (N a I); unfold sys_dom in D; lia.
- apply err_keep; [|exact H3]. intros a I D. destruct (N a I); unfold err_dom in D; lia.
Qed.
End Along.
Definition brange (LBc : list (Z * Z)) : Prop :=
forall B m, In (B, m) LBc -> 4096 <= B /\ (B + m <= 0x10000 \/ 0xe9000 <= B) /\ B + m <= hl_ceil L.
Lemma brange_of_heap : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q9'Q2vA&Q?vRC%211v?%63521'4'8'>%2211%411&Q1'SLyR0%211'6y8%511%311p051'F&Q3r5r3r2r1%55F4321&REr6%23D71&QN%113p031p071pUL>1pQB@1pV<I1pQ8K1pQ:L1pQ2Q21").
Proof. intros HIok LBf LBc cr M VM.
intros HH INC B m Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LBf cr M VM HH) (B, m) (INC _ Hin)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
cbn [fst snd] in *. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. split; [exact Q0|]. split; [exact Q1| exact Q4].
Qed.
Definition hobjs (M : word -> option byte) (s s2 : PM.vstr) (sm : PM.strm) (p : PM.pst) : Prop :=
vstr_at M (fb + 712) s /\ iss_at M (fb + 440) s2 sm /\ parser_at M (fb + 40) (fb + 440) p /\ L5.u64_at RSEGS M (fb + 432) (pa_vp_visitor AD).
Section Objs.
Variables (LBc : list (Z * Z)) (scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc fb scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M fb scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : brange LBc.
Hypothesis WSTD : forall a, PMK.inW W' a -> fb <= a \/ 0x10000 <= a < 0xe9000.
Lemma ag_frame : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q6'>&RG&R9vSI%211r2%5221&RFr3%2214+g@%4271%;231':r5r1%?221&RHr4%<251%3251%8251&<&R?vRO%221D%411p061pV>L1&Q7vHvI%3421B>p051p0F1p0M1pVLQ41pV2Q51").
Proof. intros a n.
intros H1 H2 N. pose proof STKc as (_ & _ & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
apply (PMKP.ek_agree_stack RSEGS L KL LBc (sp - 752) scr' W' M M' a n E STKc SCR0); [lia|lia|]. intros i Hi. apply outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_block : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "B'>&RD'8%1233(7r2r1%347721vC%83621&Q7vHvIr3%443219p061pVD@1p2A1").
Proof. intros B m.
intros Hin. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
pose proof STKc as (_ & SLO & SHI & STOP & _).
apply (PMKP.ek_agree L LBc fb scr' W' M M' B m E). intros i Hi.
apply (PMKP.kept_block RSEGS L KL LBc fb scr' W' B m i Hin Hi); [lia| exact Q4| rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact Q1| lia|].
apply outside_of_not_inW. intros I. destruct (WSTD i I); unfold fb, PMH.fb, FRAME in *; lia.
Qed.
Lemma u64_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q;'>&RG&R9vSI%211r2%5221&RFr3+8%3221+g@%5281%<231':r5r1%@221&RH%<24:%2241%7241&<&R?vRO%221D%411p061pV>L1&Q=&RBvHr4%4432B1vIr6%74621Ep041p0:1p0J1p0Q21pWNQ91pV2Q:1").
Proof. intros a v.
intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
apply (L5C.u64_at_agree RSEGS M M'); [apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|exact N]|lia|lia].
Qed.
Lemma u32_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q;'>&RG&R9vSI%211r2%5221&RFr3+4%3221+g@%5281%<231':r5r1%@221&RH%<24:%2241%7241&<&R?vRO%221D%411p061pV>L1&Q<&RBvHr4%4432B1vIr6%74621Ep041p0:1p0J1p0Q21pWNQ91pV2Q:1").
Proof. intros a v.
intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
apply (PMF.u32_at_agree RSEGS M M'); [apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|exact N]|lia|lia].
Qed.
Lemma vstr_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QF'>'QL&RG&R9vSI%211r2%5221&RFr3+H%3221+g@%5281%<231':r5r1%@221&RH%<24:%2241%7241&<&R?vRO%221D%411p061pV>M1&RE'8%12Q0Q0&QKr4%211vC%73521&QM&RB&R6vHr6%554321KvIr7%8576214p041p0;1p0D1p0Q41p0Q<1pW:QC1pVNQE1").
Proof. intros o s.
intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
apply (PMF.vstr_at_agree RSEGS M M' o s); [lia|lia| apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|exact N]| |exact VS].
intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma iss_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QJ'>'QL'QJ&RG&R9vSI%211r3%5221&RFr4+X@%3221+g@%5281%<231':r6r1%@221&RH%<24:%2241%7241&<&R?vROr2%3221%511p071pV>O1&RE'8%12Q2Q2&QKr5%211vC%73521&QB&RB&Q@&R6vHr7%6754321M:vIr8%97876214Q0p041p0<1p0E1p0Q61p0Q>1pWBQE1pWLQG1pW0QI1").
Proof. intros ois str sm.
intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
apply (PMF.iss_at_agree RSEGS AD M M' ois str sm); [lia|lia| apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|exact N]| |exact VS].
intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma parser_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QJ'>'QF&RG&R9vSI%211r3%5221&RFr4+\0%3221+g@%5281%<231':r6r1%@221&RH%<24:%2241%7241&<&R?vROr2%3221%511p071pV>N1&RE'8%12Q1Q1&QE%11JvC%63421&QD&RB&Q@&R6&R7vHr7r5%88765432N1vIr8%;8:987215Q1p041p0>1p0F1p0Q71p0Q?1pW:QF1pW0QH1pW2QI1").
Proof. intros op ois s.
intros H1 H2 N INC PA. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
assert (Bq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; auto).
assert (Bv : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LBc) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; auto).
destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). destruct (BR _ _ Bv) as (V0 & V1 & V4).
apply (PMF.parser_at_agree RSEGS AD M M' op ois s); [lia|lia| apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|exact N]|lia|lia| apply ag_block; exact Bq|lia|lia| apply ag_block; exact Bv| |exact PA].
intros c n p Et. apply ag_block. apply INC. unfold PM.parser_own. apply in_or_app. right. apply in_or_app. right. rewrite Et. cbn. auto.
Qed.
Lemma nullis_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q:'>&RG&R9vSI%211r1%5221&RFr2+W8%3221+g@%5281%<231':r4%?21;&RH%;239%22>1%6241&<&R?vRO%221@%411p061pV>K1&QC&RB&Q@&R6vH%554321BvIr5%8576521p041p0;1p0J1p0Q21pVNQ91").
Proof. intros o.
intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PMH.fb, FRAME in *.
apply (PMF.nullis_at_agree RSEGS AD M M' o); [lia|lia| apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|exact N]].
Qed.
Lemma src_keep : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QN'>'QI&RG&R9vSI%211r4%5221&RFr5+Y8%3221+g@%5281%<231':r7+W@%:221r1%B221&RH%>26<%2241%9241&<&R?vROr2%3221%511p071pV>Q01&RD'8%12Q3Q3(7&QG%11Q0&QA%44Q8Q821vC%93721&QH&RB&R6vHr8r6%675432Q11Q8vIr9%9787215Q44p041p0<1p0G1p0Q:1p0QB1pWFQI1pW>QK1pV@QL1pW4QM1").
Proof. intros os isp sbp src.
intros H1 H2 N Bq. pose proof STKc as (_ & SLO & SHI & STOP & _). destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). unfold fb, PMH.fb, FRAME in *.
apply (PMF.src_fields_at_agree RSEGS M M' os isp sbp src); [lia|lia|lia|lia| apply ag_frame; unfold fb, PMH.fb, FRAME; [lia|lia|intros i Hi; apply N; lia]| apply ag_block; exact Bq].
Qed.
Lemma hobjs_call : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "R2'QL'QJ'QF'>&R?vROr1%3221':&<&RG&RF&R9vSI%211+Q8%5221r2%8221&RH+]8%:271%3251%?251%?11+]@%?2<1%A21:+g0%B2?1%;2=1%G241%G11%I291p0K1pV2Q01&RE'8%12Q3Q3&1&QE%11H&QKr4%211r5%411%83931%93:71vC%>3<21&R0vHr6r3%4532:<1vIr7%75215=?p041p0:1p0J1pW6QL1pWBQN1pW<R01pW:R11").
Proof. intros s s2 sm p.
intros N INC (VS & IA & PA & VV). unfold fb, PMH.fb, FRAME in *.
split. { apply vstr_keep; unfold fb, PMH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| |exact VS].
intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. right. exact Hx. }
split. { apply iss_keep; unfold fb, PMH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| |exact IA].
intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. left. exact Hx. }
split. { apply parser_keep; unfold fb, PMH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| |exact PA].
intros x Hx. apply INC. apply in_or_app. left. exact Hx. }
apply u64_keep; unfold fb, PMH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| exact VV].
Qed.
End Objs.
Section Piece.
Variables (LBc : list (Z * Z)) (M M1 : word -> option byte) (P : Z -> Prop) (scrx : Z).
Hypothesis FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis PF : forall a, P a -> fb <= a < fb + 752.
Hypothesis STKx : L5C.stk (hl_sptop L) M fb scrx.
Hypothesis SCRx : 0 <= scrx.
Hypothesis BR : brange LBc.
Lemma agp : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q5'>&RGzr2%3221&RFr3%2214&RK+2+R0%3221%;251':r5r1%?221&RHr4%>251%3251%8251&<vL%11E%311p051pV>K1&Q7vHvK%3421A=p051p0E1p0N1pVLQ31pV2Q41").
Proof. intros a n. intros H1 H2 N i Hi. apply FRZ; [lia| apply N; exact Hi]. Qed.
Lemma agp_block : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "B'>&RD'8%1233(7r2r1%347721vC%83621&Q7vHvKr3%443219p061pVD@1p2A1").
Proof. intros B m.
intros Hin. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
pose proof STKx as (_ & SLO & SHI & STOP & _). apply agp; [lia|lia|]. intros i Hi Pi. apply PF in Pi. lia.
Qed.
Lemma u64_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q:'>&RGzr2%3221&RFr3+8%3221&RK+2+R0%3221%<251':r5r1%@221&RH%>24<%2241%7241&<vL%11E%311p051pV>K1&Q=&RBvHr4%4432A1vKr6%74621Dp041p0:1p0I1p0Q31pWNQ81pV2Q91").
Proof. intros a v. intros H1 H2 N. apply (L5C.u64_at_agree RSEGS M M1); [apply agp; assumption|lia|lia]. Qed.
Lemma u32_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q:'>&RGzr2%3221&RFr3+4%3221&RK+2+R0%3221%<251':r5r1%@221&RH%>24<%2241%7241&<vL%11E%311p051pV>K1&Q<&RBvHr4%4432A1vKr6%74621Dp041p0:1p0I1p0Q31pWNQ81pV2Q91").
Proof. intros a v. intros H1 H2 N. apply (PMF.u32_at_agree RSEGS M M1); [apply agp; assumption|lia|lia]. Qed.
Lemma vstr_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QE'>'QL&RGzr2%3221&RFr3+H%3221&RK+2+R0%3221%<251':r5r1%@221&RH%>24<%2241%7241&<vL%11E%311p051pV>L1&RE'8%12OO&QKr4%211vC%73521&QM&RB&R6vHr6%554321JvKr7%8576214p041p0;1p0D1p0Q31p0Q=1pW:QB1pVNQD1").
Proof. intros o s.
intros H1 H2 N INC. apply (PMF.vstr_at_agree RSEGS M M1 o s); [lia|lia|apply agp; assumption|].
intros c n p ->. apply agp_block. apply INC. cbn. auto.
Qed.
Lemma iss_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QI'>'QL'QJ&RGzr3%3221&RFr4+X@%3221&RK+2+R0%3221%<251':r6r1%@221&RH%>24<%2241%7241&<vLr2%211%411p061pV>N1&RE'8%12Q1Q1&QKr5%211vC%73521&QB&RB&Q@&R6vHr7%6754321L:vKr8%97876214Op041p0<1p0E1p0Q51p0Q?1pWBQD1pWLQF1pW0QH1").
Proof. intros ois str sm.
intros H1 H2 N INC. apply (PMF.iss_at_agree RSEGS AD M M1 ois str sm); [lia|lia|apply agp; assumption|].
intros c n p ->. apply agp_block. apply INC. cbn. auto.
Qed.
Lemma parser_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QI'>'QF&RGzr3%3221&RFr4+\0%3221&RK+2+R0%3221%<251':r6r1%@221&RH%>24<%2241%7241&<vLr2%211%411p061pV>M1&RE'8%12Q0Q0&QE%11KvC%63421&QD&RB&Q@&R6&R7vHr7r5%88765432M1vKr8%;8:987215Q0p041p0>1p0F1p0Q61p0Q@1pW:QE1pW0QG1pW2QH1").
Proof. intros op ois s.
intros H1 H2 N INC PA.
assert (Bq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBc) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; auto).
assert (Bv : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LBc) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; auto).
destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). destruct (BR _ _ Bv) as (V0 & V1 & V4).
pose proof STKx as (_ & SLO & SHI & STOP & _).
apply (PMF.parser_at_agree RSEGS AD M M1 op ois s); [lia|lia|apply agp; assumption|lia|lia|apply agp_block; exact Bq|lia|lia|apply agp_block; exact Bv| |exact PA].
intros c n p Et. apply agp_block. apply INC. unfold PM.parser_own. apply in_or_app. right. apply in_or_app. right. rewrite Et. cbn. auto.
Qed.
Lemma nullis_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q9'>&RGzr1%3221&RFr2+W8%3221&RK+2+R0%3221%<251':r4%?21=&RH%=23;%22@1%6241&<vL%11A%311p051pV>J1&QC&RB&Q@&R6vH%554321AvKr5%8576521p041p0;1p0I1p0Q31pVNQ81").
Proof. intros o. intros H1 H2 N. apply (PMF.nullis_at_agree RSEGS AD M M1 o); [lia|lia|apply agp; assumption]. Qed.
Lemma src_keep_p : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QM'>'QI&RGzr4%3221&RFr5+Y8%3221&RK+2+R0%3221%<251':r7+W@%<221r1%B221&RH%@26>%2241%9241&<vLr2%211%411p061pV>O1&RD'8%12Q2Q2(7&QG%11Q1&QA%44Q7Q721vC%93721&QH&RB&R6vHr8r6%675432Q01Q9vKr9%9787215Q34p041p0<1p0G1p0Q91p0QC1pWFQH1pW>QJ1pV@QK1pW4QL1").
Proof. intros os isp sbp src.
intros H1 H2 N Bq. destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). pose proof STKx as (_ & SLO & SHI & STOP & _).
apply (PMF.src_fields_at_agree RSEGS M M1 os isp sbp src); [lia|lia|lia|lia| apply agp; [lia|lia|intros i Hi; apply N; lia]| apply agp_block; exact Bq].
Qed.
Lemma hobjs_piece : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "QO'QL'QJ'QF'>vLr1%211'=':&RG&RF&R9vSI%211+8%5221r2%8221&RH+Q8%:271%3251%>251+]8%>2;1%@219+]@%A2>1%:2<1%E241%G281p0I1pV2M1&RE'8%12Q0Q0&1&QE%11F&QKr4%211r5%411%83931%93:71vC%>3<21&R0vHr6r3%4532:<1vKr7%75215=?p041p0:1p0J1pW6QI1pWBQK1pW<QM1pW:QN1").
Proof. intros s s2 sm p.
intros N INC (VS & IA & PA & VV). pose proof STKx as (_ & SLO & SHI & STOP & _). unfold hobjs. unfold fb, PMH.fb, FRAME in *.
split. { apply vstr_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| |exact VS].
intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. right. exact Hx. }
split. { apply iss_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| |exact IA].
intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. left. exact Hx. }
split. { apply parser_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| |exact PA].
intros x Hx. apply INC. apply in_or_app. left. exact Hx. }
apply u64_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| exact VV].
Qed.
Lemma hstat_piece : ltac2:(TCodec.tc2 tcn__PmSHarnessKit "Q@'2&Q9&Q4vA%211vH&R9vSI%211&RL&R5&R4%3221%<49851'8'>%2211&RDr1vC%33421&RG&RF&3r2%23::1&9%13<<3%6231+XPPP0%E2J1%:231p0<1pV4A1&R;r5r4r3%44Q1321vKr6%742165p041p0:1p0O1pV6Q=1pV:Q>1pV8Q?1").
Proof. intros bl bs be.
intros (_ & SLO & SHI & STOP & _) LBhi. unfold fb, PMH.fb, FRAME, SCR in *.
assert (EK1 : PMK.ek L LBc sp 65536 [] M M1).
{ apply (PMK.ek_piece_in' RSEGS L KL LBc sp 65536 [] M M1 P FRZ); [lia|lia|exact LBhi|]. intros a Pa. left. apply PF in Pa. unfold fb, PMH.fb, FRAME in Pa. lia. }
apply (hstat_keep LBc sp 65536 [] M M1 EK1). intros a (r & [] & _).
Qed.
End Piece.
End Kit.
End PMHK.

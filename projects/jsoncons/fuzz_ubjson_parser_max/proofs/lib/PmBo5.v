(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit
PmCertKitG PmSrcSMemmove PmBaKit PmBoStmts PmBo1 PmBo2 PmBo4 PmBoSP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBo5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBo1.PMBO1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBo2.PMBO2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBo5.PMBO5.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoStmts.PMBOS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1option"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"]; ["0R"; "0R0"; "6credit"; "7SCFG"; "8FPB"; "8blk_ok"; "9push_st"; ":gstate"; ":pushok"; ";mem_ok"; ";regs_at"; ";saves"; "<ADDR_S"; "=inv"; "=p_b"; "=p_k"]; ["=p_tb"; "=p_tg"; "=parser_at"; "=pot_parser"; "=pst"; "=pstate"; "=pstate_at"; "=strm"; "=tb_ok"; ">T3"; ">T4"; ">cfg"; ">credit_keep"; ">ec_at"; ">prog_value"; ">run_pre"]; ["?opdel_spec"; "@FPState"; "@getr"; "Asrealizes"; "Bmem_grows"; "Cloaded_segments"; "0S"; "0SCFG_P"; "Dadd"; "Dle"; "Dlt"; "Dmul"; "Dof_nat"; "Dpow"; "0c"; "0cat"]; ["0cr"; "0cr0"; "0e"; "0fb"; "0fx"; "0i"; "0k"; "0len"; "0m"; "0model"; "0s"; "0s'"; "0s0"; "0s1"; "0sm"; "0sm0"]; ["EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0str"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBO5.
Import PMS.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBO2.push_st.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis PRE : PMBOS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBOS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBOS.kept0 R0).
Local Abbreviation regs_at := (PMBOS.regs_at R0 S fb).
Local Abbreviation saves := (PMBOS.saves R0 S).
Local Abbreviation mem_ok := (PMBOS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBOS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBOS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBO1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBO1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBO1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBO1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBO1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBO1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBO1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBO1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBO2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBO2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBO2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBo5 "B'RAyR0%211'3&QIz&RBr1%2271%5241&QJ&QM+2+R0%3221%5271%=271pU:?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBOP2.aligned; first [assumption | lia]].
Local Ltac prep_ctx M W MO :=
let PA := fresh "PA" in let IA := fresh "IA" in let VIS := fresh "VIS" in let VREF := fresh "VREF" in let BASE := fresh "BASE" in
let ERR := fresh "ERR" in let TB := fresh "TB" in let HH := fresh "HH" in let MB := fresh "MB" in let STEP := fresh "STEP" in
let EE := fresh "EE" in let CK := fresh "CK" in let EK := fresh "EK" in let DK := fresh "DK" in let STK := fresh "STK" in
pose proof W as ((PA & IA & VIS & VREF & BASE & ERR & TB) & HH & MB & STEP & EE & CK);
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF; cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF;
unfold PMSP.visitor_at in VIS; cbn [pa_vp_visitor AD PmLayoutS.ADDR_S] in VIS;
pose proof MO as (EK & DK & STK);
let MOK := fresh "MOK" in pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK;
let Mh := fresh "Mh" in let Ml := fresh "Ml" in pose proof MOK as (Mh & Ml & _);
let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in pose proof FOK as (F1 & F2 & F3);
let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in let X4 := fresh "X4" in let X5 := fresh "X5" in
pose proof SBND as (X1 & X2 & X3 & X4 & X5);
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBOS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBO1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBO1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBO1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBO1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBO1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBO1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBO1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_del := PMBO4.grow_del L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_end_i := PMBO4.grow_end_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_end_ct := PMBO4.grow_end_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Definition gstate (M : word -> option byte) (model : Model) (s1 : PM.pst) (sm : PM.strm) (e : bool) (cr : credit) (B : Z) : Prop :=
PMSP.run_pre RSEGS AD M fb s1 str sm e /\ hi_heap HI ((B, 32 * 2 ^ (PM.p_k s1 + 1)) :: PM.parser_own s1 ++ LBX) cr M (m_vmmaps model)
/\ model_but_vm model0 model /\ PMSP.src_step (PM.p_src s0) (PM.p_src s1) sm0 sm /\ (e0 = true -> e = true)
/\ 4096 <= B /\ B mod 16 = 0 /\ B + 32 * 2 ^ (PM.p_k s1 + 1) <= hl_ceil L
/\ (B + 32 * 2 ^ (PM.p_k s1 + 1) <= hl_img_lo L \/ hl_img_hi L <= B)
/\ (forall B2 m2, In (B2, m2) (PM.parser_own s1 ++ LBX) -> B + 32 * 2 ^ (PM.p_k s1 + 1) <= B2 \/ B2 + m2 <= B)
/\ L5.defined M B (32 * 2 ^ (PM.p_k s1 + 1)).
Definition pushok (s1 : PM.pst) (sm : PM.strm) (c : PM.pstate) : Prop :=
PM.inv_d 1 s1 /\ PM.p_depth s1 <= 1024 /\ PM.p_stk s1 = PM.p_stk s0 /\ Z.of_nat (length (PM.p_stk s1)) = 2 ^ PM.p_k s1 /\ 0 <= PM.p_k s1 <= 10
/\ PM.pstate_ok c /\ ~ PM.mode_bottom (PM.ps_mode c) /\ PM.ps_idx c = 0
/\ (PM.mode_counted (PM.ps_mode c) -> PM.unread (PM.p_src s1) sm < PM.unread (PM.p_src s0) sm0).
Lemma push_facts : ltac2:(TCodec.tc2 tcn__PmBo5 "K'Q4'Q7'Q5'6&Hr5r4r3%43321'3&M&Fr6r2%342718%511&Q>vR<vR?%34251>%;251p0=1pT>C1p2D1pSNF1pTNH1pTLJ1").
Proof. intros s1 sm c B k.
intros (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof IV1 as (IM & ID & IDP & ISH & ITB).
split.
- unfold PM.inv, push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [exact IM|]. split; [exact ID|]. split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; lia|].
split; [|exact ITB]. apply (PMBK.stack_shape_push _ c ISH); [unfold PM.MAX_DEPTH; lia| exact Hc| exact Hm].
- unfold PMSP.prog_value, PMSP.push_rel. right. exists c. unfold push_st. cbn [PM.p_stk PM.p_src].
split; [rewrite ES1; reflexivity|]. split; [exact Hc|]. split; [exact Hi0|]. split; [exact Hm| exact Hcnt].
Qed.
Lemma keep_objs : ltac2:(TCodec.tc2 tcn__PmBo5 "S3'RAyR0%211'2y8%511%311p051'Q4'Q7'1'6&Q?&QE&Lr8vR3r6vRCr4r3%9887654321&Iv9v?v:vQFr9%665432<1&QDr:%2214'3&QIzr1%3221&QJ&QM+2+R0%3221%5271%;271&5&Dr7r2%35FQ02O1%511'4r=&R@%12QDQ1%311r>%113%73QC31p091p0@1pT<QA1&Er5%24Q8Q6Q>1&Q2&Q9&Q:r<&QH+Q8%22QF1+]H%42QH1%98QLQK87631Q;&Q8&Q0r;%211&Q1%113%6231%R58R4R3JR1>QO5QC%QL6QKQJQIQHR2K%QC221p041p0<1p0G1p0K1p0QI1p0QM1p0R51pTBR@1p2RA1pT6RC1pTNRE1pTHRG1pTFRH1pNRJ1pLRK1").
Proof. intros M M' s s' sm e B m.
intros RP (EK & DK & STK) MG FR BK PA' TB'.
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
assert (EKP : PMK.ek L LBX S SCR (PMBO1.WP fb) M M') by exact (ek_fp M M' B m FR BK).
assert (SC0 : 0 <= SCR) by (unfold PMBOS.SCR; lia).
assert (NW : forall a n, fb + 424 <= a -> forall i, a <= i < a + n -> ~ PMK.inW (PMBO1.WP fb) i).
{ intros a n H1 i Hi (r0 & Hr & Hin). unfold PMBO1.WP in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
destruct RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
split.
- unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S].
split; [exact PA'|].
split. { apply (PMFR.iss_keep RSEGS AD L KL LBX S SCR (PMBO1.WP fb) M M' EKP STK SC0 brx WP_hi); [lia|lia| |exact INCS| exact IA]. apply NW. lia. }
split. { apply (PMFR.visitor_keep RSEGS AD L KL LBX S SCR (PMBO1.WP fb) M M' EKP STK SC0); [lia|lia| |exact VIS]. apply NW. lia. }
split. { apply (PMFR.u64_keep RSEGS L KL LBX S SCR (PMBO1.WP fb) M M' EKP STK SC0); [lia|lia| |exact VREF]. apply NW. lia. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX S SCR (PMBO1.WP fb) M M' EKP); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros (r0 & Hr & Hin); unfold PMBO1.WP in Hr;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha;
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
split; [|exact TB'].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX S SCR (PMBO1.WP fb) M M' EKP); [| | exact ERR].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros (r0 & Hr & Hin); unfold PMBO1.WP in Hr;
cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha;
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
- split; [|split].
+ apply (PMK.ek_trans L LBX S SCR _ M0 M M' EK).
apply (PMK.ek_weaken L LBX LBX S SCR S SCR _ (PMBO1.WP fb) M M' EKP); [apply incl_refl| intros x Hx; exact Hx| exact WP_run].
+ apply (PMK.dk_trans L LBX S SCR M0 M M' DK). apply PMK.dk_grows. exact MG.
+ exact (PMK.stk_grows L M M' S SCR MG STK).
Qed.
Lemma grow_h_i : ltac2:(TCodec.tc2 tcn__PmBo5 "U;'QA&<y5'RAyR0%211%5241'2y8%611%311p061';'Q4'Q7'1&B'6'Q5&JvAvQFvR3r9%544321'4&QBr:&R@&QLuC%211%42N1%7261r3%72O1%;3O31r;uD%:11%<2Q61%?241&QHr4&QK+Q0&QM+2&Or8%211%5241%8271%;2:1%<219%K2QC1%O3QC?1r<uE%N11%Q02QJ1%Q3241r5%?1Q8+1%G221%D2C1%G2F1%J261%Q92R11%Q=3R191&K%13QDQC?&Iv9v?v:r=%56432QIQH1&Gr>%2714HQ<QFQJQ0&Q=&QEr?+8%Q<2R01zvQO%7565321&H%13;>R4'3&QIr1%2281&QJr@%QB11%QE2QD1%QH2QG1%5271%:271rCr2%QO2L1%R>2S61%411&NrA%211%R5217%RD2S<1%:11%RI3S871p0=1pT<S31&Q6rB%R=2QNC%34Q521RC&Q<vR1&Q3vR<%22QC1&F%R?1B%RF21R0%34DQD1R8%72QH1%:49QC61&Q@vQGv7%332QM1'QC&C%115&Q;rGrF+Vme@rErD%66QN54321v8%;4R0921p0=1p0B1p0N1p0Q31p0QM1p0R01p0R91p0R=1p0RD1p0RG1p0S61p0SK1p0T81pSNT?1p2TA1pT2TC1pT6TE1pTNTG1pTLTI1pTDTK1pLTM1pQ2U31pT:U:1").
Proof. intros fx R M model s1 sm e cr B c.
intros RA R19 R20 R21 SV MO GS ECZ PK CP PC CK OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBOS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
pose proof PA as (_ & _ & _ & P8 & _ & P12 & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & PB1 & PB2 & PB3).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL). rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4). unfold hl_ceil in V4, GB1.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
cfeed P (PMBOP2.boIH_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 54%nat => 2 ^ (vk1 + 1) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & T12 & C80 & C88 & C96 & C104 & C376 & C368 & C360).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x376b0 R1 0x54400 M1
(fun a => (fb + 40 + 360 <= a < fb + 40 + 360 + 24) \/ (S - 104 <= a < S - 104 + 32)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 400 \/ fb + 424 <= a) -> (a + n <= S - 104 \/ S - 72 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
set (s' := push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) B (vk1 + 1) c).
assert (VEC1 : PM.vec_at RSEGS PMSP.T3 PMSP.T4 M1 (fb + 40 + 360) B (vk1 + 1) (stk1 ++ [c])).
{ apply (PMBK.vec_grow RSEGS M M1 (fb + 40 + 360) vb1 vk1 stk1 c B PVEC HL); [lia|lia|lia|lia|lia|lia| | | | | |].
- replace (fb + 40 + 360) with (fb + 40 + 360) by lia. exact C360.
- replace (fb + 40 + 360 + 8) with (fb + 40 + 368) by lia. replace (B + 32 * 2 ^ vk1 + 32) with (B + 32 * 2 ^ vk1 + 32) by lia. exact C368.
- replace (fb + 40 + 360 + 16) with (fb + 40 + 376) by lia. replace (B + 32 * 2 ^ (vk1 + 1)) with (B + 32 * 2 ^ (vk1 + 1)) by lia. exact C376.
- intros i Hi. apply MG1. apply GBD. exact Hi.
- intros i Hi. rewrite (AGo (B + i) 1) by (clear - Hi GB0 GB1 X3 X5 F1 P2 Pp; lia || (unfold hl_ceil in *; lia)). apply CP. exact Hi.
- apply (PMF.pstate_at_agree RSEGS M M1); [lia|lia| |exact PC]. apply AGo; clear - GB0 GB1 X3 X5 F1 P2 Pp; lia. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s').
{ unfold s', push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg].
apply (PMBK.parser_upd RSEGS AD M M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) mo1 dp1 B (vk1 + 1) (stk1 ++ [c]) PA);
cbn [PM.p_src PM.p_tb]; [lia|lia| | | | | | | | | |exact VEC1| |].
- apply AGo; lia.
- apply AGo; lia.
- apply AGo; lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- apply (L5C.u8_at_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact P8].
- exact PB1.
- apply (PMF.u32_at_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact P12].
- exact PB3.
- apply PMPK.dkr_grows. exact MG1.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
destruct (keep_objs M M1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) s' sm e 0 0 RP MO MG1) as (RP1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBO1.FPB; [right; right; left; lia| left; unfold PMBOS.SCR; lia]. }
{ left; reflexivity. }
{ exact PA1. }
{ exact ITB. }
apply (grow_del 0x376dc fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- exact T1.
- split; [lia| reflexivity].
- split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T10.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBOS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
- exact MO1.
- exact RP1.
- exact HH1.
- exact MB.
- exact STEP.
- exact EE.
- exact CK.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact ECZ].
- cbn [PM.p_k]. lia.
- exact OPD.
- intros fx2 R2' M2 model2 RP2 SV2 MO2 W2 EC2 AGH2.
destruct (push_facts (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm c B (vk1 + 1) PK) as (INV' & PV').
apply (grow_end_i fx2 R2' M2 model2 s' sm e cr); [| | exact SV2| exact MO2| exact W2| exact EC2| exact INV'| exact PV'].
+ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; rewrite (KS1 2%nat) by PMK.inl; exact R2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; rewrite (KS1 9%nat) by PMK.inl; exact R9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; rewrite (KS1 18%nat) by PMK.inl; exact R18|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [| unfold PMBOS.CSK in Hk0; cbn in Hk0; repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]); destruct Hk0].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP| exact Hk0].
+ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. rewrite R20.
rewrite L5.unsigned_lit by lia.
apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH2; lia|lia|lia|]. replace (fb + 408) with (fb + 40 + 368) by lia. exact C368.
Qed.
Lemma grow_h_ct : ltac2:(TCodec.tc2 tcn__PmBo5 "UJ'QA&<y5'RAyR0%211%5241'2y8%611%311p061';'Q4'Q7'1&B'6'Q5&JvAvQFvR3r:%544321'4&QBr;&R@&QLuC%211%42N1%7261r2%72O1%;3O31'3&QIzr3%3221+`PPP0%5231%7231r=uD%B11%D2Q>1%G241r6%G2Q?1%K3Q?31r>uE%J11%L2QF1%O241&QHr7&QK+Q0&QM+2&O%11Q6%4231%7261%:291%;218%Q:2R21%Q>3R2>1r?uF%Q=11%Q?2R91%QB241r8r<%?11+1%G221%D2C1%G2F1%J271%QI2RA1%QM3RA:1&K%13R4R3@&Iv9v?v:r@%56432R9R81&GrA%2714IQ<QDCR6&Q=&QErB+8%Q<2R@1vQO%65542R11&H%13:=Lr1%R62R51&QJrC%Q?11%QB2QA1%QE2QD1%5271%R>271rF%QK2HRC%RJ2SB1%311&NrD%211%R121RI%S02SH1%911%S53SD71p0<1pT<S?1&Q6rE%R92QKB%34Q121R?&Q<vR1&Q3vR<%22Q?1&F%R;1B%RB21QL%34DQ@1R5%72QD1%:49Q?61&Q@vQGv7%332QI1'QC&C%115&Q;rJrI+VnQ<rHrG%66QJ54321v8%;4QL921p0=1p0B1p0N1p0Q31p0QJ1p0QM1p0R51p0R91p0R@1p0RC1p0S31p0SG1p0T01p0T91p0TF1pT@TN1pSNTN1p2U01pT2U21pT6U41pTNU61pTLU81pTDU:1pLU<1pQ2UB1pT:UI1").
Proof. intros fx R M model s1 sm e cr B c len.
intros RA R19 HLn R20 R21 R22 SV MO GS ECZ PK CP PC CK OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBOS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
pose proof PA as (_ & _ & _ & P8 & _ & P12 & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & PB1 & PB2 & PB3).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL). rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4). unfold hl_ceil in V4, GB1.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
cfeed P (PMBOP2.boH_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 48%nat => len
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 54%nat => 2 ^ (vk1 + 1) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & T12 & C80 & C88 & C96 & C104 & C376 & C368 & C360).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x3782c R1 0x54400 M1
(fun a => (fb + 40 + 360 <= a < fb + 40 + 360 + 24) \/ (S - 104 <= a < S - 104 + 32)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 400 \/ fb + 424 <= a) -> (a + n <= S - 104 \/ S - 72 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
set (s' := push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) B (vk1 + 1) c).
assert (VEC1 : PM.vec_at RSEGS PMSP.T3 PMSP.T4 M1 (fb + 40 + 360) B (vk1 + 1) (stk1 ++ [c])).
{ apply (PMBK.vec_grow RSEGS M M1 (fb + 40 + 360) vb1 vk1 stk1 c B PVEC HL); [lia|lia|lia|lia|lia|lia| | | | | |].
- replace (fb + 40 + 360) with (fb + 40 + 360) by lia. exact C360.
- replace (fb + 40 + 360 + 8) with (fb + 40 + 368) by lia. replace (B + 32 * 2 ^ vk1 + 32) with (B + 32 * 2 ^ vk1 + 32) by lia. exact C368.
- replace (fb + 40 + 360 + 16) with (fb + 40 + 376) by lia. replace (B + 32 * 2 ^ (vk1 + 1)) with (B + 32 * 2 ^ (vk1 + 1)) by lia. exact C376.
- intros i Hi. apply MG1. apply GBD. exact Hi.
- intros i Hi. rewrite (AGo (B + i) 1) by (clear - Hi GB0 GB1 X3 X5 F1 P2 Pp; lia || (unfold hl_ceil in *; lia)). apply CP. exact Hi.
- apply (PMF.pstate_at_agree RSEGS M M1); [lia|lia| |exact PC]. apply AGo; clear - GB0 GB1 X3 X5 F1 P2 Pp; lia. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s').
{ unfold s', push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg].
apply (PMBK.parser_upd RSEGS AD M M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) mo1 dp1 B (vk1 + 1) (stk1 ++ [c]) PA);
cbn [PM.p_src PM.p_tb]; [lia|lia| | | | | | | | | |exact VEC1| |].
- apply AGo; lia.
- apply AGo; lia.
- apply AGo; lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- apply (L5C.u8_at_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact P8].
- exact PB1.
- apply (PMF.u32_at_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact P12].
- exact PB3.
- apply PMPK.dkr_grows. exact MG1.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
destruct (keep_objs M M1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) s' sm e 0 0 RP MO MG1) as (RP1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBO1.FPB; [right; right; left; lia| left; unfold PMBOS.SCR; lia]. }
{ left; reflexivity. }
{ exact PA1. }
{ exact ITB. }
apply (grow_del 0x37858 fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- exact T1.
- split; [lia| reflexivity].
- split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T10.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBOS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
- exact MO1.
- exact RP1.
- exact HH1.
- exact MB.
- exact STEP.
- exact EE.
- exact CK.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact ECZ].
- cbn [PM.p_k]. lia.
- exact OPD.
- intros fx2 R2' M2 model2 RP2 SV2 MO2 W2 EC2 AGH2.
destruct (push_facts (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm c B (vk1 + 1) PK) as (INV' & PV').
apply (grow_end_ct fx2 R2' M2 model2 s' sm e cr len); [| | exact HLn| | exact SV2| exact MO2| exact W2| exact EC2| exact INV'| exact PV'].
+ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; rewrite (KS1 2%nat) by PMK.inl; exact R2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; rewrite (KS1 9%nat) by PMK.inl; exact R9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; rewrite (KS1 18%nat) by PMK.inl; exact R18|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [| unfold PMBOS.CSK in Hk0; cbn in Hk0; repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]); destruct Hk0].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP| exact Hk0].
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
+ rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. rewrite R21.
rewrite L5.unsigned_lit by lia.
apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH2; lia|lia|lia|]. replace (fb + 408) with (fb + 40 + 368) by lia. exact C368.
Qed.
Lemma grow_cpy_i : ltac2:(TCodec.tc2 tcn__PmBo5 "UJ'QA&<y5'RAyR0%211%5241'2y8%611%311p061';'Q4'Q7'1&B'6'Q5&JvAvQFvR3r9%544321'4&QBr:&R@&QLu1%211%42N1%7261+Vme@%72O1%;3O31r;u:%:11%<2Q61%?241r4%?2Q71%C3Q731r<u;%B11%D2Q>1%G241&N%11L%H2Q@1%L3Q@41r=u<%K11%M2QG1%Q0241&QK+Q0&QM+2&O%11Q5%4231%7261%Q72QO1%Q;3QO:1r>uC%Q:11%Q<2R61%Q?241r7%Q?2R71%QC3R731r?uD%QB11%QD2R>1%QG241&QHr8%E1Q7%H2G1%K2J1%5241%621L%QM2RE1%R13RE91r@uE%R011%R22RL1%R5241%Q11Q:+1%@221%Q62Q51%Q92Q81%C2R>1%R:2S21%R>3S281&K%13RERD>&Iv9v?v:rA%56432RJRI1&GrB%2714GQ5Q=QLR5&Q=&QErC+8%Q52S11zvQO%7565321&H%13;>R6&Q6rE%R01:%R32R21%R62R51%Q@2QE1%64?51QN&Q<vR1&Q3vR<%22M1&FrD%R<11%QJ21Q;%443QB1R0%82Q31%;4:Q171&Q@vQGv7%332Q81'QC&C%115&Q;rJrI+eT[0rHrG%66Q954321v8%;4Q;921p0=1p0B1p0O1p0Q71p0Q:1p0QC1p0QG1p0QN1p0R11p0R?1p0RN1p0S71p0SG1p0T11p0T:1p0TG1pSNTN1p2U01pT2U21pT6U41pTNU61pTLU81pTDU:1pLU<1pQ2UB1pT:UI1").
Proof. intros fx R M model s1 sm e cr B c.
intros RA X1r X10 X11 X12 R19 R20 R21 SV MO GS ECZ PK PC CK OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4).
unfold hl_ceil in V4, GB1.
pose proof (GB3 vb1 (32 * 2 ^ vk1) VIN) as GAP.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
destruct (PMBK.copy_run_eq RSEGS 0xa9160 PMCPS.memcpy_copy1 fx R M B vb1 (32 * 2 ^ vk1) 0x376b0 X10 X11 X12 X1r) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & CP3 & KS3 & _).
{ split; [lia| reflexivity]. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
{ apply (L5.defined_sub M vb1 (32 * 2 ^ vk1)); [exact DB|lia|lia]. }
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx R 0xa9160 R3 0x376b0 M3 (fun a => B <= a < B + (32 * 2 ^ vk1)) K HH Mh Ml ltac:(lia) MS3 MG3 FR3).
{ intros a Pa. apply (PMK.cwr_block L ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) B (32 * 2 ^ (vk1 + 1)) a (or_introl eq_refl)). lia. }
{ intros a. apply PMK.rng_dec. }
intros HH3.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= B \/ B + (32 * 2 ^ vk1) <= a) -> L5C.agree_on M M3 a n).
{ intros a n H1 H2 H4 i Hi. apply FR3; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA3 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M3 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M3 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia].
- apply PMPK.dkr_grows. exact MG3.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GAP P2; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG3. }
assert (BK : PMBO1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M3 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG3)
as (RP3 & MO3).
{ intros i Hi N. apply FR3; [exact Hi|]. intros X. apply N. unfold PMBO1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA3. } { exact ITB. }
apply (grow_h_i fx R3 M3 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- split; [rewrite (KS3 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS3 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS3 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS3 18%nat) by PMK.inl; exact R18|].
intros k Hk0. rewrite (KS3 k); [apply KP; exact Hk0|]. unfold PMBOS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
- rewrite (KS3 19%nat) by PMK.inl. exact R19.
- rewrite (KS3 20%nat) by PMK.inl. exact R20.
- rewrite (KS3 21%nat) by PMK.inl. exact R21.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBOS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
- exact MO3.
- split; [exact RP3|]. split; [exact HH3|]. split; [exact MB|]. split; [exact STEP|]. split; [exact EE|].
split; [exact GB0|]. split; [exact GB16|]. split; [exact GB1|]. split; [exact GB2|]. split; [exact GB3|].
intros i Hi. apply MG3. apply GBD. exact Hi.
- apply (PMBK.ec_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia]|lia|lia| exact ECZ].
- exact PK.
- intros i Hi. cbn [PM.p_b PM.p_k] in Hi |- *. rewrite (CP3 i Hi). symmetry. apply FR3; [clear - Hi V0 V4 X3 Pp; lia|]. clear - Hi GAP P2 Pp. lia.
- cbn [PM.p_k] in PC |- *. apply (PMF.pstate_at_agree RSEGS M M3); [clear - GB0 GB1 X3 P2 Pp; lia|clear - GB0 GB1 X3 P2 Pp; lia| apply AGo; [clear - GB0 GB1 X3 P2 Pp; lia|clear - GB0 GB1 X3 P2 Pp; lia|lia]| exact PC].
- exact CK.
- exact OPD.
Qed.
Lemma grow_cpy_ct : ltac2:(TCodec.tc2 tcn__PmBo5 "V;'QA&<y5'RAyR0%211%5241'2y8%611%311p061';'Q4'Q7'1&B'6'Q5&JvAvQFvR3r:%544321'4&QBr;&R@&QLu1%211%42N1%7261+VnQ<%72O1%;3O31r<u:%:11%<2Q61%?241r5%?2Q71%C3Q731r=u;%B11%D2Q>1%G241&N%11L%H2Q@1%L3Q@41r>u<%K11%M2QG1%Q0241&QK+Q0&QM+2&O%11Q5%4231%7261%Q72QO1%Q;3QO:1r?uC%Q:11%Q<2R61%Q?241r6%Q?2R71%QC3R731'3&QIzr7%3221+`PPP0%5231%7231rAuD%QJ11%QL2RF1%QO241%QN2RFR3%R23RF21rBuE%R111%R32RM1%R6241&QH%Q31M%Q62Q51%Q92Q81%42R:1%521Q:%R;2S31%R?3S381rCuF%R>11%R@2S:1%RC241r@%Q@11+1%@221%QE2QD1%QH2QG1%C2R?1%RI2SA1%RM3SA91&K%13S4S3?&Iv9v?v:rD%56432S9S81&GrE%2714HQ5Q<CQL&Q=&QErF+8%Q52S@1vQO%65542QI1&H%13:=L&Q6rH%R>19%RA2R@1%RD2RC1%Q?2QD1%64>51QL&Q<vR1&Q3vR<%22L1&FrG%RJ11%QI21Q:%443QB1QO%82Q21%;4:Q071&Q@vQGv7%332Q71'QC&C%115&Q;rMrL+eT[0rKrJ%66Q854321v8%;4Q:921p0=1p0B1p0O1p0Q71p0Q:1p0QB1p0QF1p0QM1p0R01p0R?1p0RM1p0S51p0S>1p0SG1p0T71p0TA1p0TJ1p0U71pT@U?1pSNU?1p2UA1pT2UC1pT6UE1pTNUG1pTLUI1pTDUK1pLUM1pQ2V31pT:V:1").
Proof. intros fx R M model s1 sm e cr B c len.
intros RA X1r X10 X11 X12 R19 HLn R20 R21 R22 SV MO GS ECZ PK PC CK OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4).
unfold hl_ceil in V4, GB1.
pose proof (GB3 vb1 (32 * 2 ^ vk1) VIN) as GAP.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
destruct (PMBK.copy_run_eq RSEGS 0xa9160 PMCPS.memcpy_copy1 fx R M B vb1 (32 * 2 ^ vk1) 0x3782c X10 X11 X12 X1r) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & CP3 & KS3 & _).
{ split; [lia| reflexivity]. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
{ apply (L5.defined_sub M vb1 (32 * 2 ^ vk1)); [exact DB|lia|lia]. }
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx R 0xa9160 R3 0x3782c M3 (fun a => B <= a < B + (32 * 2 ^ vk1)) K HH Mh Ml ltac:(lia) MS3 MG3 FR3).
{ intros a Pa. apply (PMK.cwr_block L ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) B (32 * 2 ^ (vk1 + 1)) a (or_introl eq_refl)). lia. }
{ intros a. apply PMK.rng_dec. }
intros HH3.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= B \/ B + (32 * 2 ^ vk1) <= a) -> L5C.agree_on M M3 a n).
{ intros a n H1 H2 H4 i Hi. apply FR3; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA3 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M3 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M3 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia].
- apply PMPK.dkr_grows. exact MG3.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GAP P2; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG3. }
assert (BK : PMBO1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M3 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG3)
as (RP3 & MO3).
{ intros i Hi N. apply FR3; [exact Hi|]. intros X. apply N. unfold PMBO1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA3. } { exact ITB. }
apply (grow_h_ct fx R3 M3 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c len).
- split; [rewrite (KS3 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS3 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS3 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS3 18%nat) by PMK.inl; exact R18|].
intros k Hk0. rewrite (KS3 k); [apply KP; exact Hk0|]. unfold PMBOS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
- rewrite (KS3 19%nat) by PMK.inl. exact R19.
- exact HLn.
- rewrite (KS3 20%nat) by PMK.inl. exact R20.
- rewrite (KS3 21%nat) by PMK.inl. exact R21.
- rewrite (KS3 22%nat) by PMK.inl. exact R22.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBOS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
- exact MO3.
- split; [exact RP3|]. split; [exact HH3|]. split; [exact MB|]. split; [exact STEP|]. split; [exact EE|].
split; [exact GB0|]. split; [exact GB16|]. split; [exact GB1|]. split; [exact GB2|]. split; [exact GB3|].
intros i Hi. apply MG3. apply GBD. exact Hi.
- apply (PMBK.ec_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia]|lia|lia| exact ECZ].
- exact PK.
- intros i Hi. cbn [PM.p_b PM.p_k] in Hi |- *. rewrite (CP3 i Hi). symmetry. apply FR3; [clear - Hi V0 V4 X3 Pp; lia|]. clear - Hi GAP P2 Pp. lia.
- cbn [PM.p_k] in PC |- *. apply (PMF.pstate_at_agree RSEGS M M3); [clear - GB0 GB1 X3 P2 Pp; lia|clear - GB0 GB1 X3 P2 Pp; lia| apply AGo; [clear - GB0 GB1 X3 P2 Pp; lia|clear - GB0 GB1 X3 P2 Pp; lia|lia]| exact PC].
- exact CK.
- exact OPD.
Qed.
End Call.
End WithHeap.
End PMBO5.

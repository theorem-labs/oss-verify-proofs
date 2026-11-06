(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit
PmCertKitG PmSrcUMemmove PmBaKit PmBoUStmts PmBoU1 PmBoU2 PmBoU4 PmBoUP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU1.PMBOU1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU2.PMBOU2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU5.PMBOU5.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1option"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"]; ["0R"; "0R0"; "6credit"; "7SCFG"; "8FPB"; "8blk_ok"; "9push_st"; ":gstate"; ":pushok"; ":sof"; ";kept0"; ";mem_ok"; ";saves"; "<ADDR_U"; "=inv"; "=p_b"]; ["=p_k"; "=p_tb"; "=p_tg"; "=parser_at"; "=pot_parser"; "=pst"; "=pstate"; "=pstate_at"; "=strm"; "=tb_ok"; ">T3"; ">T4"; ">cfg"; ">credit_keep"; ">ec_at"; ">prog_value"]; [">run_pre"; "?opdel_spec"; "@FPState"; "@getr"; "Asrealizes"; "Bmem_grows"; "Cloaded_segments"; "0S"; "0SCFG_P"; "Dadd"; "Dle"; "Dlt"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"]; ["0c"; "0cat"; "0cr"; "0cr0"; "0e"; "0fb"; "0fx"; "0i"; "0k"; "0len"; "0m"; "0model"; "0s"; "0s'"; "0s0"; "0s1"]; ["0sm"; "0sm0"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0str"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU5.
Import PMU.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBOU2.push_st.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis PRE : PMBOUS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBOUS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBOUS.kept0 R0).
Local Abbreviation regs_at := (PMBOUS.regs_at R0 S fb).
Local Abbreviation saves := (PMBOUS.saves R0 S).
Local Abbreviation mem_ok := (PMBOUS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBOUS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBOUS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBOU1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBOU1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBOU1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBOU1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBOU1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBOU1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBOU1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBOU1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBOU2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBOU2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBOU2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU5 "B'RCyR0%211'3&QJz&RDr1%2271%5241&QK&QN+2+R0%3221%5271%=271pU>?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBOUP2.aligned; first [assumption | lia]].
Local Ltac prep_ctx M W MO :=
let PA := fresh "PA" in let IA := fresh "IA" in let VIS := fresh "VIS" in let VREF := fresh "VREF" in let BASE := fresh "BASE" in
let ERR := fresh "ERR" in let TB := fresh "TB" in let HH := fresh "HH" in let MB := fresh "MB" in let STEP := fresh "STEP" in
let EE := fresh "EE" in let CK := fresh "CK" in let EK := fresh "EK" in let DK := fresh "DK" in let STK := fresh "STK" in
pose proof W as ((PA & IA & VIS & VREF & BASE & ERR & TB) & HH & MB & STEP & EE & CK);
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF; cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF;
unfold PMSP.visitor_at in VIS; cbn [pa_vp_visitor AD PmLayoutU.ADDR_U] in VIS;
pose proof MO as (EK & DK & STK);
let MOK := fresh "MOK" in pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK;
let Mh := fresh "Mh" in let Ml := fresh "Ml" in pose proof MOK as (Mh & Ml & _);
let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in pose proof FOK as (F1 & F2 & F3);
let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in let X4 := fresh "X4" in let X5 := fresh "X5" in
pose proof SBND as (X1 & X2 & X3 & X4 & X5);
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBOUS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBOU1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBOU1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBOU1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBOU1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBOU1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBOU1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBOU1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_del := PMBOU4.grow_del L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
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
Lemma push_facts : ltac2:(TCodec.tc2 tcn__PmBoU5 "K'Q5'Q8'Q6'6&Hr5r4r3%43321'3&N&Fr6r2%342718%511&Q?vR>vRA%34251>%;251p0=1pTBC1p2D1pT2F1pU2H1pU0J1").
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
Lemma keep_objs : ltac2:(TCodec.tc2 tcn__PmBoU5 "S3'RCyR0%211'2y8%511%311p051'Q5'Q8'1'6&Q@&QF&Mr8vR5r6vREr4r3%9887654321&Kv9v?v:vQGr9%665432<1&QEr:%2214'3&QJzr1%3221&QK&QN+2+R0%3221%5271%;271&5&Dr7r2%35FQ02O1%511'4r=&RB%12QDQ1%311r>%113%73QC31p091p0@1pT@QA1&Er5%24Q8Q6Q>1&Q3&Q:&Q;r<&QI+Q8%22QF1+]H%42QH1%98QLQK87631Q;&Q9&Q1r;%211&Q2%113%6231%R58R4R3JR1>QO5QC%QL6QKQJQIQHR2K%QC221p041p0<1p0G1p0K1p0QI1p0QM1p0R51pTFR@1p2RA1pT:RC1pU2RE1pTLRG1pTJRH1pNRJ1pLRK1").
Proof. intros M M' s s' sm e B m.
intros RP (EK & DK & STK) MG FR BK PA' TB'.
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
assert (EKP : PMK.ek L LBX S SCR (PMBOU1.WP fb) M M') by exact (ek_fp M M' B m FR BK).
assert (SC0 : 0 <= SCR) by (unfold PMBOUS.SCR; lia).
assert (NW : forall a n, fb + 424 <= a -> forall i, a <= i < a + n -> ~ PMK.inW (PMBOU1.WP fb) i).
{ intros a n H1 i Hi (r0 & Hr & Hin). unfold PMBOU1.WP in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
destruct RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
split.
- unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [exact PA'|].
split. { apply (PMFR.iss_keep RSEGS AD L KL LBX S SCR (PMBOU1.WP fb) M M' EKP STK SC0 brx WP_hi); [lia|lia| |exact INCS| exact IA]. apply NW. lia. }
split. { apply (PMFR.visitor_keep RSEGS AD L KL LBX S SCR (PMBOU1.WP fb) M M' EKP STK SC0); [lia|lia| |exact VIS]. apply NW. lia. }
split. { apply (PMFR.u64_keep RSEGS L KL LBX S SCR (PMBOU1.WP fb) M M' EKP STK SC0); [lia|lia| |exact VREF]. apply NW. lia. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX S SCR (PMBOU1.WP fb) M M' EKP); [| | | | exact BASE].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros (r0 & Hr & Hin); unfold PMBOU1.WP in Hr;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha;
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
split; [|exact TB'].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX S SCR (PMBOU1.WP fb) M M' EKP); [| | exact ERR].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros (r0 & Hr & Hin); unfold PMBOU1.WP in Hr;
cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha;
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
- split; [|split].
+ apply (PMK.ek_trans L LBX S SCR _ M0 M M' EK).
apply (PMK.ek_weaken L LBX LBX S SCR S SCR _ (PMBOU1.WP fb) M M' EKP); [apply incl_refl| intros x Hx; exact Hx| exact WP_run].
+ apply (PMK.dk_trans L LBX S SCR M0 M M' DK). apply PMK.dk_grows. exact MG.
+ exact (PMK.stk_grows L M M' S SCR MG STK).
Qed.
Definition sof (M : word -> option byte) (B sz raS : Z) : Prop :=
L5.u64_at RSEGS M (S - 96) B /\ L5.u64_at RSEGS M (S - 88) (B + sz) /\ L5.u64_at RSEGS M (S - 80) (B + sz + 32)
/\ L5.u64_at RSEGS M (S - 72) (B + 2 * sz) /\ L5.u64_at RSEGS M (S - 64) (fb + 400) /\ L5.u64_at RSEGS M (S - 120) raS
/\ L5.u64_at RSEGS M (S - 128) (fb + 40) /\ L5.u64_at RSEGS M (S - 136) (fb + 8) /\ L5.u64_at RSEGS M (S - 144) (fb + 432).
Lemma grow_h_i : ltac2:(TCodec.tc2 tcn__PmBoU5 "V5'QB&<y5'RCyR0%211%5241'2y8%611%311p061';'Q5'Q8'1&B'6'Q6'4&QCr9&RB&QMu2%211%42H1%7261&QOvQG+T@%3221%:2L1%>3L61r:u8%=11%?2Q31%B241+S0%<2;1%C2Q51%G3Q541r;u9%F11%H2Q<1%K241&QIvR5+\@%3221%N2Q@1%Q23Q@61r<uB%Q111%Q32QG1%Q6241r5%Q62QH1%Q:3QH31r=uE%Q911%Q;2QO1%Q>241+Qo`0%Q>2R01%QB3R031&JvAr>%3221r?uC%QE11%QG2R;1%QJ241%QL3R:1K&I&QL+Q0&QN+2&Q0%11H%4231%7261+WQ\8%:4@R521&Lr@%23FR01&Kv9v?v:rA%56432R6QB1&GrB%2714:LNQ8Q@&Q>&QFrC+8%QK2QJ1zvR1%7565321&H%13;>QB'3&QJr1%2281&QKrD%Q211%Q52Q41%Q82Q71%5271%:271rGr2%R>2L1%S92SK1%411&OrE%211%RD217%S?2T11%:11%SD3SM71p0=1pT@SH1&Q7rF%RL2Q@C%34Q521R3&Q=vR3&Q4vR>%22QC1&F%QO1B+1%S6221%44EQE1QK%82QI1%;4:QD71&QAvQHv7%332QN1'QD&C%115&Q<rKrJ+Vhh8rIrH%66QO54321v8%;4R1921p0=1p0B1p0O1p0Q41p0QN1p0R11p0R:1p0R>1p0RE1p0RI1p0S51p0S<1p0SA1p0SJ1p0T31p0T?1p0TI1pT2U91p2U;1pT6U=1pT:U?1pU2UA1pU0UC1pTHUE1pLUG1pQ2UM1pT>V41").
Proof. intros fx R M model s1 sm e cr B c.
intros X2 X8 X9 X18 X21 KP X19 SO SV MO GS ECZ PK CP PC CK OPD.
pose proof SO as (O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBOUS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
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
cfeed P (PMBOUP2.uboIH_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & _ & T18 & T19 & C72 & C96 & C376 & C80 & C368 & C88 & C360 & C64 & C120 & C128 & C136 & C144).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x36308 R1 0x55454 M1
(fun a => (fb + 40 + 360 <= a < fb + 40 + 360 + 24) \/ (S - 144 <= a < S - 144 + 88)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 400 \/ fb + 424 <= a) -> (a + n <= S - 144 \/ S - 56 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
set (s' := push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) B (vk1 + 1) c).
assert (VEC1 : PM.vec_at RSEGS PMSP.T3 PMSP.T4 M1 (fb + 40 + 360) B (vk1 + 1) (stk1 ++ [c])).
{ apply (PMBK.vec_grow RSEGS M M1 (fb + 40 + 360) vb1 vk1 stk1 c B PVEC HL); [lia|lia|lia|lia|lia|lia| | | | | |].
- exact C360.
- replace (fb + 40 + 360 + 8) with (fb + 40 + 368) by lia. exact C368.
- replace (fb + 40 + 360 + 16) with (fb + 40 + 376) by lia. replace (B + 32 * 2 ^ (vk1 + 1)) with (B + 2 * (32 * 2 ^ vk1)) by lia. exact C376.
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
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBOU1.FPB; [right; right; left; lia| left; unfold PMBOUS.SCR; lia]. }
{ left; reflexivity. }
{ exact PA1. }
{ exact ITB. }
apply (grow_del 0x38594 fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- exact T1.
- split; [lia| reflexivity].
- split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact X21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T10.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
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
apply (tail_i fx2 R2' M2 model2 s' sm e cr); [| | exact SV2| exact MO2| exact W2| exact EC2| exact INV'| exact PV'].
+ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; exact T2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; exact T8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; exact T9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; exact T18|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl; rewrite (KS1 21%nat) by PMK.inl; exact X21|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [| unfold PMBOUS.CSK in Hk0; cbn in Hk0; repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]); destruct Hk0].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP| exact Hk0].
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite T19. f_equal. unfold s', push_st. cbn [PM.p_b PM.p_stk].
rewrite length_app, Nat2Z.inj_add. cbn [length]. rewrite HL. lia.
Qed.
Lemma grow_h_c : ltac2:(TCodec.tc2 tcn__PmBoU5 "VF'QB&<y5'RCyR0%211%5241'2y8%611%311p061';'Q5'Q8'1&B'6'Q6'4&QCr:&RB&QMu2%211%42H1%7261&QOvQG+T@%3221%:2L1%>3L61r;u8%=11%?2Q31%B241+S0%<2;1%C2Q51%G3Q541r<u9%F11%H2Q<1%K241&QIvR5+\@%3221%N2Q@1%Q23Q@61r=uB%Q111%Q32QG1%Q6241r6%Q62QH1%Q:3QH31r>uE%Q911%Q;2QO1%Q>241+Qo`0%Q>2R01%QB3R031&JvAr?%3221r@uC%QE11%QG2R;1%QJ241r7%QJ2R<1%QN3R<31'3&QJzr8%3221+`PPP0%5231%7231rBuD%R511%R72RK1%R:241%R<3RJ1Q;&I&QL+Q0&QN+2&Q0%11L%4231%7261+WQdL%:4@QO21&LrC%23Q6R@1&Kv9v?v:rD%56432RFR21&GrErA%3725;M1Q=Q?&Q>&QFrF+8%R<2R;1vR1%65542Q:1&H%13;>QFr1%Q?2Q>1&QKrG%Q011%Q32Q21%Q62Q51%5271%QG271rJr2%RL2J1%SG2T91%411&OrH%211%S2217%SM2T?1%:11%T23T;71p0=1pT@T61&Q7rI%S:2Q>C%34Q221R1&Q=vR3&Q4vR>%22QA1&F%QM1B+1%SD221%44EQC1QI%82QG1%;4:QB71&QAvQHv7%332QL1'QD&C%115&Q<rNrM+Vhh8rLrK%66QL54321v8%;4QN921p0=1p0B1p0O1p0Q41p0QL1p0QO1p0R71p0R<1p0RC1p0RG1p0S31p0S:1p0SC1p0SL1p0T11p0T:1p0TC1p0TO1p0U91pTDUJ1pT2UJ1p2UL1pT6UN1pT:V01pU2V21pU0V41pTHV61pLV81pQ2V>1pT>VE1").
Proof. intros fx R M model s1 sm e cr B c len.
intros X2 X8 X9 X18 X21 KP X19 HLn X20 SO SV MO GS ECZ PK CP PC CK OPD.
pose proof SO as (O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBOUS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
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
cfeed P (PMBOUP2.uboCH_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & _ & T18 & T20 & C72 & C96 & C376 & C80 & C368 & C88 & C360 & C64 & C120 & C128 & C136 & C144).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x36308 R1 0x55454 M1
(fun a => (fb + 40 + 360 <= a < fb + 40 + 360 + 24) \/ (S - 144 <= a < S - 144 + 88)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 400 \/ fb + 424 <= a) -> (a + n <= S - 144 \/ S - 56 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
set (s' := push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) B (vk1 + 1) c).
assert (VEC1 : PM.vec_at RSEGS PMSP.T3 PMSP.T4 M1 (fb + 40 + 360) B (vk1 + 1) (stk1 ++ [c])).
{ apply (PMBK.vec_grow RSEGS M M1 (fb + 40 + 360) vb1 vk1 stk1 c B PVEC HL); [lia|lia|lia|lia|lia|lia| | | | | |].
- exact C360.
- replace (fb + 40 + 360 + 8) with (fb + 40 + 368) by lia. exact C368.
- replace (fb + 40 + 360 + 16) with (fb + 40 + 376) by lia. replace (B + 32 * 2 ^ (vk1 + 1)) with (B + 2 * (32 * 2 ^ vk1)) by lia. exact C376.
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
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBOU1.FPB; [right; right; left; lia| left; unfold PMBOUS.SCR; lia]. }
{ left; reflexivity. }
{ exact PA1. }
{ exact ITB. }
apply (grow_del 0x3873c fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- exact T1.
- split; [lia| reflexivity].
- split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact X21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T10.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
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
apply (tail_ct fx2 R2' M2 model2 s' sm e cr len); [| | exact HLn| | exact SV2| exact MO2| exact W2| exact EC2| exact INV'| exact PV'].
+ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; exact T2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; exact T8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; exact T9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; exact T18|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl; rewrite (KS1 21%nat) by PMK.inl; exact X21|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [| unfold PMBOUS.CSK in Hk0; cbn in Hk0; repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]); destruct Hk0].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP| exact Hk0].
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact X19.
+ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite T20. f_equal. unfold s', push_st. cbn [PM.p_b PM.p_stk].
rewrite length_app, Nat2Z.inj_add. cbn [length]. rewrite HL. lia.
Qed.
Lemma grow_h_t : ltac2:(TCodec.tc2 tcn__PmBoU5 "VF'QB&<y5'RCyR0%211%5241'2y8%611%311p061';'Q5'Q8'1&B'6'Q6'4&QCr:&RB&QMu2%211%42H1%7261&QOvQG+T@%3221%:2L1%>3L61r;u8%=11%?2Q31%B241+S0%<2;1%C2Q51%G3Q541r<u9%F11%H2Q<1%K241&QIvR5+\@%3221%N2Q@1%Q23Q@61r=uB%Q111%Q32QG1%Q6241r6%Q62QH1%Q:3QH31r>uE%Q911%Q;2QO1%Q>241+Qo`0%Q>2R01%QB3R031&JvAr?%3221r@uC%QE11%QG2R;1%QJ241r7%QJ2R<1%QN3R<31'3&QJzr8%3221+`PPP0%5231%7231rBuD%R511%R72RK1%R:241%R<3RJ1Q;&I&QL+Q0&QN+2&Q0%11L%4231%7261+WQi@%:4@QO21&LrC%23Q6R@1&Kv9v?v:rD%56432RFR21&GrErA%3725;M1Q=Q?&Q>&QFrF+8%R<2R;1vR1%65542Q:1&H%13;>QFr1%Q?2Q>1&QKrG%Q011%Q32Q21%Q62Q51%5271%QG271rJr2%RL2J1%SG2T91%411&OrH%211%S2217%SM2T?1%:11%T23T;71p0=1pT@T61&Q7rI%S:2Q>C%34Q221R1&Q=vR3&Q4vR>%22QA1&F%QM1B+1%SD221%44EQC1QI%82QG1%;4:QB71&QAvQHv7%332QL1'QD&C%115&Q<rNrM+Vhh8rLrK%66QL54321v8%;4QN921p0=1p0B1p0O1p0Q41p0QL1p0QO1p0R71p0R<1p0RC1p0RG1p0S31p0S:1p0SC1p0SL1p0T11p0T:1p0TC1p0TO1p0U91pTDUJ1pT2UJ1p2UL1pT6UN1pT:V01pU2V21pU0V41pTHV61pLV81pQ2V>1pT>VE1").
Proof. intros fx R M model s1 sm e cr B c len.
intros X2 X8 X9 X18 X21 KP X19 HLn X20 SO SV MO GS ECZ PK CP PC CK OPD.
pose proof SO as (O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBOUS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
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
cfeed P (PMBOUP2.uboTH_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & _ & T18 & T20 & C72 & C96 & C376 & C80 & C368 & C88 & C360 & C64 & C120 & C128 & C136 & C144).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x36308 R1 0x55454 M1
(fun a => (fb + 40 + 360 <= a < fb + 40 + 360 + 24) \/ (S - 144 <= a < S - 144 + 88)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 400 \/ fb + 424 <= a) -> (a + n <= S - 144 \/ S - 56 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
set (s' := push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) B (vk1 + 1) c).
assert (VEC1 : PM.vec_at RSEGS PMSP.T3 PMSP.T4 M1 (fb + 40 + 360) B (vk1 + 1) (stk1 ++ [c])).
{ apply (PMBK.vec_grow RSEGS M M1 (fb + 40 + 360) vb1 vk1 stk1 c B PVEC HL); [lia|lia|lia|lia|lia|lia| | | | | |].
- exact C360.
- replace (fb + 40 + 360 + 8) with (fb + 40 + 368) by lia. exact C368.
- replace (fb + 40 + 360 + 16) with (fb + 40 + 376) by lia. replace (B + 32 * 2 ^ (vk1 + 1)) with (B + 2 * (32 * 2 ^ vk1)) by lia. exact C376.
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
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBOU1.FPB; [right; right; left; lia| left; unfold PMBOUS.SCR; lia]. }
{ left; reflexivity. }
{ exact PA1. }
{ exact ITB. }
apply (grow_del 0x3873c fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- exact T1.
- split; [lia| reflexivity].
- split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact X21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T10.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
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
apply (tail_ct fx2 R2' M2 model2 s' sm e cr len); [| | exact HLn| | exact SV2| exact MO2| exact W2| exact EC2| exact INV'| exact PV'].
+ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; exact T2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; exact T8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; exact T9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; exact T18|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl; rewrite (KS1 21%nat) by PMK.inl; exact X21|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [| unfold PMBOUS.CSK in Hk0; cbn in Hk0; repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]); destruct Hk0].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP| exact Hk0].
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact X19.
+ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite T20. f_equal. unfold s', push_st. cbn [PM.p_b PM.p_stk].
rewrite length_app, Nat2Z.inj_add. cbn [length]. rewrite HL. lia.
Qed.
End Call.
End WithHeap.
End PMBOU5.

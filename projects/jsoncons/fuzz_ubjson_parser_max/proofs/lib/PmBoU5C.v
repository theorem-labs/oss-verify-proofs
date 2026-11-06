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
PmCertKitG PmSrcUMemmove PmBaKit PmBoUStmts PmBoU1 PmBoU2 PmBoU4 PmBoU5 PmBoUP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU5C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU2.PMBOU2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU5.PMBOU5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1option"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"]; ["6credit"; "7SCFG"; "8push_st"; "9gstate"; "9pushok"; "9sof"; ":kept0"; ":mem_ok"; ":saves"; ";p_b"; ";p_k"; ";pot_parser"; ";pst"; ";pstate"; ";pstate_at"; ";strm"]; ["<cfg"; "<credit_keep"; "<ec_at"; "=opdel_spec"; ">FPState"; ">getr"; "?srealizes"; "@loaded_segments"; "0S"; "0SCFG_P"; "Aadd"; "Ale"; "Alt"; "Amul"; "Aof_nat"; "Apow"]; ["Asub"; "0c"; "0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"; "0fx"; "0len"; "0model"; "0model0"; "0s0"; "0s1"; "0sm"; "0sm0"]; ["BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0str"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU5C.
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
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU5C "B'R1yR0%211'3&Q;z&R2r1%2271%5241&Q<&Q?+2+R0%3221%5271%=271pT:?1").
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
Let keep_objs := PMBOU5.keep_objs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_facts := PMBOU5.push_facts L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_h_i := PMBOU5.grow_h_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_h_c := PMBOU5.grow_h_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_h_t := PMBOU5.grow_h_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Abbreviation gstate := (PMBOU5.gstate L HI model0 LBX fb s0 str sm0 e0).
Local Abbreviation pushok := (PMBOU5.pushok s0 sm0).
Local Abbreviation sof := (PMBOU5.sof S fb).
Lemma grow_cpy_i : ltac2:(TCodec.tc2 tcn__PmBoU5C "VI'Q4&;y5'R1yR0%211%5241'2y8%611%311p061':'L'O'1&@'5'M'4&Q5r9&R0&Q>u1%211%42H1%7261+Vhh8%72I1%;3I31r:u2%:11%<2Q01%?241&Q@vQ8+T@%3221%B2Q41%F3Q461r;u8%E11%G2Q;1%J241+S0%<2;1%K2Q=1%O3Q=41r<u9%N11%Q02QD1%Q3241&Q:vQG+\@%3221%Q62QH1%Q:3QH61r=uB%Q911%Q;2QO1%Q>241r6%Q>2R01%QB3R031r>uE%QA11%QC2R71%QF241+Qo`0%QF2R81%QJ3R831&Fv?r?%3221r@uC%QM11%QO2RC1%R2241%R43RB1KrAu:%R311%R52RI1%R8241%R72RIQN%R;3RI21rBu;%R:11%R<2S01%R?241&I%11E%R@2S21%RD3S241rCu<%RC11%RE2S91%RH241&Q=+Q0&Q?+2&J%11Q0%4231%7261%RO2SA1%S33SA:1&E%71Q0%:291%=2<1+WQ\8%56RGR3DQN21&HrD%23Q@RJ1&Gv8v=v9rE%56432S0R<1&Cv6vQKvQLvR3vQOvQFrF%8@=76;RE54321:@Q6Q?QFQL&Q2&Q7rG+8%RK2RJ1zvQB%7565321&D%15?=;DR0&NrI%Q:1:%Q=2Q<1%Q@2Q?1%S62QF1%64?51R0&Q1vQD&K%12Q2J&BrH%QE11+1%S@221%544Q;1R1%82Q91%;4:Q781&Q3vQ9%231Q=Q7'Q6&A%114&Q0rNrM+eX]DrLrK%66Q854321v7%;4Q:921p0=1p0A1p0N1p0Q61p0Q91p0QB1p0QL1p0R31p0R71p0R>1p0RN1p0S81p0S@1p0SG1p0SL1p0T51p0T>1p0TJ1p0U41p0U@1pS4UM1p2UO1pS8V11pS<V31pSNV51pSLV71pSFV91pJV;1pNVA1pSBVH1").
Proof. intros fx R M model s1 sm e cr B c.
intros X1r X2 X8 X9 X18 X21 KP X19 X10 X11 X12 SO SV MO GS ECZ PK PC CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
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
destruct (PMBK.copy_run_eq RSEGS 0xaa1b4 OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSrcUMemmove.PMCPS.memcpy_copy1 fx R M B vb1 (32 * 2 ^ vk1) 0x36308 X10 X11 X12 X1r) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & CP3 & KS3 & _).
{ split; [lia| reflexivity]. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
{ apply (L5.defined_sub M vb1 (32 * 2 ^ vk1)); [exact DB|lia|lia]. }
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx R 0xaa1b4 R3 0x36308 M3 (fun a => B <= a < B + (32 * 2 ^ vk1)) K HH Mh Ml ltac:(lia) MS3 MG3 FR3).
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
assert (BK : PMBOU1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M3 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG3)
as (RP3 & MO3).
{ intros i Hi N. apply FR3; [exact Hi|]. intros X. apply N. unfold PMBOU1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA3. } { exact ITB. }
assert (AGs : forall a n, S - 144 <= a -> a + n <= S -> L5C.agree_on M M3 a n) by (intros a n H1 H2; apply AGo; [lia|lia| clear - H1 GB1 X5 P2 Pp; lia]).
apply (grow_h_i fx R3 M3 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c).
- rewrite (KS3 2%nat) by PMK.inl. exact X2.
- rewrite (KS3 8%nat) by PMK.inl. exact X8.
- rewrite (KS3 9%nat) by PMK.inl. exact X9.
- rewrite (KS3 18%nat) by PMK.inl. exact X18.
- rewrite (KS3 21%nat) by PMK.inl. exact X21.
- intros k Hk0. rewrite (KS3 k); [apply KP; exact Hk0|]. unfold PMBOUS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
- rewrite (KS3 19%nat) by PMK.inl. exact X19.
- pose proof SO as (O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
unfold PMBOU5.sof. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGs; lia|lia|lia|assumption]).
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
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
Lemma grow_cpy_c : ltac2:(TCodec.tc2 tcn__PmBoU5C "W<'Q4&;y5'R1yR0%211%5241'2y8%611%311p061':'L'O'1&@'5'M'4&Q5r:&R0&Q>u1%211%42H1%7261+Vhh8%72I1%;3I31r;u2%:11%<2Q01%?241&Q@vQ8+T@%3221%B2Q41%F3Q461r<u8%E11%G2Q;1%J241+S0%<2;1%K2Q=1%O3Q=41r=u9%N11%Q02QD1%Q3241&Q:vQG+\@%3221%Q62QH1%Q:3QH61r>uB%Q911%Q;2QO1%Q>241r7%Q>2R01%QB3R031r?uE%QA11%QC2R71%QF241+Qo`0%QF2R81%QJ3R831&Fv?r@%3221rAuC%QM11%QO2RC1%R2241r8%R22RD1%R63RD31'3&Q;zr9%3221+`PPP0%5231%7231rCuD%R=11%R?2S31%RB241%RD3S21Q;rDu:%RC11%RE2S91%RH241%RG2S9QJ%RK3S921rEu;%RJ11%RL2S@1%RO241&IrB%211%S12SC1%S53SC51rFu<%S411%S62SJ1%S9241&Q=+Q0&Q?+2&J%11Q1%4231%7261%S@2T21%SD3T2:1&E%71Q1%:291%=2<1+WQdL%56S8RDDQM21&HrG%23R1S;1&Gv8v=v9rH%56432SARM1&Cv6vQKvQLvR3vQOvQFrI%8@=76;S654321:@Q6Q@QGQM&Q2&Q7rJ+8%S<2S;1vQB%65542R:1&D%15><:CR0&NrL%Q919%Q<2Q;1%Q?2Q>1%SF2QE1%64>51R0&Q1vQD&K%12Q1I&BrK%QD11+1%T0221%544Q:1R0%82Q81%;4:Q681&Q3vQ9%231Q<Q6'Q6&A%114&Q0rQ1rQ0+eX]DrOrN%66Q754321v7%;4Q9921p0=1p0A1p0N1p0Q61p0Q91p0QA1p0QK1p0R21p0R61p0R=1p0RM1p0S81p0S@1p0SG1p0T01p0T91p0T>1p0TG1p0U01p0U<1p0UF1p0V21pSDV@1pS4V@1p2VB1pS8VD1pS<VF1pSNVH1pSLVJ1pSFVL1pJVN1pNW41pSBW;1").
Proof. intros fx R M model s1 sm e cr B c len.
intros X1r X2 X8 X9 X18 X21 KP X19 HLn X20 X10 X11 X12 SO SV MO GS ECZ PK PC CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
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
destruct (PMBK.copy_run_eq RSEGS 0xaa1b4 OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSrcUMemmove.PMCPS.memcpy_copy1 fx R M B vb1 (32 * 2 ^ vk1) 0x36308 X10 X11 X12 X1r) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & CP3 & KS3 & _).
{ split; [lia| reflexivity]. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
{ apply (L5.defined_sub M vb1 (32 * 2 ^ vk1)); [exact DB|lia|lia]. }
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx R 0xaa1b4 R3 0x36308 M3 (fun a => B <= a < B + (32 * 2 ^ vk1)) K HH Mh Ml ltac:(lia) MS3 MG3 FR3).
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
assert (BK : PMBOU1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M3 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG3)
as (RP3 & MO3).
{ intros i Hi N. apply FR3; [exact Hi|]. intros X. apply N. unfold PMBOU1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA3. } { exact ITB. }
assert (AGs : forall a n, S - 144 <= a -> a + n <= S -> L5C.agree_on M M3 a n) by (intros a n H1 H2; apply AGo; [lia|lia| clear - H1 GB1 X5 P2 Pp; lia]).
apply (grow_h_c fx R3 M3 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c len).
- rewrite (KS3 2%nat) by PMK.inl. exact X2.
- rewrite (KS3 8%nat) by PMK.inl. exact X8.
- rewrite (KS3 9%nat) by PMK.inl. exact X9.
- rewrite (KS3 18%nat) by PMK.inl. exact X18.
- rewrite (KS3 21%nat) by PMK.inl. exact X21.
- intros k Hk0. rewrite (KS3 k); [apply KP; exact Hk0|]. unfold PMBOUS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
- rewrite (KS3 19%nat) by PMK.inl. exact X19.
- exact HLn.
- rewrite (KS3 20%nat) by PMK.inl. exact X20.
- pose proof SO as (O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
unfold PMBOU5.sof. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGs; lia|lia|lia|assumption]).
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
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
Lemma grow_cpy_t : ltac2:(TCodec.tc2 tcn__PmBoU5C "W<'Q4&;y5'R1yR0%211%5241'2y8%611%311p061':'L'O'1&@'5'M'4&Q5r:&R0&Q>u1%211%42H1%7261+Vhh8%72I1%;3I31r;u2%:11%<2Q01%?241&Q@vQ8+T@%3221%B2Q41%F3Q461r<u8%E11%G2Q;1%J241+S0%<2;1%K2Q=1%O3Q=41r=u9%N11%Q02QD1%Q3241&Q:vQG+\@%3221%Q62QH1%Q:3QH61r>uB%Q911%Q;2QO1%Q>241r7%Q>2R01%QB3R031r?uE%QA11%QC2R71%QF241+Qo`0%QF2R81%QJ3R831&Fv?r@%3221rAuC%QM11%QO2RC1%R2241r8%R22RD1%R63RD31'3&Q;zr9%3221+`PPP0%5231%7231rCuD%R=11%R?2S31%RB241%RD3S21Q;rDu:%RC11%RE2S91%RH241%RG2S9QJ%RK3S921rEu;%RJ11%RL2S@1%RO241&IrB%211%S12SC1%S53SC51rFu<%S411%S62SJ1%S9241&Q=+Q0&Q?+2&J%11Q1%4231%7261%S@2T21%SD3T2:1&E%71Q1%:291%=2<1+WQi@%56S8RDDQM21&HrG%23R1S;1&Gv8v=v9rH%56432SARM1&Cv6vQKvQLvR3vQOvQFrI%8@=76;S654321:@Q6Q@QGQM&Q2&Q7rJ+8%S<2S;1vQB%65542R:1&D%15><:CR0&NrL%Q919%Q<2Q;1%Q?2Q>1%SF2QE1%64>51R0&Q1vQD&K%12Q1I&BrK%QD11+1%T0221%544Q:1R0%82Q81%;4:Q681&Q3vQ9%231Q<Q6'Q6&A%114&Q0rQ1rQ0+eX]DrOrN%66Q754321v7%;4Q9921p0=1p0A1p0N1p0Q61p0Q91p0QA1p0QK1p0R21p0R61p0R=1p0RM1p0S81p0S@1p0SG1p0T01p0T91p0T>1p0TG1p0U01p0U<1p0UF1p0V21pSDV@1pS4V@1p2VB1pS8VD1pS<VF1pSNVH1pSLVJ1pSFVL1pJVN1pNW41pSBW;1").
Proof. intros fx R M model s1 sm e cr B c len.
intros X1r X2 X8 X9 X18 X21 KP X19 HLn X20 X10 X11 X12 SO SV MO GS ECZ PK PC CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
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
destruct (PMBK.copy_run_eq RSEGS 0xaa1b4 OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSrcUMemmove.PMCPS.memcpy_copy1 fx R M B vb1 (32 * 2 ^ vk1) 0x36308 X10 X11 X12 X1r) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & CP3 & KS3 & _).
{ split; [lia| reflexivity]. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
{ apply (L5.defined_sub M vb1 (32 * 2 ^ vk1)); [exact DB|lia|lia]. }
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx R 0xaa1b4 R3 0x36308 M3 (fun a => B <= a < B + (32 * 2 ^ vk1)) K HH Mh Ml ltac:(lia) MS3 MG3 FR3).
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
assert (BK : PMBOU1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M3 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG3)
as (RP3 & MO3).
{ intros i Hi N. apply FR3; [exact Hi|]. intros X. apply N. unfold PMBOU1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA3. } { exact ITB. }
assert (AGs : forall a n, S - 144 <= a -> a + n <= S -> L5C.agree_on M M3 a n) by (intros a n H1 H2; apply AGo; [lia|lia| clear - H1 GB1 X5 P2 Pp; lia]).
apply (grow_h_t fx R3 M3 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B c len).
- rewrite (KS3 2%nat) by PMK.inl. exact X2.
- rewrite (KS3 8%nat) by PMK.inl. exact X8.
- rewrite (KS3 9%nat) by PMK.inl. exact X9.
- rewrite (KS3 18%nat) by PMK.inl. exact X18.
- rewrite (KS3 21%nat) by PMK.inl. exact X21.
- intros k Hk0. rewrite (KS3 k); [apply KP; exact Hk0|]. unfold PMBOUS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
- rewrite (KS3 19%nat) by PMK.inl. exact X19.
- exact HLn.
- rewrite (KS3 20%nat) by PMK.inl. exact X20.
- pose proof SO as (O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
unfold PMBOU5.sof. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGs; lia|lia|lia|assumption]).
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M3); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
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
End PMBOU5C.

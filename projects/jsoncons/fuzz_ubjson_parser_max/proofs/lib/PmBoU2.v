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
PmCertKitG PmBaKit PmBoUStmts PmBoU1 PmBoUP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoU2.PMBOU2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1length"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "4m_vmmaps"]; ["5bvmap"; "0M"; "0M0"; "0M1"; "0R"; "0R0"; "6credit"; "6hi_heap"; "7agree_on"; "9defined"; "9u64_at"; "8SCFG"; ":push_st"; ";mem_ok"; ";regs_at"; ";saves"]; [";world"; "<inv"; "<inv_d"; "<mode_bottom"; "<mode_counted"; "<p_b"; "<p_depth"; "<p_k"; "<p_more"; "<p_src"; "<p_stk"; "<parser_own"; "<ps_idx"; "<ps_mode"; "<pst"; "<pstate"]; ["<pstate_at"; "<pstate_ok"; "<strm"; "<unread"; "=set_more"; ">cfg"; ">ec_at"; ">prog_value"; "?FPState"; "?getr"; "@srealizes"; "Amem_grows"; "Bloaded_segments"; "0S"; "0SCFG_P"; "Cadd"]; ["Cle"; "Clt"; "Cmul"; "Cof_nat"; "Cpow"; "0a"; "0c"; "0cat"; "0cr"; "0cr'"; "0cr0"; "0e"; "0e'"; "0e0"; "0fb"; "0fx"]; ["0i"; "0len"; "0model"; "0model0"; "0s"; "0s'"; "0s0"; "0s1"; "0sm"; "0sm'"; "0sm0"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0str"; "0v"]; ["0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU2.
Import PMU.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition push_st (s1 : PM.pst) (b k : Z) (c : PM.pstate) : PM.pst :=
PM.PST (PM.p_more s1) (PM.p_done s1) (PM.p_depth s1) (PM.p_src s1) (PM.p_tb s1) (PM.p_tg s1) b k (PM.p_stk s1 ++ [c]).
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
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU2 "B'RLyR0%211'6&R0z&RMr1%2271%5241&R1&R4+2+R0%3221%5271%=271pV2?1").
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
Lemma set_more_1 : ltac2:(TCodec.tc2 tcn__PmBoU2 ">'Q>'7'9&Q8r1%211+1%63521&QDr2%2214%:3;12p051pU:=1").
Proof. intros s. destruct s as [mo dn dp src tb tg vb vk stk]. cbn. intros ->. reflexivity. Qed.
Lemma u64_same_agree : ltac2:(TCodec.tc2 tcn__PmBoU2 "Q@'RLyR0%211'4y8%511%311p051'9&R0zr2%3221&QOr3+8%3221&R4+2+R0%3221%<251&J&QLr6r4%44321<r5%645413&Ir8%2317@r7%4331B&Hr:r9%34217Fp051p081p0<1p0?1p0E1p0O1pV0Q41pT<Q51pQ8Q71pQ4Q81").
Proof. intros M M1 a v.
intros H1 H2 U U1 D D1 i Hi. unfold L5.u64_at in U, U1.
pose proof (PMBK.rdn_nth RSEGS M 8 a _ H1 ltac:(lia) D U (Z.to_nat (i - a)) ltac:(lia)) as E.
pose proof (PMBK.rdn_nth RSEGS M1 8 a _ H1 ltac:(lia) D1 U1 (Z.to_nat (i - a)) ltac:(lia)) as E1.
rewrite Z2Nat.id in E, E1 by lia. replace (a + (i - a)) with i in E, E1 by lia. rewrite E, E1. reflexivity.
Qed.
Lemma tail_ct : ltac2:(TCodec.tc2 tcn__PmBoU2 "SN'QH&@y5'RLyR0%211%5241'4y8%611%311p061'>'Q>'QB'1&F'9&NvEvQMvR>r8%544321'7&QIr9&RK&R3uC%211%42M1%7261r2%72N1%;3N31'6&R0zr3%3221+`PPP0%5231%7231r;uD%B11%D2Q=1%G241&QO&Q5%11M&R2+Q0&2'Q?&Q:%11Q3%4231%O11%8271%<2:1%Q32QJ1%Q73QJ?1&O%13Q>Q=E&Mv<vBv=r<%56432QCQB1&Q0v:vRCvR:vRFvRNvRJvR=r=r:%:@?98=7QM65432<Q61QHQL&QF&QLr>+8%Q62R21vR7%65542QC1&Q1%11;&QG%14A8?='QJ&KvQN%211&QErCrB+WQiLrAr@%66D54321v;%<4F921p0>1p0A1p0D1p0L1p0Q81p0Q?1p0QB1p0R71p0R@1p0RM1pU4S41pTDS61pTJS81pUDS:1pU<S<1pU6S>1pQ4S@1pQ:SF1pU0SM1").
Proof. intros fx R M model s' sm' e' cr' len.
intros (R2 & R8 & R9 & R18 & R21 & KP) R19 Hlen REND SV MO W ECZ INV' PV.
prep_ctx M W MO.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _).
destruct s' as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1]. cbn [PM.p_b PM.p_stk] in REND.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr' M _ _ _ HH VIN) as (BK & V0 & V4).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [PM.p_b PM.p_k PM.p_stk] in PVEC.
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen2 & Hal & _).
pose proof INV' as (IM & _ & _ & (SH1 & _) & _). cbn [PM.p_more PM.p_stk] in IM, SH1. subst mo1.
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2.
assert (B4 : 4096 <= vb1) by (destruct BK as [BK|(BK & _)]; [lia| exact BK]).
set (E53 := vb1 + 32 * Z.of_nat (length stk1)) in *.
assert (C368 : L5.u64_at RSEGS M (fb + 40 + 368) E53) by (replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia; exact VC8).
assert (E53r : 4128 <= E53 <= 140737487306752) by (unfold E53; clear - B4 SH1 V4 X3 Hlen2; unfold hl_ceil in *; lia).
assert (E53a : E53 mod 16 = 0) by (unfold E53; clear - Hal; Lia.lia).
cfeed P (PMBOUP2.uboCT_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 48%nat => len | 53%nat => E53
| 40%nat => bv_unsigned (getr R0 (reg 1)) | 41%nat => bv_unsigned (getr R0 (reg 8)) | 42%nat => bv_unsigned (getr R0 (reg 9))
| 43%nat => bv_unsigned (getr R0 (reg 18)) | 44%nat => bv_unsigned (getr R0 (reg 19)) | 45%nat => bv_unsigned (getr R0 (reg 20))
| 46%nat => bv_unsigned (getr R0 (reg 21)) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & _ & _ & _ & _ & _ & _ & T18 & T19 & T20 & T21 & Z8 & _ & C1).
assert (E368 : L5C.agree_on M M1 (fb + 408) 8).
{ apply (u64_same_agree M M1 (fb + 408) E53); [lia|lia| replace (fb + 408) with (fb + 40 + 368) by lia; exact C368| replace (fb + 408) with (fb + 40 + 368) by lia; exact C1| | ].
- apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia].
- intros j Hj. apply MG1. apply (L5.defined_sub M (fb + 40) 384 (fb + 408) 8); [exact PDEF|lia|lia|exact Hj]. }
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr' M model fx fx1 R 0x3873c R1 0x387b0 M1
(fun a => (fb + 40 + 368 <= a < fb + 40 + 368 + 8) \/ (S - 128 <= a < S - 128 + 16) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 49 <= a) -> (a + n <= S - 128 \/ S - 112 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. destruct (PMK.rng_dec i (fb + 408) (fb + 408 + 8)) as [I8|O8]; [apply E368; exact I8|].
apply FRZ1; [clear - H1 H2 Hi; lia| clear - O8; lia| clear - H5 Hi; lia| clear - H4 Hi; lia]. }
destruct (keep_step M M1 model _ (PMPK.set_more (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 1) sm' e' cr' 0 0 W MO MG1) as (W1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi| | |]; intros X; apply N; unfold PMBOU1.FPB; [right; right; left; lia| left; unfold PMBOUS.SCR; lia| right; left; lia]. }
{ left; reflexivity. }
{ exact HH1. }
{ apply (PMPK.parser_more_upd RSEGS AD M M1 (fb + 40) (fb + 440) _ 1 PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG1.
- exact Z8.
- right. reflexivity.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 X3. unfold hl_ceil in *. lia.
- apply AG; [lia|clear - V4 X3; unfold hl_ceil in *; lia| clear - V4 X5 F1; unfold hl_ceil in *; lia| clear - V4 X5; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
{ exact TB. }
{ reflexivity. }
{ exact CK. }
rewrite (set_more_1 (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) eq_refl) in W1.
apply (fin fx1 R1 M1 model (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm' e' cr'); try assumption.
- apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- right. split; [|split; [exact INV'| exact PV]].
apply (PMBK.ec_agree RSEGS M M1); [apply AG; lia|lia|lia| exact ECZ].
Qed.
Lemma tail_i : ltac2:(TCodec.tc2 tcn__PmBoU2 "S<'QH&@y5'RLyR0%211%5241'4y8%611%311p061'>'Q>'QB'1&F&NvEvQMvR>r7%544321'7&QIr8&RK&R3uC%211%42L1%7261&QO&Q5r5%211&R2+Q0&2'Q?&Q:%117%4231%@11%8271%=2:1%D2Q:1%H3Q:@1&O%13ONH&Mv<vBv=r9%56432Q4Q31&Q0v:vRCvR:vRFvRNvRJvR=r:r6%:@?98=7Q>65432<Q9Q=1Q0&QF&QLr;+8%Q72QC1zvR7%7565321&Q1%11<&QG%14B9@>'QJ&KvQN%211&QEr@r?+WQ\Dr>r=%66E54321v;%<4G921p0>1p0A1p0D1p0M1p0Q91p0Q@1p0QC1p0R=1pTDRD1pTJRF1pUDRH1pU<RJ1pU6RL1pQ4RN1pQ:S41pU0S;1").
Proof. intros fx R M model s' sm' e' cr'.
intros (R2 & R8 & R9 & R18 & R21 & KP) REND SV MO W ECZ INV' PV.
prep_ctx M W MO.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
pose proof PA as (_ & _ & _ & _ & _ & _ & P16 & _).
destruct s' as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1]. cbn [PM.p_b PM.p_stk] in REND.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr' M _ _ _ HH VIN) as (BK & V0 & V4).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [PM.p_b PM.p_k PM.p_stk] in PVEC.
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen2 & Hal & _).
pose proof INV' as (IM & _ & _ & (SH1 & _) & _). cbn [PM.p_more PM.p_stk] in IM, SH1. subst mo1.
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2.
assert (B4 : 4096 <= vb1) by (destruct BK as [BK|(BK & _)]; [lia| exact BK]).
set (E53 := vb1 + 32 * Z.of_nat (length stk1)) in *.
assert (C368 : L5.u64_at RSEGS M (fb + 40 + 368) E53) by (replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia; exact VC8).
assert (E53r : 4128 <= E53 <= 140737487306752) by (unfold E53; clear - B4 SH1 V4 X3 Hlen2; unfold hl_ceil in *; lia).
assert (E53a : E53 mod 16 = 0) by (unfold E53; clear - Hal; Lia.lia).
cfeed P (PMBOUP2.uboIT_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 53%nat => E53
| 40%nat => bv_unsigned (getr R0 (reg 1)) | 41%nat => bv_unsigned (getr R0 (reg 8)) | 42%nat => bv_unsigned (getr R0 (reg 9))
| 43%nat => bv_unsigned (getr R0 (reg 18)) | 44%nat => bv_unsigned (getr R0 (reg 19)) | 45%nat => bv_unsigned (getr R0 (reg 20))
| 46%nat => bv_unsigned (getr R0 (reg 21)) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & _ & _ & _ & _ & _ & T18 & T19 & T20 & T21 & Z8 & C1).
assert (E368 : L5C.agree_on M M1 (fb + 408) 8).
{ apply (u64_same_agree M M1 (fb + 408) E53); [lia|lia| replace (fb + 408) with (fb + 40 + 368) by lia; exact C368| replace (fb + 408) with (fb + 40 + 368) by lia; exact C1| | ].
- apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia].
- intros j Hj. apply MG1. apply (L5.defined_sub M (fb + 40) 384 (fb + 408) 8); [exact PDEF|lia|lia|exact Hj]. }
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr' M model fx fx1 R 0x38594 R1 0x387b0 M1
(fun a => (fb + 40 + 368 <= a < fb + 40 + 368 + 8) \/ (S - 128 <= a < S - 128 + 16) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 49 <= a) -> (a + n <= S - 128 \/ S - 112 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. destruct (PMK.rng_dec i (fb + 408) (fb + 408 + 8)) as [I8|O8]; [apply E368; exact I8|].
apply FRZ1; [clear - H1 H2 Hi; lia| clear - O8; lia| clear - H5 Hi; lia| clear - H4 Hi; lia]. }
destruct (keep_step M M1 model _ (PMPK.set_more (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) 1) sm' e' cr' 0 0 W MO MG1) as (W1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi| | |]; intros X; apply N; unfold PMBOU1.FPB; [right; right; left; lia| left; unfold PMBOUS.SCR; lia| right; left; lia]. }
{ left; reflexivity. }
{ exact HH1. }
{ apply (PMPK.parser_more_upd RSEGS AD M M1 (fb + 40) (fb + 440) _ 1 PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG1.
- exact Z8.
- right. reflexivity.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- clear - V4 X3. unfold hl_ceil in *. lia.
- apply AG; [lia|clear - V4 X3; unfold hl_ceil in *; lia| clear - V4 X5 F1; unfold hl_ceil in *; lia| clear - V4 X5; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
{ exact TB. }
{ reflexivity. }
{ exact CK. }
rewrite (set_more_1 (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) eq_refl) in W1.
apply (fin fx1 R1 M1 model (PM.PST 1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm' e' cr'); try assumption.
- apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- right. split; [|split; [exact INV'| exact PV]].
apply (PMBK.ec_agree RSEGS M M1); [apply AG; lia|lia|lia| exact ECZ].
Qed.
Lemma push_end_fast : ltac2:(TCodec.tc2 tcn__PmBoU2 "VG'RLyR0%211'4y8%511%311p051'>'Q>'QB'1&F'Q?&OvEvQMr8%43321&Mv<vBv=vR>r9%66543921&Q0v:vRCvR:vRFvRNvRJvR=r:r7r6r5r4%=@C<;A:@98765F4321&QF&QLr;&QO+8%22F1zvR7%8576321&Q2+1%221K&R0&Q6%11D+QP0%4221'7'3%11Q>&Q:%11C%21Q0%63421&R1&R3&2r<%811%32QH1%511&R4+2&Q7%117%4231%<261&QA%11QF&8&Q3&Q=%11Q@%311%511'9&Q<%11Q=%O331Q:&Q4%91G%211&QC&Q9rA%211r@%5221%51R4%721R3%Q4231p0:1&QKrDrC%3221'6r1%QH2QN1+R0%Q72Q61%Q?241%6241&Q5%11;&R2+Q0%QI1>%QD2S91%QF11%5241%R>271r2%R7221%RA238%QM231%D231%Q@11+\H%RF2S:1r3%R?221+]0%RJ2S>1%R6241%M241%QI11rH&RK%12T:S5%311rI%113%RF3T931p081p0B1p0Q21pU2QN1&Q@rE%Q51Q>%RK1Q?%RF2T;1%RH11%Q72Q61%S@251r?%94SD821&JrF%24SG1OQ4&G&0'5%12R?R?&Q;%11A%5331TArBrG&?%11<%;5TA5431%TO3TNTMQ4%TK6TJTITHTNTGQ5&L%QO1A%S81B%34C21:%TI@TOTHTGTMTFTLTETDTCTBQ::1NR<R;%T<5T;Q;T7T6T5&Q1%114&QG%14TJ6THQ3%R?231%R@261%RA281%RB2>1%RC2@1p0B1p0O1p0Q31p0Q>1p0RI1p0RN1p0S<1p0SA1p0SH1p0SK1p0T91p0TA1p0TG1p0TK1p0U51p0UD1p0UL1pT>V21pTBV41pTHV61pUBV81pU@V:1pU6V<1pQ8V>1pQ4V?1").
Proof. intros M M1 model s1 sm e cr c.
intros SV MO W ECZ IV1 HD1 ES1 HL Hc Hm Hi0 Hcnt MG FR PC C8 HH1.
prep_ctx M W MO.
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1]. cbn [PM.p_b PM.p_k PM.p_stk PM.p_depth PM.p_src PM.p_more PM.p_done PM.p_tb PM.p_tg] in *.
set (n1 := Z.of_nat (length stk1)) in *.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr M _ _ _ HH VIN) as (BK & V0 & V4).
pose proof PA as (_ & _ & _ & P8 & _ & P12 & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & PB1 & PB2 & PB3).
cbn [PM.p_more PM.p_depth PM.p_b PM.p_k PM.p_stk] in P8, P12, PVEC, PB1.
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & _ & _ & EL).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2.
assert (FRZ : forall i, 0 <= i < 2 ^ 64 -> ~ PMBOU1.FPB S fb vb1 (32 * 2 ^ vk1) i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
{ intros i Hi N. apply FR; [exact Hi| |]; intros X; apply N; unfold PMBOU1.FPB; [right; right; right; lia| right; right; left; lia]. }
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 408 \/ fb + 416 <= a) -> (a + n <= vb1 \/ vb1 + 32 * 2 ^ vk1 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FR; [clear - H1 H2 Hi; lia| clear - H5 Hi Hlen HL; lia| clear - H4 Hi; lia]. }
assert (AGb : L5C.agree_on M M1 vb1 (32 * n1)).
{ intros i Hi. apply FR; [clear - Hi V0 V4 X3 HL P2; unfold hl_ceil in *; lia| lia| clear - Hi V4 X5 F1 HL P2; unfold hl_ceil in *; lia]. }
assert (VEC1 : PM.vec_at RSEGS PMSP.T3 PMSP.T4 M1 (fb + 40 + 360) vb1 vk1 (stk1 ++ [c])).
{ apply (PMBK.vec_push RSEGS M M1 (fb + 40 + 360) vb1 vk1 stk1 c PVEC HL); [lia|lia|lia| clear - V4 X3; unfold hl_ceil in *; lia| | |exact AGb| | |exact PC].
- apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- intros i Hi. apply MG. apply DB. exact Hi.
- replace (fb + 40 + 360 + 8) with (fb + 408) by lia. exact C8. }
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) vb1 vk1 c)).
{ unfold push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg].
apply (PMBK.parser_upd RSEGS AD M M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) mo1 dp1 vb1 vk1 (stk1 ++ [c]) PA);
cbn [PM.p_src PM.p_tb]; [lia|lia| | | | | | | | | |exact VEC1| |].
- apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia].
- apply PMPK.dkr_grows. exact MG.
- apply PMPK.dkr_grows. exact MG.
- apply (L5C.u8_at_agree RSEGS M M1); [apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia]|lia|lia| exact P8].
- exact PB1.
- apply (PMF.u32_at_agree RSEGS M M1); [apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia]|lia|lia| exact P12].
- cbn [PM.p_depth] in PB3. exact PB3.
- apply PMPK.dkr_grows. exact MG.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
destruct (keep_step M M1 model _ (push_st (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) vb1 vk1 c) sm e cr vb1 (32 * 2 ^ vk1) W MO MG FRZ BK)
as (W1 & MO1); [exact HH1| exact PA1| exact ITB| reflexivity| exact CK|].
split.
{ pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; [lia|lia|lia| clear - V4 X5; unfold hl_ceil in *; lia]|lia|lia|assumption]). }
split; [exact MO1|]. split; [exact W1|].
split; [apply (PMBK.ec_agree RSEGS M M1); [apply AGo; [lia|lia|lia| clear - V4 X5 F1; unfold hl_ceil in *; lia]|lia|lia| exact ECZ]|].
pose proof INV0 as (I0M & I0D & I0P & I0S & I0T).
split.
- unfold PM.inv, push_st. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [exact IM|]. split; [exact ID|]. split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; fold n1; lia|].
split; [|exact ITB]. apply (PMBK.stack_shape_push stk1 c ISH); [unfold PM.MAX_DEPTH; fold n1; lia| exact Hc| exact Hm].
- unfold PMSP.prog_value, PMSP.push_rel. right. exists c. unfold push_st. cbn [PM.p_stk PM.p_src].
split; [rewrite ES1; reflexivity|]. split; [exact Hc|]. split; [exact Hi0|]. split; [exact Hm| exact Hcnt].
Qed.
End Call.
End WithHeap.
End PMBOU2.

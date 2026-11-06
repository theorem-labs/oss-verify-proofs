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
PmCertKitG PmBaKit PmBoUStmts PmBoU1 PmBoU2 PmBoUP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1length"; "1list"; "1option"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"]; ["0R0"; "6credit"; "8u8_at"; "7SCFG"; "9mem_ok"; "9regs_at"; "9saves"; "9world"; ":inv_d"; ":p_depth"; ":p_k"; ":p_src"; ":p_stk"; ":pst"; ":pstate"; ":strm"]; [":unread"; ";cfg"; ";ec_at"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"; "0S"; "0SCFG_P"; "?add"; "?le"; "?lt"; "?of_nat"; "?pow"; "?sub"; "0cat"]; ["0cr"; "0cr0"; "0e"; "0e0"; "0fb"; "0fx"; "0k"; "0len"; "0model"; "0model0"; "0s0"; "0s1"; "0sm"; "0sm0"; "@Z_to_bv"; "@bv"]; ["@bv_unsigned"; "0str"; "0tb"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU3.
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
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU3 "B'QOyR0%211'4&Q:z&R0r1%2271%5241&Q;&Q=+2+R0%3221%5271%=271pT8?1").
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
Lemma pow2_le11 : ltac2:(TCodec.tc2 tcn__PmBoU3 "D'6'4&Q:zr1%3221+;%5231%7231+1&Q=+2r2%3221%<251+RP0%>231%@231p0:1pS>C1").
Proof. intros k. intros Hk. split; [pose proof (PM.pow2_pos k ltac:(lia)); lia| change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia]. Qed.
Lemma push_fast_i : ltac2:(TCodec.tc2 tcn__PmBoU3 "SL'Q3&<y5'QOyR0%211%5241'3y8%611%311p061';'M'O'0&A&Ev@vQ7vQDr7%544321'5&Q4r8&QN&Q<uC%211%42L1%7261&Q9+R0%22>1%92O1%=3O51&F%13DC=&Dv9v>v:r9%56432IH1&Gv7vQIvQAvQJvR1vQMvQCr:r6r5%;@@:9>8Q476543=OQ321&Q2&Q6r;+8%M2Q91zvQ?%7565321&H+1%221>&Q:&I%11;+QP0%4221'2'N%211&Lr<%211%31N%QI3521&Q;&1r=%811%32;1%QK11&Q=+2&J%117%4231%;261'Q5&CvQ8%211&Q1rBrA+WQU4r@r?%66Q=54321v8%<4Q?921p0>1p0K1p0Q41p0Q:1p0Q>1p0QG1p0R41p0R;1p0R>1p0RM1pS2S41pS6S61pSJS81pSHS:1pSBS<1pLS>1pQ0SD1pS<SK1").
Proof. intros fx R M model s1 sm e cr.
intros RA R19 SV MO W ECZ IV1 HD1 ES1 HL. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & _ & _ & EL).
assert (VIN : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) (PM.parser_own s1)) by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr M _ _ _ HH VIN) as (BK & V0 & V4). unfold hl_ceil in V4.
pose proof BK as [BK0|(BB0 & _)]; [exfalso; pose proof (PM.pow2_pos (PM.p_k s1) ltac:(lia)); lia|].
assert (VIN' : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) (PM.parser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
set (b := PM.p_b s1) in *. set (k := PM.p_k s1) in *. set (n1 := Z.of_nat (length (PM.p_stk s1))) in *.
pose proof (pow2_le11 k Hk) as P2.
assert (WB : L5.writable RSEGS M b (32 * 2 ^ k)) by (apply (L5C.writable_of_defined RSEGS); [exact DB|lia| clear - V4 X3; unfold hl_ceil in *; lia]).
assert (WE : L5.writable RSEGS M (b + 32 * n1) 32) by (apply (L5.writable_sub RSEGS M b (32 * 2 ^ k)); [exact WB| lia| lia]).
cfeed P (PMBOUP2.uboIf_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => b | 53%nat => b + 32 * n1 | 51%nat => 32 * 2 ^ k - 32 * n1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & _ & T19 & C368 & E24 & E16 & E8 & E0).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s1 ++ LBX) cr M model fx fx1 R 0x384a4 R1 0x38594 M1
(fun a => (b + 32 * n1 + 0 <= a < b + 32 * n1 + 0 + 32) \/ (fb + 40 + 368 <= a < fb + 40 + 368 + 8)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a [Pa|Pa]; [apply (PMK.cwr_block L _ b (32 * 2 ^ k) a VIN'); lia| apply (PMK.cwr_stack L _ M S SCR a STK); unfold PMBOUS.SCR; lia]. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
destruct (push_end_fast M M1 model s1 sm e cr (PM.PS 9 0 0 0) SV MO W ECZ IV1 HD1 ES1 HL) as (SV1 & MO1 & W1 & EC1 & INV1 & PV1).
{ unfold PM.pstate_ok. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [lia|]. right; left. split; [unfold PM.mode_indef; lia|]. split; [reflexivity|]. unfold PM.MAX_ITEMS. lia. }
{ unfold PM.mode_bottom. cbn. lia. }
{ reflexivity. }
{ unfold PM.mode_counted. cbn. lia. }
{ exact MG1. }
{ intros i Hi N1 N2. apply FRZ1; [exact Hi| intros X; apply N1; fold b n1; lia| intros X; apply N2; lia]. }
{ unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. fold b n1.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24]. }
{ fold b n1. replace (fb + 408) with (fb + 40 + 368) by lia. exact C368. }
{ exact HH1. }
apply (tail_i fx1 R1 M1 model (push_st s1 b k (PM.PS 9 0 0 0)) sm e cr); [| | exact SV1| exact MO1| exact W1| exact EC1| exact INV1| exact PV1].
2: { rewrite T19. f_equal. unfold push_st. cbn [PM.p_b PM.p_stk]. rewrite length_app, Nat2Z.inj_add. cbn [length]. unfold n1, b. lia. }
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
Lemma push_fast_c : ltac2:(TCodec.tc2 tcn__PmBoU3 "TF'Q3&<y5'QOyR0%211%5241'3y8%611%311p061';'M'O'0&A'6&Ev@vQ7vQDr8%544321'5&Q4r9&QN&Q<uC%211%42M1%7261&Q9+R0%22>1%92Q01%=3Q051r:u:%<11%>2Q71%A241r3%A2Q81%E3Q831'4&Q:zr4%3221+`PPP0%5231%7231&Q;&Q0&K%11O%321Q4vQJ%411vQM%7221%9251&Fr<%23Q?Q>1&Dv9v>v:r=%56432QDQC1&Gv7vQIvQAvR1vQCr>r;%8@=76;5QLF4D32:@1Q;QG&Q2&Q6r?+8%QE2R11vQ?%65542Q81&H+1%221<&I%119+QP0%Q@221'2'N%211&Lr@%211%31Q;%R?3521&1rA%711%32:1%R@11&Q=+2&J%117%4231%QL261'Q5&CvQ8%211&Q1rFrE+WQT4rDrC%66Q:54321v8%<4Q<921p0>1p0J1p0Q31p0Q81p0Q<1p0QD1p0QN1p0R51p0R91p0RD1p0RM1p0S61p0SE1pS@SL1pS2SN1pS6T01pSJT21pSHT41pSBT61pLT81pQ0T>1pS<TE1").
Proof. intros fx R M model s1 sm e cr len.
intros RA R19 R10 HLn UNR SV MO W ECZ IV1 HD1 ES1 HL. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _ & _ & PVEC & _). unfold PM.MAX_ITEMS in P328.
pose proof ECZ as (EC0 & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & _ & _ & EL).
assert (VIN : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) (PM.parser_own s1)) by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr M _ _ _ HH VIN) as (BK & V0 & V4). unfold hl_ceil in V4.
pose proof BK as [BK0|(BB0 & _)]; [exfalso; pose proof (PM.pow2_pos (PM.p_k s1) ltac:(lia)); lia|].
assert (VIN' : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) (PM.parser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
set (b := PM.p_b s1) in *. set (k := PM.p_k s1) in *. set (n1 := Z.of_nat (length (PM.p_stk s1))) in *.
pose proof (pow2_le11 k Hk) as P2.
assert (WB : L5.writable RSEGS M b (32 * 2 ^ k)) by (apply (L5C.writable_of_defined RSEGS); [exact DB|lia| clear - V4 X3; unfold hl_ceil in *; lia]).
assert (WE : L5.writable RSEGS M (b + 32 * n1) 32) by (apply (L5.writable_sub RSEGS M b (32 * 2 ^ k)); [exact WB| lia| lia]).
cfeed P (PMBOUP2.uboCf_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 48%nat => len
| 34%nat => b | 53%nat => b + 32 * n1 | 51%nat => 32 * 2 ^ k - 32 * n1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & _ & T19 & T20 & C368 & E24 & E16 & E8 & E0).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s1 ++ LBX) cr M model fx fx1 R 0x38484 R1 0x3873c M1
(fun a => (b + 32 * n1 + 0 <= a < b + 32 * n1 + 0 + 32) \/ (fb + 40 + 368 <= a < fb + 40 + 368 + 8)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a [Pa|Pa]; [apply (PMK.cwr_block L _ b (32 * 2 ^ k) a VIN'); lia| apply (PMK.cwr_stack L _ M S SCR a STK); unfold PMBOUS.SCR; lia]. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
destruct (push_end_fast M M1 model s1 sm e cr (PM.PS 5 len 0 0) SV MO W ECZ IV1 HD1 ES1 HL) as (SV1 & MO1 & W1 & EC1 & INV1 & PV1).
{ unfold PM.pstate_ok. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; lia|]. unfold PM.MAX_ITEMS. lia. }
{ unfold PM.mode_bottom. cbn. lia. }
{ reflexivity. }
{ intros _. exact UNR. }
{ exact MG1. }
{ intros i Hi N1 N2. apply FRZ1; [exact Hi| intros X; apply N1; fold b n1; lia| intros X; apply N2; lia]. }
{ unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. fold b n1.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24]. }
{ fold b n1. replace (fb + 408) with (fb + 40 + 368) by lia. exact C368. }
{ exact HH1. }
apply (tail_ct fx1 R1 M1 model (push_st s1 b k (PM.PS 5 len 0 0)) sm e cr len); [| exact T19| exact HLn| | exact SV1| exact MO1| exact W1| exact EC1| exact INV1| exact PV1].
2: { rewrite T20. f_equal. unfold push_st. cbn [PM.p_b PM.p_stk]. rewrite length_app, Nat2Z.inj_add. cbn [length]. unfold n1, b. lia. }
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
Lemma push_fast_t : ltac2:(TCodec.tc2 tcn__PmBoU3 "U='Q3&<y5'QOyR0%211%5241'3y8%611%311p061';'M'O'0&A'6&Ev@vQ7vQDr9%544321'5&Q4r:&QN&Q<uC%211%42M1%7261&Q9+R0%22>1%92Q01%=3Q051r;uD%<11%>2Q71%A241+1%A2Q81%E3Q831r<u:%D11%F2Q?1%I241r5%I2Q@1%M3Q@31'4&Q:zr6%3221+`PPP0%5231%7231&B&Q6r=&Q>+S1%22Q?1%64541;r7%?2>1&Q;+X0%2241%D241&Q0&K%11=%321Q0vQJ%411vQM%7221%<251&Fr@%23R3R21&Dv9v>v:rA%56432R8R71&Gv7vQIvQAvR1vQCrBr?r>%9@>87<6RAG5E43;A21Q6&Q2rC+8%R92RE1vQ?%55Q=42QD1&H%12R3;&I%118+QP0%QK221'2'N%211&LrD%211%31Q:%S23521&1rE%711%32:1%S311&Q=+2&J%117%4231%QN261'Q5&CvQ8%211&Q1rJrI+WPoHrHrG%66RA54321v8%<4RC921p0>1p0J1p0Q31p0Q81p0Q;1p0QB1p0QM1p0R41p0R81p0RB1p0RI1p0S11p0S:1p0SC1p0SL1p0T;1pT6TB1pS@TC1pS2TE1pS6TG1pSJTI1pSHTK1pSBTM1pLTO1pQ0U51pS<U<1").
Proof. intros fx R M model s1 sm e cr len tb.
intros RA R19 R20 R10 HLn TBY Htb UNR SV MO W ECZ IV1 HD1 ES1 HL. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _ & _ & PVEC & _). unfold PM.MAX_ITEMS in P328.
pose proof ECZ as (EC0 & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & _ & _ & EL).
assert (VIN : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) (PM.parser_own s1)) by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr M _ _ _ HH VIN) as (BK & V0 & V4). unfold hl_ceil in V4.
pose proof BK as [BK0|(BB0 & _)]; [exfalso; pose proof (PM.pow2_pos (PM.p_k s1) ltac:(lia)); lia|].
assert (VIN' : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) (PM.parser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
set (b := PM.p_b s1) in *. set (k := PM.p_k s1) in *. set (n1 := Z.of_nat (length (PM.p_stk s1))) in *.
pose proof (pow2_le11 k Hk) as P2.
assert (WB : L5.writable RSEGS M b (32 * 2 ^ k)) by (apply (L5C.writable_of_defined RSEGS); [exact DB|lia| clear - V4 X3; unfold hl_ceil in *; lia]).
assert (WE : L5.writable RSEGS M (b + 32 * n1) 32) by (apply (L5.writable_sub RSEGS M b (32 * 2 ^ k)); [exact WB| lia| lia]).
cfeed P (PMBOUP2.uboTf_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 48%nat => len | 50%nat => tb
| 34%nat => b | 53%nat => b + 32 * n1 | 51%nat => 32 * 2 ^ k - 32 * n1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & _ & _ & T19 & T20 & C368 & E24 & E16 & E8 & E0).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s1 ++ LBX) cr M model fx fx1 R 0x383f8 R1 0x3873c M1
(fun a => (b + 32 * n1 + 0 <= a < b + 32 * n1 + 0 + 32) \/ (fb + 40 + 368 <= a < fb + 40 + 368 + 8)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a [Pa|Pa]; [apply (PMK.cwr_block L _ b (32 * 2 ^ k) a VIN'); lia| apply (PMK.cwr_stack L _ M S SCR a STK); unfold PMBOUS.SCR; lia]. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
destruct (push_end_fast M M1 model s1 sm e cr (PM.PS 7 len tb 0) SV MO W ECZ IV1 HD1 ES1 HL) as (SV1 & MO1 & W1 & EC1 & INV1 & PV1).
{ unfold PM.pstate_ok. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; lia|]. unfold PM.MAX_ITEMS. lia. }
{ unfold PM.mode_bottom. cbn. lia. }
{ reflexivity. }
{ intros _. exact UNR. }
{ exact MG1. }
{ intros i Hi N1 N2. apply FRZ1; [exact Hi| intros X; apply N1; fold b n1; lia| intros X; apply N2; lia]. }
{ unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. fold b n1.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24]. }
{ fold b n1. replace (fb + 408) with (fb + 40 + 368) by lia. exact C368. }
{ exact HH1. }
apply (tail_ct fx1 R1 M1 model (push_st s1 b k (PM.PS 7 len tb 0)) sm e cr len); [| exact T19| exact HLn| | exact SV1| exact MO1| exact W1| exact EC1| exact INV1| exact PV1].
2: { rewrite T20. f_equal. unfold push_st. cbn [PM.p_b PM.p_stk]. rewrite length_app, Nat2Z.inj_add. cbn [length]. unfold n1, b. lia. }
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
End Call.
End WithHeap.
End PMBOU3.

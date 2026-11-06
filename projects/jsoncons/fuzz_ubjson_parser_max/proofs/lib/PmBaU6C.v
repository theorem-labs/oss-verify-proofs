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
PmCertKitG PmSrcUMemmove PmBaKit PmBaUStmts PmBaU1 PmBaU2 PmBaU4 PmBaU5 PmBaU5C PmBaU6 PmBaUP3I PmBaUP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBaU6C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaU5.PMBAU5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaUStmts.PMBAUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "2and"; "2eq"; "0HI"; "0K"; "0L"; "0LBX"; "3Model"; "4bvmap"; "0M"; "0M0"; "0R"; "0R0"; "5credit"; "6SCFG"]; ["7pushok"; "8mem_ok"; "8regs_at"; "8saves"; "8world"; "9PS"; "9pst"; "9strm"; ":cfg"; ":ec_at"; ";opdel_spec"; ";opnew_spec"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"]; ["0S"; "0SCFG_P"; "?add"; "?le"; "?lt"; "?of_nat"; "?pow"; "0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"; "0fx"; "0model"; "0model0"]; ["0s0"; "0s1"; "0sm"; "0sm0"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0str"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBAU6C.
Import PMU.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBAU2.push_st.
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
Hypothesis PRE : PMBAUS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBAUS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBAUS.kept0 R0).
Local Abbreviation regs_at := (PMBAUS.regs_at R0 S fb).
Local Abbreviation saves := (PMBAUS.saves R0 S).
Local Abbreviation mem_ok := (PMBAUS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBAUS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBAUS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBAU1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBAU1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBAU1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBAU1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBAU1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBAU1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBAU1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBAU1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBAU2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBAU2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBAU2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBaU6C "B'QEyR0%211'2&Q3z&QFr1%2271%5241&Q4&Q6+2+R0%3221%5271%=271pSB?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBAUP2.aligned; first [assumption | lia]].
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
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBAUS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBAU1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBAU1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBAU1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBAU1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBAU1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBAU1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBAU1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_del := PMBAU4.grow_del L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let CRED0 := PMBAU1.CRED0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rgp0 := PMBAU1.Rgp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let call_keep0 := PMBAU4.call_keep0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_objs := PMBAU5.keep_objs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_facts := PMBAU5.push_facts L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_i := PMBAU5C.grow_cpy_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_c := PMBAU5C.grow_cpy_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_t := PMBAU5C.grow_cpy_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Abbreviation gstate := (PMBAU5.gstate L HI model0 LBX fb s0 str sm0 e0).
Local Abbreviation pushok := (PMBAU5.pushok s0 sm0).
Local Abbreviation sof := (PMBAU5.sof S fb).
Let grow_new := PMBAU6.grow_new L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_g_i := PMBAU6.grow_g_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Ltac gpost PP :=
repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end;
repeat split; first [ PMK.greg | PMK.gmem ].
Lemma grow_cap_i : ltac2:(TCodec.tc2 tcn__PmBaU6C "S8'L&9y5'QEyR0%211%5241'1y8%611%311p061'8'F'G'0&>&Bv=vQ0vQ<r7%544321'3&Mr8&QD&Q5uC%211%42L1%7261&Q2+R0%22>1%92O1%=3O51&C%13DC=&Av6v;v7r9%56432IH1&Dv4vQ?vQ9vQ@vQGvQCvQ;r:r6r5%;@@:9>8Q476543=OQ321&I&Or;+8%M2Q91zvQ7%7565321&@(E+3%241666%45DB@J1&KvQ1%231Q0J&J%133Q2L'N&?%116&HrAr@+VonLr?r>%66J54321v5%;4L921p0=1p0@1p0D1p0J1p0Q31p0Q@1p0QG1p0QJ1p0R91pRBR@1pRFRB1pS6RD1pS4RF1pRNRH1pFRJ1pJS01pRLS71").
Proof. intros fx R M model s1 sm e cr.
intros RA R19 SV MO W ECZ PK OPN OPD. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _ & _ & PVEC & _). unfold PM.MAX_ITEMS in P328.
pose proof ECZ as (EC0 & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr M _ _ _ HH VIN) as (BK & V0 & V4). unfold hl_ceil in V4.
pose proof BK as [BK0|(BB0 & _)]; [exfalso; pose proof (PM.pow2_pos vk1 ltac:(lia)); lia|].
assert (CAP : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x37fdc) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xaf0ec) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 160 <= i < S - 160 + 64) -> ~ (S - 96 <= i < S - 96 + 40) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0x363ec /\ getr R1 (reg 2) = Z_to_bv 64 (S - 160) /\ getr R1 (reg 8) = Z_to_bv 64 (2 ^ (vk1 + 1))
/\ getr R1 (reg 9) = Z_to_bv 64 (2 ^ vk1) /\ getr R1 (reg 10) = Z_to_bv 64 (32 * 2 ^ (vk1 + 1)) /\ getr R1 (reg 19) = Z_to_bv 64 (fb + 400)
/\ L5.u64_at RSEGS M1 (S - 160) (S - 96) /\ L5.u64_at RSEGS M1 (S - 152) 0x36208 /\ L5.u64_at RSEGS M1 (S - 64) (fb + 400)
/\ L5.u64_at RSEGS M1 (S - 72) 0 /\ L5.u64_at RSEGS M1 (S - 136) (fb + 8) /\ L5.u64_at RSEGS M1 (S - 128) (fb + 40)
/\ L5.u64_at RSEGS M1 (S - 120) 0x38068).
{ assert (KC : vk1 = 0 \/ vk1 = 1 \/ vk1 = 2 \/ vk1 = 3 \/ vk1 = 4 \/ vk1 = 5 \/ vk1 = 6 \/ vk1 = 7 \/ vk1 = 8 \/ vk1 = 9 \/ vk1 = 10) by lia.
destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- change (2 ^ 0) with 1 in *. change (2 ^ (0 + 1)) with 2 in *.
cfeed P (PMBAUP3I.ubaIs0_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 1) with 2 in *. change (2 ^ (1 + 1)) with 4 in *.
cfeed P (PMBAUP3I.ubaIs1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 2) with 4 in *. change (2 ^ (2 + 1)) with 8 in *.
cfeed P (PMBAUP3I.ubaIs2_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 3) with 8 in *. change (2 ^ (3 + 1)) with 16 in *.
cfeed P (PMBAUP3I.ubaIs3_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 4) with 16 in *. change (2 ^ (4 + 1)) with 32 in *.
cfeed P (PMBAUP3I.ubaIs4_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 5) with 32 in *. change (2 ^ (5 + 1)) with 64 in *.
cfeed P (PMBAUP3I.ubaIs5_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 6) with 64 in *. change (2 ^ (6 + 1)) with 128 in *.
cfeed P (PMBAUP3I.ubaIs6_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 7) with 128 in *. change (2 ^ (7 + 1)) with 256 in *.
cfeed P (PMBAUP3I.ubaIs7_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 8) with 256 in *. change (2 ^ (8 + 1)) with 512 in *.
cfeed P (PMBAUP3I.ubaIs8_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 9) with 512 in *. change (2 ^ (9 + 1)) with 1024 in *.
cfeed P (PMBAUP3I.ubaIs9_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 10) with 1024 in *. change (2 ^ (10 + 1)) with 2048 in *.
cfeed P (PMBAUP3I.ubaIs10_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
}
destruct CAP as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T9 & T10 & T19 & C160 & C152 & C64 & C72 & C136 & C128 & C120).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x37fdc R1 0xaf0ec M1
(fun a => (S - 160 <= a < S - 160 + 64) \/ (S - 96 <= a < S - 96 + 40)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBAUS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 160 \/ S - 56 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H4 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M1 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; lia.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- apply AGo; [lia|lia| clear - V4 X5; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
destruct (keep_step M M1 model _ (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr 0 0 W MO MG1) as (W1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBAU1.FPB; left; unfold PMBAUS.SCR; lia. }
{ left; reflexivity. } { exact HH1. } { exact PA1. } { exact ITB. } { reflexivity. } { exact CK. }
assert (KP1 : kept0 R1) by (intros k Hk0; rewrite (KS1 k) by (unfold PMBAUS.CSK in Hk0; cbn in Hk0 |- *; tauto); apply KP; exact Hk0).
apply (grow_new fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr (PM.PS 3 0 0 0) T1 T2 T10 KP1).
- unfold PMBAUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
- exact MO1.
- exact W1.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact ECZ].
- cbn [PM.p_k]. exact Hk.
- exact OPN.
- intros fx2 R2' M2 model2 B RP2 RB SV2 MO2 GS2 EC2 CK2 AGN.
apply (grow_g_i fx2 R2' M2 model2 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e (debit L cr (32 * 2 ^ (vk1 + 1))) B).
+ rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl. exact T2.
+ rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl. exact T8.
+ rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl. exact T9.
+ exact RB.
+ rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact R18.
+ rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. exact R21.
+ intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [apply KP1; exact Hk0|]. unfold PMBAUS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. exact T19.
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C152].
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C160].
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C120].
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C128].
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C136].
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C64].
+ apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGN; lia|lia|lia| exact C72].
+ exact SV2.
+ exact MO2.
+ exact GS2.
+ exact EC2.
+ exact PK.
+ exact CK2.
+ exact OPD.
Qed.
End Call.
End WithHeap.
End PMBAU6C.

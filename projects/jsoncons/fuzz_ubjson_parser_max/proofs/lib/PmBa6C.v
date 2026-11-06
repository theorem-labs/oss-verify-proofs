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
PmCertKitG PmSrcSMemmove PmBaKit PmBaStmts PmBa1 PmBa2 PmBa4 PmBa5 PmBa6 PmBaSP2 PmBaSP3I PmBaSP3C PmBaSP3T.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBa6C () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBa5.PMBA5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaStmts.PMBAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"; "6credit"]; ["8u8_at"; "7SCFG"; "9pushok"; ":mem_ok"; ":regs_at"; ":saves"; ":world"; ";PS"; ";pst"; ";strm"; "<cfg"; "<ec_at"; "=opdel_spec"; "=opnew_spec"; ">FPState"; ">getr"]; ["?srealizes"; "@loaded_segments"; "0S"; "0SCFG_P"; "Aadd"; "Ale"; "Alt"; "Aof_nat"; "Apow"; "Asub"; "0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"]; ["0fx"; "0len"; "0model"; "0model0"; "0s0"; "0s1"; "0sm"; "0sm0"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0str"; "0tb"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBA6C.
Import PMS.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBA2.push_st.
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
Hypothesis PRE : PMBAS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBAS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBAS.kept0 R0).
Local Abbreviation regs_at := (PMBAS.regs_at R0 S fb).
Local Abbreviation saves := (PMBAS.saves R0 S).
Local Abbreviation mem_ok := (PMBAS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBAS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBAS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBA1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBA1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBA1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBA1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBA1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBA1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBA1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBA1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBA2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBA2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBA2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBa6C "B'QIyR0%211'2&Q5z&QJr1%2271%5241&Q6&Q8+2+R0%3221%5271%=271pSL?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBAP2.aligned; first [assumption | lia]].
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
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBAS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBA1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBA1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBA1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBA1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBA1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBA1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBA1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_del := PMBA4.grow_del L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_end_i := PMBA4.grow_end_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_end_ct := PMBA4.grow_end_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let CRED0 := PMBA1.CRED0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rgp0 := PMBA1.Rgp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let call_keep0 := PMBA4.call_keep0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_objs := PMBA5.keep_objs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_facts := PMBA5.push_facts L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_i := PMBA5.grow_cpy_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_ct := PMBA5.grow_cpy_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_new := PMBA6.grow_new L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_g_i := PMBA6.grow_g_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_g_c := PMBA6.grow_g_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_g_t := PMBA6.grow_g_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Abbreviation gstate := (PMBA5.gstate L HI model0 LBX fb s0 str sm0 e0).
Local Abbreviation pushok := (PMBA5.pushok s0 sm0).
Lemma grow_cap_i : ltac2:(TCodec.tc2 tcn__PmBa6C "S8'N&:y5'QIyR0%211%5241'1y8%611%311p061'9'H'I'0&?&Dv>vQ2vQ?r7%544321'3&Or8&QH&Q7uC%211%42L1%7261&Q4+R0%22>1%92O1%=3O51&E%13DC=&Cv7v<v8r9%56432IH1&Fv5vQCvQ<vQDvQKvQGvQ>r:r6r5%;@@:9>8Q476543=OQ321&K&Q1r;+8%M2Q91zvQ:%7565321&B(G+3%241666%45DB@J1&MvQ3%231Q0J&L%133Q2L'Q0&A%116&JrAr@+Vl^4r?r>%66J54321v6%;4L921p0=1p0@1p0D1p0J1p0Q31p0Q@1p0QG1p0QJ1p0R91pRHR@1pRLRB1pS>RD1pS<RF1pS6RH1pHRJ1pLS01pS2S71").
Proof. intros fx R M model s1 sm e cr.
intros RA R19 SV MO W ECZ PK OPN OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
prep_ctx M W MO.
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr M _ _ _ HH VIN) as (BK & V0 & V4). unfold hl_ceil in V4.
pose proof BK as [BK0|(BB0 & _)]; [exfalso; pose proof (PM.pow2_pos vk1 ltac:(lia)); lia|].
assert (CAP : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x371c4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xae098) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 128 <= i < S - 128 + 16) -> ~ (S - 72 <= i < S - 72 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 9; 18; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0x3596c /\ getr R1 (reg 2) = Z_to_bv 64 (S - 128) /\ getr R1 (reg 8) = Z_to_bv 64 (2 ^ (vk1 + 1))
/\ getr R1 (reg 10) = Z_to_bv 64 (32 * 2 ^ (vk1 + 1)) /\ getr R1 (reg 19) = Z_to_bv 64 (32 * 2 ^ vk1)
/\ L5.u64_at RSEGS M1 (S - 128) (fb + 40) /\ L5.u64_at RSEGS M1 (S - 120) 0x37234).
{ assert (KC : vk1 = 0 \/ vk1 = 1 \/ vk1 = 2 \/ vk1 = 3 \/ vk1 = 4 \/ vk1 = 5 \/ vk1 = 6 \/ vk1 = 7 \/ vk1 = 8 \/ vk1 = 9 \/ vk1 = 10) by lia.
destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- change (2 ^ 0) with 1 in *. change (2 ^ (0 + 1)) with 2.
cfeed P (PMBAP3I.baIs0_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 1) with 2 in *. change (2 ^ (1 + 1)) with 4.
cfeed P (PMBAP3I.baIs1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 2) with 4 in *. change (2 ^ (2 + 1)) with 8.
cfeed P (PMBAP3I.baIs2_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 3) with 8 in *. change (2 ^ (3 + 1)) with 16.
cfeed P (PMBAP3I.baIs3_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 4) with 16 in *. change (2 ^ (4 + 1)) with 32.
cfeed P (PMBAP3I.baIs4_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 5) with 32 in *. change (2 ^ (5 + 1)) with 64.
cfeed P (PMBAP3I.baIs5_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 6) with 64 in *. change (2 ^ (6 + 1)) with 128.
cfeed P (PMBAP3I.baIs6_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 7) with 128 in *. change (2 ^ (7 + 1)) with 256.
cfeed P (PMBAP3I.baIs7_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 8) with 256 in *. change (2 ^ (8 + 1)) with 512.
cfeed P (PMBAP3I.baIs8_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 9) with 512 in *. change (2 ^ (9 + 1)) with 1024.
cfeed P (PMBAP3I.baIs9_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120].
- change (2 ^ 10) with 1024 in *. change (2 ^ (10 + 1)) with 2048.
cfeed P (PMBAP3I.baIs10_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact C128| exact C120]. }
destruct CAP as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T10 & T19 & C128 & C120).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x371c4 R1 0xae098 M1
(fun a => (S - 128 <= a < S - 128 + 16) \/ (S - 72 <= a < S - 72 + 8)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBAS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 128 \/ S - 64 <= a) -> L5C.agree_on M M1 a n).
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
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBA1.FPB; left; unfold PMBAS.SCR; lia. }
{ left; reflexivity. } { exact HH1. } { exact PA1. } { exact ITB. } { reflexivity. } { exact CK. }
assert (KP1 : kept0 R1) by (intros k Hk0; rewrite (KS1 k) by (unfold PMBAS.CSK in Hk0; cbn in Hk0 |- *; tauto); apply KP; exact Hk0).
apply (grow_new 0x37234 fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr (PM.PS 3 0 0 0) T1 T2 T10 KP1 C120 C128).
- unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
- exact MO1.
- exact W1.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact ECZ].
- cbn [PM.p_k]. exact Hk.
- exact OPN.
- intros fx2 R2' M2 model2 B RP2 RB SV2 MO2 GS2 C120' C128' EC2 CK2 AGN.
apply (grow_g_i fx2 R2' M2 model2 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e (debit L cr (32 * 2 ^ (vk1 + 1))) B); try assumption.
+ rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl. exact T2.
+ rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl. exact T8.
+ rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact R9.
+ rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact R18.
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. exact T19.
+ intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [apply KP1; exact Hk0|]. unfold PMBAS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
Qed.
Lemma grow_cap_c : ltac2:(TCodec.tc2 tcn__PmBa6C "SJ'N&:y5'QIyR0%211%5241'1y8%611%311p061'9'H'I'0&?'4&Dv>vQ2vQ?r8%544321'3&Or9&QH&Q7uC%211%42M1%7261&Q4+R0%22>1%92Q01%=3Q051r:u:%<11%>2Q71%A241r3%A2Q81%E3Q831'2&Q5zr4%3221+`PPP0%5231%7231&Er;%23Q5Q41&Cv7v<v8r<%56432Q:Q91&Fv5vQCvQ<vQDvQKvQGvQ>r=%9@>87<6QC54321;AQ2Q>QB&K&Q1r>+8%Q<2QH1vQ:%65542O1&B(G+2%241QIQ3Q3%45A?=G1&MvQ3%231MG&L%133OI'Q0&A%116&JrDrC+Vl]4rBrA%66I54321v6%;4K921p0=1p0@1p0D1p0J1p0Q21p0Q=1p0QD1p0QH1p0R11p0R:1p0RI1pS4S01pRHS21pRLS41pS>S61pS<S81pS6S:1pHS<1pLSB1pS2SI1").
Proof. intros fx R M model s1 sm e cr len.
intros RA R19 R10 HLn SV MO W ECZ PK OPN OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
prep_ctx M W MO.
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
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
assert (CAP : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x371a4) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xae098) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 128 <= i < S - 128 + 16) -> ~ (S - 72 <= i < S - 72 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 9; 18; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0x3596c /\ getr R1 (reg 2) = Z_to_bv 64 (S - 128) /\ getr R1 (reg 8) = Z_to_bv 64 (2 ^ (vk1 + 1))
/\ getr R1 (reg 10) = Z_to_bv 64 (32 * 2 ^ (vk1 + 1)) /\ getr R1 (reg 19) = Z_to_bv 64 len /\ getr R1 (reg 20) = Z_to_bv 64 (32 * 2 ^ vk1)
/\ L5.u64_at RSEGS M1 (S - 128) (fb + 40) /\ L5.u64_at RSEGS M1 (S - 120) 0x3734c).
{ assert (KC : vk1 = 0 \/ vk1 = 1 \/ vk1 = 2 \/ vk1 = 3 \/ vk1 = 4 \/ vk1 = 5 \/ vk1 = 6 \/ vk1 = 7 \/ vk1 = 8 \/ vk1 = 9 \/ vk1 = 10) by lia.
destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- change (2 ^ 0) with 1 in *. change (2 ^ (0 + 1)) with 2.
cfeed P (PMBAP3C.baCs0_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 1) with 2 in *. change (2 ^ (1 + 1)) with 4.
cfeed P (PMBAP3C.baCs1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 2) with 4 in *. change (2 ^ (2 + 1)) with 8.
cfeed P (PMBAP3C.baCs2_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 3) with 8 in *. change (2 ^ (3 + 1)) with 16.
cfeed P (PMBAP3C.baCs3_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 4) with 16 in *. change (2 ^ (4 + 1)) with 32.
cfeed P (PMBAP3C.baCs4_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 5) with 32 in *. change (2 ^ (5 + 1)) with 64.
cfeed P (PMBAP3C.baCs5_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 6) with 64 in *. change (2 ^ (6 + 1)) with 128.
cfeed P (PMBAP3C.baCs6_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 7) with 128 in *. change (2 ^ (7 + 1)) with 256.
cfeed P (PMBAP3C.baCs7_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 8) with 256 in *. change (2 ^ (8 + 1)) with 512.
cfeed P (PMBAP3C.baCs8_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 9) with 512 in *. change (2 ^ (9 + 1)) with 1024.
cfeed P (PMBAP3C.baCs9_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 10) with 1024 in *. change (2 ^ (10 + 1)) with 2048.
cfeed P (PMBAP3C.baCs10_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120]. }
destruct CAP as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T10 & T19 & T20 & C128 & C120).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x371a4 R1 0xae098 M1
(fun a => (S - 128 <= a < S - 128 + 16) \/ (S - 72 <= a < S - 72 + 8)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBAS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 128 \/ S - 64 <= a) -> L5C.agree_on M M1 a n).
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
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBA1.FPB; left; unfold PMBAS.SCR; lia. }
{ left; reflexivity. } { exact HH1. } { exact PA1. } { exact ITB. } { reflexivity. } { exact CK. }
assert (KP1 : kept0 R1) by (intros k Hk0; rewrite (KS1 k) by (unfold PMBAS.CSK in Hk0; cbn in Hk0 |- *; tauto); apply KP; exact Hk0).
apply (grow_new 0x3734c fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr (PM.PS 2 len 0 0) T1 T2 T10 KP1 C120 C128).
- unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
- exact MO1.
- exact W1.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact ECZ].
- cbn [PM.p_k]. exact Hk.
- exact OPN.
- intros fx2 R2' M2 model2 B RP2 RB SV2 MO2 GS2 C120' C128' EC2 CK2 AGN.
apply (grow_g_c fx2 R2' M2 model2 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e (debit L cr (32 * 2 ^ (vk1 + 1))) B len); try assumption.
+ rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl. exact T2.
+ rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl. exact T8.
+ rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact R9.
+ rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact R18.
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. exact T19.
+ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. exact T20.
+ intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [apply KP1; exact Hk0|]. unfold PMBAS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
Qed.
Lemma grow_cap_t : ltac2:(TCodec.tc2 tcn__PmBa6C "TC'N&:y5'QIyR0%211%5241'1y8%611%311p061'9'H'I'0&?'4&Dv>vQ2vQ?r9%544321'3&Or:&QH&Q7uC%211%42M1%7261&Q4+R0%22>1%92Q01%=3Q051r;uD%<11%>2Q71%A241+1%A2Q81%E3Q831r<u:%D11%F2Q?1%I241r5%I2Q@1%M3Q@31'2&Q5zr6%3221+`PPP0%5231%7231&@&Q1r=&Q9+S9%22Q?1%64541;r7%?2>1&Q6+X0%2241%D241&Er?%23QJQI1&Cv7v<v8r@%56432QOQN1&Fv5vQCvQ<vQDvQKvQGvQ>rAr>%:@?98=7R965432<B1NQ@&KrB+8%R12R=1vQ:%55Q542Q<1&B(G+4%241Q8QJQ@%45A?=G1&MvQ3%231MG&L%133OI'Q0&A%116&JrHrG+VlZDrFrE%66QI54321v6%;4QK921p0=1p0@1p0D1p0J1p0Q11p0Q=1p0QD1p0QH1p0QO1p0R71p0R@1p0RI1p0S21p0SA1pSJSH1pS4SI1pRHSK1pRLSM1pS>SO1pS<T11pS6T31pHT51pLT;1pS2TB1").
Proof. intros fx R M model s1 sm e cr len tb.
intros RA R19 R20 R10 HLn TBY Htb SV MO W ECZ PK OPN OPD. pose proof RA as (R2 & R8 & R9 & R18 & KP).
prep_ctx M W MO.
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
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
assert (CAP : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x37154) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xae098) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 128 <= i < S - 128 + 16) -> ~ (S - 72 <= i < S - 72 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 9; 18; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0x3596c /\ getr R1 (reg 2) = Z_to_bv 64 (S - 128) /\ getr R1 (reg 8) = Z_to_bv 64 (2 ^ (vk1 + 1))
/\ getr R1 (reg 10) = Z_to_bv 64 (32 * 2 ^ (vk1 + 1)) /\ getr R1 (reg 19) = Z_to_bv 64 len /\ getr R1 (reg 20) = Z_to_bv 64 (32 * 2 ^ vk1)
/\ L5.u64_at RSEGS M1 (S - 128) (fb + 40) /\ L5.u64_at RSEGS M1 (S - 120) 0x373c4).
{ assert (KC : vk1 = 0 \/ vk1 = 1 \/ vk1 = 2 \/ vk1 = 3 \/ vk1 = 4 \/ vk1 = 5 \/ vk1 = 6 \/ vk1 = 7 \/ vk1 = 8 \/ vk1 = 9 \/ vk1 = 10) by lia.
destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- change (2 ^ 0) with 1 in *. change (2 ^ (0 + 1)) with 2.
cfeed P (PMBAP3T.baTs0_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 1) with 2 in *. change (2 ^ (1 + 1)) with 4.
cfeed P (PMBAP3T.baTs1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 2) with 4 in *. change (2 ^ (2 + 1)) with 8.
cfeed P (PMBAP3T.baTs2_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 3) with 8 in *. change (2 ^ (3 + 1)) with 16.
cfeed P (PMBAP3T.baTs3_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 4) with 16 in *. change (2 ^ (4 + 1)) with 32.
cfeed P (PMBAP3T.baTs4_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 5) with 32 in *. change (2 ^ (5 + 1)) with 64.
cfeed P (PMBAP3T.baTs5_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 6) with 64 in *. change (2 ^ (6 + 1)) with 128.
cfeed P (PMBAP3T.baTs6_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 7) with 128 in *. change (2 ^ (7 + 1)) with 256.
cfeed P (PMBAP3T.baTs7_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 8) with 256 in *. change (2 ^ (8 + 1)) with 512.
cfeed P (PMBAP3T.baTs8_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 9) with 512 in *. change (2 ^ (9 + 1)) with 1024.
cfeed P (PMBAP3T.baTs9_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120].
- change (2 ^ 10) with 1024 in *. change (2 ^ (10 + 1)) with 2048.
cfeed P (PMBAP3T.baTs10_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & _ & _ & _ & _ & T19 & T20 & C128 & C120 & _).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros i Hi N1 N2; apply FRZ1; assumption|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T10|]. split; [exact T19|]. split; [exact T20|]. split; [exact C128| exact C120]. }
destruct CAP as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T10 & T19 & T20 & C128 & C120).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x37154 R1 0xae098 M1
(fun a => (S - 128 <= a < S - 128 + 16) \/ (S - 72 <= a < S - 72 + 8)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M S SCR a STK). unfold PMBAS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 128 \/ S - 64 <= a) -> L5C.agree_on M M1 a n).
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
{ intros i Hi N. apply FRZ1; [exact Hi| |]; intros X; apply N; unfold PMBA1.FPB; left; unfold PMBAS.SCR; lia. }
{ left; reflexivity. } { exact HH1. } { exact PA1. } { exact ITB. } { reflexivity. } { exact CK. }
assert (KP1 : kept0 R1) by (intros k Hk0; rewrite (KS1 k) by (unfold PMBAS.CSK in Hk0; cbn in Hk0 |- *; tauto); apply KP; exact Hk0).
apply (grow_new 0x373c4 fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr (PM.PS 4 len tb 0) T1 T2 T10 KP1 C120 C128).
- unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; lia|lia|lia|assumption]).
- exact MO1.
- exact W1.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; lia|lia|lia| exact ECZ].
- cbn [PM.p_k]. exact Hk.
- exact OPN.
- intros fx2 R2' M2 model2 B RP2 RB SV2 MO2 GS2 C120' C128' EC2 CK2 AGN.
apply (grow_g_t fx2 R2' M2 model2 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e (debit L cr (32 * 2 ^ (vk1 + 1))) B len tb); try assumption.
+ rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl. exact T2.
+ rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl. exact T8.
+ rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact R9.
+ rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact R18.
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. exact T19.
+ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. exact T20.
+ intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [apply KP1; exact Hk0|]. unfold PMBAS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0.
+ apply (L5C.u8_at_agree RSEGS M M2); [intros i Hi; rewrite (AGN (S - 105) 1) by lia; apply FRZ1; lia|lia|lia| exact TBY].
Qed.
End Call.
End WithHeap.
End PMBA6C.

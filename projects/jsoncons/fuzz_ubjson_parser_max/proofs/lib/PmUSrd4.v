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
PmTxtSpecs PmTxtKit PmTxtKit2 PmUSrdP PmUSrd1 PmUSrd2 PmUSrd3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUSrd4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecs.PMPS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUSrd1.PMUSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "4Model"; "4m_vmmaps"; "5bvmap"; "0M"]; ["0M0"; "0M1"; "0R"; "0R0"; "6credit"; "6hi_heap"; "7SCFG"; "8SRC"; "8mu_src"; "8p_src"; "8p_tb"; "8parser_own"; "8pst"; "8sm_st"; "8sr_de"; "8sr_qc"]; ["8sr_rem"; "8strm"; "8vs_size"; "9with_src"; ":cfg"; ":consumed"; ":src_step"; ";IHt"; ";acct"; ";fields_eq"; ";kept6"; ";lregs"; ";state_ok"; "<FPState"; "<getr"; "=srealizes"]; [">mem_grows"; "?loaded_segments"; "0S"; "0SCFG_P"; "@add"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@opp"; "@pow"; "@sub"; "0c"; "0cr"; "0cr0"]; ["0fb"; "0fx"; "0i"; "0k"; "0len"; "0model"; "0model0"; "0mu0"; "0n"; "0s"; "0s0"; "0sm"; "0sm0"; "AZ_to_bv"; "Abv"; "0str"]; ["0w"; "0x"]]).
Module PMUSR4.
Import PMU.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Lemma subw : ltac2:(TCodec.tc2 tcn__PmUSrd4 "Q3'6'3&QEzr2%3221r1%5231%7231&QF&QK+2+R0%3221%52:1'4&QG&QL&QDr3&QH+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pT8Q11pU4Q21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmUSrd4 "G'6'3&QF&QJ&QK+2+R0%3221%511r1%8221z%:231%<231'4&QGr2%221:&QD%123<%63D31p081pU4F1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmUSrd4 "J'6'3&QF&QJ&QK+2+R0%3221%511r1%8221&QEz%2241%=241&QGr2%221:+1%A221'4r3%23F1:p041p0:1pU4I1").
Proof. intros x. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis FR1 : S <= fb.
Hypothesis FR2 : fb + 752 <= hl_sptop L.
Hypothesis FR3 : fb mod 16 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size (PM.p_tb s0) + PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis RSZ : PMU.str_resize_spec L HI.
Hypothesis SRD : PMPSU.src_read_spec L HI.
Hypothesis FBT : PMTXS.fill_buffer_tb_spec RSEGS AD L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
PMSP.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s0) + d ->
PM.parser_at RSEGS AD T3 T4 M' (PMSP.o_p AD fb) (PMSP.o_is AD fb) s' -> PM.iss_at RSEGS AD T3 M' (PMSP.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSP.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5C.hpres L LBX S (PMSP.pm_scr 5) (PMUSR1.W0 fb) M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
model_but_vm model0 model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
#[local] Abbreviation W0 := (PMUSR1.W0 fb).
#[local] Abbreviation saves9 := (PMUSR1.saves9 R0 S).
#[local] Abbreviation kept6 := (PMUSR1.kept6 R0).
#[local] Abbreviation memrel := (PMUSR1.memrel L M0 LBX S fb).
#[local] Abbreviation fields_eq := (PMUSR1.fields_eq s0).
#[local] Abbreviation acct := (PMUSR1.acct len s0 sm0).
#[local] Abbreviation state_ok := (PMUSR1.state_ok L HI R0 M0 model0 LBX cr0 S fb s0 str).
#[local] Abbreviation lregs := (PMUSR1.lregs R0 S fb len).
#[local] Abbreviation tbdst := (PMUSR1.tbdst fb).
#[local] Abbreviation lstate := (PMUSR1.lstate L HI R0 M0 model0 LBX cr0 S fb len s0 str sm0).
#[local] Abbreviation IHt := (PMUSR1.IHt L HI R0 M0 model0 K LBX cr0 S fb len s0 str sm0).
#[local] Abbreviation finish := (PMUSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PMUSR1.call_resize L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PMUSR1.call_srcread L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PMUSR1.call_filltb L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PMUSR1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation base_keep := (PMUSR1.base_keep L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation after_shrink := (PMUSR2.after_shrink L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat.
Lemma with_src_eta : ltac2:(TCodec.tc2 tcn__PmUSrd4 "A'L'4&Q3r1(G&O&I%114%311&N%113&Q0%115%93531%<2;1%>3?1<pTD@1").
Proof. intros s. destruct s as [a b c [q d e] f g h i j]; reflexivity. Qed.
Lemma pos_upd : ltac2:(TCodec.tc2 tcn__PmUSrd4 "RK'R>yR0%211'1y8%511%311p051'<'L'Q1&D&Q<v:v7vCv@vR6v;vQOvQBvR0vR:vR?r6r4r3r2r1%A@@?>=<;:987654321&Q@r7%2218'6'3&QEz%2219&QF&QK+2+R0%3221%52?1%:271&5&QD%12J6+X0%3221%?21G+8%6231%?2J1%D241%:11'4r:&R=%12QJQ1%311r;%113%73QI31p091p0E1pT6Q11&E&0'2%12Q5Q5&K%11Q@%5331QGr8&=%11Q=%:5QO4QD31r9r5%R4@R3R2R1R0QOQNQMQLQKQJQI26QAQH1p041p0@1p0QC1p0QG1pSNR:1pTHR<1pTDR>1pT<R@1pQ4RB1pQ0RC1").
Proof using All. intros M M1 model s sm cr.
intros SO MG FRZ HH1.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= fb + 320 \/ fb + 328 <= a) -> L5C.agree_on M M1 a m).
{ intros a m Ha Hm X i Hi. apply FRZ; lia. }
assert (AGH : forall B m, In (B, m) (PM.parser_own s ++ LBX) -> L5C.agree_on M M1 B m).
{ intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4). apply AG; lia. }
assert (EKn : PMK.ek L LBX S 22528 W0 M M1).
{ apply (PMK.ek_piece L LBX S 22528 W0 M M1 (fun a => fb + 64 + 256 <= a < fb + 64 + 256 + 8)); [intros a Ha N; apply FRZ; [exact Ha| exact N]|].
intros a Ha CA NE OW Pa. apply (OW (PMSP.o_src AD fb + 256, 40)); [unfold W0, PMSP.W_srcf; left; reflexivity|].
unfold L5.in_rng, PMSP.o_src, PMSP.o_p; cbn [fst snd pa_off_p AD PmLayoutU.ADDR_U]. lia. }
split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 22528 W0 M0 M M1 EK EKn).
- apply (PMK.dk_trans L LBX S 22528 M0 M M1 DK). apply PMK.dk_grows. exact MG.
- exact (PMK.stk_grows L M M1 S 22528 MG STK).
- split.
{ destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
unfold PMUSR1.saves9. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption]). }
split.
{ pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & _ & VEC & _).
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (INV : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
destruct (BR _ _ INV) as (V0 & _ & V4).
rewrite <- (with_src_eta s).
apply (PMPK.parser_src_upd RSEGS AD M M1 (fb + 40) (fb + 440) s (PM.sr_de (PM.p_src s)) (PM.sr_rem (PM.p_src s)) PA); [lia|lia| | | | | | | | | | | | | | |].
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG.
- apply PMPK.dkr_grows. exact MG.
- lia.
- lia.
- exact (AGH _ _ INV).
- intros c n p E. apply PMPK.dkr_grows. exact MG.
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia; exact F4].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia; exact F5].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| replace (fb + 40 + 304) with (fb + 40 + 24 + 280) by lia; exact F6].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| replace (fb + 40 + 312) with (fb + 40 + 24 + 288) by lia; exact F7].
- exact G1.
- exact G2.
- exact G3. }
split.
{ apply (PMF.iss_at_agree RSEGS AD M M1 (fb + 440) str sm); [lia|lia| apply AG; lia| |exact IA].
intros c n p E. assert (INs : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
exact (AGH _ _ INs). }
split; [exact (base_keep M M1 EKn STK BASE)|].
split; [exact TBOK|]. split; [exact HH1|]. split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.
Lemma d_after_fill : ltac2:(TCodec.tc2 tcn__PmUSrd4 "VB'6&Q7vQCv:v7vCv@vR6v9v;vQOvQBvR0vR4vR:vR?vR<r1%A@@?>=<;:987654321'Q=&>y5'R>yR0%211%5241'1y8%611%311p061'<'L'Q1&D'4&Q>r9&R=&QIu2%211%42E1%7261&QL+R@%22Q31%92H1%=3H51r:u8%<11%>2O1%A241%@2OQ9%D3O21r;u9%C11%E2Q61%H241&QD+[H%22QC1%J2Q91%N3Q951r<u:%M11%O2Q@1%Q2241r4%Q22QA1%Q63QA31r=uB%Q511%Q72QH1%Q:241+R0%C2R41%Q;2QJ1%Q?3QJ41r>uC%Q>11%Q@2R11%QC241+`P0%QC2R21%QG3R231r?uE%QF11%QH2R91%QK241%QJ2R9QK%QN3R921r@uF%QM11%QO2R@1%R2241+1%Q;2Q91%R32RB1%R73RB41rAuG%R611%R82RI1%R;241%R:2RIQO%R>3RI21&Q:rB%22S?1'3&QEz%221R0%32R1Q1%5221%52Q3Q8%62Q9S?%8221&Q<rDrC%3@SNSMSLSKSJSHSGSFSESCSB21>FO&Q2&J%114%311%R92Q;Q>%S43T721%B2AQ6%61SK%811%RO2SNH%R?221%S:3T=Q21&Q5&I%11T2rF%311rE%6442T41%S92T8E%RI21Q;%SD3TG31&Q6rG%;11%34;1T;:&Q9rH%22T@1&QF&HrI%C11%3216rO%6221'Q?&QA&F%11U7&Q4rNrM+WRXLrLrK%66954321%;4:81U9p0=1p0E1p0I1p0N1p0Q91p0Q?1p0QA1p0QH1p0QM1p0R11p0R81p0R<1p0RD1p0RN1p0S61p0S?1p0SI1p0T21p0T=1p0TE1pSLV61pTBV71pU2V81pSNU71pTHU91pTDU;1pT<U=1pQ0U?1pQ6UE1pT4UL1pBUN1pT@VA1").
Proof using All. intros mu0 IH fx R M model s sm cr w n c.
intros A2 A8 A9 A10 A18 A19 A21 A22 A23 KP Hc Hw SO SZ Hn0 En CONS STEP FE MU.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
assert (Hn : n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
destruct SRC as (_ & _ & F3 & _).
assert (D256 : L5.defined M (fb + 64 + 256) 8) by (replace (fb + 64 + 256) with (fb + 40 + 24 + 256) by lia; exact F3).
assert (W256 : L5.writable RSEGS M (fb + 64 + 256) 8) by (apply (L5C.writable_of_defined RSEGS M _ 8 D256); destruct STOP; lia).
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
pose proof (PMUSRP.utsD3_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 43%nat => n | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23)) | 53%nat => c | _ => 0 end)) as PP.
cbn beta iota in PP. bvr.
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
set (P := fun a => fb + 64 + 256 <= a < fb + 64 + 256 + 8).
assert (SPC : forall pc1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x3891c) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
(state_ok M1 model s sm cr -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3891c M model) K).
{ intros pc1 MS NEXT. unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x3891c R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
- intros a Ha N. apply FRZ; [exact Ha| exact N].
- intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M S 22528 a STK). lia.
- intros a. unfold P. apply PMK.rng_dec.
- intros HH1. apply NEXT. apply (pos_upd M M1 model s sm cr SO MG); [|exact HH1]. intros i Hi N. apply FRZ; [exact Hi| exact N]. }
destruct EX as [(MS & KS & E1 & E10 & E11 & E12 & E20 & C0) | [(MS & KS & E20 & E21 & C0 & C1) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & C0 & C1)]];
apply (SPC _ MS); intros SO1.
-
assert (DK' : c < 16384).
{ destruct (Z.eq_dec c 16384) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
apply (call_resize fx1 R1 M1 model s sm cr (n + c) 231744); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ kept_tac KS KP.
+ unfold PM.CHUNK. lia.
+ unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (after_shrink mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 w c); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 20%nat RP2) by PMK.inl. exact E20.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* unfold PMUSR1.acct. cbn [PMTK2.with_tb PM.p_src PM.p_tb]. split; [lia|]. split; [lia|]. split; [exact STEP|].
destruct FE as (F1 & F2 & F3' & F4 & F5 & F6). unfold PMUSR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
-
rewrite subw in C0 by lia.
assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
apply (IH fx1 R1 M1 model s sm cr (w - 16384) MU).
split; [|split; [exact SO1| split; [|lia]]].
+ unfold PMUSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [exact E21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
kept_tac KS KP.
+ unfold PMUSR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
-
rewrite subw in C0 by lia.
assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
apply (finish fx1 R1 M1 model s sm cr 0); try assumption.
+ kept_tac KS KP.
+ rewrite E10. f_equal. lia.
+ lia.
+ unfold PMUSR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.
Lemma d_after_resize : ltac2:(TCodec.tc2 tcn__PmUSrd4 "V7'6&Q7vQCv:v7vCv@vR6v9v;vQOvQBvR0vR4vR:vR?vR<r1%A@@?>=<;:987654321'Q=&>y5'R>yR0%211%5241'1y8%611%311p061'<'L'Q1&D'4&Q>r8&R=&QIu2%211%42E1%7261&QL+R@%22Q31%92H1%=3H51r9u8%<11%>2O1%A241%@2OQ9%D3O21r:u9%C11%E2Q61%H241&QD+[H%22QC1%J2Q91%N3Q951r;uB%M11%O2Q@1%Q2241+R0%;2QL1%Q32QB1%Q73QB41r<uC%Q611%Q82QI1%Q;241+`P0%Q;2QJ1%Q?3QJ31r=uE%Q>11%Q@2R11%QC241r7%QC2R21%QG3R231r>uF%QF11%QH2R91%QK241+1%Q42Q21%QL2R;1%R03R;41r?uG%QO11%R12RB1%R4241%R32RBR4%R73RB21&Q:r@%22S81'3&QE%12Q0Q>%22Q?S4%4221&Q<rA%2@SBSAS@S?S>S<S;S:S9S7S619AJQ2&Q2&J%11<%311%QM2Q?Q:%RH3SK21z%>21Q:%71S@%911%RD2SCL%R4221%RO3T2Q71&Q5&I%11SGrC%311rB%6442SI1%RN2SMN%S83T;21&Q6rD%:11%34:1SO9&Q9rE%22T41&M%113%SB3TE1I&HrG%D11rF%4221rM%Q=221'Q?&QA&F%11TN&Q4rLrK+WRW<rJrI%66954321%;4:81U0p0=1p0E1p0I1p0M1p0Q21p0Q<1p0QB1p0QE1p0QL1p0R01p0R61p0R:1p0RB1p0RL1p0S51p0S>1p0SH1p0T31p0T;1pTBUL1pU2UM1pSNTL1pTHTN1pTDU01pT<U21pQ0U41pQ6U:1pT4UA1pBUC1pT@V61").
Proof using All. intros mu0 IH fx R M model s sm cr w n.
intros A2 A8 A9 A18 A19 A21 A22 A23 KP Hw SO SZ Hn0 En CONS STEP FE ST0 MU.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
assert (Hn : n < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (fb + 40 + 336) with (fb + 376) in VS by lia.
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & _ & VS) SZ; cbn [PM.vs_size] in SZ.
-
exfalso. destruct VS as (Hn1 & _). lia.
- destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
pose proof (PMF.u8_of_u64 RSEGS M (fb + 376) (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
assert (IN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (BR q1 c1 IN) as (Q0 & _ & Q4).
cfeed PP (PMUSRP.utsD2_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => (c1 + 1) mod 256 | 41%nat => q1 | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x388ec R1 0x37720 M K Mh Ml MS).
apply (call_filltb fx1 R1 M model s sm cr (q1 + n) 231708 c1 n1 q1); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ kept_tac KS KP.
+ lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 sm2 c RP2 Y10 Hc G2 STF STEP2 SO2.
destruct (STF ST0) as (Ec & ST2).
pose proof (unread_nn M2 model s sm2 cr SO2) as (UN2 & ST2' & RM2 & GE2).
assert (CONS2 : PMSP.consumed (PM.p_src s) (PM.p_src s) sm sm2 = c).
{ unfold PMSP.consumed, PM.unread. destruct STEP2 as (_ & E2 & _). lia. }
apply (d_after_fill mu0 IH fx2 R2 M2 model s sm2 cr w n c); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
* rewrite (PMK.cs_of_preserved R1 R2 23%nat RP2) by PMK.inl. rewrite (KS 23%nat) by PMK.inl. exact A23.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
* rewrite ETB. cbn [PM.vs_size]. exact SZ.
* unfold PMSP.consumed in *. lia.
* exact (PMUSR3.src_step_trans _ _ _ _ _ _ STEP STEP2).
* enough (PM.mu_src (PM.p_src s) sm2 < PM.mu_src (PM.p_src s) sm) by lia.
apply (PMUSR3.mu_dec _ _ _ _ STEP2 ST ST2').
destruct (Z.ltb_spec c PM.CHUNK) as [LT|GE']; [right; split; [exact ST0| exact ST2]| left].
unfold PMSP.consumed in CONS2. unfold PM.CHUNK in *. lia.
Qed.
Lemma dpath : ltac2:(TCodec.tc2 tcn__PmUSrd4 "S7'6&Q7vQCv:v7vCv@vR6v9v;vQOvQBvR0vR4vR:vR?vR<r1%A@@?>=<;:987654321'Q=&>y5'R>yR0%211%5241'1y8%611%311p061'<'L'Q1&D&Q;r7%26Q0JIH1D'4&Q>r8&R=&QIuC%211%42H1%7261+`P0%72I1%;3I31'3&QEr3%2261%322Q9%5221&Q<r9r6r5%4@QIQHQGQFQEQCQBQAQ@Q>Q=3DH21&Q8%16QAQ@Q>FJ3&M%11Hz%L3R221&H&Ir:%211%421>r@%F221'Q?&QA&F%11R;&Q4r?r>+WRV4r=r<%66954321%;4:81R=p0=1p0E1p0J1p0M1p0Q31p0Q:1p0QG1pU2RM1pSNQL1pTHQN1pTDR01pT<R21pQ0R41pQ6R:1pT4RA1pBRC1pT@S61").
Proof using All. intros mu0 IH fx R M model s sm cr w.
intros (A2 & A8 & A9 & A18 & A21 & A22 & KP) A19 Hw SO (CONS & SZ & STEP & FE) ST0 MU.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (fb + 40 + 336) with (fb + 376) in VS by lia.
revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & _ & VS) SZ; cbn [PM.vs_size] in SZ.
-
destruct VS as (Hn1 & B0).
pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMUSRP.utsDS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => 2 * n1 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E23).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x388c4 R1 0x57d34 M K Mh Ml MS).
assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + 16384)) by (rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 11))), E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; rewrite Z.mod_small by lia; lia).
assert (E23' : getr R1 (reg 23) = Z_to_bv 64 n1) by (rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 23))), E23; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
apply (call_resize fx1 R1 M model s sm cr (n1 + 16384) 231660); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ kept_tac KS KP.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (d_after_resize mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 w n1); try assumption; try lia.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
* rewrite (PMK.cs_of_preserved R1 R2 23%nat RP2) by PMK.inl. exact E23'.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
pose proof (PMF.u8_of_u64 RSEGS M (fb + 376) (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
cfeed PP (PMUSRP.utsDL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => (c1 + 1) mod 256 | 40%nat => n1 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E23).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x388c4 R1 0x57d34 M K Mh Ml MS).
apply (call_resize fx1 R1 M model s sm cr (n1 + 16384) 231660); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ kept_tac KS KP.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (d_after_resize mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 w n1); try assumption; try lia.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
* rewrite (PMK.cs_of_preserved R1 R2 23%nat RP2) by PMK.inl. exact E23.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMUSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
Qed.
End Call.
End WithHeap.
End PMUSR4.

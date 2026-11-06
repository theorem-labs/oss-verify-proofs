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
PmTxtSpecs PmTxtKit PmTxtKit2 PmSSrdP PmSSrd1 PmSSrd2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSSrd3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2and"; "2eq"; "2or"; "3Z"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"]; ["6credit"; "7SCFG"; "8CHUNK"; "8mu_src"; "8p_src"; "8p_tb"; "8pst"; "8sm_st"; "8sr_rem"; "8srcst"; "8strm"; "8unread"; "8vs_size"; "9IHt"; "9acct"; "9fields_eq"]; ["9kept7"; "9lregs"; "9state_ok"; "9tbdst"; ":cfg"; ":consumed"; ":src_step"; ";FPState"; ";getr"; "<srealizes"; "=loaded_segments"; "0S"; "0SCFG_P"; ">add"; ">le"; ">lt"]; [">modulo"; ">mul"; ">of_nat"; ">opp"; ">pow"; ">sub"; "0a"; "0b"; "0c"; "0cr"; "0cr0"; "0fb"; "0fx"; "0k"; "0len"; "0model"]; ["0model0"; "0mu0"; "0n"; "0p"; "0s"; "0s0"; "0sa"; "0sb"; "0sc"; "0sm"; "0sm'"; "0sm0"; "0src"; "0src'"; "?Z_to_bv"; "?bv"]; ["0str"; "0w"; "0x"]]).
Module PMSSR3.
Import PMS.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Lemma subw : ltac2:(TCodec.tc2 tcn__PmSSrd3 "Q3'4'1&Q>zr2%3221r1%5231%7231&Q?&QD+2+R0%3221%52:1'2&Q@&QE&Q=r3&QA+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pSLQ11pU6Q21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmSSrd3 "G'4'1&Q?&QC&QD+2+R0%3221%511r1%8221z%:231%<231'2&Q@r2%221:&Q=%123<%63D31p081pU6F1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmSSrd3 "J'4'1&Q?&QC&QD+2+R0%3221%511r1%8221&Q>z%2241%=241&Q@r2%221:+1%A221'2r3%23F1:p041p0:1pU6I1").
Proof. intros x. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.
Lemma src_step_trans : ltac2:(TCodec.tc2 tcn__PmSSrd3 "B'I'J&Q6r6r5r3r2%544321r8%741654p031p041pTB;1pT@<1pT>=1pSB?1pS@@1pS>A1").
Proof. intros a b c sa sb sc.
unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Lemma mu_dec : ltac2:(TCodec.tc2 tcn__PmSSrd3 "Q>'I'J&Q6r4r3r2r1%544321'3'2'4&G%118z%53421+2%73641%9231&Q?&Kr6%221Br7r5%5221%7241'1%@14%C3B1?%B1J%E3D1?%5231%H271&C%12<;r8%321@%C231p061p0F1p0G1p0Q21pTFQ91pTDQ:1pTLQ<1pTJQ=1").
Proof. intros src src' sm sm'.
unfold PM.mu_src. intros (_ & _ & _ & S2 & U) ST ST' H.
destruct ST as [E|E]; destruct ST' as [E'|E']; rewrite ?E, ?E' in *; cbn [Z.eqb]; [lia|lia| specialize (S2 eq_refl); lia| lia].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
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
Hypothesis RSZ : PMS.str_resize_spec L HI.
Hypothesis SRD : PMPSS.src_read_spec L HI.
Hypothesis FBT : PMTXS.fill_buffer_tb_spec RSEGS AD L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
PMSP.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s0) + d ->
PM.parser_at RSEGS AD T3 T4 M' (PMSP.o_p AD fb) (PMSP.o_is AD fb) s' -> PM.iss_at RSEGS AD T3 M' (PMSP.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSP.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5C.hpres L LBX S (PMSP.pm_scr 5) (PMSSR1.W0 fb) M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
model_but_vm model0 model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
#[local] Abbreviation W0 := (PMSSR1.W0 fb).
#[local] Abbreviation saves8 := (PMSSR1.saves8 R0 S).
#[local] Abbreviation kept7 := (PMSSR1.kept7 R0).
#[local] Abbreviation memrel := (PMSSR1.memrel L M0 LBX S fb).
#[local] Abbreviation fields_eq := (PMSSR1.fields_eq s0).
#[local] Abbreviation acct := (PMSSR1.acct len s0 sm0).
#[local] Abbreviation state_ok := (PMSSR1.state_ok L HI R0 M0 model0 LBX cr0 S fb s0 str).
#[local] Abbreviation lregs := (PMSSR1.lregs R0 S fb len).
#[local] Abbreviation tbdst := (PMSSR1.tbdst fb).
#[local] Abbreviation lstate := (PMSSR1.lstate L HI R0 M0 model0 LBX cr0 S fb len s0 str sm0).
#[local] Abbreviation IHt := (PMSSR1.IHt L HI R0 M0 model0 K LBX cr0 S fb len s0 str sm0).
#[local] Abbreviation finish := (PMSSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PMSSR1.call_resize L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PMSSR1.call_srcread L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PMSSR1.call_filltb L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PMSSR1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation after_read := (PMSSR2.after_read L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
Lemma at_srcread : ltac2:(TCodec.tc2 tcn__PmSSrd3 "WH'4&MvQ<v8v5v?v=vR0v7v9vQJvQ;vQKvQNvR5vR@vR;r1%A@@?>=<;:987654321'Q7&;y5'R?yR0%211%5241'0y8%611%311p061':'F'J&@'2&Q8r:&R>&QBu1%211%42E1%7261+Vn\@%72F1%;3F31r;u2%:11%<2M1%?241&QE+R0%22Q;1%A2Q01%E3Q051r<u8%D11%F2Q71%I241%H2Q7QA%L3Q721r=u9%K11%M2Q>1%Q0241&Q=+[H%22QK1%Q22QA1%Q63QA51r>u:%Q511%Q72QH1%Q:241%:2R3J%Q:2QI1%Q>3QI31r?u;%Q=11%Q?2R01%QB241r6%QB2R11%QF3R131r@u<%QE11%QG2R81%QJ241r9%QJ2R91%QN3R931rAuB%QM11%QO2R@1%R2241%R43R?1GrBuC%R311%R52RF1%R8241%R72RFQN%R;3RF21rCuD%R:11%R<2RM1%R?241%R>2RMQD%RB3RM21rDuE%RA11%RC2S41%RF241+1%QG2QE1%RG2S61%RK3S641rEuF%RJ11%RL2S=1%RO241%S13S<1@&Q0rF%22T21'1&Q>%12?Q@%22QAQ9%4221&B%52Q<1%62Q0T2&Q3rG%24T61Q@Q3&Q2rJrIrH%4@TDTCTBTAT@T>T=T<T;T9T83216A&L&E%115%311%RG2Q6M%SJ3TM21z%F21Q0%71TB%911%S>2TE<%RN221%T13U4N1&Q5&D%11TIrL%311rK%6442TK1%SH2TOG%T:3U=21&Q6rM%:11%34:1U19&OrN%22U61'3&HrO%B11%311%QA2QO1&G%119%TJ3UM1O%9241&CrQ0%K11%321;rQ6%QK221'Q9&Q:&A%11V6&Q4rQ5rQ4+VjQ@rQ3rQ2%66954321%;4:81V8p0=1p0D1p0O1p0Q31p0Q81p0QB1p0QH1p0QK1p0R21p0R81p0R<1p0R>1p0RA1p0RG1p0RK1p0S21p0S<1p0SD1p0SL1p0T31p0T<1p0TE1p0TN1p0U91p0UA1p0UL1pT8W;1pT6W<1pSLW=1pU4W>1pSDV=1pTDV?1pT:VA1pT0VC1pJVE1pNVK1pSJW21p>W41pT4WG1").
Proof using All. intros mu0 IH fx R M model s sm cr w k n p.
intros A1 A2 A8 A9 A10 A11 A12 A18 A19 A20 A21 A22 KP Hk HkC Hw DST SO SZ Hn0 En CONS STEP FE PRG MU.
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
apply (call_srcread fx R M model s sm cr p k 227728 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 ltac:(lia) DST SO).
intros fx2 R2 M2 src2 sm2 d RP2 Y10 Hd CONS2 POS ZERO STEP2 SO2.
pose proof (unread_nn M2 model _ sm2 cr SO2) as (UN2 & ST2 & RM2 & GE2). cbn [PMPS.with_src PM.p_src] in UN2, RM2.
apply (after_read mu0 IH fx2 R2 M2 model (PMPS.with_src s src2) sm2 cr w k d n); try assumption.
- rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl. exact A2.
- rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl. exact A8.
- rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl. exact A9.
- rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl. exact A18.
- rewrite (PMK.cs_of_preserved R R2 19%nat RP2) by PMK.inl. exact A19.
- rewrite (PMK.cs_of_preserved R R2 20%nat RP2) by PMK.inl. exact A20.
- rewrite (PMK.cs_of_preserved R R2 21%nat RP2) by PMK.inl. exact A21.
- rewrite (PMK.cs_of_preserved R R2 22%nat RP2) by PMK.inl. exact A22.
- intros x Hx. rewrite (PMK.cs_of_preserved R R2 x RP2) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- unfold PMSP.consumed in *. cbn [PMPS.with_src PM.p_src]. lia.
- cbn [PMPS.with_src PM.p_src]. exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
- cbn [PMPS.with_src PM.p_src]. enough (PM.mu_src src2 sm2 < PM.mu_src (PM.p_src s) sm) by lia.
apply (mu_dec _ _ _ _ STEP2 ST ST2).
unfold PMSP.consumed in CONS2. destruct (Z.eq_dec d 0) as [D0|D0]; [right| left; lia].
destruct (ZERO D0) as (_ & E2). split; [|exact E2].
destruct PRG as [P1|P1]; [specialize (POS P1); lia| exact P1].
Qed.
Lemma after_resize1 : ltac2:(TCodec.tc2 tcn__PmSSrd3 "VC'4&MvQ<v8v5v?v=vR0v7v9vQJvQ;vQKvQNvR5vR@vR;r1%A@@?>=<;:987654321'Q7&;y5'R?yR0%211%5241'0y8%611%311p061':'F'J&@'2&Q8r9&R>&QBu2%211%42E1%7261&QE+R0%22Q31%92H1%=3H51r:u8%<11%>2O1%A241%@2OQ9%D3O21r;u9%C11%E2Q61%H241&Q=+[H%22QC1%J2Q91%N3Q951r<uB%M11%O2Q@1%Q2241%:2QKJ%Q22QA1%Q63QA31r=uC%Q511%Q72QH1%Q:241r6%Q:2QI1%Q>3QI31r>uD%Q=11%Q?2R01%QB241r8%QB2R11%QF3R131r?uE%QE11%QG2R81%QJ241+1%Q32Q11%QK2R:1%QO3R:41r@uF%QN11%R02RA1%R3241%R53R@1@&Q0rA%22S61'1&Q>%12?QF%22QGQ=%4221&B%52Q@1%62Q1S6&Q2rDrCrB%4@SESDSCSBSAS?S>S=S<S:S9321>E&L&E%115%311%R02Q;Q3%RK3SN21z%C21Q6%71SC%911%RG2SF<%R7221%S23T5Q21&Q5&D%11SJrF%311rE%6442SL1%S12T0G%S;3T>21&Q6rG%:11%34:1T29&OrH%22T71'3&HrI%B11%311%Q>2QL1&G%119%SK3TN1O%9241&CrJ%K11%321;rQ0%QH221'Q9&Q:&A%11U7&Q4rOrN+Vn[<rMrL%66954321%;4:81U9p0=1p0D1p0O1p0Q31p0Q81p0QB1p0QH1p0QK1p0R21p0R81p0R:1p0R=1p0RC1p0RG1p0RN1p0S81p0SA1p0SJ1p0T31p0T>1p0TF1pT6V71pSLV81pU4V91pSDU81pTDU:1pT:U<1pT0U>1pJU@1pNUF1pSJUM1p>UO1pT4VB1").
Proof using All. intros mu0 IH fx R M model s sm cr w k n.
intros A2 A8 A9 A18 A19 A20 A21 A22 KP Hk HkC Hw SO SZ Hn0 En CONS STEP FE PRG MU.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
assert (Hn : n < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (fb + 40 + 336) with (fb + 376) in VS by lia.
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & _ & VS) SZ; cbn [PM.vs_size] in SZ.
-
destruct VS as (Hn1 & B0).
pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMSSRP.tsQS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => 2 * n1 | 42%nat => k | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3796c R1 0x36830 M K Mh Ml MS).
apply (at_srcread mu0 IH fx1 R1 M model s sm cr w k n (fb + 376 + n + 1)); try assumption.
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ rewrite (KS 8%nat) by PMK.inl. exact A8.
+ rewrite (KS 9%nat) by PMK.inl. exact A9.
+ rewrite (KS 18%nat) by PMK.inl. exact A18.
+ rewrite (KS 19%nat) by PMK.inl. exact A19.
+ rewrite (KS 20%nat) by PMK.inl. exact A20.
+ rewrite (KS 21%nat) by PMK.inl. exact A21.
+ rewrite (KS 22%nat) by PMK.inl. exact A22.
+ kept_tac KS KP.
+ unfold PMSSR1.tbdst. left. split; [exists n1; exact ETB|]. lia.
+ rewrite ETB. exact SZ.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
pose proof (PMF.u8_of_u64 RSEGS M (fb + 376) (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
assert (IN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (BR q1 c1 IN) as (Q0 & _ & Q4).
cfeed PP (PMSSRP.tsQL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => (c1 + 1) mod 256 | 41%nat => q1 | 42%nat => k | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3796c R1 0x36830 M K Mh Ml MS).
apply (at_srcread mu0 IH fx1 R1 M model s sm cr w k n (q1 + n)); try assumption.
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ rewrite (KS 8%nat) by PMK.inl. exact A8.
+ rewrite (KS 9%nat) by PMK.inl. exact A9.
+ rewrite (KS 18%nat) by PMK.inl. exact A18.
+ rewrite (KS 19%nat) by PMK.inl. exact A19.
+ rewrite (KS 20%nat) by PMK.inl. exact A20.
+ rewrite (KS 21%nat) by PMK.inl. exact A21.
+ rewrite (KS 22%nat) by PMK.inl. exact A22.
+ kept_tac KS KP.
+ unfold PMSSR1.tbdst. right. exists c1, n1, q1. split; [exact ETB|]. lia.
+ rewrite ETB. exact SZ.
Qed.
Lemma rpath : ltac2:(TCodec.tc2 tcn__PmSSrd3 "SF'4&MvQ<v8v5v?v=vR0v7v9vQJvQ;vQKvQNvR5vR@vR;r1%A@@?>=<;:987654321'Q7&;y5'R?yR0%211%5241'0y8%611%311p061':'F'J&@&Q1r8r2%36Q1KJI21'2&Q8r9&R>&QBuC%211%42I1%7261%62I;%:3I21'1&Q>+1r3%3221r4%5231%7231&B%8241r6%:21Q@&Q2r<r;r:%4@QOQNQMQLQKQIQHQGQFQDQC321IN&N%16QGQFQD43Q0'3&H&D%119%311%G2F1&G%11<z%Q73R>21%:251&Cr=%;11%321DrC%Q2221'Q9&Q:&A%11RG&Q4rBrA+VnZ4r@r?%66954321%;4:81RIp0=1p0D1p0Q01p0Q31p0Q91p0Q<1p0Q?1p0QH1p0R41pSLS;1pU4S<1pSDR;1pTDR=1pT:R?1pT0RA1pJRC1pNRI1pSJS01p>S21pT4SE1").
Proof using All. intros mu0 IH fx R M model s sm cr w k.
intros (A2 & A8 & A9 & A18 & A20 & A21 & KP) A19 Hk HkC Hw SO (CONS & SZ & STEP & FE) PRG MU.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (fb + 40 + 336) with (fb + 376) in VS by lia.
assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & _ & VS) SZ; cbn [PM.vs_size] in SZ.
-
destruct VS as (Hn1 & B0).
pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMSSRP.tsRS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => 2 * n1 | 42%nat => k | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E22).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37944 R1 0x56ce0 M K Mh Ml MS).
assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + k)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
assert (E22' : getr R1 (reg 22) = Z_to_bv 64 n1) by (rewrite E22; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
apply (call_resize fx1 R1 M model s sm cr (n1 + k) 227692); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ kept_tac KS KP.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (after_resize1 mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 w k n1); try assumption; try lia.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
* rewrite (PMK.cs_of_preserved R1 R2 20%nat RP2) by PMK.inl. rewrite (KS 20%nat) by PMK.inl. exact A20.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. exact E22'.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
pose proof (PMF.u8_of_u64 RSEGS M (fb + 376) (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
cfeed PP (PMSSRP.tsRL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 39%nat => (c1 + 1) mod 256 | 40%nat => n1 | 42%nat => k | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E22).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37944 R1 0x56ce0 M K Mh Ml MS).
apply (call_resize fx1 R1 M model s sm cr (n1 + k) 227692); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ kept_tac KS KP.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (after_resize1 mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 w k n1); try assumption; try lia.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
* rewrite (PMK.cs_of_preserved R1 R2 20%nat RP2) by PMK.inl. rewrite (KS 20%nat) by PMK.inl. exact A20.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. exact E22.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
Qed.
End Call.
End WithHeap.
End PMSSR3.

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
PmTxtSpecs PmTxtKit PmTxtKit2 PmSSrdP PmSSrd1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSSrd2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2and"; "2eq"; "3Z"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"; "6credit"]; ["7SCFG"; "8CHUNK"; "8mu_src"; "8p_src"; "8p_tb"; "8pst"; "8strm"; "8vs_size"; "9IHt"; "9acct"; "9fields_eq"; "9kept7"; "9state_ok"; ":cfg"; ":consumed"; ":src_step"]; [";FPState"; ";getr"; "<srealizes"; "=loaded_segments"; "0S"; "0SCFG_P"; ">add"; ">le"; ">lt"; ">modulo"; ">mul"; ">of_nat"; ">opp"; ">pow"; ">sub"; "0cr"]; ["0cr0"; "0d"; "0fb"; "0fx"; "0k"; "0len"; "0model"; "0model0"; "0mu0"; "0n"; "0s"; "0s0"; "0sm"; "0sm0"; "?Z_to_bv"; "?bv"]; ["0str"; "0w"; "0x"]]).
Module PMSSR2.
Import PMS.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Lemma subw : ltac2:(TCodec.tc2 tcn__PmSSrd2 "Q3'3'1&Q7zr2%3221r1%5231%7231&Q8&Q=+2+R0%3221%52:1'2&Q9&Q>&Q6r3&Q:+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pS:Q11pT6Q21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmSSrd2 "G'3'1&Q8&Q<&Q=+2+R0%3221%511r1%8221z%:231%<231'2&Q9r2%221:&Q6%123<%63D31p081pT6F1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmSSrd2 "J'3'1&Q8&Q<&Q=+2+R0%3221%511r1%8221&Q7z%2241%=241&Q9r2%221:+1%A221'2r3%23F1:p041p0:1pT6I1").
Proof. intros x. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.
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
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.
Lemma after_shrink : ltac2:(TCodec.tc2 tcn__PmSSrd2 "U5'3&HvQ5v7v4v>v<vQGv6v8vQ@vQ4vQBvQEvQKvR0vQMr1%A@@?>=<;:987654321'Q0&:y5'QOyR0%211%5241'0y8%611%311p061'9'E'F&?'2&Q1r8&QN&Q;u2%211%42E1%7261&Q>+R0%22Q31%92H1%=3H51r9u8%<11%>2O1%A241%@2OQ9%D3O21r:u9%C11%E2Q61%H241&Q6+[H%22QC1%J2Q91%N3Q951r;uB%M11%O2Q@1%Q2241%:2QKJ%Q22QA1%Q63QA31r<uC%Q511%Q72QH1%Q:241r5%Q:2QI1%Q>3QI31r=uD%Q=11%Q?2R01%QB241r7%QB2R11%QF3R131r>uE%QE11%QG2R81%QJ241+1%Q32Q11%QK2R:1%QO3R:41&Kr?%22S01'1&Q7z%221QH%32QIQB%5221&A%62QE1%72?Q4%82Q5S2%:221&LrBrAr@%4@SBSAS@S?S>S<S;S:S9S7S6321AK&I%R;2MQ5%26S;S:S8541&Q8&B&C%11:%321:rH%6221'Q2&Q3&@%11T1&MrGrF+Vn`@rErD%66954321%;4:81T3p0=1p0E1p0I1p0O1p0Q31p0Q61p0Q=1p0QA1p0QK1p0R41p0R=1p0RF1p0S11p0S91pS4TJ1pT4TK1pS0SJ1pSJSL1pSFSN1pS>T01pHT21pLT81pS8T?1p<TA1pSBU41").
Proof using All. intros mu0 IH fx R M model s sm cr w d.
intros A2 A8 A9 A18 A19 A20 A21 KP Hd HdC Hw SO AC MU. unfold PM.CHUNK in HdC.
pose proof SO as ((EK & DK & STK) & SV & _ & _ & _ & _ & _ & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
pose proof (PMSSRP.tsF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w | 42%nat => d
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) as PP.
cbn beta iota in PP. bvr.
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E20 & C0) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & C0)]).
- assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37a10 R1 0x37900 M K Mh Ml MS).
rewrite subw in C0 by lia.
apply (IH fx1 R1 M model s sm cr (w - d) MU).
split; [|split; [exact SO| split; [exact AC| lia]]].
unfold PMSSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [exact E20|]. split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
intros x Hx. rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37a10 R1 0x37a40 M K Mh Ml MS).
rewrite subw in C0 by lia.
apply (finish fx1 R1 M model s sm cr 0); try assumption.
+ intros x Hx. rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ rewrite E10. f_equal. lia.
+ lia.
+ replace 0 with (w - d) by lia. exact AC.
Qed.
Lemma after_read : ltac2:(TCodec.tc2 tcn__PmSSrd2 "VJ'3&HvQ5v7v4v>v<vQGv6v8vQ@vQ4vQBvQEvQKvR0vQMr1%A@@?>=<;:987654321'Q0&:y5'QOyR0%211%5241'0y8%611%311p061'9'E'F&?'2&Q1r:&QN&Q;u2%211%42E1%7261&Q>+R0%22Q31%92H1%=3H51r;u8%<11%>2O1%A241%@2OQ9%D3O21r<u9%C11%E2Q61%H241&Q6+[H%22QC1%J2Q91%N3Q951r=u:%M11%O2Q@1%Q2241r5%Q22QA1%Q63QA31r>uB%Q511%Q72QH1%Q:241%B2R3Q2%Q:2QI1%Q>3QI31r?uC%Q=11%Q?2R01%QB241r8%QB2R11%QF3R131r@uD%QE11%QG2R81%QJ241%QI2R8QJ%QM3R821rAuE%QL11%QN2R?1%R1241+1%Q:2Q81%R22RA1%R63RA41rBuF%R511%R72RH1%R:241r9%R:2RI1%R>3RI31&KrC%22S?1'1&Q7z%221R0%32R1QG%5221%52EQA%62QBQ:%8221&A%92Q=1%:2OSC&LrGrFrErD%5@T3T2T1T0SOSMSLSKSJSHSG4321C&G&D%116%311%R>2QAQ1%S93T<21%G2FQ<%61T0%811%S42T3<%RD221%S?3TBQ81&N&C%11T7rI%311rH%6442T91%S>2T=G%RN21F%SI3TL31&OrJ%;11%34;1T@:&JrK%22TE1&Q8&BrL%C11%3216rQ2%6221'Q2&Q3&@%11U<&MrQ1rQ0+Vn\@rOrN%66954321%;4:81U>p0=1p0E1p0I1p0N1p0Q91p0Q?1p0QA1p0QH1p0QO1p0R11p0R41p0R81p0R?1p0RC1p0RL1p0S61p0S>1p0SG1p0T01p0T91p0TD1p0TL1pSDV=1pS4V>1pS:V?1pT4V@1pS0U?1pSJUA1pSFUC1pS>UE1pHUG1pLUM1pS8V41p<V61pSBVI1").
Proof using All. intros mu0 IH fx R M model s sm cr w k d n.
intros A2 A8 A9 A10 A18 A19 A20 A21 A22 KP Hd Hk HkC Hw SO SZ Hn0 En CONS STEP FE MU. unfold PM.CHUNK in HkC.
pose proof SO as ((EK & DK & STK) & SV & _ & _ & _ & _ & _ & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & _).
assert (Hn : 0 <= n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
pose proof (PMSSRP.tsE_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w | 42%nat => k
| 43%nat => n | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 53%nat => d | _ => 0 end)) as PP.
cbn beta iota in PP. bvr.
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E12 & E19 & C0)
|[(MS & KS & E20 & C0 & C1) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & C0 & C1)]]).
-
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37990 R1 0x56ce0 M K Mh Ml MS).
assert (DK' : d < k).
{ destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
apply (call_resize fx1 R1 M model s sm cr (n + d) 227856); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS 2%nat) by PMK.inl. exact A2.
+ intros x Hx. rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ unfold PM.CHUNK. lia.
+ unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (after_shrink mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 w d); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
* rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
* rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
* rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
* rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. exact E19.
* rewrite (PMK.cs_of_preserved R1 R2 20%nat RP2) by PMK.inl. rewrite (KS 20%nat) by PMK.inl. exact A20.
* rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
* intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* unfold PMSSR1.acct. cbn [PMTK2.with_tb PM.p_src PM.p_tb]. split; [lia|]. split; [lia|]. split; [exact STEP|].
destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMSSR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
-
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37990 R1 0x37900 M K Mh Ml MS).
rewrite subw in C0 by lia.
assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
apply (IH fx1 R1 M model s sm cr (w - k) MU).
split; [|split; [exact SO| split; [|lia]]].
+ unfold PMSSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [exact E20|]. split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
intros x Hx. rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ unfold PMSSR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
-
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37990 R1 0x37a40 M K Mh Ml MS).
rewrite subw in C0 by lia.
assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
apply (finish fx1 R1 M model s sm cr 0); try assumption.
+ intros x Hx. rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ rewrite E10. f_equal. lia.
+ lia.
+ unfold PMSSR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.
End Call.
End WithHeap.
End PMSSR2.

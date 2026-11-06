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
PmTxtSpecs PmTxtKit PmTxtKit2 PmSSrdP PmSSrd1 PmSSrd2 PmSSrd3 PmSSrd4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSSrd5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsS.PMPSS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtSpecs.PMTXS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1nat"; "1option"; "1prod"; "2and"; "2eq"; "3lt"; "4Z"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "5Model"; "5m_vmmaps"; "6bvmap"]; ["0M"; "0M0"; "0R"; "0R0"; "7credit"; "7hi_heap"; "7hl_sptop"; "8stk"; "9SCFG"; ":ADDR_S"; ";iss_at"; ";mu_src"; ";p_src"; ";p_tb"; ";p_tg"; ";parser_at"]; [";parser_own"; ";pot_text"; ";pst"; ";strm"; ";tb_ok"; "<src_read_spec"; "=IHt"; "=lstate"; ">T3"; ">T4"; ">cfg"; ">credit_le"; ">model_ok"; "?str_resize_spec"; "@base_ok"; "Afill_buffer_tb_spec"]; ["Asrd_read_spec"; "BFPState"; "Bgetr"; "Csrealizes"; "Dloaded_segments"; "0S"; "0SCFG_P"; "Eadd"; "Ele"; "Elt"; "Emodulo"; "Emul"; "Eof_nat"; "Eopp"; "Epow"; "Esub"]; ["Eto_nat"; "0cr"; "0cr0"; "0fb"; "0fx"; "0k"; "0len"; "0model"; "0model0"; "0mu0"; "0n"; "0s"; "0s0"; "0sm"; "0sm0"; "FZ_to_bv"]; ["Fbv"; "0str"; "0w"; "0x"]]).
Module PMSSR5.
Import PMS.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Lemma subw : ltac2:(TCodec.tc2 tcn__PmSSrd5 "Q3'7'4&QHzr2%3221r1%5231%7231&QI&QN+2+R0%3221%52:1'5&QJ&QO&QGr3&QK+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pT<Q11pU8Q21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmSSrd5 "G'7'4&QI&QM&QN+2+R0%3221%511r1%8221z%:231%<231'5&QJr2%221:&QG%123<%63D31p081pU8F1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmSSrd5 "J'7'4&QI&QM&QN+2+R0%3221%511r1%8221&QHz%2241%=241&QJr2%221:+1%A221'5r3%23F1:p041p0:1pU8I1").
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
#[local] Abbreviation base_keep := (PMSSR1.base_keep L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation rpath := (PMSSR3.rpath L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation dpath := (PMSSR4.dpath L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT).
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.
Lemma head : ltac2:(TCodec.tc2 tcn__PmSSrd5 "R9'7&Q6vQFv;v8vCvAvR8v:v<vR2vQEvR3vR6vR<vRAvR>r1%A@@?>=<;:987654321'QA&?y5'R@yR0%211%5241'2y8%611%311p061'='Q2'Q3&D&Q7r7r6r5r4r3r2%7DQ7Q6Q5Q4Q3Q1Q0ONMLKJ654321I&QH&K&L%118%3218r;%6221'QC&QD&H%11QC&Q:r:r9+VnX0r8%5684321G%:4971QDp0<1p0D1pU6QO1pT4N1pTLQ01pTHQ21pT@Q41pQ2Q61pQ6Q<1pT:QC1pDQE1pTDR81").
Proof using All. intros mu0 IH fx R M model s sm cr w.
intros LS MU. pose proof LS as ((A2 & A8 & A9 & A18 & A20 & A21 & KP) & SO & AC & Hw).
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof MOK as (Mh & Ml & Mm).
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
destruct SRC as (F1 & _ & _ & _ & F5 & _ & F7 & _).
replace (fb + 40 + 24 + 240) with (fb + 64 + 240) in F1 by lia.
replace (fb + 40 + 24 + 272) with (fb + 64 + 272) in F5 by lia.
replace (fb + 40 + 24 + 288) with (fb + 64 + 288) in F7 by lia.
change PM.CHUNK with 16384 in F5, RM.
destruct (Z.eq_dec (PM.sr_rem (PM.p_src s)) 0) as [RZ|RNZ].
-
rewrite RZ in F7.
pose proof IA as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
cbn [pa_vp_iss AD PmLayoutS.ADDR_S] in I0.
destruct IOS as (_ & U32 & _).
pose proof (PMTK2.u8_of_u32 RSEGS M (fb + 440 + 120 + 32) (PM.sm_st sm) ltac:(lia) U32) as B152.
rewrite Z.mod_small in B152 by lia.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
pose proof (PMSSRP.tsH0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 38%nat => fb + 440 | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => PM.sm_st sm | _ => 0 end)) as PP.
cbn beta iota in PP. bvr.
pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E10 & E11 & E19 & C0 & C1) | [(MS & KS & E10 & E11 & E19 & C0 & C1)
| (MS & KS & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & C0)]]).
+
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37900 R1 0x37944 M K Mh Ml MS).
assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
apply (rpath mu0 IH fx1 R1 M model s sm cr w w); try assumption.
* unfold PMSSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [rewrite (KS 20%nat) by PMK.inl; exact A20|]. split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
kept_tac KS KP.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* right. exact ST0.
+
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37900 R1 0x379a0 M K Mh Ml MS).
assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
apply (dpath mu0 IH fx1 R1 M model s sm cr w); try assumption.
* unfold PMSSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [rewrite (KS 20%nat) by PMK.inl; exact A20|]. split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
kept_tac KS KP.
* lia.
+
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37900 R1 0x37a40 M K Mh Ml MS).
apply (PMSSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT
fx1 R1 M model s sm cr w); try assumption.
* kept_tac KS KP.
* lia.
-
cfeed PP (PMSSRP.tsH1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => w
| 37%nat => PM.sr_rem (PM.p_src s) | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E10 & E19 & C0) | (MS & KS & E10 & E19 & C0)]);
(assert (EM : M1 = M) by (apply functional_extensionality; exact FRw)); subst M1;
unfold PMSP.cfg; apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37900 R1 0x37944 M K Mh Ml MS).
+ apply (rpath mu0 IH fx1 R1 M model s sm cr w w); try assumption.
* unfold PMSSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [rewrite (KS 20%nat) by PMK.inl; exact A20|]. split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
kept_tac KS KP.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* left. lia.
+ apply (rpath mu0 IH fx1 R1 M model s sm cr w 16384); try assumption.
* unfold PMSSR1.lregs.
split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
split; [rewrite (KS 20%nat) by PMK.inl; exact A20|]. split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
kept_tac KS KP.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* left. lia.
Qed.
Lemma loop : ltac2:(TCodec.tc2 tcn__PmSSrd5 "R7'1'QA&?y5'R@yR0%211%5241'2y8%611%311p061'='Q2'Q3&D'7&6&R0&K&Lr4%211r3%5221%711r9%:221&Q7v;v8vCvAvR8v<vR2vQEvR3vR6vR<vRAvR>r8r7r6r5r2%CDBA@?>=<;:98765432JH1'QC&QD&HvQF%211&Q:r:+VnX0%3672N1>=v:%:49621p0<1p0Q11pU6Q=1pT4Q?1pTLQA1pTHQC1pT@QE1pQ2QG1pQ6QM1pT:R41pTFR61").
Proof using All. intros n.
induction n as [|n IHn]; intros fx R M model s sm cr w Hn LS; [lia|].
assert (IHm : IHt (PM.mu_src (PM.p_src s) sm)).
{ intros fx' R' M' model' s' sm' cr' w' Hlt LS'. apply (IHn fx' R' M' model' s' sm' cr' w'); [|exact LS'].
pose proof LS' as (_ & SO' & _). pose proof (unread_nn _ _ _ _ _ SO') as (UN' & _).
assert (0 <= PM.mu_src (PM.p_src s') sm') by (unfold PM.mu_src; destruct (Z.eqb _ _); lia). lia. }
exact (head _ IHm fx R M model s sm cr w LS ltac:(lia)).
Qed.
Lemma entry_ok : ltac2:(TCodec.tc2 tcn__PmSSrd5 "S='QA&Ev8&0'3'7%2211&Q0vR<%211v<%83521vR2vA&>vR8%211%@5?6541&Q<%114&G&Fv;%211vQE+fP0%643=21'5'R@yR0%211&QBvC&R?y5&QLu:%211%5241%8271&QGvR3+R0%3221%;2?1%B3?61u;%<11%?2>1%B2A1+[H%;2:1%C2G1%J3G41u<%D11%G2F1%J2I1vR6%J2N1%Q13N31&O&QD&I&Q8&Q9+Q8%K2J1+]H%M2L1%988765QI31QN&JvRAvR>%37<;:QM521&Q>%13>=QO&Q4&M%11R7&N%11R9%5231&Q;&Q1%13QO64%321R:'QC&HvQF%211&Q:r<+VnV4%36Q02QN1RAR?v:%94Q2621p0;1p0@1p0G1p0J1p0O1p0Q:1p0QB1p0QK1p0R?1p0RG1p0RJ1pT:S<1").
Proof using All. intros fx.
intros HH MOK STK A10 A11 A12 PA IA BASE TBOK CRL.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M0 S 22528 STK) as WR.
assert (BR : PMFR.brange L (PM.parser_own s0 ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_refl).
cfeed PP (PMSSRP.tsA_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
set (P := fun a => S - 64 <= a < S - 64 + 64).
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= S - 64 \/ S <= a) -> L5C.agree_on M0 M1 a m).
{ intros a m Ha Hm X i Hi. apply FRZ; lia. }
assert (AGH : forall B m, In (B, m) (PM.parser_own s0 ++ LBX) -> L5C.agree_on M0 M1 B m).
{ intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4). apply AG; lia. }
assert (EKn : PMK.ek L LBX S 22528 W0 M0 M1).
{ apply (PMK.ek_piece_in RSEGS L KL LBX S 22528 W0 M0 M1 P); [intros a Ha N; apply FRZ; [exact Ha| exact N]| exact STK| |].
- exact (PMFR.brange_hi L LBX (PMFR.brange_incl L LBX _ BR (fun x Hx => in_or_app _ _ _ (or_intror Hx)))).
- intros a Pa. left. unfold P in Pa. lia. }
assert (SPC : forall pc1, msteps RSEGS (@mkst fx R0 (Z_to_bv 64 0x378c4) M0 (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
(hi_heap HI (PM.parser_own s0 ++ LBX) cr0 M1 (m_vmmaps model0) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model0) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x378c4 M0 model0) K).
{ intros pc1 MS NEXT. unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s0 ++ LBX) cr0 M0 model0 fx fx1 R0 0x378c4 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
- intros a Ha N. apply FRZ; [exact Ha| exact N].
- intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.parser_own s0 ++ LBX) M0 S 22528 a STK). lia.
- intros a. unfold P. apply PMK.rng_dec.
- exact NEXT. }
assert (SO1 : forall (C1 : L5.u64_at RSEGS M1 (S - 64) (bv_unsigned (getr R0 (reg 22)))) (C2 : L5.u64_at RSEGS M1 (S - 56) (bv_unsigned (getr R0 (reg 21))))
(C3 : L5.u64_at RSEGS M1 (S - 48) (bv_unsigned (getr R0 (reg 20)))) (C4 : L5.u64_at RSEGS M1 (S - 40) (bv_unsigned (getr R0 (reg 19))))
(C5 : L5.u64_at RSEGS M1 (S - 32) (bv_unsigned (getr R0 (reg 18)))) (C6 : L5.u64_at RSEGS M1 (S - 24) (bv_unsigned (getr R0 (reg 9))))
(C7 : L5.u64_at RSEGS M1 (S - 16) (bv_unsigned (getr R0 (reg 8)))) (C8 : L5.u64_at RSEGS M1 (S - 8) (bv_unsigned (getr R0 (reg 1)))),
hi_heap HI (PM.parser_own s0 ++ LBX) cr0 M1 (m_vmmaps model0) -> state_ok M1 model0 s0 sm0 cr0).
{ intros C1 C2 C3 C4 C5 C6 C7 C8 HH1.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & _ & VEC & _).
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s0) (proj1 Hk)) as P2.
assert (INV : In (PM.p_b s0, 32 * 2 ^ PM.p_k s0) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (INC : In (PM.sr_qc (PM.p_src s0), PM.CHUNK) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BR _ _ INV) as (V0 & _ & V4). destruct (BR _ _ INC) as (Q0 & _ & Q4).
split; [split; [|split]|].
- exact EKn.
- apply PMK.dk_grows. exact MG.
- exact (PMK.stk_grows L M0 M1 S 22528 MG STK).
- split; [unfold PMSSR1.saves8; repeat split; assumption|].
split.
{ apply (PMF.parser_at_agree RSEGS AD M0 M1 (fb + 40) (fb + 440) s0); [lia|lia| apply AG; lia| lia| lia| exact (AGH _ _ INC)| lia| lia| exact (AGH _ _ INV)| |exact PA].
intros c n p E. assert (INT : In (p, c) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite E; cbn; right; right; left; reflexivity).
exact (AGH _ _ INT). }
split.
{ apply (PMF.iss_at_agree RSEGS AD M0 M1 (fb + 440) str sm0); [lia|lia| apply AG; lia| |exact IA].
intros c n p E. assert (INs : In (p, c) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
exact (AGH _ _ INs). }
split; [exact (base_keep M0 M1 EKn STK BASE)|].
split; [exact TBOK|]. split; [exact HH1|]. split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|].
split; [exact CRL| unfold PMSP.credit_keep; lia]. }
pose proof (unread_nn M0 model0 s0 sm0 cr0) as UNX.
destruct EX as [(MS & KS & E2 & E8 & E9 & E18 & E20 & E21 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) | (MS & KS & E10 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8)];
apply (SPC _ MS); intros HH1; pose proof (SO1 C1 C2 C3 C4 C5 C6 C7 C8 HH1) as SOk.
-
rewrite Z.sub_0_r, Z.mod_small in C0 by lia.
pose proof (unread_nn M1 model0 s0 sm0 cr0 SOk) as (UN & _).
apply (loop (Nat.succ (Z.to_nat (PM.mu_src (PM.p_src s0) sm0))) fx1 R1 M1 model0 s0 sm0 cr0 len); [apply Nat.lt_succ_diag_r|].
split; [|split; [exact SOk| split; [|lia]]].
+ unfold PMSSR1.lregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E20|]. split; [exact E21|].
intros x Hx. rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). reflexivity.
+ unfold PMSSR1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [lia|]. split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|].
unfold PMSSR1.fields_eq. repeat split; reflexivity.
-
rewrite Z.sub_0_r, Z.mod_small in C0 by lia. assert (L0 : len = 0) by lia.
apply (PMSSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UNS0 RSZ SRD FBT KONT
fx1 R1 M1 model0 s0 sm0 cr0 0); try assumption.
all: try (rewrite (KS 2%nat) by PMK.inl; exact Rsp0).
all: try (rewrite (KS _) by PMK.inl; symmetry; apply Z_to_bv_bv_unsigned).
+ intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); reflexivity.
+ rewrite E10; f_equal; lia.
+ lia.
+ unfold PMSSR1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [lia|].
split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|].
unfold PMSSR1.fields_eq. repeat split; reflexivity.
Qed.
End Call.
Theorem srd_read_ok : ltac2:(TCodec.tc2 tcn__PmSSrd5 "@&Q=vQFv;v8%43321&Q5%13543&Q?&QD&I%3592187&Q@%15;43:9p031p081p0;1").
Proof.
intros RSZ SRD FBT fx R M model K LBX cr sp r fb len s str sm HH MOK K0 EN FR A10 A11 A12 Hlen PA IA BASE TB INCS UN UNS CRL KONT.
unfold PMSP.entry in EN. destruct EN as (E1 & RA & E2 & E3 & E4 & STK).
unfold PMSP.frame_ok in FR. cbn [pa_frame AD PmLayoutS.ADDR_S] in FR. destruct FR as (FR1 & FR2 & FR3).
unfold PMSP.o_src, PMSP.o_tb, PMSP.o_p, PMSP.o_is in A10, A11, PA, IA. cbn [pa_off_p pa_off_is AD PmLayoutS.ADDR_S] in A10, A11, PA, IA.
change (PMSP.pm_scr 5) with 22528 in STK.
apply (entry_ok R M model K LBX cr sp r fb len s str sm E1 RA E2 E3 E4 K0 FR1 FR2 FR3 Hlen INCS UNS RSZ SRD FBT KONT fx HH MOK STK);
try assumption.
- replace (fb + 64) with (fb + 40 + 24) by lia. exact A10.
- replace (fb + 376) with (fb + 40 + 336) by lia. exact A11.
Qed.
End WithHeap.
End PMSSR5.

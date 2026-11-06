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
PmTxtSpecs PmTxtKit PmTxtKit2 PmSSrd1 PmSRdSpanP Js0_code_36ff0_36ff4 PmSRdSpan1 PmSReset.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSRdSpan2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdSpan1.PMSRS1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtKit2.PMTK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1list"; "1option"; "1prod"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"]; ["6credit"; "7SCFG"; "8p_src"; "8p_tb"; "8parser_own"; "8pst"; "8sr_rem"; "8srcst"; "8strm"; "8vs_own"; "8vs_size"; "8vstr"; "9bregs"; "9st_ok"; ":fields_eq"; ";cfg"]; [";src_step"; "<with_tb"; "=FPState"; "=getr"; ">srealizes"; "?loaded_segments"; "0S"; "0SCFG_P"; "@add"; "@le"; "@modulo"; "@of_nat"; "@pow"; "0a"; "0b"; "0c"]; ["0cr"; "0cr0"; "0fb"; "0fx"; "0len"; "0model"; "0model0"; "0s"; "0s0"; "0sa"; "0sb"; "0sc"; "0sm"; "0sm0"; "AZ_to_bv"; "Abv"]; ["0str"; "0tb1"; "0tg1"; "0z"]]).
Module PMSRS2.
Import PMS.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
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
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis FBS : PMPSS.fill_buffer_spec L HI.
Hypothesis SRDS : PMTXS.srd_read_spec RSEGS AD L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (PMSP.o_tb AD fb + 1 <= ptr /\ ptr + n <= PMSP.o_tb AD fb + 24)) ->
L5.defined M' ptr n ->
PM.parser_at RSEGS AD T3 T4 M' (PMSP.o_p AD fb) (PMSP.o_is AD fb) s' -> PM.iss_at RSEGS AD T3 M' (PMSP.o_is AD fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSP.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5C.hpres L LBX S (PMSP.pm_scr 6) (PMSP.W_srcf AD fb ++ [(PMSP.o_tb AD fb, 24)]) M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_text L (PM.p_tb s0) (PM.p_tg s0)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
model_but_vm model0 model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
#[local] Abbreviation W0 := (PMSRS1.W0 fb).
#[local] Abbreviation saves4 := (PMSRS1.saves4 R0 S).
#[local] Abbreviation kept_rs := (PMSRS1.kept_rs R0).
#[local] Abbreviation memrel := (PMSRS1.memrel L M0 LBX S fb).
#[local] Abbreviation fields_eq := (PMSSR1.fields_eq s0).
#[local] Abbreviation st_ok := (PMSRS1.st_ok L HI R0 M0 model0 LBX cr0 S fb s0 str).
#[local] Abbreviation bregs := (PMSRS1.bregs R0 S fb len).
#[local] Abbreviation finish_rs := (PMSRS1.finish_rs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation call_fill := (PMSRS1.call_fill L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PMSRS1.call_srd L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation base_keep := (PMSRS1.base_keep L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation unread_nn := (PMSRS1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation src_callee_mem := (PMSRS1.src_callee_mem L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat.
Lemma zbv_mod : ltac2:(TCodec.tc2 tcn__PmSRdSpan2 "A'5'4'QOyR0%211&QNr1%2241&Q:&Q<+2+R0%3221%5271%92;1%>3;81pT8@1").
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma src_step_trans : ltac2:(TCodec.tc2 tcn__PmSRdSpan2 "B'G'H&Q0r6r5r3r2%544321r8%741654p031p041pSH;1pSF<1pSD=1pS0?1pRN@1pRLA1").
Proof. intros a b c sa sb sc.
unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Lemma fast : ltac2:(TCodec.tc2 tcn__PmSRdSpan2 "RM'Q2&;y5'QOyR0%211%5241'1y8%611%311p061':'E'H&@&Lv?vQ6vQBvQDr6%6554321'4&Q3r7&QN&Q;u;%211%42L1%7261&F&Br4%211%411%;2Q11%?3Q171'3&Q9+1%221Fr5%;11%=11%62J1%8251&Mv8v6v=vQFv9vQAvQHvR0r8%:@98Q97654Q8Q7321Q1Q5?H&N%125Q3&Q0%M17%N16vQM%44321Q8'Q4&Q5&AvQ7%211&Or=r<+VkiDr;r:%66:54321v7%=4<921p0?1p0E1p0H1p0Q41p0Q>1p0QO1pS2R71pSJR91pS@R;1pS<R=1pJR?1pNRE1pS8RL1").
Proof using All. intros fx R M model s sm cr.
intros (A2 & A8 & A9 & A18 & KP) A11 Hl SO FE STEP.
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & _ & VEC & _).
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
set (qc := PM.sr_qc (PM.p_src s)) in *. set (de := PM.sr_de (PM.p_src s)) in *. set (rem := PM.sr_rem (PM.p_src s)) in *.
replace (fb + 40 + 24 + 280) with (fb + 64 + 280) in F6 by lia. replace (fb + 40 + 24 + 256) with (fb + 64 + 256) in F3 by lia.
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
assert (QIN : In (qc, PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BR qc PM.CHUNK QIN) as (Q0 & _ & Q4).
unfold PM.CHUNK in *.
destruct (PMTK.u64_of_defined RSEGS M (fb + 64 + 256) ltac:(lia) ltac:(destruct STOP; lia) F3) as (pos & Hpos & POS).
cfeed PP (PMSRPP.rpF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 36%nat => rem
| 37%nat => de | 38%nat => pos | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & E10 & E11 & E12 & E13).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x36f34 R1 0x36f48 M K Mh Ml MS1).
rewrite zbv_mod in E12.
pose proof (Z.mod_pos_bound (len + pos) (2 ^ 64) ltac:(lia)) as HP49.
pose proof SV as (S8 & S16 & S24 & S32). bvr.
pose proof (PMSRPP.rpG_conc fx1 R1 M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 37%nat => de
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => -1 * len + rem | 49%nat => (len + pos) mod 2 ^ 64 | 50%nat => len + de | _ => 0 end)) as PP.
cbn beta iota in PP.
assert (WF : L5.writable RSEGS M (fb + 64 + 256) 40).
{ apply (L5C.writable_of_defined RSEGS M _ 40); [| lia| destruct STOP; lia].
pose proof PA as (_ & PD & _). apply (L5.defined_sub M (fb + 40) 384 (fb + 64 + 256) 40 PD); lia. }
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & E1 & E2 & E8 & E9 & E11' & E18 & C0 & C1 & C2).
set (P := fun a => (fb + 64 + 256 <= a < fb + 64 + 256 + 8) \/ (fb + 64 + 280 <= a < fb + 64 + 280 + 16)).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx1 fx2 R1 0x36f48 R2 0x36ff0 M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2).
{ intros a Ha N. apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M S 24576 a STK). lia. }
{ intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH2.
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= fb + 320 \/ fb + 328 <= a) -> (a + m <= fb + 344 \/ fb + 360 <= a) -> L5C.agree_on M M2 a m).
{ intros a m Ha Hm X Y i Hi. apply FRZ2; lia. }
assert (AGH : forall B m, In (B, m) (PM.parser_own s ++ LBX) -> L5C.agree_on M M2 B m).
{ intros B m Hin. destruct (BR B m Hin) as (Z0 & _ & Z4). apply AG; lia. }
set (s' := PMPS.with_src s (PM.SRC qc (len + de) (-1 * len + rem))).
assert (QC : PM.sr_qc (PM.p_src s') = PM.sr_qc (PM.p_src s)) by reflexivity.
assert (EKn : PMK.ek L LBX S 24576 W0 M M2).
{ apply (PMK.ek_piece L LBX S 24576 W0 M M2 P); [intros a Ha N; apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]|].
intros a Ha CA NE OW Pa. apply (OW (PMSP.o_src AD fb + 256, 40)); [unfold PMSRS1.W0, PMSP.W_srcf; left; reflexivity|].
unfold L5.in_rng, PMSP.o_src, PMSP.o_p, P in *; cbn [fst snd pa_off_p AD PmLayoutS.ADDR_S]. lia. }
assert (SO2 : st_ok M2 model s' sm cr).
{ split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 24576 W0 M0 M M2 EK EKn).
- apply (PMK.dk_trans L LBX S 24576 M0 M M2 DK). apply PMK.dk_grows. exact MG2.
- exact (PMK.stk_grows L M M2 S 24576 MG2 STK).
- split; [unfold PMSRS1.saves4; repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| eassumption])|].
split.
{ pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (INV : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
destruct (BR _ _ INV) as (V0 & _ & V4).
apply (PMPK.parser_src_upd RSEGS AD M M2 (fb + 40) (fb + 440) s (len + de) (-1 * len + rem) PA); [lia|lia| | | | | | | | | | | | | | |].
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG2.
- apply PMPK.dkr_grows. exact MG2.
- lia.
- lia.
- exact (AGH _ _ INV).
- intros c n p E. apply PMPK.dkr_grows. exact MG2.
- apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| replace (fb + 40 + 288) with (fb + 40 + 24 + 264) by lia; exact F4].
- apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia; exact F5].
- replace (fb + 40 + 304) with (fb + 64 + 280) by lia. exact C1.
- replace (fb + 40 + 312) with (fb + 64 + 288) by lia. exact C0.
- change (PM.sr_qc (PM.p_src s)) with qc. lia.
- lia.
- unfold PM.CHUNK. change (PM.sr_qc (PM.p_src s)) with qc. lia. }
split.
{ apply (PMF.iss_at_agree RSEGS AD M M2 (fb + 440) str sm); [lia|lia| apply AG; lia| |exact IA].
intros c n p E. assert (INs : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
exact (AGH _ _ INs). }
split; [exact (base_keep M M2 EKn STK BASE)|].
split; [exact TBOK|]. split; [unfold s'; rewrite (PMSSR1.own_with_src s (PM.SRC qc (len + de) (-1 * len + rem)) eq_refl); exact HH2|]. split; [exact MOK|]. split; [exact MB|].
split; [exact CRL| exact CRK]. }
apply (finish_rs fx2 R2 M2 model s' sm cr de len); try assumption.
- intros x Hx. rewrite (KS2 x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- rewrite (KS2 10%nat) by PMK.inl. exact E10.
- lia.
- lia.
- right. left. exists qc, 16384. split; [unfold s', PM.parser_own, PM.src_own; left; reflexivity| lia].
- intros i Hi. apply MG2. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
- unfold PMSP.src_step in *. cbn [PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem] in *. unfold s'.
apply (src_step_trans _ _ _ _ _ _ STEP). unfold PMSP.src_step, PM.unread. cbn [PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem].
split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| unfold rem; lia].
Qed.
Lemma own_with_tb : ltac2:(TCodec.tc2 tcn__PmSRdSpan2 "K'E'K'5'4'0'2%1244%311&Ir2%211&Cr3%211%611%<3851&D&Q1r4%2317:%411%513%C3?21p081pT6F1pT4H1pS@J1").
Proof using All. intros s tb1 tg1. intros E. unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.
Lemma at_srd : ltac2:(TCodec.tc2 tcn__PmSRdSpan2 "SE'Q2&;y5'QOyR0%211%5241'1y8%611%311p061':'E'H&@'4&Q3r6&QN&Q;u1%211%42E1%7261+Vkm@%72F1%;3F31&Lv?vQ6vQBvQDr7%6554321r8u:%A11%C2Q41%F241&Q8+R0%22;1%H2Q71%L3Q751r9u;%K11%M2Q>1%Q0241+[H%;2D1%Q12Q@1%Q53Q@41r:u<%Q411%Q62QG1%Q9241%Q82QGK%Q<3QG21&Mv8v6v=vQFv9vQAvQHvR0%9@87Q96543Q8Q721@IQ3Q5QD&N%124K&Q0&B%117%21FvQM%54321Q1'5&J&Cr;%211%411z%R63721'Q4&Q5&AvQ7%211&Or@r?+VnV4r>r=%66:54321v7%=4<921p0?1p0H1p0O1p0Q21p0Q=1p0QE1p0QO1p0R:1p0RB1pS2RO1pSJS11pS@S31pS<S51pJS71pNS=1pS8SD1").
Proof using All. intros fx R M model s sm cr.
intros A1 (A2 & A8 & A9 & A18 & KP) A10 A11 A12 SO FE STEP SZ0.
pose proof (unread_nn M model s sm cr SO) as (UN & ST & RM & GE).
assert (UNs : PM.unread (PM.p_src s) sm < 2 ^ 26) by (destruct STEP as (_ & _ & _ & _ & U); lia).
apply (call_srd fx R M model s sm cr 225200 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO UNs ltac:(lia)).
intros fx2 R2 M2 model2 s2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 G1 G2 G3 G4 G5 G6 STEP2 SO2.
pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & MOK2 & MB2 & CRL2 & CRK2).
pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK2 as (Mh & Ml & Mm).
pose proof (L5C.stk_writable RSEGS _ M2 S 24576 STK2) as WR.
pose proof (unread_nn M2 model2 s2 sm2 cr2 SO2) as (UN2 & _).
assert (Hd2 : d < 2 ^ 26) by (unfold PMSP.consumed in CONS2; lia).
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (fb + 40 + 336) with (fb + 376) in VS by lia.
assert (FE2 : fields_eq s2).
{ destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMSSR1.fields_eq. repeat split; congruence. }
assert (STEP02 : PMSP.src_step (PM.p_src s0) (PM.p_src s2) sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
pose proof SV2 as (S8 & S16 & S24 & S32). bvr.
revert VS SZ2. destruct (PM.p_tb s2) as [n1|c1 n1 q1] eqn:ETB; intros (VD & _ & VS) SZ2; cbn [PM.vs_size] in SZ2.
-
destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
pose proof (PMSRPP.rpES_conc fx2 R2 M2 (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 39%nat => 2 * n1
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) as PP.
cbn beta iota in PP.
assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 32)) by (rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl; exact A2).
assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl; exact A8).
assert (B9 : getr R2 (reg 9) = Z_to_bv 64 (fb + 376)) by (rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl; exact A9).
assert (B18 : getr R2 (reg 18) = Z_to_bv 64 (fb + 64)) by (rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl; exact A18).
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx3 & R3 & M3 & MG3 & FRw & _ & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
assert (EM : M3 = M2) by (apply functional_extensionality; exact FRw). subst M3.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x36fb0 R3 0x36ff0 M2 K Mh Ml MS3).
apply (finish_rs fx3 R3 M2 model2 s2 sm2 cr2 (fb + 376 + 1) n1); try assumption.
+ intros x Hx. rewrite (KS3 x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (PMK.cs_of_preserved R R2 x RP2) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ rewrite <- (Z_to_bv_bv_unsigned _ (getr R3 (reg 11))), E11. f_equal. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
+ lia.
+ lia.
+ right. right. lia.
+ apply (L5.defined_sub M2 (fb + 376) 24 (fb + 376 + 1) n1 VD); lia.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
pose proof (PMF.u8_of_u64 RSEGS M2 (fb + 376) (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
assert (BR : PMFR.brange L (PM.parser_own s2 ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M2 _ HH2); apply incl_refl).
assert (IN : In (q1, c1) (PM.parser_own s2 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (BR q1 c1 IN) as (Q0 & _ & Q4).
pose proof (PMSRPP.rpEL_conc fx2 R2 M2 (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 39%nat => (c1 + 1) mod 256
| 40%nat => n1 | 41%nat => q1 | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) as PP.
cbn beta iota in PP.
assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 32)) by (rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl; exact A2).
assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl; exact A8).
assert (B9 : getr R2 (reg 9) = Z_to_bv 64 (fb + 376)) by (rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl; exact A9).
assert (B18 : getr R2 (reg 18) = Z_to_bv 64 (fb + 64)) by (rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl; exact A18).
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx3 & R3 & M3 & MG3 & FRw & _ & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
assert (EM : M3 = M2) by (apply functional_extensionality; exact FRw). subst M3.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x36fb0 R3 0x36ff0 M2 K Mh Ml MS3).
apply (finish_rs fx3 R3 M2 model2 s2 sm2 cr2 q1 n1); try assumption.
+ intros x Hx. rewrite (KS3 x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (PMK.cs_of_preserved R R2 x RP2) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ lia.
+ lia.
+ right. left. exists q1, c1. split; [unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| lia].
+ apply (L5.defined_sub M2 q1 c1 q1 n1 DQ); lia.
Qed.
Lemma slow : ltac2:(TCodec.tc2 tcn__PmSRdSpan2 "R:'Q2&;y5'QOyR0%211%5241'1y8%611%311p061':'E'H&@&Lv?vQ6vQBvQDr6%6554321&Q9+1%2215&Mv8v6v=vQFv9vQAvQHvR0r7r5r4r3%=@<;F:987ED654B321&N%128D&Q0&B%11;%21:vQM%54321J'Q4&Q5&AvQ7%211&Or<r;+Vkl0r:r9%66:54321v7%=4<921p0?1p0F1p0I1p0Q81p0Q<1pS2QD1pSJQF1pS@QH1pS<QJ1pJQL1pNR21pS8R91").
Proof using All. intros fx R M model s sm cr.
intros BR0 Hl SO FE STEP. pose proof BR0 as (A2 & A8 & A9 & A18 & KP).
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & VS & VEC & _).
destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _).
replace (fb + 40 + 336) with (fb + 376) in VS by lia.
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (INV : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
destruct (BR _ _ INV) as (V0 & _ & V4).
assert (INC : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BR _ _ INC) as (C0' & _ & C4').
pose proof (PMPK.heap_nodup L HI HIok _ _ _ _ HH) as NDL.
revert VS. destruct (PM.p_tb s) as [n0|c0 n0 q0] eqn:ETB; intros (VD & _ & VS).
-
destruct VS as (Hn0 & B0). pose proof (PMF.even_byte n0) as EV.
assert (W2 : L5.writable RSEGS M (fb + 376) 2) by (apply (L5C.writable_of_defined RSEGS M _ 2); [apply (L5.defined_sub M (fb + 376) 24 _ 2 VD); lia| lia| destruct STOP; lia]).
cfeed PP (PMSRPP.rpSS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 39%nat => 2 * n0 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & (C0 & C1)).
set (P := fun a => fb + 376 + 0 <= a < fb + 376 + 0 + 2).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x36f80 R1 0x378c4 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M S 24576 a STK). lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= fb + 376 \/ fb + 378 <= a) -> L5C.agree_on M M1 a m).
{ intros a m Ha Hm X i Hi. apply FRZ1; [lia| unfold P; lia]. }
assert (AGH : forall B m, In (B, m) (PM.parser_own s ++ LBX) -> L5C.agree_on M M1 B m).
{ intros B m Hin. destruct (BR B m Hin) as (Z0 & _ & Z4). apply AG; lia. }
set (s1 := PMTK2.with_tb s (PM.VShort 0) (PM.p_tg s)).
assert (OW1 : PM.vs_own (PM.VShort 0) = PM.vs_own (PM.p_tb s)) by (rewrite ETB; reflexivity).
assert (EKn : PMK.ek L LBX S 24576 W0 M M1).
{ apply (PMK.ek_piece L LBX S 24576 W0 M M1 P); [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
intros a Ha CA NE OW Pa. apply (OW (PMSP.o_tb AD fb, 24)); [unfold PMSRS1.W0; apply in_or_app; right; left; reflexivity|].
unfold L5.in_rng, PMSP.o_tb, PMSP.o_p, P in *; cbn [fst snd pa_off_p AD PmLayoutS.ADDR_S]. lia. }
assert (SO1 : st_ok M1 model s1 sm cr).
{ split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 24576 W0 M0 M M1 EK EKn).
- apply (PMK.dk_trans L LBX S 24576 M0 M M1 DK). apply PMK.dk_grows. exact MG1.
- exact (PMK.stk_grows L M M1 S 24576 MG1 STK).
- split; [destruct SV as (S8 & S16 & S24 & S32); unfold PMSRS1.saves4; repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption])|].
split.
{ apply (PMTK2.parser_tb_set RSEGS AD M M1 (fb + 40) (fb + 440) s (PM.VShort 0) (PM.p_tg s) PA); [lia|lia| apply AG; lia| apply AG; lia| | lia| lia| exact (AGH _ _ INV)| |].
- apply PMPK.dkr_grows. exact MG1.
- replace (fb + 40 + 336) with (fb + 376) by lia. split; [intros i Hi; apply MG1; apply VD; exact Hi|]. split; [exact I|]. split; [lia|].
replace (2 * 0) with 0 by lia. exact C0.
- intros i Hi. apply MG1. apply PD. exact Hi. }
split.
{ apply (PMF.iss_at_agree RSEGS AD M M1 (fb + 440) str sm); [lia|lia| apply AG; lia| |exact IA].
intros c n p E. assert (INs : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
exact (AGH _ _ INs). }
split; [exact (base_keep M M1 EKn STK BASE)|].
split; [unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]; try rewrite ETB in TBOK; unfold PM.tb_ok in *; cbn [PM.vs_cap] in *; exact TBOK|].
split; [unfold s1; rewrite (own_with_tb s _ _ OW1); exact HH1|]. split; [exact MOK|]. split; [exact MB|].
unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]. try rewrite ETB in CRL; try rewrite ETB in CRK; unfold PM.pot_text in *. cbn [PM.vs_cap] in *. split; [exact CRL| exact CRK]. }
apply (at_srd fx1 R1 M1 model s1 sm cr); try assumption.
+ unfold PMSRS1.bregs.
split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
kept_tac KS1 KP.
+ reflexivity.
-
destruct VS as (W0' & W8 & W16 & Hn0 & Hc0 & Hce & DQ & _).
pose proof (PMF.u8_of_u64 RSEGS M (fb + 376) (c0 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c0 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c0 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)); lia).
assert (TIN : In (q0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (BR q0 c0 TIN) as (T0 & T1 & T4).
assert (Wq : L5.writable RSEGS M q0 1) by (apply (L5C.writable_of_defined RSEGS M _ 1); [apply (L5.defined_sub M q0 c0 _ 1 DQ); lia| lia| lia]).
assert (W8' : L5.writable RSEGS M (fb + 376 + 8) 8) by (apply (L5C.writable_of_defined RSEGS M _ 8); [apply (L5.defined_sub M (fb + 376) 24 _ 8 VD); lia| lia| destruct STOP; lia]).
cfeed PP (PMSRPP.rpSL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len | 39%nat => (c0 + 1) mod 256
| 41%nat => q0 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & C0 & C1).
set (P := fun a => (q0 + 0 <= a < q0 + 0 + 1) \/ (fb + 376 + 8 <= a < fb + 376 + 8 + 8)).
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x36f80 R1 0x378c4 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
{ intros a Pa. unfold P in Pa. destruct Pa as [X|X].
- apply (PMK.cwr_block L (PM.parser_own s ++ LBX) q0 c0 a TIN). lia.
- apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M S 24576 a STK). lia. }
{ intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= q0 \/ q0 + 1 <= a) -> (a + m <= fb + 384 \/ fb + 392 <= a) -> L5C.agree_on M M1 a m).
{ intros a m Ha Hm X Y i Hi. apply FRZ1; lia. }
assert (OTH : forall B m, In (B, m) (PM.parser_own s ++ LBX) -> B <> q0 -> L5C.agree_on M M1 B m).
{ intros B m Hin NEB. destruct (BR B m Hin) as (Z0 & _ & Z4).
destruct (PMPK.blocks_apart_heap L HI HIok _ cr M _ B m q0 c0 HH Hin TIN NEB) as [AP|AP]; apply AG; lia. }
set (s1 := PMTK2.with_tb s (PM.VLong c0 0 q0) (PM.p_tg s)).
assert (OW1 : PM.vs_own (PM.VLong c0 0 q0) = PM.vs_own (PM.p_tb s)) by (rewrite ETB; reflexivity).
assert (EKn : PMK.ek L LBX S 24576 W0 M M1).
{ apply (PMK.ek_piece L LBX S 24576 W0 M M1 P); [intros a Ha N; apply FRZ1; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]|].
intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|X].
- apply (PMSRS.own_not_client L HI HIok (PM.parser_own s) LBX cr M _ q0 c0 a S 24576 HH); [unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| lia| exact CA].
- apply (OW (PMSP.o_tb AD fb, 24)); [unfold PMSRS1.W0; apply in_or_app; right; left; reflexivity|].
unfold L5.in_rng, PMSP.o_tb, PMSP.o_p; cbn [fst snd pa_off_p AD PmLayoutS.ADDR_S]. lia. }
assert (NEV : PM.p_b s <> q0).
{ intros E. apply (PMPK.fst_neq_app ([(PM.sr_qc (PM.p_src s), PM.CHUNK)] ++ PM.vec_own (PM.p_b s) (PM.p_k s)) (PM.vs_own (PM.p_tb s) ++ LBX) (PM.p_b s) (32 * 2 ^ PM.p_k s) q0 c0).
- rewrite <- app_assoc. exact NDL.
- right. left. reflexivity.
- rewrite ETB. left. reflexivity.
- exact E. }
assert (NEQ : PM.sr_qc (PM.p_src s) <> q0).
{ intros E. apply (PMPK.fst_neq_app [(PM.sr_qc (PM.p_src s), PM.CHUNK)] (PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s) ++ LBX) (PM.sr_qc (PM.p_src s)) PM.CHUNK q0 c0).
- exact NDL.
- left. reflexivity.
- rewrite ETB. right. left. reflexivity.
- exact E. }
assert (SO1 : st_ok M1 model s1 sm cr).
{ split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 24576 W0 M0 M M1 EK EKn).
- apply (PMK.dk_trans L LBX S 24576 M0 M M1 DK). apply PMK.dk_grows. exact MG1.
- exact (PMK.stk_grows L M M1 S 24576 MG1 STK).
- split; [destruct SV as (S8 & S16 & S24 & S32); unfold PMSRS1.saves4; repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption])|].
split.
{ apply (PMTK2.parser_tb_set RSEGS AD M M1 (fb + 40) (fb + 440) s (PM.VLong c0 0 q0) (PM.p_tg s) PA); [lia|lia| apply AG; lia| apply AG; lia| | lia| lia| exact (OTH _ _ INV NEV)| |].
- apply PMPK.dkr_grows. exact MG1.
- replace (fb + 40 + 336) with (fb + 376) by lia. split; [intros i Hi; apply MG1; apply VD; exact Hi|]. split; [exact I|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W0']|].
split; [replace (fb + 376 + 8) with (fb + 376 + 8) by lia; exact C0|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W16]|].
split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG1; apply DQ; exact Hi| exact I].
- intros i Hi. apply MG1. apply PD. exact Hi. }
split.
{ apply (PMF.iss_at_agree RSEGS AD M M1 (fb + 440) str sm); [lia|lia| apply AG; lia| |exact IA].
intros c n p E. assert (INs : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
apply (OTH _ _ INs). intros Ep. subst p.
apply (PMPK.fst_neq_app (PM.parser_own s) LBX q0 c0 q0 c); [exact NDL| unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| apply INCS; rewrite E; left; reflexivity| reflexivity]. }
split; [exact (base_keep M M1 EKn STK BASE)|].
split; [unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]; try rewrite ETB in TBOK; unfold PM.tb_ok in *; cbn [PM.vs_cap] in *; exact TBOK|].
split; [unfold s1; rewrite (own_with_tb s _ _ OW1); exact HH1|]. split; [exact MOK|]. split; [exact MB|].
unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]. try rewrite ETB in CRL; try rewrite ETB in CRK; unfold PM.pot_text in *. cbn [PM.vs_cap] in *. split; [exact CRL| exact CRK]. }
apply (at_srd fx1 R1 M1 model s1 sm cr); try assumption.
+ unfold PMSRS1.bregs.
split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
kept_tac KS1 KP.
+ reflexivity.
Qed.
End Call.
End WithHeap.
End PMSRS2.

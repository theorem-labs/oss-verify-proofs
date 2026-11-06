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
PmTxtSpecs PmTxtKit PmTxtKit2 PmSSrd1 PmSReset PmURdSpanP Ju0_code_37da4_37da8 PmURdSpan1 PmURdSpan2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmURdSpan3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSSrd1.PMSSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtSpecs.PMTXS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmURdSpan1.PMURS1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1option"; "1prod"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "4m_vmmaps"; "5bvmap"; "0M"; "0M0"; "0R"]; ["0R0"; "6credit"; "6hi_heap"; "6hl_sptop"; "7stk"; "8SCFG"; "9ADDR_U"; ":CHUNK"; ":iss_at"; ":p_src"; ":p_tb"; ":p_tg"; ":parser_at"; ":parser_own"; ":pot_text"; ":pst"]; [":sm_g"; ":sr_rem"; ":strm"; ":tb_ok"; ";fill_buffer_spec"; "<fields_eq"; "=T3"; "=T4"; "=cfg"; "=credit_le"; "=model_ok"; "=src_step"; ">read_span_spec"; "?base_ok"; "@srd_read_spec"; "Abregs"]; ["Ast_ok"; "BFPState"; "Bgetr"; "Csrealizes"; "Dloaded_segments"; "0S"; "0SCFG_P"; "Eadd"; "Ele"; "Eof_nat"; "0c"; "0cr"; "0cr0"; "0fb"; "0fx"; "0len"]; ["0model"; "0model0"; "0s"; "0s0"; "0sm"; "0sm0"; "0sm1"; "FZ_to_bv"; "Fbv"; "0str"]]).
Module PMURS3.
Import PMU.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
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
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis FBS : PMPSU.fill_buffer_spec L HI.
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
#[local] Abbreviation W0 := (PMURS1.W0 fb).
#[local] Abbreviation saves4 := (PMURS1.saves4 R0 S).
#[local] Abbreviation kept_rs := (PMURS1.kept_rs R0).
#[local] Abbreviation memrel := (PMURS1.memrel L M0 LBX S fb).
#[local] Abbreviation fields_eq := (PMSSR1.fields_eq s0).
#[local] Abbreviation st_ok := (PMURS1.st_ok L HI R0 M0 model0 LBX cr0 S fb s0 str).
#[local] Abbreviation bregs := (PMURS1.bregs R0 S fb len).
#[local] Abbreviation finish_rs := (PMURS1.finish_rs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation call_fill := (PMURS1.call_fill L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PMURS1.call_srd L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation base_keep := (PMURS1.base_keep L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation unread_nn := (PMURS1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation src_callee_mem := (PMURS1.src_callee_mem L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation fast := (PMURS2.fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation slow := (PMURS2.slow L HI LY HIok R0 M0 model0 K LBX cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FR1 FR2 FR3 Hlen INCS UN0 FBS SRDS KONT).
Lemma after_fill : ltac2:(TCodec.tc2 tcn__PmURdSpan3 "SC'QA&<y5'R8yR0%211%5241'1y8%611%311p061':'O'Q2&A'5&Q?v@vQEvQMvQOr8%6554321'4&QBr9&R7&QIu:%211%42M1%7261r2%72N1%;3N31'3&QHzr3%3221&G%5231%7231+1%821H&Q@v8v6v>vR1v9vQLvR3vR9r;r:r7r6%=@<;Q9:987Q8Q76543Q121&Q5%1285&Q;&I%11;%21:vR5%54321;r<%611%8411?>&Q1r=%:11%311%QC3QK1Q5&Q0%119&QG%317%221H%QI3R141'QC&QD&EvQF%211&Q8rCrB+VoY4rAr@%66:54321v7%=4<921p0?1p0F1p0L1p0Q01p0Q71p0Q:1p0QI1p0QL1p0R51p0RB1pSFRJ1pSHRL1pT>RN1pT:RO1pT6S11pT2S31pLS51pQ0S;1pSNSB1").
Proof using All. intros fx R M model s sm sm1 cr c.
intros BR0 A10 Hc Hl SO FE STEP STEP1 RZ G1. pose proof BR0 as (A2 & A8 & A9 & A18 & KP).
pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
assert (BR : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & _ & VEC & _).
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & Q1 & Q2 & Q3 & Q4 & DC & _ & _).
replace (fb + 40 + 24 + 264) with (fb + 64 + 264) in F4 by lia.
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (INV : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
destruct (BR _ _ INV) as (V0 & _ & V4).
assert (INC : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BR _ _ INC) as (C0' & _ & C4').
assert (W16 : L5.writable RSEGS M (fb + 64 + 280) 16) by (apply (L5C.writable_of_defined RSEGS M _ 16); [apply (L5.defined_sub M (fb + 40) 384 _ 16 PD); lia| lia| destruct STOP; lia]).
unfold PM.CHUNK in Hc.
cfeed PP (PMURPP.urpB_conc fx R M (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len
| 42%nat => PM.sr_qc (PM.p_src s) | 43%nat => c | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & EX).
assert (CC : L5.u64_at RSEGS M1 (fb + 64 + 288) c /\ L5.u64_at RSEGS M1 (fb + 64 + 280) (PM.sr_qc (PM.p_src s))).
{ destruct EX as [(_ & _ & _ & _ & _ & C1 & C2) | (_ & _ & _ & _ & _ & C1 & C2)]; split; assumption. }
destruct CC as (C1 & C2).
set (P := fun a => fb + 64 + 280 <= a < fb + 64 + 280 + 16).
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= fb + 344 \/ fb + 360 <= a) -> L5C.agree_on M M1 a m).
{ intros a m Ha Hm X i Hi. apply FRZ1; [lia| unfold P; lia]. }
assert (AGH : forall B m, In (B, m) (PM.parser_own s ++ LBX) -> L5C.agree_on M M1 B m).
{ intros B m Hin. destruct (BR B m Hin) as (Z0 & _ & Z4). apply AG; lia. }
set (s2 := PMPS.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) (PM.sr_qc (PM.p_src s)) c)).
assert (EKn : PMK.ek L LBX S 24576 W0 M M1).
{ apply (PMK.ek_piece L LBX S 24576 W0 M M1 P); [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
intros a Ha CA NE OW Pa. apply (OW (PMSP.o_src AD fb + 256, 40)); [unfold PMURS1.W0, PMSP.W_srcf; left; reflexivity|].
unfold L5.in_rng, PMSP.o_src, PMSP.o_p, P in *; cbn [fst snd pa_off_p AD PmLayoutU.ADDR_U]. lia. }
assert (SO2f : hi_heap HI (PM.parser_own s ++ LBX) cr M1 (m_vmmaps model) -> st_ok M1 model s2 sm1 cr).
{ intros HH1. split; [split; [|split]|].
- exact (PMK.ek_trans L LBX S 24576 W0 M0 M M1 EK EKn).
- apply (PMK.dk_trans L LBX S 24576 M0 M M1 DK). apply PMK.dk_grows. exact MG1.
- exact (PMK.stk_grows L M M1 S 24576 MG1 STK).
- split; [destruct SV as (S8 & S16 & S24 & S32); unfold PMURS1.saves4; repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption])|].
split.
{ apply (PMPK.parser_src_upd RSEGS AD M M1 (fb + 40) (fb + 440) s (PM.sr_qc (PM.p_src s)) c PA); [lia|lia| | | | | | | | | | | | | | |].
- apply AG; lia.
- apply AG; lia.
- apply PMPK.dkr_grows. exact MG1.
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- exact (AGH _ _ INV).
- intros c' n' p' E. apply PMPK.dkr_grows. exact MG1.
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| replace (fb + 40 + 288) with (fb + 64 + 264) by lia; exact F4].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| replace (fb + 40 + 296) with (fb + 40 + 24 + 272) by lia; exact F5].
- replace (fb + 40 + 304) with (fb + 64 + 280) by lia. exact C2.
- replace (fb + 40 + 312) with (fb + 64 + 288) by lia. exact C1.
- lia.
- lia.
- unfold PM.CHUNK. lia. }
split.
{ apply (PMF.iss_at_agree RSEGS AD M M1 (fb + 440) str sm1); [lia|lia| apply AG; lia| |exact IA].
intros c' n' p' E. assert (INs : In (p', c') (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
exact (AGH _ _ INs). }
split; [exact (base_keep M M1 EKn STK BASE)|].
split; [exact TBOK|]. split; [unfold s2; rewrite (PMSSR1.own_with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) (PM.sr_qc (PM.p_src s)) c) eq_refl); exact HH1|].
split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK]. }
assert (STEP2 : PMSP.src_step (PM.p_src s0) (PM.p_src s2) sm0 sm1).
{ apply (PMURS2.src_step_trans _ _ _ _ _ _ STEP). destruct STEP1 as (_ & E2 & L2 & S2 & U2).
unfold PMSP.src_step, PM.unread in *. cbn [s2 PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem].
split; [reflexivity|]. split; [exact E2|]. split; [lia|]. split; [exact S2| rewrite RZ in *; lia]. }
assert (SPC : forall pc1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x37d24) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
(st_ok M1 model s2 sm1 cr -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x37d24 M model) K).
{ intros pc1 MS NEXT. unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x37d24 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG1).
- intros a Ha N. apply FRZ1; [exact Ha| exact N].
- intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M S 24576 a STK). lia.
- intros a. unfold P. apply PMK.rng_dec.
- intros HH1. apply NEXT. exact (SO2f HH1). }
destruct EX as [(MS1 & KS1 & E10 & E11 & C0 & _ & _) | (MS1 & KS1 & E10 & E11 & C0 & _ & _)]; apply (SPC _ MS1); intros SO2.
-
apply (slow fx1 R1 M1 model s2 sm1 cr); try assumption.
unfold PMURS1.bregs.
split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
kept_tac KS1 KP.
-
apply (fast fx1 R1 M1 model s2 sm1 cr); try assumption.
+ unfold PMURS1.bregs.
split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
kept_tac KS1 KP.
+ cbn [s2 PMPS.with_src PM.p_src PM.sr_rem]. lia.
Qed.
#[local] Abbreviation after_fillA := (after_fill).
Lemma entry_rs : ltac2:(TCodec.tc2 tcn__PmURdSpan3 "S='QA&Bv6&0'2'5%2211&MvR3%211v9%83521vQLv>&;vR1%211%@5?6541&Q:%114&D&Cv8%211vQE+hP0%643=21'4'R8yR0%211&QBv@&R7y5&QIu:%211%5241%8271&QGvQM+R0%3221%;2?1%B3?61u;%<11%?2>1%B2A1vQO%B2F1%I3F31u<%C11%F2E1%I2H1+[H%B2A1%J2N1%Q13N41&L&QD&F&Q6&Q7+Q8%K2J1+]H%M2L1%988765QI31QN&HvR9vR5%37<;:QM521&Q=%13>=QO&Q3&J%11R7&K%11R9%5231&Q9&N%13QO64%321R:'QC&EvQF%211&Q8r<+VoU@%36Q02QN1RAR?v7%94Q2621p0;1p0@1p0G1p0J1p0O1p0Q:1p0QC1p0QK1p0R?1p0RG1p0RJ1pSNS<1").
Proof using All. intros fx.
intros HH MOK STK A10 A11 A12 PA IA BASE TBOK CRL.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M0 S 24576 STK) as WR.
assert (BR : PMFR.brange L (PM.parser_own s0 ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_refl).
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & _ & VEC & _).
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & Q1 & Q2 & Q3 & Q4 & DC & _ & _).
replace (fb + 40 + 24 + 288) with (fb + 64 + 288) in F7 by lia. replace (fb + 40 + 24 + 272) with (fb + 64 + 272) in F5 by lia.
replace (fb + 40 + 24 + 264) with (fb + 64 + 264) in F4 by lia.
change PM.CHUNK with 16384 in F5, Q3.
assert (RM : PM.sr_rem (PM.p_src s0) <= 16384) by lia.
cfeed PP (PMURPP.urpA_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len
| 36%nat => PM.sr_rem (PM.p_src s0) | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
set (P := fun a => S - 32 <= a < S - 32 + 32).
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= S - 32 \/ S <= a) -> L5C.agree_on M0 M1 a m).
{ intros a m Ha Hm X i Hi. apply FRZ; lia. }
assert (AGH : forall B m, In (B, m) (PM.parser_own s0 ++ LBX) -> L5C.agree_on M0 M1 B m).
{ intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4'). apply AG; lia. }
assert (EKn : PMK.ek L LBX S 24576 W0 M0 M1).
{ apply (PMK.ek_piece_in RSEGS L KL LBX S 24576 W0 M0 M1 P); [intros a Ha N; apply FRZ; [exact Ha| exact N]| exact STK| |].
- exact (PMFR.brange_hi L LBX (PMFR.brange_incl L LBX _ BR (fun x Hx => in_or_app _ _ _ (or_intror Hx)))).
- intros a Pa. left. unfold P in Pa. lia. }
assert (SPC : forall pc1, msteps RSEGS (@mkst fx R0 (Z_to_bv 64 0x37cb0) M0 (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
(hi_heap HI (PM.parser_own s0 ++ LBX) cr0 M1 (m_vmmaps model0) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model0) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x37cb0 M0 model0) K).
{ intros pc1 MS NEXT. unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s0 ++ LBX) cr0 M0 model0 fx fx1 R0 0x37cb0 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
- intros a Ha N. apply FRZ; [exact Ha| exact N].
- intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.parser_own s0 ++ LBX) M0 S 24576 a STK). lia.
- intros a. unfold P. apply PMK.rng_dec.
- exact NEXT. }
assert (SO1 : forall (C1 : L5.u64_at RSEGS M1 (S - 32) (bv_unsigned (getr R0 (reg 18)))) (C2 : L5.u64_at RSEGS M1 (S - 24) (bv_unsigned (getr R0 (reg 9))))
(C3 : L5.u64_at RSEGS M1 (S - 16) (bv_unsigned (getr R0 (reg 8)))) (C4 : L5.u64_at RSEGS M1 (S - 8) (bv_unsigned (getr R0 (reg 1)))),
hi_heap HI (PM.parser_own s0 ++ LBX) cr0 M1 (m_vmmaps model0) -> st_ok M1 model0 s0 sm0 cr0).
{ intros C1 C2 C3 C4 HH1.
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s0) (proj1 Hk)) as P2.
assert (INV : In (PM.p_b s0, 32 * 2 ^ PM.p_k s0) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (INC : In (PM.sr_qc (PM.p_src s0), PM.CHUNK) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BR _ _ INV) as (V0 & _ & V4). destruct (BR _ _ INC) as (Z0 & _ & Z4).
split; [split; [|split]|].
- exact EKn.
- apply PMK.dk_grows. exact MG.
- exact (PMK.stk_grows L M0 M1 S 24576 MG STK).
- split; [unfold PMURS1.saves4; repeat split; assumption|].
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
assert (FE0 : fields_eq s0) by (unfold PMSSR1.fields_eq; repeat split; reflexivity).
assert (STEP0 : PMSP.src_step (PM.p_src s0) (PM.p_src s0) sm0 sm0) by (unfold PMSP.src_step; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]).
destruct EX as [(MS & KS & E10 & E11 & C0 & C1 & C2 & C3 & C4) | [(MS & KS & E2 & E8 & E9 & E11 & E18 & C0 & C0' & C0'' & C1 & C2 & C3 & C4)
| [(MS & KS & E2 & E8 & E9 & E11 & E18 & C0 & C0' & C0'' & C1 & C2 & C3 & C4) | (MS & KS & E2 & E8 & E9 & E11 & E18 & C0 & C0' & C1 & C2 & C3 & C4)]]];
apply (SPC _ MS); intros HH1; pose proof (SO1 C1 C2 C3 C4 HH1) as SOk.
-
rewrite Z.sub_0_r, Z.mod_small in C0 by lia. assert (L0 : len = 0) by lia.
apply (finish_rs fx1 R1 M1 model0 s0 sm0 cr0 0 0); try assumption.
all: try (rewrite (KS 2%nat) by PMK.inl; exact Rsp0).
all: try (rewrite (KS _) by PMK.inl; symmetry; apply Z_to_bv_bv_unsigned).
+ intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); reflexivity.
+ lia.
+ lia.
+ left. split; reflexivity.
+ intros i Hi. lia.
-
rewrite Z.sub_0_r, Z.mod_small in C0', C0'' by lia.
apply (fast fx1 R1 M1 model0 s0 sm0 cr0); try assumption.
+ unfold PMURS1.bregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|].
intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); reflexivity.
+ lia.
-
rewrite Z.sub_0_r, Z.mod_small in C0', C0'' by lia.
apply (slow fx1 R1 M1 model0 s0 sm0 cr0); try assumption.
+ unfold PMURS1.bregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|].
intros x Hx; rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity); reflexivity.
-
rewrite Z.sub_0_r, Z.mod_small in C0, C0' by lia. assert (RZ : PM.sr_rem (PM.p_src s0) = 0) by lia.
pose proof SOk as ((EK1 & DK1 & STK1) & SV1 & PA1 & IA1 & BASE1 & TBOK1 & HH1' & MOK1 & MB1 & CRL1 & CRK1).
pose proof (L5C.stk_writable RSEGS _ M1 S 24576 STK1) as WR1.
assert (F5' : L5.u64_at RSEGS M1 (fb + 64 + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M0 M1); [apply AG; lia| lia| lia| exact F5]).
assert (F4' : L5.u64_at RSEGS M1 (fb + 64 + 264) (PM.sr_qc (PM.p_src s0))) by (apply (L5C.u64_at_agree RSEGS M0 M1); [apply AG; lia| lia| lia| exact F4]).
assert (Hq : 0 <= PM.sr_qc (PM.p_src s0) < 2 ^ 64).
{ assert (INC : In (PM.sr_qc (PM.p_src s0), PM.CHUNK) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
destruct (BR _ _ INC) as (Z0 & _ & Z4). unfold PM.CHUNK in Z4. destruct STOP. lia. }
cfeed PP (PMURPP.urpR0_conc fx1 R1 M1 (fun j => match j with 2%nat => S | 33%nat => fb + 64 | 34%nat => fb + 376 | 35%nat => len
| 42%nat => PM.sr_qc (PM.p_src s0) | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx2 & R2 & M2 & MG2 & FRw & _ & [(MS2 & KS2 & E12 & D0) | (MS2 & KS2 & E1 & E10 & E11' & E12 & D0)]);
(assert (EM : M2 = M1) by (apply functional_extensionality; exact FRw)); subst M2;
unfold PMSP.cfg; apply (PMK.spiece_ro RSEGS model0 fx1 fx2 R1 0x37d10 R2 _ M1 K Mh Ml MS2).
+
apply (slow fx2 R2 M1 model0 s0 sm0 cr0); try assumption.
* unfold PMURS1.bregs.
split; [rewrite (KS2 2%nat) by PMK.inl; exact E2|]. split; [rewrite (KS2 8%nat) by PMK.inl; exact E8|].
split; [rewrite (KS2 9%nat) by PMK.inl; exact E9|]. split; [rewrite (KS2 18%nat) by PMK.inl; exact E18|].
intros x Hx. rewrite (KS2 x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). reflexivity.
+
assert (BRG : bregs R2).
{ unfold PMURS1.bregs.
split; [rewrite (KS2 2%nat) by PMK.inl; exact E2|]. split; [rewrite (KS2 8%nat) by PMK.inl; exact E8|].
split; [rewrite (KS2 9%nat) by PMK.inl; exact E9|]. split; [rewrite (KS2 18%nat) by PMK.inl; exact E18|].
intros x Hx. rewrite (KS2 x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity).
rewrite (KS x) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). reflexivity. }
pose proof BRG as (B2 & B8 & B9 & B18 & BKP).
apply (call_fill fx2 R2 M1 model0 s0 sm0 cr0 228644 E1 ltac:(split; [lia| reflexivity]) B2 BKP E10 E11' E12 SOk).
intros fx3 R3 M3 sm3 c RP3 Y10 Hc G3 ST0 ST2 STEP3 SO3.
apply (after_fill fx3 R3 M3 model0 s0 sm0 sm3 cr0 c); try assumption.
* unfold PMURS1.bregs.
split; [rewrite (PMK.cs_of_preserved R2 R3 2%nat RP3) by PMK.inl; exact B2|].
split; [rewrite (PMK.cs_of_preserved R2 R3 8%nat RP3) by PMK.inl; exact B8|].
split; [rewrite (PMK.cs_of_preserved R2 R3 9%nat RP3) by PMK.inl; exact B9|].
split; [rewrite (PMK.cs_of_preserved R2 R3 18%nat RP3) by PMK.inl; exact B18|].
intros x Hx. rewrite (PMK.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply PMSSR1.sub_in; vm_compute; reflexivity). apply BKP. exact Hx.
Qed.
End Call.
Theorem read_span_ok : ltac2:(TCodec.tc2 tcn__PmURdSpan3 "=&Q4vQFv8v6%43321&Q>&QD&F%3572165&Q<%13987p031p081").
Proof.
intros FBS SRDS. unfold PMU.read_span_spec, PMSP.read_span_spec. cbn [pa_read_span AD PmLayoutU.ADDR_U].
intros fx R M model K LBX cr sp r fb len s str sm HH MOK K0 EN FR A10 A11 A12 Hlen PA IA BASE TB INCS UN CRL KONT.
unfold PMSP.entry in EN. destruct EN as (E1 & RA & E2 & E3 & E4 & STK).
unfold PMSP.frame_ok in FR. cbn [pa_frame AD PmLayoutU.ADDR_U] in FR. destruct FR as (FR1 & FR2 & FR3).
unfold PMSP.o_src, PMSP.o_tb, PMSP.o_p, PMSP.o_is in A10, A12, PA, IA. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in A10, A12, PA, IA.
change (PMSP.pm_scr 6) with 24576 in STK.
apply (entry_rs R M model K LBX cr sp r fb len s str sm E1 RA E2 E3 E4 K0 FR1 FR2 FR3 Hlen INCS UN FBS SRDS KONT fx HH MOK STK);
try assumption.
- replace (fb + 64) with (fb + 40 + 24) by lia. exact A10.
- replace (fb + 376) with (fb + 40 + 336) by lia. exact A12.
Qed.
End WithHeap.
End PMURS3.

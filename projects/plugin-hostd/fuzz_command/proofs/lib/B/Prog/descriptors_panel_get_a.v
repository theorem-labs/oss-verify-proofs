(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's ASan+UBSan walk from the call of arg_s (0x8cd20) to the call of rec_shape_of (0x8cd30) (plugin-hostd/fuzz_command.asan-ubsan), in the form of lib/A/Prog/descriptors_panel_get_s5.v (a working branch 2db68b2223b; a call through cl_callS and the callee's contract, then a run from a fresh seed to the next segment's statement), with B's function arg_s where A inlined it. *)

(* 0x8cd20 .. 0x8cd30: arg_s copies uri into a fresh block and records it in the slot (c->nargs := 1, c->args[0]);
   then a0 := "panel_get" (0x21fc0, the listing's object atom 88), a1 := 9 and the call of rec_shape_of, where
   `dpgb_R_stmt` (descriptors_panel_get_aux.v) takes over. No branch, no inline check. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c rec_shape_of_c hand_back_c mix_call_c answer_c descriptors_panel_get_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRo CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import descriptors_panel_get_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the verb "panel_get" (0x21fc0) is the listing's object 88 (CmdAddr.v's cmd_objs) *)
Lemma dpgb_atom88 : A_OBJ 88 = 329%nat.
Proof. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
(* a Theorem Labs lane's CmdRecRest.v `cmd_sig_prog_PB`, stated for the abstract instance *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
Hypothesis MTL : ameter_laws MT.
(* a Theorem Labs lane's CmdRecImg.v `cmd_img_facts_tfib`, stated for the abstract instance's segments *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> cmd_img_facts SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : cmd_img_facts SEGS B := cmd_img_facts_tfib B HB.
(* a Theorem Labs lane's record facts over any segments (lib/B/Prog/CmdRecRo.v, CmdRecRest.v), at this walk's *)
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) := CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let RUN := paj_run B LAWS.

Lemma dpgb_A_of_R : dpgb_R_stmt B MT -> dpgb_A_stmt B MT.
Proof.
intros HR ly S W regs mem md ch pu x R O CTX lyc Sc Wc regs1 memc mdc O1 BLK HJ MLE HBB HREPc
  Hsp1 R3 R4 R1 R8 R9 R10 R11 Rhi HFR HBLKS HSTRS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & Hfrm & HROD & HRO & H10 & Hpu & HBLK0 & HSTR0 & HLEN & HAPO & HREP & Hfr8 & Hev & Hlive & MOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (proj1 HJ) as HAR.
pose proof HREP as (Q & HQ & HQO).
pose proof HQ as (_ & _ & _ & (HL16 & _) & _).
destruct (dpgb_slot_ok R HL16) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hc3' : (rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL)
  by (destruct Hc3 as [[H _] | H]; [left | right]; exact H).
clear Hc3.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (dpgb_rec_repA_in B ly S (rdW W mem) R O HREP).
assert (HSTK1 : ARG_S_STK + 32 <= DESCRIPTORS_PANEL_GET_STK) by (unfold DESCRIPTORS_PANEL_GET_STK; lia).
assert (HSTKp : 0 <= ARG_S_STK) by (unfold ARG_S_STK, XMALLOC_STK, ESTACK, ASTACK; lia).
(* the meter, the event and live budgets arg_s asks *)
assert (HXMs : 0 <= XM_ARG_S MT (Some x))
  by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HXMa : 0 <= XM_ANSWER MT (snd (descriptors_panel_get_m R (Some x)))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (snd (descriptors_panel_get_m R (Some x)))) + 1))
    ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HLIVEa : 0 <= LIVE_ANSWER (snd (descriptors_panel_get_m R (Some x))))
  by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs1 & Hnev1 & _).
assert (HEVa : st_nev Sc + EV_ARG_S <= EV_MAX)
  by (unfold EV_DESCRIPTORS_PANEL_GET, EV_ANSWER, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC in *; lia).
assert (HLVa : blocks_bytes Sc + LIVE_ARG_S (Some x) <= LIVE_MAX)
  by (unfold LIVE_DESCRIPTORS_PANEL_GET in Hlive; lia).
assert (HMOKa : mo_ok MT Sc (XM_ARG_S MT (Some x))).
{ apply (mok_station MT S Sc (XM_DESCRIPTORS_PANEL_GET MT R (Some x)) (XM_RECORD MT R) (XM_ARG_S MT (Some x))
    MTL MOK MLE HXMs).
  unfold XM_DESCRIPTORS_PANEL_GET. lia. }
(* arg_s's premises: the return address, the read-only bytes, the stack words above its sp, the string *)
assert (Hraw1 : YK0s.ret_ok (getr regs1 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold DPGB_RET_ARG, AF_descriptors_panel_get; lia | reflexivity]).
assert (Hraw4 : 4096 <= bv_unsigned (getr regs1 1))
  by (rewrite R1, unsigned_lit_small by (unfold DPGB_RET_ARG, AF_descriptors_panel_get; lia);
      unfold DPGB_RET_ARG, AF_descriptors_panel_get; lia).
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (dpgb_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] lyc Sc Wc memc mdc _ HAR0 HOin HJ HROD).
pose proof (cmd_ro_ok_of_aro lyc Sc Wc memc mdc HAR HROD1) as HRO1.
pose proof HBLKS as (qb & kb & Hqb & Hqb1 & Hqb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ qb kb HAR Hqb) as (_ & Hqb4096 & Hqbc & _ & _ & _ & Hkb).
pose proof (dpgb_req_ge kb ltac:(lia)) as [_ Rkb].
assert (HARG : astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] pu (Some x)).
{ unfold astr_argA. split; [lia|]. split; [exact HSTRS|]. split; [exact HLEN|].
  left. split; [exact HBLKS | constructor]. }
assert (HTAIL : forall x0, Some x = Some x0 -> atail_vis SEGS Wc memc (pu + Z.of_nat (length x0))).
{ intros x0 Hx0. injection Hx0 as <-.
  exact (dpgb_tail_vis B lyc Sc Wc memc mdc pu (Z.of_nat (length x) + 1) (pu + Z.of_nat (length x)) HAR HBLKS
    ltac:(lia)). }
(* the call of arg_s(c, uri) *)
rewrite (dpgb_sig_arg cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc regs1 memc _ DESCRIPTORS_PANEL_GET_STK (spZ regs) (dpgb_FP O) ly S W mem md [] lyc Sc mdc
    (EV_RECORD R) ARG_S_STK
    [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
     (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
      rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
    EV_ARG_S (-32) (getr regs1 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       blocks_bytes S2 <= blocks_bytes Sc + LIVE_ARG_S (Some x) /\ mo_le MT Sc S2 (XM_ARG_S MT (Some x)) /\
       exists p, 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length x) + 1) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) ((p, Z.of_nat (length x) + 1) :: O1))
    HJ).
  - rewrite Hsp1. unfold DPGB_FRAME. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - exact Hraw1.
  - exact Hraw4.
  - apply achain_low. unfold s0Z. rewrite R8, unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply SRr_mono.
    + exact (TARG_S fx lyc Sc Wc regs1 memc mdc [] (rec_slot R) pu REC_DESCRIPTORS_PANEL_GET [] (Some x) R O1
        HPRE1 HROD1 HRO1 R10 R11 eq_refl HREPc (or_introl HARG) HTAIL HEVa HLVa HMOKa).
    + cbv beta. unfold apost_base. intros Wx cx _ (lyx & Sx & regsx & memx & mdx & -> & HJ1 & HP & HK3).
      exists lyx, Sx, regsx, memx, mdx. split; [reflexivity|]. split; [exact HJ1|]. split; [exact HP|].
      destruct HK3 as (Hbbx & Hmlex & [(Hl6 & _) | (_ & px & Hpx)]);
        [unfold REC_ARGS_MAX in Hl6; cbn in Hl6; discriminate Hl6|].
      cbv zeta in Hpx. destruct Hpx as (Hpx4 & HPermx & Hapx & HREPx).
      split; [exact Hbbx|]. split; [exact Hmlex|]. exists px. split; [exact Hpx4|]. split; [exact HPermx|].
      split; [exact Hapx | exact HREPx].
  - (* arg_s writes the slot's nargs and args[0], words of g_rec or record.spill *)
    intros a Ha. apply (dpgb_awr_slot B HB cmd_prog_img).
    destruct Ha as (r & Hr & Ha).
    apply (dpgb_slot_PG (rec_slot R)); [exact Hc1 | exact Hc2 | exact Hc3' |].
    destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha; lia.
  - (* none of them is in this call's stack window *)
    intros ly5 S5 W5 regs5 mem5 md5 _ a Ha Hw _. exfalso.
    destruct Ha as (r & Hr & Ha).
    destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Ha;
      unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJx & HP2 &
  (HBBx & MLEx & p & Hp4096 & HPerm2 & Hap2 & HREP2)).
pose proof (proj1 HJx) as HAR2.
(* back at 0x8cd24: the registers arg_s keeps, the frame *)
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regs1 rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (X2 : getr regs2 2 = getr regs1 2) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X3 : getr regs2 3 = getr regs1 3) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X4 : getr regs2 4 = getr regs1 4) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X9 : getr regs2 9 = getr regs1 9) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (Hsp2 : spZ regs2 = spZ regs - 32)
  by (unfold spZ at 1; rewrite X2; unfold DPGB_FRAME in Hsp1; exact Hsp1).
pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & GX1 & GX2 & GX3 & _).
assert (HFR2 : forall j r, nth_error dpgb_saved j = Some r ->
  aval_mem (rdW W2 mem2) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj3 : (j < 3)%nat) by (apply (proj1 (nth_error_Some dpgb_saved j)); rewrite Hj; discriminate).
  apply (dpgb_aval_mem_kept (rdW Wc memc)); [exact (HFR j r Hj)|].
  intros kk Hkk. apply GX1; [lia | lia |].
  intros (r' & Hr' & Ha'). destruct Hr' as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Ha';
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia. }
(* 0x8cd24 .. 0x8cd30: a0 := "panel_get", a1 := 9, then rec_shape_of *)
destruct (dpgb_reg_seed W2 regs2 mem2 DPGB_RET_ARG (SLit 0)) as [HS SHOK].
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (EE2 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew (Eimg (Ereg regs2 [])) nn = getr regs2 rr).
{ intros nn rr Hnn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
set (E2 := Eimg (Ereg regs2 [])) in *.
rewrite R1.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ apply awr_ok_nil. }
rewrite ?wvb_collapse in HJ2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdX := mdx) in *; clearbody mdX end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; exfalso; exact Hin)) as UN2.
pmkst HS.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KR2 : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs2 r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W2) Ex SSX MSX r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EE2; lia)
| st_ok _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KR2 : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs2 r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W2) Ex SSX MSX r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EE2; lia)
end.
prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsX := rg) in *; set (memX := mm) in * end.
assert (HKT2 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 memX a = rdW W2 mem2 a)
  by (intros a Ha; exact (UN2 a Ha (fun z => z))).
(* the state at the call of rec_shape_of, as dpgb_R_stmt takes it *)
assert (MLE2 : mo_le MT S S2 (XM_RECORD MT R + XM_ARG_S MT (Some x)))
  by exact (mle_station MT S Sc S2 _ _ MTL MLE MLEx).
assert (HBB2 : blocks_bytes S2 <= blocks_bytes S + LIVE_ARG_S (Some x)) by lia.
assert (HREPX : rec_repA B ly2 S2 (rdW W2 memX) (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) ((p, Z.of_nat (length x) + 1) :: O1))
  by exact (dpgb_rep_low B ly2 S2 W2 mem2 md2 (rdW W2 memX) _ _ HAR2 HREP2 (fun a Ha => HKT2 a ltac:(lia))).
assert (KX2 : getr regsX 2 = getr regs2 2) by (apply KR2; vm_compute; reflexivity).
assert (KX3 : getr regsX 3 = getr regs2 3) by (apply KR2; vm_compute; reflexivity).
assert (KX4 : getr regsX 4 = getr regs2 4) by (apply KR2; vm_compute; reflexivity).
assert (KX9 : getr regsX 9 = getr regs2 9) by (apply KR2; vm_compute; reflexivity).
assert (HspX : spZ regsX = spZ regs - DPGB_FRAME) by (unfold spZ at 1; rewrite KX2; unfold DPGB_FRAME; exact Hsp2).
assert (R3X : getr regsX 3 = w64 (as_gp B)) by (rewrite KX3, X3; exact R3).
assert (R4X : getr regsX 4 = w64 (as_tp B)) by (rewrite KX4, X4; exact R4).
assert (R9X : getr regsX 9 = w64 (rec_slot R)) by (rewrite KX9, X9; exact R9).
assert (R1X : getr regsX 1 = Z_to_bv 64 (BASE + DPGB_RET_R))
  by (rewrite T1; unfold DPGB_RET_R, AF_descriptors_panel_get; reflexivity).
assert (T10' : getr regsX 10 = w64 0x21fc0).
{ rewrite T10, <- (Z_to_bv_bv_unsigned 64 (ew E2 329)), (HEI2 329%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  change 329%nat with (A_OBJ 88). rewrite (dpgb_obj88 VOBJS). reflexivity. }
assert (T11' : getr regsX 11 = w64 9) by (rewrite T11; reflexivity).
assert (RhiX : forall r, 18 <= r <= 27 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (Rhi r Hr), <- (HP2 r ltac:(unfold acallee_saved; lia)).
  assert (Hrr : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hrr as [-> | Hrr]; [apply KR2; vm_compute; reflexivity|]).
  subst r. apply KR2. vm_compute. reflexivity. }
assert (HFRX : forall j r, nth_error dpgb_saved j = Some r ->
  aval_mem (rdW W2 memX) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj3 : (j < 3)%nat) by (apply (proj1 (nth_error_Some dpgb_saved j)); rewrite Hj; discriminate).
  apply (dpgb_aval_mem_kept (rdW W2 mem2)); [exact (HFR2 j r Hj)|].
  intros kk Hkk. apply HKT2. lia. }
exact (HR ly S W regs mem md ch pu x R O CTX lyc Sc O1 ly2 S2 W2 regsX memX mdX p BLK HJ2 MLE2 HBB2 HPerm2 Hap2
  Hp4096 HREPX HspX R3X R4X R1X R9X T10' T11' RhiX HFRX).
Qed.

End e.
End f.
End d.

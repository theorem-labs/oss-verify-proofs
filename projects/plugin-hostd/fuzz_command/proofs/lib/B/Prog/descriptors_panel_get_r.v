(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's ASan+UBSan walk from the call of rec_shape_of (0x8cd30) to its end (plugin-hostd/fuzz_command.asan-ubsan), re-made at B's addresses from lib/A/Prog/descriptors_panel_get_s8.v (a working branch 2db68b2223b): rec_shape_of composed with its contract (cl_callS_na), the epilogue run from a fresh seed, and the tail jump into answer at the entry's stack pointer (PaFx.v's callS_wideF: answer's post is FP-existential, apost_baseF). *)

(* 0x8cd30 .. 0x8cd50: rec_shape_of finds the reply shape of the verb "panel_get" (0x21fc0, 9 bytes); at 0x8cd34
   a1 := the shape, a0 := the slot c (s1), a2 := 0, the epilogue loads ra, s0, s1 from the frame and adds 32 to sp,
   and `j answer` runs answer at the entry's stack pointer with the entry's return address. The segment has no
   branch and no inline check. answer's post is the contract's post through dpgb_post_of. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRo CmdRecRest PaFx RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import descriptors_panel_get_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
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

Lemma dpgb_R_holds : dpgb_R_stmt B MT.
Proof.
intros ly S W regs mem md ch pu x R O CTX lyc Sc O1 ly2 S2 W2 regs2 mem2 md2 p
  BLK HJ2 MLE2 HBB2 HPerm2 Hap2 Hp4096 HREP2 Hsp2 R3 R4 R1 R9 R10 R11 Rhi HFR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & Hfrm & HROD & HRO & H10 & Hpu & HBLK0 & HSTR0 & HLEN & HAPO & HREP & Hfr8 & Hev & Hlive & MOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof BLK as (Bsub & Bgone & BO1 & BO1g & Bperm).
pose proof HREP as (Q & HQ & HQO).
pose proof HQ as (_ & _ & _ & (HL16 & _) & _).
destruct (dpgb_slot_ok R HL16) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hc64 : 0 <= rec_slot R < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (dpgb_rec_repA_in B ly S (rdW W mem) R O HREP).
pose proof (proj1 HJ2) as HAR2.
assert (HSTK1 : REC_SHAPE_OF_STK + 32 <= DESCRIPTORS_PANEL_GET_STK /\ ANSWER_STK <= DESCRIPTORS_PANEL_GET_STK)
  by (unfold DESCRIPTORS_PANEL_GET_STK; lia).
assert (HSTKp : 0 <= REC_SHAPE_OF_STK /\ 0 <= ANSWER_STK) by (unfold REC_SHAPE_OF_STK, ANSWER_STK, ESTACK; lia).
(* the model's step: rec_stub of the call (24, [x]) with the shape of "panel_get" and changes = 0 *)
pose proof (dpgb_model R x) as HM.
(* ---------- the call of rec_shape_of("panel_get", 9) ---------- *)
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2))
  by exact (dpgb_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] ly2 S2 W2 mem2 md2 _ HAR0 HOin HJ2 HROD).
pose proof (cmd_ro_ok_of_aro ly2 S2 W2 mem2 md2 HAR2 HROD2) as HRO2.
pose proof (dpgb_verb_pre B HB CMD_RO_IN ly2 S2 (rdW W2 mem2) HRO2) as HVERB.
assert (HEV2 : st_nev S2 + EV_REC_SHAPE_OF <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  unfold EV_DESCRIPTORS_PANEL_GET, EV_REC_SHAPE_OF, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (R11' : getr regs2 11 = w64 (Z.of_nat (length dpgb_verb))) by (rewrite dpgb_verb_len; exact R11).
assert (HSP2 : spZ regs2 = spZ regs + -32) by (rewrite Hsp2; unfold DPGB_FRAME; lia).
rewrite (dpgb_sig_rso cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 regs2 mem2 _ DESCRIPTORS_PANEL_GET_STK (spZ regs) (dpgb_FP O) ly S W mem md [] ly2 S2 md2
    (EV_RECORD R + EV_ARG_S) REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (getr regs2 1) (dpgb_Krso B ly2 S2)
    HJ2 HSP2).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold DPGB_RET_R, AF_descriptors_panel_get; lia | reflexivity].
  - rewrite R1, unsigned_lit_small by (unfold DPGB_RET_R, AF_descriptors_panel_get; lia).
    unfold DPGB_RET_R, AF_descriptors_panel_get. lia.
  - intros HPRE1. eapply SRr_mono.
    + exact (TREC_SHAPE_OF fx ly2 S2 W2 regs2 mem2 md2 0x21fc0 dpgb_verb HPRE1 HROD2 R10 ltac:(lia) R11'
        ltac:(rewrite dpgb_verb_len; lia) HRO2 VOBJS HVERB HEV2).
    + cbv beta. intros Wx cx _ (lyx & Sx & regsx & memx & mdx & -> & HJx & HPx & HKx).
      exists lyx, Sx, regsx, memx, mdx. split; [reflexivity|]. split; [exact HJx|]. split; [exact HPx | exact HKx].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as ((q & Hq10 & Hq64 & HqA) & _ & Ely3 & ES3). subst ly3 S3.
rewrite R1.
(* ---------- back at 0x8cd34: the registers rec_shape_of keeps, the frame ---------- *)
assert (CS3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs3 rr = getr regs2 rr)
  by (intros rr Hr; pose proof (HP3 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (X2 : getr regs3 2 = getr regs2 2) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X3 : getr regs3 3 = getr regs2 3) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X4 : getr regs3 4 = getr regs2 4) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X9 : getr regs3 9 = getr regs2 9) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (Hsp3 : spZ regs3 = spZ regs - 32) by (unfold spZ in *; rewrite X2; unfold DPGB_FRAME in Hsp2; exact Hsp2).
assert (HspR3 : 2 ^ 46 <= spZ regs3 <= 2 ^ 47 - 32) by (rewrite Hsp3; lia).
assert (Hsp16 : spZ regs3 mod 16 = 0).
{ rewrite Hsp3. replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & GX1 & GX2 & GX3 & _).
assert (HFR3 : forall j r, nth_error dpgb_saved j = Some r ->
  aval_mem (rdW W3 mem3) (spZ regs3 + 24 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj3 : (j < 3)%nat) by (apply (proj1 (nth_error_Some dpgb_saved j)); rewrite Hj; discriminate).
  rewrite Hsp3. apply (dpgb_aval_mem_kept (rdW W2 mem2)).
  - replace (spZ regs - 32 + 24 - 8 * Z.of_nat j) with (spZ regs - 8 - 8 * Z.of_nat j) by lia. exact (HFR j r Hj).
  - intros kk Hkk. apply GX1; [lia | lia | intros (r' & [] & _)]. }
destruct (dpgb_tail_seed W3 mem3 regs3 regs (SLit 0) HspR3 Hsp16 HFR3) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 (dpgb_extra regs)))) by apply Eimg_env.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs3 (dpgb_extra regs))) n = getr regs3 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j (rr : bv 5), nth_error dpgb_saved j = Some (bv_unsigned rr) ->
  ew (Eimg (Ereg regs3 (dpgb_extra regs))) (32 + j) = getr regs rr).
{ intros j rr Hj. assert (Hj3 : (j < 3)%nat) by (apply (proj1 (nth_error_Some dpgb_saved j)); rewrite Hj; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  assert (Hx : nth_error (dpgb_extra regs) j = Some (getr regs (Z_to_bv 5 (bv_unsigned rr))))
    by (unfold dpgb_extra; rewrite nth_error_map, Hj; reflexivity).
  rewrite (nth_error_nth _ _ _ Hx), Z_to_bv_bv_unsigned. reflexivity. }
remember (Eimg (Ereg regs3 (dpgb_extra regs))) as E eqn:HE.
(* 0x8cd34 .. 0x8cd50: a1 := the shape, a0 := c, a2 := 0, the frame restored, then `j answer` *)
paj_run_tok RUN HS HJ3 SHOK Bspan.
{ awr_ok_tac. }
rewrite ?wvb_collapse in HJ3.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgT := rg) in *; set (mT := mm) in *; set (mdT := mdq) in *
end.
clearbody mdT.
(* the registers at the tail jump *)
assert (S1 : getr rgT 1 = getr regs 1) by (rewrite T1; exact (EX 0%nat 1%bv eq_refl)).
assert (S8 : getr rgT 8 = getr regs 8) by (rewrite T8; exact (EX 1%nat 8%bv eq_refl)).
assert (S9 : getr rgT 9 = getr regs 9) by (rewrite T9; exact (EX 2%nat 9%bv eq_refl)).
assert (R3T : getr rgT 3 = w64 (as_gp B)) by (rewrite T3, (EE 3%nat 3%bv eq_refl), X3; exact R3).
assert (R4T : getr rgT 4 = w64 (as_tp B)) by (rewrite T4, (EE 4%nat 4%bv eq_refl), X4; exact R4).
assert (R10T : getr rgT 10 = w64 (rec_slot R)) by (rewrite T10, (EE 9%nat 9%bv eq_refl), X9; exact R9).
assert (R11T : getr rgT 11 = w64 q) by (rewrite T11, (EE 10%nat 10%bv eq_refl); exact Hq10).
assert (RspT : spZ rgT = spZ regs).
{ unfold spZ at 1. rewrite T2, (EE 2%nat 2%bv eq_refl).
  change (bv_unsigned (getr regs3 2%bv)) with (spZ regs3). rewrite Hsp3, unsigned_lit_small by lia. lia. }
assert (HI : forall r, 18 <= r <= 27 -> getr rgT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (Rhi r Hr), <- (HP3 r ltac:(unfold acallee_saved; lia)).
  assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
  - rewrite (dpgb_z5 18%bv 18 eq_refl), T18. exact (EE 18%nat 18%bv eq_refl).
  - rewrite (dpgb_z5 19%bv 19 eq_refl), T19. exact (EE 19%nat 19%bv eq_refl).
  - rewrite (dpgb_z5 20%bv 20 eq_refl), T20. exact (EE 20%nat 20%bv eq_refl).
  - rewrite (dpgb_z5 21%bv 21 eq_refl), T21. exact (EE 21%nat 21%bv eq_refl).
  - rewrite (dpgb_z5 22%bv 22 eq_refl), T22. exact (EE 22%nat 22%bv eq_refl).
  - rewrite (dpgb_z5 23%bv 23 eq_refl), T23. exact (EE 23%nat 23%bv eq_refl).
  - rewrite (dpgb_z5 24%bv 24 eq_refl), T24. exact (EE 24%nat 24%bv eq_refl).
  - rewrite (dpgb_z5 25%bv 25 eq_refl), T25. exact (EE 25%nat 25%bv eq_refl).
  - rewrite (dpgb_z5 26%bv 26 eq_refl), T26. exact (EE 26%nat 26%bv eq_refl).
  - rewrite (dpgb_z5 27%bv 27 eq_refl), T27. exact (EE 27%nat 27%bv eq_refl). }
assert (HPT : aregs_preserved regs rgT).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct (Z.le_gt_cases 18 r) as [H18 | H18]; [exact (HI r ltac:(lia))|].
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]].
  - rewrite (dpgb_z5 2%bv 2 eq_refl). apply bv_eq. change (spZ rgT = spZ regs). exact RspT.
  - rewrite (dpgb_z5 3%bv 3 eq_refl), R3T. symmetry. exact Hgp.
  - rewrite (dpgb_z5 4%bv 4 eq_refl), R4T. symmetry. exact Htp.
  - rewrite (dpgb_z5 8%bv 8 eq_refl). exact S8.
  - rewrite (dpgb_z5 9%bv 9 eq_refl). exact S9. }
assert (Hchg : false = negb (bv_unsigned (getr rgT 12) =? 0)) by (rewrite T12; reflexivity).
(* the epilogue wrote nothing *)
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem3) (mrestrict _ mT) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ (w_H W3) mem3 mT (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN
end.
assert (HKT : forall a, 0 <= a < 2 ^ 64 -> rdW W3 mT a = rdW W3 mem3 a) by (intros a Ha; exact (UN a Ha (fun z => z))).
(* the state the tail jump hands to answer *)
pose proof (proj1 HJ3) as HART.
pose proof HJ3 as (_ & HlyT & _ & _ & _ & HfrT & HnevT & _ & F1T & _).
pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW W3 mT))
  by exact (dpgb_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] ly2 S2 W3 mT mdT _ HAR0 HOin HJ3 HROD).
pose proof (cmd_ro_ok_of_aro ly2 S2 W3 mT mdT HART HRODT) as HROT.
assert (HFRT : Z.of_nat (length (frames S2)) <= 8) by (rewrite HfrT; exact Hfr8).
assert (HCH : achain ly2 (rdW W3 mT) (spZ regs + 0) (s0Z rgT) ch).
{ rewrite Z.add_0_r.
  assert (Es0 : s0Z rgT = s0Z regs) by (unfold s0Z; rewrite S8; reflexivity).
  rewrite Es0. apply (achain_ly_top ly ly2 _ _ _ _ EtopT).
  apply (achain_kept ly (rdW W mem) (rdW W3 mT) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply F1T; [lia | lia |]. intros Hfp. pose proof (dpgb_FP_low B ly S W mem md O HAR0 HOin a Hfp). lia. }
(* the recorder at the tail jump: rec_shape_of and the epilogue kept g_rec, record.spill and its blocks *)
destruct HREP2 as (Q2 & HAT2 & HQ2).
set (O2 := (p, Z.of_nat (length x) + 1) :: O1) in *.
assert (HO2bl : forall pn, In pn (lay_blocks Q2) -> In pn (ablocks B ly2 S2)) by exact (lay_blocks_in _ _ _ _ _ _ HAT2).
assert (HO2in : forall pn, In pn O2 -> In pn (ablocks B ly2 S2)) by (intros pn H; exact (HO2bl pn (proj1 (HQ2 pn) H))).
assert (HKR : dpgb_rd_kept Q2 (rdW W2 mem2) (rdW W3 mT) (fun _ => False)).
{ intros a Ha _.
  destruct Ha as [Ha | [Ha | ((pb & nb) & Hpn & Hr)]].
  - rewrite HKT by (unfold A_G_REC, REC_SIZE in Ha; lia).
    destruct (dpgb_unowned B HB a ltac:(left; exact Ha)) as [Hown Herr].
    apply GX3; [apply cmd_prog_img, dpgb_in_PG; left; exact Ha | exact Hown | exact Herr |
      apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]].
  - rewrite HKT by (unfold A_REC_SPILL, SC_SIZE in Ha; lia).
    destruct (dpgb_unowned B HB a ltac:(right; exact Ha)) as [Hown Herr].
    apply GX3; [apply cmd_prog_img, dpgb_in_PG; right; exact Ha | exact Hown | exact Herr |
      apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]].
  - cbn [fst snd] in Hr. pose proof (HO2bl _ Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR2 Hin) as (_ & H4096 & Hpc & _ & _ & _ & Hk0).
    pose proof (dpgb_req_ge nb (proj1 Hk0)) as [_ Hreq].
    rewrite HKT by lia.
    replace a with (pb + (a - pb)) by lia.
    apply (GX2 pb nb (a - pb)); [exact Hin | exact Hin | lia | intros (r' & [] & _)]. }
assert (HAT : arep_at (ablocks B ly2 S2) (rdW W3 mT) A_G_REC A_REC_SPILL (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) Q2)
  by exact (dpgb_arep_kept _ _ _ _ _ _ HAT2 HO2bl HKR).
assert (HREPT : rec_repA B ly2 S2 (rdW W3 mT) (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) O2)
  by (exists Q2; split; [exact HAT | exact HQ2]).
(* the answer the recorder holds: 0 or the start of one of its blocks *)
assert (HOLD : exists old, aval_mem (rdW W3 mT) (A_G_REC + OFF_ANSWER) 8 old /\ 0 <= old < 2 ^ 64 /\
  (old = 0 \/ exists m, In (old, m) O2)).
{ pose proof (dpgb_answer_ptr _ _ _ _ HAT) as H.
  destruct (l_answer Q2) as [[a m]|] eqn:EA.
  - exists a. split; [exact H|].
    assert (Hin : In (a, m) (lay_blocks Q2))
      by (unfold lay_blocks; rewrite EA; cbn [oblk]; rewrite !in_app_iff; right; right; left; left; reflexivity).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ a m HART (HO2bl _ Hin)) as (_ & H4096 & Hpc & _ & _ & _ & Hk).
    pose proof (dpgb_req_ge m (proj1 Hk)) as [Hr1 _].
    split; [lia|]. right. exists m. exact (proj2 (HQ2 _) Hin).
  - exists 0. split; [exact H|]. split; [lia | left; reflexivity]. }
destruct HOLD as (old & Hold & Hold64 & Hold').
(* answer's other premises *)
assert (HSH : r_refuse (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) = 0 ->
  astr_argA B ly2 S2 (rdW W3 mT) (in_roP SEGS RLO RHI) O2 q (Some (shape_of dpgb_verb)) /\
  fits (shape_of dpgb_verb)).
{ intros _. split; [|exact dpgb_fits].
  apply (dpgb_argA_rd B ly2 S2 (rdW W3 mem3) (rdW W3 mT) O2 q _ (HqA O2)).
  intros i Hi. apply HKT.
  exact (dpgb_argA_bound B cmd_ro_prog_apart ly2 S2 W3 mT mdT _ [] q _ HART (proj1 Hq64) (HqA []) i Hi). }
assert (HSLOT : r_refuse (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) = 0 -> false = true ->
  (exists k, nth_error (r_calls (rec_record R REC_DESCRIPTORS_PANEL_GET [x])) k = Some (REC_DESCRIPTORS_PANEL_GET, [x]) /\
     rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (rec_slot R = A_REC_SPILL /\ (REC_DESCRIPTORS_PANEL_GET, [x]) = r_spill (rec_record R REC_DESCRIPTORS_PANEL_GET [x])))
  by (intros _ Hf; discriminate Hf).
assert (HEVT : st_nev S2 + EV_ANSWER <= EV_MAX)
  by (unfold EV_DESCRIPTORS_PANEL_GET, EV_REC_SHAPE_OF in *; lia).
set (t := snd (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x])
  (shape_of dpgb_verb) false)).
assert (Ht : snd (descriptors_panel_get_m R (Some x)) = t) by (rewrite HM; reflexivity).
assert (HLIVET : blocks_bytes S2 + LIVE_ANSWER t <= LIVE_MAX).
{ unfold LIVE_DESCRIPTORS_PANEL_GET in Hlive. rewrite Ht in Hlive. lia. }
assert (HXa : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HMOKT : mo_ok MT S2 (XM_ANSWER MT t)).
{ apply (mok_station MT S S2 (XM_DESCRIPTORS_PANEL_GET MT R (Some x))
    (XM_RECORD MT R + XM_ARG_S MT (Some x)) (XM_ANSWER MT t) MTL MOK MLE2 HXa).
  unfold XM_DESCRIPTORS_PANEL_GET. rewrite Ht. lia. }
(* ---------- the tail jump: answer runs at the entry's sp and returns to the entry's caller ---------- *)
rewrite (dpgb_sig_ans cmd_sig_prog_PB).
eapply SRr_mono.
{ eapply (callS_wideF B LAWS W3 rgT mT _ DESCRIPTORS_PANEL_GET_STK (spZ regs) (dpgb_FP O) ly S W mem md [] ly2 S2 mdT
    (EV_RECORD R + EV_ARG_S + EV_REC_SHAPE_OF) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER 0 (getr rgT 1) ch _ HJ3).
  - rewrite RspT. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3T.
  - exact R4T.
  - reflexivity.
  - rewrite S1. exact Hra.
  - rewrite S1. exact Hra4.
  - exact HCH.
  - intros HPRE3. eapply SRr_mono.
    + exact (TANSWER fx ly2 S2 W3 rgT mT mdT ch (rec_slot R) q old (REC_DESCRIPTORS_PANEL_GET, [x]) (shape_of dpgb_verb) false
        (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) O2
        HPRE3 Hfrm HFRT HRODT HROT R10T Hc64 R11T Hq64 Hchg HREPT Hold Hold64 HSH HSLOT HEVT HLIVET HMOKT).
    + cbv beta. intros Wx cx _ (fx' & lyx & Sx & regsx & memx & mdx & -> & HFx & HCx & HJx & HPx & HKx).
      exists fx', lyx, Sx, regsx, memx, mdx. split; [reflexivity|]. split; [exact HFx|]. split; [exact HCx|].
      split; [exact HJx|]. split; [exact HPx | exact HKx].
  - (* every byte answer writes is one this call may write *)
    intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp]; [|apply inFP_cons in Hfp as [Ha | Hfp]].
    + apply (dpgb_awr_slot B HB cmd_prog_img). left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
    + apply (dpgb_awr_slot B HB cmd_prog_img). left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (pb & nb & Hin & Hr).
      apply dpgb_filter_in in Hin.
      pose proof (HO2in _ Hin) as HinT.
      destruct (in_dec recb_pair_dec (pb, nb) O) as [HO | HnO].
      * right; left. split; [|exists pb, nb; split; [exact HinT | exact Hr]].
        replace a with (pb + (a - pb)) by lia.
        apply (dpgb_inFP_blk O pb nb (a - pb) HO). lia.
      * right; right; left. exists pb, nb. split; [exact HinT|]. split; [|exact Hr].
        intros H0. destruct Hin as [Hpn | Hin1].
        -- assert (Hnc : ~ In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc)).
           { intros Hc. rewrite Forall_forall in Hap2. specialize (Hap2 _ Hc). cbn [fst snd] in Hap2.
             unfold iv_apart in Hap2. lia. }
           rewrite <- Hpn in H0, HnO. exact (HnO (Bgone _ H0 Hnc)).
        -- exact (HnO (BO1 _ Hin1)).
  - (* no byte of answer's footprint is in this call's stack window *)
    intros ly5 S5 W5 regs5 mem5 md5 _ a Hfp Hw _. exfalso.
    apply inFP_cons in Hfp as [Ha | Hfp]; [|apply inFP_cons in Hfp as [Ha | Hfp]].
    + unfold A_G_REC, OFF_ANSWER in Ha. lia.
    + unfold A_G_REC, OFF_STATE in Ha. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (pb & nb & Hin & Hr).
      apply dpgb_filter_in in Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HART (HO2in _ Hin)) as (_ & _ & Hbc & _). lia. }
(* ---------- answer's post is the contract's post ---------- *)
cbv beta. intros W5 c5 _ (fx' & ly5 & S5 & regs5 & mem5 & md5 & -> & HFR5 & HFC5 & HJ5 & HJc5 & HP5 & HK5).
destruct HK5 as (p1 & p2 & O' & HK5). cbv zeta in HK5.
destruct HK5 as (Hp2r & Hp24096 & H12 & Hfr12 & Hbl5 & HREP5 & HO'iff & Hstr5 & Hbb5 & HMLE5).
pose proof (proj1 HJ5) as HAR5.
assert (HO2iff : forall pn, In pn O2 <-> In pn O1 \/ pn = (p, Z.of_nat (length x) + 1)).
{ intros pn. unfold O2. cbn [In]. split; intros [H | H]; [right; symmetry; exact H | left; exact H |
    right; exact H | left; symmetry; exact H]. }
unfold dpgb_post, apost_baseF. exists fx', ly5, S5, regs5, mem5, md5.
split; [rewrite S1; reflexivity|].
split; [exact HFR5|]. split; [exact HFC5|].
split.
{ eapply (ajournal_mono_k SEGS B); [exact HJ5|]. unfold EV_DESCRIPTORS_PANEL_GET, EV_REC_SHAPE_OF. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPT HP5)|].
apply (dpgb_post_of B MT ly S R (Some x) O lyc Sc O1 ly2 S2 ly2 S2 W3 mT mdT ly5 S5 W5 regs5 mem5 md5 x p p1 p2 old
  O2 O' (fst (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x]) (shape_of dpgb_verb) false))
  t BLK HPerm2 Hap2 (Permutation_refl _) HART HAR5 HO2iff HO2in Hold' Hp24096 H12 Hfr12 Hbl5 HREP5 HO'iff Hstr5 Hp2r).
- rewrite HM. apply surjective_pairing.
- unfold LIVE_DESCRIPTORS_PANEL_GET. rewrite Ht. unfold t in *. clear - Hbb5 HBB2. lia.
- apply (mle_weaken MT S S5 _ _ MTL (mle_station MT S S2 S5 _ _ MTL MLE2 HMLE5)).
  unfold XM_DESCRIPTORS_PANEL_GET. rewrite Ht. unfold t in *. clear - MT R x. lia.
Qed.

End e.
End f.
End d.

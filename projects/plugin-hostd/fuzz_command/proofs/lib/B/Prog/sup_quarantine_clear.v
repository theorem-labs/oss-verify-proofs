(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_quarantine_clear (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan): the theorem `tsup_quarantine_clear_holds` for the statement
   lib/B/Prog/sup_quarantine_clear_c.v, from the entry (the prologue and the call of record), the middle segments
   (sup_quarantine_clear_m.v) and the tail (sup_quarantine_clear_t.v), in the form of
   lib/A/Prog/sup_quarantine_clear.v and _s3.v (the A walk, a working branch f2402580166), re-derived on
   B's code. *)

(* sup_quarantine_clear on B (recorder.c:411-417; entry BASE + AF_sup_quarantine_clear = 0x8bdb0, 22 instructions;
   capstone on the .symtab entry of fuzz_command.asan-ubsan): 0x8bdb0 .. 0x8bdc8: addi sp,sp,-32; sd ra,24(sp);
   sd s0,16(sp); sd s1,8(sp); mv s0,a0; li a0,11; jal record. No branch, no inline ASan check, no UBSan trap site in
   the function (the slot's checks are record's and arg_s's), so no report edge to refute here. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c rec_shape_of_c mix_call_c hand_back_c answer_c sup_quarantine_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRest CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_quarantine_clear_aux sup_quarantine_clear_t sup_quarantine_clear_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the value a register held at the entry, as the frame stores it *)
Ltac sqcb_fr_val EE r :=
  cbn [sv_denot]; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z.add_0_r; reflexivity.
Ltac sqcb_fr_rng regs r :=
  let Hb := fresh "Hrng" in
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb;
  cbn; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees, each at every FP state (sup_quarantine_clear_c.v:73-76), and its object bridge *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of a Theorem Labs lane's RULING-STMT.md section 1: the allocator record, the meter's laws, the program
   functions' call targets (a Theorem Labs lane's cmd_sig_prog_PB at the pinned image), and the image facts at the pinned image
   under a Theorem Labs lane's name (lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib); a Theorem Labs lane's CmdRecRest / CmdRecRo / CmdRecImg give the
   read-only, program-static and heap-tail facts from them for any segs and B *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @CmdRecBase.cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @CmdRecBase.cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RUN := paj_run B LAWS.
Let cmd_prog_img := @CmdRecRest.cmd_prog_img rc SK SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart := @CmdRecRest.cmd_ro_prog_apart rc SK SEGS B LAWS HB IMG.
Let ROB := @CmdRecRo.ROB rc SK SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro := @CmdRecRo.cmd_ro_ok_of_aro rc SK SEGS B LAWS HB IMG.

Let S1L := sqcb_S1 B MT (TARG_S := TARG_S) (TREC_SHAPE_OF := TREC_SHAPE_OF) (TANSWER := TANSWER) (VOBJS := VOBJS)
  (HB := HB) (IMG := IMG) (MTL := MTL) (cmd_sig_prog_PB := cmd_sig_prog_PB).

(* the entry (0x8bdb0): the 32-byte frame, s0 := which, the call of record(11) *)
Lemma sqcb_SA : forall ly S W regs mem md ch pw which R O,
sqcb_pre B MT ly S W regs mem md ch pw which R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_quarantine_clear) regs mem md)
(apost_baseF SEGS B SQB_STK (sqcb_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqcb_Q B MT ly S R O which)).
Proof.
intros ly S W regs mem md ch pw which R O PRE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & Hfrm0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQTi).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SQB_STK = 16592) by reflexivity.
assert (HPRES : forall a, spZ regs - SQB_FRAME <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; rewrite HST; unfold SQB_FRAME in Ha; lia).
rewrite HST in Hslo.
set (sp0 := spZ regs) in *.
pose proof HARG as (x & Hwh & (b0 & m0 & Hin0 & Hb01 & Hb02) & _ & Hxl & _).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sqcb_rec_repA_in B ly S _ R O HREP).
assert (Hn16 : (length (r_calls R) <= 16)%nat).
{ destruct HREP as (Q0 & (_ & _ & _ & (Gl & _) & _) & _). exact Gl. }
destruct (sqcb_slot_bounds R Hn16) as (Hcs & Hcb).
set (c := rec_slot R) in *.
destruct (sqcb_blk_bounds B ly S W mem md b0 m0 HAR Hin0) as (Hbb0 & Hbc0 & _ & Hmr0 & _).
assert (Hsp : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
pose proof (sqcb_seed_entry W regs mem Hsp Hal16 HPRES) as HS.
pose proof (ajournal_init SEGS B SQB_STK (sqcb_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew (sqcb_E regs regs) kk = getr regs rr)
  by (intros kk rr Hkk; exact (sqcb_E_reg regs regs kk rr Hkk)).
assert (HEI : img_env VAL A_LIM (sqcb_E regs regs)) by exact (sqcb_E_img regs regs).
set (E := sqcb_E regs regs) in *.
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at.
(* 0x8bdb0 .. 0x8bdc8: the frame, s0 := which, a0 := 11, jal record *)
paj_run_tok RUN HS HJ SHOK sqcb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
pmkst HS. sqcb_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRA end.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1. apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) (fun a => sp0 - 32 <= a < sp0) HFRA);
  [|exact Ha | exact H1].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ) as HARc.
assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + SQB_RETR)) by (rewrite P1; reflexivity).
assert (G2 : getr (ms_regs ms) 2 = w64 (sp0 - SQB_FRAME)) by (rewrite P2, Usp; unfold w64, SQB_FRAME; f_equal; lia).
assert (G2s : spZ (ms_regs ms) = sp0 + -32)
  by (unfold spZ; rewrite G2; unfold w64; rewrite unsigned_lit_small by (unfold SQB_FRAME; lia); unfold SQB_FRAME; lia).
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (G8 : getr (ms_regs ms) 8 = w64 pw) by (rewrite P8, (EE 10%nat 10%bv eq_refl); exact H10).
assert (G10 : getr (ms_regs ms) 10 = w64 SQB_FN) by (rewrite P10; reflexivity).
assert (X18_27 : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (H10r : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H10r as [-> | H10r]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
(* the frame the prologue wrote: the entry's ra, s0, s1 at sp0 - 8, - 16, - 24 *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) sqcb_frame) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict mkst] in HR0 end.
assert (HFRm : sqcb_frame_at (mrestrict (w_H W) (ms_mem ms)) (sp0 - SQB_FRAME) regs).
{ intros j r Hjr.
  unfold sqcb_saved in Hjr. destruct j as [|[|[|j]]]; cbn in Hjr; try (destruct j; discriminate); injection Hjr as <-.
  - replace (sp0 - SQB_FRAME + 24 - 8 * Z.of_nat 0) with (sp0 + -8) by (unfold SQB_FRAME; cbn; lia).
    apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) _ HR0 Usp ltac:(cbn; tauto));
    [sqcb_fr_val EE 1%nat | sqcb_fr_rng regs 1 | cbn; lia].
  - replace (sp0 - SQB_FRAME + 24 - 8 * Z.of_nat 1) with (sp0 + -16) by (unfold SQB_FRAME; cbn; lia).
    apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) _ HR0 Usp ltac:(cbn; tauto));
    [sqcb_fr_val EE 8%nat | sqcb_fr_rng regs 8 | cbn; lia].
  - replace (sp0 - SQB_FRAME + 24 - 8 * Z.of_nat 2) with (sp0 + -24) by (unfold SQB_FRAME; cbn; lia).
    apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) _ HR0 Usp ltac:(cbn; tauto));
    [sqcb_fr_val EE 9%nat | sqcb_fr_rng regs 9 | cbn; lia]. }
assert (HREPc : rec_repA B ly S (rdW W (ms_mem ms)) R O).
{ apply (sqcb_rec_repA_ext B ly S (rdW W mem) ly S _ _ _ HREP HOin).
  intros a [Ha | [Ha | (pn & Hpn & Ha)]]; apply KEEP;
  try (unfold A_G_REC, REC_SIZE in Ha; lia); try (unfold A_REC_SPILL, SC_SIZE in Ha; lia).
  all: destruct pn as [b m]; cbn [fst snd] in Ha;
    destruct (sqcb_blk_bounds B ly S W mem md b m HAR (HOin _ Hpn)) as (Hb & Hbc & _ & Hmr & _); lia. }
assert (HAROc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms)))
  by exact (sqcb_aro B (ROB := ROB) cmd_ro_prog_apart _ ly S W mem md O ly S W (ms_mem ms) mdv [] _ sp0 HAR HOin HJ HROD).
assert (HXM0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
assert (HXS0 : 0 <= XM_ARG_S MT which).
{ unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT MTL). lia. }
(* the footprint of record: g_rec.ncalls, the slot's fn and nargs, and on the spill arm the spill's argument blocks *)
assert (HFPR : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (c, c + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a ->
    (inFP cmd_PG a /\ inFP (sqcb_FP O) a) \/ (inFP (sqcb_FP O) a /\ exists b n, In (b, n) O /\ b <= a < b + req_size n)).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
  - left. split; [apply sqcb_PG_grec | unfold sqcb_FP; apply inFP_cons; left]; unfold OFF_NCALLS, REC_SIZE in *; lia.
  - apply inFP_cons in Ha as [Ha | Ha].
    + left. destruct (sqcb_PG_slot R a Hn16 ltac:(fold c; unfold CALL_SIZE; lia)) as [H1 H2].
      split; [exact H1 | exact (sqcb_FP_O O a H2)].
    + destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
      right. split; [unfold sqcb_FP; apply inFP_cons; right; apply inFP_cons; right; exact Ha|].
      exact (inFP_ablocks_fp_inv O a Ha). }
assert (HFPRlow : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (c, c + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFPR a Ha) as [[_ H] | [H _]]; exact (sqcb_FP_low B ly S W mem md O a HAR HOin H). }
(* the call of record(11) (0x8bdc8) *)
rewrite (cmd_sig_prog_PB CS_record ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_record) with (BASE + AF_record).
assert (HRS : RECORD_STK = 16560) by reflexivity.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ SQB_STK sp0 (sqcb_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK _ (EV_RECORD R) (-32) (w64 (BASE + SQB_RETR)) []
    (fun ly1 S1 W1 regs1 mem1 md1 => exists (F O1 : list (Z * Z)),
      getr regs1 10 = w64 (rec_slot R) /\
      Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) /\
      Z.of_nat (length F) = rec_spill_frees R /\
      (forall pn, In pn F -> In pn O) /\
      rec_repA B ly1 S1 (rdW W1 mem1) (rec_record R SQB_FN []) O1 /\
      (forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
      blocks_bytes S1 <= blocks_bytes S /\
      mo_le MT S S1 (XM_RECORD MT R)) HJ G2s).
  - reflexivity.
  - lia.
  - rewrite HRS. lia.
  - rewrite HRS, HST. lia.
  - exact G3.
  - exact G4.
  - exact G1.
  - unfold w64. apply sqcb_ret_ok. left; reflexivity.
  - unfold w64. rewrite sqcb_ret_val by (left; reflexivity). unfold SQB_RETR, AF_sup_quarantine_clear. lia.
  - apply achain_low. unfold s0Z. rewrite G8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TRECORD fx ly S W (ms_regs ms) (ms_mem ms) _ [] SQB_FN R O HPRE1).
      * exact HAROc.
      * exact G10.
      * unfold SQB_FN, REC_FN_COUNT. lia.
      * exact HREPc.
      * unfold EV_SUP_QUARANTINE_CLEAR, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HEV. lia.
      * apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_QUARANTINE_CLEAR.
        pose proof (HXM0 (snd (sup_quarantine_clear_m R which))). lia.
    + cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & HQ1).
      exists ly1, S1, regs1, mem1, md1. split; [rewrite G1; reflexivity|]. split; [exact HJ1|]. split; [exact HP1|].
      exact HQ1.
  - intros a Ha. destruct (HFPR a Ha) as [[HP Hf] | [Hf (b & n & Hbn & Hba)]].
    + exact (sqcb_awr_prog B HB cmd_prog_img _ _ _ _ _ _ _ _ a HP Hf).
    + right; left. split; [exact Hf|]. exists b, n. split; [exact (HOin _ Hbn) | exact Hba].
  - intros ly1' S1' W1' regs1' mem1' md1' _ a Ha Hw _. exfalso. pose proof (HFPRlow a Ha). rewrite HST in Hw. lia. }
cbv beta. intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HJc1 & HP1 &
  (F & O1 & HR10 & HPERM1 & HFN & HFO & HREP1 & HO1 & HBB1 & MLE1)).
assert (CS1 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs1 rr = getr (ms_regs ms) rr)
  by (intros rr Hr; pose proof (HP1 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (R2 : getr regs1 2 = w64 (sp0 - SQB_FRAME))
  by (rewrite (CS1 2%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G2).
assert (R3 : getr regs1 3 = w64 (as_gp B))
  by (rewrite (CS1 3%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G3).
assert (R4 : getr regs1 4 = w64 (as_tp B))
  by (rewrite (CS1 4%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G4).
assert (R8 : getr regs1 8 = w64 pw)
  by (rewrite (CS1 8%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G8).
assert (R18 : forall r, 18 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP1 r ltac:(unfold acallee_saved; lia)). exact (X18_27 r Hr). }
(* the frame survives record, whose footprint lies below the stack *)
assert (HFRM1 : sqcb_frame_at (mrestrict (w_H W1) mem1) (sp0 - SQB_FRAME) regs).
{ apply (sqcb_frame_kept W W1 (ms_mem ms) mem1 _ regs HFRm). intros a Ha. unfold SQB_FRAME in Ha.
  apply (sqcb_keep_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc1); [exact HFPRlow | lia | rewrite HRS; lia]. }
apply (S1L ly S W regs mem md ch pw which R O x F O1 ly1 S1 W1 regs1 mem1 md1 (0 + EV_RECORD R)
  PRE Hwh HJ1 ltac:(lia) HFRM1 R2 R3 R4 R8 HR10 R18 HREP1 HPERM1 HFO HO1 MLE1 HBB1).
Qed.

Theorem tsup_quarantine_clear_holds : tsup_quarantine_clear_spec B MT.
Proof.
intros ly S W regs mem md ch pw which R O H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
exact (sqcb_SA ly S W regs mem md ch pw which R O
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 H12)))))))))))).
Qed.

End e.
End f.
End d.

Print Assumptions tsup_quarantine_clear_holds.

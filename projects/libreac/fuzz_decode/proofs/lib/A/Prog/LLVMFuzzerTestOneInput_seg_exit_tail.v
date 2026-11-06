(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): aj_flag_store_xR is aj_flag_store_x over a journal at
   a world relation R and the step relation SRrG R (YSRrG.SRrG_msteps for the run, YCbqG's R forms for the journal);
   the run keeps the world, so no law of R is read, and the R form takes R reflexive and transitive as every R rule
   does. aj_flag_store_x keeps its statement and is the instance at wle. aj_stack_malloc_at_xR (the call's own journal
   enters the caller's at R by reflexivity and transitivity; the post's own-call journal stays at wle) and
   aj_set_shadow_at_xR are the other two rules over R; their old names are the instances at wle. *)
(* Modified by Theorem Labs, 2026-10: cgif's frame-area call rule aj_stack_malloc_at (proofs/cgif/cgif_file_fuzzer/lib/
   YCbq.v:1749-1809, this tree's copy lib/Reusable/YCbq.v:1749) restated over YCbqG.v's journal ajournal_x (allocator
   invariant a parameter ARx, ghost head set Hp after S / Hpc after Sc, program statics PST), for the frame-area
   contract astack_malloc_realizes_x of the frozen lib/Reusable/FCiface.v (frameclass d9a884240c6e, sha256
   673aac5ee2f6ed86). Generic: no image
   class, no address, no allocator instance.
   Differences from the donor, each minimal:
   (a) cgif read the model's progress and post from model_laws (stack_malloc_progressP, ml_stack_malloc through
       am_wf); here they are ONE hypothesis in ARx form, SMX, which an instance discharges from its own model laws
       (the cf instance: YG05cf.v stack_malloc_progress_cf and stack_malloc_ok_cf with Wf_cf from ARcf);
   (b) the call's own journal is call_effect_journal_x (YGcallx.v:251) at PST = [], lifted by ajournal_x_nil_pst, and
       composed by ajournal_x_sub (YCbqG.v, footprint FP1 = []); Hp is threaded unchanged (FCiface: a frame-area call
       neither poisons nor unpoisons a head);
   (c) the frame's presence (FCiface's post) is also returned, which a caller writing its new frame needs;
   (d) as cgif's aj_stack_malloc_atS (cgif_file_fuzzer lib/YC85.v:292), the post ends with the call's own journal and
       `exists f, S2 = set_fs f Sc` (the call changes st_fs only), so a caller carries a state fact across the call.
   SECOND RULE, aj_flag_store_x: cgif's aj_flag_store (YCbq.v:2362-2439, the inline release under astack_free_law)
   for the LISTING engine over ajournal_x; its ARx-form hypotheses and their cf discharges are stated at the rule
   (ASFX = YG0dcf.v astack_free_law_cf; FFLX = the two conjuncts of cgif's frame_flag_lawP the rule reads, over ARx;
   SFX = YG05cf.v stack_free_ok_cf).
   THIRD RULE, aj_set_shadow_at_x: cgif's frame-area set_shadow call rule (cgif_rgb_fuzzer lib/YC05.v:206) over
   ajournal_x for FCiface's aset_shadow_realizes_x, taken from WalkH6's set-shadow-v2.patch (cold/h-hpreset-7-walk-H6
   321efcb143d) unchanged but for its comment.
   Rule 24: no ajournal_x port of aj_stack_malloc_at or aj_flag_store existed on any branch read (WalkS8a confirmed,
   2026-10-28 ~23:40Z; h-hpreset-7 stopped c-omx-alloc's lane for both); cgif's released YCbq.v is the source ported.
   Numerals: 0, 10 (cgif's class range), 16 (stack alignment), 64 (the smallest frame), 4096 (= ESTACK, YG0d.v),
   2 ^ 40, 2 ^ 64: LENGTH / DERIVED. No ADDRESS. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSx.v, with its module paths and module names changed; 408 of its 467 lines of code are new or changed and 302 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_tail: the piece ex_tail_stmt of the exit segment of the image-A walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v), offsets
   +0x9a8 .. +0xa48 of the audited listing lib/A/Prog/DecodeList.v (lines 646-686), from llvm_a_st_9a8 to the slot
   post dec_a_post.

   What the code does. +0x9a8 lui/addiw a0 = 0x45e0360e and +0x9b0 sd a0, 0(s5): the released-frame magic into the
   first word of the fake frame F (s5 = F). +0x9b4 beqz s3: s3 = F >= 4096, so the machine-stack arm +0x9e8 .. +0xa04
   is never entered (the engine decides the branch from the atom fact of s3). +0x9b8 li a0, -11 and the eight
   sb a0, i(s11) at +0x9bc .. +0x9d8: the frame's eight shadow bytes become 0xf5 (s11 = shadow_addr F).
   +0x9dc ld a0, 56(s3): the flag pointer FL from the frame's last word; +0x9e0 sb zero, 0(a0): the flag byte, which
   releases the frame (the frame-flag store of lib/Reusable/YCbq.v:2362 aj_flag_store, stated here for the pi engine
   as t_flag_store_pi, cgif lib/YC44.v aj_flag_store_pi's form). +0x9e4 j +0xa08; +0xa08 li a0, 0;
   +0xa0c addi sp, s0, -224; the 13 reloads +0xa10 .. +0xa40 of the words the prologue saved below the entry sp
   (dec_a_saved); +0xa44 addi sp, sp, 224; +0xa48 ret to the caller's ra.

   One run of the plain pi engine (lib/A/Prog/PaSym.v sym_run_pi: no shadow token, so the writable shadow region is
   allowed) covers +0x9a8 .. +0xa48 and stops at the ret, which DecodePaLib.v paj_ret_at takes. The symbolic state:
   registers as atoms 0..31 (Ereg), atom 32 the flag pointer FL, atoms 33..45 the 13 entry values of the saved
   registers in dec_a_saved_at's order; regions: F's first word (s5, written), F's last word (s3, read: FL), F's
   shadow (s11, written), the flag byte (atom 32, written), the 13 saved words below s0 (read).

   The post: the journal after the flag store has own = [] and the frame released (stack_free_state); FP [] goes to
   [YI16.sink_token] (t_fp_token); the callee-saved registers are the 13 reloads, sp = s0 = the entry sp, gp/tp kept;
   the meter from llvm_a_st_9a8's mo_le, dec_cost_ladder and the XL premise; asink_none / ameta_inv from the two
   journal premises; the payload bytes from the journal's block clause. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow DecodeSyms DecodeList DecodePa.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaJournal DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep DecodePaLib YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI00 YO09 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeAddr DecodeImg check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs
  LLVMFuzzerTestOneInput_seg_exit_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The frame-flag store on the pi engine                             *)
(* ------------------------------------------------------------------ *)

(* lib/Reusable/YCbq.v:2362 aj_flag_store, for a run of the plain pi engine (lib/A/Prog/PaRun.v sym_run_pi_sound) in
   place of the absolute one; the pi prefix is cgif lib/YC44.v aj_flag_store_pi's. A run that writes only bytes the
   journal lets it write and the flag byte of its first owned frame, and leaves that byte 0, releases the frame:
   own loses (cid, pos) and the state becomes stack_free_state cid pos Sc. *)
Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation SEGS := (@pa_segs _ decode_listing PI_decode).
#[local] Notation VAL := (@pa_val _ decode_listing PI_decode).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Definition t_plain_stop (st : prun_status dsym) : Prop :=
  match st with PRS_running | PRS_stopped _ => True | _ => False end.
Lemma t_flag_store_pi : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_runN_pi decode_tpi n ss = (ss', st) -> t_plain_stop st ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok_pi SEGS VAL E ss' msr -> mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ms' mat',
     st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJ Hcid Hwr Hflag0 Hk.
unfold sym_runN_pi, decode_tpi in Hrun.
destruct (sym_run_pi_sound dsym SEGS (clookup (@pa_tbl _ decode_listing PI_decode)) VAL
  (@pa_sigma _ decode_listing PI_decode) decode_listing (pa_fetch_ok (PI := PI_decode))
  (@pa_cert _ decode_listing PI_decode) (@pa_B_ok _ decode_listing PI_decode) A_LIM A_LIM_text
  (@pl_lim decode_listing PL_decode)
  _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HS'0 & _ & Hfr0).
assert (HS' : st_ok_pi SEGS VAL E ss' msr') by (destruct st; cbn [prun_post] in HS'0; first [exact HS'0 | destruct Hst]).
clear HS'0.
assert (Hfr : frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr'))
  by (first [exact Hfr0 | destruct ss; exact Hfr0]).
clear Hfr0.
pose proof decode_wx as Hwx. pose proof decode_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL lyc Sc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
apply (SRr_msteps SEGS Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows SEGS _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) ->
  mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a ->
  aview SEGS (w_H W) memc' a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos SEGS B LAWS lyc Sc W (ms_mem ms) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
assert (HAR' : AR SEGS B lyc (stack_free_state cid pos Sc) W memc'
  (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASF lyc Sc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
  - unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 msr' HS'). reflexivity.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_after_write SEGS B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms)
    mdc k memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) own' HJ Heqw
    ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + etransitivity; [exact E2 | symmetry; exact E1].
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
End fp.

(* ------------------------------------------------------------------ *)
(* 2. Journal facts the post reads                                      *)
(* ------------------------------------------------------------------ *)

Section jf. Context {rc : YM05.RunCeil}.
(* A journal with no file range (FP = []) is one with the sink token's range [0, 1) as FP: the token only widens what
   the journal allows, and no clause of the [] journal ever holds an address in a range. *)
Lemma t_fp_token : forall (segs : list Segment) B STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  @ajournal rc dec_A_sink_head segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  @ajournal rc dec_A_sink_head segs B STK sp0 [YI16.sink_token] ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros segs B STK sp0 ly S W mem md own ly' S' W' mem' md' k
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Hc; exfalso; exact (sink_closed_nil Hc)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; exact (F2 p n i H1 H2 Hi (inFP_nil (p + i)))|].
split; [intros a Hi Ho He _; exact (F3 a Hi Ho He (fp_spares_closed [] a sink_closed_nil))|].
split; [intros cid pos a Hin Hr _; exact (F4 cid pos a Hin Hr (inFP_nil a))|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [exact F5 | exact HQT].
Qed.
(* cgif lib/A/ACfh.v ajournal_closed_io at FP = []: the file descriptors and the file system are the entry's. *)
Lemma t_journal_io : forall (segs : list Segment) B STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  @ajournal rc dec_A_sink_head segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros segs B STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
End jf.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic state at +0x9a8 and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* F's first word (s5, atom 21), written; F's last word (s3, atom 19), holding FL (atom 32); F's eight shadow bytes
   (s11, atom 27), written; the flag byte (atom 32), written; the 13 saved words below s0 (atom 8): the word at
   s0 - o holds atom 33 + i for the i-th entry (o, r) of dec_a_saved_at. *)
Definition t_rg_f0 : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 8 [].
Definition t_rg_f56 : YP09.region :=
  YP09.mkRegion (Some 19%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition t_rg_sh : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 0 8 [].
Definition t_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition t_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
(* s3 = F is at least 4096 (decides the `beqz s3` at +0x9b4) and 32-aligned. *)
Definition t_facts : facts := mkFacts [(19%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss9a8 : sstate := mkSS 0x9a8 sr_atoms [t_rg_f0; t_rg_f56; t_rg_sh; t_rg_fl; t_rg_sv] None t_facts.
Definition T_FUEL : N := 64.
Definition t_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi decode_tpi T_FUEL ss9a8).
Definition t_st_end : prun_status dsym := Eval vm_compute in snd (sym_runN_pi decode_tpi T_FUEL ss9a8).
Lemma t_run : sym_runN_pi decode_tpi T_FUEL ss9a8 = (t_ss_end, t_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma t_stop : t_plain_stop t_st_end.
Proof. exact I. Qed.
Lemma t_end_pc : ss_pc t_ss_end = 0xa48.
Proof. reflexivity. Qed.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := decodesegs0.
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
Definition t_extra (cx : dctx) : list word :=
  w64 (d_FL cx) :: map (fun o : Z * Z => YK11.getr (d_regs cx) (Z_to_bv 5 (snd o))) dec_a_saved_at.
Definition t_E (regs : bvmap 5 word) (cx : dctx) : env := Eimg (PI := PI_decode) (Ereg regs (t_extra cx)).
Lemma t_ew_reg : forall regs cx n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (t_E regs cx) n = YK11.getr regs r.
Proof. intros regs cx n r Hn. unfold t_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma t_ew_x : forall regs cx j, (j < 14)%nat -> ew (t_E regs cx) (32 + j) = nth j (t_extra cx) (Z_to_bv 64 0).
Proof. intros regs cx j Hj. unfold t_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma t_bv_small : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* The geometry the run and the post read: F, its shadow, FL and the entry sp, at the frame's layout ly'. *)
Lemma t_geom : forall (B : asyms) (LAWS : AR_laws segs B) (FFL : frame_flag_lawP segs B) (cx : dctx) (W' : world segs)
    ly' S' regs' mem' md' k,
  dec_a_core B cx ly' S' W' regs' mem' md' k ->
  frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx /\ flag_addr ly' DEC_FCLASS (d_fpos cx) = d_FL cx /\
  4096 <= d_F cx /\ d_F cx + 64 <= alloc_ceiling /\ d_F cx mod 32 = 0 /\ in_app (d_F cx) 64 /\
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W') mem' a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H W') mem' (d_SH cx + i)) /\
  apresent (w_H W') mem' (d_FL cx) /\ 4096 <= d_FL cx < alloc_ceiling /\
  (d_FL cx < d_F cx \/ d_F cx + 64 <= d_FL cx) /\ (d_FL cx < d_SH cx \/ d_SH cx + 8 <= d_FL cx) /\
  alloc_ceiling + DEC_LLVMF_STK <= d_sp0 cx <= 2 ^ 47.
Proof.
intros B LAWS FFL cx W' ly' S' regs' mem' md' k HC.
pose proof HC as (HJ & Hfrs & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EFL : flag_addr ly' DEC_FCLASS (d_fpos cx) = d_FL cx).
{ unfold d_FL, flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF' & _). rewrite EF'. reflexivity. }
destruct (al_frames _ _ LAWS ly' S' W' mem' md' _ _ HAR Hin0) as (Hfa32 & Happ & Hfpres & Hshp).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' _ _ HAR Hin0) as (Hf0 & Hfc & _).
destruct (FFL ly' S' W' mem' md' _ _ HAR Hin0) as (Hflp & Hflo & _ & (Hfl4096 & _ & Hflc)).
replace (fs_frame_bytes DEC_FCLASS) with 64 in * by reflexivity.
rewrite EF in Hfa32, Happ, Hfpres, Hshp, Hf0, Hfc. rewrite EFL in Hflp, Hflo, Hfl4096, Hflc.
change (64 / 8) with 8 in Hshp.
assert (ESH : d_SH cx = shadow_addr (d_F cx)) by reflexivity.
split; [exact EF|]. split; [exact EFL|]. split; [lia|]. split; [lia|]. split; [exact Hfa32|]. split; [exact Happ|].
split; [intros a Ha; exact (proj1 (Hfpres a Ha))|].
split; [intros i Hi; rewrite ESH; exact (proj1 (Hshp i Hi))|].
split; [exact Hflp|]. split; [lia|].
split.
{ destruct (Z_lt_le_dec (d_FL cx) (d_F cx)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (d_FL cx) (d_F cx + 64)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (Hfpres (d_FL cx) (conj h h2)) Hflo). }
split.
{ destruct (Z_lt_le_dec (d_FL cx) (d_SH cx)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (d_FL cx) (d_SH cx + 8)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (Hshp (d_FL cx - d_SH cx) ltac:(lia))) as Hno. rewrite <- ESH in Hno.
  replace (d_SH cx + (d_FL cx - d_SH cx)) with (d_FL cx) in Hno by lia. exact (Hno Hflo). }
clear - Hceil Hslo Hshi H47. unfold DEC_LLVMF_STK in *. lia.
Qed.

Lemma t_entry : forall (B : asyms) (LAWS : AR_laws segs B) (FFL : frame_flag_lawP segs B) (cx : dctx) (W' : world segs)
    ly' S' regs' mem' md' k,
  dec_a_core B cx ly' S' W' regs' mem' md' k -> dec_a_fr cx regs' ->
  @st_ok_pi segs decode_val fx (t_E regs' cx) ss9a8
    (restrict (w_H W') (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + 0x9a8)) mem' (YK11.seg_rom segs))).
Proof.
intros B LAWS FFL cx W' ly' S' regs' mem' md' k HC (R19 & R21 & R27).
destruct (t_geom B LAWS FFL cx W' ly' S' regs' mem' md' k HC)
  as (EF & EFL & HF4 & HFc & HFa & HFapp & HFp & HSp & HFLp & HFLr & HFLF & HFLS & Hsp0).
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & _ & _ & _ & HFL & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DEC_LLVMF_STK in Hsp0.
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
set (E := t_E regs' cx).
assert (U8 : bv_unsigned (ew E 8) = d_sp0 cx)
  by (unfold E; rewrite (t_ew_reg regs' cx 8 8%bv eq_refl), R8; apply t_bv_small; lia).
assert (U19 : bv_unsigned (ew E 19) = d_F cx)
  by (unfold E; rewrite (t_ew_reg regs' cx 19 19%bv eq_refl), R19; apply t_bv_small; lia).
assert (U21 : bv_unsigned (ew E 21) = d_F cx)
  by (unfold E; rewrite (t_ew_reg regs' cx 21 21%bv eq_refl), R21; apply t_bv_small; lia).
assert (U27 : bv_unsigned (ew E 27) = d_SH cx)
  by (unfold E; rewrite (t_ew_reg regs' cx 27 27%bv eq_refl), R27; apply t_bv_small; rewrite ESH; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 (d_FL cx)) by (unfold E; exact (t_ew_x regs' cx 0 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = d_FL cx) by (rewrite E32; apply t_bv_small; lia).
unfold dec_a_saved, dec_a_saved_at in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss9a8.
apply (@pa_entry_st_ok_full fx rc decode_listing PI_decode).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks t_rg_f0 t_rg_f56 t_rg_sh t_rg_fl t_rg_sv
      base_val];
    rewrite ?U8, ?U19, ?U21, ?U27, ?U32.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HFp. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (d_F cx) 56 8 (SOff 32 0) (d_FL cx));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HFL).
  + split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HSp. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (d_FL cx + o) with (d_FL cx) by lia. exact HFLp.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ ?b (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      match goal with Sv : rdword _ (?b0 - ?o) = Some (bv_unsigned ?x) |- _ =>
        apply (chunk_ok_val segs E _ b off 8 (SOff n 0) (bv_unsigned x));
        [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity
        | let Hrr := fresh "Hrr" in pose proof (bv_unsigned_in_range 64 x) as Hrr;
          change (bv_modulus 64) with (2 ^ 64) in Hrr; exact Hrr
        | zside
        | replace (b + off) with (b0 - o) by lia; exact (val_mem_of_rdword segs _ _ _ _ Sv) ]
      end end.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, t_rg_f0, t_rg_f56, t_rg_sh, t_rg_fl, t_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U19, U21, U27, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite ESH in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; zify; lia.
- unfold t_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
  change (2 ^ 5) with 32. repeat split; try exact I; lia.
Qed.
End en.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac t_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* ------------------------------------------------------------------ *)
(* 4. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section x. Context {rc : YM05.RunCeil}.
(* The Variables of LLVMFuzzerTestOneInput_seg_exit_cuts.v's Section cuts, in its order. *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

Section w. Context {fx : YK11.FPState}.
Lemma t_walk :
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
  astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W mem) md -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W mem) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  forall (cx : dctx) (W' : world segs) ly' S' regs' mem' md' k,
    dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
    dec_a_core B cx ly' S' W' regs' mem' md' k -> k <= dec_ev_9a8 ->
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx)) ->
    mo_le MT (d_S cx) S' (dec_spent_9a8 MT (d_n cx)) ->
    dec_a_fr cx regs' -> frm_zero (@fp_csr fx) ->
    SRr segs W' (mkCfg (@YK11.mkst fx regs' (w64 (DEC_A_LLVMF + 0x9a8)) mem' (YK11.seg_rom segs)) md')
      (dec_a_post asink_syms tfib_K asink_none ameta_inv RA_LLVMF B MT XL cx).
Proof.
intros LAWS ML MTL MTF HXL ASF FFL HSINK HMETA cx W' ly' S' regs' mem' md' k HB HC Hk Hperm Hmle Hfr Hfrm.
pose proof HB as (HAFN & Hra & _ & _ & Hpn & Hlen & _ & _ & _ & _ & _ & _ & Hsink0 & _ & Hsorted & Hmeta0 & _ & _).
pose proof HAFN as (_ & Hraok & _ & Hgp0 & Htp0 & _).
destruct (t_geom B LAWS FFL cx W' ly' S' regs' mem' md' k HC)
  as (EF & EFL & HF4 & HFc & HFa & HFapp & HFp & HSp & HFLp & HFLr & HFLF & HFLS & Hsp0).
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & _ & _ & Hgp & Htp & _).
pose proof Hfr as (R19 & R21 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
pose proof (t_entry (fx := fx) B LAWS FFL cx W' ly' S' regs' mem' md' k HC Hfr) as HS.
set (E := t_E regs' cx) in HS.
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM E) by (unfold E, t_E; apply Eimg_env).
assert (U21 : bv_unsigned (ew E 21) = d_F cx)
  by (unfold E; rewrite (t_ew_reg regs' cx 21 21%bv eq_refl), R21; apply t_bv_small; lia).
assert (U27 : bv_unsigned (ew E 27) = d_SH cx)
  by (unfold E; rewrite (t_ew_reg regs' cx 27 27%bv eq_refl), R27; apply t_bv_small; rewrite ESH; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 (d_FL cx)) by (unfold E; exact (t_ew_x regs' cx 0 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = d_FL cx) by (rewrite E32; apply t_bv_small; lia).
change (SRr segs W' (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 0x9a8)) mem'
  (YK11.seg_rom segs)) md') (dec_a_post asink_syms tfib_K asink_none ameta_inv RA_LLVMF B MT XL cx)).
(* +0x9a8 .. +0xa48 in one run, the flag store at +0x9e0 releasing the frame. *)
refine (t_flag_store_pi B LAWS ML ASF FFL W' T_FUEL E ss9a8 t_ss_end t_st_end _
  DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [] ly' S' md' k DEC_FCLASS (d_fpos cx) _
  HEI HS t_run t_stop HJ _ _ _ _).
- unfold DEC_FCLASS. lia.
- (* the run writes F's first word, F's shadow and the flag byte *)
  intros a (r & Hin & Ha). unfold ss9a8 in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi t_rg_f0 t_rg_f56 t_rg_sh t_rg_fl t_rg_sv] in Ha;
    rewrite ?U21, ?U27, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists DEC_FCLASS, (d_fpos cx).
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes DEC_FCLASS) with 64. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists DEC_FCLASS, (d_fpos cx).
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes DEC_FCLASS / 8) with 8.
    unfold d_SH in Ha. lia.
  + right. rewrite EFL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem t_ss_end) 3) in
    lazymatch rr with Some ?r3 =>
      pose proof (st_ok_pi_region_nth (PI := PI_decode) E t_ss_end msr 3 r3 HSr eq_refl) as HR3 end end.
  pose proof (field_of_region E (ms_mem msr) 32 (d_FL cx) _ 0 1 0 1 0 1%N (SLit 0) 0 HR3 U32
    ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)). rewrite EFL.
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (d_FL cx + 0 + Z.of_nat 0) with (d_FL cx) in V by lia. exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ _ _.
  set (md2 := with_vm_backing (m_vm_lazy md') mat2 md') in *. clearbody md2.
  eapply (paj_ret_at (PL := PL_decode) (PI := PI_decode) W' E t_ss_end ms2 md2 _ HS2 eq_refl
    ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
  pose proof (ajournal_materialize segs B LAWS decode_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2) as HJ3.
  fold md3 in HJ3. clearbody md3.
  (* the registers at the ret *)
  assert (R1 : YK11.getr (ms_regs ms2) 1 = YK11.getr (d_regs cx) 1).
  { t_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : YK11.getr (ms_regs ms2) 10 = w64 0).
  { t_regv HS2. reflexivity. }
  assert (HP : aregs_preserved (d_regs cx) (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      t_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    1: { transitivity (YK11.getr regs' 8); [apply t_ew_reg; reflexivity|].
         rewrite R8. unfold w64, d_sp0, spZ. apply Z_to_bv_bv_unsigned. }
    1: { transitivity (YK11.getr regs' 3); [apply t_ew_reg; reflexivity|]. rewrite Hgp. symmetry. exact Hgp0. }
    1: { transitivity (YK11.getr regs' 4); [apply t_ew_reg; reflexivity|]. rewrite Htp. symmetry. exact Htp0. }
    all: reflexivity. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = w64 RA_LLVMF).
  { rewrite R1. unfold YK0s.ret_ok in Hraok. rewrite Hraok. rewrite <- Hra. unfold w64, raZ.
    symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hn0 : 0 <= d_n cx) by (rewrite Hlen; lia).
  unfold dec_a_post.
  exists fx, ly', (stack_free_state DEC_FCLASS (d_fpos cx) S'), (ms_regs ms2), (ms_mem ms2), md3, k.
  split; [rewrite Hpc; reflexivity|].
  split; [exact Hfrm|].
  unfold dec_lib_post_x.
  split; [exact (t_fp_token _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|].
  split; [pose proof dec_ev_in_lib; lia|].
  split; [exact HP|].
  split; [exact R10|].
  split; [unfold ablocks; rewrite blocks_stack_free_state; exact Hperm|].
  split; [intros fd; rewrite (proj1 (t_journal_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)); reflexivity|].
  split; [exact (proj2 (t_journal_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3))|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hsorted|].
  (* the walk's own frame list is [] (dec_a_core), and sink_open_fp [] = in_fp [] 0 is false (YI16.v:71) *)
  split; [exact (HSINK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 ltac:(intros (? & [] & ?)) Hsink0)|].
  split; [exact (HMETA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 Hmeta0)|].
  split.
  { unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). apply (mo_le_mono MT MTL _ _ _ _ Hmle).
    pose proof (dec_cost_ladder MT (d_n cx)) as (_ & _ & _ & _ & _ & _ & _ & L8). unfold dec_rest_9a8 in L8.
    pose proof (HXL (d_n cx) Hn0). lia. }
  intros i Hi. destruct Hpn as [[Hz _] | [_ Hin]]; [lia|].
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (req_size_pos0 (d_n cx) Hn0) as Hrq.
  apply (F2 (d_p cx) (d_n cx) i Hin); [| lia | intros (rg & [] & _)].
  unfold ablocks. rewrite blocks_stack_free_state.
  exact (Permutation_in _ (Permutation_sym Hperm) Hin).
Qed.
End w.

Theorem ex_tail_ok : ex_tail_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold ex_tail_stmt.
intros LAWS ML MTL MTF HXL ASF FFL HSINK HMETA cx W' c' HB _ H9a8.
destruct H9a8 as (fx' & ly' & S' & regs' & mem' & md' & k & -> & Hfrm & HC & Hk & Hperm & Hmle & Hfr & _).
exact (@t_walk fx' LAWS ML MTL MTF HXL ASF FFL HSINK HMETA cx W' ly' S' regs' mem' md' k HB HC Hk Hperm Hmle Hfr Hfrm).
Qed.

End x.

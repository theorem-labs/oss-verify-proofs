(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 49 of its 78 lines of code are new or changed and 123 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/check_words_chain_c.v, with its module paths and module names changed; 104 of its 136 lines of code are new or changed and 46 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from an earlier version of lib/A/Prog/check_words_chain.v
   for fuzz_command.asan-ubsan: module paths, the B statement's runtime cells, the alignment premises
   carried into cwc_pre, CwcRec built from lib/B/Prog/CmdRecFacts.v (cr_lit_tail by cmd_tail_vis_at); statement
   passes 4, 4b, 5: the runtime hypotheses hold at every FP state, the entry has rounding
   mode 0, the post is apost_baseF. *)
(* The proof of check_words_chain's statement (lib/B/Prog/check_words_chain_c.v) on the ASan+UBSan build of
   plugin-hostd/fuzz_command (fuzz_command.asan-ubsan), entry 0x890e0.

   The walk is cut where the code joins (lib/B/Prog/check_words_chain_iv.v):
   - check_words_chain_s1.v: the entry to the call of the class-4 side-stack entry at 0x89158;
   - check_words_chain_s2.v: that call, the frame set-up and its two shadow-fill calls, to the guard read < 3;
   - check_words_chain_s3.v: the word loop 0x892b4, by induction on the words left;
   - check_words_chain_s4.v: the tail 0x89334 (the count text, the checks of the recorded call, the two strcmp
     calls);
   - check_words_chain_s5.v: the teardown 0x89408 (the release of the frame) and the return.
   Each of the ten UBSan trap sites (a branch to `unimp` 0x894a8) is refuted in the stage that holds it.
   Each later stage takes the next one as a hypothesis; this file chains them and discharges the walk's own
   hypotheses: the allocator record's laws (AR_laws_ok), the model laws and the image's symbol facts (from the
   entry's AR). The statement's strings in live blocks are the walk's cwc_sblk by definition, and the cells the
   atoi and snprintf entries read are the record's at the entry (cr_rt_cells). The record facts CwcRec names over
   the image's read-only range CMD_RLO .. CMD_RHI come from the lemma file lib/B/Prog/CmdRecFacts.v. What is
   left are the statement's Section hypotheses and the walk hypotheses, with cgif's names: HB (the record
   is this binary's), TL, TLF (PALib, PALibF over the image) and IMG (the image facts).
   The FP state: the loop and the tail call the snprintf wrapper, which returns at another FP state, so the loop,
   the tail and the teardown are proved at every FP state (each takes the next at the FP state it reaches), and
   this file takes the runtime hypotheses in the statement's form, at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG05 YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
check_words_chain_c check_words_chain_s0 check_words_chain_iv check_words_chain_s1 check_words_chain_s2h
check_words_chain_s2 check_words_chain_s3 check_words_chain_s4 check_words_chain_s5.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's runtime entries (lib/B/Prog/check_words_chain_c.v:100-109) *)
Hypothesis ASMALLOC4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASET00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASETF5 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5.
Hypothesis ASETF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
(* the walk hypotheses *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMG : cmd_img_facts SEGS B.

Theorem tcheck_words_chain_ok : tcheck_words_chain_spec B MT.
Proof.
(* Hcp8 and Hwp8, the statement's alignment premises, go into cwc_pre: the tail refutes the trap site 0x8936c
   (call misaligned) with Hcp8, the loop the trap site 0x892d8 (w + k misaligned) with Hwp8 *)
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 HFN HRND HROD H10 H11 H12 Hr64 Hwp HRO HOBJ
Hlo Hhi Hcp8 HNA HNA6 HA1 HA2 HWS Hwp8 Hn3 Hx1 Hx2 Hroom Hev.
assert (HRND0 : frm0 fx) by exact HRND.
pose proof HFN as (HAR & _).
pose proof (AR_laws_ok SEGS B) as LAWS.
assert (BOK : asyms_ok B) by (eapply am_syms; exact (proj1 HAR)).
assert (ML : model_laws (as_universe B)) by (apply model_laws_ok; eapply am_universe; exact (proj1 HAR)).
(* the per-binary record facts (lib/B/Prog/check_words_chain_iv.v CwcRec), each from CmdRecFacts.v *)
assert (HR : CwcRec B CMD_RLO CMD_RHI).
{ constructor.
  - (* cr_tl *) exact TL.
  - (* cr_tlf *) exact TLF.
  - (* cr_grec_ra: the addressability checker cmd_addressable_chk on the recorded calls' range *)
    intros ly0 S0 W0 mem0 md0 HAR0.
    exact (cmd_addressable_chk SEGS B LAWS HB ly0 S0 W0 mem0 md0 (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS) HAR0
      ltac:(vm_compute; reflexivity)).
  - (* cr_grec_not_rt: g_rec is cmd_PG's first range *)
    intros a Ha. apply (cmd_prog_unowned SEGS B LAWS HB IMG a).
    unfold inFP, cmd_PG. exists (A_G_REC, A_G_REC + 960).
    split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
  - (* cr_lit_ra: the addressability and shadow-hull checkers (cmd_aread_ok_chk) on the two literals *)
    intros ly0 S0 W0 mem0 md0 HAR0.
    destruct (cmd_aread_ok_chk SEGS B LAWS HB ly0 S0 W0 mem0 md0 A_FMT_D (LEN_FMT_D + 1) HAR0
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [R1 V1].
    destruct (cmd_aread_ok_chk SEGS B LAWS HB ly0 S0 W0 mem0 md0 A_FMT_SPD (LEN_FMT_SPD + 1) HAR0
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [R2 V2].
    exact (conj R1 (conj V1 (conj R2 V2))).
  - (* cr_lit_ro: the literals are CmdRo's objects (0x218e0, 3) and (0x21b80, 4), so IMG's cif_ro_img and
       cif_ro_unowned hold at their bytes *)
    intros a Ha.
    assert (HX : Exists (in_zr a) cmd_ro_objs).
    { apply Exists_exists. unfold A_FMT_D, LEN_FMT_D, A_FMT_SPD, LEN_FMT_SPD in Ha.
      destruct Ha as [Ha | Ha]; [exists (0x218e0, 3) | exists (0x21b80, 4)];
      (split; [unfold cmd_ro_objs; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]). }
    destruct (cmd_ro_in_to _ (cif_ro_unowned _ _ IMG) a HX) as [Ho He].
    exact (conj (cmd_ro_in_to _ (cif_ro_img _ _ IMG) a HX) (conj Ho He)).
  - (* cr_lit_tail: the literals' ends 0x218e2 and 0x21b83 are in cmd_ro_ends *)
    intros ly0 S0 W0 mem0 md0 HAR0. split.
    + apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly0 S0 W0 mem0 md0 (A_FMT_D + LEN_FMT_D) HAR0).
      change (A_FMT_D + LEN_FMT_D) with 0x218e2. unfold cmd_ro_ends. repeat (first [left; reflexivity | right]).
    + apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly0 S0 W0 mem0 md0 (A_FMT_SPD + LEN_FMT_SPD) HAR0).
      change (A_FMT_SPD + LEN_FMT_SPD) with 0x21b83. unfold cmd_ro_ends. repeat (first [left; reflexivity | right]).
  - (* cr_heap_tail: the terminator lies in the block, and a block's size is at most its request size *)
    intros ly0 S0 W0 mem0 md0 p x HAR0 (_ & (q & k & Hin & Hq1 & Hq2) & _).
    pose proof (crf_req_size_ge k) as Hreq.
    apply (cmd_heap_tail_vis SEGS B LAWS HB ly0 S0 W0 mem0 md0 q k (p + astr_len x) HAR0 Hin).
    unfold astr_len. lia.
  - (* cr_relro_img *) exact (relro_img SEGS B LAWS HB IMG).
  - (* cr_rt_cells: cmd_rec_cells, its first two conjuncts swapped *)
    intros ly0 S0 W0 mem0 md0 HAR0.
    destruct (cmd_rec_cells SEGS B LAWS HB IMG ly0 S0 W0 mem0 md0 HAR0) as (CF & CG & CE).
    exact (conj CG (conj CF CE)). }
pose proof (cr_grec_ra _ _ _ HR) as GREC_RA. pose proof (cr_grec_not_rt _ _ _ HR) as GREC_NOT_RT.
(* the cells the atoi and snprintf entries read are the record's at the entry too *)
destruct (cr_rt_cells _ _ _ HR ly S W mem md HAR) as (HGUARD & HFLAG & HERRNO).
(* the statement's premises in the walk's form: its strings are cwc_sblk by definition *)
assert (HPRE : cwc_pre B CMD_RLO CMD_RHI ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2)
by exact (conj HFN (conj HROD (conj H10 (conj H11 (conj H12 (conj Hr64 (conj Hwp (conj HRO (conj HOBJ
(conj HGUARD (conj HFLAG (conj HERRNO (conj Hlo (conj Hhi (conj Hcp8 (conj HNA (conj HNA6 (conj HA1 (conj HA2
(conj HWS (conj Hwp8 (conj Hn3 (conj Hx1 (conj Hx2 (conj Hroom Hev))))))))))))))))))))))))).
(* the teardown, the tail and the loop at every FP state: each runs on at the FP state the previous snprintf
   call returned *)
assert (TD : forall fx0 : YK11.FPState, CWC_TD_stmt (fx := fx0) B CMD_RLO CMD_RHI).
{ intros fx0. pose proof (ASET00 fx0) as A00. pose proof (ASETF5 fx0) as AF5. pose proof (ASETF8 fx0) as AF8.
  eapply (cwc_td_ok (fx := fx0) (PI := PI)); eassumption. }
assert (TAIL : forall fx0 : YK11.FPState, CWC_TAIL_stmt (fx := fx0) B CMD_RLO CMD_RHI)
by (eapply (cwc_tail_ok (PI := PI)); eassumption).
assert (LOOP : forall fx0 : YK11.FPState, CWC_LOOP_stmt (fx := fx0) B CMD_RLO CMD_RHI)
by (eapply (cwc_loop_ok (PI := PI)); eassumption).
(* the frame set-up runs at the entry's FP state *)
pose proof (LOOP fx) as LOOPx. pose proof (TAIL fx) as TAILx.
pose proof (ASET00 fx) as A00. pose proof (ASETF8 fx) as AF8. pose proof (ASMALLOC4 fx) as AM4.
destruct (HA1 Hn3) as (V1 & R1 & _). destruct (HA2 Hn3) as (V2 & R2 & _).
change (SRr SEGS W (cfg_at SEGS (pa_val A_TEXT + CWC_ENTRY) regs mem md) (cwc_post B ly S W regs mem md)).
eapply cwc_to_sm; try eassumption.
- rewrite Hn3 in HNA. exact HNA.
- intros E0 ms0 mdq sp1 HEI HS SHOK HJ AGo E1024 E33 Hsp1e Hsp1al Hsp1.
  eapply (cwc_s2_ok (fx := fx) (PI := PI)); eassumption.
Qed.

End e.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module names changed; 63 of its 100 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words.v, with its module paths and module names changed; 93 of its 133 lines of code are new or changed and 60 lines of the source are left out. *)
(* The proof of check_words_chain's statement (lib/A/Prog/check_words_chain_c.v) on the ASan build of
   plugin-hostd/fuzz_command, entry 0x88ca0.

   The walk is cut where the code joins (lib/A/Prog/check_words_chain_iv.v):
   - check_words_chain_s1.v: the entry to the call of the class-4 side-stack entry at 0x88d14;
   - check_words_chain_s2.v: that call, the frame set-up and its two shadow-fill calls, to the guard read < 3;
   - check_words_chain_s3.v: the word loop 0x88e74, by induction on the words left;
   - check_words_chain_s4.v: the tail 0x88ed4 (the count text, the three checks of the recorded call, the two
     strcmp calls);
   - check_words_chain_s5.v: the teardown 0x88f6c (the release of the frame) and the return.
   Each later stage takes the next one as a hypothesis; this file chains them and discharges the walk's own
   hypotheses: the allocator record's laws (AR_laws_ok), the model laws and the image's symbol facts (from the
   entry's AR). The statement's strings in live blocks are the walk's cwc_sblk by definition, and the cells the
   atoi and snprintf entries read are the record's at the entry (cr_rt_cells). The record facts CwcRec names over
   the image's read-only range CMD_RLO .. CMD_RHI come from the lemma file CmdRecFacts.v. What is left are
   the statement's Section hypotheses and the walk hypotheses, with cgif's names: HB (the record is
   this binary's), TL, TLF (PALib, PALibF over the image) and IMG (the image facts). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c HarnessPropsA CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
check_words_chain_c check_words_chain_s0 check_words_chain_iv check_words_chain_s1 check_words_chain_s2h
check_words_chain_s2 check_words_chain_s3 check_words_chain_s4 check_words_chain_s5.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
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
(* the statement's runtime entries (lib/A/Prog/check_words_chain_c.v:87-96), at every FP state *)
Hypothesis ASMALLOC4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASET00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASETF5 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5.
Hypothesis ASETF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
(* the walk hypotheses *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMG : cmd_img_facts SEGS B.

Theorem tcheck_words_chain_ok : tcheck_words_chain_spec B MT.
Proof.
(* Hcp8 and Hwp8, the statement's alignment premises (call and w 8-aligned), carry what the B statement's UBSan
   checks need; the ASan walk reads cp + 4, cp + 16, cp + 24 and wp + 8 * k without them: the inline checks of the
   call read the shadow of g_rec over its address range, and the word slot's shadow is 0 by cwc_word_shadow0
   (check_words_chain_s2h.v), which takes the 8-aligned block start of the allocator's shadow law al_shadow *)
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 HFN HRM0 HROD H10 H11 H12 Hr64 Hwp HRO HOBJ
Hlo Hhi Hcp8 HNA HNA6 HA1 HA2 HWS Hwp8 Hn3 Hx1 Hx2 Hroom Hev.
(* the rounding mode 0 of the pre, in PaFx.v's name *)
assert (HRM : frm0 fx) by exact HRM0.
pose proof HFN as (HAR & _).
pose proof (AR_laws_ok SEGS B) as LAWS.
assert (BOK : asyms_ok B) by (eapply am_syms; exact (proj1 HAR)).
assert (ML : model_laws (as_universe B)) by (apply model_laws_ok; eapply am_universe; exact (proj1 HAR)).
(* the per-binary record facts (lib/A/Prog/check_words_chain_iv.v CwcRec), each from CmdRecFacts.v *)
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
  - (* cr_lit_ro: the literals are CmdRo's objects (0x218a0, 3) and (0x21b40, 4), so IMG's cif_ro_img and
       cif_ro_unowned hold at their bytes *)
    intros a Ha.
    assert (HX : Exists (in_zr a) cmd_ro_objs).
    { apply Exists_exists. unfold A_FMT_D, LEN_FMT_D, A_FMT_SPD, LEN_FMT_SPD in Ha.
      destruct Ha as [Ha | Ha]; [exists (0x218a0, 3) | exists (0x21b40, 4)];
      (split; [unfold cmd_ro_objs; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]). }
    destruct (cmd_ro_in_to _ (cif_ro_unowned _ _ IMG) a HX) as [Ho He].
    exact (conj (cmd_ro_in_to _ (cif_ro_img _ _ IMG) a HX) (conj Ho He)).
  - (* cr_lit_tail: the literals' ends 0x218a2 and 0x21b43 are in cmd_ro_ends *)
    intros ly0 S0 W0 mem0 md0 HAR0 HAO0.
    pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly0 S0 W0 mem0 md0 HAR0 HAO0) as ROK.
    split.
    + apply (cmd_tail_vis SEGS B LAWS HB W0 mem0 (A_FMT_D + LEN_FMT_D) ROK).
      change (A_FMT_D + LEN_FMT_D) with 0x218a2. unfold cmd_ro_ends. repeat (first [left; reflexivity | right]).
    + apply (cmd_tail_vis SEGS B LAWS HB W0 mem0 (A_FMT_SPD + LEN_FMT_SPD) ROK).
      change (A_FMT_SPD + LEN_FMT_SPD) with 0x21b43. unfold cmd_ro_ends. repeat (first [left; reflexivity | right]).
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
pose proof (cr_lit_ra _ _ _ HR) as LIT_RA. pose proof (cr_lit_ro _ _ _ HR) as LIT_RO.
(* the cells the atoi and snprintf entries read are the record's at the entry too *)
destruct (cr_rt_cells _ _ _ HR ly S W mem md HAR) as (HGUARD & HFLAG & HERRNO).
(* the statement's premises in the walk's form: its strings are cwc_sblk by definition *)
assert (HPRE : cwc_pre B CMD_RLO CMD_RHI ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2)
by exact (conj HFN (conj HROD (conj H10 (conj H11 (conj H12 (conj Hr64 (conj HRO (conj HOBJ (conj HGUARD
(conj HFLAG (conj HERRNO (conj Hlo (conj Hhi (conj HNA (conj HNA6 (conj HA1 (conj HA2 (conj HWS (conj Hn3
(conj Hx1 (conj Hx2 (conj Hroom Hev)))))))))))))))))))))).
(* the teardown and the tail at every FP state (they run after the snprintf wrapper returned), the loop at the
   entry's *)
assert (TD : forall fx0 : YK11.FPState, CWC_TD_stmt (fx := fx0) B CMD_RLO CMD_RHI)
by (intros fx0; eapply (cwc_td_ok (fx := fx0)); eassumption).
assert (TAILg : forall fx0 : YK11.FPState, CWC_TAIL_stmt (fx := fx0) B CMD_RLO CMD_RHI)
by (intros fx0; eapply (cwc_tail_ok (fx := fx0)); eassumption).
assert (LOOP : CWC_LOOP_stmt B CMD_RLO CMD_RHI) by (eapply cwc_loop_ok; eassumption).
pose proof (TAILg fx) as TAIL.
destruct (HA1 Hn3) as (V1 & R1 & _). destruct (HA2 Hn3) as (V2 & R2 & _).
change (SRr SEGS W (cfg_at SEGS (pa_val A_TEXT + CWC_ENTRY) regs mem md) (cwc_post B ly S W regs mem md)).
eapply cwc_to_sm; try eassumption.
- rewrite Hn3 in HNA. exact HNA.
- intros E0 ms0 mdq sp1 HEI HS SHOK HJ AGo E1024 E33 Hsp1e Hsp1al Hsp1.
  eapply cwc_s2_ok; eassumption.
Qed.

End e.
End f.
End d.

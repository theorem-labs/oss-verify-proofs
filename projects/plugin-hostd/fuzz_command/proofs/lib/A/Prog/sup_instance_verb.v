(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sup_instance_verb's ASan walk (plugin-hostd/fuzz_command, 0x8b3b8, 78 instructions;
   recorder.c:379-388) assembled from its segments (sup_instance_verb_s2.v .. _s14.v), after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACke.v (cgif_close's walk assembled from A/ACh1.v .. ACh8.v); it proves the
   statement of an earlier commit, then of passes 4, 4b, 5. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6 sup_instance_verb_s7 sup_instance_verb_s8 sup_instance_verb_s9.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  sup_instance_verb_s10 sup_instance_verb_s11 sup_instance_verb_s12 sup_instance_verb_s13 sup_instance_verb_s14.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (sup_instance_verb_c.v:74-81), word for word *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's per-binary facts, under cgif's names and the walks' shared names, in those forms; no file of
   the tree states them yet (CmdRecFacts.v) *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
  AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
(* the line's tail word (statement gap G2 in its (b) form: the line is a heap block, the tail comes from it) *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis cmd_rec_cells : forall ly S W mem md, AR SEGS B ly S W mem md ->
  rdW W mem A_FLAG_REPLACE_STR = Some 1 /\ aguard_ok SEGS W mem 0xa7098 0x6045d8 /\
  exists ev, rd32 (rdW W mem) (as_errno B) ev.
Hypothesis cmd_rom_view_on : forall (W : world SEGS) mem,
  arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
(* the accept set " \t" (.str.5) the two wrappers read *)
Hypothesis ZSH_lit_21d60 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (rdW W mem) SHADOW_OFF 0x21d60 3.
Hypothesis HULL_lit_21d60 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  shadow_hull_vis (rdW W mem) 0x21d60 3.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.

Let HY : siv_hyps B MT :=
  Build_siv_hyps B MT TRCF TARG_LINE TARG_I TREC_SHAPE_OF TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL cmd_prog_img
    cmd_prog_writable SIGP cmd_ro_ok_of_aro RRO RELRO_IMG cmd_heap_tail_vis cmd_rec_cells cmd_rom_view_on
    ZSH_lit_21d60 HULL_lit_21d60 cmd_ro_prog_apart.

(* the walk, segment by segment: entry .. record()'s join .. arg_line .. arg_i .. strspn .. strcspn .. rec_shape_of
   .. the tail jump to answer *)
Theorem tsup_instance_verb_walk : siv_walk_goal B MT.
Proof.
exact (siv_seg_E B MT HY (siv_seg_J B MT HY (siv_seg_L B MT HY (fun fx1 => siv_seg_A2 (fx := fx1) B MT HY)))).
Qed.

Theorem tsup_instance_verb_holds : tsup_instance_verb_spec B MT.
Proof.
unfold tsup_instance_verb_spec.
intros ly S W regs mem md ch pl ledger line R O HPRE HFRM HROD HRO H10 Hpl64 H11 Hled HLB HLSTR HLL HLAP HREP HFR HEV
  HLIVE HMOK.
exact (tsup_instance_verb_walk ly S W regs mem md ch pl ledger line R O
  (conj HPRE (conj HROD (conj HRO (conj H10 (conj Hpl64 (conj H11 (conj Hled (conj HLB (conj HLSTR
   (conj HLL (conj HLAP (conj HREP (conj HFR (conj HEV (conj HLIVE HMOK))))))))))))))) HFRM).
Qed.

End e.
End f.
End d.

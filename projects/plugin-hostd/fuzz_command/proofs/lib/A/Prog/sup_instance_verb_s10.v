(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the states at which the segments of sup_instance_verb's ASan walk
   (plugin-hostd/fuzz_command) meet, stated once so each segment is proved against the next one's statement, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_cx / cl_mid: the bundles one segment walk hands the next). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6 sup_instance_verb_s7 sup_instance_verb_s8 sup_instance_verb_s9.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
(* the plain proof's lemmas on the line's first word (lib/Prog/sup_instance_verb.v:210-276); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

(* 0x8b474, after arg_i: both arguments recorded; s1 the line *)
Definition siv_A2_goal : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O lyc Sc (Wc : world SEGS) memc mdc regs1 kk Q1,
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
siv_mid B MT ly S W regs mem md line ledger R O lyc Sc Wc memc mdc regs1 kk Q1 [canon line; dec ledger]
  (rec_spill_frees R + EV_ARG_LINE + EV_ARG_I) (rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line + XM_ARG_I MT ledger)
  (LIVE_ARG_LINE line + LIVE_ARG_I ledger) ->
getr regs1 9 = w64 pl ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SIV_I_RET)) memc (seg_rom SEGS)) mdc)
  (siv_post B MT ly S W regs mem md line ledger R O).

(* 0x8b468, after arg_line: the call recorded (record()'s slot layout Q0) with the canonical line as its first
   argument, held in the block (p1, k1); s1 the line, s2 the ledger number *)
Definition siv_L_goal : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O lyc Sc (Wc : world SEGS) memc mdc regs1 kk Q0 p1 k1,
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
siv_mid B MT ly S W regs mem md line ledger R O lyc Sc Wc memc mdc regs1 kk (slot_lay Q0 R [(p1, k1)]) [canon line]
  (rec_spill_frees R + EV_ARG_LINE) (rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line) (LIVE_ARG_LINE line) ->
getr regs1 9 = w64 pl -> getr regs1 18 = w64 ledger ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SIV_L_RET)) memc (seg_rom SEGS)) mdc)
  (siv_post B MT ly S W regs mem md line ledger R O).

(* 0x8b42c, the join of record()'s two arms: s0 the slot, s3 the shadow base, g_rec.ncalls already counting the
   call; the recorder R0 (R, or R with the spill cleared by rec_calls_free on the spill arm) is represented in the
   reader rd0 with layout Q0, and the memory agrees with rd0 on g_rec / record.spill outside ncalls and on Q0's
   blocks *)
Definition siv_J_goal : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O lyc Sc (Wc : world SEGS) memc mdc regs1 kk
  (R0 : rstate) (Q0 : rlay) (rd0 : reader),
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
ajournal SEGS B SUP_INSTANCE_VERB_STK (spZ regs) (siv_FP O) ly S W mem md [] lyc Sc Wc memc mdc kk ->
0 <= kk <= rec_spill_frees R ->
siv_frame_ok (mrestrict (w_H Wc) memc) (spZ regs) regs ->
siv_regs_ok B regs regs1 (siv_slot R) ->
getr regs1 9 = w64 pl -> getr regs1 18 = w64 ledger -> getr regs1 19 = w64 SB ->
((R0 = R /\ (length (r_calls R) < 16)%nat) \/
 ((16 <= length (r_calls R))%nat /\ R0 = set_spill R (fst (r_spill R), []))) ->
arep_at (ablocks B lyc Sc) rd0 A_G_REC A_REC_SPILL R0 Q0 ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW Wc memc a = rd0 a) ->
(forall pn i, In pn (lay_blocks Q0) -> 0 <= i < snd pn -> rdW Wc memc (fst pn + i) = rd0 (fst pn + i)) ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4
  (Z.of_nat (length (r_calls (rec_record R REC_INSTANCE_VERB [])))) ->
(forall pn, In pn (lay_blocks Q0) -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q0)) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
blocks_bytes Sc <= blocks_bytes S ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SIV_J)) memc (seg_rom SEGS)) mdc)
  (siv_post B MT ly S W regs mem md line ledger R O).

(* the whole walk, from the entry *)
Definition siv_walk_goal : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O,
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_instance_verb) regs mem md)
  (siv_post B MT ly S W regs mem md line ledger R O).

End e.
End f.
End d.

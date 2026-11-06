(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of pins_clear (plugin-hostd/fuzz_command, entry 0x8ccb4), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACke.v (the instantiation of the cgif_close walk) over
   fuzz_command's listing. *)

(* pins_clear (recorder.c:524-533) walks in two segments:
   - lib/A/Prog/pins_clear_s3.v, the entry segment: the frame, the shadow base, and the inlined record() up to
     the point where its two arms meet (0x8cd2c);
   - lib/A/Prog/pins_clear_s4.v, the join segment: the slot's fields, the xstrdup copy of the argument, the
     refusal test, the mix_call fold of the call into g_rec.state, and the tail jump into answer_code.
   This file joins the two and proves the statement of lib/A/Prog/pins_clear_c.v.

   The one premise the statement does not yet carry is the tail of the string argument (`atail_vis` at its
   terminator's word), which xstrdup's contract asks for and which neither the heap arm nor the read-only arm of
   `astr_argA` gives. It is an explicit premise of the theorem, so it
   disappears when the statement carries it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaNoChain PaDenot PaSB PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas pins_clear_s1 pins_clear_s2 pins_clear_s3 pins_clear_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c hand_back_c answer_code_c pins_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
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
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses (lib/A/Prog/pins_clear_c.v), at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis TANSWER_CODE : forall fx0 : YK11.FPState, @tanswer_code_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's per-binary hypotheses, with the statements' names, shared by every recorder walk; RecBClosed.v discharges
   them with CmdRecFacts *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.

Theorem tpins_clear_holds : tpins_clear_spec B MT.
Proof.
unfold tpins_clear_spec.
intros ly S W regs mem md ch pu u R O PRE HFRM HROD HROOK H10 Hpu HBLK HAP HSTR HLEN HREP HFR HEV HLIVE HMOK.
destruct HREP as (Q & HA & HO).
exact (pcl_entry_seg B MT TRCF VOBJS TL HB MTL SIGP cmd_prog_img cmd_prog_writable
  ly S W regs mem md ch R O Q pu (Some u) _ PRE HROD H10 HA HO HEV HMOK
  (fun lyc Sc Wc memc mdc k c regsJ HJ HAJ Hc Hsp R8 R9 R19 R20 R3 R4 Rhi HFRAME HMLE HBB =>
     pcl_join_seg B MT TXSTRDUP TMIX_CALL TANSWER_CODE VOBJS HB MTL SIGP cmd_prog_img cmd_prog_writable
       RRO RELRO_IMG cmd_ro_prog_apart cmd_ro_ok_of_aro cmd_heap_tail_vis
       ly S W regs mem md ch R O Q pu u lyc Sc Wc memc mdc k c regsJ
       PRE HFRM HROD HROOK H10 Hpu HBLK HAP HSTR HLEN HA HO HFR HEV HLIVE HMOK
       HJ HAJ Hc Hsp R8 R9 R19 R20 R3 R4 Rhi HFRAME HMLE HBB)).
Qed.
Print Assumptions tpins_clear_holds.
End e.
End f.
End d.
Print Assumptions tpins_clear_holds.

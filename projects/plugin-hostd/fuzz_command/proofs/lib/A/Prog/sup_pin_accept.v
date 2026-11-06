(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the assembly of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command) from
   its two halves, after proofs/cgif/cgif_file_fuzzer/lib/A/ACke.v (the instantiation file of a cgif walk). *)

(* sup_pin_accept(uri) (recorder.c:428-434, entry BASE + AF_sup_pin_accept = 0x8bb90, 91 instructions):
   lib/A/Prog/sup_pin_accept_s4.v walks the entry, the inlined record(13) with its two arms and the two
   instrumented checks on the slot, to the point B0 = 0x8bc40, and ends with spa_entry; lib/A/Prog/sup_pin_accept_s2.v
   walks B0 to the tail jump `j answer` (the copy of the argument by xstrdup, the two checks on the slot,
   rec_shape_of of "pin_accept", the frame's release) and composes answer with cl_callS_wide.

   The Section hypotheses beyond the statement's callee contracts are the walk facts with cgif's names
   (TL, HB, MTL, SIGP) and the per-binary facts under the walks' shared names, which the statements
   do not give yet (lib/A/Prog/CmdRecFacts.v is to prove them): cmd_prog_img, cmd_prog_writable,
   cmd_ro_prog_apart, RRO, RELRO_IMG, cmd_ro_ok_of_aro, cmd_heap_tail_vis, and CMD_RO_IN (the premise the
   statement dropped, which the verb literal's read-only arm asks). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib PaCall PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c answer_c sup_pin_accept_c RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_pin_accept_r sup_pin_accept_s1 sup_pin_accept_s3 sup_pin_accept_s2 sup_pin_accept_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

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
(* the statement's callee contracts (sup_pin_accept_c.v:67-71) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names (LAWS is the core's AR_laws_ok) *)
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary facts the statements do not give yet (the walks' shared names and forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S W mem md p n e, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).

(* the contract of lib/A/Prog/sup_pin_accept_c.v *)
Theorem tsup_pin_accept_holds : tsup_pin_accept_spec B MT.
Proof.
unfold tsup_pin_accept_spec.
intros ly S W regs mem md ch pu uri R O HPRE HFRM HROD HROOK H10 Hpu HSTR HREP HFR HEV HLIVE HMOK.
exact (spa_entry B MT TXSTRDUP TANSWER TREC_SHAPE_OF VOBJS HB MTL SIGP cmd_prog_img cmd_prog_writable
  cmd_ro_prog_apart RRO RELRO_IMG cmd_ro_ok_of_aro cmd_heap_tail_vis CMD_RO_IN TRCF TL
  ly S W regs mem md ch pu uri R O HPRE HFRM HROD HROOK H10 Hpu HSTR HREP HFR HEV HLIVE HMOK).
Qed.

End e.
End f.
End d.

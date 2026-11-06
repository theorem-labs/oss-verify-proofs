(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of descriptors_panel_get (plugin-hostd/fuzz_command.asan, 0x8d10c, 91 instructions), assembled from its four segments in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cgif_close's walk composed from the segment statements CL_*_stmtX). *)

(* descriptors_panel_get (recorder.c:554-560): the inlined record(REC_DESCRIPTORS_PANEL_GET) (the slot
   g_rec.calls[n], or record.spill after rec_calls_free), the inlined arg_s (xstrdup of uri, the copy stored in the
   slot), rec_shape_of on "panel_get", and the tail jump into answer. Every instrumented check reads the shadow byte
   at (a >> 3) + 0x7fff8000 of a byte of the slot, which lies in g_rec or record.spill, whose shadow is 0, so the
   error path is not reached. The segments:
   - descriptors_panel_get_s7.v, dpg_entry: the entry, the prologue and both arms of record() to their join;
   - descriptors_panel_get_s4.v, dpg_J_of_X: the join to the call of xstrdup;
   - descriptors_panel_get_s5.v, dpg_X_of_R: xstrdup and arg_s to the call of rec_shape_of;
   - descriptors_panel_get_s8.v, dpg_R_holds: rec_shape_of, the epilogue and the tail jump into answer. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c answer_c descriptors_panel_get_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_s1 descriptors_panel_get_s3 descriptors_panel_get_s4 descriptors_panel_get_s5
descriptors_panel_get_s7 descriptors_panel_get_s8.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (descriptors_panel_get_c.v:67-71) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts the statement does not carry yet, by the recorder walks' shared names *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI).

Theorem tdescriptors_panel_get_holds : tdescriptors_panel_get_spec B MT.
Proof.
assert (HR : dpg_R_stmt B MT) by (apply dpg_R_holds; assumption).
assert (HX : dpg_X_stmt B MT) by (apply dpg_X_of_R; assumption).
assert (HJ : dpg_J_stmt B MT) by (apply dpg_J_of_X; assumption).
assert (HE : forall ly S W regs mem md ch pu x R O, dpg_ctx B MT ly S W regs mem md ch pu x R O ->
  SRr SEGS W (cfg_at SEGS (pa_val A_TEXT + AF_descriptors_panel_get) regs mem md)
    (dpg_post B MT ly S W regs mem md R (Some x) O))
  by (apply dpg_entry; assumption).
intros ly S W regs mem md ch pu uri R O HPRE HFRM HROD HRO H10 Hpu (x & -> & HB0 & HS0 & HL & HF) HREP Hfr Hev Hlive MOK.
pose (CTX := conj HPRE (conj HFRM (conj HROD (conj HRO (conj H10 (conj Hpu (conj HB0 (conj HS0 (conj HL (conj HF
  (conj HREP (conj Hfr (conj Hev (conj Hlive MOK))))))))))))) : dpg_ctx B MT ly S W regs mem md ch pu x R O).
exact (HE ly S W regs mem md ch pu x R O CTX).
Qed.

End e.
End f.
End d.

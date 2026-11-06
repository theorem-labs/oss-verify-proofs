(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to the statements of an earlier revision, then of passes 4, 4b and 5. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_pool_config (plugin-hostd/fuzz_command, 0x8bcfc, 97
   instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v, AChc.v and A/ACke.v (cgif_close's
   segment walk assembled into the contract). *)

(* sup_pool_config (recorder.c:436-443): block P (the inlined record(REC_POOL_CONFIG)), block S (the name, "(null)" when
   NULL, copied by xstrdup), block I (arg_i on max), tail TA (rec_shape_of on "pool_config", then the tail jump to answer
   with changes = 1) of the recorder-call walk template. Three segments: sup_pool_config_w1.v (the entry to the
   point where record()'s two arms meet, 0x8bd78), sup_pool_config_w2.v (that point to the call of xstrdup, 0x8bdb4),
   sup_pool_config_w3.v (that call through arg_i, rec_shape_of and answer to the member's post). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c rec_shape_of_c answer_c hand_back_c mix_call_c sup_pool_config_c PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_pool_config_s1 sup_pool_config_s2 sup_pool_config_s3 sup_pool_config_s4 sup_pool_config_s5
sup_pool_config_d sup_pool_config_w1 sup_pool_config_w2 sup_pool_config_w3.
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
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (sup_pool_config_c.v:70-75), word for word *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's per-binary facts the statement does not give yet, under cgif's names and the recorder walks' shared
   names; each goes when lib/A/Prog/CmdRecFacts.v states it *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG ->
  writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the premise the statement dropped, for the verb literal "pool_config" handed to rec_shape_of (CmdRo.v:434) *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
(* G2 (b): the tail word of the heap string xstrdup copies (xstrdup_c.v:75) *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.

Let HY : spc_hyps B MT :=
  mk_spc_hyps B MT TRCF TXSTRDUP TARG_I TREC_SHAPE_OF TANSWER VOBJS TL HB MTL SIGP cmd_prog_img cmd_prog_writable
    cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart CMD_RO_IN cmd_heap_tail_vis.

(* the walk, segment by segment: the entry .. record()'s join (0x8bd78) .. the call of xstrdup (0x8bdb4) .. arg_i ..
   rec_shape_of .. the tail jump to answer *)
Theorem spc_walk : forall ly S W regs mem md ch pn max name R O,
spc_pre B MT ly S W regs mem md ch pn max name R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_pool_config) regs mem md) (spc_goal B MT ly S W regs mem md R O name max).
Proof.
intros ly S W regs mem md ch pn max name R O HPRE.
exact (spc_seg_entry B MT HY ly S W regs mem md ch pn max name R O HPRE
  (spc_seg_join B MT HY ly S W regs mem md ch pn max name R O HPRE
    (spc_seg_dup B MT HY ly S W regs mem md ch pn max name R O HPRE))).
Qed.

Theorem tsup_pool_config_holds : tsup_pool_config_spec B MT.
Proof.
unfold tsup_pool_config_spec.
intros ly S W regs mem md ch pn max name R O HPRE HFR0 HROD HRO H10 Hpn H11 Hmax HSTR HREP HFR HEV HLIVE HMOK.
exact (spc_walk ly S W regs mem md ch pn max name R O
  (conj HPRE (conj HFR0 (conj HROD (conj HRO (conj H10 (conj Hpn (conj H11 (conj Hmax (conj HSTR (conj HREP
   (conj HFR (conj HEV (conj HLIVE HMOK)))))))))))))).
Qed.

Print Assumptions tsup_pool_config_holds.

End e.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the seed of a mid-walk segment of sup_worker_env's ASan walk
   (plugin-hostd/fuzz_command), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed: a segment's symbolic state
   rebuilt from the machine state at a return point). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c rec_shape_of_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_worker_env_c sup_worker_env_m sup_worker_env_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the frame of a mid segment: [sp, sp + 64) above the current sp, the saved registers at sp + 56 - 8 j (the atoms
   35 + j of swe_extra) *)
Definition swe_frame_chunks : list YP09.chunk :=
map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 8).
Definition swe_stack_mid : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0 swe_frame_chunks.
Definition swe_rs_mid (stk : bool) (cs : list YP09.chunk) : YP09.smem :=
if stk then [swe_stack_mid; swe_slot cs] else [swe_slot cs].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma swe_mid_seed : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) E sp n c pc sregs
(stk : bool) cs,
AR SEGS B ly1 S1 W1 mem1 md1 ->
swe_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> swe_slot_ok c ->
regs_ok E sregs regs1 ->
regions_wf (swe_rs_mid stk cs) = true ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W1) mem1) c) cs ->
(stk = true -> Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W1) mem1) sp) swe_frame_chunks) ->
st_ok_pi SEGS VAL E (mkSS pc sregs (swe_rs_mid stk cs) None swe_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS swe_Bx swe_SH E (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 E sp n c pc sregs stk cs HAR HE Hsp Hsp16 Hn Hc HREG Hwf Hcs Hstk.
pose proof HE as (HEI & E2 & ESB & EN & EC).
destruct (swe_slot_bounds c Hc) as [Hcb Hc8].
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (Bc : base_val E (Some SW_C) = c) by (apply VB; [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia]).
assert (B2 : base_val E (Some 2%nat) = sp) by (apply VB; [exact E2 | lia]).
assert (HSL : YP09.region_ok SEGS E (mrestrict (w_H W1) mem1) (swe_slot cs)).
{ unfold YP09.region_ok, swe_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Bc. split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold CALL_SIZE, A_REC_SPILL in *; lia|].
  split; [|exact Hcs].
  intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR|].
  destruct Hc as [(H1 & H2 & H3) | ->]; [apply recb_grec_in | apply recb_spill_in];
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, CALL_SIZE, OFF_CALLS in *; lia. }
split; [| exact (swe_sh_ok B HB ly1 S1 W1 mem1 md1 E sp n c HAR HE Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- exact Hwf.
- destruct stk; unfold swe_rs_mid; [|apply Forall_cons; [exact HSL | apply Forall_nil]].
  apply Forall_cons; [|apply Forall_cons; [exact HSL | apply Forall_nil]].
  unfold YP09.region_ok, swe_stack_mid. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. exact (Hstk eq_refl).
- apply pairwise_disjoint_of_extents.
  destruct stk; unfold swe_rs_mid, swe_stack_mid, swe_slot, extent_of_region;
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?Bc, ?B2;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  unfold CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *; repeat split; lia.
- exact (swe_facts_ok VOBJS E sp n c HE Hsp Hsp16 Hn Hc).
Qed.


End e.
End f.
End d.

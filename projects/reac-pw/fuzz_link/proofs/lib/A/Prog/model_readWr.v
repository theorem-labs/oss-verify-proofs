(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v; 35 of its 76 lines of code are new or changed and 298 lines of the source are left out. *)
(* model_read on image A: two facts of its walk's tail, beside model_readKit.v: the write set's bytes stay writable
   at a later memory of any world that shows them as a present memory did, and the index index_of answers is one of
   the table's indices or 0.
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs LinkWalkWseg model_readKit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the join of a state at +pc into a given state TGT: the registers CL forgotten to the atoms from k *)
Lemma mr_index_rng : forall tab s,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab s < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros s H; cbn [index_of]; [lia|].
  destruct (bl_eqb n s).
  - exact (H 0%nat n ix eq_refl).
  - apply IH. intros i n' ix' Hi. exact (H (S i) n' ix' Hi).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HSEGS : pa_segs = tfibsegs.

(* a write-set byte writable at a memory m1 of a world W1 is writable at a memory m2 of W2 showing it as m1 did *)
Lemma mr_wr_writable2 : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (W1 : world pa_segs) (m1 : word -> option byte) (W2 : world pa_segs) (m2 : word -> option byte) a,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  inFP (model_read_awr regs (rdW W memc)) a ->
  writable_at pa_segs (rdW W1 m1) a ->
  (~ in_img pa_segs a -> aview pa_segs (w_H W2) m2 a = aview pa_segs (w_H W1) m1 a) ->
  writable_at pa_segs (rdW W2 m2) a.
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W1 m1 W2 m2 a HENT Ha Hw Hv.
destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HENT a Ha)
  as (_ & _ & _ & _ & Ha64).
pose proof HENT as (HPRE & _ & _).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnro).
destruct (classic (in_img pa_segs a)) as [Hi | Hn].
- assert (Hw' : writable_at tfibsegs (rdW W2 m2) a).
  { apply wseg_writable_tfib.
    destruct Hi as (sg & Hin & Hr). exists sg. split; [rewrite <- HSEGS; exact Hin|]. split; [|exact Hr].
    destruct (seg_writable sg) eqn:Ew; [reflexivity|]. exfalso. apply (Hnro a Ha). left.
    exists sg. split; [exact Hin|]. split; [exact Ew | exact Hr]. }
  rewrite <- HSEGS in Hw'. exact Hw'.
- apply apresent_writable. apply (apresent_transfer pa_segs (w_H W1) (w_H W2) m1 m2 a Ha64 Hn (Hv Hn)).
  assert (Hw' : writable_at tfibsegs (rdW W1 m1) a) by (rewrite <- HSEGS; exact Hw).
  assert (Hn' : ~ in_img tfibsegs a) by (rewrite <- HSEGS; exact Hn).
  exact (AE7f.apresent_of_writable (w_H W1) m1 a Ha64 Hn' Hw').
Qed.

End b.
End a.

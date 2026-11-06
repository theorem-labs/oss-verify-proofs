(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: module paths changed to omx-clap-core fuzz_manifest (copied from cgif_file_fuzzer, no other change). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YI09 YI5w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition set_fr_gen (f : frame_st) (v : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) v (fr_delay f) (fr_nlp f) (fr_ctidx f) (fr_disp f) (fr_tidx f).
Definition flush_upd (s : cgif_st) (i : nat) (gen' rwcur' : Z) : cgif_st :=
mkCgif (list_set (cg_frames s) i (option_map (fun f => set_fr_gen f gen') (nth i (cg_frames s) None)))
(cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) (cg_cur s) (cg_ihead s)
(rw_gct s) (rw_attr s) (rw_loops s) rwcur'.
Lemma flush_upd_blocks : forall g s N i gen' rwcur',
(i < length (cg_frames s))%nat ->
cgif_blocks g (flush_upd s i gen' rwcur') N = cgif_blocks g s N.
Proof.
intros g s N i gen' rwcur' Hi. unfold cgif_blocks, flush_upd, pal_blocks, raw_sgct. cbn.
f_equal. f_equal. f_equal.
revert i Hi. generalize (cg_frames s) as l. induction l as [|o l IH]; intros [|i] Hi; cbn in *; try lia.
- destruct o as [f|]; cbn; reflexivity.
- rewrite IH by lia. reflexivity.
Qed.
End a.

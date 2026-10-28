(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 UI21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FLUSH_STK : Z := 1024 + ALLOC_STACK.
Definition set_fr_gen (f : frame_st) (v : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) v (fr_delay f) (fr_nlp f) (fr_ctidx f) (fr_disp f) (fr_tidx f).
Definition flush_upd (s : cgif_st) (i : nat) (gen' rwcur' : Z) : cgif_st :=
mkCgif (list_set (cg_frames s) i (option_map (fun f => set_fr_gen f gen') (nth i (cg_frames s) None)))
(cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) (cg_cur s) (cg_ihead s)
(rw_gct s) (rw_attr s) (rw_loops s) rwcur' (cg_file s).
Section b.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition flush_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (i : nat) (f : frame_st) (rest : list (Z * Z)) (S : list Z),
fn_pre ubs0_msyms MR FLUSH_STK L A regs mem md -> st_init_done A = true ->
sink_at ubs0_msyms mem md (cg_file s) S -> Z.of_nat (length S) + FRAME_OUT N <= SINK_MAX -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g ->
cgif_at mem g s -> cgif_wf s N ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = Z_to_bv 64 (fr_ptr f) ->
getr regs 12 = Z_to_bv 64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_flushFrame) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (r gen' rwcur' : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FLUSH_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem' g (flush_upd s i gen' rwcur') /\ cgif_wf (flush_upd s i gen' rwcur') N /\
Permutation (blocks L' A') (cgif_blocks g s N ++ rest) /\
(exists S', sink_at ubs0_msyms mem' md' (cg_file s) S' /\ Z.of_nat (length S') <= Z.of_nat (length S) + FRAME_OUT N)).
End b.
Lemma flush_upd_blocks : forall g s N i gen' rwcur',
(i < length (cg_frames s))%nat ->
cgif_blocks g (flush_upd s i gen' rwcur') N = cgif_blocks g s N.
Proof using.
intros g s N i gen' rwcur' Hi. unfold cgif_blocks, flush_upd, pal_blocks, raw_sgct. cbn.
f_equal. f_equal. f_equal. f_equal.
revert i Hi. generalize (cg_frames s) as l. induction l as [|o l IH]; intros [|i] Hi; cbn in *; try lia.
- destruct o as [f|]; cbn; reflexivity.
- rewrite IH by lia. reflexivity.
Qed.
End a.

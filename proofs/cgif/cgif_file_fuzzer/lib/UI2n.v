(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c UI21 UI2m UI3u UI22 YI5a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition flushX_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (i : nat) (f : frame_st) (rest : list (Z * Z)) (S : list Z)
(GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame) (b : rbound),
fn_pre ubs0_msyms MR FLUSH_STK L A regs mem md -> st_init_done A = true ->
sink_at ubs0_msyms mem md (cg_file s) S -> Z.of_nat (length S) + FRAME_OUT N <= SINK_MAX -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g ->
cgif_at mem g s -> cgif_wf s N ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = Z_to_bv 64 (fr_ptr f) ->
getr regs 12 = Z_to_bv 64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) ->
frame_rel mem N f cur -> oframe_rel0 mem N (nth (i - 1) (cg_frames s) None) bef ->
rw_attr s = raw_attr_of (cg_attr s) ->
res_ok A b -> flush_room b N ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_flushFrame) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (r rwcur' : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FLUSH_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem' g (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) rwcur') /\
cgif_wf (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) rwcur') N /\
Permutation (blocks L' A') (cgif_blocks g s N ++ rest) /\
(exists code bytes, YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) cur bef = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem' md' (cg_file s) (S ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
res_ok A' (flush_rb b) /\
(forall a n k, In (a, n) (blocks L A) -> (a, n) <> (cg_file s, FILE_BLOCK) -> 0 <= k < n ->
~ (a = cg_raw s /\ 40 <= k < 44) -> ~ (a = fr_ptr f /\ 20 <= k < 24) ->
mbyte ubs0segs mem' (a + k) = mbyte ubs0segs mem (a + k))).
End d.
End c.

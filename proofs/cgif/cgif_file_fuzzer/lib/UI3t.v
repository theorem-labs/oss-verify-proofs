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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RAWADD_STK : Z := 512 + ALLOC_STACK.
Section b.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition rawadd_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md
(raw g cfp : Z) (gvals : list Z) (gct rattr W H sgct loops rcur : Z)
(lct img fattr w h top left delay slct disp tidx : Z) (Nimg : Z) (rest : list (Z * Z)) (f : Z) (S : list Z),
fn_pre ubs0_msyms MR RAWADD_STK L A regs mem md -> st_init_done A = true ->
In (f, FILE_BLOCK) rest -> sink_at ubs0_msyms mem md f S -> Z.of_nat (length S) + (2 * (w * h) + 2048) <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 raw -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + 40 <= 2 ^ 63 ->
obj_at ubs0segs mem cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at ubs0segs mem raw LAY_Raw [ubs0_A_cgif_writecb; g; gct; rattr; W; H; sgct; loops; rcur] ->
sgct <= 256 ->
obj_at ubs0segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
1 <= w -> 1 <= h -> w * h <= 100000000 ->
w * h <= Nimg ->
Permutation (blocks L A) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
(0 < slct <= 256 -> exists Nl, In (lct, Nl) rest /\ 3 * slct <= Nl) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_addframe) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWADD_STK (spZ regs) ((raw + 40, raw + 44) :: sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem' raw LAY_Raw [ubs0_A_cgif_writecb; g; gct; rattr; W; H; sgct; loops; rcur'] /\
Permutation (blocks L' A') (blocks L A) /\
(exists S', sink_at ubs0_msyms mem' md' f S' /\ Z.of_nat (length S') <= Z.of_nat (length S) + (2 * (w * h) + 2048))).
End b.
End a.

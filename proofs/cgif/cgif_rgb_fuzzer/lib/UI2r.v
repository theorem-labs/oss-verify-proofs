(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RAWADD_STK : Z := 512 + ALLOC_STACK.
Section b.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition rawadd_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md
(raw g cfp : Z) (gvals : list Z) (gct rattr W H sgct loops rcur : Z)
(lct img fattr w h top left delay slct disp tidx : Z) (Nimg : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR RAWADD_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 raw -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + 40 <= 2 ^ 63 ->
obj_at ubs2segs mem cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at ubs2segs mem raw LAY_Raw [ubs2_A_cgif_writecb; g; gct; rattr; W; H; sgct; loops; rcur] ->
sgct <= 256 ->
obj_at ubs2segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some ubs2_A_writecb -> nth_error gvals CG_file = Some 0 ->
1 <= w -> 1 <= h -> w * h <= 100000000 ->
w * h <= Nimg ->
Permutation (blocks L A) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
(0 < slct <= 256 -> exists Nl, In (lct, Nl) rest /\ 3 * slct <= Nl) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_raw_addframe) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR RAWADD_STK (spZ regs) [(raw + 40, raw + 44)] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs2segs mem' raw LAY_Raw [ubs2_A_cgif_writecb; g; gct; rattr; W; H; sgct; loops; rcur'] /\
Permutation (blocks L' A') (blocks L A)).
End b.
End a.

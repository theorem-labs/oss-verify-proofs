(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 UI1i YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FREECHT_STK : Z := 16 + ALLOC_STACK.
Definition RGBCLOSE_STK : Z := 32 + CLOSE_STK.
Definition RGBNEWGIF_STK : Z := 80 + NEWGIF_STK.
Definition RGB_GIFATTR : Z := 6.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition free_cht_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (c : Z) (f h u p x cnt ts : Z) (nf nh nu np nx : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR FREECHT_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 c ->
obj_at ubs2segs mem c LAY_Cht [f; h; u; p; x; cnt; ts] ->
Permutation (blocks L A) ((c, CHT_SIZE) :: optb f nf ++ optb h nh ++ optb u nu ++ optb p np ++ optb x nx ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_free_col_hash_table) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR FREECHT_STK (spZ regs)
((c, c + CHT_SIZE) :: optfp f nf ++ optfp h nh ++ optfp u nu ++ optfp p np ++ optfp x nx)
L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Definition rgb_close_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (r : Z) (rv : list Z) (g : Z) (s : cgif_st) (N bef nbef : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR RGBCLOSE_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 r ->
obj_at ubs2segs mem r LAY_Rgb rv -> nth_error rv RG_gif = Some g -> nth_error rv RG_bef = Some bef ->
cgif_at mem g s -> cgif_wf s N ->
Permutation (blocks L A) ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef nbef ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_close) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR RGBCLOSE_STK (spZ regs)
((r, r + RGB_SIZE) :: blocks_fp (cgif_blocks g s N) ++ optfp bef nbef)
L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Definition rgb_newgif_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (cfgp attr gen loops W H : Z),
fn_pre ubs2_msyms MR RGBNEWGIF_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + RGBCONFIG_SIZE <= 2 ^ 63 ->
obj_at ubs2segs mem cfgp LAY_RgbConfig [ubs2_A_writecb; 0; 0; attr; gen; loops; W; H] ->
(forall i, 0 <= i < RGBCONFIG_SIZE -> exists b, mbyte ubs2segs mem (cfgp + i) = Some b) ->
W * H <= 100000000 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_newgif) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR RGBNEWGIF_STK (spZ regs) [] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ exists leak, Permutation (blocks L' A') (leak ++ blocks L A)) \/
(res <> 0 /\ res mod 16 = 0 /\ exists g s,
obj_at ubs2segs mem' res LAY_Rgb [g; ubs2_A_writecb; 0; 0; attr; gen; loops; W; H; 0; 0; R_PENDING] /\
cgif_at mem' g s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = RGB_GIFATTR /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (blocks L' A') ((res, RGB_SIZE) :: cgif_blocks g s (W * H) ++ blocks L A)))).
End d.
End a.

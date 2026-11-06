(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCdy YCe9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Definition taddframe_specG : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)),
afn_pre trbsegs B TADDFRAME_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_cgif_addframe -> Z.of_nat (length (frames S)) <= 7 ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
getr regs 10 = w64 g -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp 32 ->
obj_at trbsegs (mrestrict (w_H W) mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
(Z.land fattr 1 <> 0 -> afobj B ly S W mem lpal (3 * nlp)) ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (img, N) :: rest) ->
vev S + EV_ADDFRAME <= VEV_MAX -> blocks_bytes S + LIVE_ADDFRAME <= LIVE_MAX ->
SRr trbsegs W (cfg_at trbsegs A_cgif_addframe regs mem md)
(apost_base B TADDFRAME_STK (ablocks_fp (cgif_blocks g s N)) regs ly S W mem md EV_ADDFRAME
(fun ly' S' W' regs' mem' md' => exists s' : cgif_st,
tcgif_at (mrestrict (w_H W') mem') g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (ablocks B ly' S') (cgif_blocks g s' N ++ (img, N) :: rest) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) blc ly' [] (fst b + i)))).
End c.
End a.

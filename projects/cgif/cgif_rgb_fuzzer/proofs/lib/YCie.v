(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCdy YCe9 YCi1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition TRGBNEWGIF_STK : Z := 96 + TNEWGIF_STK.
Definition EV_RGBNEWGIF : Z := EV_NEWGIF + 2.
Definition LIVE_RGBNEWGIF : Z := LIVE_NEWGIF + 64.
Definition TRGB_GIFATTR : Z := 6.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Definition trgb_newgif_post (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world trbsegs) (mem : word -> option byte) (md : Model)
(attr gen loops Wd Hd : Z) : world trbsegs -> config -> Prop :=
apost_base B TRGBNEWGIF_STK [] regs ly S W mem md EV_RGBNEWGIF
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ exists g s,
obj_at trbsegs (mrestrict (w_H W') mem') res LAY_Rgb [g; A_writecb; 0; 0; attr; gen; loops; Wd; Hd; 0; 0; R_PENDING] /\
tcgif_at (mrestrict (w_H W') mem') g s /\ cgif_wf s (Wd * Hd) /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = TRGB_GIFATTR /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (ablocks B ly' S') ((res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd) ++ ablocks B ly S) /\
(forall b, In b ((res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd)) ->
aftok [] (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TRGBNEWGIF_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (fst b + i))))).
Definition trgb_newgif_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp attr gen loops Wd Hd : Z),
afn_pre trbsegs B TRGBNEWGIF_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX_cgif_rgb_newgif -> Z.of_nat (length (frames S)) <= 6 -> spZ regs + 32 <= ly_top ly ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp RGBCONFIG_SIZE ->
obj_at trbsegs (mrestrict (w_H W) mem) cfgp LAY_RgbConfig [A_writecb; 0; 0; attr; gen; loops; Wd; Hd] ->
Wd * Hd <= 100000000 ->
vev S + EV_RGBNEWGIF <= VEV_MAX -> blocks_bytes S + LIVE_RGBNEWGIF <= LIVE_MAX ->
SRr trbsegs W (cfg_at trbsegs A_cgif_rgb_newgif regs mem md)
(trgb_newgif_post regs ly S W mem md attr gen loops Wd Hd).
End c.
End a.

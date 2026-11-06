(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c YM01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC10 YC1b YC4u
YC59 YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition TRGBADD_FRAME : Z := 512.
Definition TRGBADD_STK : Z := TRGBADD_FRAME + FDT_STK TREE_HMAX.
Definition EV_RGBADD : Z := 1200 + EV_ADDFRAME.
Definition LIVE_RGBADD : Z := 2 ^ 31 + 2 ^ 30.

Definition tfmt_okb (fmt : Z) : bool := (fmt =? 3) || (fmt =? 4).
Definition timg_block (img fmt N : Z) : list (Z * Z) := if tfmt_okb fmt then [(img, fmt * N)] else [].
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition apost_baseF (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world trasegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world trasegs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom trasegs)) md' /\ frm_zero (@fp_csr fx') /\
ajournal trasegs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
Section c.
Variable B : asyms.
Definition trgb_own (r g : Z) (s : cgif_st) (N bef beffmt : Z) : list (Z * Z) :=
(r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N).
Definition trgb_addframe_post (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world trasegs) (mem : word -> option byte) (md : Model)
(r g wfn ctx path attr gen loops Wd Hd bef beffmt : Z) (s : cgif_st) (N img fmt : Z) (rest : list (Z * Z))
: world trasegs -> config -> Prop :=
apost_baseF B TRGBADD_STK (ablocks_fp (trgb_own r g s N bef beffmt)) regs ly S W mem md EV_RGBADD
(fun ly' S' W' regs' mem' md' => exists (s' : cgif_st) (bef' beffmt' cur' : Z),
obj_at trasegs (mrestrict (w_H W') mem') r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef'; beffmt'; cur'] /\
tcgif_at (mrestrict (w_H W') mem') g s' /\ cgif_wf s' N /\
cg_W s' = Wd /\ cg_H s' = Hd /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (ablocks B ly' S') (trgb_own r g s' N bef' beffmt' ++ timg_block img fmt N ++ rest) /\
(forall b, In b (trgb_own r g s' N bef' beffmt') ->
aftok (ablocks_fp (trgb_own r g s N bef beffmt)) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) (ablocks B ly S) blc ly' [] (fst b + i))).
Definition trgb_addframe_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch
(r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur : Z) (s : cgif_st) (N : Z)
(img fmt fattr fgen delay : Z) (rest : list (Z * Z)),
afn_pre trasegs B TRGBADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX_cgif_rgb_addframe -> Z.of_nat (length (frames S)) <= 6 -> spZ regs + 32 <= ly_top ly ->
arodata_ok B (aview trasegs (w_H W) mem) ->
frm_zero fp_csr ->
getr regs 10 = w64 r -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp RGBFC_SIZE ->
obj_at trasegs (mrestrict (w_H W) mem) cfp LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] ->
obj_at trasegs (mrestrict (w_H W) mem) r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef; beffmt; cur] ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N -> cg_W s = Wd -> cg_H s = Hd -> N <= RGB_NMAX ->
(bef = 0 \/ beffmt = 3 \/ beffmt = 4) ->
Permutation (ablocks B ly S) (trgb_own r g s N bef beffmt ++ timg_block img fmt N ++ rest) ->
vev S + EV_RGBADD <= VEV_MAX -> blocks_bytes S + LIVE_RGBADD <= LIVE_MAX ->
SRr trasegs W (cfg_at trasegs A_cgif_rgb_addframe regs mem md)
(trgb_addframe_post regs ly S W mem md r g wfn ctx path attr gen loops Wd Hd bef beffmt s N img fmt rest).
End c.
End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0f YC04 YC07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP15 YC6e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y YC6z YC70 YC71 YC72 YC7a YC73 YC74 YC7b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BR := (at_BR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_PA := (at_PA B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation FRAMEF := (hk_frame_facts B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK Hsp32).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation at_M1C := (at_M1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RT := (at_RT B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HSTEP := (hcore_raw_step B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation OTHERK := (hk_tbl_other_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M1R := (at_M1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2C := (at_M2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2R := (at_M2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRRS := (hcore_raw_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation APARTN := (hk_tbl_apart_nth B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Local Notation at_RA1C := (at_RA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA1R := (at_RA1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA2C := (at_RA2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RA2R := (at_RA2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA1C := (at_MA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA1R := (at_MA1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA2C := (at_MA2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA2R := (at_MA2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA3C := (at_MA3C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MA3R := (at_MA3R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FAIL := (at_FAIL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_MSC := (at_MSC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rh_pre := (rh_pre B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rz_common := (rz_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rcore := (rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rz_old := (rz_old).
Local Notation hspill := (hspill s1v).
Local Notation slot_is := (slot_is s1v).
Local Notation rh_slots := (rh_slots s1v).
Local Notation at_MSR := (at_MSR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_LH := (at_LH B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rh_common := (rh_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Local Notation cfgat regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs)) md).
Hypothesis TL : TraLib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640.
Variable ch0 : list (Z * Z * Z).
Hypothesis HSTKA : 512 + ASTACK <= STK.
Hypothesis Htop32 : sp0 + 32 <= ly_top ly.
Hypothesis HCH0 : achain ly (aview trasegs (w_H W0) mem0) sp0 s0v ch0.
Hypothesis Hrav : rav = 0x81368.
Hypothesis Hspine : spine ch0 = [] \/ spine ch0 = [0x80ea8].
Hypothesis HEV : vev S + 80 <= VEV_MAX.
Hypothesis HLIVE : bsum PROT + 2 ^ 30 <= LIVE_MAX.
Local Notation hk_ch := (hk_ch sp0 rav s0v ch0).
Local Notation at_LN := (at_LN B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_CHC := (at_CHC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM1C := (at_RM1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM1R := (at_RM1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM2C := (at_RM2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RM2R := (at_RM2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_CHR := (at_CHR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Hypothesis TCOLHASH : tcolhash_spec B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Local Notation at_DONE := (at_DONE B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_F1C := (at_F1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation rf_common := (rf_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_F1R := (at_F1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_F2C := (at_F2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_F2R := (at_F2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_F3C := (at_F3C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_F3R := (at_F3R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_TL := (at_TL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation xf_common := (xf_common B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FF1C := (at_FF1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FF1R := (at_FF1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FF2C := (at_FF2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FF2R := (at_FF2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FF3C := (at_FF3C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_FF3R := (at_FF3R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_XF := (at_XF B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Lemma rh_BL_nth_3 : forall C p1 x1 h1 u1 f1,
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 0 = Some (tb, CHT_SIZE) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 1 = Some (ac_f C, 4 * ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 2 = Some (ac_h C, 3 * ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 3 = Some (ac_u C, ac_T C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 4 = Some (p1, 3 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 5 = Some (x1, 4 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 6 = Some (h1, 3 * ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 7 = Some (u1, ac_Tn C) /\
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) 8 = Some (f1, 4 * ac_Tn C).
Proof. intros; eapply rh_BL_nth; eassumption. Qed.
Lemma rh_apart_3 : forall lyc Sc W regs mem md k cells C p1 x1 h1 u1 f1 (p q : nat) x y,
rcore lyc Sc W regs mem md k cells (rh_BL C p1 x1 h1 u1 f1) ->
nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) p = Some x -> nth_error ((tb, CHT_SIZE) :: rh_BL C p1 x1 h1 u1 f1) q = Some y -> p <> q ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof. intros; eapply rh_apart; eassumption. Qed.

Lemma rh_pre_step_3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt cnt' regs' mem' md',
rh_pre lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 cnt ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (alloc_ceiling <= a < s1v) -> ~ (tb <= a < tb + 48) -> ~ rh_innew C p1 x1 h1 u1 f1 a ->
aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
obj_at trasegs (mrestrict (w_H W) mem') tb LAY_Cht (rh_cells C p1 x1 cnt') ->
rh_pre lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 cnt'.
Proof. intros; eapply rh_pre_step; eassumption. Qed.

Lemma rh_new_kept_3 : forall (W : world trasegs) (mem mem' : word -> option byte) C p1 x1 h1 u1 f1 K,
rh_new W mem C p1 x1 h1 u1 f1 K -> 0 <= ac_Tn C ->
rg_blk_kept (w_H W) (w_H W) mem mem' p1 (req_size (3 * ac_Tn C)) -> rg_blk_kept (w_H W) (w_H W) mem mem' x1 (req_size (4 * ac_Tn C)) ->
rg_blk_kept (w_H W) (w_H W) mem mem' h1 (req_size (3 * ac_Tn C)) -> rg_blk_kept (w_H W) (w_H W) mem mem' u1 (req_size (ac_Tn C)) ->
rg_blk_kept (w_H W) (w_H W) mem mem' f1 (req_size (4 * ac_Tn C)) ->
rh_new W mem' C p1 x1 h1 u1 f1 K.
Proof. intros; eapply rh_new_kept; eassumption. Qed.
Lemma rh_common_run_same_3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K regs' mem' md',
rh_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r HK_CONST -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
rh_common lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 K.
Proof. intros; eapply rh_common_run_same; eassumption. Qed.
Lemma saved_used : acallee_saved 20 /\ acallee_saved 21 /\ acallee_saved 22 /\ acallee_saved 24 /\ acallee_saved 26 /\ acallee_saved 27 /\ acallee_saved 23.
Proof. intros; eapply saved_used; eassumption. Qed.
Lemma saved_26 : acallee_saved 26.
Proof. unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate. Qed.
Lemma saved_20_24 : acallee_saved 20 /\ acallee_saved 24.
Proof. split; unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate. Qed.
Lemma xf_common_run_same : forall lyc Sc W regs mem md k C i ha p1 x1 BL d regs' mem' md',
xf_common lyc Sc W regs mem md k C i ha p1 x1 BL d ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r (HK_CONST ++ [20; 24; 26]%bv) -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha ->
xf_common lyc Sc W regs' mem' md' k C i ha p1 x1 BL d.
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 BL d regs' mem' md' (HC & HF & Hk & _ & Hok1 & Hok2 & G20 & G24 & G26x) HJ' Hregs KM Hsp.
pose proof HC as (HJ & _ & _ & Hobj & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
split.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := xf_cells C p1 x1); try eassumption.
- intros r Hr. apply Hregs. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ _. exact (KM a Ha H1).
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem' tb LAY_Cht _ 48 Hobj lay_inside_Cht). intros t Ht.
assert (Hin' : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md tb CHT_SIZE HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3). change (req_size CHT_SIZE) with 48 in Hb1.
apply KM; [clear - Ht Hb0 Hb1 F47; lia | intros [Hx _]; clear - Hx Ht Hb1; lia]. }
split; [exact HF|]. split; [exact Hk|]. split; [exact Hsp|]. split; [exact Hok1|]. split; [exact Hok2|].
rewrite (Hregs 20%bv ltac:(cbv; clear; tauto)), (Hregs 24%bv ltac:(cbv; clear; tauto)), (Hregs 26%bv ltac:(cbv; clear; tauto)). split; [exact G20|]. split; [exact G24 | exact G26x].
Qed.
Lemma xf_free_opt : forall lyc Sc W regs mem md k C i ha p1 x1 (rest : list (Z * Z)) d v n ret,
xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb v n ++ rest) d ->
rz_ok1 v -> getr regs 10 = Z_to_bv 64 v -> getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 -> 0 <= d <= 2 ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs hk_ch) (as_universe B) ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 ret mem2 md2 /\
xf_common ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 (rz_BL C p1 x1 ++ rest) (d + 1) /\
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a)).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 rest d v n ret HP Hok G10 Gra Hret Hret2 Hd Htr.
pose proof HP as (HC & HF & Hk & [SP72 SP56] & Hok1 & Hok2 & G20 & G24 & G26x).
pose proof (ts_rank_range (ac_T C)) as Hrk.
assert (TR : forall ly2 S2 W2 regs2 mem2 md2 BL2, rcore ly2 S2 W2 regs2 mem2 md2 (k + 1) (xf_cells C p1 x1) BL2 -> aregs_preserved regs regs2 ->
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) mem a) ->
xf_common ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 BL2 (d + 1)).
{ intros ly2 S2 W2 regs2 mem2 md2 BL2 HC2 HP2 Hfr. destruct saved_20_24 as [Sv20 Sv24].
split; [exact HC2|]. split; [exact HF|]. split; [clear - Hk; lia|].
split; [split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia]|].
split; [exact Hok1|]. split; [exact Hok2|]. rewrite (aregs_get regs regs2 20%bv HP2 Sv20), (aregs_get regs regs2 24%bv HP2 Sv24), (aregs_get regs regs2 26%bv HP2 saved_26). split; [exact G20|]. split; [exact G24 | exact G26x]. }
destruct Hok as [-> | Hnz].
- change (optb 0 n) with (@nil (Z * Z)) in HC. cbn [app] in HC.
eapply SRr_mono.
{ eapply rz_free_null with (ret := ret) (BL := rz_BL C p1 x1 ++ rest) (ch0 := ch0); try eassumption;
first [ (clear - Hk Hrk Hd; lia) | (destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) ]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HC2 & HP2 & Hfr & _).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact (TR _ _ _ _ _ _ _ HC2 HP2 Hfr) | exact Hfr].
- assert (Eo : optb v n = [(v, n)]) by (unfold optb; destruct (Z.eqb_spec v 0) as [X | _]; [exfalso; clear - X Hnz; lia | reflexivity]).
rewrite Eo in HC. cbn [app] in HC.
eapply SRr_mono.
{ eapply rz_free with (q := 5%nat) (pa := v) (n := n) (ret := ret) (BL := rz_BL C p1 x1 ++ (v, n) :: rest) (ch0 := ch0); try eassumption;
first [ reflexivity | (clear - Hk Hrk Hd; lia) | (destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) ]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HC2 & HP2 & Hfr & _).
change (ldel (rz_BL C p1 x1 ++ (v, n) :: rest) 5) with (rz_BL C p1 x1 ++ rest) in HC2.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact (TR _ _ _ _ _ _ _ HC2 HP2 Hfr) | exact Hfr].
Qed.
Lemma hl_ff1 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_FF1C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_FF1R mem2 md2 /\ at_FF1R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HP & Hok3 & Hok4 & Hok5 & S296 & S168 & G10 & Gra).
idtac.
eapply SRr_mono.
{ apply (xf_free_opt lyc Sc W regs mem md k C i ha p1 x1 (optb u1 (ac_Tn C) ++ optb f1 (4 * ac_Tn C)) 0 h1 (3 * ac_Tn C) HL_FF1R HP Hok3 G10 Gra); [unfold HL_FF1R; clear; lia | reflexivity | clear; lia |].
rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_FF1R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_FF1R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2 & Hfr). exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [exact HP2|]. split; [exact Hok4|]. split; [exact Hok5|]. split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia].
Qed.
Lemma hl_ff2 : forall lyc Sc W regs mem md k C i ha p1 x1 u1 f1,
at_FF2C lyc Sc W regs mem md k C i ha p1 x1 u1 f1 ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_FF2R mem2 md2 /\ at_FF2R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 u1 f1 ((HP & Hok4 & Hok5 & S296 & S168) & G10 & Gra).
idtac.
eapply SRr_mono.
{ apply (xf_free_opt lyc Sc W regs mem md k C i ha p1 x1 (optb f1 (4 * ac_Tn C)) 1 u1 (ac_Tn C) HL_FF2R HP Hok4 G10 Gra); [unfold HL_FF2R; clear; lia | reflexivity | clear; lia |].
rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_FF2R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_FF2R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2 & Hfr). exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [exact HP2|]. split; [exact Hok5|]. eapply slot_kept with (W := W) (mem := mem); try eassumption; lia.
Qed.
Lemma hl_ff3 : forall lyc Sc W regs mem md k C i ha p1 x1 f1,
at_FF3C lyc Sc W regs mem md k C i ha p1 x1 f1 ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_FF3R mem2 md2 /\ at_FF3R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 f1 ((HP0 & Hok5 & S168) & G10 & Gra).
assert (HP : xf_common lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb f1 (4 * ac_Tn C) ++ []) 2) by (rewrite app_nil_r; exact HP0).
eapply SRr_mono.
{ apply (xf_free_opt lyc Sc W regs mem md k C i ha p1 x1 [] 2 f1 (4 * ac_Tn C) HL_FF3R HP Hok5 G10 Gra); [unfold HL_FF3R; clear; lia | reflexivity | clear; lia |].
rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_FF3R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_FF3R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2 & Hfr). exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
rewrite app_nil_r in HP2. exact HP2.
Qed.
Lemma hl_ff1r : forall lyc Sc W regs mem md k C i ha p1 x1 u1 f1,
at_FF1R lyc Sc W regs mem md k C i ha p1 x1 u1 f1 ->
SRr trasegs W (cfgat regs HL_FF1R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF2C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 u1 f1 (HCm & Hok4 & Hok5 & S296 & S168).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & HF & Hk & [SP72 SP56] & Hok1 & Hok2 & G20 & G24 & G26x).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells xf_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (rsel (ac_p C) p1) (rsel (ac_x C) x1) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; u1; f1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 u1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FF1R false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 168 (SOff 55 0)] [ck 296 (SOff 54 0)] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (rsel (ac_p C) p1) (rsel (ac_x C) x1) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 Rf1), Z.add_0_r; reflexivity | exact Rf1 | lia | exact S168]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 54 u1 0 E54 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 56 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 56 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 56 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 24; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 56 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 56 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 56 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 56 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : xf_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 (rz_BL C p1 x1 ++ optb u1 (ac_Tn C) ++ optb f1 (4 * ac_Tn C)) 1) end.
{ apply (xf_common_run_same lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb u1 (ac_Tn C) ++ optb f1 (4 * ac_Tn C)) 1 _ _ _ HCm HJ); [intros r Hr; apply HKR; exact Hr | exact KM1 | split; [exact SP72' | exact SP56']]. }
split; [split; [exact HP'|]; split; [exact Hok4|]; split; [exact Hok5|]; split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 54 0)] 296 (SOff 54 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 u1 0 E54 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1] | apply (SLOT 4%nat 160 184 [ck 168 (SOff 55 0)] 168 (SOff 55 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 55 f1 0 E55 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]]|].
split; [apply (RD 10%bv (SOff 54 0) u1 eq_refl); [rewrite (denot_off E 54 u1 0 E54 Ru1), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_FF2R) HL_FF2R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_ff2r : forall lyc Sc W regs mem md k C i ha p1 x1 f1,
at_FF2R lyc Sc W regs mem md k C i ha p1 x1 f1 ->
SRr trasegs W (cfgat regs HL_FF2R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF3C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 f1 (HCm & Hok5 & S168).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & HF & Hk & [SP72 SP56] & Hok1 & Hok2 & G20 & G24 & G26x).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells xf_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (rsel (ac_p C) p1) (rsel (ac_x C) x1) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FF2R false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 168 (SOff 54 0)] [] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (rsel (ac_p C) p1) (rsel (ac_x C) x1) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | exact Rf1 | lia | exact S168]. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 24; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 55 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : xf_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 (rz_BL C p1 x1 ++ optb f1 (4 * ac_Tn C)) 2) end.
{ apply (xf_common_run_same lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1 ++ optb f1 (4 * ac_Tn C)) 2 _ _ _ HCm HJ); [intros r Hr; apply HKR; exact Hr | exact KM1 | split; [exact SP72' | exact SP56']]. }
split; [split; [exact HP'|]; split; [exact Hok5|]; apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
split; [apply (RD 10%bv (SOff 54 0) f1 eq_refl); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_FF3R) HL_FF3R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_ff3r : forall lyc Sc W regs mem md k C i ha p1 x1,
at_FF3R lyc Sc W regs mem md k C i ha p1 x1 ->
SRr trasegs W (cfgat regs HL_FF3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_XF mem2 md2 /\ at_XF lyc Sc W regs2 mem2 md2 k C i ha p1 x1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 HCm.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & HF & Hk & [SP72 SP56] & Hok1 & Hok2 & G20 & G24 & G26x).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells xf_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (rsel (ac_p C) p1) (rsel (ac_x C) x1) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FF3R false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (rsel (ac_p C) p1) (rsel (ac_x C) x1) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_XF.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 24; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 54 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : xf_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 (rz_BL C p1 x1) 3) end.
{ apply (xf_common_run_same lyc Sc W regs mem md k C i ha p1 x1 (rz_BL C p1 x1) 3 _ _ _ HCm HJ); [intros r Hr; apply HKR; exact Hr | exact KM1 | split; [exact SP72' | exact SP56']]. }
split; [exact HP'|]. apply (RD 27%bv (SOff 41 0) hv27 eq_refl); [rewrite (denot_off E 41 hv27 0 (HV 9%nat _ eq_refl) O27), Z.add_0_r; reflexivity | reflexivity].
Qed.
Lemma hl_fail_nz_nz : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_FAIL lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 <> 0) ->
SRr trasegs W (cfgat regs HL_FAIL mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S296 & S168 & Hsome) (HcP & HcX).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FAIL true [(21%bv, SOff 32 24)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_NE (SOff 27 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G21. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | exact Rf1 | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact HcP|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact HcX|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [23; 27; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
set (cnt := ht_cnt (ac_H C)) in *.
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 (ac_T C)) by exact (HV 7%nat _ eq_refl).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb;
assert (DA : forall n z, (n < 57)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 23 0) p1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 23%nat _ ltac:(lia) E23 Rp1) Rp1 ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 27 0) x1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 27%nat _ ltac:(lia) E27 Rx1) Rx1 ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) cnt HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) (ac_T C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (EP : rsel (ac_p C) p1 = p1) by (unfold rsel; destruct (Z.eqb_spec p1 0) as [X | _]; [exfalso; exact (HcP X) | reflexivity]).
assert (EX : rsel (ac_x C) x1 = x1) by (unfold rsel; destruct (Z.eqb_spec x1 0) as [X | _]; [exfalso; exact (HcX X) | reflexivity]).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (xf_cells C p1 x1) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := ac_cells C); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx].
- unfold xf_cells. rewrite EP, EX. cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Rp1]|]. split; [split; [exact Vx' | exact Rx1]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
rewrite <- !app_assoc in HC'.
split; [split; [exact HC'|]; split; [exact HF|]; split; [clear - Hk; lia|]; split; [split; [exact SP72' | exact SP56']|]; split; [exact Hok1|]; split; [exact Hok2|]; split; [|split]|].
- apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 24%bv (SOff 50 0) hv24 eq_refl); [rewrite (denot_off E 50 hv24 0 (HV 18%nat _ eq_refl) O24), Z.add_0_r; reflexivity | reflexivity].
- rewrite (HKR 26%bv ltac:(cbv; clear; tauto)). exact G26.
- split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
split; [apply (RD 10%bv (SOff 55 0) h1 eq_refl); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_FF1R) HL_FF1R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_fail_nz_z : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_FAIL lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 <> 0 /\ x1 = 0) ->
SRr trasegs W (cfgat regs HL_FAIL mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S296 & S168 & Hsome) (HcP & HcX).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FAIL true [(21%bv, SOff 32 24)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_NE (SOff 23 0) (SLit 0); mkAC BC_EQ (SOff 27 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G21. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | exact Rf1 | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact HcP|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Z.eqb_eq; exact HcX|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [23; 27; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
set (cnt := ht_cnt (ac_H C)) in *.
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 (ac_T C)) by exact (HV 7%nat _ eq_refl).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb;
assert (DA : forall n z, (n < 57)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 23 0) p1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 23%nat _ ltac:(lia) E23 Rp1) Rp1 ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 37 0) (ac_x C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 37%nat _ ltac:(lia) E37 Bx) Bx ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) cnt HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) (ac_T C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (EP : rsel (ac_p C) p1 = p1) by (unfold rsel; destruct (Z.eqb_spec p1 0) as [X | _]; [exfalso; exact (HcP X) | reflexivity]).
assert (EX : rsel (ac_x C) x1 = ac_x C) by (unfold rsel; rewrite HcX; reflexivity).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (xf_cells C p1 x1) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := ac_cells C); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx].
- unfold xf_cells. rewrite EP, EX. cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Rp1]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
rewrite <- !app_assoc in HC'.
split; [split; [exact HC'|]; split; [exact HF|]; split; [clear - Hk; lia|]; split; [split; [exact SP72' | exact SP56']|]; split; [exact Hok1|]; split; [exact Hok2|]; split; [|split]|].
- apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 24%bv (SOff 50 0) hv24 eq_refl); [rewrite (denot_off E 50 hv24 0 (HV 18%nat _ eq_refl) O24), Z.add_0_r; reflexivity | reflexivity].
- rewrite (HKR 26%bv ltac:(cbv; clear; tauto)). exact G26.
- split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
split; [apply (RD 10%bv (SOff 55 0) h1 eq_refl); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_FF1R) HL_FF1R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_fail_z_nz : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_FAIL lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 = 0 /\ x1 <> 0) ->
SRr trasegs W (cfgat regs HL_FAIL mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S296 & S168 & Hsome) (HcP & HcX).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FAIL true [(21%bv, SOff 32 24)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_EQ (SOff 23 0) (SLit 0); mkAC BC_NE (SOff 27 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G21. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | exact Rf1 | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Z.eqb_eq; exact HcP|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; exact HcX|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [23; 27; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
set (cnt := ht_cnt (ac_H C)) in *.
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 (ac_T C)) by exact (HV 7%nat _ eq_refl).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb;
assert (DA : forall n z, (n < 57)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 36 0) (ac_p C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 36%nat _ ltac:(lia) E36 Bp) Bp ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 27 0) x1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 27%nat _ ltac:(lia) E27 Rx1) Rx1 ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) cnt HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) (ac_T C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (EP : rsel (ac_p C) p1 = ac_p C) by (unfold rsel; rewrite HcP; reflexivity).
assert (EX : rsel (ac_x C) x1 = x1) by (unfold rsel; destruct (Z.eqb_spec x1 0) as [X | _]; [exfalso; exact (HcX X) | reflexivity]).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (xf_cells C p1 x1) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := ac_cells C); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx].
- unfold xf_cells. rewrite EP, EX. cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Rx1]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
rewrite <- !app_assoc in HC'.
split; [split; [exact HC'|]; split; [exact HF|]; split; [clear - Hk; lia|]; split; [split; [exact SP72' | exact SP56']|]; split; [exact Hok1|]; split; [exact Hok2|]; split; [|split]|].
- apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 24%bv (SOff 50 0) hv24 eq_refl); [rewrite (denot_off E 50 hv24 0 (HV 18%nat _ eq_refl) O24), Z.add_0_r; reflexivity | reflexivity].
- rewrite (HKR 26%bv ltac:(cbv; clear; tauto)). exact G26.
- split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
split; [apply (RD 10%bv (SOff 55 0) h1 eq_refl); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_FF1R) HL_FF1R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_fail_z_z : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_FAIL lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 -> (p1 = 0 /\ x1 = 0) ->
SRr trasegs W (cfgat regs HL_FAIL mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 (HCm & Hres & Hok3 & Hok4 & Hok5 & S176 & S296 & S168 & Hsome) (HcP & HcX).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HCm as (HC & Hold & HF & Hk & [SP72 SP56] & G20 & G21 & G22 & G26).
pose proof HF as (Hinv & HTc & HTlt & Hi & Hha & Hz).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Himg & HPerm & Hperm & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (FI : 4096 <= img /\ img + fmt * N <= alloc_ceiling) by (eapply rk_img_facts; eassumption). destruct FI as (Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & Tn3 & Tn4 & Tn5). fold (ac_Tn C) in Tn1, Tn2, Tn3, Tn4.
set (Tn := ac_Tn C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht ac_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [i; ha; f1; h1; u1]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E20 : ew E 20 = Z_to_bv 64 (3 * Tn)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 Tn) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (D4T : sv_denot E (SAlu ALU_SLL (SOff 22 0) (SLit 2)) = Z_to_bv 64 (4 * Tn)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 22 Tn E22) by (clear - Tn2; lia). rewrite (U_lit E 2) by lia.
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; clear - Tn2; lia). lia. }
assert (Rf1 : 0 <= f1 < 2 ^ 64) by (destruct Hok5 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rh1 : 0 <= h1 < 2 ^ 64) by (destruct Hok3 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (destruct Hok4 as [-> | X]; [clear; lia | clear - X; lia]).
pose proof Hres as (Hok1 & Hok2 & G23 & G24 & G27).
assert (Rp1 : 0 <= p1 < 2 ^ 64) by (destruct Hok1 as [-> | X]; [clear; lia | clear - X; lia]).
assert (Rx1 : 0 <= x1 < 2 ^ 64) by (destruct Hok2 as [-> | X]; [clear; lia | clear - X; lia]).
assert (E54 : ew E 54 = Z_to_bv 64 f1) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 h1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 u1) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 p1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E27 : ew E 27 = Z_to_bv 64 x1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_FAIL true [(21%bv, SOff 32 24)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] [ck 296 (SOff 56 0)] [] [] [mkAC BC_EQ (SOff 23 0) (SLit 0); mkAC BC_EQ (SOff 27 0) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G21. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | exact Rf1 | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | exact Rh1 | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | exact Ru1 | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 23 p1 E23 Rp1), (U_lit E 0) by lia; apply Z.eqb_eq; exact HcP|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, (U_atom E 27 x1 E27 Rx1), (U_lit E 0) by lia; apply Z.eqb_eq; exact HcX|]. exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [23; 27; 26]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 57 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv | exact Hv]) end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
set (cnt := ht_cnt (ac_H C)) in *.
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 (ac_T C)) by exact (HV 7%nat _ eq_refl).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb;
assert (DA : forall n z, (n < 57)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 36 0) (ac_p C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 36%nat _ ltac:(lia) E36 Bp) Bp ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 37 0) (ac_x C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 37%nat _ ltac:(lia) E37 Bx) Bx ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) cnt HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) (ac_T C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (EP : rsel (ac_p C) p1 = ac_p C) by (unfold rsel; rewrite HcP; reflexivity).
assert (EX : rsel (ac_x C) x1 = ac_x C) by (unfold rsel; rewrite HcX; reflexivity).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (xf_cells C p1 x1) (((rz_BL C p1 x1 ++ optb h1 (3 * ac_Tn C)) ++ optb u1 (ac_Tn C)) ++ optb f1 (4 * ac_Tn C))) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := ac_cells C); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx].
- unfold xf_cells. rewrite EP, EX. cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
rewrite <- !app_assoc in HC'.
split; [split; [exact HC'|]; split; [exact HF|]; split; [clear - Hk; lia|]; split; [split; [exact SP72' | exact SP56']|]; split; [exact Hok1|]; split; [exact Hok2|]; split; [|split]|].
- apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 24%bv (SOff 50 0) hv24 eq_refl); [rewrite (denot_off E 50 hv24 0 (HV 18%nat _ eq_refl) O24), Z.add_0_r; reflexivity | reflexivity].
- rewrite (HKR 26%bv ltac:(cbv; clear; tauto)). exact G26.
- split; [exact Hok3|]. split; [exact Hok4|]. split; [exact Hok5|].
split; [apply (SLOT 6%nat 296 304 [ck 296 (SOff 56 0)] 296 (SOff 56 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 56 u1 0 E56 Ru1), Z.add_0_r; reflexivity | reflexivity | exact Ru1]|].
split; [apply (SLOT 4%nat 160 184 [ck 168 (SOff 54 0); ck 176 (SOff 55 0)] 168 (SOff 54 0) f1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 f1 0 E54 Rf1), Z.add_0_r; reflexivity | reflexivity | exact Rf1]|].
split; [apply (RD 10%bv (SOff 55 0) h1 eq_refl); [rewrite (denot_off E 55 h1 0 E55 Rh1), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_FF1R) HL_FF1R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_fail : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1,
at_FAIL lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 ->
SRr trasegs W (cfgat regs HL_FAIL mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_XF mem2 md2 /\ at_XF ly2 S2 W2 regs2 mem2 md2 (k + 3) C i ha p1 x1).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 HF.
assert (S1 : SRr trasegs W (cfgat regs HL_FAIL mem md) (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_FF1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1)).
{ destruct (Z.eq_dec p1 0) as [Zp | Np], (Z.eq_dec x1 0) as [Zx | Nx];
[exact (hl_fail_z_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF (conj Zp Zx)) | exact (hl_fail_z_nz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF (conj Zp Nx))
| exact (hl_fail_nz_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF (conj Np Zx)) | exact (hl_fail_nz_nz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF (conj Np Nx))]. }
eapply SRr_bind; [exact S1|]. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & H1).
eapply SRr_bind; [exact (hl_ff1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1)|]. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & H2).
eapply SRr_bind; [exact (hl_ff1r _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2)|]. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & H3).
eapply SRr_bind; [exact (hl_ff2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3)|]. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & H4).
eapply SRr_bind; [exact (hl_ff2r _ _ _ _ _ _ _ _ _ _ _ _ _ H4)|]. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & H5).
eapply SRr_bind; [exact (hl_ff3 _ _ _ _ _ _ _ _ _ _ _ _ _ H5)|]. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & H6).
eapply SRr_mono; [exact (hl_ff3r _ _ _ _ _ _ _ _ _ _ _ _ H6)|]. intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & H7).
exists ly6, S6, regs7, mem7, md7. split; [reflexivity|]. replace (k + 3) with (k + 1 + 1 + 1) by lia. exact H7.
Qed.
End c.

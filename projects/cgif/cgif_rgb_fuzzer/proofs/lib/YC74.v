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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y YC6z YC70 YC71 YC72 YC7a YC73.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YC6f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section f.
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
Lemma rcore_perm : forall lyc Sc W regs mem md k cells BL BL', rcore lyc Sc W regs mem md k cells BL -> Permutation BL BL' -> rcore lyc Sc W regs mem md k cells BL'.
Proof.
intros lyc Sc W regs mem md k cells BL BL' (HJ & HR & Hsl & Hobj & Himg & HPerm & Hperm & Hkept) HP.
split; [exact HJ|]. split; [exact HR|]. split; [exact Hsl|]. split; [exact Hobj|]. split; [exact Himg|].
split; [eapply Permutation_trans; [exact HPerm|]; apply Permutation_app_head; apply perm_skip; exact HP|].
split; [|exact Hkept]. intros b n Hb. apply Hperm. destruct Hb as [Hb | Hb]; [left; exact Hb | right; eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb]].
Qed.
Lemma rf_free : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K BL d (q : nat) pa n ret,
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K BL d -> nth_error BL q = Some (pa, n) ->
(forall y, In y (rf_new5 C p1 x1 h1 u1 f1) -> exists q' : nat, nth_error BL q' = Some y /\ q' <> q) ->
getr regs 10 = Z_to_bv 64 pa -> getr regs 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 63 -> ret mod 2 = 0 -> 0 <= d <= 2 ->
In (call_trace0 (pc_free_ra0 (as_code B)) regs hk_ch) (as_universe B) ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 ret mem2 md2 /\
rf_common ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1 u1 f1 K (ldel BL q) (d + 1)).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K BL d q pa n ret HP Hq Hnew G10 Gra Hret Hret2 Hd Htr.
pose proof HP as (HC & HNw & HinvKT & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf & G20 & G27).
pose proof HF as (Hinv & HTc & HTlt & _). destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & _). fold (ac_Tn C) in Tn1, Tn2.
pose proof (ts_rank_range (ac_T C)) as Hrk.
eapply SRr_mono.
{ eapply rz_free with (q := q) (pa := pa) (n := n) (ret := ret) (BL := BL) (ch0 := ch0); try eassumption;
first [ (clear - Hk Hrk Hd; lia) | (destruct HOP as (_ & _ & _ & _ & _ & _ & _ & _ & Os0 & _); exact Os0) ]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HC2 & HP2 & Hfr & Hoth & Hd2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
assert (Knew : forall b m, In (b, m) (rf_new5 C p1 x1 h1 u1 f1) -> rg_blk_kept (w_H W) (w_H W2) mem mem2 b (req_size m)).
{ intros b m Hb. destruct (Hnew _ Hb) as (q' & Hq' & Hne). exact (Hoth q' _ Hq' Hne). }
split; [exact HC2|]. split.
{ destruct HNw as ((Af & Ah & Au & Ap & Ax) & Hlens & HTK). pose proof Hlens as (L1 & L2 & L3 & L4 & L5). rewrite HTK in L1, L2, L3, L4, L5.
pose proof (req_size_pos (ac_Tn C) ltac:(clear - Tn2; lia)) as [_ Hr1]. pose proof (req_size_pos (3 * ac_Tn C) ltac:(clear - Tn2; lia)) as [_ Hr3]. pose proof (req_size_pos (4 * ac_Tn C) ltac:(clear - Tn2; lia)) as [_ Hr4].
split; [|split; assumption].
split; [apply (arr32_frame trasegs _ _ _ _ Af); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L3 in Ha; replace a with (f1 + (a - f1)) by lia; apply (Knew f1 (4 * ac_Tn C)); [unfold rf_new5; cbn; clear; tauto | clear - Ha Hr4; lia]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ah); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L2 in Ha; replace a with (h1 + (a - h1)) by lia; apply (Knew h1 (3 * ac_Tn C)); [unfold rf_new5; cbn; clear; tauto | clear - Ha Hr3; lia]|].
split; [apply (arr8_frame trasegs _ _ _ _ Au); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L1 in Ha; replace a with (u1 + (a - u1)) by lia; apply (Knew u1 (ac_Tn C)); [unfold rf_new5; cbn; clear; tauto | clear - Ha Hr1; lia]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ap); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L5 in Ha; replace a with (p1 + (a - p1)) by lia; apply (Knew p1 (3 * ac_Tn C)); [unfold rf_new5; cbn; clear; tauto | clear - Ha Hr3; lia]|].
apply (arr32_frame trasegs _ _ _ _ Ax); intros a Ha; apply (mbyte_of_aview trasegs); rewrite L4 in Ha; replace a with (x1 + (a - x1)) by lia; apply (Knew x1 (4 * ac_Tn C)); [unfold rf_new5; cbn; clear; tauto | clear - Ha Hr4; lia]. }
split; [exact HinvKT|]. split; [exact HF|]. split; [split; [clear - Hk; lia | exact (gbud_free S Sc S2 k (proj2 Hk) Hd2)]|].
split; [split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia]|].
split; [split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|]; split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia|];
split; [eapply slot_kept with (W := W) (mem := mem); try eassumption; lia | eapply slot_kept with (W := W) (mem := mem); try eassumption; lia]|].
split; [exact Pp|]. split; [exact Px|]. split; [exact Ph|]. split; [exact Pu|]. split; [exact Pf|].
destruct saved_used as (Sv20 & _ & _ & _ & _ & Sv27 & _).
rewrite (aregs_get regs regs2 20%bv HP2 Sv20), (aregs_get regs regs2 27%bv HP2 Sv27). split; [exact G20 | exact G27].
Qed.
Lemma rf_common_run_same : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K BL d regs' mem' md',
rf_common lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K BL d ->
(forall y, In y (rf_new5 C p1 x1 h1 u1 f1) -> In y BL) ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
(forall r, In r (HK_CONST ++ [20; 27]%bv) -> getr regs' r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill W mem' i ha -> rh_slots W mem' C h1 u1 f1 ->
rf_common lyc Sc W regs' mem' md' k C i ha p1 x1 h1 u1 f1 K BL d.
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K BL d regs' mem' md' HP Hnew HJ' Hregs KM Hsp Hsl.
pose proof HP as (HC & HNw & HinvKT & HF & Hk & _ & _ & Pp & Px & Ph & Pu & Pf & G20 & G27).
pose proof HF as (Hinv & HTc & HTlt & _). destruct (ts_next_facts _ HTc HTlt) as (Tn1 & Tn2 & _). fold (ac_Tn C) in Tn1, Tn2.
pose proof HC as (HJ & _ & _ & Hobj & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (Hlow : forall b n, In (b, n) ((tb, CHT_SIZE) :: BL) -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin t Ht.
assert (Hin' : In (b, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact Hin).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
apply KM; [clear - Ht Hb0 Hb1 F47; lia | intros [Hx _]; clear - Hx Ht Hb1; lia]. }
split.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := [ac_f C; ac_h C; ac_u C; p1; x1; ht_cnt K; ac_Tn C]); try eassumption.
- intros r Hr. apply Hregs. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ _. exact (KM a Ha H1).
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem' tb LAY_Cht _ 48 Hobj lay_inside_Cht). exact (Hlow tb CHT_SIZE ltac:(left; reflexivity)). }
split.
{ apply (rh_new_kept_3 W mem mem' C p1 x1 h1 u1 f1 K HNw ltac:(clear - Tn2; lia)); apply Hlow; right; apply Hnew; unfold rf_new5; cbn; clear; tauto. }
split; [exact HinvKT|]. split; [exact HF|]. split; [exact Hk|]. split; [exact Hsp|]. split; [exact Hsl|].
split; [exact Pp|]. split; [exact Px|]. split; [exact Ph|]. split; [exact Pu|]. split; [exact Pf|].
rewrite (Hregs 20%bv ltac:(cbv; clear; tauto)), (Hregs 27%bv ltac:(cbv; clear; tauto)). split; [exact G20 | exact G27].
Qed.
Lemma rh_new_kept_tb : forall lyc Sc W regs mem md k cells BL C p1 x1 h1 u1 f1 K (mem' : word -> option byte),
rcore lyc Sc W regs mem md k cells BL -> (forall y, In y (rf_new5 C p1 x1 h1 u1 f1) -> In y BL) ->
rh_new W mem C p1 x1 h1 u1 f1 K -> 0 <= ac_Tn C ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
rh_new W mem' C p1 x1 h1 u1 f1 K.
Proof.
intros lyc Sc W regs mem md k cells BL C p1 x1 h1 u1 f1 K mem' HC Hnew HNw HTn KM.
pose proof HC as (HJ & _ & _ & _ & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (FF : alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a)) by (eapply rk_frame_facts; eassumption).
destruct FF as (Fceil & F47 & F32 & Fpres).
assert (Hlow : forall b n, In (b, n) (rf_new5 C p1 x1 h1 u1 f1) -> rg_blk_kept (w_H W) (w_H W) mem mem' b (req_size n)).
{ intros b n Hin t Ht. pose proof (Hnew _ Hin) as HinBL.
assert (Hin' : In (b, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; right; exact HinBL).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md b n HAR Hin' Fceil) as (Hb0 & Hb1 & Hb2 & Hb3).
assert (Hap : rapart tb PROT lyc Sc (b + t)) by (eapply rblk_apart with (b := b) (n := n) (BLX := BL); try eassumption; clear - Ht; lia).
destruct Hap as (_ & _ & Hp & _).
apply KM; [clear - Ht Hb0 Hb1 F47; lia | intros [Hx _]; clear - Hx Ht Hb1; lia|].
intros Hx. apply (Hp tb CHT_SIZE ltac:(apply in_app_iff; right; left; reflexivity)). change (req_size CHT_SIZE) with 48. exact Hx. }
apply (rh_new_kept_3 W mem mem' C p1 x1 h1 u1 f1 K HNw HTn); apply Hlow; unfold rf_new5; cbn; clear; tauto.
Qed.
Lemma perm5 : forall (a b c d e : Z * Z), Permutation [a; b; c; d; e] [e; c; d; a; b].
Proof.
intros a b c d e. apply Permutation_sym.
change [e; c; d; a; b] with ([e; c; d] ++ a :: [b]). eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
change ([e; c; d] ++ [b]) with ([e; c; d] ++ b :: []). eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
rewrite app_nil_r. change [e; c; d] with ([e] ++ [c; d]). change [c; d; e] with ([c; d] ++ [e]). apply Permutation_app_comm.
Qed.
Lemma hl_f1 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_F1C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_F1R mem2 md2 /\ at_F1R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K (HP & G10 & Gra).
eapply SRr_mono.
{ apply (rf_free lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K _ 0 1%nat (ac_h C) (3 * ac_T C) HL_F1R HP eq_refl); [| exact G10 | exact Gra | unfold HL_F1R; clear; lia | reflexivity | clear; lia |].
- unfold rf_new5. intros y [<- | [<- | [<- | [<- | [<- | []]]]]]; [exists 3%nat | exists 4%nat | exists 5%nat | exists 6%nat | exists 7%nat]; (split; [reflexivity | lia]).
- rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_F1R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_F1R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2). exists ly2, S2, regs2, mem2, md2. split; [reflexivity | exact HP2].
Qed.
Lemma hl_f2 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_F2C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_F2R mem2 md2 /\ at_F2R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K (HP & G10 & Gra).
eapply SRr_mono.
{ apply (rf_free lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K _ 1 1%nat (ac_u C) (ac_T C) HL_F2R HP eq_refl); [| exact G10 | exact Gra | unfold HL_F2R; clear; lia | reflexivity | clear; lia |].
- unfold rf_new5. intros y [<- | [<- | [<- | [<- | [<- | []]]]]]; [exists 2%nat | exists 3%nat | exists 4%nat | exists 5%nat | exists 6%nat]; (split; [reflexivity | lia]).
- rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_F2R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_F2R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2). exists ly2, S2, regs2, mem2, md2. split; [reflexivity | exact HP2].
Qed.
Lemma hl_f3 : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_F3C lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs A_free_tra mem md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfgat regs2 HL_F3R mem2 md2 /\ at_F3R ly2 S2 W2 regs2 mem2 md2 (k + 1) C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K (HP & G10 & Gra).
eapply SRr_mono.
{ apply (rf_free lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K _ 2 0%nat (ac_f C) (4 * ac_T C) HL_F3R HP eq_refl); [| exact G10 | exact Gra | unfold HL_F3R; clear; lia | reflexivity | clear; lia |].
- unfold rf_new5. intros y [<- | [<- | [<- | [<- | [<- | []]]]]]; [exists 1%nat | exists 2%nat | exists 3%nat | exists 4%nat | exists 5%nat]; (split; [reflexivity | lia]).
- rewrite (tl_code B TL). apply (hk_trace_in B TL sp0 rav s0v ch0 Hrav Hspine _ regs HL_F3R); [unfold raZ; rewrite Gra; apply unsigned_lit_small; unfold HL_F3R; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2). exists ly2, S2, regs2, mem2, md2. split; [reflexivity | exact HP2].
Qed.
Lemma hl_f1r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_F1R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs HL_F1R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_F2C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K HP.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HP as (HC & HNw & HinvKT & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf & G20 & G27).
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
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht rh_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
unfold rh_ptr in Pp, Px, Ph, Pu, Pf.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) Tn).
set (xv := [i; ha; Tn; f1; h1; u1] ++ []).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 p1) by exact (HV 4%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 x1) by exact (HV 5%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt K)) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 Tn) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 Tn) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 h1) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 u1) by exact (HV 25%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
pose proof HNw as (_ & _ & HTK). pose proof HinvKT as (_ & (HcntK & _) & _).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_F1R false [(20%bv, SOff 32 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) Tn xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G20. symmetry. rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 58)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
assert (Hsl' : rh_slots W (ms_mem ms) C h1 u1 f1).
{ split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 160 (SOff 54 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 168 (SOff 55 0) f1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pf; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 176 (SOff 56 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Ph; lia]|].
apply (SLOT 6%nat 296 304 [ck 296 (SOff 57 0)] 296 (SOff 57 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pu; lia]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : rf_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: (ac_u C, ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 1) end.
{ apply (rf_common_run_same lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: (ac_u C, ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 1 _ _ _ HP); [intros y Hy; right; right; exact Hy | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56'] | exact Hsl'].
intros r Hr; apply in_app_iff in Hr; destruct Hr as [Hr | [<- | [<- | []]]];
[apply HKR; apply in_or_app; left; exact Hr
| rewrite G20; apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity]
| apply HKR; apply in_or_app; right; left; reflexivity]. }
split; [exact HP'|].
split; [apply (RD 10%bv (SOff 35 0) (ac_u C) eq_refl); [rewrite (denot_off E 35 (ac_u C) 0 E35 Bu), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_F2R) HL_F2R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_f2r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_F2R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs HL_F2R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_F3C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K HP.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HP as (HC & HNw & HinvKT & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf & G20 & G27).
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
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht rh_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
unfold rh_ptr in Pp, Px, Ph, Pu, Pf.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) Tn).
set (xv := [i; ha; Tn; f1; h1; u1] ++ []).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 p1) by exact (HV 4%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 x1) by exact (HV 5%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt K)) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 Tn) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 Tn) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 h1) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 u1) by exact (HV 25%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
pose proof HNw as (_ & _ & HTK). pose proof HinvKT as (_ & (HcntK & _) & _).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_F2R false [(20%bv, SOff 32 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) Tn xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G20. symmetry. rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 58)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
assert (Hsl' : rh_slots W (ms_mem ms) C h1 u1 f1).
{ split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 160 (SOff 54 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 168 (SOff 55 0) f1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pf; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 176 (SOff 56 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Ph; lia]|].
apply (SLOT 6%nat 296 304 [ck 296 (SOff 57 0)] 296 (SOff 57 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pu; lia]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HP' : rf_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 2) end.
{ apply (rf_common_run_same lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ((ac_f C, 4 * ac_T C) :: rf_new5 C p1 x1 h1 u1 f1) 2 _ _ _ HP); [intros y Hy; right; exact Hy | exact HJ | | exact KM1 | split; [exact SP72' | exact SP56'] | exact Hsl'].
intros r Hr; apply in_app_iff in Hr; destruct Hr as [Hr | [<- | [<- | []]]];
[apply HKR; apply in_or_app; left; exact Hr
| rewrite G20; apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity]
| apply HKR; apply in_or_app; right; left; reflexivity]. }
split; [exact HP'|].
split; [apply (RD 10%bv (SOff 33 0) (ac_f C) eq_refl); [rewrite (denot_off E 33 (ac_f C) 0 E33 Bf), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_F3R) HL_F3R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_done : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_DONE lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs HL_DONE mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_free_tra mem2 md2 /\ at_F1C lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ([HP HNw] & HinvKT & G15 & G16 & G20).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HP as (HC & Hold & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf).
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
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht rh_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
unfold rh_ptr in Pp, Px, Ph, Pu, Pf.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T).
set (xv := [i; ha; Tn; f1; h1; u1] ++ []).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 p1) by exact (HV 4%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 x1) by exact (HV 5%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt K)) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 Tn) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 h1) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 u1) by exact (HV 25%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_DONE true [(15%bv, SOff 32 44); (16%bv, SOff 32 8)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; (split; [reflexivity|]); cbn [fst snd].
- rewrite G15. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G16. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_free_tra.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 58)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
assert (Hsl' : rh_slots W (ms_mem ms) C h1 u1 f1).
{ split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 160 (SOff 54 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 168 (SOff 55 0) f1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pf; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 176 (SOff 56 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Ph; lia]|].
apply (SLOT 6%nat 296 304 [ck 296 (SOff 57 0)] 296 (SOff 57 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pu; lia]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of UX32 with bv_unsigned (ew ?Ex 32) = _ =>
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) E34 Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 36 0) p1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 36%nat _ ltac:(lia) E36 Bp) Bp ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 37 0) x1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 37%nat _ ltac:(lia) E37 Bx) Bx ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) (ht_cnt K) HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 54 0) Tn HRtb UX32 ltac:(cbn; clear; tauto) (DA 54%nat _ ltac:(lia) E54 ltac:(clear - Tn2; lia)) ltac:(clear - Tn2; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (Hobj' : obj_at trasegs (mrestrict (w_H W) (ms_mem ms)) tb LAY_Cht [ac_f C; ac_h C; ac_u C; p1; x1; ht_cnt K; Tn]).
{ cbn [obj_at LAY_Cht rh_cells]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | clear - Tn2; lia]|]. exact I. }
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k [ac_f C; ac_h C; ac_u C; p1; x1; ht_cnt K; Tn] (rh_BL C p1 x1 h1 u1 f1)) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := rh_cells C p1 x1 (ht_cnt K)); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx]. }
split; [|split; [apply (RD 10%bv (SOff 34 0) (ac_h C) eq_refl); [rewrite (denot_off E 34 (ac_h C) 0 E34 Bh), Z.add_0_r; reflexivity | reflexivity] | exact (RD 1%bv (SLit HL_F1R) HL_F1R eq_refl eq_refl eq_refl)]].
split; [exact HC'|].
split; [apply (rh_new_kept_tb lyc Sc W regs mem md k _ (rh_BL C p1 x1 h1 u1 f1) C p1 x1 h1 u1 f1 K (ms_mem ms) HC ltac:(intros y Hy; right; right; right; exact Hy) HNw ltac:(fold Tn; clear - Tn2; lia) KM1)|].
split; [exact HinvKT|]. split; [exact HF|]. split; [split; [clear - Hk; subst T; lia | exact (proj2 Hk)]|]. split; [split; [exact SP72' | exact SP56']|]. split; [exact Hsl'|].
split; [exact Pp|]. split; [exact Px|]. split; [exact Ph|]. split; [exact Pu|]. split; [exact Pf|].
split; [rewrite (HKR 20%bv ltac:(cbv; clear; tauto)); exact G20|].
apply (RD 27%bv (SOff 41 0) hv27 eq_refl); [rewrite (denot_off E 41 hv27 0 (HV 9%nat _ eq_refl) O27), Z.add_0_r; reflexivity | reflexivity].
Qed.
Lemma hl_f3r : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K,
at_F3R lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K ->
SRr trasegs W (cfgat regs HL_F3R mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_TAIL mem2 md2 /\ at_TL lyc Sc W regs2 mem2 md2 k (ac_new C p1 x1 h1 u1 f1 K) i ha).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K HP.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HP as (HC & HNw & HinvKT & HF & Hk & [SP72 SP56] & (S160 & S168 & S176 & S296) & Pp & Px & Ph & Pu & Pf & G20 & G27).
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
destruct (rh_BL_nth_3 C p1 x1 h1 u1 f1) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
set (Tn := ac_Tn C) in *. set (T := ac_T C) in *.
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht rh_cells] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Bc, BT.
pose proof HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
unfold rh_ptr in Pp, Px, Ph, Pu, Pf.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) Tn).
set (xv := [i; ha; Tn; f1; h1; u1] ++ []).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 (ac_h C)) by exact (HV 2%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 p1) by exact (HV 4%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 x1) by exact (HV 5%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt K)) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 Tn) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 Tn) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 f1) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 h1) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 u1) by exact (HV 25%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_F3R true [(20%bv, SOff 32 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] [] [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) Tn xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G20. symmetry. rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ exact I. }
{ exact I. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_TAIL.
{ apply (hk_awr_ok s1v tb fmt E true _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros _ a Ha; destruct (Hperm tb CHT_SIZE ltac:(left; reflexivity)) as [_ Hw]; replace a with (tb + (a - tb)) by lia; apply Hw; [exact Htbin | change (req_size CHT_SIZE) with 48; clear - Ha; lia] | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt. apply (hk_frame_kept s1v tb fmt _ true _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 58)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb; cbn [ms_mem restrict] in HRtb end.
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (SLOT 2%nat 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity | clear - Hi HN; lia]).
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (SLOT 1%nat 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity | clear - Hha; lia]).
assert (Hsl' : rh_slots W (ms_mem ms) C h1 u1 f1).
{ split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 160 (SOff 54 0) Tn eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Tn2; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 168 (SOff 55 0) f1 eq_refl ltac:(right; left; reflexivity)); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pf; lia]|].
split; [apply (SLOT 4%nat 160 184 [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] 176 (SOff 56 0) h1 eq_refl ltac:(right; right; left; reflexivity)); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Ph; lia]|].
apply (SLOT 6%nat 296 304 [ck 296 (SOff 57 0)] 296 (SOff 57 0) u1 eq_refl ltac:(left; reflexivity)); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | reflexivity | clear - Pu; lia]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of UX32 with bv_unsigned (ew ?Ex 32) = _ =>
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 55 0) f1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 55%nat _ ltac:(lia) E55 ltac:(clear - Pf; lia)) ltac:(clear - Pf; lia) ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 56 0) h1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 56%nat _ ltac:(lia) E56 ltac:(clear - Ph; lia)) ltac:(clear - Ph; lia) ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 57 0) u1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 57%nat _ ltac:(lia) E57 ltac:(clear - Pu; lia)) ltac:(clear - Pu; lia) ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 36 0) p1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 36%nat _ ltac:(lia) E36 Bp) Bp ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 37 0) x1 HRtb UX32 ltac:(cbn; clear; tauto) (DA 37%nat _ ltac:(lia) E37 Bx) Bx ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 0) (ht_cnt K) HRtb UX32 ltac:(cbn; clear; tauto) (DA 38%nat _ ltac:(lia) E38 ltac:(clear - Bc; lia)) ltac:(clear - Bc; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) Tn HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) E39 ltac:(clear - BT; lia)) ltac:(clear - BT; cbn; lia) ltac:(lia)) as VT' end.
rewrite !Z.add_0_r in Vf'.
assert (Hobj' : obj_at trasegs (mrestrict (w_H W) (ms_mem ms)) tb LAY_Cht [f1; h1; u1; p1; x1; ht_cnt K; Tn]).
{ cbn [obj_at LAY_Cht rh_cells]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | clear - Pf; lia]|]. split; [split; [exact Vh' | clear - Ph; lia]|]. split; [split; [exact Vu' | clear - Pu; lia]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | exact Bc]|].
split; [split; [exact VT' | exact BT]|]. exact I. }
set (Cn := ac_new C p1 x1 h1 u1 f1 K).
pose proof HNw as (HarrK & HlensK & HTK).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HC' : rcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k [f1; h1; u1; p1; x1; ht_cnt K; Tn] (rf_new5 C p1 x1 h1 u1 f1)) end.
{ eapply rcore_run with (regs := regs) (mem := mem) (md := md) (cells := [ac_f C; ac_h C; ac_u C; p1; x1; ht_cnt K; Tn]); try eassumption.
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnb. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnb. exists tb, CHT_SIZE. split; [left; reflexivity | change (req_size CHT_SIZE) with 48; exact Hx]. }
assert (HNw' : rh_new W (ms_mem ms) C p1 x1 h1 u1 f1 K)
by (apply (rh_new_kept_tb lyc Sc W regs mem md k _ (rf_new5 C p1 x1 h1 u1 f1) C p1 x1 h1 u1 f1 K (ms_mem ms) HC ltac:(intros y Hy; exact Hy) HNw ltac:(fold Tn; clear - Tn2; lia) KM1)).
assert (ETn : ac_T Cn = Tn) by (unfold ac_T, Cn, ac_new; cbn [ac_H]; exact HTK).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
assert (HCr : hcore_raw lyc Sc W (ms_regs ms) (ms_mem ms) mdx k Cn) end.
{ apply (hcore_raw_of_rcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
- unfold ac_cells, ac_arrs. rewrite ETn. unfold Cn, ac_new. cbn [ac_f ac_h ac_u ac_p ac_x ac_H].
apply (rcore_perm _ _ _ _ _ _ _ _ (rf_new5 C p1 x1 h1 u1 f1)); [exact HC'|]. unfold rf_new5, cht_blocks. fold Tn. apply perm5.
- unfold Cn, ac_new. cbn [ac_f ac_h ac_u ac_p ac_x ac_H]. exact (proj1 HNw').
- unfold Cn, ac_new. cbn [ac_H]. exact HlensK.
- rewrite ETn. exact Tn3.
- split; [rewrite ETn; subst Tn; unfold ac_Tn; rewrite (ts_rank_next (ac_T C) HTc HTlt); clear - Hk; subst T; lia | exact (proj2 Hk)]. }
pose proof (rehash_done (ac_H C) (ac_ent C) Hinv) as HPent.
split; [split; [exact HCr | unfold Cn, ac_new; cbn [ac_H ac_ent]; exact HinvKT]|].
split.
{ split; [apply (RD 5%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [apply (RD 6%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 7%bv (SLit fmt) fmt eq_refl eq_refl eq_refl)|].
split; [apply (RD 16%bv (SOff 47 0) hv16 eq_refl); [rewrite (denot_off E 47 hv16 0 (HV 15%nat _ eq_refl) O16), Z.add_0_r; reflexivity | reflexivity]|].
split; [apply (RD 17%bv (SOff 46 0) hv17 eq_refl); [rewrite (denot_off E 46 hv17 0 (HV 14%nat _ eq_refl) O17), Z.add_0_r; reflexivity | reflexivity]|].
rewrite (HKR 27%bv ltac:(cbv; clear; tauto)). exact G27. }
split; [apply (RD 28%bv (SOff 52 0) i eq_refl); [rewrite (denot_off E 52 i 0 E52 ltac:(clear - Hi HN; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [apply (RD 12%bv (SOff 53 0) ha eq_refl); [rewrite (denot_off E 53 ha 0 E53 ltac:(clear - Hha; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact Hi|]. split; [exact Hha|].
unfold Cn, ac_new. cbn [ac_ent].
assert (X : zsum (map snd (ents_below (ac_H C) (ac_T C))) = zsum (map snd (ac_ent C))) by (symmetry; exact (perm_zsum _ _ HPent)).
fold T in X. fold T. rewrite X. exact Hz.
Qed.
End f.

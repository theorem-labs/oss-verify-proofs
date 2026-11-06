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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y YC6z YC70 YC71 YC72 YC7a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
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
Lemma hl_ln_next : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j,
at_LN lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j -> j + 1 < ac_T C ->
SRr trasegs W (cfgat regs HL_LN mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_LH mem2 md2 /\ at_LH lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K (j + 1)).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j ([HP HNw] & HinvK & Hj & (G21 & G26 & G27 & G5 & G15 & G16 & G17 & G20)) Hcase.
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
assert (RT0 : 524309 <= T <= 8388617) by (subst T; clear - HTc HTlt; unfold MAX_TABLE_SIZE in HTlt; cbv [ts_chain In] in HTc; lia).
assert (E21 : ew E 21 = Z_to_bv 64 j) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (E26 : ew E 26 = Z_to_bv 64 (4 * j)) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (E27 : ew E 27 = Z_to_bv 64 (3 * j)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
set (xat0 := [(21%nat, mkAF 0 8388616 0); (39%nat, mkAF 524309 8388617 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_LN false [(15%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] xat0 [mkAC BC_LTU (SOff 21 1) (SOff 39 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G15. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
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
{ subst xat0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E21, E39. rewrite !unsigned_lit_small by (clear - Hj RT0; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Hj RT0. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (U_atom_off E 21 j 1 E21) by (clear - Hj RT0; lia). rewrite (U_atom E 39 T E39) by (clear - RT0; lia). apply Z.ltb_lt. exact Hcase. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_LH.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [5; 16; 17; 20]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
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
assert (HCM' : rh_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 K) end.
{ apply (rh_common_run_same_3 lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K _ _ _ (conj HP HNw) HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | exact KM1 | split; [exact SP72' | exact SP56'] | exact Hsl']. }
split; [exact HCM'|]. split; [exact HinvK|]. split; [clear - Hj Hcase; subst T; lia|].
unfold rh_loop_regs. rewrite (HKR 5%bv ltac:(cbv; clear; tauto)), (HKR 16%bv ltac:(cbv; clear; tauto)), (HKR 17%bv ltac:(cbv; clear; tauto)), (HKR 20%bv ltac:(cbv; clear; tauto)).
split; [apply (RD 21%bv (SOff 21 1) (j + 1) eq_refl); [apply denot_off; [exact E21 | clear - Hj RT0; lia] | reflexivity]|].
split; [replace (4 * (j + 1)) with (4 * j + 4) by lia; apply (RD 26%bv (SOff 26 4) (4 * j + 4) eq_refl); [apply denot_off; [exact E26 | clear - Hj RT0; lia] | reflexivity]|].
split; [replace (3 * (j + 1)) with (3 * j + 3) by lia; apply (RD 27%bv (SOff 27 3) (3 * j + 3) eq_refl); [apply denot_off; [exact E27 | clear - Hj RT0; lia] | reflexivity]|].
split; [exact G5|]. split; [apply (RD 15%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [exact G16|]. split; [exact G17 | exact G20].
Qed.
Lemma hl_ln_done : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j,
at_LN lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j -> ~ (j + 1 < ac_T C) ->
SRr trasegs W (cfgat regs HL_LN mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_DONE mem2 md2 /\ at_DONE lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j ([HP HNw] & HinvK & Hj & (G21 & G26 & G27 & G5 & G15 & G16 & G17 & G20)) Hcase.
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
assert (RT0 : 524309 <= T <= 8388617) by (subst T; clear - HTc HTlt; unfold MAX_TABLE_SIZE in HTlt; cbv [ts_chain In] in HTc; lia).
assert (E21 : ew E 21 = Z_to_bv 64 j) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (E26 : ew E 26 = Z_to_bv 64 (4 * j)) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (E27 : ew E 27 = Z_to_bv 64 (3 * j)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
set (xat0 := [(21%nat, mkAF 0 8388616 0); (39%nat, mkAF 524309 8388617 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_LN false [(15%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [] xat0 [mkAC BC_GEU (SOff 21 1) (SOff 39 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. split; [reflexivity|]. cbn [fst snd]. rewrite G15. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
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
{ subst xat0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E21, E39. rewrite !unsigned_lit_small by (clear - Hj RT0; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Hj RT0. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (U_atom_off E 21 j 1 E21) by (clear - Hj RT0; lia). rewrite (U_atom E 39 T E39) by (clear - RT0; lia). apply Bool.negb_true_iff, Z.ltb_ge. clear - Hcase. subst T. lia. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_DONE.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [5; 16; 17; 20]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
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
assert (HCM' : rh_common lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C i ha p1 x1 h1 u1 f1 K) end.
{ apply (rh_common_run_same_3 lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K _ _ _ (conj HP HNw) HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | exact KM1 | split; [exact SP72' | exact SP56'] | exact Hsl']. }
split; [exact HCM'|]. split; [replace (ac_T C) with (j + 1) by (clear - Hj Hcase; subst T; lia); exact HinvK|].
rewrite (HKR 16%bv ltac:(cbv; clear; tauto)), (HKR 20%bv ltac:(cbv; clear; tauto)).
split; [apply (RD 15%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [exact G16 | exact G20].
Qed.
Ltac hl_use L := (eapply L; eassumption).
Lemma hl_slot : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j,
at_LH lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j ->
SRr trasegs W (cfgat regs HL_LH mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 K2, c2 = cfgat regs2 HL_LN mem2 md2 /\ at_LN lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K2 j).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j HLH.
pose proof HLH as (((_ & _ & (Hinv & _) & _) & _) & _ & Hj & _).
destruct (inv_used01 (ac_H C) (ac_ent C) Hinv j Hj) as [Hu0 | Hu1].
- eapply SRr_mono; [hl_use hl_lh_unused|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HLN). split; [reflexivity|]. exists regs2, mem2, md2, K. split; [reflexivity | exact HLN].
- eapply SRr_bind; [hl_use hl_lh_used|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & h2 & H1).
eapply SRr_bind; [hl_use hl_ch|]. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & H2).
eapply SRr_bind; [hl_use hl_chr|]. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & H3).
eapply SRr_bind; [hl_use hl_rm1|]. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & H4).
eapply SRr_bind; [hl_use hl_rm1r|]. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & H5).
eapply SRr_bind; [hl_use hl_rm2|]. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & H6).
eapply SRr_mono; [hl_use hl_rm2r|].
intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HLN). split; [reflexivity|]. eexists regs7, mem7, md7, _. split; [reflexivity | exact HLN].
Qed.
Theorem hl_rehash : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j,
at_LH lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j ->
SRr trasegs W (cfgat regs HL_LH mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 K2, c2 = cfgat regs2 HL_DONE mem2 md2 /\ at_DONE lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K2).
Proof.
intros lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j HLH.
pose (X := (bvmap 5 word * (word -> option byte) * Model * htab * Z)%type).
pose (P := fun (x : X) (Wx : world trasegs) (c : config) =>
let '(rx, mx, mdx, Kx, jx) := x in Wx = W /\ c = cfgat rx HL_LH mx mdx /\ at_LH lyc Sc W rx mx mdx k C i ha p1 x1 h1 u1 f1 Kx jx).
pose (m := fun (x : X) => let '(_, _, _, _, jx) := x in ac_T C - jx).
apply (SRr_loopZ trasegs X m P _) with (x := (regs, mem, md, K, j)); [|split; [reflexivity|]; split; [reflexivity | exact HLH]].
clear HLH. clear regs mem md K j. intros [[[[rx mx] mdx] Kx] jx] Wx c (-> & -> & HLH). cbn [m].
eapply SRr_bind; [exact (hl_slot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLH)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & K1 & -> & HLN).
pose proof HLN as (_ & _ & Hj & _).
destruct (Z_lt_dec (jx + 1) (ac_T C)) as [Hlt | Hge].
- eapply SRr_mono; [hl_use hl_ln_next|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HLH2). right. exists (regs2, mem2, md2, K1, jx + 1). cbn [m P].
split; [clear - Hlt Hj; lia|]. split; [reflexivity|]. split; [reflexivity | exact HLH2].
- eapply SRr_mono; [hl_use hl_ln_done|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HD). left. split; [reflexivity|]. exists regs2, mem2, md2, K1. split; [reflexivity | exact HD].
Qed.
End d.

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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79 YC6x YC6y YC6z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition uj_reg (v : Z) : YQ0b.region := YQ0b.mkRegion (Some 58%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit v))].
Definition UJE : sv := SAlu ALU_ADD (SOff 35 0) (SOff 21 0).
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
Lemma rh_uj_side : forall (E : env) lyc Sc W mem md (u T j : Z) (used : list Z) (v : Z),
AR trasegs B lyc Sc W mem md -> In (u, T) (ablocks B lyc Sc) -> arr8 trasegs (mrestrict (w_H W) mem) u used -> zlen used = T -> 0 < T < 2 ^ 30 -> 0 <= j < T ->
ew E 25 = Z_to_bv 64 SB -> ew E 35 = Z_to_bv 64 u -> ew E 21 = Z_to_bv 64 j -> ew E 58 = Z_to_bv 64 (u + j) -> v = getz used j ->
Forall (region_ok trasegs E (mrestrict (w_H W) mem)) [uj_reg v] /\
extent_of_region E (uj_reg v) = (u + j, u + j + 1) /\
atoms_ok E [(58%nat, mkAF 4096 140737479966720 0)] /\ alias_ok E [(UJE, SOff 58 0)] /\
Forall (shent_ok trasegs hk_Bx E (mrestrict (w_H W) mem)) [mkSHE 58 0 1].
Proof.
intros E lyc Sc W mem md u T j used v HAR Hin Hu LU RT Rj E25 E35 E21 E58 Hv.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W mem md u T HAR Hin) as (_ & Hu4096 & Huceil & Happ & _ & _ & Hn0).
pose proof (req_size_pos T ltac:(lia)) as [_ Hrq].
destruct (arr8_getz trasegs _ u used j Hu ltac:(lia)) as [Bu Rub]. rewrite <- Hv in Bu, Rub.
assert (U58 : bv_unsigned (ew E 58) = u + j) by (rewrite E58; apply unsigned_lit_small; clear - Hu4096 Huceil Hrq Rj C1; lia).
split.
{ apply Forall_cons; [|apply Forall_nil]. unfold uj_reg, region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U58.
split; [clear - Hu4096 Rj; lia|]. split; [clear - Huceil Hrq Rj C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (u + j) 0 1 _ v); [reflexivity | exact Rub | lia |].
rewrite Z.add_0_r. apply (val_mem_byte trasegs); assumption. }
split.
{ unfold extent_of_region, uj_reg. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U58. f_equal; lia. }
split.
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U58, Z.pow_0_r, Z.mod_1_r. clear - Hu4096 Huceil Hrq Rj C1. repeat split; lia. }
split.
{ cbn [alias_ok]. split; [|exact I]. apply U_inj. rewrite (U_atom E 58 (u + j) E58) by (clear - Hu4096 Huceil Hrq Rj C1; lia).
unfold UJE. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 35 u E35) by (clear - Hu4096 Huceil Hrq C1 RT; lia).
rewrite (U_atom E 21 j E21) by (clear - Rj RT; lia).
apply zcanon_id. unfold M64. clear - Hu4096 Huceil Hrq Rj C1. lia. }
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 58 (u + j) 1 (u + j) 0 1).
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md u T _ _ HAR Hin); clear - Rj Hrq; lia.
- unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U58.
- lia.
- lia.
- intros x Hx. revert Hx Happ Rj Hrq. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma D_and32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 4294967295)) = Z_to_bv 64 v.
Proof.
intros E n v En Hv. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v En) by lia. rewrite (U_lit E 4294967295) by lia.
change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma D_h3j : forall E h v, ew E 34 = Z_to_bv 64 h -> ew E 27 = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> 0 <= h -> h + v < 2 ^ 63 ->
sv_denot E (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_AND (SOff 27 0) (SLit 4294967295))) = Z_to_bv 64 (h + v).
Proof.
intros E h v E34 E27 Hv Hh Hs. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 34 h E34) by lia.
assert (UA : U E (SAlu ALU_AND (SOff 27 0) (SLit 4294967295)) = v) by (unfold U; rewrite (D_and32 E 27 v E27 Hv); apply unsigned_lit_small; lia).
rewrite UA. apply zcanon_id. unfold M64. lia.
Qed.
Lemma hl_lh_unused : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j,
at_LH lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j -> usedz (ac_H C) j = 0 ->
SRr trasegs W (cfgat regs HL_LH mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 HL_LN mem2 md2 /\ at_LN lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j).
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
set (xv := [i; ha; Tn; f1; h1; u1] ++ [ac_u C + j]).
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
pose proof Hold as (Af & Ah & Au). pose proof Hinv as ((LU & LK & LF & _) & (Hcnt & _) & _). change (ht_T (ac_H C)) with T in LU, LK, LF, Hcnt.
assert (RT : 0 < T < 2 ^ 30) by (subst T; clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (E58 : ew E 58 = Z_to_bv 64 (ac_u C + j)) by exact (HV 26%nat _ eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 j) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (E27 : ew E 27 = Z_to_bv 64 (3 * j)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N3)).
destruct (rh_uj_side E lyc Sc W mem md (ac_u C) T j (ht_used (ac_H C)) 0 HAR Huin Au LU RT Hj E25 E35 E21 E58 ltac:(symmetry; exact Hcase)) as (SIDE1 & SIDE2 & SIDE3 & SIDE4 & SIDE5).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_u C) T HAR Huin Fceil) as (Hu0 & Hu1 & Hu2 & Hu3).
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 3%nat _ _ HC N0 N3 ltac:(lia)) as A03. cbn [fst snd] in A03. change (req_size CHT_SIZE) with 48 in A03.
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_LH false [(5%bv, SLit 1); (15%bv, SOff 32 44); (16%bv, SOff 32 8); (17%bv, SOff 32 16); (20%bv, SOff 32 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [uj_reg 0] [(58%nat, mkAF 4096 140737479966720 0)] [] [(UJE, SOff 58 0)] [mkSHE 58 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G5. reflexivity.
- rewrite G15. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G16. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G17. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G20. symmetry. rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ exact SIDE1. }
{ intros e [<- | []]. rewrite SIDE2. cbn [fst snd]. split; [clear - Hj Hu2 Hu3; lia | clear - Hj A03 Hu3; lia]. }
{ cbn [map zpairwise_disjoint zall_disjoint]. repeat split. }
{ exact SIDE3. }
{ exact I. }
{ exact SIDE4. }
{ exact SIDE5. }
assert (HAE : env_agree 59 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_LN.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 59 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | []] & Hr). cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val uj_reg] in Hr. clear - Hr. lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 59 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [21; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 59 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 59 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 59 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 59 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 59)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
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
split; [exact HCM'|]. split; [exact (rehash_step_unused (ac_H C) K j HinvK (proj1 Hj) Hcase)|]. split; [exact Hj|].
unfold rh_loop_regs. rewrite (HKR 21%bv ltac:(cbv; clear; tauto)), (HKR 26%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)).
split; [exact G21|]. split; [exact G26|]. split; [exact G27|]. split; [exact (RD 5%bv (SLit 1) 1 eq_refl eq_refl eq_refl)|].
split; [apply (RD 15%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [apply (RD 16%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|]. split; [apply (RD 17%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
apply (RD 20%bv (SOff 32 0) tb eq_refl); [rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r; reflexivity | reflexivity].
Qed.
Lemma hl_lh_used : forall lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j,
at_LH lyc Sc W regs mem md k C i ha p1 x1 h1 u1 f1 K j -> usedz (ac_H C) j = 1 ->
SRr trasegs W (cfgat regs HL_LH mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_col_hash mem2 md2 /\ exists h2, at_CHC lyc Sc W regs2 mem2 md2 k C i ha p1 x1 h1 u1 f1 K j h2).
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
set (xv := [i; ha; Tn; f1; h1; u1] ++ [ac_u C + j]).
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
pose proof Hold as (Af & Ah & Au). pose proof Hinv as ((LU & LK & LF & _) & (Hcnt & _) & _). change (ht_T (ac_H C)) with T in LU, LK, LF, Hcnt.
assert (RT : 0 < T < 2 ^ 30) by (subst T; clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (E58 : ew E 58 = Z_to_bv 64 (ac_u C + j)) by exact (HV 26%nat _ eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 j) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (E27 : ew E 27 = Z_to_bv 64 (3 * j)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N3)).
destruct (rh_uj_side E lyc Sc W mem md (ac_u C) T j (ht_used (ac_H C)) 1 HAR Huin Au LU RT Hj E25 E35 E21 E58 ltac:(symmetry; exact Hcase)) as (SIDE1 & SIDE2 & SIDE3 & SIDE4 & SIDE5).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_u C) T HAR Huin Fceil) as (Hu0 & Hu1 & Hu2 & Hu3).
pose proof (rh_apart_3 _ _ _ _ _ _ _ _ C p1 x1 h1 u1 f1 0%nat 3%nat _ _ HC N0 N3 ltac:(lia)) as A03. cbn [fst snd] in A03. change (req_size CHT_SIZE) with 48 in A03.
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_LH false [(5%bv, SLit 1); (15%bv, SOff 32 44); (16%bv, SOff 32 8); (17%bv, SOff 32 16); (20%bv, SOff 32 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [ck 160 (SOff 54 0); ck 168 (SOff 55 0); ck 176 (SOff 56 0)] [ck 296 (SOff 57 0)] [uj_reg 1] [(58%nat, mkAF 4096 140737479966720 0)] [] [(UJE, SOff 58 0)] [mkSHE 58 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) p1 x1 (ht_cnt K) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G5. reflexivity.
- rewrite G15. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G16. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G17. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G20. symmetry. rewrite (denot_off E 32 tb 0 E32 ltac:(clear - Htb4096 Htbceil C1; lia)), Z.add_0_r. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold ck.
- apply (chunk_ok_val trasegs E _ s1v 160 8 _ Tn); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | clear - Tn2; lia | lia | exact S160].
- apply (chunk_ok_val trasegs E _ s1v 168 8 _ f1); [rewrite (denot_off E 55 f1 0 E55 ltac:(clear - Pf; lia)), Z.add_0_r; reflexivity | clear - Pf; lia | lia | exact S168].
- apply (chunk_ok_val trasegs E _ s1v 176 8 _ h1); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | clear - Ph; lia | lia | exact S176]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ u1); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | clear - Pu; lia | lia | exact S296]. }
{ exact SIDE1. }
{ intros e [<- | []]. rewrite SIDE2. cbn [fst snd]. split; [clear - Hj Hu2 Hu3; lia | clear - Hj A03 Hu3; lia]. }
{ cbn [map zpairwise_disjoint zall_disjoint]. repeat split. }
{ exact SIDE3. }
{ exact I. }
{ exact SIDE4. }
{ exact SIDE5. }
assert (HAE : env_agree 59 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_col_hash.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 59 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ _ _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | []] & Hr). cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val uj_reg] in Hr. clear - Hr. lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 59 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [21; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 59 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 59 E Ex e HAE1 Hat); exact Dv);
assert (SLOT : forall idx lo hi cs off e v, nth_error (ss_mem ssx) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs) -> In (ck off e) cs ->
sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 59 e = true -> 0 <= v < 2 ^ 64 -> val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + off) 8 v)
by (intros idx lo hi cs off e v Hnth Hin Dv Hat Hv;
apply (hk_slot_of_state s1v Ex ssx ms (w_H W) idx lo hi lo hi cs off e v HS Hnth Hin);
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (sv_denot_agree 59 E Ex e HAE1 Hat); exact Dv | exact Hv]);
assert (DA : forall n z, (n < 59)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
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
destruct HNw as (HarrK & HlensK & HTK).
destruct (rehash_step_used (ac_H C) (ac_ent C) Hinv K j HinvK Hj ltac:(rewrite Hcase; clear; lia) ltac:(rewrite HTK; fold Tn; clear - Hcnt Tn1; lia)) as (h2 & Hfs & Hh2 & Hfree & Hcle & Hins).
assert (Hin_h : In (ac_h C, 3 * T) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; exact (nth_error_In _ _ N2)).
destruct (hk_blk_low B LAWS s1v lyc Sc W mem md (ac_h C) (3 * T) HAR Hin_h Fceil) as (Hh0 & Hh1 & Hh2' & Hh3).
assert (E34' : ew E 34 = Z_to_bv 64 (ac_h C)) by exact E34.
assert (DH : sv_denot E (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_AND (SOff 27 0) (SLit 4294967295))) = Z_to_bv 64 (ac_h C + 3 * j))
by (apply (D_h3j E (ac_h C) (3 * j) E34 E27); [clear - Hj RT; lia | exact Hh0 | clear - Hj Hh2' Hh3 C1; lia]).
exists h2. split; [exact HCM'|]. split; [split; [exact HinvK|]; split; [exact Hj|]; split; [exact Hcase|]; split; [exact Hfs|]; split; [exact Hh2|]; split; [exact Hfree|]; split; [exact Hcle | exact Hins]|].
split.
{ unfold rh_used_regs. rewrite (HKR 21%bv ltac:(cbv; clear; tauto)), (HKR 26%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)).
split; [apply (RD 20%bv _ (3 * j) eq_refl (D_and32 E 27 (3 * j) E27 ltac:(clear - Hj RT; lia)) eq_refl)|]. split; [exact G21|].
split; [apply (RD 22%bv (SOff 56 0) h1 eq_refl); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact G26 | exact G27]. }
split; [exact (RD 24%bv _ (ac_h C + 3 * j) eq_refl DH eq_refl)|].
split; [apply (RD 10%bv (SAlu ALU_ADD (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_AND (SOff 27 0) (SLit 4294967295))) (SLit 0)) (ac_h C + 3 * j) eq_refl); [rewrite denot_add0; exact DH | reflexivity]|].
split; [apply (RD 11%bv (SOff 56 0) h1 eq_refl); [rewrite (denot_off E 56 h1 0 E56 ltac:(clear - Ph; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [apply (RD 12%bv (SOff 57 0) u1 eq_refl); [rewrite (denot_off E 57 u1 0 E57 ltac:(clear - Pu; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [apply (RD 13%bv (SOff 54 0) Tn eq_refl); [rewrite (denot_off E 54 Tn 0 E54 ltac:(clear - Tn2; lia)), Z.add_0_r; reflexivity | reflexivity]|].
split; [exact (RD 14%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit HL_CHR) HL_CHR eq_refl eq_refl eq_refl)].
Qed.
End c.

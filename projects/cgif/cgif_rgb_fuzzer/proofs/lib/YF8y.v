(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8w YF8x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YL02 YL07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kStackSpan, t_unwinding, TFX_IMG_END, UNW_STK, BST_SIZE, TFX_TP, TFX_TSD, zcanon, M64 in *.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section g. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (this pc0 bp ra0 nfp0 : Z) (ch : list (Z * Z * Z)).
#[local] Notation Hd := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (bv_unsigned (getr regs 2%bv)).
#[local] Notation T := (ly_T ly).
#[local] Notation C := (ly_C ly).
#[local] Notation top := (ly_top ly).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypotheses (R10 : getr regs 10%bv = Z_to_bv 64 this) (R11 : getr regs 11%bv = Z_to_bv 64 pc0) (R12 : getr regs 12%bv = Z_to_bv 64 bp)
(R13 : getr regs 13%bv = Z_to_bv 64 0) (R14 : getr regs 14%bv = Z_to_bv 64 1) (R15 : getr regs 15%bv = Z_to_bv 64 30)
(R4 : getr regs 4%bv = Z_to_bv 64 TFX_TP) (Hra : YK0s.ret_ok (getr regs 1%bv)) (Hpc0 : 0 <= pc0 < 2 ^ 64).
Hypotheses (V_inited : val_mem tfxsegs m0 (0xaae98 + D_10c0) 1 1) (V_tsdk1 : val_mem tfxsegs m0 (0xa9a20 + D_10c0) 1 1) (V_tsdk2 : val_mem tfxsegs m0 (0xa9a24 + D_10c0) 4 0)
(V_tp : val_mem tfxsegs m0 (TFX_TP - 88) 8 TFX_TSD) (V_tsd : val_mem tfxsegs m0 TFX_TSD 8 C)
(V_ctx : val_mem tfxsegs m0 (C + 152) 8 T) (V_t40 : val_mem tfxsegs m0 (T + 40) 1 0)
(V_t8 : val_mem tfxsegs m0 (T + 8) 8 top) (V_t16 : val_mem tfxsegs m0 (T + 16) 8 (ly_bot ly))
(V_unw : val_mem tfxsegs m0 (T + t_unwinding) 1 0) (P_unw : apresent Hd mem (T + t_unwinding))
(V_psz1 : val_mem tfxsegs m0 (0xa2140 + D_10f0) 8 (0x139c60 + D_10c0)) (V_psz2 : val_mem tfxsegs m0 (0x139c60 + D_10c0) 8 4096).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hsplo : ly_stk_lo ly <= sp - UNW_STK) (P_stk : forall a, sp - UNW_STK <= a < sp -> apresent Hd mem a)
(Hthis8 : this mod 8 = 0) (Hthislo : ly_stk_lo ly <= this) (Hthis_sp : this + BST_SIZE <= sp - UNW_STK \/ sp <= this)
(P_this : forall a, this <= a < this + BST_SIZE -> apresent Hd mem a)
(Hthis_bp : this + BST_SIZE <= bp - 16) (Hsp_bp : sp <= bp - 16) (Hbot_bp : ly_bot ly < bp) (Hbp_hi : bp <= ly_stk_hi ly) (Hbp8 : bp mod 8 = 0)
(Hra0 : rdword (aview tfxsegs Hd mem) (bp - 8) = Some ra0) (Hnfp0 : rdword (aview tfxsegs Hd mem) (bp - 16) = Some nfp0)
(Hra0_4096 : 4096 <= ra0).
Hypothesis Hch : if bp + 16 <? top
then (if bad_next bp top nfp0 then ch = [] else bp + 16 <= nfp0 /\ fpchain (rdword (aview tfxsegs Hd mem)) nfp0 top ch)
else ch = [].
Lemma T_high : in_app T kThreadObjSize.
Proof. pose proof (lo_app ly LY) as HH. unfold owned_extents in HH. do 2 apply Forall_inv_tail in HH. apply Forall_inv in HH. img_exact HH. Qed.
Lemma C_high : in_app C 256.
Proof. pose proof (lo_app ly LY) as HH. unfold owned_extents in HH. do 6 apply Forall_inv_tail in HH. apply Forall_inv in HH. img_exact HH. Qed.
Lemma TC_disj : (T + kThreadObjSize <= C \/ C + 256 <= T) /\ (T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(C + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= C).
Proof.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & D3 & _ & _ & _ & D7 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3)))) as X1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3)))))) as X2.
pose proof (Forall_inv (Forall_inv_tail D7)) as X3. unfold zdisjoint in X1, X2, X3. cbn [fst snd] in X1, X2, X3.
split; [img_try (img_exact X1) | img_try (split; [img_exact X2 | img_exact X3])].
Qed.
Lemma top_facts : ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < top <= ly_stk_hi ly /\ top mod 4096 = 0 /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof. pose proof (lo_top ly LY) as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold page_aligned in A3. repeat split; try assumption; img_apply A2. Qed.
Lemma bot_eq : ly_bot ly = top - kStackSpan. Proof. img_refl. Qed.
Lemma T_zone : zone3 T kThreadObjSize.
Proof.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & D3 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3))))))) as X.
img_exact (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (unfold kThreadObjSize; img_lia)) T_high X).
Qed.
Lemma C_zone : zone3 C 256.
Proof.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & _ & _ & _ & _ & D7 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail D7))) as X.
img_exact (zone3_intro ly C 256 IMG ltac:(img_lia) C_high X).
Qed.
Ltac zoneTC := pose proof T_zone as TZ; pose proof C_zone as CZ;
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in TZ, CZ.
Lemma T_off : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img T kThreadObjSize a T_zone Ha). Qed.
Lemma unw_off : off_img (T + t_unwinding).
Proof. img_apply T_off. unfold t_unwinding, kThreadObjSize. img_lia. Qed.
Lemma zone_facts :
0x10007fff8000 <= ly_stk_lo ly /\ ly_stk_lo ly <= top - 8388608 /\ top <= ly_stk_hi ly /\ ly_stk_hi ly <= 0x800000000000 /\
4096 <= T /\ T + 4096 <= 140737479966720 /\ 4096 <= C /\ C + 256 <= 140737479966720 /\
(T + 4096 <= C \/ C + 256 <= T) /\ (T + 4096 <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (C + 256 <= ly_stk_lo ly \/ ly_stk_hi ly <= C) /\
ly_stk_lo ly <= sp - 144 /\ sp <= bp - 16 /\ ly_stk_lo ly <= this /\ this + 2064 <= bp - 16 /\ (this + 2064 <= sp - 144 \/ sp <= this) /\
top - 8388608 < bp /\ bp <= ly_stk_hi ly.
Proof.
pose proof T_high as [B1 B2]. pose proof C_high as [B3 B4]. pose proof TC_disj as (B5 & B6 & B7). pose proof top_facts as (B8 & B9 & B10 & B11 & B12).
pose proof Hsplo as C1. pose proof Hsp_bp as C2. pose proof Hthislo as C3. pose proof Hthis_bp as C4. pose proof Hthis_sp as C5.
pose proof Hbot_bp as C6. pose proof Hbp_hi as C7.
clear - B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 C1 C2 C3 C4 C5 C6 C7.
ceil; unfold in_app, ly_bot, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL, kThreadObjSize, kStackSpan, UNW_STK, BST_SIZE in *.
repeat split; img_lia.
Qed.
Ltac zone := pose proof zone_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18).
Definition XW : list word := [Z_to_bv 64 T; Z_to_bv 64 C; Z_to_bv 64 top; Z_to_bv 64 nfp0; Z_to_bv 64 ra0].
Definition E0 : env := Ereg regs XW.
Lemma EaT : ew E0 aT = Z_to_bv 64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 aC = Z_to_bv 64 C. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 aTOP = Z_to_bv 64 top. Proof. img_refl. Qed.
Lemma EaNFP : ew E0 aNFP = Z_to_bv 64 nfp0. Proof. img_refl. Qed.
Lemma EaRA : ew E0 aRA = Z_to_bv 64 ra0. Proof. img_refl. Qed.
Lemma EaT' : ew E0 32 = Z_to_bv 64 T. Proof. img_refl. Qed.
Lemma EaC' : ew E0 33 = Z_to_bv 64 C. Proof. img_refl. Qed.
Lemma EaTOP' : ew E0 34 = Z_to_bv 64 top. Proof. img_refl. Qed.


Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs XW k r Hk). Qed.
Lemma E1 : ew E0 1 = getr regs 1%bv. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E2 : ew E0 2 = getr regs 2%bv. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = Z_to_bv 64 this. Proof. rewrite <- R10. img_exact (Er 10 10%bv eq_refl). Qed.
Lemma E11 : ew E0 11 = Z_to_bv 64 pc0. Proof. rewrite <- R11. img_exact (Er 11 11%bv eq_refl). Qed.
Lemma E12 : ew E0 12 = Z_to_bv 64 bp. Proof. rewrite <- R12. img_exact (Er 12 12%bv eq_refl). Qed.
Lemma nfp0_range : 0 <= nfp0 < 2 ^ 64. Proof. img_exact (rdword_range _ _ _ _ Hnfp0). Qed.
Lemma ra0_range : 0 <= ra0 < 2 ^ 64. Proof. img_exact (rdword_range _ _ _ _ Hra0). Qed.
Lemma sp_range : 0 <= sp < 2 ^ 64. Proof. img_apply u64_range. Qed.
Ltac evals := rewrite ?EaT, ?EaC, ?EaTOP, ?EaNFP, ?EaRA, ?E2, ?E10, ?E11, ?E12, ?E1.
#[local] Notation msU0 := (mkst regs (Z_to_bv 64 A_UnwindImpl) mem (seg_rom tfxsegs)).
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) UMEM0.
Proof.
zone. pose proof nfp0_range as NR. pose proof ra0_range as RR. pose proof Hpc0 as PR. pose proof sp_range as SR.
unfold UMEM0, UCONST, R_S, R_O1a0, R_O1b0, R_O2, R_F, R_C, R_T1, R_T2, lit1, lit4, lit8. cbn [app].
img_apply Forall_cons. { img_apply (region_ok_stack tfxsegs E0 m0 2 sp (- UNW_STK)); [img_try (rewrite E2; img_refl) | img_try (clear - Z1 Z12; numconst; img_lia) | img_try (clear - SR; img_lia) |].
intros a Ha. img_apply apresent_writable; [img_try (clear - Ha Z1 Z12 SR; numconst; img_lia) | img_try (img_apply P_stk; img_exact Ha)]. }
img_apply Forall_cons. { img_apply (region_ok_window E0 m0 10 this); [img_try (rewrite E10; img_apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)
| img_try (clear - Z1 Z14; numconst; img_lia) | img_try (clear - Z15 Z18 Z4; numconst; img_lia) |].
intros a Ha. img_apply apresent_writable; [img_try (clear - Ha Z1 Z14 Z15 Z18 Z4; numconst; img_lia) | img_try (img_apply P_this; clear - Ha; numconst; img_lia)]. }
img_apply Forall_cons. { img_apply (region_ok_window E0 m0 10 this); [img_try (rewrite E10; img_apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)
| img_try (clear - Z1 Z14; numconst; img_lia) | img_try (clear - Z15 Z18 Z4; numconst; img_lia) |].
intros a Ha. img_apply apresent_writable; [img_try (clear - Ha Z1 Z14 Z15 Z18 Z4; numconst; img_lia) | img_try (img_apply P_this; clear - Ha; numconst; img_lia)]. }
img_apply Forall_cons. { img_apply (region_ok_window E0 m0 10 this); [img_try (rewrite E10; img_apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)
| img_try (clear - Z1 Z14; numconst; img_lia) | img_try (clear - Z15 Z18 Z4; numconst; img_lia) |].
intros a Ha. img_apply apresent_writable; [img_try (clear - Ha Z1 Z14 Z15 Z18 Z4; numconst; img_lia) | img_try (img_apply P_this; clear - Ha; numconst; img_lia)]. }
img_apply Forall_cons. {   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E12, unsigned_lit_small by (img_try (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia)).
split; [img_try (clear - Z1 Z2 Z17; numconst; img_lia)|]. split; [img_try (clear - Z18 Z4; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_cons; [| img_apply Forall_nil])].
- eapply (chunk_ok_val tfxsegs E0 m0 bp (-16) 8 (SOff aNFP 0) nfp0); [img_try (cbn [sv_denot]; rewrite EaNFP, unsigned_lit_small by img_exact NR; f_equal; img_lia) | img_try (img_exact NR) | img_try (clear; numconst; cbn; img_lia) |].
replace (bp + -16) with (bp - 16) by img_lia. img_exact (val_mem_of_rdword tfxsegs _ _ _ _ Hnfp0).
- eapply (chunk_ok_val tfxsegs E0 m0 bp (-8) 8 (SOff aRA 0) ra0); [img_try (cbn [sv_denot]; rewrite EaRA, unsigned_lit_small by img_exact RR; f_equal; img_lia) | img_try (img_exact RR) | img_try (clear; numconst; cbn; img_lia) |].
replace (bp + -8) with (bp - 8) by img_lia. img_exact (val_mem_of_rdword tfxsegs _ _ _ _ Hra0). }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0xaae98 + D_10c0) 1 1 V_inited); clear; numconst; cbn; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0xa9a20 + D_10c0) 1 1 V_tsdk1); clear; numconst; cbn; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0xa9a24 + D_10c0) 4 0 V_tsdk2); clear; numconst; cbn; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (TFX_TP - 88) 8 TFX_TSD V_tp); clear; numconst; cbn; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_atom8 E0 m0 TFX_TSD aC C V_tsd EaC); clear - Z7 Z8; numconst; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0xa2140 + D_10f0) 8 (0x139c60 + D_10c0) V_psz1); clear; numconst; cbn; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0x139c60 + D_10c0) 8 4096 V_psz2); clear; numconst; cbn; img_lia. }
img_apply Forall_cons. {   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite EaC, unsigned_lit_small by (img_try (clear - Z7 Z8; numconst; img_lia)).
split; [img_try (clear - Z7; numconst; img_lia)|]. split; [img_try (clear - Z8; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E0 m0 C 152 8 (SOff aT 0) T); [img_try (cbn [sv_denot]; rewrite EaT, unsigned_lit_small by (clear - Z5 Z6; numconst; img_lia); f_equal; img_lia)
| img_try (clear - Z5 Z6; numconst; img_lia) | img_try (clear; numconst; cbn; img_lia) | img_try (img_exact V_ctx)]. }
img_apply Forall_cons. {   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite EaT, unsigned_lit_small by (img_try (clear - Z5 Z6; numconst; img_lia)).
split; [img_try (clear - Z5; numconst; img_lia)|]. split; [img_try (clear - Z6; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply Forall_nil]])].
- eapply (chunk_ok_val tfxsegs E0 m0 T 8 8 (SOff aTOP 0) top); [img_try (cbn [sv_denot]; rewrite EaTOP, unsigned_lit_small by (clear - Z1 Z2 Z3 Z4; numconst; img_lia); f_equal; img_lia)
| img_try (clear - Z1 Z2 Z3 Z4; numconst; img_lia) | img_try (clear; numconst; cbn; img_lia) | img_try (img_exact V_t8)].
- eapply (chunk_ok_val tfxsegs E0 m0 T 16 8 (SOff aTOP (- kStackSpan)) (top - kStackSpan));
[img_try (cbn [sv_denot]; rewrite EaTOP, unsigned_lit_small by (clear - Z1 Z2 Z3 Z4; numconst; img_lia); f_equal; img_lia)
| img_try (clear - Z1 Z2 Z3 Z4; numconst; img_lia) | img_try (clear; numconst; cbn; img_lia) | img_try (rewrite <- bot_eq; img_exact V_t16)].
- eapply (chunk_ok_val tfxsegs E0 m0 T 40 1 (SLit 0) 0); [img_refl | img_try (clear; numconst; cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_exact V_t40)]. }
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
{   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite EaT, unsigned_lit_small by (img_try (clear - Z5 Z6; numconst; img_lia)).
split; [img_try (clear - Z5; numconst; img_lia)|]. split; [img_try (clear - Z6; numconst; img_lia)|]. split.
{ intros o Ho. replace (T + o) with (T + t_unwinding) by (img_try (clear - Ho; img_lia)). img_apply apresent_writable_off; [img_try (img_exact unw_off) | img_try (img_exact P_unw)]. }
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E0 m0 T t_unwinding 1 (SLit 0) 0); [img_refl | img_try (clear; numconst; cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_exact V_unw)]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 UMEM0.
Proof.
zone. pose proof sp_range as SR.
img_apply pairwise_disjoint_of_extents. unfold UMEM0, UCONST, R_S, R_O1a0, R_O1b0, R_O2, R_F, R_C, R_T1, R_T2, lit1, lit4, lit8, atom8, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2, E10, E12, EaT, EaC. rewrite !unsigned_lit_small by (img_try (clear - Z1 Z2 Z4 Z5 Z6 Z7 Z8 Z14 Z15 Z17 Z18; numconst; img_lia)).
zoneTC.
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 SR TZ CZ.
numconst. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; img_lia.
Qed.
Lemma FACTS_ok : facts_ok E0 UF0.
Proof.
zone. pose proof nfp0_range as NR. pose proof ra0_range as RR. pose proof Hpc0 as PR. pose proof sp_range as SR.
pose proof top_facts as (_ & _ & TA & _). pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL. unfold page_aligned in TAL.
pose proof Hsp16 as A16. pose proof Hthis8 as A8. pose proof Hbp8 as B8. pose proof Hra0_4096 as RA.
assert (AF : forall k X lo hi al, ew E0 k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (E2' : ew E0 2 = Z_to_bv 64 sp) by (img_try (rewrite E2; symmetry; img_apply Z_to_bv_bv_unsigned)).
split; [| img_try (split; [| img_exact I])].
- unfold UF0, UF_atoms. cbn [f_atoms atoms_ok]. unfold aT, aC, aTOP, aNFP, aRA.
split. { img_apply (AF 2%nat sp _ _ _ E2'); clear - SR Z1 Z12 Z13 Z18 Z4 A16; [img_lia | img_try (numconst; img_lia) | img_try (img_exact A16) | img_lia]. }
split. { img_apply (AF 10%nat this _ _ _ E10); clear - Z1 Z14 Z15 Z18 Z4 A8; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact A8) | img_lia]. }
split. { img_apply (AF 11%nat pc0 _ _ _ E11); clear - PR; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 12%nat bp _ _ _ E12); clear - Z1 Z2 Z17 Z18 Z4 B8; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact B8) | img_lia]. }
split. { img_apply (AF 32%nat T _ _ _ EaT); clear - Z5 Z6 TAL; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact TAL) | img_lia]. }
split. { img_apply (AF 33%nat C _ _ _ EaC); clear - Z7 Z8 CAL; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact CAL) | img_lia]. }
split. { img_apply (AF 34%nat top _ _ _ EaTOP); clear - Z1 Z2 Z3 Z4 TA; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact TA) | img_lia]. }
split. { img_apply (AF 35%nat nfp0 _ _ _ EaNFP); clear - NR; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
split; [| img_try (img_exact I)]. { img_apply (AF 36%nat ra0 _ _ _ EaRA); clear - RR RA; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
-   unfold UF0, UF_conds. cbn [f_conds conds_ok]. split; [| img_try (img_exact I)].
unfold acond_ok. cbn [ac_c ac_a ac_b]. unfold branch_taken, bv_ltu. rewrite !denot_SOff, EaTOP, E12.
rewrite !unsigned_lit_small by (img_try (clear - Z1 Z2 Z3 Z4 Z17 Z18; numconst; img_lia)). unfold zcanon.
rewrite !Z.mod_small by (img_try (clear - Z1 Z2 Z3 Z4 Z17 Z18; numconst; img_lia)).
img_apply Z.ltb_lt. clear - Z17. numconst. img_lia.
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 SS_U0 (restrict Hd msU0).
Proof.
rewrite restrict_mkst_fx. unfold SS_U0, UREGS0. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact R15)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact R14)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact R13)].
img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact R4)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- img_exact FACTS_ok.
Qed.
Definition WINX (a : Z) : Prop :=
(sp - UNW_STK <= a < sp) \/ (this + 8 <= a < this + 12) \/ (this + 16 <= a < this + 24) \/ (this + 2056 <= a < this + BST_SIZE) \/
(T + t_unwinding <= a < T + t_unwinding + 1).
Definition WINQ (q a : Z) : Prop := WINX a \/ (q <= a < q + 8).
Definition WIN (a : Z) : Prop := WINX a \/ (this + 24 <= a < this + 16 + 8 * 30).
Definition WSKX : list (option nat * Z * Z) :=
[(Some 2%nat, - UNW_STK, 0); (Some 10%nat, 8, 12); (Some 10%nat, 16, 24); (Some 10%nat, 2056, 2064); (Some aT, t_unwinding, t_unwinding + 1)].
Definition WSK : list (option nat * Z * Z) := WSKX ++ [(Some aQ, 0, 8)].
Definition wsk_ok (sk : list (option nat * Z * Z)) (rs : smem) : bool :=
forallb (fun t => existsb (win_eqb t) sk || (snd t <=? snd (fst t))) (windows rs).
Definition envU (E : env) : Prop := forall k, (k < 35)%nat -> ew E k = ew E0 k.
Lemma windows_WINQ : forall E rs a, envU E -> wsk_ok WSK rs = true -> in_wrange E rs a -> WINQ (bv_unsigned (ew E aQ)) a.
Proof.
intros E rs a HE Hb Hw. zone.
destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. exfalso. clear - Hr Ht. img_lia. }
unfold WSK, WSKX in Ht. cbn [existsb app] in Ht. unfold WINQ, WINX.
repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
- rewrite (HE 2%nat ltac:(img_lia)), E2 in Hr. clear - Hr. img_lia.
- rewrite (HE 10%nat ltac:(img_lia)), E10, unsigned_lit_small in Hr by (img_try (clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). clear - Hr. img_lia.
- rewrite (HE 10%nat ltac:(img_lia)), E10, unsigned_lit_small in Hr by (img_try (clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). clear - Hr. img_lia.
- rewrite (HE 10%nat ltac:(img_lia)), E10, unsigned_lit_small in Hr by (img_try (clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). clear - Hr. numconst. img_lia.
- unfold aT in Hr. rewrite (HE 32%nat ltac:(img_lia)) in Hr. img_change (ew E0 32) with (ew E0 aT) in Hr. rewrite EaT, unsigned_lit_small in Hr by (img_try (clear - Z5 Z6; numconst; img_lia)).
clear - Hr. img_lia.
- unfold aQ in Hr |- *. clear - Hr. img_lia.
- discriminate Ht.
Qed.
Lemma windows_WINX : forall E rs a, envU E -> wsk_ok WSKX rs = true -> in_wrange E rs a -> WINX a.
Proof.
intros E rs a HE Hb Hw. zone.
destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. exfalso. clear - Hr Ht. img_lia. }
unfold WSKX in Ht. cbn [existsb] in Ht. unfold WINX.
repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
- rewrite (HE 2%nat ltac:(img_lia)), E2 in Hr. clear - Hr. img_lia.
- rewrite (HE 10%nat ltac:(img_lia)), E10, unsigned_lit_small in Hr by (img_try (clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). clear - Hr. img_lia.
- rewrite (HE 10%nat ltac:(img_lia)), E10, unsigned_lit_small in Hr by (img_try (clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). clear - Hr. img_lia.
- rewrite (HE 10%nat ltac:(img_lia)), E10, unsigned_lit_small in Hr by (img_try (clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). clear - Hr. numconst. img_lia.
- unfold aT in Hr. rewrite (HE 32%nat ltac:(img_lia)) in Hr. img_change (ew E0 32) with (ew E0 aT) in Hr. rewrite EaT, unsigned_lit_small in Hr by (img_try (clear - Z5 Z6; numconst; img_lia)).
clear - Hr. img_lia.
- discriminate Ht.
Qed.
Lemma WINQ_WIN : forall q a, this + 24 <= q -> q + 8 <= this + 16 + 8 * 30 -> WINQ q a -> WIN a.
Proof. intros q a HQ1 HQ2 [Hx | Hq]; [img_try (left; img_exact Hx) | img_try (right)]. clear - HQ1 HQ2 Hq. img_lia. Qed.
Lemma WINX_WIN : forall a, WINX a -> WIN a.
Proof. intros a Hx. left. img_exact Hx. Qed.
Lemma WIN_off : forall a, WIN a -> off_img a.
Proof.
intros a Ha. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne]; [img_try (img_exact unw_off)|]. right.
zone. pose proof sp_range as SR. unfold WIN, WINX in Ha. clear - Ha Hne Z1 Z12 Z13 Z14 Z15 Z4 Z18 SR. numconst. img_lia.
Qed.
Lemma pres_after_run_off : forall E ss' rs (ms ms' : machine_state),
st_ok tfxsegs E ss' (restrict Hd ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
(forall a, in_wrange E rs a -> off_img a) ->
forall a, apresent Hd (ms_mem ms) a -> apresent Hd (ms_mem ms') a.
Proof.
clear - W. intros E ss' rs ms ms' HS HF Hws Hhi a Ha.
set (x := Z_to_bv 64 a). assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by img_apply Z_to_bv_bv_unsigned.
destruct (in_wrangeb E (ss_mem ss') (bv_unsigned x)) eqn:Hb.
- destruct (in_wrangeb_true E _ _ Hb) as (i & r & Hi & Hr).
assert (P : apresent Hd (ms_mem ms') (bv_unsigned x)).
{ img_apply (st_ok_window_apresent_off Hd E ss' ms' i r _ HS Hi Hr). img_apply Hhi.
img_apply (in_wrange_of_windows E (ss_mem ss') rs); [img_try (symmetry; img_exact Hws)|]. exists r. split; [img_try (img_exact (nth_error_In _ _ Hi)) | img_try (img_exact Hr)]. }
unfold apresent in P |- *. rewrite Ex in P. img_exact P.
- img_apply (apresent_same Hd (ms_mem ms)); [| img_try (img_exact Ha)]. img_apply (HF x). intros Hw.
img_exact (in_wrangeb_false E _ _ Hb (in_wrange_of_windows E rs (ss_mem ss') _ Hws Hw)).
Qed.
Lemma frame_WINQ : forall E rs (m m' : word -> option byte),
envU E -> wsk_ok WSK rs = true -> frame_of E rs m m' -> forall x : word, ~ WINQ (bv_unsigned (ew E aQ)) (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WINQ E rs _ HE Hb Hw). Qed.
Lemma frame_WINX : forall E rs (m m' : word -> option byte),
envU E -> wsk_ok WSKX rs = true -> frame_of E rs m m' -> forall x : word, ~ WINX (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WINX E rs _ HE Hb Hw). Qed.
Lemma pres_runQ : forall E ss' rs (ms ms' : machine_state),
envU E -> this + 24 <= bv_unsigned (ew E aQ) -> bv_unsigned (ew E aQ) + 8 <= this + 16 + 8 * 30 -> wsk_ok WSK rs = true ->
st_ok tfxsegs E ss' (restrict Hd ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
forall a, apresent Hd (ms_mem ms) a -> apresent Hd (ms_mem ms') a.
Proof.
intros E ss' rs ms ms' HE HQ1 HQ2 Hb HS HF Hws. img_apply (pres_after_run_off E ss' rs ms ms' HS HF Hws).
intros a Ha. img_apply WIN_off. img_apply (WINQ_WIN _ a HQ1 HQ2). img_exact (windows_WINQ E _ a HE Hb Ha).
Qed.
Lemma pres_runX : forall E ss' rs (ms ms' : machine_state),
envU E -> wsk_ok WSKX rs = true ->
st_ok tfxsegs E ss' (restrict Hd ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
forall a, apresent Hd (ms_mem ms) a -> apresent Hd (ms_mem ms') a.
Proof.
intros E ss' rs ms ms' HE Hb HS HF Hws. img_apply (pres_after_run_off E ss' rs ms ms' HS HF Hws).
intros a Ha. img_apply WIN_off. img_apply WINX_WIN. img_exact (windows_WINX E _ a HE Hb Ha).
Qed.
Definition TR : list Z := if bp + 16 <? top then unwind_of_chain pc0 ((bp, ra0, nfp0) :: ch) else [pc0].
Definition UPOST : world tfxsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1%bv) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - UNW_STK <= bv_unsigned x < sp) -> ~ (this + 8 <= bv_unsigned x < this + 12) ->
~ (this + 16 <= bv_unsigned x < this + 16 + 8 * 30) -> ~ (this + 2056 <= bv_unsigned x < this + BST_SIZE) ->
mem' x = mem x) /\
(forall a, apresent Hd mem a -> apresent Hd mem' a) /\
val_mem tfxsegs (mrestrict Hd mem') (this + 8) 4 (Z.of_nat (length TR)) /\
(forall i, (i < length TR)%nat -> val_mem tfxsegs (mrestrict Hd mem') (this + 16 + 8 * Z.of_nat i) 8 (nth i TR 0)) /\
val_mem tfxsegs (mrestrict Hd mem') (this + 2056) 8 bp.
Definition INV (m : word -> option byte) (acc : list Z) : Prop :=
(forall x : word, ~ WIN (bv_unsigned x) -> m x = mem x) /\
(forall a, apresent Hd mem a -> apresent Hd m a) /\
(1 <= length acc <= 30)%nat /\ nth 0 acc 0 = pc0 /\
(forall i, (1 <= i < length acc)%nat -> val_mem tfxsegs (mrestrict Hd m) (this + 16 + 8 * Z.of_nat i) 8 (nth i acc 0)).
Lemma unw_byte_same : forall (m' : word -> option byte),
val_mem tfxsegs (mrestrict Hd m') (T + t_unwinding) 1 0 -> m' (Z_to_bv 64 (T + t_unwinding)) = mem (Z_to_bv 64 (T + t_unwinding)).
Proof.
intros m' Hv. zone. pose proof P_unw as [Hh _].
pose proof (V_unw 0%nat ltac:(img_lia)) as A. pose proof (Hv 0%nat ltac:(img_lia)) as B. rewrite Z.add_0_r in A, B.
unfold mbyte in A, B. unfold mrestrict in A, B. rewrite Hh in A, B.
rewrite (seg_rom_none_off (T + t_unwinding) unw_off) in A, B.
destruct (m' (Z_to_bv 64 (T + t_unwinding))) as [b'|]; [|img_try (discriminate B)].
destruct (mem (Z_to_bv 64 (T + t_unwinding))) as [b|]; [|img_try (discriminate A)]. congruence.
Qed.
Lemma exit_ok : forall E ms mat acc,
st_ok tfxsegs E S_X (restrict Hd ms) -> envU E -> INV (ms_mem ms) acc -> bv_unsigned (ew E aZ) = Z.of_nat (length acc) -> acc = TR ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) UPOST.
Proof.
intros E ms mat acc HS HE HI IL Hacc. pose proof Hwx_tfa as Hwx. zone. symmetry in IL.
pose proof HE as HEk. pose proof HI as (IF & IP & IL2 & I0 & IT).
srr_run_with tfxtbl_rtA_ok HS.
eapply (SRr_ret_at tfxsegs tfxtbl_rtA tfxtbl_rtA_ok Hwx W); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_collapse. split; [img_refl|].
lazymatch goal with |- context [mkst (ms_regs ?msf) _ (ms_mem _) _] =>
exists (ms_regs msf), (ms_mem msf), mat' end.
rreg HS (1%bv : bv 5) Q1. rewrite (HEk 1%nat ltac:(img_lia)), E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { img_apply regs_preserved_intro.
- rreg HS (2%bv : bv 5) Q. rewrite Q, (HEk 2%nat ltac:(img_lia)). img_exact E2.
- rreg HS (3%bv : bv 5) Q. rewrite Q, (HEk 3%nat ltac:(img_lia)). img_exact (Er 3 3%bv eq_refl).
- rreg HS (4%bv : bv 5) Q. rewrite Q. symmetry. img_exact R4.
- rreg HS (8%bv : bv 5) Q. rewrite Q, (HEk 8%nat ltac:(img_lia)). img_exact (Er 8 8%bv eq_refl).
- rreg HS (9%bv : bv 5) Q. rewrite Q, (HEk 9%nat ltac:(img_lia)). img_exact (Er 9 9%bv eq_refl).
- rreg HS (18%bv : bv 5) Q. rewrite Q, (HEk 18%nat ltac:(img_lia)). img_exact (Er 18 18%bv eq_refl).
- rreg HS (19%bv : bv 5) Q. rewrite Q, (HEk 19%nat ltac:(img_lia)). img_exact (Er 19 19%bv eq_refl).
- rreg HS (20%bv : bv 5) Q. rewrite Q, (HEk 20%nat ltac:(img_lia)). img_exact (Er 20 20%bv eq_refl).
- rreg HS (21%bv : bv 5) Q. rewrite Q, (HEk 21%nat ltac:(img_lia)). img_exact (Er 21 21%bv eq_refl).
- rreg HS (22%bv : bv 5) Q. rewrite Q, (HEk 22%nat ltac:(img_lia)). img_exact (Er 22 22%bv eq_refl).
- rreg HS (23%bv : bv 5) Q. rewrite Q, (HEk 23%nat ltac:(img_lia)). img_exact (Er 23 23%bv eq_refl).
- rreg HS (24%bv : bv 5) Q. rewrite Q, (HEk 24%nat ltac:(img_lia)). img_exact (Er 24 24%bv eq_refl).
- rreg HS (25%bv : bv 5) Q. rewrite Q, (HEk 25%nat ltac:(img_lia)). img_exact (Er 25 25%bv eq_refl).
- rreg HS (26%bv : bv 5) Q. rewrite Q, (HEk 26%nat ltac:(img_lia)). img_exact (Er 26 26%bv eq_refl).
- rreg HS (27%bv : bv 5) Q. rewrite Q, (HEk 27%nat ltac:(img_lia)). img_exact (Er 27 27%bv eq_refl). }
assert (WOK : wsk_ok WSKX (ss_mem S_X) = true) by (img_try ((img_case; vm_compute); img_refl)).
pose proof (frame_WINX E _ _ _ HE WOK HF) as FR.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msf) =>
assert (UNW : val_mem tfxsegs (mrestrict Hd (ms_mem msf)) (T + t_unwinding) 1 0);
[ img_try (memv HS 13%nat 0%nat; [unfold aT; rewrite (HEk 32%nat ltac:(img_lia)); img_change (ew E0 32) with (ew E0 aT); rewrite EaT, unsigned_lit_small by (clear - Z5 Z6; numconst; img_lia); img_refl
| img_refl | clear; img_lia]) |] end.
assert (THIS : bv_unsigned (ew E 10) = this).
{ rewrite (HEk 10%nat ltac:(img_lia)), E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
split.
{   intros x N1 N2 N3 N4.
destruct (Z.eq_dec (bv_unsigned x) (T + t_unwinding)) as [Ex | Nx].
- rewrite <- (Z_to_bv_bv_unsigned 64 x), Ex. img_apply unw_byte_same. img_exact UNW.
- rewrite FR by (img_try (unfold WINX; clear - N1 N2 N3 N4 Nx; numconst; img_lia)).
img_apply IF. unfold WIN, WINX. clear - N1 N2 N3 N4 Nx. numconst. img_lia. }
split.
{   intros a Ha. lazymatch type of HS with st_ok _ _ ?ssf (restrict _ ?msf) =>
apply (pres_runX E ssf (ss_mem S_X) ms msf HE WOK HS HF ltac:(img_try ((img_case; vm_compute); img_refl))) end. img_apply IP. img_exact Ha. }
rewrite <- Hacc. split.
{   memv HS 0%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_try (cbn [sv_denot]; unfold aZ in IL; rewrite <- IL, Z.add_0_r; img_refl) | img_try (clear - IL2; img_lia)]. }
split.
{   intros i Hi. destruct i as [|i].
- memv HS 2%nat 0%nat; [img_try (rewrite THIS; clear; img_lia) | img_try (cbn [sv_denot]; rewrite (HEk 11%nat ltac:(img_lia)), E11, unsigned_lit_small, Z.add_0_r, I0 by img_exact Hpc0; img_refl) | img_try (rewrite I0; img_exact Hpc0)].
- eapply val_mem_frame; [| img_try (img_exact (IT (S i) ltac:(clear - Hi; img_lia)))].
intros k Hk. img_apply FR. rewrite unsigned_lit_small by (img_try (clear - Hi Hk IL2 Z1 Z14 Z15 Z18 Z4; numconst; img_lia)).
unfold WINX. clear - Hi Hk IL2 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18. numconst. img_lia. }
memv HS 3%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_try (cbn [sv_denot]; rewrite (HEk 12%nat ltac:(img_lia)), E12, unsigned_lit_small, Z.add_0_r by (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia); img_refl)
| img_try (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia)].
Qed.
Definition LT35 (j : nat) : bool := (j <? 35)%nat.
Lemma envU_havoc : forall E k ws, envU E -> (35 <= k)%nat -> envU (havoc E k ws).
Proof. intros E k ws HE Hk n Hn. rewrite ew_havoc_old by img_lia. img_exact (HE n Hn). Qed.
Lemma agree_pd_havoc : forall E k ws, (35 <= k)%nat -> env_agree_pd LT35 PT E (havoc E k ws).
Proof.
intros E k ws Hk. split; [| img_try (intros d _; rewrite ed_havoc; img_refl)].
intros n Hn. unfold LT35 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_havoc_old by img_lia. img_refl.
Qed.
Lemma LFIX_mem_ok : forall E E' ss (m : word -> option byte),
mem_ok tfxsegs E m (ss_mem ss) -> submem LFIX (ss_mem ss) -> (forall n, (n < 35)%nat -> ew E' n = ew E n) -> ed E' = ed E ->
mem_ok tfxsegs E' m LFIX.
Proof.
intros E E' ss m HM Hsub HEE HED.
img_apply (mem_ok_agree tfxsegs 35 E E'); [img_try (split; [img_exact HEE | img_exact HED]) | img_try ((img_case; vm_compute); img_refl) |].
img_apply (mem_ok_sub tfxsegs E m (ss_mem ss) LFIX Hsub); [img_try ((img_case; vm_compute); img_refl) | img_try (img_exact HM)].
Qed.
Lemma O1a_disj : forall E z, envU E -> all_disjoint E (R_O1a z) LFIX.
Proof.
intros E z HE. zone. pose proof sp_range as SR.
img_apply all_disjoint_of_extents. unfold LFIX, UCONST, R_O1a, R_S', R_O1b, R_O2', R_C, R_T1, R_T2', lit1, lit4, lit8, atom8, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite (HE 10%nat ltac:(img_lia)), (HE 2%nat ltac:(img_lia)), E2, E10. unfold aC, aT. rewrite (HE 33%nat ltac:(img_lia)), (HE 32%nat ltac:(img_lia)).
img_change (ew E0 33) with (ew E0 aC). img_change (ew E0 32) with (ew E0 aT). rewrite EaT, EaC.
rewrite !unsigned_lit_small by (img_try (clear - Z1 Z2 Z4 Z5 Z6 Z7 Z8 Z14 Z15 Z17 Z18; numconst; img_lia)).
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 SR.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Definition EX (E : env) (sz : Z) (rg : bvmap 5 word) : env :=
havoc E 38 [Z_to_bv 64 sz; Z_to_bv 64 0; getr rg 12%bv; getr rg 15%bv; getr rg 16%bv; getr rg 17%bv; getr rg 14%bv].
Lemma reabs_X : forall E ss ms sz,
st_ok tfxsegs E ss (restrict Hd ms) -> envU E -> ss_pc ss = A_EXIT ->
reabs_check LT35 ss XREGS XF = true -> submem LFIX (ss_mem ss) ->
val_mem tfxsegs (mrestrict Hd (ms_mem ms)) (this + 8) 4 sz -> 1 <= sz <= 30 ->
(forall a, this + 8 <= a < this + 12 -> apresent Hd (ms_mem ms) a) ->
st_ok tfxsegs (EX E sz (ms_regs ms)) S_X (restrict Hd ms) /\ envU (EX E sz (ms_regs ms)) /\ bv_unsigned (ew (EX E sz (ms_regs ms)) aZ) = sz.
Proof.
intros E ss ms sz HS HE Hpc Hck Hsub Hsz Hszr Hpres. zone.
set (E' := EX E sz (ms_regs ms)).
assert (HE' : envU E') by (img_try (img_apply envU_havoc; [img_try (img_exact HE) | img_lia])).
assert (EZ : ew E' aZ = Z_to_bv 64 sz) by img_refl.
assert (THIS : bv_unsigned (ew E' 10) = this).
{ rewrite (HE' 10%nat ltac:(img_lia)), E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
split; [| img_try (split; [img_exact HE' | rewrite EZ; img_apply unsigned_lit_small; clear - Hszr; img_lia])].
unfold S_X, XMEM. rewrite <- Hpc.
img_apply (st_ok_add_region E' (mkSS (ss_pc ss) XREGS LFIX None XF) (restrict Hd ms) (R_O1a (SOff aZ 0))).
- img_apply (st_ok_reabs tfxsegs LT35 E E' ss (restrict Hd ms) XREGS LFIX XF HS (agree_pd_havoc E 38 _ ltac:(img_lia)) Hck).
+ cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
assert (OB : forall (r' : bv 5) k (w : word), ew E' k = w -> getr (ms_regs ms) r' = w -> bv_unsigned r = bv_unsigned r' -> ew E' k = getr (ms_regs ms) r).
{ clear. intros r' k w H1 H2 H3. rewrite H1, <- H2. f_equal. symmetry. img_apply bv_eq. img_exact H3. }
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* img_apply (OB 12%bv 40%nat (getr (ms_regs ms) 12%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 14%bv 44%nat (getr (ms_regs ms) 14%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 15%bv 41%nat (getr (ms_regs ms) 15%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 16%bv 42%nat (getr (ms_regs ms) 16%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 17%bv 43%nat (getr (ms_regs ms) 17%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
+ assert (FO : fact_obls LT35 XF = [(aZ, mkAF 1 30 0); (aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0);
(S (S aHAV), mkAF 0 (2 ^ 64 - 1) 0); (S (S (S aHAV)), mkAF 0 (2 ^ 64 - 1) 0); (44%nat, mkAF 0 (2 ^ 64 - 1) 0)])
by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
assert (JK : forall k (r : bv 5), ew E' k = getr (ms_regs ms) r -> afact_ok E' k (mkAF 0 (2 ^ 64 - 1) 0)).
{ clear. intros k r Hk. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hk. pose proof (u64_range (getr (ms_regs ms) r)).
split; [img_lia|]. split; [img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { cbn [fst snd]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EZ, unsigned_lit_small by (img_try (clear - Hszr; img_lia)).
clear - Hszr. split; [img_lia|]. split; [img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons; [img_try (img_apply (JK _ 12%bv); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JK _ 15%bv); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JK _ 16%bv); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JK _ 17%bv); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JK _ 14%bv); img_refl)|]. img_apply Forall_nil.
+ cbn [ms_mem restrict]. img_apply (LFIX_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EX. rewrite ew_havoc_old by img_lia. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. unfold region_ok, R_O1a. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite THIS. split; [img_try (clear - Z1 Z14; numconst; img_lia)|]. split; [img_try (clear - Z15 Z18 Z4; numconst; img_lia)|]. split.
{ intros o Ho. img_apply apresent_writable; [img_try (clear - Ho Z1 Z14 Z15 Z18 Z4; numconst; img_lia) | img_try (img_apply Hpres; clear - Ho; img_lia)]. }
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E' _ this 8 4 (SOff aZ 0) sz); [img_try (cbn [sv_denot]; rewrite EZ, unsigned_lit_small by (clear - Hszr; img_lia); f_equal; img_lia) | img_try (clear - Hszr; cbn; img_lia) | img_try (clear; cbn; img_lia) | img_try (img_exact Hsz)].
- cbn [ss_mem]. img_apply O1a_disj. img_exact HE'.
Qed.
Lemma INV_start : INV mem [pc0].
Proof.
split; [img_try (intros x _; img_refl)|]. split; [img_try (intros a Ha; img_exact Ha)|]. split; [img_try (cbn; img_lia)|]. split; [img_refl|].
intros i Hi. exfalso. cbn in Hi. img_lia.
Qed.
Lemma INV_run : forall E ss' rs (ms ms' : machine_state) acc,
INV (ms_mem ms) acc -> envU E -> wsk_ok WSKX rs = true ->
st_ok tfxsegs E ss' (restrict Hd ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
INV (ms_mem ms') acc.
Proof.
intros E ss' rs ms ms' acc (IF & IP & IL2 & I0 & IT) HE Hb HS HF Hws. zone.
pose proof (frame_WINX E rs _ _ HE Hb HF) as FR.
split. { intros x Hx. rewrite FR by (img_try (intros Hw; img_apply Hx; left; img_exact Hw)). img_exact (IF x Hx). }
split. { intros a Ha. img_apply (pres_runX E ss' rs ms ms' HE Hb HS HF Hws). img_exact (IP a Ha). }
split; [img_try (img_exact IL2)|]. split; [img_try (img_exact I0)|].
intros i Hi. eapply val_mem_frame; [| img_try (img_exact (IT i Hi))].
intros k Hk. img_apply FR. rewrite unsigned_lit_small by (img_try (clear - Hi Hk IL2 Z1 Z14 Z15 Z18 Z4; numconst; img_lia)).
unfold WINX. clear - Hi Hk IL2 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18. numconst. img_lia.
Qed.
Lemma INV_pres_obj : forall m acc a, INV m acc -> this <= a < this + BST_SIZE -> apresent Hd m a.
Proof. intros m acc a (_ & IP & _) Ha. img_apply IP. img_apply P_this. img_exact Ha. Qed.
Lemma alias_denot : forall E sz, bv_unsigned (ew E 10) = this -> ew E aZ = Z_to_bv 64 sz -> 0 <= sz <= 30 ->
ew E aQ = Z_to_bv 64 (this + 16 + 8 * sz) ->
sv_denot E (fst LALIAS) = sv_denot E (snd LALIAS).
Proof.
intros E sz H10 HZ Hsz HQ. zone. unfold LALIAS. cbn [fst snd sv_denot]. rewrite H10, HQ. unfold aZ, aQ in *. rewrite HZ.
rewrite alu_sll. unfold v_sll. rewrite (unsigned_lit_small sz) by (img_try (clear - Hsz; img_lia)). rewrite Z.add_0_r. rewrite (unsigned_lit_small sz) by (img_try (clear - Hsz; img_lia)).
rewrite (unsigned_lit_small 3) by (img_try (clear; img_lia)). img_change (3 mod 64) with 3.
rewrite (unsigned_lit_small (this + 16 + 8 * sz)) by (img_try (clear - Hsz Z1 Z14 Z15 Z18 Z4; numconst; img_lia)). rewrite Z.add_0_r.
rewrite Z.shiftl_mul_pow2 by (img_try (clear; img_lia)). img_change (2 ^ 3) with 8.
img_change (alu64 ALU_ADD (Z_to_bv 64 (this + 16)) (Z_to_bv 64 (sz * 8))) with (Z_to_bv 64 (this + 16) + Z_to_bv 64 (sz * 8))%bv.
img_apply bv_eq. rewrite bv_add_unsigned. rewrite !unsigned_lit_small by (img_try (clear - Hsz Z1 Z14 Z15 Z18 Z4; numconst; img_lia)).
unfold bv_wrap, bv_modulus. img_change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by (img_try (clear - Hsz Z1 Z14 Z15 Z18 Z4; numconst; img_lia)).
clear - Hsz. f_equal. img_lia.
Qed.
Lemma F_disj : forall E z b, envU E -> bv_unsigned (ew E aB) = b -> bp <= b -> b + 16 <= top -> all_disjoint E (R_F aB) (R_O1a z :: LFIX).
Proof.
intros E z b HE HB Hb1 Hb2. zone. pose proof sp_range as SR.
img_apply all_disjoint_of_extents. unfold LFIX, UCONST, R_F, R_O1a, R_S', R_O1b, R_O2', R_C, R_T1, R_T2', lit1, lit4, lit8, atom8, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite HB.
rewrite (HE 10%nat ltac:(img_lia)), (HE 2%nat ltac:(img_lia)), E2, E10. unfold aC, aT. rewrite (HE 33%nat ltac:(img_lia)), (HE 32%nat ltac:(img_lia)), EaT', EaC'.
rewrite !unsigned_lit_small by (img_try (clear - Z1 Z2 Z4 Z5 Z6 Z7 Z8 Z14 Z15 Z17 Z18; numconst; img_lia)).
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 SR Hb1 Hb2.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Lemma rdword_above : forall (m : word -> option byte) a v,
(forall x : word, ~ WIN (bv_unsigned x) -> m x = mem x) -> bp - 16 <= a -> a + 8 <= top ->
rdword (aview tfxsegs Hd mem) a = Some v -> rdword (aview tfxsegs Hd m) a = Some v.
Proof.
intros m a v HF Ha1 Ha2 Hv. zone. eapply rdword_ext; [| img_try (img_exact Hv)]. intros i Hi. img_apply aview_same. img_apply HF.
rewrite unsigned_lit_small by (img_try (clear - Hi Ha1 Ha2 Z1 Z2 Z3 Z4 Z13 Z14 Z15; numconst; img_lia)).
unfold WIN, WINX. clear - Hi Ha1 Ha2 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18. numconst. img_lia.
Qed.
Definition EL (E : env) (nfp ra b sz : Z) (rg : bvmap 5 word) : env :=
havoc E 35 [Z_to_bv 64 nfp; Z_to_bv 64 ra; Z_to_bv 64 b; Z_to_bv 64 sz; Z_to_bv 64 (this + 16 + 8 * sz); getr rg 16%bv; getr rg 17%bv].
Lemma reabs_L : forall E ss ms (m : word -> option byte) nfp ra b sz,
st_ok tfxsegs E ss (restrict Hd ms) -> envU E -> ss_pc ss = A_LOOP -> ms_mem ms = m ->
reabs_check LT35 ss LREGS LF0 = true -> submem LFIX (ss_mem ss) ->
getr (ms_regs ms) 12%bv = Z_to_bv 64 b -> getr (ms_regs ms) 15%bv = Z_to_bv 64 sz ->
val_mem tfxsegs (mrestrict Hd m) (this + 8) 4 sz -> 1 <= sz <= 30 ->
(forall a, this + 8 <= a < this + 12 -> apresent Hd m a) ->
(forall x : word, ~ WIN (bv_unsigned x) -> m x = mem x) ->
bp <= b -> b + 16 <= top -> b mod 8 = 0 ->
rdword (aview tfxsegs Hd mem) (b - 8) = Some ra -> rdword (aview tfxsegs Hd mem) (b - 16) = Some nfp -> 4096 <= ra ->
let E' := EL E nfp ra b sz (ms_regs ms) in
st_ok tfxsegs E' S_L (restrict Hd ms) /\ envU E' /\
ew E' aNFP = Z_to_bv 64 nfp /\ ew E' aRA = Z_to_bv 64 ra /\ ew E' aB = Z_to_bv 64 b /\ ew E' aZ = Z_to_bv 64 sz /\
ew E' aQ = Z_to_bv 64 (this + 16 + 8 * sz).
Proof.
intros E ss ms m nfp ra b sz HS HE Hpc Hm Hck Hsub G12 G15 Hsz Hszr Hpres HFR Hb1 Hb2 Hb8 Hrd Hnfp Hra4. zone.
pose proof (rdword_range _ _ _ _ Hrd) as RR. pose proof (rdword_range _ _ _ _ Hnfp) as NR.
cbn zeta. set (E' := EL E nfp ra b sz (ms_regs ms)).
assert (HE' : envU E') by (img_try (img_apply envU_havoc; [img_try (img_exact HE) | img_lia])).
assert (ENFP : ew E' aNFP = Z_to_bv 64 nfp) by img_refl. assert (ERA : ew E' aRA = Z_to_bv 64 ra) by img_refl.
assert (EB : ew E' aB = Z_to_bv 64 b) by img_refl. assert (EZ : ew E' aZ = Z_to_bv 64 sz) by img_refl.
assert (EQ : ew E' aQ = Z_to_bv 64 (this + 16 + 8 * sz)) by img_refl.
assert (THIS : bv_unsigned (ew E' 10) = this).
{ rewrite (HE' 10%nat ltac:(img_lia)), E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
assert (UB : bv_unsigned (ew E' aB) = b) by (img_try (rewrite EB; img_apply unsigned_lit_small; clear - Hb1 Hb2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)).
split; [| img_try (split; [img_exact HE' | split; [img_exact ENFP | split; [img_exact ERA | split; [img_exact EB | split; [img_exact EZ | img_exact EQ]]]]])].
unfold S_L, LMEM, LF. rewrite <- Hpc.
apply (st_ok_add_alias E' (mkSS (ss_pc ss) LREGS (R_F aB :: R_O1a (SOff aZ 0) :: LFIX) None LF0) (restrict Hd ms) (fst LALIAS) (snd LALIAS));
[| img_try (img_exact (alias_denot E' sz THIS EZ ltac:(clear - Hszr; img_lia) EQ))].
apply (st_ok_add_region E' (mkSS (ss_pc ss) LREGS (R_O1a (SOff aZ 0) :: LFIX) None LF0) (restrict Hd ms) (R_F aB)).
1: img_apply (st_ok_add_region E' (mkSS (ss_pc ss) LREGS LFIX None LF0) (restrict Hd ms) (R_O1a (SOff aZ 0))).
- img_apply (st_ok_reabs tfxsegs LT35 E E' ss (restrict Hd ms) LREGS LFIX LF0 HS (agree_pd_havoc E 35 _ ltac:(img_lia)) Hck).
+ cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
assert (OB : forall (r' : bv 5) k (w : word), ew E' k = w -> getr (ms_regs ms) r' = w -> bv_unsigned r = bv_unsigned r' -> ew E' k = getr (ms_regs ms) r).
{ clear. intros r' k w H1 H2 H3. rewrite H1, <- H2. f_equal. symmetry. img_apply bv_eq. img_exact H3. }
destruct Hin as [H | [H | [H | [H | []]]]]; injection H as <- <-.
* img_apply (OB 12%bv 37%nat (Z_to_bv 64 b)); [img_refl | img_try (img_exact G12) | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 15%bv 38%nat (Z_to_bv 64 sz)); [img_refl | img_try (img_exact G15) | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 16%bv 40%nat (getr (ms_regs ms) 16%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 17%bv 41%nat (getr (ms_regs ms) 17%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
+ assert (FO : fact_obls LT35 LF0 = [(aNFP, mkAF 0 (2 ^ 64 - 1) 0); (aRA, mkAF 4096 (2 ^ 64 - 1) 0); (aB, mkAF kHighMemBeg kHighMemEnd 3); (aZ, mkAF 1 30 0);
(aQ, mkAF kHighMemBeg kHighMemEnd 3); (aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0)])
by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
assert (AF : forall k X lo hi al, ew E' k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E' k (mkAF lo hi al)).
{ clear. intros k X lo hi al HEq HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HEq. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (JK : forall k (r : bv 5), ew E' k = getr (ms_regs ms) r -> afact_ok E' k (mkAF 0 (2 ^ 64 - 1) 0)).
{ clear. intros k r Hk. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hk. pose proof (u64_range (getr (ms_regs ms) r)).
split; [img_lia|]. split; [img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ nfp _ _ _ ENFP); clear - NR; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ ra _ _ _ ERA); clear - RR Hra4; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ b _ _ _ EB); clear - Hb1 Hb2 Hb8 Z1 Z2 Z3 Z4 Z17; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact Hb8) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ sz _ _ _ EZ); clear - Hszr; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ (this + 16 + 8 * sz) _ _ _ EQ); clear - Hszr Hthis8 Z1 Z14 Z15 Z18 Z4; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 3) with 8. apply Z.mod_divide in Hthis8 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (q + 2 + sz). img_lia. }
img_apply Forall_cons; [img_try (img_apply (JK _ 16%bv); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JK _ 17%bv); img_refl)|]. img_apply Forall_nil.
+ cbn [ms_mem restrict]. img_apply (LFIX_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EL. rewrite ew_havoc_old by img_lia. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. rewrite Hm. unfold region_ok, R_O1a. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite THIS. split; [img_try (clear - Z1 Z14; numconst; img_lia)|]. split; [img_try (clear - Z15 Z18 Z4; numconst; img_lia)|]. split.
{ intros o Ho. img_apply apresent_writable; [img_try (clear - Ho Z1 Z14 Z15 Z18 Z4; numconst; img_lia) | img_try (img_apply Hpres; clear - Ho; img_lia)]. }
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E' _ this 8 4 (SOff aZ 0) sz); [img_try (cbn [sv_denot]; rewrite EZ, unsigned_lit_small by (clear - Hszr; img_lia); f_equal; img_lia) | img_try (clear - Hszr; cbn; img_lia) | img_try (clear; cbn; img_lia) | img_try (img_exact Hsz)].
- cbn [ss_mem]. img_apply O1a_disj. img_exact HE'.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. rewrite Hm. unfold region_ok, R_F. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite UB. split; [img_try (clear - Hb1 Z1 Z2 Z17; numconst; img_lia)|]. split; [img_try (clear - Hb2 Z3 Z4; numconst; img_lia)|]. split; [img_try (intros o Ho; exfalso; clear - Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_cons; [| img_apply Forall_nil])].
+ eapply (chunk_ok_val tfxsegs E' _ b (-16) 8 (SOff aNFP 0) nfp); [img_try (cbn [sv_denot]; rewrite ENFP, unsigned_lit_small by img_exact NR; f_equal; img_lia) | img_try (img_exact NR) | img_try (clear; cbn; img_lia) |].
replace (b + -16) with (b - 16) by img_lia. img_apply (val_mem_of_rdword tfxsegs). img_apply (rdword_above m); [img_try (img_exact HFR) | img_try (clear - Hb1; img_lia) | img_try (clear - Hb2; img_lia) | img_try (img_exact Hnfp)].
+ eapply (chunk_ok_val tfxsegs E' _ b (-8) 8 (SOff aRA 0) ra); [img_try (cbn [sv_denot]; rewrite ERA, unsigned_lit_small by img_exact RR; f_equal; img_lia) | img_try (img_exact RR) | img_try (clear; cbn; img_lia) |].
replace (b + -8) with (b - 8) by img_lia. img_apply (val_mem_of_rdword tfxsegs). img_apply (rdword_above m); [img_try (img_exact HFR) | img_try (clear - Hb1; img_lia) | img_try (clear - Hb2; img_lia) | img_try (img_exact Hrd)].
- cbn [ss_mem]. img_apply (F_disj E' _ b HE' UB Hb1 Hb2).
Qed.
Lemma Fb_disj : forall E z b, envU E -> bv_unsigned (ew E aB) = b -> bp <= b -> b + 16 <= top -> all_disjoint E (R_Fb aB) (R_O1a z :: LFIX).
Proof.
intros E z b HE HB Hb1 Hb2. zone. pose proof sp_range as SR.
img_apply all_disjoint_of_extents. unfold LFIX, UCONST, R_Fb, R_O1a, R_S', R_O1b, R_O2', R_C, R_T1, R_T2', lit1, lit4, lit8, atom8, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite HB.
rewrite (HE 10%nat ltac:(img_lia)), (HE 2%nat ltac:(img_lia)), E2, E10. unfold aC, aT. rewrite (HE 33%nat ltac:(img_lia)), (HE 32%nat ltac:(img_lia)), EaT', EaC'.
rewrite !unsigned_lit_small by (img_try (clear - Z1 Z2 Z4 Z5 Z6 Z7 Z8 Z14 Z15 Z17 Z18; numconst; img_lia)).
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 SR Hb1 Hb2.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Definition ELB (E : env) (r b sz : Z) (rg : bvmap 5 word) : env :=
havoc E 35 [Z_to_bv 64 0; Z_to_bv 64 r; Z_to_bv 64 b; Z_to_bv 64 sz; Z_to_bv 64 (this + 16 + 8 * sz); getr rg 16%bv; getr rg 17%bv].
Lemma reabs_LB : forall E ss ms (m : word -> option byte) r b sz,
st_ok tfxsegs E ss (restrict Hd ms) -> envU E -> ss_pc ss = A_LOOP -> ms_mem ms = m ->
reabs_check LT35 ss LREGS LFB = true -> submem LFIX (ss_mem ss) ->
getr (ms_regs ms) 12%bv = Z_to_bv 64 b -> getr (ms_regs ms) 15%bv = Z_to_bv 64 sz ->
val_mem tfxsegs (mrestrict Hd m) (this + 8) 4 sz -> 1 <= sz <= 30 ->
(forall a, this + 8 <= a < this + 12 -> apresent Hd m a) ->
(forall x : word, ~ WIN (bv_unsigned x) -> m x = mem x) ->
bp <= b -> b + 16 <= top -> b mod 8 = 0 ->
rdword (aview tfxsegs Hd mem) (b - 8) = Some r -> 0 <= r < 4096 ->
let E' := ELB E r b sz (ms_regs ms) in
st_ok tfxsegs E' S_LB (restrict Hd ms) /\ envU E' /\ ew E' aZ = Z_to_bv 64 sz.
Proof.
intros E ss ms m r b sz HS HE Hpc Hm Hck Hsub G12 G15 Hsz Hszr Hpres HFR Hb1 Hb2 Hb8 Hrd Hr4. zone.
pose proof (rdword_range _ _ _ _ Hrd) as RR.
cbn zeta. set (E' := ELB E r b sz (ms_regs ms)).
assert (HE' : envU E') by (img_try (img_apply envU_havoc; [img_try (img_exact HE) | img_lia])).
assert (ERA : ew E' aRA = Z_to_bv 64 r) by img_refl.
assert (EB : ew E' aB = Z_to_bv 64 b) by img_refl. assert (EZ : ew E' aZ = Z_to_bv 64 sz) by img_refl.
assert (EQ : ew E' aQ = Z_to_bv 64 (this + 16 + 8 * sz)) by img_refl.
assert (THIS : bv_unsigned (ew E' 10) = this).
{ rewrite (HE' 10%nat ltac:(img_lia)), E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
assert (UB : bv_unsigned (ew E' aB) = b) by (img_try (rewrite EB; img_apply unsigned_lit_small; clear - Hb1 Hb2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)).
split; [| img_try (split; [img_exact HE' | img_exact EZ])].
unfold S_LB, LMEMB. rewrite <- Hpc.
apply (st_ok_add_region E' (mkSS (ss_pc ss) LREGS (R_O1a (SOff aZ 0) :: LFIX) None LFB) (restrict Hd ms) (R_Fb aB)).
1: img_apply (st_ok_add_region E' (mkSS (ss_pc ss) LREGS LFIX None LFB) (restrict Hd ms) (R_O1a (SOff aZ 0))).
- img_apply (st_ok_reabs tfxsegs LT35 E E' ss (restrict Hd ms) LREGS LFIX LFB HS (agree_pd_havoc E 35 _ ltac:(img_lia)) Hck).
+ cbn [ms_regs restrict]. img_apply Forall_forall. intros [rr j] Hin. vm_compute in Hin. cbn [fst snd].
assert (OB : forall (r' : bv 5) k (w : word), ew E' k = w -> getr (ms_regs ms) r' = w -> bv_unsigned rr = bv_unsigned r' -> ew E' k = getr (ms_regs ms) rr).
{ clear. intros r' k w H1 H2 H3. rewrite H1, <- H2. f_equal. symmetry. img_apply bv_eq. img_exact H3. }
destruct Hin as [H | [H | [H | [H | []]]]]; injection H as <- <-.
* img_apply (OB 12%bv 37%nat (Z_to_bv 64 b)); [img_refl | img_try (img_exact G12) | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 15%bv 38%nat (Z_to_bv 64 sz)); [img_refl | img_try (img_exact G15) | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 16%bv 40%nat (getr (ms_regs ms) 16%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
* img_apply (OB 17%bv 41%nat (getr (ms_regs ms) 17%bv)); [img_refl | img_refl | img_try ((img_case; vm_compute); img_refl)].
+ assert (FO : fact_obls LT35 LFB = [(aRA, mkAF 0 4095 0); (aB, mkAF kHighMemBeg kHighMemEnd 3); (aZ, mkAF 1 30 0);
(aQ, mkAF kHighMemBeg kHighMemEnd 3); (aHAV, mkAF 0 (2 ^ 64 - 1) 0); (S aHAV, mkAF 0 (2 ^ 64 - 1) 0)])
by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
assert (AF : forall k X lo hi al, ew E' k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E' k (mkAF lo hi al)).
{ clear. intros k X lo hi al HEq HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HEq. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (JK : forall k (r' : bv 5), ew E' k = getr (ms_regs ms) r' -> afact_ok E' k (mkAF 0 (2 ^ 64 - 1) 0)).
{ clear. intros k r' Hk. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hk. pose proof (u64_range (getr (ms_regs ms) r')).
split; [img_lia|]. split; [img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ r _ _ _ ERA); clear - RR Hr4; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ b _ _ _ EB); clear - Hb1 Hb2 Hb8 Z1 Z2 Z3 Z4 Z17; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_exact Hb8) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ sz _ _ _ EZ); clear - Hszr; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AF _ (this + 16 + 8 * sz) _ _ _ EQ); clear - Hszr Hthis8 Z1 Z14 Z15 Z18 Z4; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 3) with 8. apply Z.mod_divide in Hthis8 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (q + 2 + sz). img_lia. }
img_apply Forall_cons; [img_try (img_apply (JK _ 16%bv); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JK _ 17%bv); img_refl)|]. img_apply Forall_nil.
+ cbn [ms_mem restrict]. img_apply (LFIX_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold ELB. rewrite ew_havoc_old by img_lia. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. rewrite Hm. unfold region_ok, R_O1a. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite THIS. split; [img_try (clear - Z1 Z14; numconst; img_lia)|]. split; [img_try (clear - Z15 Z18 Z4; numconst; img_lia)|]. split.
{ intros o Ho. img_apply apresent_writable; [img_try (clear - Ho Z1 Z14 Z15 Z18 Z4; numconst; img_lia) | img_try (img_apply Hpres; clear - Ho; img_lia)]. }
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E' _ this 8 4 (SOff aZ 0) sz); [img_try (cbn [sv_denot]; rewrite EZ, unsigned_lit_small by (clear - Hszr; img_lia); f_equal; img_lia) | img_try (clear - Hszr; cbn; img_lia) | img_try (clear; cbn; img_lia) | img_try (img_exact Hsz)].
- cbn [ss_mem]. img_apply O1a_disj. img_exact HE'.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. rewrite Hm. unfold region_ok, R_Fb. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite UB. split; [img_try (clear - Hb1 Z1 Z2 Z17; numconst; img_lia)|]. split; [img_try (clear - Hb2 Z3 Z4; numconst; img_lia)|]. split; [img_try (intros o Ho; exfalso; clear - Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E' _ b (-8) 8 (SOff aRA 0) r); [img_try (cbn [sv_denot]; rewrite ERA, unsigned_lit_small by img_exact RR; f_equal; img_lia) | img_try (img_exact RR) | img_try (clear; cbn; img_lia) |].
replace (b + -8) with (b - 8) by img_lia. img_apply (val_mem_of_rdword tfxsegs). img_apply (rdword_above m); [img_try (img_exact HFR) | img_try (clear - Hb1; img_lia) | img_try (clear - Hb2; img_lia) | img_try (img_exact Hrd)].
- cbn [ss_mem]. img_apply (Fb_disj E' _ b HE' UB Hb1 Hb2).
Qed.
Lemma Q_disj : forall E z b sz, envU E -> bv_unsigned (ew E aB) = b -> bp <= b ->
bv_unsigned (ew E aQ) = this + 16 + 8 * sz -> 1 <= sz <= 29 ->
all_disjoint E R_Q (R_F aB :: R_O1a z :: LFIX).
Proof.
intros E z b sz HE HB Hb1 HQ Hsz. zone. pose proof sp_range as SR.
img_apply all_disjoint_of_extents. unfold LFIX, UCONST, R_Q, R_F, R_O1a, R_S', R_O1b, R_O2', R_C, R_T1, R_T2', lit1, lit4, lit8, atom8, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite HB, HQ.
rewrite (HE 10%nat ltac:(img_lia)), (HE 2%nat ltac:(img_lia)), E2, E10. unfold aC, aT. rewrite (HE 33%nat ltac:(img_lia)), (HE 32%nat ltac:(img_lia)), EaT', EaC'.
rewrite !unsigned_lit_small by (img_try (clear - Z1 Z2 Z4 Z5 Z6 Z7 Z8 Z14 Z15 Z17 Z18; numconst; img_lia)).
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 SR Hb1 Hsz.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Lemma st_ok_add_Q : forall E ss ms z b sz acc,
st_ok tfxsegs E ss (restrict Hd ms) -> ss_mem ss = R_F aB :: R_O1a z :: LFIX -> envU E ->
bv_unsigned (ew E aB) = b -> bp <= b -> bv_unsigned (ew E aQ) = this + 16 + 8 * sz -> 1 <= sz <= 29 -> INV (ms_mem ms) acc ->
st_ok tfxsegs E (mkSS (ss_pc ss) (ss_regs ss) (R_Q :: ss_mem ss) (ss_resv ss) (ss_facts ss)) (restrict Hd ms).
Proof.
intros E ss ms z b sz acc HS Hm HE HB Hb1 HQ Hsz HI. zone.
img_apply st_ok_add_region; [img_try (img_exact HS) | img_try ((img_case; vm_compute); img_refl) | | img_try (rewrite Hm; img_exact (Q_disj E z b sz HE HB Hb1 HQ Hsz))].
cbn [ms_mem restrict]. unfold region_ok, R_Q. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HQ. split; [img_try (clear - Z1 Z14 Hsz; numconst; img_lia)|]. split; [img_try (clear - Z15 Z18 Z4 Hsz; numconst; img_lia)|]. split; [| img_try (img_apply Forall_nil)].
intros o Ho. img_apply apresent_writable; [img_try (clear - Ho Hsz Z1 Z14 Z15 Z18 Z4; numconst; img_lia)|]. img_apply (INV_pres_obj _ _ _ HI). clear - Ho Hsz. numconst. img_lia.
Qed.
Lemma INV_runQ : forall E ss' rs (ms ms' : machine_state) acc acc' ra,
(INV (ms_mem ms) acc \/ INV (ms_mem ms) acc') -> acc' = acc ++ [ra] -> (1 <= length acc <= 29)%nat -> envU E ->
bv_unsigned (ew E aQ) = this + 16 + 8 * Z.of_nat (length acc) -> wsk_ok WSK rs = true ->
st_ok tfxsegs E ss' (restrict Hd ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
val_mem tfxsegs (mrestrict Hd (ms_mem ms')) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra ->
INV (ms_mem ms') acc'.
Proof.
intros E ss' rs ms ms' acc acc' ra HI Hacc Hlen HE HQ Hb HS HF Hws Hnew. zone.
assert (HQ1 : this + 24 <= bv_unsigned (ew E aQ)) by (img_try (rewrite HQ; clear - Hlen; img_lia)).
assert (HQ2 : bv_unsigned (ew E aQ) + 8 <= this + 16 + 8 * 30) by (img_try (rewrite HQ; clear - Hlen; img_lia)).
pose proof (frame_WINQ E rs _ _ HE Hb HF) as FR. rewrite HQ in FR.
assert (CORE : (forall x : word, ~ WIN (bv_unsigned x) -> ms_mem ms x = mem x) -> (forall a, apresent Hd mem a -> apresent Hd (ms_mem ms) a) ->
nth 0 acc 0 = pc0 ->
(forall i, (1 <= i < length acc)%nat -> val_mem tfxsegs (mrestrict Hd (ms_mem ms)) (this + 16 + 8 * Z.of_nat i) 8 (nth i acc 0)) ->
INV (ms_mem ms') acc').
{ intros IF IP I0 IT. split.
{ intros x Hx. rewrite FR by (img_try (intros Hw; img_apply Hx; img_apply (WINQ_WIN (this + 16 + 8 * Z.of_nat (length acc))); [img_try (clear - Hlen; img_lia) | img_try (clear - Hlen; img_lia) | img_try (img_exact Hw)])). img_exact (IF x Hx). }
split. { intros a Ha. img_apply (pres_runQ E ss' rs ms ms' HE HQ1 HQ2 Hb HS HF Hws). img_exact (IP a Ha). }
rewrite Hacc, length_app. cbn [length]. split; [img_try (clear - Hlen; img_lia)|]. split; [img_try (rewrite app_nth1 by img_lia; img_exact I0)|].
intros i Hi. destruct (Nat.eq_dec i (length acc)) as [->|Hne].
- rewrite nth_middle. img_exact Hnew.
- rewrite app_nth1 by (img_try (clear - Hi Hne; img_lia)). eapply val_mem_frame; [| img_try (img_exact (IT i ltac:(clear - Hi Hne; img_lia)))].
intros k Hk. img_apply FR. rewrite unsigned_lit_small by (img_try (clear - Hi Hk Hne Hlen Z1 Z14 Z15 Z18 Z4; numconst; img_lia)).
unfold WINQ, WINX. clear - Hi Hk Hne Hlen Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18. numconst. img_lia. }
destruct HI as [(IF & IP & IL2 & I0 & IT) | (IF & IP & IL2 & I0 & IT)].
- img_exact (CORE IF IP I0 IT).
- img_apply (CORE IF IP).
+ rewrite Hacc, app_nth1 in I0 by img_lia. img_exact I0.
+ intros i Hi. rewrite Hacc in IT. rewrite <- (app_nth1 acc [ra] 0) by (img_try (clear - Hi; img_lia)). img_apply IT. rewrite length_app. cbn. clear - Hi. img_lia.
Qed.
Ltac sub_keep := img_apply submem_keep; [img_try (img_apply subregion_refl)|].
Ltac sub_drop := img_apply submem_drop.
Definition Fr (r : Z * Z * Z) : list Z := match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end.
Lemma firstn_full : forall (acc l : list Z), (length acc = 30)%nat -> firstn 30 (acc ++ l) = acc.
Proof. intros acc l H. rewrite firstn_app, H, Nat.sub_diag. cbn. rewrite app_nil_r. img_apply firstn_all2. img_lia. Qed.
Lemma firstn_short : forall (acc : list Z), (length acc <= 30)%nat -> firstn 30 (acc ++ []) = acc.
Proof. intros acc H. rewrite app_nil_r. img_apply firstn_all2. img_exact H. Qed.
Lemma condZ : forall E (c : branch_cond) n1 k1 n2 k2 (r : bool),
branch_taken c (sv_denot E (SOff n1 k1)) (sv_denot E (SOff n2 k2)) = r ->
0 <= bv_unsigned (ew E n1) + k1 < 2 ^ 64 -> 0 <= bv_unsigned (ew E n2) + k2 < 2 ^ 64 ->
match c with
| BC_EQ => (bv_unsigned (ew E n1) + k1 =? bv_unsigned (ew E n2) + k2) = r
| BC_NE => negb (bv_unsigned (ew E n1) + k1 =? bv_unsigned (ew E n2) + k2) = r
| BC_LTU => (bv_unsigned (ew E n1) + k1 <? bv_unsigned (ew E n2) + k2) = r
| BC_GEU => negb (bv_unsigned (ew E n1) + k1 <? bv_unsigned (ew E n2) + k2) = r
| _ => True
end.
Proof.
intros E c n1 k1 n2 k2 r Hc H1 H2. unfold branch_taken, bv_ltu, bv_eqb in Hc. rewrite !denot_SOff in Hc. unfold zcanon, M64 in Hc.
rewrite !Z.mod_small in Hc by assumption. destruct c; first [img_exact Hc | img_exact I].
Qed.
Lemma condZ_lit : forall E (c : branch_cond) n1 k1 z (r : bool),
branch_taken c (sv_denot E (SOff n1 k1)) (sv_denot E (SLit z)) = r ->
0 <= bv_unsigned (ew E n1) + k1 < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
match c with
| BC_LTU => (bv_unsigned (ew E n1) + k1 <? z) = r
| BC_GEU => negb (bv_unsigned (ew E n1) + k1 <? z) = r
| _ => True
end.
Proof.
intros E c n1 k1 z r Hc H1 H2. unfold branch_taken, bv_ltu in Hc. rewrite denot_SOff in Hc. cbn [sv_denot] in Hc. unfold zcanon, M64 in Hc.
rewrite unsigned_lit_small in Hc by img_exact H2. rewrite !Z.mod_small in Hc by assumption. destruct c; first [img_exact Hc | img_exact I].
Qed.
Lemma cond_and7 : forall E n (r : bool),
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 7))) (sv_denot E (SLit 0)) = r ->
(bv_unsigned (ew E n) mod 8 =? 0) = r.
Proof.
intros E n r Hc. unfold branch_taken, bv_eqb in Hc. cbn [sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
img_change (alu64 ALU_AND (ew E n) (Z_to_bv 64 7)) with (bv_and (ew E n) (Z_to_bv 64 7)) in Hc.
rewrite bv_and_unsigned in Hc. rewrite !unsigned_lit_small in Hc by (img_try (clear; img_lia)).
img_change 7 with (Z.ones 3) in Hc. rewrite Z.land_ones in Hc by (img_try (clear; img_lia)). img_exact Hc.
Qed.
Ltac do_exit HS HE INVa THIS idx acc Hlen :=
lazymatch type of HS with st_ok _ ?E ?ssA (restrict _ ?msA) =>
let SZ := fresh "SZ" in
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem msA)) (this + 8) 4 (Z.of_nat (length acc)));
[ memv HS idx 0%nat; [img_try (rewrite THIS; img_refl) | | img_try (clear - Hlen; img_lia)]
| let HSX := fresh "HSX" in let HEX := fresh "HEX" in let HZX := fresh "HZX" in
destruct (reabs_X E ssA msA (Z.of_nat (length acc)) HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop))) SZ ltac:(img_try (clear - Hlen; img_lia))
(fun a Ha => INV_pres_obj _ _ a INVa ltac:(img_try (clear - Ha; numconst; img_lia)))) as (HSX & HEX & HZX);
eapply (exit_ok _ _ _ acc HSX HEX INVa); [img_try (img_exact HZX) |] ]
end.
Lemma break_ok : forall acc E ms mat,
st_ok tfxsegs E S_LB (restrict Hd ms) -> envU E -> INV (ms_mem ms) acc ->
bv_unsigned (ew E aZ) = Z.of_nat (length acc) -> TR = acc ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) UPOST.
Proof.
intros acc E ms mat HS HE HI EZ HTR. pose proof Hwx_tfa as Hwx. zone. pose proof HI as (IF & IP & IL2 & I0 & IT).
assert (THIS : bv_unsigned (ew E 10) = this).
{ rewrite (HE 10%nat ltac:(img_lia)), E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
pose proof (u64_range (ew E 38)) as U38. unfold aZ in EZ.
srr_branch_with tfxtbl_rtA_ok HS.
-
srr_run_to_with tfxtbl_rtA_ok HS A_EXIT. clear HFr.
lazymatch type of HS with st_ok _ _ ?ssA (restrict _ ?msA) =>
lazymatch type of HF with frame_of _ ?rsA _ _ =>
assert (INVa : INV (ms_mem msA) acc)
by (img_try (img_apply (INV_run E ssA rsA ms msA acc HI HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))))
end end.
do_exit HS HE INVa THIS 1%nat acc IL2.
{ cbn [sv_denot]. rewrite EZ, Z.add_0_r. img_refl. }
symmetry. img_exact HTR.
-
srr_run_to_with tfxtbl_rtA_ok HS A_EXIT. clear HFr.
lazymatch type of HS with st_ok _ _ ?ssA (restrict _ ?msA) =>
lazymatch type of HF with frame_of _ ?rsA _ _ =>
assert (INVa : INV (ms_mem msA) acc)
by (img_try (img_apply (INV_run E ssA rsA ms msA acc HI HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))))
end end.
do_exit HS HE INVa THIS 1%nat acc IL2.
{ cbn [sv_denot]. rewrite EZ, Z.add_0_r. img_refl. }
symmetry. img_exact HTR.
Qed.
Lemma loop_ok : forall rem acc E ms mat,
st_ok tfxsegs E S_L (restrict Hd ms) -> envU E -> INV (ms_mem ms) acc ->
bv_unsigned (ew E aZ) = Z.of_nat (length acc) -> bv_unsigned (ew E aQ) = this + 16 + 8 * Z.of_nat (length acc) ->
bp <= bv_unsigned (ew E aB) -> bv_unsigned (ew E aB) + 16 < top ->
fpchain (rdword (aview tfxsegs Hd mem)) (bv_unsigned (ew E aB)) top rem ->
match rem with [] => False | (_, ra, nfp) :: _ => bv_unsigned (ew E aRA) = ra /\ bv_unsigned (ew E aNFP) = nfp end ->
TR = firstn 30 (acc ++ flat_map Fr rem) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) UPOST.
Proof.
induction rem as [| [[b' ra] nfp] rest IH]; intros acc E ms mat HS HE HI EZ EQ Hb1 Hb2 HCH HX HTR; [img_try (destruct HX)|].
destruct HX as [ERA ENFP]. cbn [fpchain] in HCH. destruct HCH as (Hbb & Hb8 & Hrd1 & Hrd2 & Hra4 & Hrest).
pose proof Hwx_tfa as Hwx. zone. pose proof HI as (IF & IP & IL2 & I0 & IT).
set (b := bv_unsigned (ew E aB)) in *.
assert (THIS : bv_unsigned (ew E 10) = this).
{ rewrite (HE 10%nat ltac:(img_lia)), E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
assert (UTOP : bv_unsigned (ew E 34) = top).
{ rewrite (HE 34%nat ltac:(img_lia)), EaTOP'. img_apply unsigned_lit_small. clear - Z1 Z2 Z3 Z4; numconst; img_lia. }
pose proof (u64_range (ew E 38)) as U38. pose proof (u64_range (ew E 37)) as U37. pose proof (u64_range (ew E 36)) as U36. pose proof (u64_range (ew E 35)) as U35.
unfold aZ in EZ. unfold aQ in EQ. unfold aB in b. unfold aRA in ERA. unfold aNFP in ENFP. (subst b'; cbv beta).
srr_branch_with tfxtbl_rtA_ok HS.
-
apply (condZ_lit E BC_GEU 38 0 30 true) in Hc; [| img_try (clear - U38; img_lia) | img_try (clear; img_lia)]. cbn beta iota in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ssA (restrict _ ?msA) =>
lazymatch type of HF with frame_of _ ?rsA _ _ =>
assert (INVa : INV (ms_mem msA) acc)
by (img_try (img_apply (INV_run E ssA rsA ms msA acc HI HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))))
end end.
do_exit HS HE INVa THIS 1%nat acc IL2.
{ cbn [sv_denot]. rewrite EZ, Z.add_0_r. img_refl. }
rewrite HTR. symmetry. img_apply firstn_full. clear - Hc EZ IL2. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. img_lia.
-
apply (condZ_lit E BC_GEU 38 0 30 false) in Hc; [| img_try (clear - U38; img_lia) | img_try (clear; img_lia)]. cbn beta iota in Hc. rename Hc into Hsz.
assert (Hlen : (1 <= length acc <= 29)%nat) by (img_try (clear - Hsz EZ IL2; apply Bool.negb_false_iff in Hsz; apply Z.ltb_lt in Hsz; img_lia)). clear Hsz.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) => lazymatch type of HF with frame_of _ ?rs1 _ _ =>
assert (INV1 : INV (ms_mem ms1) acc) by (img_try (img_apply (INV_run E ss1 rs1 ms ms1 acc HI HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF end end.
srr_branch_with tfxtbl_rtA_ok HS.
+
apply (condZ E BC_EQ 36 0 11 0 true) in Hc; [| img_try (clear - U36; img_lia) | img_try (pose proof (u64_range (ew E 11)); clear - H; img_lia)]. cbn beta iota in Hc.
rewrite (HE 11%nat ltac:(img_lia)), E11, unsigned_lit_small, !Z.add_0_r, ERA in Hc by img_exact Hpc0. apply Z.eqb_eq in Hc. rename Hc into Hrapc.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) => lazymatch type of HF with frame_of _ ?rs2 (ms_mem ?ms1) _ =>
assert (INV2 : INV (ms_mem ms2) acc) by (img_try (img_apply (INV_run E ss2 rs2 ms1 ms2 acc INV1 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV1 end end.
assert (TRX : bad_next b top nfp = true -> acc = TR).
{ intros Hbn. rewrite Hbn in Hrest. rewrite HTR, Hrest. cbn [flat_map Fr app]. rewrite Hrapc, Z.eqb_refl. cbn [app]. symmetry. img_apply firstn_short. clear - Hlen; img_lia. }
srr_branch_with tfxtbl_rtA_ok HS.
*
apply (condZ E BC_GEU 37 0 35 0 true) in Hc; [| img_try (clear - U37; img_lia) | img_try (clear - U35; img_lia)]. cbn beta iota in Hc. rewrite !Z.add_0_r, ENFP in Hc. fold b in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) => lazymatch type of HF with frame_of _ ?rs3 (ms_mem ?ms2) _ =>
assert (INVa : INV (ms_mem ms3) acc) by (img_try (img_apply (INV_run E ss3 rs3 ms2 ms3 acc INV2 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV2 end end.
do_exit HS HE INVa THIS 1%nat acc IL2.
{ cbn [sv_denot]. rewrite EZ, Z.add_0_r. img_refl. }
img_apply TRX. unfold bad_next. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. replace (nfp <=? b) with true by (img_try (symmetry; img_apply Z.leb_le; clear - Hc; img_lia)). img_refl.
* apply (condZ E BC_GEU 37 0 35 0 false) in Hc; [| img_try (clear - U37; img_lia) | img_try (clear - U35; img_lia)]. cbn beta iota in Hc. rewrite !Z.add_0_r, ENFP in Hc. fold b in Hc.
apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. rename Hc into Hn1.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) => lazymatch type of HF with frame_of _ ?rs3 (ms_mem ?ms2) _ =>
assert (INV3 : INV (ms_mem ms3) acc) by (img_try (img_apply (INV_run E ss3 rs3 ms2 ms3 acc INV2 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV2 end end.
srr_branch_with tfxtbl_rtA_ok HS.
--
apply (condZ E BC_GEU 35 0 34 (-16) true) in Hc; [| img_try (clear - U35; img_lia) | img_try (rewrite UTOP; clear - Z1 Z2 Z3 Z4; numconst; img_lia)]. cbn beta iota in Hc.
rewrite !Z.add_0_r, ENFP, UTOP in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss4 (restrict _ ?ms4) => lazymatch type of HF with frame_of _ ?rs4 (ms_mem ?ms3) _ =>
assert (INVa : INV (ms_mem ms4) acc) by (img_try (img_apply (INV_run E ss4 rs4 ms3 ms4 acc INV3 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV3 end end.
do_exit HS HE INVa THIS 1%nat acc IL2.
{ cbn [sv_denot]. rewrite EZ, Z.add_0_r. img_refl. }
img_apply TRX. unfold bad_next. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc.
replace (top - 16 <=? nfp) with true by (img_try (symmetry; img_apply Z.leb_le; clear - Hc; img_lia)). rewrite Bool.orb_true_r. img_refl.
-- apply (condZ E BC_GEU 35 0 34 (-16) false) in Hc; [| img_try (clear - U35; img_lia) | img_try (rewrite UTOP; clear - Z1 Z2 Z3 Z4; numconst; img_lia)]. cbn beta iota in Hc.
rewrite !Z.add_0_r, ENFP, UTOP in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. rename Hc into Hn2.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss4 (restrict _ ?ms4) => lazymatch type of HF with frame_of _ ?rs4 (ms_mem ?ms3) _ =>
assert (INV4 : INV (ms_mem ms4) acc) by (img_try (img_apply (INV_run E ss4 rs4 ms3 ms4 acc INV3 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV3 end end.
srr_branch_with tfxtbl_rtA_ok HS.
++
apply cond_and7 in Hc. rewrite ENFP in Hc. apply Z.eqb_eq in Hc. rename Hc into Hn3.
assert (Hbn : bad_next b top nfp = false).
{ unfold bad_next. rewrite Hn3. replace (nfp <=? b) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hn1)).
replace (top - 16 <=? nfp) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hn2)). img_refl. }
rewrite Hbn in Hrest. clear TRX Hbn.
destruct rest as [| [[f ra'] n'] rest'].
{
cbn [fpchain] in Hrest. destruct Hrest as (rS & HlS & HrS).
srr_run_to_with tfxtbl_rtA_ok HS A_LOOP. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) => lazymatch type of HF with frame_of _ ?rs5 (ms_mem ?ms4) _ =>
assert (INV5 : INV (ms_mem ms5) acc) by (img_try (img_apply (INV_run E ss5 rs5 ms4 ms5 acc INV4 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV4 end end.
rreg HS (12%bv : bv 5) G12. rreg HS (15%bv : bv 5) G15.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) =>
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem ms5)) (this + 8) 4 (Z.of_nat (length acc)))
by (img_try (memv HS 1%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_try (cbn [sv_denot]; rewrite EZ, Z.add_0_r; img_refl) | img_try (clear - Hlen; img_lia)]));
destruct (reabs_LB E ss5 ms5 (ms_mem ms5) rS nfp (Z.of_nat (length acc)) HS HE eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
ltac:(img_try (rewrite G12, <- ENFP; symmetry; img_apply Z_to_bv_bv_unsigned))
ltac:(img_try (rewrite G15, <- EZ; symmetry; img_apply Z_to_bv_bv_unsigned))
SZ ltac:(img_try (clear - Hlen; img_lia)) (fun a Ha => INV_pres_obj _ _ a INV5 ltac:(img_try (clear - Ha; numconst; img_lia))) (proj1 INV5)
ltac:(img_try (clear - Hb1 Hn1; img_lia)) ltac:(img_try (clear - Hn2; img_lia)) Hn3 HlS HrS)
as (HSB & HEB & EZB)
end.
lazymatch type of HSB with st_ok _ ?E' _ (restrict _ ?ms5) => apply (break_ok acc E' ms5 _ HSB HEB INV5) end.
- rewrite EZB. img_apply unsigned_lit_small. clear - Hlen; img_lia.
- rewrite HTR. cbn [flat_map Fr app]. rewrite Hrapc, Z.eqb_refl. cbn [app]. img_apply firstn_short. clear - Hlen; img_lia. }
pose proof Hrest as HR2. cbn [fpchain] in HR2. destruct HR2 as (Hf & _ & Hl1 & Hl2 & H4096' & _). (subst f; cbv beta).
srr_run_to_with tfxtbl_rtA_ok HS (0x73a18 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) => lazymatch type of HF with frame_of _ ?rs5 (ms_mem ?ms4) _ =>
assert (INV5 : INV (ms_mem ms5) acc) by (img_try (img_apply (INV_run E ss5 rs5 ms4 ms5 acc INV4 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV4 end end.
rreg HS (12%bv : bv 5) G12. rreg HS (15%bv : bv 5) G15.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) =>
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem ms5)) (this + 8) 4 (Z.of_nat (length acc)))
by (img_try (memv HS 1%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_try (cbn [sv_denot]; rewrite EZ, Z.add_0_r; img_refl) | img_try (clear - Hlen; img_lia)]));
destruct (reabs_L E ss5 ms5 (ms_mem ms5) n' ra' nfp (Z.of_nat (length acc)) HS HE eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
ltac:(img_try (rewrite G12, <- ENFP; symmetry; img_apply Z_to_bv_bv_unsigned))
ltac:(img_try (rewrite G15, <- EZ; symmetry; img_apply Z_to_bv_bv_unsigned))
SZ ltac:(img_try (clear - Hlen; img_lia)) (fun a Ha => INV_pres_obj _ _ a INV5 ltac:(img_try (clear - Ha; numconst; img_lia))) (proj1 INV5)
ltac:(img_try (clear - Hb1 Hn1; img_lia)) ltac:(img_try (clear - Hn2; img_lia)) Hn3 Hl1 Hl2 H4096')
as (HSL & HEL & EN' & ER' & EB' & EZ' & EQ')
end.
pose proof (rdword_range _ _ _ _ Hl1) as RR'. pose proof (rdword_range _ _ _ _ Hl2) as NR'.
lazymatch type of HSL with st_ok _ ?E' _ (restrict _ ?ms5) =>
apply (IH acc E' ms5 _ HSL HEL INV5) end.
** rewrite EZ'. img_apply unsigned_lit_small. clear - Hlen; img_lia.
** rewrite EQ'. img_apply unsigned_lit_small. clear - Hlen Z1 Z14 Z15 Z18 Z4; numconst; img_lia.
** rewrite EB', unsigned_lit_small by (img_try (clear - Hb1 Hn1 Hn2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)). clear - Hb1 Hn1; img_lia.
** rewrite EB', unsigned_lit_small by (img_try (clear - Hb1 Hn1 Hn2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)). clear - Hn2; img_lia.
** rewrite EB', unsigned_lit_small by (img_try (clear - Hb1 Hn1 Hn2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)). img_exact Hrest.
** rewrite EN', ER', !unsigned_lit_small by first [img_exact RR' | img_exact NR']. split; img_refl.
** rewrite HTR. cbn [flat_map]. unfold Fr at 1. rewrite Hrapc, Z.eqb_refl. img_refl.
++
apply cond_and7 in Hc. rewrite ENFP in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) => lazymatch type of HF with frame_of _ ?rs5 (ms_mem ?ms4) _ =>
assert (INVa : INV (ms_mem ms5) acc) by (img_try (img_apply (INV_run E ss5 rs5 ms4 ms5 acc INV4 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV4 end end.
do_exit HS HE INVa THIS 1%nat acc IL2.
{ cbn [sv_denot]. rewrite EZ, Z.add_0_r. img_refl. }
img_apply TRX. unfold bad_next. rewrite Hc. cbn [negb]. rewrite !Bool.orb_true_r. img_refl.
+
apply (condZ E BC_EQ 36 0 11 0 false) in Hc; [| img_try (clear - U36; img_lia) | img_try (pose proof (u64_range (ew E 11)); clear - H; img_lia)]. cbn beta iota in Hc.
rewrite (HE 11%nat ltac:(img_lia)), E11, unsigned_lit_small, !Z.add_0_r, ERA in Hc by img_exact Hpc0. apply Z.eqb_neq in Hc. rename Hc into Hrapc.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) => lazymatch type of HF with frame_of _ ?rs2 (ms_mem ?ms1) _ =>
assert (INV2 : INV (ms_mem ms2) acc) by (img_try (img_apply (INV_run E ss2 rs2 ms1 ms2 acc INV1 HE ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl))));
clear HF INV1 end end.
apply (st_ok_add_Q E _ _ (SOff 38%nat 1) b (Z.of_nat (length acc)) acc) in HS;
[| img_refl | img_try (img_exact HE) | img_refl | img_try (img_exact Hb1) | img_try (img_exact EQ) | img_try (clear - Hlen; img_lia) | img_try (img_exact INV2)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
set (acc' := acc ++ [ra]).
assert (Hlen' : (1 <= length acc' <= 30)%nat) by (img_try ((subst acc'; cbv beta); rewrite length_app; cbn; clear - Hlen; img_lia)).
assert (EZ1 : sv_denot E (SOff 38 1) = Z_to_bv 64 (Z.of_nat (length acc'))).
{ (subst acc'; cbv beta). rewrite length_app. cbn [sv_denot length]. rewrite EZ. f_equal. clear; img_lia. }
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) => lazymatch type of HF with frame_of _ ?rs3 (ms_mem ?ms2) _ =>
assert (NEW3 : val_mem tfxsegs (mrestrict Hd (ms_mem ms3)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INV3 : INV (ms_mem ms3) acc')
by (img_try (img_apply (INV_runQ E ss3 rs3 ms2 ms3 acc acc' ra (or_introl INV2) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW3)));
clear HF INV2 NEW3 end end.
assert (TRX : bad_next b top nfp = true -> acc' = TR).
{ intros Hbn. rewrite Hbn in Hrest. rewrite HTR, Hrest. cbn [flat_map Fr app]. replace (ra =? pc0) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_exact Hrapc)).
(subst acc'; cbv beta). rewrite ?app_nil_r. symmetry. img_apply firstn_all2. clear - Hlen. rewrite length_app. cbn. img_lia. }
srr_branch_with tfxtbl_rtA_ok HS.
*
apply (condZ E BC_GEU 37 0 35 0 true) in Hc; [| img_try (clear - U37; img_lia) | img_try (clear - U35; img_lia)]. cbn beta iota in Hc. rewrite !Z.add_0_r, ENFP in Hc. fold b in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss4 (restrict _ ?ms4) => lazymatch type of HF with frame_of _ ?rs4 (ms_mem ?ms3) _ =>
assert (NEW4 : val_mem tfxsegs (mrestrict Hd (ms_mem ms4)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INVa : INV (ms_mem ms4) acc')
by (img_try (img_apply (INV_runQ E ss4 rs4 ms3 ms4 acc acc' ra (or_intror INV3) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW4)));
clear HF INV3 NEW4 end end.
do_exit HS HE INVa THIS 2%nat acc' Hlen'.
{ img_exact EZ1. }
img_apply TRX. unfold bad_next. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. replace (nfp <=? b) with true by (img_try (symmetry; img_apply Z.leb_le; clear - Hc; img_lia)). img_refl.
* apply (condZ E BC_GEU 37 0 35 0 false) in Hc; [| img_try (clear - U37; img_lia) | img_try (clear - U35; img_lia)]. cbn beta iota in Hc. rewrite !Z.add_0_r, ENFP in Hc. fold b in Hc.
apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. rename Hc into Hn1.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss4 (restrict _ ?ms4) => lazymatch type of HF with frame_of _ ?rs4 (ms_mem ?ms3) _ =>
assert (NEW4 : val_mem tfxsegs (mrestrict Hd (ms_mem ms4)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INV4 : INV (ms_mem ms4) acc')
by (img_try (img_apply (INV_runQ E ss4 rs4 ms3 ms4 acc acc' ra (or_intror INV3) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW4)));
clear HF INV3 NEW4 end end.
srr_branch_with tfxtbl_rtA_ok HS.
--
apply (condZ E BC_GEU 35 0 34 (-16) true) in Hc; [| img_try (clear - U35; img_lia) | img_try (rewrite UTOP; clear - Z1 Z2 Z3 Z4; numconst; img_lia)]. cbn beta iota in Hc.
rewrite !Z.add_0_r, ENFP, UTOP in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) => lazymatch type of HF with frame_of _ ?rs5 (ms_mem ?ms4) _ =>
assert (NEW5 : val_mem tfxsegs (mrestrict Hd (ms_mem ms5)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INVa : INV (ms_mem ms5) acc')
by (img_try (img_apply (INV_runQ E ss5 rs5 ms4 ms5 acc acc' ra (or_intror INV4) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW5)));
clear HF INV4 NEW5 end end.
do_exit HS HE INVa THIS 2%nat acc' Hlen'.
{ img_exact EZ1. }
img_apply TRX. unfold bad_next. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc.
replace (top - 16 <=? nfp) with true by (img_try (symmetry; img_apply Z.leb_le; clear - Hc; img_lia)). rewrite Bool.orb_true_r. img_refl.
-- apply (condZ E BC_GEU 35 0 34 (-16) false) in Hc; [| img_try (clear - U35; img_lia) | img_try (rewrite UTOP; clear - Z1 Z2 Z3 Z4; numconst; img_lia)]. cbn beta iota in Hc.
rewrite !Z.add_0_r, ENFP, UTOP in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. rename Hc into Hn2.
srr_run_with tfxtbl_rtA_ok HS. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss5 (restrict _ ?ms5) => lazymatch type of HF with frame_of _ ?rs5 (ms_mem ?ms4) _ =>
assert (NEW5 : val_mem tfxsegs (mrestrict Hd (ms_mem ms5)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INV5 : INV (ms_mem ms5) acc')
by (img_try (img_apply (INV_runQ E ss5 rs5 ms4 ms5 acc acc' ra (or_intror INV4) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW5)));
clear HF INV4 NEW5 end end.
srr_branch_with tfxtbl_rtA_ok HS.
++
apply cond_and7 in Hc. rewrite ENFP in Hc. apply Z.eqb_eq in Hc. rename Hc into Hn3.
assert (Hbn : bad_next b top nfp = false).
{ unfold bad_next. rewrite Hn3. replace (nfp <=? b) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hn1)).
replace (top - 16 <=? nfp) with false by (img_try (symmetry; img_apply Z.leb_gt; img_exact Hn2)). img_refl. }
rewrite Hbn in Hrest. clear TRX Hbn.
destruct rest as [| [[f ra'] n'] rest'].
{
cbn [fpchain] in Hrest. destruct Hrest as (rS & HlS & HrS).
srr_run_to_with tfxtbl_rtA_ok HS A_LOOP. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss6 (restrict _ ?ms6) => lazymatch type of HF with frame_of _ ?rs6 (ms_mem ?ms5) _ =>
assert (NEW6 : val_mem tfxsegs (mrestrict Hd (ms_mem ms6)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INV6 : INV (ms_mem ms6) acc')
by (img_try (img_apply (INV_runQ E ss6 rs6 ms5 ms6 acc acc' ra (or_intror INV5) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW6)));
clear HF INV5 NEW6 end end.
rreg HS (12%bv : bv 5) G12. rreg HS (15%bv : bv 5) G15.
lazymatch type of HS with st_ok _ _ ?ss6 (restrict _ ?ms6) =>
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem ms6)) (this + 8) 4 (Z.of_nat (length acc')))
by (img_try (memv HS 2%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_try (img_exact EZ1) | img_try (clear - Hlen'; img_lia)]));
destruct (reabs_LB E ss6 ms6 (ms_mem ms6) rS nfp (Z.of_nat (length acc')) HS HE eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
ltac:(img_try (rewrite G12, <- ENFP; symmetry; img_apply Z_to_bv_bv_unsigned))
ltac:(img_try (rewrite G15; img_exact EZ1))
SZ ltac:(img_try (clear - Hlen'; img_lia)) (fun a Ha => INV_pres_obj _ _ a INV6 ltac:(img_try (clear - Ha; numconst; img_lia))) (proj1 INV6)
ltac:(img_try (clear - Hb1 Hn1; img_lia)) ltac:(img_try (clear - Hn2; img_lia)) Hn3 HlS HrS)
as (HSB & HEB & EZB)
end.
lazymatch type of HSB with st_ok _ ?E' _ (restrict _ ?ms6) => apply (break_ok acc' E' ms6 _ HSB HEB INV6) end.
- rewrite EZB. img_apply unsigned_lit_small. clear - Hlen'; img_lia.
- rewrite HTR. cbn [flat_map]. unfold Fr at 1. replace (ra =? pc0) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_exact Hrapc)).
cbn [app]. (subst acc'; cbv beta). rewrite <- (app_nil_r (acc ++ [ra])) at 1. img_apply firstn_short. rewrite length_app. cbn [length]. clear - Hlen; img_lia. }
pose proof Hrest as HR2. cbn [fpchain] in HR2. destruct HR2 as (Hf & _ & Hl1 & Hl2 & H4096' & _). (subst f; cbv beta).
srr_run_to_with tfxtbl_rtA_ok HS (0x73a18 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss6 (restrict _ ?ms6) => lazymatch type of HF with frame_of _ ?rs6 (ms_mem ?ms5) _ =>
assert (NEW6 : val_mem tfxsegs (mrestrict Hd (ms_mem ms6)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INV6 : INV (ms_mem ms6) acc')
by (img_try (img_apply (INV_runQ E ss6 rs6 ms5 ms6 acc acc' ra (or_intror INV5) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW6)));
clear HF INV5 NEW6 end end.
rreg HS (12%bv : bv 5) G12. rreg HS (15%bv : bv 5) G15.
lazymatch type of HS with st_ok _ _ ?ss6 (restrict _ ?ms6) =>
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem ms6)) (this + 8) 4 (Z.of_nat (length acc')))
by (img_try (memv HS 2%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_try (img_exact EZ1) | img_try (clear - Hlen'; img_lia)]));
destruct (reabs_L E ss6 ms6 (ms_mem ms6) n' ra' nfp (Z.of_nat (length acc')) HS HE eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
ltac:(img_try (rewrite G12, <- ENFP; symmetry; img_apply Z_to_bv_bv_unsigned))
ltac:(img_try (rewrite G15; img_exact EZ1))
SZ ltac:(img_try (clear - Hlen'; img_lia)) (fun a Ha => INV_pres_obj _ _ a INV6 ltac:(img_try (clear - Ha; numconst; img_lia))) (proj1 INV6)
ltac:(img_try (clear - Hb1 Hn1; img_lia)) ltac:(img_try (clear - Hn2; img_lia)) Hn3 Hl1 Hl2 H4096')
as (HSL & HEL & EN' & ER' & EB' & EZ' & EQ')
end.
pose proof (rdword_range _ _ _ _ Hl1) as RR'. pose proof (rdword_range _ _ _ _ Hl2) as NR'.
lazymatch type of HSL with st_ok _ ?E' _ (restrict _ ?ms6) =>
apply (IH acc' E' ms6 _ HSL HEL INV6) end.
** rewrite EZ'. img_apply unsigned_lit_small. clear - Hlen'; img_lia.
** rewrite EQ'. img_apply unsigned_lit_small. clear - Hlen' Z1 Z14 Z15 Z18 Z4; numconst; img_lia.
** rewrite EB', unsigned_lit_small by (img_try (clear - Hb1 Hn1 Hn2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)). clear - Hb1 Hn1; img_lia.
** rewrite EB', unsigned_lit_small by (img_try (clear - Hb1 Hn1 Hn2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)). clear - Hn2; img_lia.
** rewrite EB', unsigned_lit_small by (img_try (clear - Hb1 Hn1 Hn2 Z1 Z2 Z3 Z4 Z17; numconst; img_lia)). img_exact Hrest.
** rewrite EN', ER', !unsigned_lit_small by first [img_exact RR' | img_exact NR']. split; img_refl.
** rewrite HTR. cbn [flat_map]. unfold Fr at 1. replace (ra =? pc0) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_exact Hrapc)).
(subst acc'; cbv beta). rewrite <- app_assoc. img_refl.
++
apply cond_and7 in Hc. rewrite ENFP in Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ ?ss6 (restrict _ ?ms6) => lazymatch type of HF with frame_of _ ?rs6 (ms_mem ?ms5) _ =>
assert (NEW6 : val_mem tfxsegs (mrestrict Hd (ms_mem ms6)) (this + 16 + 8 * Z.of_nat (length acc)) 8 ra)
by (img_try (memv HS 0%nat 0%nat; [img_try (rewrite EQ; clear; img_lia) | img_try (cbn [sv_denot]; rewrite ERA, Z.add_0_r; img_refl) | img_try (pose proof (rdword_range _ _ _ _ Hrd1); clear - H; img_lia)]));
assert (INVa : INV (ms_mem ms6) acc')
by (img_try (img_apply (INV_runQ E ss6 rs6 ms5 ms6 acc acc' ra (or_intror INV5) eq_refl Hlen HE EQ ltac:((img_case; vm_compute); img_refl) HS HF ltac:((img_case; vm_compute); img_refl) NEW6)));
clear HF INV5 NEW6 end end.
do_exit HS HE INVa THIS 2%nat acc' Hlen'.
{ img_exact EZ1. }
img_apply TRX. unfold bad_next. rewrite Hc. cbn [negb]. rewrite !Bool.orb_true_r. img_refl.
Qed.
Lemma unw_main : forall mat, SRr tfxsegs W (mkCfg msU0 (with_vm_backing (m_vm_lazy md) mat md)) UPOST.
Proof.
intros mat. pose proof Hwx_tfa as Hwx. pose proof SEED_ok as HS. zone.
assert (HE0 : envU E0) by (img_try (intros k Hk; img_refl)).
srr_run_with tfxtbl_rtA_ok HS. rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
assert (INV1 : INV (ms_mem ms1) [pc0])
by (img_try (img_apply (INV_run E0 ss1 (ss_mem SS_U0) msU0 ms1 [pc0] INV_start HE0 ltac:((img_case; vm_compute); img_refl) HS HF1 ltac:((img_case; vm_compute); img_refl))))
end.
clear HF1. srr_branch_with tfxtbl_rtA_ok HS.
-
srr_run_to_with tfxtbl_rtA_ok HS (0x73a54 + D_2c4). rename HF into HF2. clear HFr.
lazymatch type of HS with st_ok _ _ ?ssA (restrict _ ?msA) =>
lazymatch type of HF2 with frame_of _ ?rs2 (ms_mem ?ms1) _ =>
assert (INVa : INV (ms_mem msA) [pc0])
by (img_try (img_apply (INV_run E0 ssA rs2 ms1 msA [pc0] INV1 HE0 ltac:((img_case; vm_compute); img_refl) HS HF2 ltac:((img_case; vm_compute); img_refl))));
clear INV1 HF2
end end.
assert (THIS : bv_unsigned (ew E0 10) = this).
{ rewrite E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
lazymatch type of HS with st_ok _ _ ?ssA (restrict _ ?msA) =>
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem msA)) (this + 8) 4 1) by (img_try (memv HS 1%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_refl | img_try (clear; img_lia)]));
destruct (reabs_X E0 ssA msA 1 HS HE0 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; unfold LFIX, UCONST; cbn [app]; sub_keep; sub_drop; sub_keep; sub_keep; sub_drop; do 10 sub_keep; img_apply submem_nil))
SZ ltac:(img_try (clear; img_lia)) (fun a Ha => INV_pres_obj _ _ a INVa ltac:(img_try (clear - Ha; numconst; img_lia)))) as (HSX & HEX & HZX)
end.
eapply (exit_ok _ _ _ [pc0] HSX HEX INVa); [img_try (rewrite HZX; img_refl)|].
unfold TR. destruct (bp + 16 <? top) eqn:Hlt; [| img_refl]. exfalso.
apply Z.ltb_lt in Hlt. unfold branch_taken, bv_ltu in Hc. rewrite !denot_SOff, E12, EaTOP' in Hc.
rewrite !unsigned_lit_small in Hc by (img_try (clear - Z1 Z2 Z3 Z4 Z17 Z18; numconst; img_lia)). unfold zcanon in Hc.
rewrite !Z.mod_small in Hc by (img_try (clear - Z1 Z2 Z3 Z4 Z17 Z18; numconst; img_lia)).
apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. clear - Hc Hlt. img_lia.
-
apply (condZ E0 BC_GEU 12 0 34 (-16) false) in Hc;
[| img_try (rewrite E12, unsigned_lit_small by (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia); clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia)
| img_try (rewrite EaTOP', unsigned_lit_small by (clear - Z1 Z2 Z3 Z4; numconst; img_lia); clear - Z1 Z2 Z3 Z4; numconst; img_lia)].
cbn beta iota in Hc. rewrite E12, EaTOP', !unsigned_lit_small in Hc by (img_try (clear - Z1 Z2 Z3 Z4 Z17 Z18; numconst; img_lia)).
apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. rewrite Z.add_0_r in Hc.
assert (Hc' : bp + 16 < top) by (img_try (clear - Hc; img_lia)). clear Hc. rename Hc' into Hc.
srr_run_to_with tfxtbl_rtA_ok HS (0x73a18 + D_2c4). rename HF into HF2. clear HFr.
lazymatch type of HS with st_ok _ _ ?ssL (restrict _ ?msL) =>
lazymatch type of HF2 with frame_of _ ?rs2 (ms_mem ?ms1) _ =>
assert (INVL : INV (ms_mem msL) [pc0])
by (img_try (img_apply (INV_run E0 ssL rs2 ms1 msL [pc0] INV1 HE0 ltac:((img_case; vm_compute); img_refl) HS HF2 ltac:((img_case; vm_compute); img_refl))));
clear INV1 HF2
end end.
assert (THIS : bv_unsigned (ew E0 10) = this).
{ rewrite E10. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia. }
rreg HS (12%bv : bv 5) G12. rewrite E12 in G12. rreg HS (15%bv : bv 5) G15.
lazymatch type of HS with st_ok _ _ ?ssL (restrict _ ?msL) =>
assert (SZ : val_mem tfxsegs (mrestrict Hd (ms_mem msL)) (this + 8) 4 1) by (img_try (memv HS 1%nat 0%nat; [img_try (rewrite THIS; img_refl) | img_refl | img_try (clear; img_lia)]));
destruct (reabs_L E0 ssL msL (ms_mem msL) nfp0 ra0 bp 1 HS HE0 eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; sub_keep; sub_drop; sub_keep; sub_keep; sub_drop; img_apply submem_refl))
G12 G15 SZ ltac:(img_try (clear; img_lia)) (fun a Ha => INV_pres_obj _ _ a INVL ltac:(img_try (clear - Ha; numconst; img_lia))) (proj1 INVL)
ltac:(img_try (clear; img_lia)) ltac:(img_try (clear - Hc; img_lia)) Hbp8 Hra0 Hnfp0 Hra0_4096)
as (HSL & HEL & EN' & ER' & EB' & EZ' & EQ')
end.
pose proof nfp0_range as NR. pose proof ra0_range as RR.
lazymatch type of HSL with st_ok _ ?E' _ (restrict _ ?msL) =>
apply (loop_ok ((bp, ra0, nfp0) :: ch) [pc0] E' msL _ HSL HEL INVL) end.
+ rewrite EZ'. img_case; vm_compute. all: img_refl.
+ rewrite EQ'. cbn [length Z.of_nat Pos.of_succ_nat]. img_apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; img_lia.
+ rewrite EB', unsigned_lit_small by (img_try (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia)). clear; img_lia.
+ rewrite EB', unsigned_lit_small by (img_try (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia)). img_exact Hc.
+ rewrite EB', unsigned_lit_small by (img_try (clear - Z1 Z2 Z17 Z18 Z4; numconst; img_lia)). cbn [fpchain].
split; [img_refl|]. split; [img_try (img_exact Hbp8)|]. split; [img_try (img_exact Hra0)|]. split; [img_try (img_exact Hnfp0)|]. split; [img_try (img_exact Hra0_4096)|].
pose proof Hch as HC. replace (bp + 16 <? top) with true in HC by (img_try (symmetry; img_apply Z.ltb_lt; img_exact Hc)).
destruct (bad_next bp top nfp0); [img_try (img_exact HC) | img_try (img_exact (proj2 HC))].
+ rewrite EN', ER', !unsigned_lit_small by first [img_exact RR | img_exact NR]. split; img_refl.
+ unfold TR. replace (bp + 16 <? top) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_exact Hc)). img_refl.
Qed.
Theorem unw_spec_ok : SRr tfxsegs W (mkCfg msU0 md) UPOST.
Proof.
rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)). img_apply unw_main.
Qed.
End g.
Theorem tfx_unwind_ok {imgk : img} : tfx_unwind_spec.
Proof.
intros W ly regs mem md this pc0 bp ra0 nfp0 ch Hh m sp T. intros.
eapply unw_spec_ok; eassumption.
Qed.
End e.

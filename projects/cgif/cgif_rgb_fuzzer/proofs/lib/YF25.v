(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF2d YF1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_TP, TFX_TSD in *.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variables (p nn hb1 : Z) (q : qcache) (lastb : batch) (j1 j2 j3 : Z).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53100 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii.
Local Notation tr := (YF2d.tr ly regs0 ch).
Local Notation LENv := (YF2d.LENv ly regs0 ch).
Local Notation IMv := (YF2d.IMv p).
Local Notation HWv := (YF2d.HWv hb1).
Local Notation SPv := (YF2d.SPv p).
Local Notation N8v := (YF2d.N8v nn).
Local Notation CNT8v := (YF2d.CNT8v nn).
Local Notation Bv := (YF2d.Bv ly lastb).
Local Notation BBv := (YF2d.BBv lastb).
Local Notation BCv := (YF2d.BCv lastb).
Local Notation SLOTv := (YF2d.SLOTv ly lastb).
Local Notation QSv := (YF2d.QSv q).
Local Notation QFv := (YF2d.QFv ly q).
Local Notation QBv := (YF2d.QBv q).
Local Notation XW := (YF2d.XW ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E0 := (YF2d.E0 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation Er := (YF2d.Er ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E2 := (YF2d.E2 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E1 := (YF2d.E1 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E8 := (YF2d.E8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E10 := (YF2d.E10 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E4 := (YF2d.E4 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaT := (YF2d.EaT ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaC := (YF2d.EaC ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSB := (YF2d.EaSB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaTOP := (YF2d.EaTOP ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaLEN := (YF2d.EaLEN ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaIM := (YF2d.EaIM ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaHW := (YF2d.EaHW ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaN := (YF2d.EaN ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSHB := (YF2d.EaSHB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSP := (YF2d.EaSP ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaN8 := (YF2d.EaN8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaCNT8 := (YF2d.EaCNT8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaB := (YF2d.EaB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaBB := (YF2d.EaBB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaBC := (YF2d.EaBC ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSLOT := (YF2d.EaSLOT ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQS := (YF2d.EaQS ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQF := (YF2d.EaQF ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQB := (YF2d.EaQB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ1 := (YF2d.EaJ1 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ2 := (YF2d.EaJ2 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ3 := (YF2d.EaJ3 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation AL := YF2d.AL.
Local Notation HB1MASK := (YF2d.HB1MASK hb1).
Local Notation PSTATIC := (YF2d.PSTATIC ly p nn).
Local Notation PBDISJ := (YF2d.PBDISJ ly p nn lastb).
Local Notation REG0 := YF2d.REG0.
Local Notation SS0 := YF2d.SS0.
Local Notation LYB := (YF2d.LYB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation LYD := (YF2d.LYD W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation iv_vs_stack := (YF2d.iv_vs_stack W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation N8_ge := (YF2d.N8_ge W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation stack_ivs := (YF2d.stack_ivs W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation derived_ranges := (YF2d.derived_ranges W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation derived_align := (YF2d.derived_align W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WINT := (YF2d.WINT ly).
Local Notation WINB := (YF2d.WINB ly p lastb).
Local Notation WIN := (YF2d.WIN ly regs0 p lastb).
Local Notation WSKEL := YF2d.WSKEL.
Local Notation win_sub := YF2d.win_sub.
Local Notation win_sub_sound := (YF2d.win_sub_sound W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WSKEL_WIN := (YF2d.WSKEL_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation windows_WIN := (YF2d.windows_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation frame_WIN := (YF2d.frame_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_zone := (YF2d.WIN_zone W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_off := (YF2d.WIN_off W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_not_high := (YF2d.WIN_not_high W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation all_disjoint_of_forall := (YF2d.all_disjoint_of_forall W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_frame := (YF2d.kept_of_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_frame_hi := (YF2d.kept_of_frame_hi W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_vframe := (YF2d.kept_of_vframe W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation p_ivs := (YF2d.p_ivs W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation SKEL_TAIL := YF2d.SKEL_TAIL.
Local Notation DZONE := (YF2d.DZONE ly).
Local Notation IZONE := YF2d.IZONE.
Local Notation tail_facts := (YF2d.tail_facts W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation MEQ := (YF2d.MEQ ly regs0 mem0 p lastb).
Local Notation IAL_POST := (YF2d.IAL_POST W).
Local Notation MEQI := (YF2d.MEQI W ly regs0 mem0 p lastb).
Local Notation MEQI_frame := (YF2d.MEQI_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN2 := (YF2d.WIN2 ly regs0 p lastb).
Local Notation WIN2_WIN := (YF2d.WIN2_WIN ly regs0 p lastb).
Local Notation WSKEL2 := YF2d.WSKEL2.
Local Notation WSKEL2_WIN2 := (YF2d.WSKEL2_WIN2 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation windows_WIN2 := (YF2d.windows_WIN2 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation OBJQ := (YF2d.OBJQ regs0).
Local Notation MEQJ := (YF2d.MEQJ W ly regs0 mem0 p lastb).
Local Notation MEQJ_frame := (YF2d.MEQJ_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation memset_stretch := (YF2d.memset_stretch W ly regs0 mem0 md0 ch p nn hb1 q lastb j1 j2 j3 ii mat0 FH).
Local Notation notWIN_img := (YF2d.notWIN_img W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_shb := (YF2d.notWIN_shb W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_Thead := (YF2d.notWIN_Thead W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_C := (YF2d.notWIN_C W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_NB := (YF2d.notWIN_NB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_SB := (YF2d.notWIN_SB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hq Hlastb HB HB_al HBp HB_pres Hjunk HIAL IA1 U1 SEED].
Local Notation off_T := (YF2d.off_T W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_C := (YF2d.off_C W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_NB := (YF2d.off_NB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_SB := (YF2d.off_SB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_P := (YF2d.off_P W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_P8 := (YF2d.off_P8 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation pres_off_of_frame := (YF2d.pres_off_of_frame W).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize; tac | img_apply off_C; tac | img_apply off_P8; tac | img_apply off_P; tac
| img_apply off_NB; unfold kNodesBlockSize; tac | img_apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Definition at_U1 (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) regs2 mem2 mat (E1 : env),
c' = mkCfg (mkst regs2 (w64 (0x532a0 + D_2c4)) mem2 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAVf)%nat -> ew E1 k = ew E0 k) /\
st_ok tfxsegs E1 SS_A (restrict (w_H W) ms) /\
regs_preserved (ms_regs ms) regs2 /\
(forall x : word, ~ (sp0 - 2128 - UNW_STK <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 2120 <= bv_unsigned x < sp0 - 2116) ->
~ (sp0 - 2112 <= bv_unsigned x < sp0 - 2112 + 8 * 30) -> ~ (sp0 - 72 <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem ms x) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) /\
val_mem tfxsegs (mrestrict (w_H W) mem2) (sp0 - 2120) 4 LENv /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) mem2) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfxsegs (mrestrict (w_H W) mem2) (sp0 - 72) 8 sp0 /\
MEQI (ms_mem ms) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma segA : SRr tfxsegs W cfg0 at_U1.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
srr_run_to_sh tfxtbl_rtF_ok HS (0x5e984 + D_2c4).
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
eapply SRr_bind.
{ destruct HIAL as (IA & IB & IC & ID).
assert (FR : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ms_mem ms (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. img_apply HF. intros Hw.
lazymatch type of Hw with in_wrange _ ?rs _ =>
pose proof (WIN_zone _ (windows_WIN E0 rs _ (fun k _ => eq_refl) ltac:(img_try ((img_case; vm_compute); img_refl)) Hw)) as (X & _) end.
rewrite unsigned_lit_small in X by (img_try (unfold zone3, kLowShadowBeg, TFX_IMG_LO, TFX_IMG_END in Ha; img_lia)). img_exact (X Ha). }
img_apply (IA1 W (ms_regs ms) (ms_mem ms) _ ii).
- rreg HS (1%bv : bv 5) R1; rewrite R1. img_apply YK0s.ret_ok_even. img_refl.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (numconst; img_lia)).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hsp_al.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (numconst; img_lia)). numconst; img_lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (numconst; img_lia)). numconst; img_lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (numconst; img_lia)).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite E2; numconst; img_lia)
| img_try (off_by ltac:(numconst; img_lia)) ].
- eapply val_mem_frame; [|img_try (img_exact IA)]. intros k Hk. img_apply FR; numconst; img_lia.
- eapply val_mem_frame; [|img_try (img_exact IB)]. intros k Hk. img_apply FR; numconst; img_lia.
- memv HS 21%nat 0%nat; [img_refl | img_refl | img_lia].
- memv HS 22%nat 0%nat; [img_refl | img_refl | img_lia].
- destruct ii; destruct IC as [IC1 IC2]; split; (eapply val_mem_frame; [|img_try (eassumption)]); intros k Hk; img_apply FR; numconst; img_lia.
- intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem0 (ms_mem ms) a) by (img_try (img_apply FR; numconst; img_lia)). img_apply ID. img_exact Ha. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & H10r & Hfr & Hpr & IV1 & IV2 & IV3 & IV4 & IV5). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
pose proof derived_ranges as DR.
set (X1 := fun a : Z => (sp0 - 2176 <= a < sp0 - 2128) \/ IZONE a).
assert (Hfr' : forall x : word, ~ X1 (bv_unsigned x) -> mem1 x = ms_mem ms x).
{ intros x Hx. (subst X1; cbv beta). unfold IZONE in Hx. rewrite R2 in Hfr. unfold w64 in Hfr. rewrite unsigned_lit_small in Hfr by (img_try (numconst; img_lia)).
img_apply Hfr; unfold IAL_STK in *; tauto || (intros HH; img_apply Hx; tauto) || img_lia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-2128) (seq 0 36) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ img_try (constructor;
[ eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:((subst X1; cbv beta); unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; img_lia) Hpr)); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite E2; (subst X1; cbv beta); unfold IZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; img_lia
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:((subst X1; cbv beta); unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; img_lia) Hpr)); intros a Ha; (subst X1; cbv beta); unfold IZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y5; numconst; img_lia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. img_apply Hpr; [img_try (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; img_lia)|]. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite E2; numconst; img_lia) | img_try (off_by ltac:(numconst; img_lia)) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (img_try (intros k Hk; (subst En1; cbv beta); img_apply ew_havoc_old; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2; unfold IFRAME;
split; [img_try (numconst; img_lia)|]; split; [img_try (numconst; img_lia)|]; split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(numconst; img_lia) | img_apply PRES1; numconst; img_lia]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME; img_lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; img_lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 37%nat) 8 16 0 0 [YQ0b.mkChunk 8 (CZero 8)])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 37%nat ltac:(img_try ((img_case; cbv); img_lia))), EaIM; unfold w64; rewrite unsigned_lit_small by (img_try (numconst; img_lia));
split; [img_lia|]; split; [img_try (numconst; img_lia)|]; split; [img_try (intros o Ho; img_lia)|];
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]; intros i Hi; cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [img_refl|]; img_apply IV5; numconst; img_lia
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 37%nat ltac:(img_try ((img_case; cbv); img_lia))), (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (img_try (numconst; img_lia)); numconst; img_lia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 37%nat ltac:(img_try ((img_case; cbv); img_lia))), (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (img_try (numconst; img_lia)); numconst; img_lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 37%nat ltac:(img_try ((img_case; cbv); img_lia))), EaIM;
unfold w64; rewrite unsigned_lit_small by (img_try (numconst; img_lia)); clear - Y5 DR; numconst; img_lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit TFX_IAL_LO)) in HS1; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot ms_regs]; symmetry; img_exact H10r)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ1 : MEQI mem1).
{ split.
- intros x Hx Hz. rewrite Hfr' by (img_try ((subst X1; cbv beta); cbn beta; intros [HH|HH]; [img_try (img_apply Hx; left; unfold ASTACK; img_lia) | img_try (img_exact (Hz HH))])).
img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN E0 (ss_mem SS0) _ (fun k _ => eq_refl) ltac:(img_try ((img_case; vm_compute); img_refl)) Hw).
- img_exact (conj IV1 (conj IV2 (conj IV3 (conj IV4 IV5)))). }
clear HF HFr Hfr Hfr'.
srr_run_sh tfxtbl_rtF_ok HS. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(img_try ((img_case; cbv); img_lia))), E10, Hp10. unfold w64. rewrite unsigned_lit_small by img_lia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by img_lia. rewrite Z.div_small by img_lia. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtF_ok HS (0x53154 + D_2c4). meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 37%nat 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(img_try ((img_case; cbv); img_lia))), (HEn1 37%nat ltac:(img_try ((img_case; cbv); img_lia))), E10, Hp10, EaIM. unfold w64.
unfold YF2d.IMv in *. rewrite !unsigned_lit_small by img_lia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by img_lia. img_change (2 ^ 3) with 8. img_change (2 ^ 32) with 4294967296 in *.
zcanon_simp. img_lia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtF_ok HS (0x5aea0 + D_2c4). meq_acc HEn1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; numconst; img_lia) | img_try (off_by ltac:(numconst; img_lia)) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; numconst; img_lia) | img_try (off_by ltac:(numconst; img_lia)) ]. }
eapply SRr_bind.
{ img_apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2128) (0x53244 + D_2c4) sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2. unfold sp0. f_equal; img_lia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2. unfold sp0. symmetry. img_apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. img_apply YK0s.ret_ok_even. img_refl. }
1:{ img_lia. }
1:{ memv HS 3%nat 0%nat; [img_refl | img_refl | img_lia]. }
1:{ memv HS 7%nat 0%nat; [img_refl | img_refl | img_lia]. }
1:{ memv HS 8%nat 0%nat; [img_refl | img_refl | img_lia]. }
1:{ memv HS 28%nat 0%nat; [img_refl | img_refl | img_try (unfold TFX_TSD; img_lia)]. }
1:{ memv HS 29%nat 0%nat; [img_refl | img_try (cbn [sv_denot]; rewrite (HEn1 33%nat ltac:((img_case; cbv); img_lia)), EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia) | img_try (clear - LB; numconst; img_lia)]. }
1:{ memv HS 30%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 33%nat ltac:((img_case; cbv); img_lia)), EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; img_lia); img_lia)
| img_try (cbn [sv_denot]; rewrite (HEn1 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia) | img_try (clear - LB; numconst; img_lia)]. }
1:{ memv HS 31%nat 3%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; img_lia); img_lia) | img_refl | img_lia]. }
1:{ memv HS 31%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; img_lia); img_lia)
| img_try (cbn [sv_denot]; rewrite (HEn1 35%nat ltac:((img_case; cbv); img_lia)), EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia) | img_try (clear - LB; numconst; img_lia)]. }
1:{ memv HS 31%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; img_lia); img_lia)
| img_try (cbn [sv_denot]; rewrite (HEn1 35%nat ltac:((img_case; cbv); img_lia)), EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; img_lia)
| img_try (unfold ly_bot, kStackSpan; clear - LB; numconst; img_lia)]. }
1:{ memv HS 33%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; img_lia); unfold t_unwinding; img_lia) | img_refl | img_lia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 33 _ _ HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn1 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; img_lia); numconst; img_lia) | img_try (off_by ltac:(clear - LB; numconst; img_lia)) ]. }
1:{ memv HS 23%nat 0%nat; [img_refl | img_refl | img_lia]. }
1:{ memv HS 24%nat 0%nat; [img_refl | img_refl | img_lia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; img_lia)).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; img_lia)). clear - Hlo LB; numconst; img_lia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - Usp Hlo LB; numconst; img_lia)). img_apply PRES2. clear - Ha; numconst; img_lia. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by img_lia.
rewrite Z_mod_plus_full. img_apply (mod0_factor _ 8 2); [img_lia | img_try (img_exact Hsp_al)]. }
1:{ clear - Hlo LB; numconst; img_lia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; img_lia)). img_lia. }
1:{ intros a Ha. img_apply PRES2. clear - Ha; numconst; img_lia. }
1:{ clear; numconst; img_lia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; img_lia)). img_lia. }
1:{ img_exact Hbot. }
1:{ img_exact Hhi. }
1:{ img_apply (mod0_factor _ 8 2); [img_lia | img_try (img_exact Hsp_al)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 2%nat 9%nat;
[img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; unfold sp0; img_lia) | img_try (cbn [sv_denot]; rewrite (HEn1 1%nat ltac:((img_case; cbv); img_lia)), E1, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 2%nat 8%nat;
[img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; unfold sp0; img_lia) | img_try (cbn [sv_denot]; rewrite (HEn1 8%nat ltac:((img_case; cbv); img_lia)), E8, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|img_try (img_exact Hch)].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [img_try (img_exact Hch)|].
destruct Hch as [H16 Hfp]. split; [img_try (img_exact H16)|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [img_try (img_exact Hfp) | img_lia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|img_try (img_exact Hva)]. intros i Hi. img_apply aview_same.
img_apply (proj1 MEQU (Z_to_bv 64 (a + i))); rewrite unsigned_lit_small by (img_try (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; img_lia)).
- img_apply WIN_not_high. img_lia.
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold YF2d.IZONE in Hz. numconst. img_lia. }
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model.
img_apply SRr_ret. split; [img_refl|].
rreg HS (1%bv : bv 5) Q1.
exists msU, regs2, mem2, mat2, En1.
split; [img_try (rewrite Q1; img_refl)|]. split; [img_try (img_exact HEn1)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact HP2)|].
split. { intros x H1 H2 H3 H4. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (img_try (clear - Usp Hlo LB; numconst; img_lia)).
img_apply Hfr2; clear - H1 H2 H3 H4; img_lia. }
split; [img_try (img_exact Hpr2)|].
unfold call_trace, frame0_ok, spZ, raZ, s0Z in *. fold sp0 in Ht1, Ht2.
split. { unfold YF2d.LENv, YF2d.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. eapply val_mem_addr; [img_try (img_exact Ht1) | img_lia]. }
split. { intros i Hi. eapply val_mem_addr; [img_try (img_apply Ht2) | img_lia]. unfold YF2d.tr, call_trace, frame0_ok, spZ, raZ, s0Z in Hi. img_exact Hi. }
split. { eapply val_mem_addr; [img_try (img_exact Ht3) | img_lia]. }
split; [img_try (img_exact MEQU) | img_try (img_exact PRES2)].
Qed.
End WK.
End b.

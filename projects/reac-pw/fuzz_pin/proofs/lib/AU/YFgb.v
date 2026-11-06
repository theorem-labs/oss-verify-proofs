(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFgb.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AFgb.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFgb.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFgb.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import YB1w YE3d YFeq YFgm YFfw.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variables (p nn hb1 : Z) (q : qcache) (j1 j2 j3 : Z).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52b50) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii.
Local Notation tr := (YFgm.tr ly regs0 ch).
Local Notation LENv := (YFgm.LENv ly regs0 ch).
Local Notation IMv := (YFgm.IMv p).
Local Notation HWv := (YFgm.HWv hb1).
Local Notation SPv := (YFgm.SPv p).
Local Notation N8v := (YFgm.N8v nn).
Local Notation CNT8v := (YFgm.CNT8v nn).
Local Notation QBFv := (YFgm.QBFv nn q).
Local Notation XW := (YFgm.XW ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E0 := (YFgm.E0 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation Er := (YFgm.Er ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E2 := (YFgm.E2 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E1 := (YFgm.E1 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E8 := (YFgm.E8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E10 := (YFgm.E10 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E4 := (YFgm.E4 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaT := (YFgm.EaT ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaC := (YFgm.EaC ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSB := (YFgm.EaSB ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaTOP := (YFgm.EaTOP ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaLEN := (YFgm.EaLEN ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaIM := (YFgm.EaIM ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaHW := (YFgm.EaHW ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaN := (YFgm.EaN ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSHB := (YFgm.EaSHB ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSP := (YFgm.EaSP ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaN8 := (YFgm.EaN8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaCNT8 := (YFgm.EaCNT8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaQBF := (YFgm.EaQBF ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ1 := (YFgm.EaJ1 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ2 := (YFgm.EaJ2 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ3 := (YFgm.EaJ3 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation AL := YFgm.AL.
Local Notation HB1MASK := (YFgm.HB1MASK hb1).
Local Notation PSTATIC := (YFgm.PSTATIC ly p nn).
Local Notation REG0 := YFgm.REG0.
Local Notation FFM := YFgm.FFM.
Local Notation SS0 := YFgm.SS0.
Local Notation LYB := (YFgm.LYB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation LYD := (YFgm.LYD W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation iv_vs_stack := (YFgm.iv_vs_stack W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation N8_ge := (YFgm.N8_ge W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation stack_ivs := (YFgm.stack_ivs W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation derived_ranges := (YFgm.derived_ranges W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation derived_align := (YFgm.derived_align W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WINT := (YFgm.WINT ly).
Local Notation WINB := (YFgm.WINB p).
Local Notation WIN := (YFgm.WIN ly regs0 p).
Local Notation WSKEL := YFgm.WSKEL.
Local Notation win_sub := YFgm.win_sub.
Local Notation win_sub_sound := (YFgm.win_sub_sound W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WSKEL_WIN := (YFgm.WSKEL_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation windows_WIN := (YFgm.windows_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation frame_WIN := (YFgm.frame_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_zone := (YFgm.WIN_zone W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_off := (YFgm.WIN_off W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_not_high := (YFgm.WIN_not_high W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation all_disjoint_of_forall := (YFgm.all_disjoint_of_forall W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_frame := (YFgm.kept_of_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_frame_hi := (YFgm.kept_of_frame_hi W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_vframe := (YFgm.kept_of_vframe W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation p_ivs := (YFgm.p_ivs W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation SKEL_TAIL := YFgm.SKEL_TAIL.
Local Notation DZONE := (YFgm.DZONE ly).
Local Notation IZONE := YFgm.IZONE.
Local Notation tail_facts := (YFgm.tail_facts W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation MEQ := (YFgm.MEQ ly regs0 mem0 p).
Local Notation IAL_POST := (YFgm.IAL_POST W).
Local Notation MEQI := (YFgm.MEQI W ly regs0 mem0 p).
Local Notation MEQI_frame := (YFgm.MEQI_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN2 := (YFgm.WIN2 ly regs0 p).
Local Notation WIN2_WIN := (YFgm.WIN2_WIN ly regs0 p).
Local Notation WSKEL2 := YFgm.WSKEL2.
Local Notation WSKEL2_WIN2 := (YFgm.WSKEL2_WIN2 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation windows_WIN2 := (YFgm.windows_WIN2 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation OBJQ := (YFgm.OBJQ regs0).
Local Notation MEQJ := (YFgm.MEQJ W ly regs0 mem0 p).
Local Notation MEQJ_frame := (YFgm.MEQJ_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation memset_stretch := (YFgm.memset_stretch W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_img := (YFgm.notWIN_img W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_shb := (YFgm.notWIN_shb W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_Thead := (YFgm.notWIN_Thead W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_C := (YFgm.notWIN_C W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_NB := (YFgm.notWIN_NB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_SB := (YFgm.notWIN_SB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hqb Hjunk HIAL IA1 U1 SEED].
Local Notation off_T := (YFgm.off_T W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_C := (YFgm.off_C W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_NB := (YFgm.off_NB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_SB := (YFgm.off_SB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_P := (YFgm.off_P W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_P8 := (YFgm.off_P8 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation pres_off_of_frame := (YFgm.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac | apply off_P8; tac | apply off_P; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Definition at_U1 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) regs2 mem2 mat (E1 : env),
c' = mkCfg (mkst regs2 (w64 0x52cec) mem2 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAVf)%nat -> ew E1 k = ew E0 k) /\
st_ok tfibsegs E1 SS_A (restrict (w_H W) ms) /\
regs_preserved (ms_regs ms) regs2 /\
(forall x : word, ~ (sp0 - 2128 - UNW_STK <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 2120 <= bv_unsigned x < sp0 - 2116) ->
~ (sp0 - 2112 <= bv_unsigned x < sp0 - 2112 + 8 * 30) -> ~ (sp0 - 72 <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem ms x) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) /\
val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2120) 4 LENv /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 72) 8 sp0 /\
MEQI (ms_mem ms) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma segA : SRr tfibsegs W cfg0 at_U1.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
srr_run_to_sh tfibtbl_rtF_ok HS 0x5e08c.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
eapply SRr_bind.
{ destruct HIAL as (IA & IB & IC & ID).
assert (FR : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ms_mem ms (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
lazymatch type of Hw with in_wrange _ ?rs _ =>
pose proof (WIN_zone _ (windows_WIN E0 rs _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)) as (X & _) end.
rewrite unsigned_lit_small in X by (unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END in Ha; zlia). exact (X Ha). }
apply (IA1 W (ms_regs ms) (ms_mem ms) _ ii).
- rreg HS (1%bv : bv 5) R1; rewrite R1. apply YK0s.ret_ok_even. reflexivity.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia). numconst; zlia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia). numconst; zlia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (numconst; zlia).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; zlia
| off_by ltac:(numconst; zlia) ].
- eapply val_mem_frame; [|exact IA]. intros k Hk. apply FR; numconst; zlia.
- eapply val_mem_frame; [|exact IB]. intros k Hk. apply FR; numconst; zlia.
- memv HS 21%nat 0%nat; [reflexivity | reflexivity | zlia].
- memv HS 22%nat 0%nat; [reflexivity | reflexivity | zlia].
- destruct ii; destruct IC as [IC1 IC2]; split; (eapply val_mem_frame; [|eassumption]); intros k Hk; apply FR; numconst; zlia.
- intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem0 (ms_mem ms) a) by (apply FR; numconst; zlia). apply ID. exact Ha. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & H10r & Hfr & Hpr & IV1 & IV2 & IV3 & IV4 & IV5). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
pose proof derived_ranges as DR.
set (X1 := fun a : Z => (sp0 - 2176 <= a < sp0 - 2128) \/ IZONE a).
assert (Hfr' : forall x : word, ~ X1 (bv_unsigned x) -> mem1 x = ms_mem ms x).
{ intros x Hx. subst X1. unfold IZONE in Hx. rewrite R2 in Hfr. unfold w64 in Hfr. rewrite unsigned_lit_small in Hfr by (numconst; zlia).
apply Hfr; unfold IAL_STK in *; tauto || (intros HH; apply Hx; tauto) || zlia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-2128) (seq 0 36) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; subst X1; unfold IZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); intros a Ha; subst X1; unfold IZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y5; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr; [clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia|]. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [numconst; zlia|]; split; [numconst; zlia|]; split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(numconst; zlia) | apply PRES1; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 37%nat) 8 16 0 0 [YP09.mkChunk 8 (CZero 8)])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 37%nat ltac:(cbv; zlia)), EaIM; unfold w64; rewrite unsigned_lit_small by (numconst; zlia);
split; [zlia|]; split; [numconst; zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil]; intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [reflexivity|]; apply IV5; numconst; zlia
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 37%nat ltac:(cbv; zlia)), (HEn1 2%nat ltac:(cbv; zlia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (numconst; zlia); numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 37%nat ltac:(cbv; zlia)), (HEn1 2%nat ltac:(cbv; zlia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (numconst; zlia); numconst; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 37%nat ltac:(cbv; zlia)), EaIM;
unfold w64; rewrite unsigned_lit_small by (numconst; zlia); clear - Y5 DR; numconst; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit TFIB_IAL_LO)) in HS1; [| intros X; discriminate | cbn [sv_denot ms_regs]; symmetry; exact H10r].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ1 : MEQI mem1).
{ split.
- intros x Hx Hz. rewrite Hfr' by (subst X1; cbn beta; intros [HH|HH]; [apply Hx; left; unfold ASTACK; zlia | exact (Hz HH)]).
apply HF. intros Hw. apply Hx. exact (windows_WIN E0 (ss_mem SS0) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw).
- exact (conj IV1 (conj IV2 (conj IV3 (conj IV4 IV5)))). }
clear HF HFr Hfr Hfr'.
srr_run_sh tfibtbl_rtF_ok HS. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(cbv; zlia)), E10, Hp10. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x52ba0. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 37%nat 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(cbv; zlia)), (HEn1 37%nat ltac:(cbv; zlia)), E10, Hp10, EaIM. unfold w64.
unfold YFgm.IMv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by zlia. change (2 ^ 3) with 8. change (2 ^ 32) with 4294967296 in *.
zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x5a5a8. meq_acc HEn1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
eapply SRr_bind.
{ apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2128) 0x52c90 sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity. }
1:{ zlia. }
1:{ memv HS 3%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 7%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 8%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 28%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; zlia]. }
1:{ memv HS 29%nat 0%nat; [reflexivity | cbn [sv_denot]; rewrite (HEn1 33%nat ltac:(cbv; zlia)), EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 30%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 33%nat ltac:(cbv; zlia)), EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 31%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia | reflexivity | zlia]. }
1:{ memv HS 31%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; zlia)), EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 31%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; zlia)), EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; zlia
| unfold ly_bot, kStackSpan; clear - LB; numconst; zlia]. }
1:{ memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 32 _ _ HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); numconst; zlia | off_by ltac:(clear - LB; numconst; zlia) ]. }
1:{ memv HS 23%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 24%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). clear - Hlo LB; numconst; zlia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - Usp Hlo LB; numconst; zlia). apply PRES2. clear - Ha; numconst; zlia. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ clear - Hlo LB; numconst; zlia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). zlia. }
1:{ intros a Ha. apply PRES2. clear - Ha; numconst; zlia. }
1:{ clear; numconst; zlia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). zlia. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 9%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | cbn [sv_denot]; rewrite (HEn1 1%nat ltac:(cbv; zlia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 8%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | cbn [sv_denot]; rewrite (HEn1 8%nat ltac:(cbv; zlia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [exact Hfp | zlia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (proj1 MEQU (Z_to_bv 64 (a + i))); rewrite unsigned_lit_small by (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; zlia).
- apply WIN_not_high. zlia.
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold YFgm.IZONE in Hz. numconst. zlia. }
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model.
apply SRr_ret. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1.
exists msU, regs2, mem2, mat2, En1.
split; [rewrite Q1; reflexivity|]. split; [exact HEn1|]. split; [exact HS|]. split; [exact HP2|].
split. { intros x H1 H2 H3 H4. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; zlia).
apply Hfr2; clear - H1 H2 H3 H4; zlia. }
split; [exact Hpr2|].
unfold call_trace, frame0_ok, spZ, raZ, s0Z in *. fold sp0 in Ht1, Ht2.
split. { unfold YFgm.LENv, YFgm.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. eapply val_mem_addr; [exact Ht1 | zlia]. }
split. { intros i Hi. eapply val_mem_addr; [apply Ht2 | zlia]. unfold YFgm.tr, call_trace, frame0_ok, spZ, raZ, s0Z in Hi. exact Hi. }
split. { eapply val_mem_addr; [exact Ht3 | zlia]. }
split; [exact MEQU | exact PRES2].
Qed.
End WK.
End b.

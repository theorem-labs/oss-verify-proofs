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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF2i YF1s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_TP, TFX_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53100 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch ii.
Local Notation tr := (YF2i.tr ly regs0 ch).
Local Notation LENv := (YF2i.LENv ly regs0 ch).
Local Notation XW := (YF2i.XW ly regs0 ch).
Local Notation E0 := (YF2i.E0 ly regs0 ch).
Local Notation Er := (YF2i.Er ly regs0 ch).
Local Notation E2 := (YF2i.E2 ly regs0 ch).
Local Notation E1 := (YF2i.E1 ly regs0 ch).
Local Notation E8 := (YF2i.E8 ly regs0 ch).
Local Notation E10 := (YF2i.E10 ly regs0 ch).
Local Notation E4 := (YF2i.E4 ly regs0 ch).
Local Notation EaT := (YF2i.EaT ly regs0 ch).
Local Notation EaC := (YF2i.EaC ly regs0 ch).
Local Notation EaSB := (YF2i.EaSB ly regs0 ch).
Local Notation EaTOP := (YF2i.EaTOP ly regs0 ch).
Local Notation EaLEN := (YF2i.EaLEN ly regs0 ch).
Local Notation EaIM := (YF2i.EaIM ly regs0 ch).
Local Notation EaSHB := (YF2i.EaSHB ly regs0 ch).
Local Notation AL := YF2i.AL.
Local Notation REG0 := YF2i.REG0.
Local Notation FFN := YF2i.FFN.
Local Notation SS0 := YF2i.SS0.
Local Notation LYB := (YF2i.LYB W ly regs0 mem0 ch ii FH).
Local Notation LYD := (YF2i.LYD W ly regs0 mem0 ch ii FH).
Local Notation iv_vs_stack := (YF2i.iv_vs_stack W ly regs0 mem0 ch ii FH).
Local Notation stack_ivs := (YF2i.stack_ivs W ly regs0 mem0 ch ii FH).
Local Notation WIN := (YF2i.WIN ly regs0).
Local Notation WSKEL := YF2i.WSKEL.
Local Notation win_sub := YF2i.win_sub.
Local Notation win_sub_sound := (YF2i.win_sub_sound W ly regs0 mem0 ch ii FH).
Local Notation WSKEL_WIN := (YF2i.WSKEL_WIN W ly regs0 mem0 ch ii FH).
Local Notation windows_WIN := (YF2i.windows_WIN W ly regs0 mem0 ch ii FH).
Local Notation frame_WIN := (YF2i.frame_WIN W ly regs0 mem0 ch ii FH).
Local Notation WIN_zone := (YF2i.WIN_zone W ly regs0 mem0 ch ii FH).
Local Notation WIN_off := (YF2i.WIN_off W ly regs0 mem0 ch ii FH).
Local Notation WIN_not_high := (YF2i.WIN_not_high W ly regs0 mem0 ch ii FH).
Local Notation all_disjoint_of_forall := (YF2i.all_disjoint_of_forall W ly regs0 mem0 ch ii FH).
Local Notation kept_of_frame := (YF2i.kept_of_frame W ly regs0 mem0 ch ii FH).
Local Notation kept_of_frame_hi := (YF2i.kept_of_frame_hi W ly regs0 mem0 ch ii FH).
Local Notation kept_of_vframe := (YF2i.kept_of_vframe W ly regs0 mem0 ch ii FH).
Local Notation SKEL_TAIL := YF2i.SKEL_TAIL.
Local Notation IZONE := YF2i.IZONE.
Local Notation tail_facts := (YF2i.tail_facts W ly regs0 mem0 ch ii FH).
Local Notation MEQ := (YF2i.MEQ ly regs0 mem0).
Local Notation IAL_POST := (YF2i.IAL_POST W).
Local Notation MEQI := (YF2i.MEQI W ly regs0 mem0).
Local Notation MEQI_frame := (YF2i.MEQI_frame W ly regs0 mem0 ch ii FH).
Local Notation notWIN_img := (YF2i.notWIN_img W ly regs0 mem0 ch ii FH).
Local Notation notWIN_shb := (YF2i.notWIN_shb W ly regs0 mem0 ch ii FH).
Local Notation notWIN_Thead := (YF2i.notWIN_Thead W ly regs0 mem0 ch ii FH).
Local Notation notWIN_C := (YF2i.notWIN_C W ly regs0 mem0 ch ii FH).
Local Notation notWIN_NB := (YF2i.notWIN_NB W ly regs0 mem0 ch ii FH).
Local Notation notWIN_SB := (YF2i.notWIN_SB W ly regs0 mem0 ch ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch HIAL IA1 U1 SEED].
Local Notation off_T := (YF2i.off_T W ly regs0 mem0 ch ii FH).
Local Notation off_C := (YF2i.off_C W ly regs0 mem0 ch ii FH).
Local Notation off_NB := (YF2i.off_NB W ly regs0 mem0 ch ii FH).
Local Notation off_SB := (YF2i.off_SB W ly regs0 mem0 ch ii FH).
Local Notation pres_off_of_frame := (YF2i.pres_off_of_frame W).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize; tac | img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac | img_apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Definition at_RETN (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
regs_preserved regs0 regs' /\
MEQI mem' /\
val_mem tfxsegs (mrestrict (w_H W) mem') (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a).
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (img_try (img_apply bv_eq; img_refl)) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR; first [ rewrite HEn by (img_try ((img_case; cbv); zlia)); img_apply Er; img_refl | rewrite Htp; img_refl ].
Lemma segN : SRr tfxsegs W cfg0 at_RETN.
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
rewrite unsigned_lit_small in X by (img_try (unfold TFX_IMG_LO, TFX_IMG_END in Ha; zlia)). img_exact (X Ha). }
img_apply (IA1 W (ms_regs ms) (ms_mem ms) _ ii).
- rreg HS (1%bv : bv 5) R1; rewrite R1. img_apply YK0s.ret_ok_even. img_refl.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (numconst; zlia)).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. img_exact Hsp_al.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (numconst; zlia)). numconst; zlia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (numconst; zlia)). numconst; zlia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (numconst; zlia)).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite E2; numconst; zlia)
| img_try (off_by ltac:(numconst; zlia)) ].
- eapply val_mem_frame; [|img_try (img_exact IA)]. intros k Hk. img_apply FR; numconst; zlia.
- eapply val_mem_frame; [|img_try (img_exact IB)]. intros k Hk. img_apply FR; numconst; zlia.
- memv HS 21%nat 0%nat; [img_refl | img_refl | img_try (zlia)].
- memv HS 22%nat 0%nat; [img_refl | img_refl | img_try (zlia)].
- destruct ii; destruct IC as [IC1 IC2]; split; (eapply val_mem_frame; [|img_try (eassumption)]); intros k Hk; img_apply FR; numconst; zlia.
- intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem0 (ms_mem ms) a) by (img_try (img_apply FR; numconst; zlia)). img_apply ID. img_exact Ha. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & H10r & Hfr & Hpr & IV1 & IV2 & IV3 & IV4 & IV5). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
set (X1 := fun a : Z => (sp0 - 2176 <= a < sp0 - 2128) \/ IZONE a).
assert (Hfr' : forall x : word, ~ X1 (bv_unsigned x) -> mem1 x = ms_mem ms x).
{ intros x Hx. (subst X1; cbv beta). unfold IZONE in Hx. rewrite R2 in Hfr. unfold w64 in Hfr. rewrite unsigned_lit_small in Hfr by (img_try (numconst; zlia)).
img_apply Hfr; unfold IAL_STK in *; tauto || (intros HH; img_apply Hx; tauto) || zlia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-2128) (seq 0 36) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ img_try (constructor;
[ eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:((subst X1; cbv beta); unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite E2; (subst X1; cbv beta); unfold IZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:((subst X1; cbv beta); unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); intros a Ha; (subst X1; cbv beta); unfold IZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y5; numconst; zlia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. img_apply Hpr; [img_try (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia)|]. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite E2; numconst; zlia) | img_try (off_by ltac:(numconst; zlia)) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (img_try (intros k Hk; (subst En1; cbv beta); img_apply ew_havoc_old; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; unfold IFRAME;
split; [img_try (numconst; zlia)|]; split; [img_try (numconst; zlia)|]; split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(numconst; zlia) | img_apply PRES1; numconst; zlia]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ R_IMN) in HS1;
[ | img_refl
| unfold R_IMN, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
split; [img_try (zlia)|]; split; [img_try (zlia)|]; split; [img_try (intros o Ho; zlia)|];
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]; intros i Hi; cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [img_refl|]; img_apply IV5; numconst; zlia
| unfold R_IMN; img_apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - Hlo LB; numconst; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; clear - Y5; numconst; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit TFX_IAL_LO)) in HS1; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot ms_regs]; symmetry; img_exact H10r)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ1 : MEQI mem1).
{ split.
- intros x Hx Hz. rewrite Hfr' by (img_try ((subst X1; cbv beta); cbn beta; intros [HH|HH]; [img_try (img_apply Hx; left; unfold ASTACK; zlia) | img_try (img_exact (Hz HH))])).
img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN E0 (ss_mem SS0) _ (fun k _ => eq_refl) ltac:(img_try ((img_case; vm_compute); img_refl)) Hw).
- img_exact (conj IV1 (conj IV2 (conj IV3 (conj IV4 IV5)))). }
clear HF HFr Hfr Hfr'.
srr_run_to_sh tfxtbl_rtF_ok HS (0x5aea0 + D_2c4). meq_acc HEn1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn1 2%nat ltac:((img_case; cbv); zlia)), E2; numconst; zlia) | img_try (off_by ltac:(numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn1 2%nat ltac:((img_case; cbv); zlia)), E2; numconst; zlia) | img_try (off_by ltac:(numconst; zlia)) ]. }
eapply SRr_bind.
{ img_apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2128) (0x53244 + D_2c4) sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2. unfold sp0. symmetry. img_apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. img_refl. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. img_apply YK0s.ret_ok_even. img_refl. }
1:{ zlia. }
1:{ memv HS 3%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 7%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 8%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 28%nat 0%nat; [img_refl | img_refl | img_try (unfold TFX_TSD; zlia)]. }
1:{ memv HS 29%nat 0%nat; [img_refl | img_try (cbn [sv_denot]; rewrite (HEn1 33%nat ltac:((img_case; cbv); zlia)), EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - LB; numconst; zlia)]. }
1:{ memv HS 30%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 33%nat ltac:((img_case; cbv); zlia)), EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia)
| img_try (cbn [sv_denot]; rewrite (HEn1 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - LB; numconst; zlia)]. }
1:{ memv HS 31%nat 3%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia) | img_refl | img_try (zlia)]. }
1:{ memv HS 31%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia)
| img_try (cbn [sv_denot]; rewrite (HEn1 35%nat ltac:((img_case; cbv); zlia)), EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - LB; numconst; zlia)]. }
1:{ memv HS 31%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia)
| img_try (cbn [sv_denot]; rewrite (HEn1 35%nat ltac:((img_case; cbv); zlia)), EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; zlia)
| img_try (unfold ly_bot, kStackSpan; clear - LB; numconst; zlia)]. }
1:{ memv HS 32%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia) | img_refl | img_try (zlia)]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 32 _ _ HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn1 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); numconst; zlia) | img_try (off_by ltac:(clear - LB; numconst; zlia)) ]. }
1:{ memv HS 23%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ memv HS 24%nat 0%nat; [img_refl | img_refl | img_try (zlia)]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; zlia)).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. img_exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; zlia)). clear - Hlo LB; numconst; zlia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (clear - Usp Hlo LB; numconst; zlia)). img_apply PRES2. clear - Ha; numconst; zlia. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. img_apply (mod0_factor _ 8 2); [img_try (zlia) | img_try (img_exact Hsp_al)]. }
1:{ clear - Hlo LB; numconst; zlia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; zlia)). zlia. }
1:{ intros a Ha. img_apply PRES2. clear - Ha; numconst; zlia. }
1:{ clear; numconst; zlia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; numconst; zlia)). zlia. }
1:{ img_exact Hbot. }
1:{ img_exact Hhi. }
1:{ img_apply (mod0_factor _ 8 2); [img_try (zlia) | img_try (img_exact Hsp_al)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 2%nat 9%nat;
[img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 2%nat ltac:((img_case; cbv); zlia)), E2; unfold sp0; zlia) | img_try (cbn [sv_denot]; rewrite (HEn1 1%nat ltac:((img_case; cbv); zlia)), E1, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_apply val_mem_rdword; [img_try (img_apply u64_range)|]. memv HS 2%nat 8%nat;
[img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 2%nat ltac:((img_case; cbv); zlia)), E2; unfold sp0; zlia) | img_try (cbn [sv_denot]; rewrite (HEn1 8%nat ltac:((img_case; cbv); zlia)), E8, Z.add_0_r; img_refl) | img_try (img_apply u64_range)]. }
1:{ img_exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|img_try (img_exact Hch)].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [img_try (img_exact Hch)|].
destruct Hch as [H16 Hfp]. split; [img_try (img_exact H16)|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [img_try (img_exact Hfp) | img_try (zlia) |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|img_try (img_exact Hva)]. intros i Hi. img_apply aview_same.
img_apply (proj1 MEQU (Z_to_bv 64 (a + i))); rewrite unsigned_lit_small by (img_try (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; zlia)).
- img_apply WIN_not_high. zlia.
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold YF2i.IZONE in Hz. numconst. zlia. }
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model. clear Ht1 Ht2 Ht3.
rreg HS (1%bv : bv 5) Q1. rewrite Q1. clear Q1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (img_try (clear - Usp Hlo LB; numconst; zlia)).
img_apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; zlia. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := img_ev (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfxsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) (0x532a0 + D_2c4) HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_drop; img_apply submem_keep; [img_try (img_apply subregion_trim_lo) | img_try (img_apply submem_refl)]))
ltac:(img_try ((img_case; vm_compute); img_refl)) HP2) as HS1;
let rsv := img_ev (rim :: trim_lo rfr (-64) :: rest) in
img_change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := img_ev (ss_after_call ss rsv 70 (0x532a0 + D_2c4)) in
change (ss_after_call ss rsv 70 (0x532a0 + D_2c4)) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ img_try (constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
intros a Ha; cbn beta; clear - Ha Hlo LB Usp; numconst; zlia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn1 2%nat ltac:((img_case; cbv); zlia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; zlia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (img_try (intros a Ha; apply Hpr2, PRES2, Ha)).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (img_try (intros k Hk; (subst En2; cbv beta); unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; img_apply HEn1; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; unfold IFRAME;
split; [img_try (clear - Usp Hlo LB; numconst; zlia)|]; split; [img_try (clear - Usp Hlo LB; numconst; zlia)|];
split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | img_apply PRES3; clear - Ho; numconst; zlia]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQI mem2).
{ destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. img_apply Hfr'. rewrite unsigned_lit_small by (img_try (clear - Ha Ha' Usp; unfold ASTACK in *; zlia)). zlia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). img_apply Hfr'. intros HH. img_apply Hx. left. unfold ASTACK in *. zlia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold YF2i.IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|img_try (eassumption)]; intros k Hk; img_apply LOWEQ; clear - Hk Hlo LB; numconst; zlia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (img_try (img_apply LOWEQ; clear - Ha Hlo LB; numconst; zlia)). img_apply I5. img_exact Ha. }
clear MEQU.
srr_run_to_sh tfxtbl_rtF_ok HS (0x532d8 + D_2c4). clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
pose proof (MEQI_frame En2 rs _ _ HEn2 ltac:(img_try ((img_case; vm_compute); img_refl)) HF MEQ2) as MEQR end.
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAME) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msR y = mem2 y).
{ intros y Y1 Y2 Y3. img_apply HF. intros Hw. destruct (in_wrange_windows En2 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := img_ev (windows rs) in img_change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ img_try (injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn2 2%nat ltac:((img_case; cbv); zlia)), ?E2, ?(HEn2 32%nat ltac:((img_case; cbv); zlia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; zlia);
clear - Y1 Y2 Y3 Hr; unfold IFRAME, ASTACK, t_unwinding in *; unfold sp0, T in *; zlia) |]).
destruct Hin. }
clear HF.
eapply (SRr_ret_at tfxsegs tfxtbl_rtF tfxtbl_rtF_ok Hwx W En2); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|].
rreg HS (1%bv : bv 5) Q1. rewrite (HEn2 1%nat ltac:(img_try ((img_case; cbv); zlia))), E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { intros r Hr. unfold callee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear Hr. repeat match type of R with _ \/ _ => destruct R as [R|R] end; (subst r; cbv beta);
[ img_try (cs_case HS HEn2 Htp (2%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (3%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (4%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (8%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (9%bv : bv 5))
| img_try (cs_case HS HEn2 Htp (18%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (19%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (20%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (21%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (22%bv : bv 5))
| img_try (cs_case HS HEn2 Htp (23%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (24%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (25%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (26%bv : bv 5)) | img_try (cs_case HS HEn2 Htp (27%bv : bv 5)) ]. }
split; [img_try (img_exact MEQR)|].
split. { memv HS 32%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn2 32%nat ltac:((img_case; cbv); zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia) | img_refl | img_try (zlia)]. }
intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)); [|img_try (destruct (Z_lt_le_dec a (sp0 - 64)))].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn2 2%nat ltac:((img_case; cbv); zlia)), E2; clear - Ha l; numconst; unfold sp0; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia)) ].
- img_apply (apresent_same (w_H W) mem2); [|img_try (img_apply PRES3; img_exact Ha)].
img_apply FRR; rewrite unsigned_lit_small by (img_try (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia));
[img_try (clear - Ha l; numconst; zlia) | img_try (clear - Ha l0; zlia) | img_try (pose proof stack_ivs as (IT & _); clear - Ha IT; numconst; unfold sp0, T in *; zlia)].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn2 2%nat ltac:((img_case; cbv); zlia)), E2; clear - Ha l0; numconst; unfold sp0; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia)) ].
Qed.
End WK.
End c.

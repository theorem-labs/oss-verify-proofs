(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AFgn AFfx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x5292c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch ii.
Local Notation tr := (AFgn.tr ly regs0 ch).
Local Notation LENv := (AFgn.LENv ly regs0 ch).
Local Notation XW := (AFgn.XW ly regs0 ch).
Local Notation E0 := (AFgn.E0 ly regs0 ch).
Local Notation Er := (AFgn.Er ly regs0 ch).
Local Notation E2 := (AFgn.E2 ly regs0 ch).
Local Notation E1 := (AFgn.E1 ly regs0 ch).
Local Notation E8 := (AFgn.E8 ly regs0 ch).
Local Notation E10 := (AFgn.E10 ly regs0 ch).
Local Notation E4 := (AFgn.E4 ly regs0 ch).
Local Notation EaT := (AFgn.EaT ly regs0 ch).
Local Notation EaC := (AFgn.EaC ly regs0 ch).
Local Notation EaSB := (AFgn.EaSB ly regs0 ch).
Local Notation EaTOP := (AFgn.EaTOP ly regs0 ch).
Local Notation EaLEN := (AFgn.EaLEN ly regs0 ch).
Local Notation EaIM := (AFgn.EaIM ly regs0 ch).
Local Notation EaSHB := (AFgn.EaSHB ly regs0 ch).
Local Notation AL := AFgn.AL.
Local Notation REG0 := AFgn.REG0.
Local Notation FFN := AFgn.FFN.
Local Notation SS0 := AFgn.SS0.
Local Notation LYB := (AFgn.LYB W ly regs0 mem0 ch ii FH).
Local Notation LYD := (AFgn.LYD W ly regs0 mem0 ch ii FH).
Local Notation iv_vs_stack := (AFgn.iv_vs_stack W ly regs0 mem0 ch ii FH).
Local Notation stack_ivs := (AFgn.stack_ivs W ly regs0 mem0 ch ii FH).
Local Notation WIN := (AFgn.WIN ly regs0).
Local Notation WSKEL := AFgn.WSKEL.
Local Notation win_sub := AFgn.win_sub.
Local Notation win_sub_sound := (AFgn.win_sub_sound W ly regs0 mem0 ch ii FH).
Local Notation WSKEL_WIN := (AFgn.WSKEL_WIN W ly regs0 mem0 ch ii FH).
Local Notation windows_WIN := (AFgn.windows_WIN W ly regs0 mem0 ch ii FH).
Local Notation frame_WIN := (AFgn.frame_WIN W ly regs0 mem0 ch ii FH).
Local Notation WIN_zone := (AFgn.WIN_zone W ly regs0 mem0 ch ii FH).
Local Notation WIN_off := (AFgn.WIN_off W ly regs0 mem0 ch ii FH).
Local Notation WIN_not_high := (AFgn.WIN_not_high W ly regs0 mem0 ch ii FH).
Local Notation all_disjoint_of_forall := (AFgn.all_disjoint_of_forall W ly regs0 mem0 ch ii FH).
Local Notation kept_of_frame := (AFgn.kept_of_frame W ly regs0 mem0 ch ii FH).
Local Notation kept_of_frame_hi := (AFgn.kept_of_frame_hi W ly regs0 mem0 ch ii FH).
Local Notation kept_of_vframe := (AFgn.kept_of_vframe W ly regs0 mem0 ch ii FH).
Local Notation SKEL_TAIL := AFgn.SKEL_TAIL.
Local Notation IZONE := AFgn.IZONE.
Local Notation tail_facts := (AFgn.tail_facts W ly regs0 mem0 ch ii FH).
Local Notation MEQ := (AFgn.MEQ ly regs0 mem0).
Local Notation IAL_POST := (AFgn.IAL_POST W).
Local Notation MEQI := (AFgn.MEQI W ly regs0 mem0).
Local Notation MEQI_frame := (AFgn.MEQI_frame W ly regs0 mem0 ch ii FH).
Local Notation notWIN_img := (AFgn.notWIN_img W ly regs0 mem0 ch ii FH).
Local Notation notWIN_shb := (AFgn.notWIN_shb W ly regs0 mem0 ch ii FH).
Local Notation notWIN_Thead := (AFgn.notWIN_Thead W ly regs0 mem0 ch ii FH).
Local Notation notWIN_C := (AFgn.notWIN_C W ly regs0 mem0 ch ii FH).
Local Notation notWIN_NB := (AFgn.notWIN_NB W ly regs0 mem0 ch ii FH).
Local Notation notWIN_SB := (AFgn.notWIN_SB W ly regs0 mem0 ch ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch HIAL IA1 U1 SEED].
Local Notation off_T := (AFgn.off_T W ly regs0 mem0 ch ii FH).
Local Notation off_C := (AFgn.off_C W ly regs0 mem0 ch ii FH).
Local Notation off_NB := (AFgn.off_NB W ly regs0 mem0 ch ii FH).
Local Notation off_SB := (AFgn.off_SB W ly regs0 mem0 ch ii FH).
Local Notation pres_off_of_frame := (AFgn.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Definition at_RETN (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
regs_preserved regs0 regs' /\
MEQI mem' /\
val_mem tfibsegs (mrestrict (w_H W) mem') (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a).
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (apply bv_eq; reflexivity) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR; first [ rewrite HEn by (cbv; zlia); apply Er; reflexivity | rewrite Htp; reflexivity ].
Lemma segN : SRr tfibsegs W cfg0 at_RETN.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
srr_run_to_sh tfibtbl_rtF_ok HS 0x5de68.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
eapply SRr_bind.
{ destruct HIAL as (IA & IB & IC & ID).
assert (FR : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ms_mem ms (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
lazymatch type of Hw with in_wrange _ ?rs _ =>
pose proof (WIN_zone _ (windows_WIN E0 rs _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)) as (X & _) end.
rewrite unsigned_lit_small in X by (unfold TFIB_IMG_LO, TFIB_IMG_END in Ha; zlia). exact (X Ha). }
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
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
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
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ R_IMN) in HS1;
[ | reflexivity
| unfold R_IMN, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil]; intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [reflexivity|]; apply IV5; numconst; zlia
| unfold R_IMN; apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - Hlo LB; numconst; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; clear - Y5; numconst; zlia ] ].
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
srr_run_to_sh tfibtbl_rtF_ok HS 0x5a384. meq_acc HEn1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
eapply SRr_bind.
{ apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2128) 0x52a6c sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
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
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold AFgn.IZONE in Hz. numconst. zlia. }
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model. clear Ht1 Ht2 Ht3.
rreg HS (1%bv : bv 5) Q1. rewrite Q1. clear Q1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; zlia).
apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; zlia. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) 0x52ac8 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_drop; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP2) as HS1;
let rsv := eval vm_compute in (rim :: trim_lo rfr (-64) :: rest) in
change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 70 0x52ac8) in
change (ss_after_call ss rsv 70 0x52ac8) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
intros a Ha; cbn beta; clear - Ha Hlo LB Usp; numconst; zlia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (intros a Ha; apply Hpr2, PRES2, Ha).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (intros k Hk; subst En2; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn1; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | apply PRES3; clear - Ho; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQI mem2).
{ destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. apply Hfr'. rewrite unsigned_lit_small by (clear - Ha Ha' Usp; unfold ASTACK in *; zlia). zlia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply Hfr'. intros HH. apply Hx. left. unfold ASTACK in *. zlia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold AFgn.IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|eassumption]; intros k Hk; apply LOWEQ; clear - Hk Hlo LB; numconst; zlia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (apply LOWEQ; clear - Ha Hlo LB; numconst; zlia). apply I5. exact Ha. }
clear MEQU.
srr_run_to_sh tfibtbl_rtF_ok HS 0x52b00. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
pose proof (MEQI_frame En2 rs _ _ HEn2 ltac:(vm_compute; reflexivity) HF MEQ2) as MEQR end.
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAME) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msR y = mem2 y).
{ intros y Y1 Y2 Y3. apply HF. intros Hw. destruct (in_wrange_windows En2 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn2 2%nat ltac:(cbv; zlia)), ?E2, ?(HEn2 32%nat ltac:(cbv; zlia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; zlia);
clear - Y1 Y2 Y3 Hr; unfold IFRAME, ASTACK, t_unwinding in *; unfold sp0, T in *; zlia |]).
destruct Hin. }
clear HF.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W En2); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite (HEn2 1%nat ltac:(cbv; zlia)), E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { intros r Hr. unfold callee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear Hr. repeat match type of R with _ \/ _ => destruct R as [R|R] end; subst r;
[ cs_case HS HEn2 Htp (2%bv : bv 5) | cs_case HS HEn2 Htp (3%bv : bv 5) | cs_case HS HEn2 Htp (4%bv : bv 5) | cs_case HS HEn2 Htp (8%bv : bv 5) | cs_case HS HEn2 Htp (9%bv : bv 5)
| cs_case HS HEn2 Htp (18%bv : bv 5) | cs_case HS HEn2 Htp (19%bv : bv 5) | cs_case HS HEn2 Htp (20%bv : bv 5) | cs_case HS HEn2 Htp (21%bv : bv 5) | cs_case HS HEn2 Htp (22%bv : bv 5)
| cs_case HS HEn2 Htp (23%bv : bv 5) | cs_case HS HEn2 Htp (24%bv : bv 5) | cs_case HS HEn2 Htp (25%bv : bv 5) | cs_case HS HEn2 Htp (26%bv : bv 5) | cs_case HS HEn2 Htp (27%bv : bv 5) ]. }
split; [exact MEQR|].
split. { memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)); [|destruct (Z_lt_le_dec a (sp0 - 64))].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Ha l; numconst; unfold sp0; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
- apply (apresent_same (w_H W) mem2); [|apply PRES3; exact Ha].
apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - Ha l; numconst; zlia | clear - Ha l0; zlia | pose proof stack_ivs as (IT & _); clear - Ha IT; numconst; unfold sp0, T in *; zlia].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Ha l0; numconst; unfold sp0; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
Qed.
End WK.
End c.

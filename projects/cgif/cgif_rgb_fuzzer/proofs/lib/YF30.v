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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF2l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD in *.
Definition qT : nat := 32.
Definition qSB : nat := 33.
Definition qU : nat := 34.
Definition qN : nat := 35.
Definition qQSZ : nat := 36.
Definition qQF : nat := 37.
Definition qQL : nat := 38.
Definition qQB : nat := 39.
Definition qCNT : nat := 40.
Definition qCP : nat := 41.
Definition qJST : nat := 42.
Definition qNB : nat := 43.
Definition qCSL : nat := 44.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (u nn : Z) (q : qcache) (cnt coff jst : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x35dd8 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 u nn q cnt coff jst.
Local Notation QSZv := (YF2l.QSZv q).
Local Notation QFv := (YF2l.QFv ly q).
Local Notation QLv := (YF2l.QLv ly q).
Local Notation QBv := (YF2l.QBv q).
Local Notation CPv := (YF2l.CPv coff).
Local Notation NBv := (YF2l.NBv ly coff).
Local Notation CSLv := (YF2l.CSLv ly cnt).
Local Notation XW := (YF2l.XW ly u nn q cnt coff jst).
Local Notation E0 := (YF2l.E0 ly regs0 u nn q cnt coff jst).
Local Notation Er := (YF2l.Er ly regs0 u nn q cnt coff jst).
Local Notation E2 := (YF2l.E2 ly regs0 u nn q cnt coff jst).
Local Notation E1 := (YF2l.E1 ly regs0 u nn q cnt coff jst).
Local Notation E8 := (YF2l.E8 ly regs0 u nn q cnt coff jst).
Local Notation EqT := (YF2l.EqT ly regs0 u nn q cnt coff jst).
Local Notation EqSB := (YF2l.EqSB ly regs0 u nn q cnt coff jst).
Local Notation EqU := (YF2l.EqU ly regs0 u nn q cnt coff jst).
Local Notation EqN := (YF2l.EqN ly regs0 u nn q cnt coff jst).
Local Notation EqQSZ := (YF2l.EqQSZ ly regs0 u nn q cnt coff jst).
Local Notation EqQF := (YF2l.EqQF ly regs0 u nn q cnt coff jst).
Local Notation EqQL := (YF2l.EqQL ly regs0 u nn q cnt coff jst).
Local Notation EqQB := (YF2l.EqQB ly regs0 u nn q cnt coff jst).
Local Notation EqCNT := (YF2l.EqCNT ly regs0 u nn q cnt coff jst).
Local Notation EqCP := (YF2l.EqCP ly regs0 u nn q cnt coff jst).
Local Notation EqJST := (YF2l.EqJST ly regs0 u nn q cnt coff jst).
Local Notation EqNB := (YF2l.EqNB ly regs0 u nn q cnt coff jst).
Local Notation EqCSL := (YF2l.EqCSL ly regs0 u nn q cnt coff jst).
Local Notation R_ROOT := YF2l.R_ROOT.
Local Notation R_CNT := YF2l.R_CNT.
Local Notation R_JST := YF2l.R_JST.
Local Notation REG0 := YF2l.REG0.
Local Notation R_LAST := YF2l.R_LAST.
Local Notation R_CSZ := YF2l.R_CSZ.
Local Notation R_SLOT := YF2l.R_SLOT.
Local Notation R_NB := YF2l.R_NB.
Local Notation FFQ := YF2l.FFQ.
Local Notation SR0 := YF2l.SR0.
Local Notation SS0 := YF2l.SS0.
Local Notation LYB := (YF2l.LYB W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation derived_ranges := (YF2l.derived_ranges W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation hit_ranges := (YF2l.hit_ranges W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WINT := (YF2l.WINT ly).
Local Notation WINA := (YF2l.WINA ly q cnt coff).
Local Notation WIN := (YF2l.WIN ly regs0 q cnt coff).
Local Notation win_sub := YF2l.win_sub.
Local Notation win_sub_sound := (YF2l.win_sub_sound ly regs0).
Local Notation WSK0 := YF2l.WSK0.
Local Notation WSKN := YF2l.WSKN.
Local Notation WSKL := YF2l.WSKL.
Local Notation WSKNL := YF2l.WSKNL.
Local Notation sk_ok := (YF2l.sk_ok ly regs0 q cnt coff).
Local Notation WSK0_ok := (YF2l.WSK0_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WSKN_ok := (YF2l.WSKN_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WSKL_ok := (YF2l.WSKL_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WSKNL_ok := (YF2l.WSKNL_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation windows_WIN := (YF2l.windows_WIN ly regs0 q cnt coff).
Local Notation WIN_zone := (YF2l.WIN_zone W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WIN_off := (YF2l.WIN_off W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation MEQ := (YF2l.MEQ ly regs0 mem0 q cnt coff).
Local Notation MEQ_frame := (YF2l.MEQ_frame ly regs0 mem0 q cnt coff).
Local Notation MEQ_0 := (YF2l.MEQ_0 ly regs0 mem0 q cnt coff).
Local Notation WIN0 := (YF2l.WIN0 ly regs0).
Local Notation WIN0_WIN := (YF2l.WIN0_WIN ly regs0 q cnt coff).
Local Notation sk_ok0 := (YF2l.sk_ok0 ly regs0).
Local Notation WSK0_ok0 := (YF2l.WSK0_ok0 W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation MEQ0 := (YF2l.MEQ0 ly regs0 mem0).
Local Notation MEQ0_frame := (YF2l.MEQ0_frame ly regs0 mem0).
Local Notation MEQ0_0 := (YF2l.MEQ0_0 ly regs0 mem0).
Local Notation WINS := (YF2l.WINS regs0).
Local Notation WINS_WIN0 := (YF2l.WINS_WIN0 ly regs0).
Local Notation WSKS := YF2l.WSKS.
Local Notation sk_okS := (YF2l.sk_okS regs0).
Local Notation WSKS_okS := (YF2l.WSKS_okS ly regs0 u nn q cnt coff jst).
Local Notation MEQS := (YF2l.MEQS regs0 mem0).
Local Notation MEQS_frame := (YF2l.MEQS_frame ly regs0 mem0).
Local Notation MEQS_0 := (YF2l.MEQS_0 regs0 mem0).
Local Notation MEQS_MEQ0 := (YF2l.MEQS_MEQ0 ly regs0 mem0).
Local Notation MEQ0_MEQ := (YF2l.MEQ0_MEQ ly regs0 mem0 q cnt coff).
Local Notation all_disjoint_of_forall := YF2l.all_disjoint_of_forall.
Local Notation kept_of_frame := (YF2l.kept_of_frame W ly regs0).
Local Notation aview_eq_mbyte := YF2l.aview_eq_mbyte.
Local Notation kept_of_aview := (YF2l.kept_of_aview W).
Local Notation SKEL_TAIL := YF2l.SKEL_TAIL.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hra4096 Hsp Hsp_al Hpres Hu IMG Hnn Hq Hnb Hlast Hcnt Hhit Hjst SEED].
Local Notation off_T := (YF2l.off_T W ly regs0 mem0 u nn q cnt coff jst FH).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac meq0_acc SKOK :=
match goal with
| M : MEQ0 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ0_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Definition R_LAST0 : YQ0b.region := YQ0b.mkRegion (Some 38%nat) 0 24 0 0 [YQ0b.mkChunk 16 (CVal 8 (SLit kBatchSlots))].
Definition at_CALLR (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs1 mem1 mat,
c' = mkCfg (mkst regs1 (w64 (0x3670c + D_150)) mem1 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs1 1 = w64 (0x35f2c + D_150) /\ getr regs1 2 = w64 (sp0 - 64) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 10 = w64 (T + t_cache) /\ getr regs1 11 = w64 (T + t_cache + 1920) /\ getr regs1 12 = w64 (0xa6b58 + D_10c0) /\ getr regs1 13 = w64 24 /\
getr regs1 8 = w64 (T + t_cache + 1920) /\ getr regs1 9 = w64 (T + t_cache) /\ getr regs1 18 = w64 (u - 16) /\ getr regs1 19 = w64 (T + t_qc) /\
getr regs1 20 = getr regs0 12 /\ getr regs1 21 = w64 nn /\
(forall r : bv 5, In r [22; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs0 r) /\
MEQ0 mem1 /\
(forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W) mem1 a) /\
let m := mrestrict (w_H W) mem1 in
val_mem tfxsegs m (T + t_qc) 8 QSZv /\ val_mem tfxsegs m (T + t_qc + 8) 8 QFv /\ val_mem tfxsegs m (T + t_qc + 16) 8 QLv /\ val_mem tfxsegs m (T + t_qc + 24) 8 QBv /\
val_mem tfxsegs m (T + t_cache + 1920) 4 cnt /\ val_mem tfxsegs m (T + t_cache_stats + 16) 8 jst /\
val_mem tfxsegs m (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\ val_mem tfxsegs m (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem tfxsegs m (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\ val_mem tfxsegs m (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem tfxsegs m (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\ val_mem tfxsegs m (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfxsegs m (sp0 - 56) 8 (bv_unsigned (getr regs0 21)).
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; img_refl.
Ltac reg_atom HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ img_refl | f_equal; numconst; zlia ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac frame_val HS i j k r BV2 := memv HS i j; [img_try (rewrite BV2; zlia) | img_try (cbn [sv_denot]; rewrite (Er k r eq_refl); f_equal; zlia) | img_try (img_apply u64_range)].
Lemma segR1 : cnt = 0 -> SRr tfxsegs W cfg0 at_CALLR.
Proof.
intros Hc. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok0 E0 HE0) as SK0.
assert (R36 : rho_of E0 36%nat = QSZv) by (img_try (unfold rho_of; rewrite EqQSZ; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R40 : rho_of E0 40%nat = cnt) by (img_try (unfold rho_of; rewrite EqCNT; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R32 : rho_of E0 32%nat = T) by (img_try (unfold rho_of; rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - LB; numconst; zlia)).
assert (BV32 : bv_unsigned (ew E0 32) = T) by img_exact R32.
assert (BV38 : bv_unsigned (ew E0 38) = QLv) by (img_try (rewrite EqQL; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (VMQ : forall m a (n : nat) v, MEQ0 m -> (forall i, 0 <= i < Z.of_nat n -> ~ WIN0 (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfxsegs m0 a n v -> val_mem tfxsegs (mrestrict (w_H W) m) a n v).
{ intros m a n v HM Hn Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(img_try (zlia))) as [N1 N2].
img_apply HM. rewrite unsigned_lit_small by img_exact N2. img_exact N1. }
assert (PRQ : forall m a, MEQ0 m -> ~ WIN0 a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem0 a -> apresent (w_H W) m a).
{ intros m a HM Hn Ha Hp. img_apply (apresent_same (w_H W) mem0); [|img_try (img_exact Hp)]. img_apply HM. rewrite unsigned_lit_small by img_exact Ha. img_exact Hn. }
assert (NW0 : forall a, ~ (sp0 - 64 <= a < sp0) -> ~ (T + t_qc <= a < T + t_qc + 32) -> ~ (T + t_cache + 1920 <= a < T + t_cache + 1924) ->
~ (T + t_cache_stats + 16 <= a < T + t_cache_stats + 24) -> ~ WIN0 a).
{ intros a N0 N1 N2 N3 [X|X]; [img_try (img_exact (N0 X))|]. unfold YF2l.WINT in X. clear - X N1 N2 N3. zlia. }
srr_run_sh tfxtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfxtbl_rtF_ok HS.
{
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfxtbl_rtF_ok HS.
2:{ exfalso. rewrite branch_eq_U in Hc1. apply Z.eqb_neq in Hc1. revert Hc1. rewrite !U_zev by img_refl. cbn [zev zalu_raw].
rewrite R40. rewrite ?zcanon_id by (img_try (clear - DR; unfold M64; zlia)). clear - Hc. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfxtbl_rtF_ok HS (0x3670c + D_150). meq0_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR. cbn [ss_pc] in HshR.
img_apply SRr_ret. split; [img_refl|].
eexists (ms_regs msR), (ms_mem msR), _.
split. { rewrite HshR at 1. img_refl. }
split. { reg_lit HS (1%bv : bv 5). }
split. { rreg HS (2%bv : bv 5) Q2. rewrite Q2. cbn [sv_denot]. rewrite E2. unfold w64. f_equal; unfold sp0; zlia. }
split. { reg_entry HS (3%bv : bv 5) 3%nat. }
split. { rreg HS (4%bv : bv 5) Q4. rewrite Q4, Htp. img_refl. }
split. { reg_atom HS (10%bv : bv 5) constr:(EqT). }
split. { reg_atom HS (11%bv : bv 5) constr:(EqT). }
split. { reg_lit HS (12%bv : bv 5). }
split. { reg_lit HS (13%bv : bv 5). }
split. { reg_atom HS (8%bv : bv 5) constr:(EqT). }
split. { reg_atom HS (9%bv : bv 5) constr:(EqT). }
split. { reg_atom HS (18%bv : bv 5) constr:(EqU). }
split. { reg_atom HS (19%bv : bv 5) constr:(EqT). }
split. { reg_entry HS (20%bv : bv 5) 12%nat. }
split. { reg_atom HS (21%bv : bv 5) constr:(EqN). }
split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
[img_try (reg_entry HS (22%bv : bv 5) 22%nat) | img_try (reg_entry HS (23%bv : bv 5) 23%nat) | img_try (reg_entry HS (24%bv : bv 5) 24%nat)
| img_try (reg_entry HS (25%bv : bv 5) 25%nat) | img_try (reg_entry HS (26%bv : bv 5) 26%nat) | img_try (reg_entry HS (27%bv : bv 5) 27%nat)]. }
split. { img_exact MQ. }
split. { intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia) | img_try (off_by ltac:(revert Ha; numconst; intros Ha; zlia)) ]. }
cbv zeta.
split. { memv HS 1%nat 0%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 1%nat 1%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 1%nat 2%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQL; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 1%nat 3%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 2%nat 0%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 3%nat 0%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqJST; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { frame_val HS 0%nat 6%nat 1%nat (1%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 5%nat 8%nat (8%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 4%nat 9%nat (9%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 3%nat 18%nat (18%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 2%nat 19%nat (19%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 1%nat 20%nat (20%bv : bv 5) BV2. }
frame_val HS 0%nat 0%nat 21%nat (21%bv : bv 5) BV2. }
{
assert (HQF : qc_list q <> []).
{ rewrite branch_eq_U in Hc0. apply Z.eqb_neq in Hc0. revert Hc0. rewrite !U_zev by img_refl. cbn [zev zalu_raw].
rewrite R36. rewrite ?zcanon_id by (img_try (clear - DR; unfold M64; zlia)). unfold YF2l.QSZv. destruct (qc_list q); cbn [length]; [img_try (zlia) | img_try (intros _; discriminate)]. }
destruct (rev (qc_list q)) as [|lastb initr] eqn:HR0; [img_try (exfalso; img_apply HQF; rewrite <- (rev_involutive (qc_list q)), HR0; img_refl)|].
destruct (Hlast lastb initr eq_refl) as (L1 & L2 & L3 & L4 & L5).
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
apply (st_ok_add_region _ _ _ R_LAST0) in HS;
[ | img_refl
| img_try (unfold R_LAST0, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV38;
split; [clear - L1 LB; numconst; zlia|]; split; [clear - L1 L2 LB; numconst; zlia|];
split; [intros o Ho; zlia|];
img_apply Forall_cons; [|img_apply Forall_nil];
eapply chunk_ok_val; [img_refl | unfold kBatchSlots; cbn; zlia | cbn; zlia |];
img_apply (VMQ _ _ 8%nat); [img_exact MQ | intros i Hi; split; [img_apply NW0; clear - Hi L1 L2 LB Hlo Hhi; numconst; zlia | clear - Hi L1 L2 LB; numconst; zlia] | img_exact L4])
| img_try (unfold R_LAST0; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV38, ?BV2;
clear - LB DR L1 L2 Hlo Hhi; numconst; repeat split; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_sh tfxtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfxtbl_rtF_ok HS.
2:{ exfalso. rewrite branch_eq_U in Hc1. apply Z.eqb_neq in Hc1. revert Hc1. rewrite !U_zev by img_refl. cbn [zev zalu_raw].
rewrite R40. rewrite ?zcanon_id by (img_try (clear - DR; unfold M64; zlia)). clear - Hc. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfxtbl_rtF_ok HS (0x3670c + D_150). meq0_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR. cbn [ss_pc] in HshR.
img_apply SRr_ret. split; [img_refl|].
eexists (ms_regs msR), (ms_mem msR), _.
split. { rewrite HshR at 1. img_refl. }
split. { reg_lit HS (1%bv : bv 5). }
split. { rreg HS (2%bv : bv 5) Q2. rewrite Q2. cbn [sv_denot]. rewrite E2. unfold w64. f_equal; unfold sp0; zlia. }
split. { reg_entry HS (3%bv : bv 5) 3%nat. }
split. { rreg HS (4%bv : bv 5) Q4. rewrite Q4, Htp. img_refl. }
split. { reg_atom HS (10%bv : bv 5) constr:(EqT). }
split. { reg_atom HS (11%bv : bv 5) constr:(EqT). }
split. { reg_lit HS (12%bv : bv 5). }
split. { reg_lit HS (13%bv : bv 5). }
split. { reg_atom HS (8%bv : bv 5) constr:(EqT). }
split. { reg_atom HS (9%bv : bv 5) constr:(EqT). }
split. { reg_atom HS (18%bv : bv 5) constr:(EqU). }
split. { reg_atom HS (19%bv : bv 5) constr:(EqT). }
split. { reg_entry HS (20%bv : bv 5) 12%nat. }
split. { reg_atom HS (21%bv : bv 5) constr:(EqN). }
split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
[img_try (reg_entry HS (22%bv : bv 5) 22%nat) | img_try (reg_entry HS (23%bv : bv 5) 23%nat) | img_try (reg_entry HS (24%bv : bv 5) 24%nat)
| img_try (reg_entry HS (25%bv : bv 5) 25%nat) | img_try (reg_entry HS (26%bv : bv 5) 26%nat) | img_try (reg_entry HS (27%bv : bv 5) 27%nat)]. }
split. { img_exact MQ. }
split. { intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia) | img_try (off_by ltac:(revert Ha; numconst; intros Ha; zlia)) ]. }
cbv zeta.
split. { memv HS 2%nat 0%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 2%nat 1%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 2%nat 2%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQL; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 2%nat 3%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqQB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 3%nat 0%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { memv HS 4%nat 0%nat; [img_try (rewrite BV32; numconst; zlia) | img_try (cbn [sv_denot]; rewrite EqJST; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - DR; numconst; zlia)]. }
split. { frame_val HS 1%nat 6%nat 1%nat (1%bv : bv 5) BV2. }
split. { frame_val HS 1%nat 5%nat 8%nat (8%bv : bv 5) BV2. }
split. { frame_val HS 1%nat 4%nat 9%nat (9%bv : bv 5) BV2. }
split. { frame_val HS 1%nat 3%nat 18%nat (18%bv : bv 5) BV2. }
split. { frame_val HS 1%nat 2%nat 19%nat (19%bv : bv 5) BV2. }
split. { frame_val HS 1%nat 1%nat 20%nat (20%bv : bv 5) BV2. }
frame_val HS 1%nat 0%nat 21%nat (21%bv : bv 5) BV2. }
Qed.
End WK.
End b.

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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF2e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Definition dT : nat := 32.
Definition dSB : nat := 33.
Definition dGSZ : nat := 34.
Definition dGF : nat := 35.
Definition dGL : nat := 36.
Definition dGB : nat := 37.
Definition dTSZ : nat := 38.
Definition dTF : nat := 39.
Definition dTL : nat := 40.
Definition dTB : nat := 41.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (gq tq : qcache).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33530 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 gq tq.
Local Notation GSZv := (YF2e.GSZv gq).
Local Notation GFv := (YF2e.GFv ly gq).
Local Notation GLv := (YF2e.GLv ly gq).
Local Notation GBv := (YF2e.GBv gq).
Local Notation TSZv := (YF2e.TSZv tq).
Local Notation TFv := (YF2e.TFv ly tq).
Local Notation TLv := (YF2e.TLv ly tq).
Local Notation TBv := (YF2e.TBv tq).
Local Notation XW := (YF2e.XW ly gq tq).
Local Notation E0 := (YF2e.E0 ly regs0 gq tq).
Local Notation Er := (YF2e.Er ly regs0 gq tq).
Local Notation E2 := (YF2e.E2 ly regs0 gq tq).
Local Notation E1 := (YF2e.E1 ly regs0 gq tq).
Local Notation E8 := (YF2e.E8 ly regs0 gq tq).
Local Notation EqT := (YF2e.EqT ly regs0 gq tq).
Local Notation EqSB := (YF2e.EqSB ly regs0 gq tq).
Local Notation EqGSZ := (YF2e.EqGSZ ly regs0 gq tq).
Local Notation EqGF := (YF2e.EqGF ly regs0 gq tq).
Local Notation EqGL := (YF2e.EqGL ly regs0 gq tq).
Local Notation EqGB := (YF2e.EqGB ly regs0 gq tq).
Local Notation EqTSZ := (YF2e.EqTSZ ly regs0 gq tq).
Local Notation EqTF := (YF2e.EqTF ly regs0 gq tq).
Local Notation EqTL := (YF2e.EqTL ly regs0 gq tq).
Local Notation EqTB := (YF2e.EqTB ly regs0 gq tq).
Local Notation R_QW := YF2e.R_QW.
Local Notation R_QG := YF2e.R_QG.
Local Notation R_QT := YF2e.R_QT.
Local Notation REG0 := YF2e.REG0.
Local Notation R_GLN := YF2e.R_GLN.
Local Notation FFD := YF2e.FFD.
Local Notation SR0 := YF2e.SR0.
Local Notation SS0 := YF2e.SS0.
Local Notation LYB := (YF2e.LYB W ly regs0 mem0 gq tq FH).
Local Notation derived_ranges := (YF2e.derived_ranges W ly regs0 mem0 gq tq FH).
Local Notation WINF := (YF2e.WINF ly).
Local Notation WINA := (YF2e.WINA ly gq).
Local Notation WIN := (YF2e.WIN ly regs0 gq).
Local Notation win_sub := YF2e.win_sub.
Local Notation win_sub_sound := (YF2e.win_sub_sound ly regs0).
Local Notation WSK0 := YF2e.WSK0.
Local Notation WSKL := YF2e.WSKL.
Local Notation sk_ok := (YF2e.sk_ok ly regs0 gq).
Local Notation WSK0_ok := (YF2e.WSK0_ok W ly regs0 mem0 gq tq FH).
Local Notation WSKL_ok := (YF2e.WSKL_ok W ly regs0 mem0 gq tq FH).
Local Notation windows_WIN := (YF2e.windows_WIN ly regs0 gq).
Local Notation WIN_cases := (YF2e.WIN_cases W ly regs0 mem0 gq tq FH).
Local Notation MEQ := (YF2e.MEQ ly regs0 mem0 gq).
Local Notation MEQ_frame := (YF2e.MEQ_frame ly regs0 mem0 gq).
Local Notation MEQ_0 := (YF2e.MEQ_0 ly regs0 mem0 gq).
Local Notation WIN0 := (YF2e.WIN0 ly regs0).
Local Notation WIN0_WIN := (YF2e.WIN0_WIN ly regs0 gq).
Local Notation sk_ok0 := (YF2e.sk_ok0 ly regs0).
Local Notation WSK0_ok0 := (YF2e.WSK0_ok0 W ly regs0 mem0 gq tq FH).
Local Notation MEQ0 := (YF2e.MEQ0 ly regs0 mem0).
Local Notation MEQ0_frame := (YF2e.MEQ0_frame ly regs0 mem0).
Local Notation MEQ0_0 := (YF2e.MEQ0_0 ly regs0 mem0).
Local Notation MEQ0_MEQ := (YF2e.MEQ0_MEQ ly regs0 mem0 gq).
Local Notation all_disjoint_of_forall := YF2e.all_disjoint_of_forall.
Local Notation kept_of_frame := (YF2e.kept_of_frame W ly regs0).
Local Notation aview_eq_mbyte := YF2e.aview_eq_mbyte.
Local Notation R_QW1 := YF2e.R_QW1.
Local Notation R_QW0 := YF2e.R_QW0.
Local Notation LSZv := (YF2e.LSZv gq tq).
Local Notation LBv := (YF2e.LBv gq tq).
Local Notation LFv := (YF2e.LFv ly gq tq).
Local Notation SREGS := YF2e.SREGS.
Local Notation at_RETD := (YF2e.at_RETD W ly regs0 mem0 md0 gq tq).
Local Notation at_L0 := (YF2e.at_L0 W ly regs0 mem0 md0 gq tq).
Local Notation postD := (YF2e.postD W ly regs0 mem0 md0 gq tq).
Local Notation SKEL_TAIL := YF2e.SKEL_TAIL.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hg Ht Hglast SEED].
Local Notation off_T := (YF2e.off_T W ly).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
Ltac meq0_acc SKOK :=
match goal with
| M : MEQ0 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ0_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac qw_split1 HS iW :=
let VW := fresh "VW" in
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) =>
assert (VW : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 4 1) by (img_try (memv HS iW 0%nat; [img_refl | img_refl | img_try (zlia)]));
apply (proj1 (val_mem4_bytes _ _ _)) in VW; destruct VW as (VW0 & VW1 & VW2 & VW3);
img_change (YP0g.le_byte 1 4 0) with 1 in VW0; img_change (YP0g.le_byte 1 4 1) with 0 in VW1;
img_change (YP0g.le_byte 1 4 2) with 0 in VW2; img_change (YP0g.le_byte 1 4 3) with 0 in VW3;
eapply (st_ok_set_region E _ _ iW _ R_QW1) in HS;
[ | img_refl | img_try (repeat split; img_refl) | img_refl
| img_try (img_apply Forall_cons; [ eapply chunk_ok_val; [img_refl | cbn; zlia | cbn; zlia | img_apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; img_exact VW0 ]
| img_apply Forall_cons; [ img_apply chunk_ok_zero_mb; img_exact (bytes3_of _ _ _ VW1 VW2 VW3) | img_apply Forall_nil ] ]) ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW0 VW1 VW2 VW3
end.
Ltac qw_join0 HS iW :=
let VW := fresh "VW" in let VZ := fresh "VZ" in
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ ?msx) =>
assert (VW : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 1 0) by (img_try (memv HS iW 0%nat; [img_refl | img_refl | img_try (zlia)]));
apply (proj1 (val_mem1_byte _ _ _)) in VW; img_change (YP0g.le_byte 0 1 0) with 0 in VW;
assert (VZ : forall a, A_QUAR + 153 <= a < A_QUAR + 153 + 3 -> mbyte tfxsegs (mrestrict (w_H W) (ms_mem msx)) a = Some (Z_to_bv 8 0))
by (img_try (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msx iW _ 1 _ _ a HS); [img_refl | img_refl | img_try (cbn [base_val YQ0b.r_base]; unfold A_QUAR, A_ALLOCATOR, o_quar in Ha; clear - Ha; zlia)]));
eapply (st_ok_set_region E _ _ iW _ R_QW0) in HS;
[ | img_refl | img_try (repeat split; img_refl) | img_refl
| img_try (img_apply Forall_cons; [ img_apply chunk_ok_zero_mb; refine (bytes4_of _ _ _ VW (VZ _ _) (VZ _ _) (VZ _ _)); zlia | img_apply Forall_nil ]) ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW VZ
end.
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; img_refl.
Ltac reg_atom HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ img_refl | f_equal; numconst; zlia ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_apply Er; img_refl | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac frame_val HS i j k r BV2 := memv HS i j; [img_try (rewrite BV2; zlia) | img_try (cbn [sv_denot]; rewrite (Er k r eq_refl); f_equal; zlia) | img_try (img_apply u64_range)].
Ltac memv_any HS i tA tV tR :=
first [ memv HS i 0%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 1%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 2%nat; [img_try (tA) | img_try (tV) | img_try (tR)]
| memv HS i 3%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 4%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 5%nat; [img_try (tA) | img_try (tV) | img_try (tR)]
| memv HS i 6%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 7%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 8%nat; [img_try (tA) | img_try (tV) | img_try (tR)] | memv HS i 9%nat; [img_try (tA) | img_try (tV) | img_try (tR)] ].
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
lazymatch goal with DR : _ |- _ => idtac end;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let m1 := img_ev (nth_error (ss_mem ss) 1) in idtac "REGION1" m1;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YQ0b.mkChunk ?o _) :: ?t => let e := img_ev (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := img_ev (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := img_ev (YQ0b.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac tA := cbn [base_val YQ0b.r_base]; rewrite ?Z.add_0_l;
first [ img_refl | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 32) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 36) = _ |- _ => rewrite B end; numconst; zlia ].
Ltac tV HG := first
[ img_refl
| cbn [sv_denot]; rewrite ?YF2e.EqT, ?YF2e.EqSB, ?YF2e.EqGSZ, ?YF2e.EqGF, ?YF2e.EqGL, ?YF2e.EqGB,
?YF2e.EqTSZ, ?YF2e.EqTF, ?YF2e.EqTL, ?YF2e.EqTB; unfold w64; rewrite ?Zbv_add_unsigned;
first [ img_refl | f_equal; unfold YF2e.LFv, YF2e.LSZv, YF2e.LBv; rewrite ?HG; cbv beta iota; cbn [length Z.of_nat]; zlia
| first [ rewrite (YF2e.Er _ _ _ _ 1 1%bv eq_refl) | rewrite (YF2e.Er _ _ _ _ 8 8%bv eq_refl) | rewrite (YF2e.Er _ _ _ _ 9 9%bv eq_refl)
| rewrite (YF2e.Er _ _ _ _ 18 18%bv eq_refl) | rewrite (YF2e.Er _ _ _ _ 19 19%bv eq_refl) | rewrite (YF2e.Er _ _ _ _ 20 20%bv eq_refl)
| rewrite (YF2e.Er _ _ _ _ 12 12%bv eq_refl) | rewrite (YF2e.Er _ _ _ _ 13 13%bv eq_refl) ];
rewrite ?Z.add_0_r; first [ img_refl | img_apply Z_to_bv_bv_unsigned | f_equal; zlia ] ]
| img_apply denot_by_zev; [ img_refl | unfold YF2e.LFv, YF2e.LSZv, YF2e.LBv; rewrite ?HG; cbv beta iota; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
unfold YF2e.LFv, YF2e.LSZv, YF2e.LBv; rewrite ?HG; cbv beta iota; land_lits; numconst; zcanon_simp; zlia ] ].
Ltac tR HG := first [ zlia | img_apply u64_range | unfold YF2e.LFv, YF2e.LSZv, YF2e.LBv; rewrite ?HG; cbv beta iota; cbn [length Z.of_nat]; numconst; zlia ].
Ltac reg_zev HS r HG :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) E0 _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := img_ev (sr_get sr rr) in img_change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
img_apply denot_by_zev; [ img_refl | unfold YF2e.LFv, YF2e.LSZv, YF2e.LBv; rewrite ?HG; cbv beta iota; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
unfold YF2e.LFv, YF2e.LSZv, YF2e.LBv; rewrite ?HG; cbv beta iota; land_lits; numconst; zcanon_simp; zlia ].
Ltac reg_val HS r HG := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV HG | reg_zev HS r HG ].
Ltac to_L0 HS HGT HG DR R37 R41 iS iW iG iT tPRES tGLN :=
srr_branch_sh tfxtbl_rtG_ok HS;
[ exfalso;
match goal with Hb : branch_taken _ _ _ = true |- _ =>
clear - Hb DR R37 R41 HGT; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; unfold YF2e.LBv in HGT; zlia end
| unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_to_sh tfxtbl_rtG_ok HS (0x337d0 + D_150);
match goal with SKW : YF2e.sk_ok _ _ _ _ _ |- _ => meq_acc SKW end;
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [img_try (idtac "L0-1"; rewrite HshR at 1; img_refl)|];
split; [img_try (idtac "L0-2"; let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite YF2e.E2; unfold w64; f_equal; unfold sp0; zlia)|];
split; [img_try (idtac "L0-3"; reg_lit HS (10%bv : bv 5))|];
split; [img_try (idtac "L0-4"; let Q := fresh "Q" in rreg HS (11%bv : bv 5) Q; rewrite Q; img_refl)|];
split; [img_try (idtac "L0-5"; let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q; tV HG)|];
split; [img_try (idtac "L0-6"; reg_entry HS (13%bv : bv 5) 13%nat)|];
split; [img_try (idtac "L0-7"; reg_lit HS (14%bv : bv 5))|];
split; [img_try (idtac "L0-8"; reg_lit HS (15%bv : bv 5))|];
split; [img_try (idtac "L0-9"; reg_val HS (16%bv : bv 5) HG)|];
split; [img_try (idtac "L0-10"; reg_val HS (5%bv : bv 5) HG)|];
split; [img_try (idtac "L0-11"; reg_entry HS (1%bv : bv 5) 1%nat)|];
split; [img_try (idtac "L0-12"; intros r Hr; cbn [YF2e.SREGS In] in Hr;
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; assumption
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat
| reg_entry HS (19%bv : bv 5) 19%nat | reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat
| reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ])|];
split; [img_try (idtac "L0-13"; assumption)|];
split; [img_try (idtac "L0-14"; tPRES)|];
cbv zeta;
split; [img_try (idtac "L0-15"; memvo HS iW (A_QUAR + 152); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-16"; memvo HS iG (A_QUAR + 160); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-17"; memvo HS iG (A_QUAR + 168); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-18"; memvo HS iG (A_QUAR + 176); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-19"; memvo HS iG (A_QUAR + 184); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-20"; memvo HS iT t_qc; [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-21"; memvo HS iT (t_qc + 8); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-22"; memvo HS iT (t_qc + 16); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-23"; memvo HS iT (t_qc + 24); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-24"; tGLN)|];
split; [img_try (idtac "L0-25"; memvo HS iS (-80); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-26"; memvo HS iS (-72); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-27"; memvo HS iS (-64); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-28"; memvo HS iS (-56); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-29"; memvo HS iS (-48); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-30"; memvo HS iS (-40); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-31"; memvo HS iS (-32); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-32"; memvo HS iS (-24); [tA | tV HG | tR HG])|];
split; [img_try (idtac "L0-33"; memvo HS iS (-16); [tA | tV HG | tR HG])|];
memvo HS iS (-8); [img_try (tA) | img_try (tV HG) | img_try (tR HG)]
end ].
Ltac presE HS iS iT BV2 BV32 LB Usp HG :=
intros a Ha Hh; unfold YF2e.WIN, YF2e.WINF, YF2e.WINA in Ha; rewrite HG in Ha;
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[Hne _]]];
[ img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iS _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Hh Usp; numconst; zlia) ])
| img_try (exfalso; clear - Ha Hh; numconst; zlia) | img_try (exfalso; clear - Ha Hh; numconst; zlia)
| img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iT _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ])
| img_try (exfalso; img_exact (Hne eq_refl)) ].
Ltac presN HS iS iT BV2 BV32 BV36 LB Usp L1 L2 :=
intros a Ha Hh; unfold YF2e.WIN, YF2e.WINF, YF2e.WINA in Ha;
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[_ Ha]]];
[ img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iS _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Hh Usp; numconst; zlia) ])
| img_try (exfalso; clear - Ha Hh; numconst; zlia) | img_try (exfalso; clear - Ha Hh; numconst; zlia)
| img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iT _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ])
| img_try (eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV36; clear - Ha; zlia | off_by ltac:(clear - Ha L1 L2 LB; numconst; zlia) ]) ].
Lemma segDN : qc_list gq <> [] ->
(kQuarantineMax < LBv -> 2 * (kBatchBytes * LSZv) <= LBv) ->
SRr tfxsegs W cfg0 postD.
Proof.
intros HGN HM. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok0 E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = T) by (img_try (unfold rho_of; rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - LB; numconst; zlia)).
assert (R33 : rho_of E0 33%nat = SB) by (img_try (unfold rho_of; rewrite EqSB; unfold w64; img_apply unsigned_lit_small; clear - LB; numconst; zlia)).
assert (R34 : rho_of E0 34%nat = GSZv) by (img_try (unfold rho_of; rewrite EqGSZ; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R37 : rho_of E0 37%nat = GBv) by (img_try (unfold rho_of; rewrite EqGB; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R38 : rho_of E0 38%nat = TSZv) by (img_try (unfold rho_of; rewrite EqTSZ; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (R41 : rho_of E0 41%nat = TBv) by (img_try (unfold rho_of; rewrite EqTB; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (BV32 : bv_unsigned (ew E0 32) = T) by img_exact R32.
assert (BV36 : bv_unsigned (ew E0 36) = GLv) by (img_try (rewrite EqGL; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (VMQ : forall m a (n : nat) v, MEQ0 m -> (forall i, 0 <= i < Z.of_nat n -> ~ WIN0 (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfxsegs m0 a n v -> val_mem tfxsegs (mrestrict (w_H W) m) a n v).
{ intros m a n v HMq Hn Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(img_try (zlia))) as [N1 N2].
img_apply HMq. rewrite unsigned_lit_small by img_exact N2. img_exact N1. }
assert (PRQ : forall m a, MEQ0 m -> ~ WIN0 a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem0 a -> apresent (w_H W) m a).
{ intros m a HMq Hn Ha Hp. img_apply (apresent_same (w_H W) mem0); [|img_try (img_exact Hp)]. img_apply HMq. rewrite unsigned_lit_small by img_exact Ha. img_exact Hn. }
assert (NW0 : forall a, ~ (sp0 - 80 <= a < sp0) -> ~ (A_QUAR + 152 <= a < A_QUAR + 156) -> ~ (A_QUAR + 160 <= a < A_QUAR + 192) ->
~ (T + t_qc <= a < T + t_qc + 32) -> ~ WIN0 a).
{ intros a N0 N1 N2 N3 [X|X]; [img_try (img_exact (N0 X))|]. unfold YF2e.WINF in X. clear - X N1 N2 N3. zlia. }
srr_run_sh tfxtbl_rtG_ok HS. meq0_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. clear - Hc DR R34 HGN. zbranch Hc. apply Z.eqb_eq in Hc. img_apply HGN.
unfold YF2e.GSZv in Hc. destruct (qc_list gq); cbn [length] in Hc; [img_refl | img_try (zlia)]. }
assert (HGQ' : exists gb gl, qc_list gq = gb :: gl) by (img_try (destruct (qc_list gq) as [|gb gl]; [img_try (exfalso; img_exact (HGN eq_refl)) | img_try (exists gb, gl; img_refl)])).
destruct HGQ' as (gb & gl & HGQ).
assert (HGR' : exists lastb initr, rev (qc_list gq) = lastb :: initr).
{ destruct (rev (qc_list gq)) as [|lb ini] eqn:R; [img_try (exfalso; img_apply HGN; rewrite <- (rev_involutive (qc_list gq)), R; img_refl) | img_try (exists lb, ini; img_refl)]. }
destruct HGR' as (lastb & initr & HGR). destruct (Hglast lastb initr HGR) as (L1 & L2 & L3 & L4 & L5).
apply (st_ok_add_region _ _ _ R_GLN) in HS;
[ | img_refl
| img_try (unfold YF2e.R_GLN, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV36;
split; [clear - L1 LB; numconst; zlia|]; split; [clear - L1 L2 LB; numconst; zlia|];
split; [intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - L1 L2 LB Ho; numconst; zlia) | img_apply PRQ; [img_exact MQ | img_apply NW0; clear - Ho L1 L2 LB Hlo Hhi; numconst; zlia | clear - Ho L1 L2 LB; numconst; zlia | img_apply L5; zlia]] |];
img_apply Forall_cons; [|img_apply Forall_nil];
eapply chunk_ok_val; [img_refl | cbn; zlia | cbn; zlia |];
img_apply (VMQ _ _ 8%nat); [img_exact MQ | intros i Hi; split; [img_apply NW0; clear - Hi L1 L2 LB Hlo Hhi; numconst; zlia | clear - Hi L1 L2 LB; numconst; zlia] | rewrite Z.add_0_r; img_exact L4])
| img_try (unfold YF2e.R_GLN; cbn [YQ0b.all_disjoint ss_mem]; repeat split; unfold YQ0b.extent_disjoint;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV2; clear - LB DR L1 L2 Hlo Hhi; numconst; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
pose proof (MEQ0_MEQ _ MQ) as MQ1. clear MQ. rename MQ1 into MQ. pose proof (WSKL_ok E0 HE0 HGN) as SKW.
srr_run_to_sh tfxtbl_rtG_ok HS (0x335f0 + D_150). meq_acc SKW.
qw_split1 HS 2%nat.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfxtbl_rtG_ok HS.
{
assert (HLE : LBv <= kQuarantineMax).
{ clear - Hc0 DR R37 R41. zbranch Hc0.
apply Bool.negb_true_iff in Hc0. apply Z.ltb_ge in Hc0. unfold YF2e.LBv. zlia. }
unfold YF2e.postD. destruct (Z.leb_spec LBv kQuarantineMax) as [_|X]; [|img_try (exfalso; clear - X HLE; zlia)].
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
qw_join0 HS 2%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfxsegs tfxtbl_rtG tfxtbl_rtG_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|]. exists (ms_regs msR), (ms_mem msR), mat'.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { rreg HS (2%bv : bv 5) Q2. rewrite Q2. img_exact E2. }
split. { intros r Hr. cbn [YF2e.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | rreg HS (4%bv : bv 5) Q4; rewrite Q4, Htp; img_refl
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat
| reg_entry HS (19%bv : bv 5) 19%nat | reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat
| reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]. }
split. { img_exact MQ. }
split. { presN HS 1%nat 4%nat BV2 BV32 BV36 LB Usp L1 L2. }
cbv zeta.
split. { intros a Ha. eapply (st_ok_chunk_zero (w_H W) E0 _ msR 2 _ 0 _ _ a HS); [img_refl | img_refl | img_try (cbn [base_val YQ0b.r_base YF2e.R_QW0]; clear - Ha; numconst; zlia)]. }
idtac "CELLS-A".
split. { memvo HS 3%nat (A_QUAR + 160); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 3%nat (A_QUAR + 168); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 3%nat (A_QUAR + 176); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 3%nat (A_QUAR + 184); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 4%nat t_qc; [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 4%nat (t_qc + 8); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 4%nat (t_qc + 16); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
split. { memvo HS 4%nat (t_qc + 24); [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
intros lastb' initr' RR. memvo HS 0%nat 0; [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)]. }
{
assert (HGT : kQuarantineMax < LBv).
{ clear - Hc0 DR R37 R41. zbranch Hc0. apply Bool.negb_false_iff in Hc0. apply Z.ltb_lt in Hc0. unfold YF2e.LBv. zlia. }
pose proof (HM HGT) as MC.
unfold YF2e.postD. destruct (Z.leb_spec LBv kQuarantineMax) as [X|_]; [img_try (exfalso; clear - X HGT; zlia)|].
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
qw_join0 HS 2%nat.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. clear - Hc1 DR R34 R37 R41 R38 MC. zbranch Hc1. apply Z.ltb_lt in Hc1.
unfold YF2e.LSZv, YF2e.LBv in MC. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfxtbl_rtG_ok HS.
{ unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW. to_L0 HS HGT HGQ DR R37 R41 1%nat 2%nat 3%nat 4%nat ltac:(img_try (presN HS 1%nat 4%nat BV2 BV32 BV36 LB Usp L1 L2)) ltac:(img_try (intros lastb' initr' RR; memvo HS 0%nat 0; [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)])). }
{ unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfxtbl_rtG_ok HS.
2:{ exfalso. clear - Hc3 DR R34 R37 R41 R38 MC. zbranch Hc3. apply Bool.negb_false_iff in Hc3. apply Z.ltb_lt in Hc3.
unfold YF2e.LSZv, YF2e.LBv in MC. zlia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SKW. to_L0 HS HGT HGQ DR R37 R41 1%nat 2%nat 3%nat 4%nat ltac:(img_try (presN HS 1%nat 4%nat BV2 BV32 BV36 LB Usp L1 L2)) ltac:(img_try (intros lastb' initr' RR; memvo HS 0%nat 0; [img_try (tA) | img_try (tV HGQ) | img_try (tR HGQ)])). } }
Qed.
End WK.
End b.

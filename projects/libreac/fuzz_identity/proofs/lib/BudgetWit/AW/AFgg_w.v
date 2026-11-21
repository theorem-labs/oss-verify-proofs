(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFgg.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFgg.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0s_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AB1t AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFl1_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFeq_w AFew_w AFeu_w AFgj_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (gq tq : qcache).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33604) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 gq tq.
Local Notation GSZv := (AFgj_w.GSZv gq).
Local Notation GFv := (AFgj_w.GFv ly gq).
Local Notation GLv := (AFgj_w.GLv ly gq).
Local Notation GBv := (AFgj_w.GBv gq).
Local Notation TSZv := (AFgj_w.TSZv tq).
Local Notation TFv := (AFgj_w.TFv ly tq).
Local Notation TLv := (AFgj_w.TLv ly tq).
Local Notation TBv := (AFgj_w.TBv tq).
Local Notation XW := (AFgj_w.XW ly gq tq).
Local Notation E0 := (AFgj_w.E0 ly regs0 gq tq).
Local Notation Er := (AFgj_w.Er ly regs0 gq tq).
Local Notation E2 := (AFgj_w.E2 ly regs0 gq tq).
Local Notation E1 := (AFgj_w.E1 ly regs0 gq tq).
Local Notation E8 := (AFgj_w.E8 ly regs0 gq tq).
Local Notation EqT := (AFgj_w.EqT ly regs0 gq tq).
Local Notation EqSB := (AFgj_w.EqSB ly regs0 gq tq).
Local Notation EqGSZ := (AFgj_w.EqGSZ ly regs0 gq tq).
Local Notation EqGF := (AFgj_w.EqGF ly regs0 gq tq).
Local Notation EqGL := (AFgj_w.EqGL ly regs0 gq tq).
Local Notation EqGB := (AFgj_w.EqGB ly regs0 gq tq).
Local Notation EqTSZ := (AFgj_w.EqTSZ ly regs0 gq tq).
Local Notation EqTF := (AFgj_w.EqTF ly regs0 gq tq).
Local Notation EqTL := (AFgj_w.EqTL ly regs0 gq tq).
Local Notation EqTB := (AFgj_w.EqTB ly regs0 gq tq).
Local Notation R_QW := AFgj_w.R_QW.
Local Notation R_QG := AFgj_w.R_QG.
Local Notation R_QT := AFgj_w.R_QT.
Local Notation REG0 := AFgj_w.REG0.
Local Notation R_GLN := AFgj_w.R_GLN.
Local Notation FFD := AFgj_w.FFD.
Local Notation SR0 := AFgj_w.SR0.
Local Notation SS0 := AFgj_w.SS0.
Local Notation LYB := (AFgj_w.LYB W ly regs0 mem0 gq tq FH).
Local Notation derived_ranges := (AFgj_w.derived_ranges W ly regs0 mem0 gq tq FH).
Local Notation WINF := (AFgj_w.WINF ly).
Local Notation WINA := (AFgj_w.WINA ly gq).
Local Notation WIN := (AFgj_w.WIN ly regs0 gq).
Local Notation win_sub := AFgj_w.win_sub.
Local Notation win_sub_sound := (AFgj_w.win_sub_sound ly regs0).
Local Notation WSK0 := AFgj_w.WSK0.
Local Notation WSKL := AFgj_w.WSKL.
Local Notation sk_ok := (AFgj_w.sk_ok ly regs0 gq).
Local Notation WSK0_ok := (AFgj_w.WSK0_ok W ly regs0 mem0 gq tq FH).
Local Notation WSKL_ok := (AFgj_w.WSKL_ok W ly regs0 mem0 gq tq FH).
Local Notation windows_WIN := (AFgj_w.windows_WIN ly regs0 gq).
Local Notation WIN_cases := (AFgj_w.WIN_cases W ly regs0 mem0 gq tq FH).
Local Notation MEQ := (AFgj_w.MEQ ly regs0 mem0 gq).
Local Notation MEQ_frame := (AFgj_w.MEQ_frame ly regs0 mem0 gq).
Local Notation MEQ_0 := (AFgj_w.MEQ_0 ly regs0 mem0 gq).
Local Notation WIN0 := (AFgj_w.WIN0 ly regs0).
Local Notation WIN0_WIN := (AFgj_w.WIN0_WIN ly regs0 gq).
Local Notation sk_ok0 := (AFgj_w.sk_ok0 ly regs0).
Local Notation WSK0_ok0 := (AFgj_w.WSK0_ok0 W ly regs0 mem0 gq tq FH).
Local Notation MEQ0 := (AFgj_w.MEQ0 ly regs0 mem0).
Local Notation MEQ0_frame := (AFgj_w.MEQ0_frame ly regs0 mem0).
Local Notation MEQ0_0 := (AFgj_w.MEQ0_0 ly regs0 mem0).
Local Notation MEQ0_MEQ := (AFgj_w.MEQ0_MEQ ly regs0 mem0 gq).
Local Notation all_disjoint_of_forall := AFgj_w.all_disjoint_of_forall.
Local Notation kept_of_frame := (AFgj_w.kept_of_frame W ly regs0).
Local Notation aview_eq_mbyte := AFgj_w.aview_eq_mbyte.
Local Notation R_QW1 := AFgj_w.R_QW1.
Local Notation R_QW0 := AFgj_w.R_QW0.
Local Notation LSZv := (AFgj_w.LSZv gq tq).
Local Notation LBv := (AFgj_w.LBv gq tq).
Local Notation LFv := (AFgj_w.LFv ly gq tq).
Local Notation SREGS := AFgj_w.SREGS.
Local Notation at_RETD := (AFgj_w.at_RETD W ly regs0 mem0 md0 gq tq).
Local Notation at_L0 := (AFgj_w.at_L0 W ly regs0 mem0 md0 gq tq).
Local Notation postD := (AFgj_w.postD W ly regs0 mem0 md0 gq tq).
Local Notation SKEL_TAIL := AFgj_w.SKEL_TAIL.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hg Ht Hglast SEED].
Local Notation off_T := (AFgj_w.off_T ly).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac meq0_acc SKOK :=
match goal with
| M : MEQ0 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ0_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac qw_split1 HS iW :=
let VW := fresh "VW" in
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) =>
assert (VW : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 4 1) by (memv HS iW 0%nat; [reflexivity | reflexivity | zlia]);
apply (proj1 (val_mem4_bytes _ _ _)) in VW; destruct VW as (VW0 & VW1 & VW2 & VW3);
change (YO0f.le_byte 1 4 0) with 1 in VW0; change (YO0f.le_byte 1 4 1) with 0 in VW1;
change (YO0f.le_byte 1 4 2) with 0 in VW2; change (YO0f.le_byte 1 4 3) with 0 in VW3;
eapply (st_ok_set_region E _ _ iW _ R_QW1) in HS;
[ | reflexivity | repeat split; reflexivity | reflexivity
| apply Forall_cons; [ eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; exact VW0 ]
| apply Forall_cons; [ apply chunk_ok_zero_mb; exact (bytes3_of _ _ _ VW1 VW2 VW3) | apply Forall_nil ] ] ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW0 VW1 VW2 VW3
end.
Ltac qw_join0 HS iW :=
let VW := fresh "VW" in let VZ := fresh "VZ" in
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ ?msx) =>
assert (VW : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 1 0) by (memv HS iW 0%nat; [reflexivity | reflexivity | zlia]);
apply (proj1 (val_mem1_byte _ _ _)) in VW; change (YO0f.le_byte 0 1 0) with 0 in VW;
assert (VZ : forall a, A_QUAR + 153 <= a < A_QUAR + 153 + 3 -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem msx)) a = Some (Z_to_bv 8 0))
by (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msx iW _ 1 _ _ a HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base]; unfold A_QUAR, A_ALLOCATOR, o_quar in Ha; clear - Ha; zlia]);
eapply (st_ok_set_region E _ _ iW _ R_QW0) in HS;
[ | reflexivity | repeat split; reflexivity | reflexivity
| apply Forall_cons; [ apply chunk_ok_zero_mb; refine (bytes4_of _ _ _ VW (VZ _ _) (VZ _ _) (VZ _ _)); zlia | apply Forall_nil ] ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW VZ
end.
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
lazymatch goal with DR : _ |- _ => idtac end;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YP09.mkChunk ?o _) :: ?t => let e := eval vm_compute in (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l;
first [ reflexivity | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 32) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; numconst; zlia
| match goal with B : bv_unsigned (ew _ 36) = _ |- _ => rewrite B end; numconst; zlia ].
Ltac tV HG := first
[ reflexivity
| cbn [sv_denot]; rewrite ?AFgj_w.EqT, ?AFgj_w.EqSB, ?AFgj_w.EqGSZ, ?AFgj_w.EqGF, ?AFgj_w.EqGL, ?AFgj_w.EqGB,
?AFgj_w.EqTSZ, ?AFgj_w.EqTF, ?AFgj_w.EqTL, ?AFgj_w.EqTB; unfold w64; rewrite ?Zbv_add_unsigned;
first [ reflexivity | f_equal; unfold AFgj_w.LFv, AFgj_w.LSZv, AFgj_w.LBv; rewrite ?HG; cbv beta iota; cbn [length Z.of_nat]; zlia
| first [ rewrite (AFgj_w.Er _ _ _ _ 1 1%bv eq_refl) | rewrite (AFgj_w.Er _ _ _ _ 8 8%bv eq_refl) | rewrite (AFgj_w.Er _ _ _ _ 9 9%bv eq_refl)
| rewrite (AFgj_w.Er _ _ _ _ 18 18%bv eq_refl) | rewrite (AFgj_w.Er _ _ _ _ 19 19%bv eq_refl) | rewrite (AFgj_w.Er _ _ _ _ 20 20%bv eq_refl)
| rewrite (AFgj_w.Er _ _ _ _ 12 12%bv eq_refl) | rewrite (AFgj_w.Er _ _ _ _ 13 13%bv eq_refl) ];
rewrite ?Z.add_0_r; first [ reflexivity | apply Z_to_bv_bv_unsigned | f_equal; zlia ] ]
| apply denot_by_zev; [ reflexivity | unfold AFgj_w.LFv, AFgj_w.LSZv, AFgj_w.LBv; rewrite ?HG; cbv beta iota; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
unfold AFgj_w.LFv, AFgj_w.LSZv, AFgj_w.LBv; rewrite ?HG; cbv beta iota; land_lits; numconst; zcanon_simp; zlia ] ].
Ltac tR HG := first [ zlia | apply u64_range | unfold AFgj_w.LFv, AFgj_w.LSZv, AFgj_w.LBv; rewrite ?HG; cbv beta iota; cbn [length Z.of_nat]; numconst; zlia ].
Ltac reg_zev HS r HG :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) E0 _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | unfold AFgj_w.LFv, AFgj_w.LSZv, AFgj_w.LBv; rewrite ?HG; cbv beta iota; numconst; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
unfold AFgj_w.LFv, AFgj_w.LSZv, AFgj_w.LBv; rewrite ?HG; cbv beta iota; land_lits; numconst; zcanon_simp; zlia ].
Ltac reg_val HS r HG := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV HG | reg_zev HS r HG ].
Ltac to_L0 HS HGT HG DR R37 R41 iS iW iG iT tPRES tGLN :=
srr_branch_sh tfibtbl_rtG_ok HS;
[ exfalso;
match goal with Hb : branch_taken _ _ _ = true |- _ =>
clear - Hb DR R37 R41 HGT; zbranch Hb; apply Bool.negb_true_iff in Hb; apply Z.ltb_ge in Hb; unfold AFgj_w.LBv in HGT; zlia end
| unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS;
srr_run_to_sh tfibtbl_rtG_ok HS 0x338a4;
match goal with SKW : AFgj_w.sk_ok _ _ _ _ _ |- _ => meq_acc SKW end;
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [idtac "L0-1"; rewrite HshR at 1; reflexivity|];
split; [idtac "L0-2"; let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite AFgj_w.E2; unfold w64; f_equal; unfold sp0; zlia|];
split; [idtac "L0-3"; reg_lit HS (10%bv : bv 5)|];
split; [idtac "L0-4"; let Q := fresh "Q" in rreg HS (11%bv : bv 5) Q; rewrite Q; reflexivity|];
split; [idtac "L0-5"; let Q := fresh "Q" in rreg HS (12%bv : bv 5) Q; rewrite Q; tV HG|];
split; [idtac "L0-6"; reg_entry HS (13%bv : bv 5) 13%nat|];
split; [idtac "L0-7"; reg_lit HS (14%bv : bv 5)|];
split; [idtac "L0-8"; reg_lit HS (15%bv : bv 5)|];
split; [idtac "L0-9"; reg_val HS (16%bv : bv 5) HG|];
split; [idtac "L0-10"; reg_val HS (5%bv : bv 5) HG|];
split; [idtac "L0-11"; reg_entry HS (1%bv : bv 5) 1%nat|];
split; [idtac "L0-12"; intros r Hr; cbn [AFgj_w.SREGS In] in Hr;
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; assumption
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat
| reg_entry HS (19%bv : bv 5) 19%nat | reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat
| reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]|];
split; [idtac "L0-13"; assumption|];
split; [idtac "L0-14"; tPRES|];
cbv zeta;
split; [idtac "L0-15"; memvo HS iW (A_QUAR + 152); [tA | tV HG | tR HG]|];
split; [idtac "L0-16"; memvo HS iG (A_QUAR + 160); [tA | tV HG | tR HG]|];
split; [idtac "L0-17"; memvo HS iG (A_QUAR + 168); [tA | tV HG | tR HG]|];
split; [idtac "L0-18"; memvo HS iG (A_QUAR + 176); [tA | tV HG | tR HG]|];
split; [idtac "L0-19"; memvo HS iG (A_QUAR + 184); [tA | tV HG | tR HG]|];
split; [idtac "L0-20"; memvo HS iT t_qc; [tA | tV HG | tR HG]|];
split; [idtac "L0-21"; memvo HS iT (t_qc + 8); [tA | tV HG | tR HG]|];
split; [idtac "L0-22"; memvo HS iT (t_qc + 16); [tA | tV HG | tR HG]|];
split; [idtac "L0-23"; memvo HS iT (t_qc + 24); [tA | tV HG | tR HG]|];
split; [idtac "L0-24"; tGLN|];
split; [idtac "L0-25"; memvo HS iS (-80); [tA | tV HG | tR HG]|];
split; [idtac "L0-26"; memvo HS iS (-72); [tA | tV HG | tR HG]|];
split; [idtac "L0-27"; memvo HS iS (-64); [tA | tV HG | tR HG]|];
split; [idtac "L0-28"; memvo HS iS (-56); [tA | tV HG | tR HG]|];
split; [idtac "L0-29"; memvo HS iS (-48); [tA | tV HG | tR HG]|];
split; [idtac "L0-30"; memvo HS iS (-40); [tA | tV HG | tR HG]|];
split; [idtac "L0-31"; memvo HS iS (-32); [tA | tV HG | tR HG]|];
split; [idtac "L0-32"; memvo HS iS (-24); [tA | tV HG | tR HG]|];
split; [idtac "L0-33"; memvo HS iS (-16); [tA | tV HG | tR HG]|];
memvo HS iS (-8); [tA | tV HG | tR HG]
end ].
Ltac presE HS iS iT BV2 BV32 LB Usp HG :=
intros a Ha Hh; unfold AFgj_w.WIN, AFgj_w.WINF, AFgj_w.WINA in Ha; rewrite HG in Ha;
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[Hne _]]];
[ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iS _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Hh Usp; numconst; zlia) ]
| exfalso; clear - Ha Hh; numconst; zlia | exfalso; clear - Ha Hh; numconst; zlia
| eapply (st_ok_window_apresent_off (w_H W) E0 _ _ iT _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ]
| exfalso; exact (Hne eq_refl) ].
Lemma segDE : qc_list gq = [] ->
(kQuarantineMax < LBv -> 2 * (kBatchBytes * LSZv) <= LBv) ->
SRr tfibsegs W cfg0 postD.
Proof.
intros HGE HM. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok0 E0 HE0) as SK0.
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R33 : rho_of E0 33%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R34 : rho_of E0 34%nat = GSZv) by (unfold rho_of; rewrite EqGSZ; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R37 : rho_of E0 37%nat = GBv) by (unfold rho_of; rewrite EqGB; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R38 : rho_of E0 38%nat = TSZv) by (unfold rho_of; rewrite EqTSZ; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R41 : rho_of E0 41%nat = TBv) by (unfold rho_of; rewrite EqTB; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV32 : bv_unsigned (ew E0 32) = T) by exact R32.
assert (BV36 : bv_unsigned (ew E0 36) = GLv) by (rewrite EqGL; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (VMQ : forall m a (n : nat) v, MEQ0 m -> (forall i, 0 <= i < Z.of_nat n -> ~ WIN0 (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) m) a n v).
{ intros m a n v HMq Hn Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(zlia)) as [N1 N2].
apply HMq. rewrite unsigned_lit_small by exact N2. exact N1. }
assert (PRQ : forall m a, MEQ0 m -> ~ WIN0 a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem0 a -> apresent (w_H W) m a).
{ intros m a HMq Hn Ha Hp. apply (apresent_same (w_H W) mem0); [|exact Hp]. apply HMq. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (NW0 : forall a, ~ (sp0 - 80 <= a < sp0) -> ~ (A_QUAR + 152 <= a < A_QUAR + 156) -> ~ (A_QUAR + 160 <= a < A_QUAR + 192) ->
~ (T + t_qc <= a < T + t_qc + 32) -> ~ WIN0 a).
{ intros a N0 N1 N2 N3 [X|X]; [exact (N0 X)|]. unfold AFgj_w.WINF in X. clear - X N1 N2 N3. zlia. }
srr_run_sh tfibtbl_rtG_ok HS. meq0_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
2:{ exfalso. clear - Hc DR R34 HGE. zbranch Hc. apply Z.eqb_neq in Hc. apply Hc. unfold AFgj_w.GSZv. rewrite HGE. reflexivity. }
assert (HGE0 : GSZv = 0) by (unfold AFgj_w.GSZv; rewrite HGE; reflexivity).
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
pose proof (MEQ0_MEQ _ MQ) as MQ1. clear MQ. rename MQ1 into MQ. pose proof (WSK0_ok E0 HE0) as SKW.
srr_run_to_sh tfibtbl_rtG_ok HS 0x336c4. meq_acc SKW.
qw_split1 HS 1%nat.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
{
assert (HLE : LBv <= kQuarantineMax).
{ clear - Hc0 DR R37 R41. zbranch Hc0.
apply Bool.negb_true_iff in Hc0. apply Z.ltb_ge in Hc0. unfold AFgj_w.LBv. zlia. }
unfold AFgj_w.postD. destruct (Z.leb_spec LBv kQuarantineMax) as [_|X]; [|exfalso; clear - X HLE; zlia].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
qw_join0 HS 1%nat.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtG tfibtbl_rtG_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { rreg HS (2%bv : bv 5) Q2. rewrite Q2. exact E2. }
split. { intros r Hr. cbn [AFgj_w.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | rreg HS (4%bv : bv 5) Q4; rewrite Q4, Htp; reflexivity
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat
| reg_entry HS (19%bv : bv 5) 19%nat | reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat
| reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]. }
split. { exact MQ. }
split. { presE HS 0%nat 3%nat BV2 BV32 LB Usp HGE. }
cbv zeta.
split. { intros a Ha. eapply (st_ok_chunk_zero (w_H W) E0 _ msR 1 _ 0 _ _ a HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base AFgj_w.R_QW0]; clear - Ha; numconst; zlia]. }
idtac "CELLS-A".
split. { memvo HS 2%nat (A_QUAR + 160); [tA | tV HGE | tR HGE]. }
split. { memvo HS 2%nat (A_QUAR + 168); [tA | tV HGE | tR HGE]. }
split. { memvo HS 2%nat (A_QUAR + 176); [tA | tV HGE | tR HGE]. }
split. { memvo HS 2%nat (A_QUAR + 184); [tA | tV HGE | tR HGE]. }
split. { memvo HS 3%nat t_qc; [tA | tV HGE | tR HGE]. }
split. { memvo HS 3%nat (t_qc + 8); [tA | tV HGE | tR HGE]. }
split. { memvo HS 3%nat (t_qc + 16); [tA | tV HGE | tR HGE]. }
split. { memvo HS 3%nat (t_qc + 24); [tA | tV HGE | tR HGE]. }
intros lastb initr R. exfalso. rewrite HGE in R. cbn [rev] in R. discriminate R. }
{
assert (HGT : kQuarantineMax < LBv).
{ clear - Hc0 DR R37 R41. zbranch Hc0. apply Bool.negb_false_iff in Hc0. apply Z.ltb_lt in Hc0. unfold AFgj_w.LBv. zlia. }
pose proof (HM HGT) as MC.
unfold AFgj_w.postD. destruct (Z.leb_spec LBv kQuarantineMax) as [X|_]; [exfalso; clear - X HGT; zlia|].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
qw_join0 HS 1%nat.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. clear - Hc1 DR R37 R41 R38 MC HGE0. zbranch Hc1. apply Z.ltb_lt in Hc1.
unfold AFgj_w.LSZv, AFgj_w.LBv in MC. rewrite HGE0 in MC. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
{ unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW. to_L0 HS HGT HGE DR R37 R41 0%nat 1%nat 2%nat 3%nat ltac:(presE HS 0%nat 3%nat BV2 BV32 LB Usp HGE) ltac:(intros lastb initr RR; exfalso; rewrite HGE in RR; cbn [rev] in RR; discriminate RR). }
{ unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
2:{ exfalso. clear - Hc3 DR R37 R41 R38 MC HGE0. zbranch Hc3. apply Bool.negb_false_iff in Hc3. apply Z.ltb_lt in Hc3.
unfold AFgj_w.LSZv, AFgj_w.LBv in MC. rewrite HGE0 in MC. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW. to_L0 HS HGT HGE DR R37 R41 0%nat 1%nat 2%nat 3%nat ltac:(presE HS 0%nat 3%nat BV2 BV32 LB Usp HGE) ltac:(intros lastb initr RR; exfalso; rewrite HGE in RR; cbn [rev] in RR; discriminate RR). } }
Qed.
End WK.
End b.

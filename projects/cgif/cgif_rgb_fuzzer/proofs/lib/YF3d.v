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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF35.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bb bc h0 sz qb lz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33ab4 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 b nx bb bc h0 sz qb lz.
Local Notation XW := (YF35.XW ly b nx bb bc h0 sz qb lz).
Local Notation E0 := (YF35.E0 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation Er := (YF35.Er ly regs0 b nx bb bc h0 sz qb lz).
Local Notation E2 := (YF35.E2 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation E1 := (YF35.E1 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqT := (YF35.EqT ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqB := (YF35.EqB ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqNX := (YF35.EqNX ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqBB := (YF35.EqBB ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqBC := (YF35.EqBC ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqH0 := (YF35.EqH0 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqSZ := (YF35.EqSZ ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqQB := (YF35.EqQB ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqLZ := (YF35.EqLZ ly regs0 b nx bb bc h0 sz qb lz).
Local Notation R_STK := YF35.R_STK.
Local Notation R_B := YF35.R_B.
Local Notation REG0 := YF35.REG0.
Local Notation FFO := YF35.FFO.
Local Notation SR0 := YF35.SR0.
Local Notation SS0 := YF35.SS0.
Local Notation LYB := (YF35.LYB W ly regs0 mem0 b nx bb bc h0 sz qb lz FH).
Local Notation derived_ranges := (YF35.derived_ranges W ly regs0 mem0 b nx bb bc h0 sz qb lz FH).
Local Notation WIN := (YF35.WIN regs0).
Local Notation win_sub := YF35.win_sub.
Local Notation win_sub_sound := (YF35.win_sub_sound ly regs0).
Local Notation WSK0 := YF35.WSK0.
Local Notation sk_ok := (YF35.sk_ok regs0).
Local Notation WSK0_ok := (YF35.WSK0_ok ly regs0 b nx bb bc h0 sz qb lz).
Local Notation windows_WIN := (YF35.windows_WIN ly regs0).
Local Notation MEQ := (YF35.MEQ regs0 mem0).
Local Notation MEQ_frame := (YF35.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (YF35.MEQ_0 regs0 mem0).
Local Notation SREGS := YF35.SREGS.
Local Notation LZn := (YF35.LZn nx lz).
Local Notation at_RC0 := (YF35.at_RC0 W regs0 mem0 md0 b nx bb bc h0 sz qb lz).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hb Hnx Hbc Hby Hsz Hlz Hh0 SEED].
Ltac off_by tac :=
first [ img_apply off_img_high; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
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
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Lemma segYO : SRr tfxsegs W cfg0 at_RC0.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dB1 & dB2 & dBal & dNX & dBC & dBB & dQB & dBQ & dSZ & dLZ & dH1 & dH2 & dS1 & dS2).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R40 : rho_of E0 40%nat = b) by (img_try (unfold rho_of; rewrite EqB; unfold w64; img_apply unsigned_lit_small; clear - dB1 dB2; numconst; zlia)).
assert (R41 : rho_of E0 41%nat = nx) by (img_try (unfold rho_of; rewrite EqNX; unfold w64; img_apply unsigned_lit_small; clear - dNX; numconst; zlia)).
assert (R42 : rho_of E0 42%nat = bb) by (img_try (unfold rho_of; rewrite EqBB; unfold w64; img_apply unsigned_lit_small; clear - dBB; zlia)).
assert (R43 : rho_of E0 43%nat = bc) by (img_try (unfold rho_of; rewrite EqBC; unfold w64; img_apply unsigned_lit_small; clear - dBC; numconst; zlia)).
assert (R46 : rho_of E0 46%nat = sz) by (img_try (unfold rho_of; rewrite EqSZ; unfold w64; img_apply unsigned_lit_small; clear - dSZ; zlia)).
assert (R47 : rho_of E0 47%nat = qb) by (img_try (unfold rho_of; rewrite EqQB; unfold w64; img_apply unsigned_lit_small; clear - dQB; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (BV40 : bv_unsigned (ew E0 40) = b) by img_exact R40.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
-
assert (LZv : (nx =? 0) = false).
{ img_apply Z.eqb_neq. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R41 dNX; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; zlia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfxtbl_rtG_ok HS (0x33b74 + D_150). meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [img_try (rewrite HshR at 1; img_refl)|] end.
split. { idtac "F1". reg_atom HS (2%bv : bv 5) 2%nat. }
split. { idtac "F2". rreg HS (1%bv : bv 5) Q; rewrite Q; img_refl. }
split. { idtac "F3". intros r Hr; cbn [YF35.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; [| | | | | | | img_try (reg_atom HS (26%bv : bv 5) 26%nat) | img_try (reg_atom HS (27%bv : bv 5) 27%nat)].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; img_exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; zlia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; img_refl.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; img_refl.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; img_refl.
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; img_refl. }
split. { idtac "F4". rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia. }
split. { idtac "F5". rreg HS (11%bv : bv 5) Q; rewrite Q; first [rewrite EqH0; img_refl | cbn [sv_denot]; rewrite EqH0; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F6". rreg HS (20%bv : bv 5) Q; rewrite Q; first [rewrite EqB; img_refl | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F7". rreg HS (22%bv : bv 5) Q; rewrite Q; first [rewrite EqBC; img_refl | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F8". rreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F9". rreg HS (24%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F10". rreg HS (25%bv : bv 5) Q; rewrite Q; img_refl. }
split. { img_exact MQ. }
split. { idtac "F12". intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; unfold YF35.WIN in Ha; unfold YFRAME in Ha; clear - Ha; unfold sp0 in *; zlia) | img_try (off_by ltac:(unfold YF35.WIN in Ha; unfold YFRAME in Ha; clear - Ha Usp dS1 dS2; numconst; zlia)) ]. }
cbv zeta.
split. { idtac "F13". memvo HS 0%nat 112; [img_try (rewrite BV2; unfold YFRAME; unfold sp0; zlia) | img_try (cbn [sv_denot]; rewrite EqSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - dSZ; zlia)]. }
split. { idtac "F14". memvo HS 0%nat 120; [img_try (rewrite BV2; unfold YFRAME; unfold sp0; zlia) | img_try (cbn [sv_denot]; rewrite EqNX; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - dNX; numconst; zlia)]. }
split. { idtac "F15". memvo HS 0%nat 128; [img_try (rewrite BV2; unfold YFRAME; unfold sp0; zlia) | img_try (first [img_refl | cbn [sv_denot]; rewrite EqLZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold YF35.LZn; rewrite LZv; zlia | unfold YF35.LZn; rewrite LZv; img_refl]) | img_try (unfold YF35.LZn; rewrite LZv; clear - dLZ; numconst; zlia)]. }
idtac "F16". memvo HS 0%nat 136; [img_try (rewrite BV2; unfold YFRAME; zlia)
| img_try (img_apply denot_by_zev; [ img_refl | clear; unfold zcanon, M64; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R47, ?R42; clear - dBB dQB; unfold zcanon, M64; numconst; zlia ])
| img_try (clear; unfold zcanon, M64; zlia) ].
-
assert (LZv : (nx =? 0) = true).
{ img_apply Z.eqb_eq. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R41 dNX; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; zlia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfxtbl_rtG_ok HS (0x33b74 + D_150). meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [img_try (rewrite HshR at 1; img_refl)|] end.
split. { idtac "F1". reg_atom HS (2%bv : bv 5) 2%nat. }
split. { idtac "F2". rreg HS (1%bv : bv 5) Q; rewrite Q; img_refl. }
split. { idtac "F3". intros r Hr; cbn [YF35.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; [| | | | | | | img_try (reg_atom HS (26%bv : bv 5) 26%nat) | img_try (reg_atom HS (27%bv : bv 5) 27%nat)].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; img_exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; zlia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; img_refl.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; img_refl.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; img_refl.
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; img_refl. }
split. { idtac "F4". rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia. }
split. { idtac "F5". rreg HS (11%bv : bv 5) Q; rewrite Q; first [rewrite EqH0; img_refl | cbn [sv_denot]; rewrite EqH0; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F6". rreg HS (20%bv : bv 5) Q; rewrite Q; first [rewrite EqB; img_refl | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F7". rreg HS (22%bv : bv 5) Q; rewrite Q; first [rewrite EqBC; img_refl | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F8". rreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F9". rreg HS (24%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F10". rreg HS (25%bv : bv 5) Q; rewrite Q; img_refl. }
split. { img_exact MQ. }
split. { idtac "F12". intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; unfold YF35.WIN in Ha; unfold YFRAME in Ha; clear - Ha; unfold sp0 in *; zlia) | img_try (off_by ltac:(unfold YF35.WIN in Ha; unfold YFRAME in Ha; clear - Ha Usp dS1 dS2; numconst; zlia)) ]. }
cbv zeta.
split. { idtac "F13". memvo HS 0%nat 112; [img_try (rewrite BV2; unfold YFRAME; unfold sp0; zlia) | img_try (cbn [sv_denot]; rewrite EqSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - dSZ; zlia)]. }
split. { idtac "F14". memvo HS 0%nat 120; [img_try (rewrite BV2; unfold YFRAME; unfold sp0; zlia) | img_try (cbn [sv_denot]; rewrite EqNX; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia) | img_try (clear - dNX; numconst; zlia)]. }
split. { idtac "F15". memvo HS 0%nat 128; [img_try (rewrite BV2; unfold YFRAME; unfold sp0; zlia) | img_try (first [img_refl | cbn [sv_denot]; rewrite EqLZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold YF35.LZn; rewrite LZv; zlia | unfold YF35.LZn; rewrite LZv; img_refl]) | img_try (unfold YF35.LZn; rewrite LZv; clear - dLZ; numconst; zlia)]. }
idtac "F16". memvo HS 0%nat 136; [img_try (rewrite BV2; unfold YFRAME; zlia)
| img_try (img_apply denot_by_zev; [ img_refl | clear; unfold zcanon, M64; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R47, ?R42; clear - dBB dQB; unfold zcanon, M64; numconst; zlia ])
| img_try (clear; unfold zcanon, M64; zlia) ].
Qed.
End WK.
End d.

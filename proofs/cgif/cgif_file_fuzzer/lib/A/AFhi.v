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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFha.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bb bc h0 sz qb lz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x334ac) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 b nx bb bc h0 sz qb lz.
Local Notation XW := (AFha.XW ly b nx bb bc h0 sz qb lz).
Local Notation E0 := (AFha.E0 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation Er := (AFha.Er ly regs0 b nx bb bc h0 sz qb lz).
Local Notation E2 := (AFha.E2 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation E1 := (AFha.E1 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqT := (AFha.EqT ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqB := (AFha.EqB ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqNX := (AFha.EqNX ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqBB := (AFha.EqBB ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqBC := (AFha.EqBC ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqH0 := (AFha.EqH0 ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqSZ := (AFha.EqSZ ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqQB := (AFha.EqQB ly regs0 b nx bb bc h0 sz qb lz).
Local Notation EqLZ := (AFha.EqLZ ly regs0 b nx bb bc h0 sz qb lz).
Local Notation R_STK := AFha.R_STK.
Local Notation R_B := AFha.R_B.
Local Notation REG0 := AFha.REG0.
Local Notation FFO := AFha.FFO.
Local Notation SR0 := AFha.SR0.
Local Notation SS0 := AFha.SS0.
Local Notation LYB := (AFha.LYB W ly regs0 mem0 b nx bb bc h0 sz qb lz FH).
Local Notation derived_ranges := (AFha.derived_ranges W ly regs0 mem0 b nx bb bc h0 sz qb lz FH).
Local Notation WIN := (AFha.WIN regs0).
Local Notation win_sub := AFha.win_sub.
Local Notation win_sub_sound := (AFha.win_sub_sound ly regs0).
Local Notation WSK0 := AFha.WSK0.
Local Notation sk_ok := (AFha.sk_ok regs0).
Local Notation WSK0_ok := (AFha.WSK0_ok ly regs0 b nx bb bc h0 sz qb lz).
Local Notation windows_WIN := (AFha.windows_WIN ly regs0).
Local Notation MEQ := (AFha.MEQ regs0 mem0).
Local Notation MEQ_frame := (AFha.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFha.MEQ_0 regs0 mem0).
Local Notation SREGS := AFha.SREGS.
Local Notation LZn := (AFha.LZn nx lz).
Local Notation at_RC0 := (AFha.at_RC0 W regs0 mem0 md0 b nx bb bc h0 sz qb lz).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hb Hnx Hbc Hby Hsz Hlz Hh0 SEED].
Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
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
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Lemma segYO : SRr tfibsegs W cfg0 at_RC0.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dB1 & dB2 & dBal & dNX & dBC & dBB & dQB & dBQ & dSZ & dLZ & dH1 & dH2 & dS1 & dS2).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R40 : rho_of E0 40%nat = b) by (unfold rho_of; rewrite EqB; unfold w64; apply unsigned_lit_small; clear - dB1 dB2; numconst; zlia).
assert (R41 : rho_of E0 41%nat = nx) by (unfold rho_of; rewrite EqNX; unfold w64; apply unsigned_lit_small; clear - dNX; numconst; zlia).
assert (R42 : rho_of E0 42%nat = bb) by (unfold rho_of; rewrite EqBB; unfold w64; apply unsigned_lit_small; clear - dBB; zlia).
assert (R43 : rho_of E0 43%nat = bc) by (unfold rho_of; rewrite EqBC; unfold w64; apply unsigned_lit_small; clear - dBC; numconst; zlia).
assert (R46 : rho_of E0 46%nat = sz) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - dSZ; zlia).
assert (R47 : rho_of E0 47%nat = qb) by (unfold rho_of; rewrite EqQB; unfold w64; apply unsigned_lit_small; clear - dQB; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV40 : bv_unsigned (ew E0 40) = b) by exact R40.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
-
assert (LZv : (nx =? 0) = false).
{ apply Z.eqb_neq. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R41 dNX; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; zlia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x3356c. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { idtac "F1". reg_atom HS (2%bv : bv 5) 2%nat. }
split. { idtac "F2". rreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { idtac "F3". intros r Hr; cbn [AFha.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; [| | | | | | | reg_atom HS (26%bv : bv 5) 26%nat | reg_atom HS (27%bv : bv 5) 27%nat].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; zlia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; reflexivity.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; reflexivity.
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; reflexivity. }
split. { idtac "F4". rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia. }
split. { idtac "F5". rreg HS (11%bv : bv 5) Q; rewrite Q; first [rewrite EqH0; reflexivity | cbn [sv_denot]; rewrite EqH0; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F6". rreg HS (20%bv : bv 5) Q; rewrite Q; first [rewrite EqB; reflexivity | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F7". rreg HS (22%bv : bv 5) Q; rewrite Q; first [rewrite EqBC; reflexivity | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F8". rreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F9". rreg HS (24%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F10". rreg HS (25%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { exact MQ. }
split. { idtac "F12". intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold AFha.WIN in Ha; unfold YFRAME in Ha; clear - Ha; unfold sp0 in *; zlia | off_by ltac:(unfold AFha.WIN in Ha; unfold YFRAME in Ha; clear - Ha Usp dS1 dS2; numconst; zlia) ]. }
cbv zeta.
split. { idtac "F13". memvo HS 0%nat 112; [rewrite BV2; unfold YFRAME; unfold sp0; zlia | cbn [sv_denot]; rewrite EqSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - dSZ; zlia]. }
split. { idtac "F14". memvo HS 0%nat 120; [rewrite BV2; unfold YFRAME; unfold sp0; zlia | cbn [sv_denot]; rewrite EqNX; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - dNX; numconst; zlia]. }
split. { idtac "F15". memvo HS 0%nat 128; [rewrite BV2; unfold YFRAME; unfold sp0; zlia | first [reflexivity | cbn [sv_denot]; rewrite EqLZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold AFha.LZn; rewrite LZv; zlia | unfold AFha.LZn; rewrite LZv; reflexivity] | unfold AFha.LZn; rewrite LZv; clear - dLZ; numconst; zlia]. }
idtac "F16". memvo HS 0%nat 136; [rewrite BV2; unfold YFRAME; zlia
| apply denot_by_zev; [ reflexivity | clear; unfold zcanon, M64; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R47, ?R42; clear - dBB dQB; unfold zcanon, M64; numconst; zlia ]
| clear; unfold zcanon, M64; zlia ].
-
assert (LZv : (nx =? 0) = true).
{ apply Z.eqb_eq. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R41 dNX; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; zlia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x3356c. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { idtac "F1". reg_atom HS (2%bv : bv 5) 2%nat. }
split. { idtac "F2". rreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { idtac "F3". intros r Hr; cbn [AFha.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; [| | | | | | | reg_atom HS (26%bv : bv 5) 26%nat | reg_atom HS (27%bv : bv 5) 27%nat].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; zlia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; reflexivity.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; reflexivity.
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; reflexivity. }
split. { idtac "F4". rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia. }
split. { idtac "F5". rreg HS (11%bv : bv 5) Q; rewrite Q; first [rewrite EqH0; reflexivity | cbn [sv_denot]; rewrite EqH0; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F6". rreg HS (20%bv : bv 5) Q; rewrite Q; first [rewrite EqB; reflexivity | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F7". rreg HS (22%bv : bv 5) Q; rewrite Q; first [rewrite EqBC; reflexivity | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia]. }
split. { idtac "F8". rreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F9". rreg HS (24%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia. }
split. { idtac "F10". rreg HS (25%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { exact MQ. }
split. { idtac "F12". intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold AFha.WIN in Ha; unfold YFRAME in Ha; clear - Ha; unfold sp0 in *; zlia | off_by ltac:(unfold AFha.WIN in Ha; unfold YFRAME in Ha; clear - Ha Usp dS1 dS2; numconst; zlia) ]. }
cbv zeta.
split. { idtac "F13". memvo HS 0%nat 112; [rewrite BV2; unfold YFRAME; unfold sp0; zlia | cbn [sv_denot]; rewrite EqSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - dSZ; zlia]. }
split. { idtac "F14". memvo HS 0%nat 120; [rewrite BV2; unfold YFRAME; unfold sp0; zlia | cbn [sv_denot]; rewrite EqNX; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - dNX; numconst; zlia]. }
split. { idtac "F15". memvo HS 0%nat 128; [rewrite BV2; unfold YFRAME; unfold sp0; zlia | first [reflexivity | cbn [sv_denot]; rewrite EqLZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold AFha.LZn; rewrite LZv; zlia | unfold AFha.LZn; rewrite LZv; reflexivity] | unfold AFha.LZn; rewrite LZv; clear - dLZ; numconst; zlia]. }
idtac "F16". memvo HS 0%nat 136; [rewrite BV2; unfold YFRAME; zlia
| apply denot_by_zev; [ reflexivity | clear; unfold zcanon, M64; zlia
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R47, ?R42; clear - dBB dQB; unfold zcanon, M64; numconst; zlia ]
| clear; unfold zcanon, M64; zlia ].
Qed.
End WK.
End d.

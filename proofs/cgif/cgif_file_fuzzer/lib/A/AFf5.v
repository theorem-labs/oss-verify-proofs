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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFgu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (m n q : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 A_RChunk) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 m n q.
Local Notation XW := (AFgu.XW ly m n q).
Local Notation E0 := (AFgu.E0 ly regs0 m n q).
Local Notation Er := (AFgu.Er ly regs0 m n q).
Local Notation E2 := (AFgu.E2 ly regs0 m n q).
Local Notation E1 := (AFgu.E1 ly regs0 m n q).
Local Notation EqSB := (AFgu.EqSB ly regs0 m n q).
Local Notation EqM := (AFgu.EqM ly regs0 m n q).
Local Notation EqN := (AFgu.EqN ly regs0 m n q).
Local Notation EqQ := (AFgu.EqQ ly regs0 m n q).
Local Notation R_STK := AFgu.R_STK.
Local Notation R_MUT := AFgu.R_MUT.
Local Notation REG0 := AFgu.REG0.
Local Notation FFA := AFgu.FFA.
Local Notation SR0 := AFgu.SR0.
Local Notation SS0 := AFgu.SS0.
Local Notation LYB := (AFgu.LYB W ly regs0 mem0 m n q FH).
Local Notation WIN := (AFgu.WIN regs0).
Local Notation win_sub := AFgu.win_sub.
Local Notation win_sub_sound := (AFgu.win_sub_sound ly regs0).
Local Notation WSK0 := AFgu.WSK0.
Local Notation sk_ok := (AFgu.sk_ok regs0).
Local Notation WSK0_ok := (AFgu.WSK0_ok ly regs0 m n q).
Local Notation windows_WIN := (AFgu.windows_WIN ly regs0).
Local Notation MEQ := (AFgu.MEQ regs0 mem0).
Local Notation MEQ_frame := (AFgu.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFgu.MEQ_0 regs0 mem0).
Local Notation SREGS := AFgu.SREGS.
Local Notation at_L0 := (AFgu.at_L0 W regs0 mem0 md0 m n q).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hregs Hsp Hsp_al Hpres Hm Hsb Hn Hq Hmut SEED].
Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
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
Ltac zdec Hbr := zbranch Hbr; unfold zcanon, M64 in Hbr;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hbr;
first [apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr | apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.leb_le in Hbr | apply Z.leb_gt in Hbr];
try unfold SB in *; try unfold sp0 in *; zlia.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
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
Ltac wordeq_prep := apply bv_eq; unfold w64; rewrite ?Z_to_bv_unsigned; repeat (rewrite alu64_unsigned; cbn [zalu_raw]);
repeat match goal with R : rho_of _ ?k = _ |- context [bv_unsigned (ew _ ?k)] => unfold rho_of in R; rewrite R end;
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
repeat match goal with |- context [?a mod ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (a mod b) in change (a mod b) with c end;
repeat match goal with |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Lemma segGA : SRr tfibsegs W cfg0 at_L0.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB.
destruct Hsp as [S1 S2]. destruct Hm as (M1 & M2 & M3 & FAR). destruct Hn as [Vn Hn]. destruct Hq as (Vq & Q1 & Q2 & Q3). pose proof Hmut as Vmut.
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
evalS HS.
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (R32 : rho_of E0 32%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - L1 L2 L3 L4; numconst; zlia).
assert (R33 : rho_of E0 33%nat = m) by (unfold rho_of; rewrite EqM; unfold w64; apply unsigned_lit_small; clear - M1 M2; numconst; zlia).
assert (R34 : rho_of E0 34%nat = n) by (unfold rho_of; rewrite EqN; unfold w64; apply unsigned_lit_small; clear - Hn; numconst; zlia).
assert (R35 : rho_of E0 35%nat = q) by (unfold rho_of; rewrite EqQ; unfold w64; apply unsigned_lit_small; clear - Q1 Q2 Hn; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
eassert (JOIN : forall ms1 mat1, MEQ (ms_mem ms1) ->
st_ok tfibsegs E0 _ (restrict (w_H W) ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) at_L0).
2: { destruct FAR as [FL|FR].
- srr_branch_sh tfibtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R33 M1 M2 L1 L2 L3 L4 FL; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x335e0. meq_acc SK0. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN; [exact MQ | exact HS].
- srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R32 R33 M1 M2 L1 L2 L3 L4 FR; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R32 R33 M1 M2 L1 L2 L3 L4 FR; zdec Hbr end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x335e0. meq_acc SK0. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN; [exact MQ | exact HS]. }
clear MQ HS. intros ms1 mat1 MQ HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x3385c. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { intros r Hr; cbn [AFgu.SREGS In] in Hr.
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with |- getr _ ?r = getr regs0 ?r => let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_atom HS r k end. }
split. { rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold AFgu.GFRAME, w64; f_equal; unfold sp0; zlia. }
split. { rreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { rreg HS (8%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { rreg HS (9%bv : bv 5) Q; rewrite Q; first [exact EqM | cbn [sv_denot]; rewrite EqM; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { rreg HS (10%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { rreg HS (11%bv : bv 5) Q; rewrite Q; first [exact EqM | cbn [sv_denot]; rewrite EqM; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { rreg HS (12%bv : bv 5) Q; rewrite Q; first [exact EqQ | cbn [sv_denot]; rewrite EqQ; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { rreg HS (13%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { rreg HS (14%bv : bv 5) Q; rewrite Q. clear - R34 R35 Hn Q1 Q2. wordeq_prep. numconst. zlia. }
split. { rreg HS (19%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { rreg HS (20%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { exact MQ. }
split. { intros a Ha.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold sp0; unfold AFgu.GFRAME in *; clear - Ha; zlia | off_by ltac:(clear - Ha S1 S2 L5 L6; unfold AFgu.GFRAME in *; numconst; unfold KSTACK in *; zlia) ]. }
unfold AFgu.GFRAME in *.
split. { memvo HS 0%nat (-8); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-16); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-24); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-32); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-40); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-48); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-56); [rewrite BV2; unfold sp0; zlia | reflexivity | cbn; zlia]. }
split. { memvo HS 0%nat (-64); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
split. { memvo HS 0%nat (-72); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite EqM; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity | clear - M1 M2; numconst; zlia]. }
split. { memvo HS 0%nat (-80); [rewrite BV2; unfold sp0; zlia | cbn [sv_denot]; rewrite (Er 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply u64_range]. }
memvo HS 1%nat (A_ALLOCATOR + 680); [reflexivity | reflexivity | cbn; zlia].
Qed.
End WK.
End d.

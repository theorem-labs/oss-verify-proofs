(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhe.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFhe.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFeq_w AFew_w AFeu_w AFh9_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (sz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 A_DoRecycle) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 sz.
Local Notation XW := (AFh9_w.XW ly sz).
Local Notation E0 := (AFh9_w.E0 ly regs0 sz).
Local Notation Er := (AFh9_w.Er ly regs0 sz).
Local Notation E2 := (AFh9_w.E2 ly regs0 sz).
Local Notation E1 := (AFh9_w.E1 ly regs0 sz).
Local Notation EqT := (AFh9_w.EqT ly regs0 sz).
Local Notation EqSZ := (AFh9_w.EqSZ ly regs0 sz).
Local Notation R_STK := AFh9_w.R_STK.
Local Notation REG0 := AFh9_w.REG0.
Local Notation FFE := AFh9_w.FFE.
Local Notation SR0 := AFh9_w.SR0.
Local Notation SS0 := AFh9_w.SS0.
Local Notation LYB := (AFh9_w.LYB W ly regs0 mem0 sz FH).
Local Notation derived_ranges := (AFh9_w.derived_ranges W ly regs0 mem0 sz FH).
Local Notation WIN := (AFh9_w.WIN regs0).
Local Notation win_sub := AFh9_w.win_sub.
Local Notation win_sub_sound := (AFh9_w.win_sub_sound ly regs0).
Local Notation WSK0 := AFh9_w.WSK0.
Local Notation sk_ok := (AFh9_w.sk_ok regs0).
Local Notation WSK0_ok := (AFh9_w.WSK0_ok ly regs0 sz).
Local Notation windows_WIN := (AFh9_w.windows_WIN ly regs0).
Local Notation MEQ := (AFh9_w.MEQ regs0 mem0).
Local Notation MEQ_frame := (AFh9_w.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFh9_w.MEQ_0 regs0 mem0).
Local Notation SAVED := AFh9_w.SAVED.
Local Notation saved_cells := (AFh9_w.saved_cells regs0).
Local Notation SREGS := AFh9_w.SREGS.
Local Notation at_OE := (AFh9_w.at_OE W ly regs0 mem0 md0 sz).
Local Notation SREGS_X := AFh9_w.SREGS_X.
Local Notation at_RETE := (AFh9_w.at_RETE W regs0 mem0 md0 sz).
Local Notation postE := (AFh9_w.postE W ly regs0 mem0 md0 sz).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hra Hsz SEED].
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
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_atomv HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ reflexivity | f_equal; zlia ].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac saved HS off k r BV2 := memvo HS 0%nat off; [rewrite BV2; zlia | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; reflexivity | apply u64_range].
Lemma segYE : SRr tfibsegs W cfg0 postE.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
pose proof derived_ranges as (dK1 & dK2 & dSZ & dT1 & dT2 & dT3).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R46 : rho_of E0 46%nat = sz) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - dSZ; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
-
assert (HZ : sz = 0).
{ lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R46 dSZ; zbranch Hbr; apply Z.eqb_eq in Hbr; zlia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
unfold AFh9_w.postE. replace (sz =? 0) with true by (symmetry; apply Z.eqb_eq; exact HZ).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtG tfibtbl_rtG_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. split; [exact HZ|]. exists (ms_regs msR), (ms_mem msR), mat'.
assert (RA : getr (ms_regs msR) 1 = getr regs0 1) by (reg_entry HS (1%bv : bv 5) 1%nat).
split. { rewrite RA. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { reg_entry HS (2%bv : bv 5) 2%nat. }
split. { intros r Hr. cbn [AFh9_w.SREGS_X In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
first [ exact RA | reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (8%bv : bv 5) 8%nat | reg_entry HS (9%bv : bv 5) 9%nat | reg_entry HS (18%bv : bv 5) 18%nat | reg_entry HS (19%bv : bv 5) 19%nat
| reg_entry HS (20%bv : bv 5) 20%nat | reg_entry HS (21%bv : bv 5) 21%nat | reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat
| reg_entry HS (24%bv : bv 5) 24%nat | reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]. }
split. { exact MQ. }
intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold AFh9_w.WIN in Ha; unfold YFRAME in Ha; clear - Ha; unfold sp0 in *; zlia | off_by ltac:(unfold AFh9_w.WIN in Ha; unfold YFRAME in Ha; clear - Ha Usp dK1 dK2; numconst; zlia) ].
-
assert (HNZ : sz <> 0).
{ lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R46 dSZ; zbranch Hbr; apply Z.eqb_neq in Hbr; zlia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33b88. meq_acc SK0.
unfold AFh9_w.postE. replace (sz =? 0) with false by (symmetry; apply Z.eqb_neq; exact HNZ).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [exact HNZ|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; numconst; zlia. }
split. { intros r Hr. cbn [AFh9_w.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ]. }
split. { let Q := fresh "Q" in rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2, ?Z.add_0_r; unfold w64; unfold sp0; first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned | f_equal; zlia]. }
split. { reg_lit HS (9%bv : bv 5). }
split. { reg_lit HS (18%bv : bv 5). }
split. { reg_lit HS (19%bv : bv 5). }
split. { reg_lit HS (21%bv : bv 5). }
split. { reg_atomv HS (10%bv : bv 5) constr:(EqSZ). }
split. { exact MQ. }
split. { intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold AFh9_w.WIN in Ha; unfold YFRAME in Ha; clear - Ha; unfold sp0 in *; zlia | off_by ltac:(unfold AFh9_w.WIN in Ha; unfold YFRAME in Ha; clear - Ha Usp dK1 dK2; numconst; zlia) ]. }
split. { idtac "CB". memvo HS 0%nat (-104); [rewrite BV2; unfold YFRAME; zlia | cbn [sv_denot]; rewrite EqT; unfold w64; rewrite Zbv_add_unsigned; reflexivity | clear - dT1 dT2; numconst; zlia]. }
idtac "SAVED".
intros k r Hk. cbn [AFh9_w.SAVED] in Hk.
destruct k as [|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]; cbn [nth_error] in Hk; [injection Hk as <- ..| destruct k; discriminate]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
+ saved HS (-8) 1%nat (1%bv : bv 5) BV2.
+ saved HS (-16) 8%nat (8%bv : bv 5) BV2.
+ saved HS (-24) 9%nat (9%bv : bv 5) BV2.
+ saved HS (-32) 18%nat (18%bv : bv 5) BV2.
+ saved HS (-40) 19%nat (19%bv : bv 5) BV2.
+ saved HS (-48) 20%nat (20%bv : bv 5) BV2.
+ saved HS (-56) 21%nat (21%bv : bv 5) BV2.
+ saved HS (-64) 22%nat (22%bv : bv 5) BV2.
+ saved HS (-72) 23%nat (23%bv : bv 5) BV2.
+ saved HS (-80) 24%nat (24%bv : bv 5) BV2.
+ saved HS (-88) 25%nat (25%bv : bv 5) BV2.
Qed.
End WK.
End b.

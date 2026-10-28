(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFhb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33530) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9.
Local Notation XW := (AFhb.XW sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation E0 := (AFhb.E0 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation Er := (AFhb.Er regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation E2 := (AFhb.E2 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation E1 := (AFhb.E1 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqSZ := (AFhb.EqSZ regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqRA := (AFhb.EqRA regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS0 := (AFhb.EqS0 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS1 := (AFhb.EqS1 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS2 := (AFhb.EqS2 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS3 := (AFhb.EqS3 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS4 := (AFhb.EqS4 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS5 := (AFhb.EqS5 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS6 := (AFhb.EqS6 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS7 := (AFhb.EqS7 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS8 := (AFhb.EqS8 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS9 := (AFhb.EqS9 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation R_STK := AFhb.R_STK.
Local Notation REG0 := AFhb.REG0.
Local Notation FFQ := AFhb.FFQ.
Local Notation SR0 := AFhb.SR0.
Local Notation SS0 := AFhb.SS0.
Local Notation LYB := (AFhb.LYB W ly regs0 mem0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 FH).
Local Notation derived_ranges := (AFhb.derived_ranges W ly regs0 mem0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 FH).
Local Notation WIN := AFhb.WIN.
Local Notation win_sub := AFhb.win_sub.
Local Notation win_sub_sound := (AFhb.win_sub_sound ly regs0).
Local Notation WSK0 := AFhb.WSK0.
Local Notation sk_ok := AFhb.sk_ok.
Local Notation WSK0_ok := (AFhb.WSK0_ok regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation windows_WIN := (AFhb.windows_WIN ly regs0).
Local Notation MEQ := (AFhb.MEQ mem0).
Local Notation MEQ_frame := (AFhb.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFhb.MEQ_0 mem0).
Local Notation MEQ_all := (AFhb.MEQ_all mem0).
Local Notation SREGS := AFhb.SREGS.
Local Notation at_O := (AFhb.at_O W regs0 mem0 md0 sz).
Local Notation SREGS_X := AFhb.SREGS_X.
Local Notation at_RETQ := (AFhb.at_RETQ W regs0 mem0 md0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation postQ := (AFhb.postQ W regs0 mem0 md0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hra Hsz Hvals SEED].
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
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_atomv HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ reflexivity | f_equal; lia ].
Lemma segYQ : SRr tfibsegs W cfg0 postQ.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
pose proof derived_ranges as (dK1 & dK2 & dSZ).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R46 : rho_of E0 46%nat = sz) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - dSZ; lia).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
-
assert (HNZ : sz <> 0).
{ lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R46 dSZ; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x334ac. meq_acc SK0.
unfold AFhb.postQ. replace (sz =? 0) with false by (symmetry; apply Z.eqb_neq; exact HNZ).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
assert (MM : ms_mem msx = mem0) by (apply functional_extensionality; intros x; exact (MEQ_all _ MQ x));
apply SRr_ret; split; [reflexivity|]; split; [exact HNZ|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), mt end;
split; [rewrite HshR at 1; rewrite MM; reflexivity|] end.
split. { reg_entry HS (2%bv : bv 5) 2%nat. }
split. { intros r Hr; cbn [AFhb.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
- reg_entry HS (3%bv : bv 5) 3%nat.
- let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity.
- let Q := fresh "Q" in rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; numconst; lia.
- let Q := fresh "Q" in rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity.
- let Q := fresh "Q" in rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; reflexivity.
- let Q := fresh "Q" in rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; reflexivity.
- let Q := fresh "Q" in rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21); rewrite R21; reflexivity.
- reg_entry HS (26%bv : bv 5) 26%nat.
- reg_entry HS (27%bv : bv 5) 27%nat. }
reg_atomv HS (10%bv : bv 5) constr:(EqSZ).
-
assert (HZ : sz = 0).
{ lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R46 dSZ; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
unfold AFhb.postQ. replace (sz =? 0) with true by (symmetry; apply Z.eqb_eq; exact HZ).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtG tfibtbl_rtG_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. split; [exact HZ|]. exists (ms_regs msR), mat'.
rreg HS (1%bv : bv 5) Q1.
assert (MM : ms_mem msR = mem0).
{ apply functional_extensionality. intros x. exact (MEQ_all _ MQ x). }
assert (RA : getr (ms_regs msR) 1 = w64 vra) by (rewrite Q1; first [exact EqRA | cbn [sv_denot]; rewrite EqRA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]).
split. { rewrite RA, MM. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; numconst; lia. }
split. { exact RA. }
split. { reg_atomv HS (8%bv : bv 5) constr:(EqS0). }
split. { reg_atomv HS (9%bv : bv 5) constr:(EqS1). }
split. { reg_atomv HS (18%bv : bv 5) constr:(EqS2). }
split. { reg_atomv HS (19%bv : bv 5) constr:(EqS3). }
split. { reg_atomv HS (20%bv : bv 5) constr:(EqS4). }
split. { reg_atomv HS (21%bv : bv 5) constr:(EqS5). }
split. { reg_atomv HS (22%bv : bv 5) constr:(EqS6). }
split. { reg_atomv HS (23%bv : bv 5) constr:(EqS7). }
split. { reg_atomv HS (24%bv : bv 5) constr:(EqS8). }
split. { reg_atomv HS (25%bv : bv 5) constr:(EqS9). }
intros r Hr. cbn [AFhb.SREGS_X In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; reflexivity
| reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Qed.
End WK.
End a.

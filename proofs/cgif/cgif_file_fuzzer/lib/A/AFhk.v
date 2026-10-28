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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFhc.
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
Variables (b bc hi i : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x334f8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 b bc hi i.
Local Notation S7v := (AFhc.S7v b i).
Local Notation XW := (AFhc.XW ly b bc hi i).
Local Notation E0 := (AFhc.E0 ly regs0 b bc hi i).
Local Notation Er := (AFhc.Er ly regs0 b bc hi i).
Local Notation E2 := (AFhc.E2 ly regs0 b bc hi i).
Local Notation E1 := (AFhc.E1 ly regs0 b bc hi i).
Local Notation EqT := (AFhc.EqT ly regs0 b bc hi i).
Local Notation EqSB := (AFhc.EqSB ly regs0 b bc hi i).
Local Notation EqB := (AFhc.EqB ly regs0 b bc hi i).
Local Notation EqBC := (AFhc.EqBC ly regs0 b bc hi i).
Local Notation EqHI := (AFhc.EqHI ly regs0 b bc hi i).
Local Notation EqS7 := (AFhc.EqS7 ly regs0 b bc hi i).
Local Notation EqI := (AFhc.EqI ly regs0 b bc hi i).
Local Notation R_STK := AFhc.R_STK.
Local Notation REG0 := AFhc.REG0.
Local Notation R_SLOT := AFhc.R_SLOT.
Local Notation FFY := AFhc.FFY.
Local Notation SR0 := AFhc.SR0.
Local Notation SS0 := AFhc.SS0.
Local Notation LYB := (AFhc.LYB W ly regs0 mem0 b bc hi i FH).
Local Notation derived_ranges := (AFhc.derived_ranges W ly regs0 mem0 b bc hi i FH).
Local Notation WIN := AFhc.WIN.
Local Notation win_sub := AFhc.win_sub.
Local Notation win_sub_sound := (AFhc.win_sub_sound ly regs0).
Local Notation WSK0 := AFhc.WSK0.
Local Notation sk_ok := AFhc.sk_ok.
Local Notation WSK0_ok := (AFhc.WSK0_ok ly regs0 b bc hi i).
Local Notation windows_WIN := (AFhc.windows_WIN ly regs0).
Local Notation MEQ := (AFhc.MEQ mem0).
Local Notation MEQ_frame := (AFhc.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFhc.MEQ_0 mem0).
Local Notation SREGS := AFhc.SREGS.
Local Notation at_RCi := (AFhc.at_RCi W regs0 mem0 md0 b bc hi i).
Local Notation at_CD24 := (AFhc.at_CD24 W ly regs0 mem0 md0 b bc i).
Local Notation postR := (AFhc.postR W ly regs0 mem0 md0 b bc hi i).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hcb Hsb Hb Hi Hslot Hhi0 SEED].
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
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Definition A2T : sv := SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 34%nat 0) (SLit 2475880078570760549664030720)) (SAlu ALU_SLL (SOff 40%nat 0) (SLit 27))) (SLit 59).
Lemma A2_val : forall (rho : nat -> Z) sb p cc rel, rho 34%nat = sb -> rho 40%nat = p -> p - sb = cc * 2 ^ 32 + rel -> 0 <= rel < 2 ^ 32 -> 0 <= cc < 32 ->
0 <= sb -> sb <= p < 2 ^ 64 -> zev rho A2T = cc.
Proof.
intros rho sb p cc rel H34 H40 Hd Hrel Hcc Hsb Hp. unfold A2T. cbn [zev zalu_raw zmd_raw]. rewrite H34, H40, !Z.add_0_r.
change (Z.land (zcanon 27) 63) with 27. change (Z.land (zcanon 59) 63) with 59.
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (zcanon 2475880078570760549664030720) with (2 ^ 64 - 2 ^ 27).
unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. change (2 ^ 27) with 134217728. change (2 ^ 59) with 576460752303423488.
change (2 ^ 32) with 4294967296 in *. lia.
Qed.
Lemma segYR : SRr tfibsegs W cfg0 postR.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dS1 & dS2 & dSal & dB1 & dB2 & dBal & dI & dBC & dHI & dS7 & dT1 & dT2 & dK1 & dK2).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R34 : rho_of E0 34%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - dS1 dS2; numconst; lia).
assert (R40 : rho_of E0 40%nat = b) by (unfold rho_of; rewrite EqB; unfold w64; apply unsigned_lit_small; clear - dS1 dS2 dB1 dB2; numconst; lia).
assert (R43 : rho_of E0 43%nat = bc) by (unfold rho_of; rewrite EqBC; unfold w64; apply unsigned_lit_small; clear - dI dBC; numconst; lia).
assert (R45 : rho_of E0 45%nat = S7v) by (unfold rho_of; rewrite EqS7; unfold w64; apply unsigned_lit_small; clear - dS1 dS2 dB1 dB2 dS7 dI dBC; numconst; lia).
assert (R52 : rho_of E0 52%nat = i) by (unfold rho_of; rewrite EqI; unfold w64; apply unsigned_lit_small; clear - dI dBC; numconst; lia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV45 : bv_unsigned (ew E0 45) = S7v) by exact R45.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
-
assert (HLT : i < bc).
{ lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R52 R43 dI dBC; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
destruct (Hslot HLT) as (Vhi & Phi & H1 & H2 & H3).
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | reflexivity
| unfold AFhc.R_SLOT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV45;
split; [clear - dS1 dS2 dB1 dB2 dS7 dI dBC; numconst; lia|]; split; [clear - dS1 dS2 dB1 dB2 dS7 dI dBC; numconst; lia|];
split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqHI; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; reflexivity | clear - dHI; cbn; numconst; lia | cbn; lia |];
lazymatch goal with M : MEQ ?mm |- val_mem _ (mrestrict _ ?mm) _ _ _ => eapply val_mem_frame; [intros kk Hkk; apply M; intros [] | eapply val_mem_addr; [exact Vhi | unfold AFhc.S7v; lia]] end
| unfold AFhc.R_SLOT; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV2, ?BV45;
unfold AFhc.S7v in *; pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & _); clear - L1 L2 L3 L4 L5 L6 L7 dS1 dS2 dB1 dB2 dI dBC dK1 dK2 Hlo Hhi; try unfold SB in *; try unfold sp0 in *; numconst; repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x3356c. meq_acc SK0.
unfold AFhc.postR. replace (i <? bc) with true by (symmetry; apply Z.ltb_lt; exact HLT).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [exact HLT|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { reg_atom HS (2%bv : bv 5) 2%nat. }
split. { rreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { intros r Hr; cbn [AFhc.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; [| | | | | | | | | | reg_atom HS (26%bv : bv 5) 26%nat | reg_atom HS (27%bv : bv 5) 27%nat].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; lia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; reflexivity.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; reflexivity.
- rreg HS (20%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & R20 & _); rewrite R20; first [rewrite EqB; reflexivity | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia].
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; reflexivity.
- rreg HS (22%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & R22 & _); rewrite R22; first [rewrite EqBC; reflexivity | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia].
- rreg HS (24%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & _ & _ & R24 & _); rewrite R24; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia. }
split. { rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; lia. }
split. { rreg HS (11%bv : bv 5) Q; rewrite Q; first [rewrite EqHI; reflexivity | cbn [sv_denot]; rewrite EqHI; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]. }
split. { rreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqS7; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia. }
split. { rreg HS (25%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqI; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia. }
exact MQ.
-
assert (HEQ : i = bc).
{ lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R52 R43 dI dBC; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R40 R34 dS1 dS2 dB1 dB2; zbranch Hbr; apply Z.ltb_lt in Hbr; lia end. }
uncond HS. srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R40 R34 dS1 dS2 dB1 dB2; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.ltb_ge in Hbr; lia end. }
uncond HS. srr_run_to_sh tfibtbl_rtG_ok HS 0x33524. meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 12%bv (SLit kBatchClass)) in HS;
[ | intros X; discriminate
| pin_prep; change (zev (rho_of E0) (SLit kBatchClass) = zev (rho_of E0) A2T);
rewrite (A2_val (rho_of E0) SB b 24 (b - SB - 24 * 2 ^ 32) R34 R40); [reflexivity | lia | clear - dB1 dB2; numconst; lia | lia | clear - dS1; numconst; lia | clear - dS1 dS2 dB1 dB2; numconst; lia ] ].
unpin HS. srr_run_to_sh tfibtbl_rtG_ok HS 0x33970. meq_acc SK0.
unfold AFhc.postR. replace (i <? bc) with false by (symmetry; apply Z.ltb_ge; lia).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [exact HEQ|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { reg_atom HS (2%bv : bv 5) 2%nat. }
split. { rreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { intros r Hr; cbn [AFhc.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; [| | | | | | | | | | reg_atom HS (26%bv : bv 5) 26%nat | reg_atom HS (27%bv : bv 5) 27%nat].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; lia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; reflexivity.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; reflexivity.
- rreg HS (20%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & R20 & _); rewrite R20; first [rewrite EqB; reflexivity | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia].
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; reflexivity.
- rreg HS (22%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & R22 & _); rewrite R22; first [rewrite EqBC; reflexivity | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia].
- rreg HS (24%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & _ & _ & R24 & _); rewrite R24; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia. }
split. { rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqT; unfold w64; rewrite Zbv_add_unsigned; reflexivity. }
split. { rreg HS (11%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); reflexivity. }
split. { rreg HS (12%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { rreg HS (13%bv : bv 5) Q; rewrite Q; first [rewrite EqB; reflexivity | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia]. }
exact MQ.
Qed.
End WK.
End a.

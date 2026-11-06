(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecZ.v (commit 67deba317dfb, blob d98f12a22431) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 3 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFha AFhk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrec.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Set Printing Depth 100. Local Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, kFreeArrayOffset, DMrec.RZ.YFRAME in *.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma A2_val0 : forall (rho : nat -> Z) sb p cc rel, rho 34%nat = sb -> rho 40%nat = p -> p - sb = cc * 2 ^ 32 + rel -> 0 <= rel < 2 ^ 32 -> 0 <= cc < 32 ->
0 <= sb -> sb <= p < 2 ^ 64 -> zev rho AFhk.A2T = cc.
Proof.
intros rho sb p cc rel H34 H40 Hd Hrel Hcc Hsb Hp. unfold AFhk.A2T. cbn [zev zalu_raw zmd_raw]. rewrite H34, H40, !Z.add_0_r.
change (Z.land (zcanon 27) 63) with 27. change (Z.land (zcanon 59) 63) with 59.
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (zcanon 2475880078570760549664030720) with (2 ^ 64 - 2 ^ 27).
unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. change (2 ^ 27) with 134217728. change (2 ^ 59) with 576460752303423488.
change (2 ^ 32) with 4294967296 in *. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bb sz qb lz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34750) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : DMrec.RZ.free_hyps W ly regs0 mem0 b nx bb sz qb lz.
Local Notation E0 := (DMrec.RZ.E0 ly regs0 b nx bb sz qb lz).
Local Notation Er := (DMrec.RZ.Er ly regs0 b nx bb sz qb lz).
Local Notation E2 := (DMrec.RZ.E2 ly regs0 b nx bb sz qb lz).
Local Notation EqT := (DMrec.RZ.EqT ly regs0 b nx bb sz qb lz).
Local Notation EqSB := (DMrec.RZ.EqSB ly regs0 b nx bb sz qb lz).
Local Notation EqB := (DMrec.RZ.EqB ly regs0 b nx bb sz qb lz).
Local Notation EqNX := (DMrec.RZ.EqNX ly regs0 b nx bb sz qb lz).
Local Notation EqBB := (DMrec.RZ.EqBB ly regs0 b nx bb sz qb lz).
Local Notation EqSZ := (DMrec.RZ.EqSZ ly regs0 b nx bb sz qb lz).
Local Notation EqQB := (DMrec.RZ.EqQB ly regs0 b nx bb sz qb lz).
Local Notation EqLZ := (DMrec.RZ.EqLZ ly regs0 b nx bb sz qb lz).
Local Notation LYB := (DMrec.RZ.LYB W ly regs0 mem0 b nx bb sz qb lz FH).
Local Notation derived_ranges := (DMrec.RZ.derived_ranges W ly regs0 mem0 b nx bb sz qb lz FH).
Local Notation WIN := (DMrec.RZ.WIN regs0).
Local Notation WSK0_ok := (DMrec.RZ.WSK0_ok ly regs0 b nx bb sz qb lz).
Local Notation MEQ := (DMrec.RZ.MEQ regs0 mem0).
Local Notation MEQ_frame := (DMrec.RZ.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (DMrec.RZ.MEQ_0 regs0 mem0).
Local Notation at_CD0 := (DMrec.RZ.at_CD0 W ly regs0 mem0 md0 b nx bb sz qb lz).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hb Hnx Hby Hsz Hlz SEED].
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
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
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
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].

Lemma b_rel : SB + 24 * 2 ^ 32 <= b /\ b - SB - 24 * 2 ^ 32 < 2 ^ 32.
Proof.
open_FH. destruct Hb as (B1 & B2 & _).
assert (RO : region_off kBatchClass = 24 * 2 ^ 32) by reflexivity. rewrite RO in B1, B2.
unfold SB. split; [exact B1|]. clear - B2. unfold kBatchBytes, kFreeArrayOffset in *. lia.
Qed.

Lemma segZ : SRr tfibsegs W cfg0 at_CD0.
Proof.
pose proof b_rel as (bR1 & bR2).
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB.
pose proof derived_ranges as DR.
destruct DR as (dSB1 & dSB2 & dSBal & dB1 & dB2 & dBal & dNX & dBB & dQB & dSZ & dLZ & dT1 & dT2 & dS1 & dS2).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R34 : rho_of E0 34%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - dSB1 dSB2; numconst; lia).
assert (R40 : rho_of E0 40%nat = b) by (unfold rho_of; rewrite EqB; unfold w64; apply unsigned_lit_small; clear - dSB1 dSB2 dB1 dB2 bR2; unfold SB in *; numconst; lia).
assert (R41 : rho_of E0 41%nat = nx) by (unfold rho_of; rewrite EqNX; unfold w64; apply unsigned_lit_small; clear - dNX; numconst; lia).
assert (R42 : rho_of E0 42%nat = bb) by (unfold rho_of; rewrite EqBB; unfold w64; apply unsigned_lit_small; clear - dBB; lia).
assert (R46 : rho_of E0 46%nat = sz) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - dSZ; lia).
assert (R47 : rho_of E0 47%nat = qb) by (unfold rho_of; rewrite EqQB; unfold w64; apply unsigned_lit_small; clear - dQB; lia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS.
1: assert (LZv : (nx =? 0) = false)
  by (apply Z.eqb_neq; lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R41 dNX; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; lia end).
2: assert (LZv : (nx =? 0) = true)
  by (apply Z.eqb_eq; lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R41 dNX; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; lia end).
all: lazymatch goal with Hbr : branch_taken _ _ _ = _ |- _ => clear Hbr end; uncond HS.
all: srr_run_sh tfibtbl_rtG_ok HS; meq_acc SK0.
all: srr_branch_sh tfibtbl_rtG_ok HS.

1,3: exfalso; lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => rename Hbr into HBR end;
  clear - HBR R40 R34 bR1 bR2 dSB1 dSB2 dB1 dB2; zbranch HBR; apply Z.ltb_lt in HBR; lia.
all: uncond HS; srr_run_sh tfibtbl_rtG_ok HS; meq_acc SK0.
all: srr_branch_sh tfibtbl_rtG_ok HS.

1,3: exfalso; lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => rename Hbr into HBR end;
  clear - HBR R40 R34 bR1 bR2 dSB1 dSB2 dB1 dB2; zbranch HBR; apply Bool.negb_true_iff in HBR; apply Z.ltb_ge in HBR; lia.
all: uncond HS; srr_run_to_sh tfibtbl_rtG_ok HS 0x347c8; meq_acc SK0.
all: apply (st_ok_pin_regU _ _ _ 12%bv (SLit kBatchClass)) in HS.
all: try (intros X; discriminate).
all: try (pin_prep; change (zev (rho_of E0) (SLit kBatchClass) = zev (rho_of E0) AFhk.A2T);
  rewrite (A2_val0 (rho_of E0) SB b 24 (b - SB - 24 * 2 ^ 32) R34 R40);
  [reflexivity | lia | lia | lia | clear - dSB1; unfold SB in *; numconst; lia | clear - dSB1 dSB2 bR1 bR2; unfold SB in *; numconst; lia ]).
all: unpin HS; srr_run_to_sh tfibtbl_rtG_ok HS 0x34c14; meq_acc SK0.
all: lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
  apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
  split; [rewrite HshR at 1; reflexivity|] end.
all: split; [ reg_atom HS (2%bv : bv 5) 2%nat |].
all: split; [ rreg HS (1%bv : bv 5) Q; rewrite Q; reflexivity |].
all: split;
[ intros r Hr; cbn [DMrec.RZ.SREGS In] in Hr;
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
  [ reg_atom HS (3%bv : bv 5) 3%nat
  | rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; exact Htp
  | rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; lia
  | rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity
  | rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; reflexivity
  | rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; reflexivity
  | rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; reflexivity
  | reg_atom HS (26%bv : bv 5) 26%nat
  | reg_atom HS (27%bv : bv 5) 27%nat ]
|].
all: split; [ rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqT; unfold w64; rewrite Zbv_add_unsigned; reflexivity |].
all: split; [ rreg HS (11%bv : bv 5) Q; rewrite Q; first [reflexivity | destruct Hregs as (_ & R9 & _); rewrite R9; reflexivity] |].
all: split; [ rreg HS (12%bv : bv 5) Q; rewrite Q; reflexivity |].
all: split; [ rreg HS (13%bv : bv 5) Q; rewrite Q; first [rewrite EqB; reflexivity | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia] |].
all: split; [ exact MQ |].
all: split;
[ intros a Ha; eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS);
  [ reflexivity
  | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold DMrec.RZ.WIN in Ha; unfold DMrec.RZ.YFRAME in *; clear - Ha; unfold sp0 in *; lia
  | off_by ltac:(unfold DMrec.RZ.WIN in Ha; unfold DMrec.RZ.YFRAME in *; clear - Ha Usp dS1 dS2; unfold sp0 in *; numconst; lia) ]
|].
all: cbv zeta.
all: split; [ memvo HS 0%nat 112 |].
all: try (rewrite BV2; unfold DMrec.RZ.YFRAME; unfold sp0; lia).
all: try (cbn [sv_denot]; rewrite EqSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia).
all: try (clear - dSZ; lia).
all: split; [ memvo HS 0%nat 120 |].
all: try (rewrite BV2; unfold DMrec.RZ.YFRAME; unfold sp0; lia).
all: try (cbn [sv_denot]; rewrite EqNX; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia).
all: try (clear - dNX; numconst; lia).
all: split; [ memvo HS 0%nat 128 |].
all: try (rewrite BV2; unfold DMrec.RZ.YFRAME; unfold sp0; lia).
all: try (first [reflexivity | cbn [sv_denot]; rewrite EqLZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold DMrec.RZ.LZn; rewrite LZv; lia | unfold DMrec.RZ.LZn; rewrite LZv; reflexivity]).
all: try (unfold DMrec.RZ.LZn; rewrite LZv; clear - dLZ; numconst; lia).
all: memvo HS 0%nat 136.
all: try (rewrite BV2; unfold DMrec.RZ.YFRAME; lia).
all: try (apply denot_by_zev; [ reflexivity | clear; unfold zcanon, M64; lia
  | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r, ?R47, ?R42; clear - dBB dQB; unfold zcanon, M64; numconst; lia ]).
all: try (clear; unfold zcanon, M64; lia).
Qed.
End WK.
End c.

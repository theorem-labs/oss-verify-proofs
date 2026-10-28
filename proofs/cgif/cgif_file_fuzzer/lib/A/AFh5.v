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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFgq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD in *.
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (u nn : Z) (q : qcache) (cnt coff jst : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x357d0) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 u nn q cnt coff jst.
Local Notation QSZv := (AFgq.QSZv q).
Local Notation QFv := (AFgq.QFv ly q).
Local Notation QLv := (AFgq.QLv ly q).
Local Notation QBv := (AFgq.QBv q).
Local Notation CPv := (AFgq.CPv coff).
Local Notation NBv := (AFgq.NBv ly coff).
Local Notation CSLv := (AFgq.CSLv ly cnt).
Local Notation XW := (AFgq.XW ly u nn q cnt coff jst).
Local Notation E0 := (AFgq.E0 ly regs0 u nn q cnt coff jst).
Local Notation Er := (AFgq.Er ly regs0 u nn q cnt coff jst).
Local Notation E2 := (AFgq.E2 ly regs0 u nn q cnt coff jst).
Local Notation E1 := (AFgq.E1 ly regs0 u nn q cnt coff jst).
Local Notation E8 := (AFgq.E8 ly regs0 u nn q cnt coff jst).
Local Notation EqT := (AFgq.EqT ly regs0 u nn q cnt coff jst).
Local Notation EqSB := (AFgq.EqSB ly regs0 u nn q cnt coff jst).
Local Notation EqU := (AFgq.EqU ly regs0 u nn q cnt coff jst).
Local Notation EqN := (AFgq.EqN ly regs0 u nn q cnt coff jst).
Local Notation EqQSZ := (AFgq.EqQSZ ly regs0 u nn q cnt coff jst).
Local Notation EqQF := (AFgq.EqQF ly regs0 u nn q cnt coff jst).
Local Notation EqQL := (AFgq.EqQL ly regs0 u nn q cnt coff jst).
Local Notation EqQB := (AFgq.EqQB ly regs0 u nn q cnt coff jst).
Local Notation EqCNT := (AFgq.EqCNT ly regs0 u nn q cnt coff jst).
Local Notation EqCP := (AFgq.EqCP ly regs0 u nn q cnt coff jst).
Local Notation EqJST := (AFgq.EqJST ly regs0 u nn q cnt coff jst).
Local Notation EqNB := (AFgq.EqNB ly regs0 u nn q cnt coff jst).
Local Notation EqCSL := (AFgq.EqCSL ly regs0 u nn q cnt coff jst).
Local Notation R_ROOT := AFgq.R_ROOT.
Local Notation R_CNT := AFgq.R_CNT.
Local Notation R_JST := AFgq.R_JST.
Local Notation REG0 := AFgq.REG0.
Local Notation R_LAST := AFgq.R_LAST.
Local Notation R_CSZ := AFgq.R_CSZ.
Local Notation R_SLOT := AFgq.R_SLOT.
Local Notation R_NB := AFgq.R_NB.
Local Notation FFQ := AFgq.FFQ.
Local Notation SR0 := AFgq.SR0.
Local Notation SS0 := AFgq.SS0.
Local Notation LYB := (AFgq.LYB W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation derived_ranges := (AFgq.derived_ranges W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation hit_ranges := (AFgq.hit_ranges W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WINT := (AFgq.WINT ly).
Local Notation WINA := (AFgq.WINA ly q cnt coff).
Local Notation WIN := (AFgq.WIN ly regs0 q cnt coff).
Local Notation win_sub := AFgq.win_sub.
Local Notation win_sub_sound := (AFgq.win_sub_sound ly regs0).
Local Notation WSK0 := AFgq.WSK0.
Local Notation WSKN := AFgq.WSKN.
Local Notation WSKL := AFgq.WSKL.
Local Notation WSKNL := AFgq.WSKNL.
Local Notation sk_ok := (AFgq.sk_ok ly regs0 q cnt coff).
Local Notation WSK0_ok := (AFgq.WSK0_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WSKN_ok := (AFgq.WSKN_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WSKL_ok := (AFgq.WSKL_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WSKNL_ok := (AFgq.WSKNL_ok W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation windows_WIN := (AFgq.windows_WIN ly regs0 q cnt coff).
Local Notation WIN_zone := (AFgq.WIN_zone W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation WIN_off := (AFgq.WIN_off W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation MEQ := (AFgq.MEQ ly regs0 mem0 q cnt coff).
Local Notation MEQ_frame := (AFgq.MEQ_frame ly regs0 mem0 q cnt coff).
Local Notation MEQ_0 := (AFgq.MEQ_0 ly regs0 mem0 q cnt coff).
Local Notation WIN0 := (AFgq.WIN0 ly regs0).
Local Notation WIN0_WIN := (AFgq.WIN0_WIN ly regs0 q cnt coff).
Local Notation sk_ok0 := (AFgq.sk_ok0 ly regs0).
Local Notation WSK0_ok0 := (AFgq.WSK0_ok0 W ly regs0 mem0 u nn q cnt coff jst FH).
Local Notation MEQ0 := (AFgq.MEQ0 ly regs0 mem0).
Local Notation MEQ0_frame := (AFgq.MEQ0_frame ly regs0 mem0).
Local Notation MEQ0_0 := (AFgq.MEQ0_0 ly regs0 mem0).
Local Notation WINS := (AFgq.WINS regs0).
Local Notation WINS_WIN0 := (AFgq.WINS_WIN0 ly regs0).
Local Notation WSKS := AFgq.WSKS.
Local Notation sk_okS := (AFgq.sk_okS regs0).
Local Notation WSKS_okS := (AFgq.WSKS_okS ly regs0 u nn q cnt coff jst).
Local Notation MEQS := (AFgq.MEQS regs0 mem0).
Local Notation MEQS_frame := (AFgq.MEQS_frame ly regs0 mem0).
Local Notation MEQS_0 := (AFgq.MEQS_0 regs0 mem0).
Local Notation MEQS_MEQ0 := (AFgq.MEQS_MEQ0 ly regs0 mem0).
Local Notation MEQ0_MEQ := (AFgq.MEQ0_MEQ ly regs0 mem0 q cnt coff).
Local Notation all_disjoint_of_forall := AFgq.all_disjoint_of_forall.
Local Notation kept_of_frame := (AFgq.kept_of_frame W ly regs0).
Local Notation aview_eq_mbyte := AFgq.aview_eq_mbyte.
Local Notation kept_of_aview := (AFgq.kept_of_aview W).
Local Notation SKEL_TAIL := AFgq.SKEL_TAIL.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hra4096 Hsp Hsp_al Hpres Hu IMG Hnn Hq Hnb Hlast Hcnt Hhit Hjst SEED].
Local Notation off_T := (AFgq.off_T W ly regs0 mem0 u nn q cnt coff jst FH).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac meq0_acc SKOK :=
match goal with
| M : MEQ0 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ0_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Definition R_LAST0 : YP09.region := YP09.mkRegion (Some 38%nat) 0 24 0 0 [YP09.mkChunk 16 (CVal 8 (SLit kBatchSlots))].
Definition at_CALLR (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs1 mem1 mat,
c' = mkCfg (mkst regs1 (w64 0x36104) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs1 1 = w64 0x35924 /\ getr regs1 2 = w64 (sp0 - 64) /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 10 = w64 (T + t_cache) /\ getr regs1 11 = w64 (T + t_cache + 1920) /\ getr regs1 12 = w64 0xa2998 /\ getr regs1 13 = w64 24 /\
getr regs1 8 = w64 (T + t_cache + 1920) /\ getr regs1 9 = w64 (T + t_cache) /\ getr regs1 18 = w64 (u - 16) /\ getr regs1 19 = w64 (T + t_qc) /\
getr regs1 20 = getr regs0 12 /\ getr regs1 21 = w64 nn /\
(forall r : bv 5, In r [22; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs0 r) /\
MEQ0 mem1 /\
(forall a, sp0 - 64 <= a < sp0 -> apresent (w_H W) mem1 a) /\
let m := mrestrict (w_H W) mem1 in
val_mem tfibsegs m (T + t_qc) 8 QSZv /\ val_mem tfibsegs m (T + t_qc + 8) 8 QFv /\ val_mem tfibsegs m (T + t_qc + 16) 8 QLv /\ val_mem tfibsegs m (T + t_qc + 24) 8 QBv /\
val_mem tfibsegs m (T + t_cache + 1920) 4 cnt /\ val_mem tfibsegs m (T + t_cache_stats + 16) 8 jst /\
val_mem tfibsegs m (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\ val_mem tfibsegs m (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\ val_mem tfibsegs m (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem tfibsegs m (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\ val_mem tfibsegs m (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs m (sp0 - 56) 8 (bv_unsigned (getr regs0 21)).
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac reg_atom HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ reflexivity | f_equal; numconst; zlia ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac frame_val HS i j k r BV2 := memv HS i j; [rewrite BV2; zlia | cbn [sv_denot]; rewrite (Er k r eq_refl); f_equal; zlia | apply u64_range].
Lemma segR1 : cnt = 0 -> SRr tfibsegs W cfg0 at_CALLR.
Proof.
intros Hc. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok0 E0 HE0) as SK0.
assert (R36 : rho_of E0 36%nat = QSZv) by (unfold rho_of; rewrite EqQSZ; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R40 : rho_of E0 40%nat = cnt) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (BV32 : bv_unsigned (ew E0 32) = T) by exact R32.
assert (BV38 : bv_unsigned (ew E0 38) = QLv) by (rewrite EqQL; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (VMQ : forall m a (n : nat) v, MEQ0 m -> (forall i, 0 <= i < Z.of_nat n -> ~ WIN0 (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) m) a n v).
{ intros m a n v HM Hn Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(zlia)) as [N1 N2].
apply HM. rewrite unsigned_lit_small by exact N2. exact N1. }
assert (PRQ : forall m a, MEQ0 m -> ~ WIN0 a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem0 a -> apresent (w_H W) m a).
{ intros m a HM Hn Ha Hp. apply (apresent_same (w_H W) mem0); [|exact Hp]. apply HM. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (NW0 : forall a, ~ (sp0 - 64 <= a < sp0) -> ~ (T + t_qc <= a < T + t_qc + 32) -> ~ (T + t_cache + 1920 <= a < T + t_cache + 1924) ->
~ (T + t_cache_stats + 16 <= a < T + t_cache_stats + 24) -> ~ WIN0 a).
{ intros a N0 N1 N2 N3 [X|X]; [exact (N0 X)|]. unfold AFgq.WINT in X. clear - X N1 N2 N3. zlia. }
srr_run_sh tfibtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfibtbl_rtF_ok HS.
{
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. rewrite branch_eq_U in Hc1. apply Z.eqb_neq in Hc1. revert Hc1. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R40. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). clear - Hc. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x36104. meq0_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR. cbn [ss_pc] in HshR.
apply SRr_ret. split; [reflexivity|].
eexists (ms_regs msR), (ms_mem msR), _.
split. { rewrite HshR at 1. reflexivity. }
split. { reg_lit HS (1%bv : bv 5). }
split. { rreg HS (2%bv : bv 5) Q2. rewrite Q2. cbn [sv_denot]. rewrite E2. unfold w64. f_equal; unfold sp0; zlia. }
split. { reg_entry HS (3%bv : bv 5) 3%nat. }
split. { rreg HS (4%bv : bv 5) Q4. rewrite Q4, Htp. reflexivity. }
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
[reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat]. }
split. { exact MQ. }
split. { intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(revert Ha; numconst; intros Ha; zlia) ]. }
cbv zeta.
split. { memv HS 1%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 1%nat 1%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 1%nat 2%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQL; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 1%nat 3%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 2%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 3%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqJST; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { frame_val HS 0%nat 6%nat 1%nat (1%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 5%nat 8%nat (8%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 4%nat 9%nat (9%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 3%nat 18%nat (18%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 2%nat 19%nat (19%bv : bv 5) BV2. }
split. { frame_val HS 0%nat 1%nat 20%nat (20%bv : bv 5) BV2. }
frame_val HS 0%nat 0%nat 21%nat (21%bv : bv 5) BV2. }
{
assert (HQF : qc_list q <> []).
{ rewrite branch_eq_U in Hc0. apply Z.eqb_neq in Hc0. revert Hc0. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R36. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). unfold AFgq.QSZv. destruct (qc_list q); cbn [length]; [zlia | intros _; discriminate]. }
destruct (rev (qc_list q)) as [|lastb initr] eqn:HR0; [exfalso; apply HQF; rewrite <- (rev_involutive (qc_list q)), HR0; reflexivity|].
destruct (Hlast lastb initr eq_refl) as (L1 & L2 & L3 & L4 & L5).
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
apply (st_ok_add_region _ _ _ R_LAST0) in HS;
[ | reflexivity
| unfold R_LAST0, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV38;
split; [clear - L1 LB; numconst; zlia|]; split; [clear - L1 L2 LB; numconst; zlia|];
split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [reflexivity | unfold kBatchSlots; cbn; zlia | cbn; zlia |];
apply (VMQ _ _ 8%nat); [exact MQ | intros i Hi; split; [apply NW0; clear - Hi L1 L2 LB Hlo Hhi; numconst; zlia | clear - Hi L1 L2 LB; numconst; zlia] | exact L4]
| unfold R_LAST0; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV38, ?BV2;
clear - LB DR L1 L2 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. rewrite branch_eq_U in Hc1. apply Z.eqb_neq in Hc1. revert Hc1. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R40. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). clear - Hc. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x36104. meq0_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR. cbn [ss_pc] in HshR.
apply SRr_ret. split; [reflexivity|].
eexists (ms_regs msR), (ms_mem msR), _.
split. { rewrite HshR at 1. reflexivity. }
split. { reg_lit HS (1%bv : bv 5). }
split. { rreg HS (2%bv : bv 5) Q2. rewrite Q2. cbn [sv_denot]. rewrite E2. unfold w64. f_equal; unfold sp0; zlia. }
split. { reg_entry HS (3%bv : bv 5) 3%nat. }
split. { rreg HS (4%bv : bv 5) Q4. rewrite Q4, Htp. reflexivity. }
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
[reg_entry HS (22%bv : bv 5) 22%nat | reg_entry HS (23%bv : bv 5) 23%nat | reg_entry HS (24%bv : bv 5) 24%nat
| reg_entry HS (25%bv : bv 5) 25%nat | reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat]. }
split. { exact MQ. }
split. { intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(revert Ha; numconst; intros Ha; zlia) ]. }
cbv zeta.
split. { memv HS 2%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 2%nat 1%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 2%nat 2%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQL; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 2%nat 3%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 3%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 4%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqJST; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
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

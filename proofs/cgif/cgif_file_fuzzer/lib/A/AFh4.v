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
Local Notation win_sub_sound := AFgq.win_sub_sound.
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
Local Notation MEQ0_MEQ := (AFgq.MEQ0_MEQ ly regs0 mem0 q cnt coff).
Local Notation all_disjoint_of_forall := AFgq.all_disjoint_of_forall.
Local Notation kept_of_frame := (AFgq.kept_of_frame W).
Local Notation aview_eq_mbyte := AFgq.aview_eq_mbyte.
Local Notation kept_of_aview := (AFgq.kept_of_aview W).
Local Notation SKEL_TAIL := AFgq.SKEL_TAIL.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Htp Hra Hra4096 Hsp Hsp_al Hpres Hu IMG Hnn Hq Hnb Hlast Hcnt Hhit Hjst SEED].
Local Notation off_T := (AFgq.off_T W ly regs0 mem0 u nn q cnt coff jst FH).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. apply Z.mod_small. exact Hv.
Qed.
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
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
Definition QF' : Z := match qc_list q with [] => NBv | _ => QFv end.
Definition at_RETQ (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
MEQ mem' /\
(forall a, WIN a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (T + t_qc) 8 (QSZv + 1) /\ val_mem tfibsegs m (T + t_qc + 8) 8 QF' /\
val_mem tfibsegs m (T + t_qc + 16) 8 NBv /\ val_mem tfibsegs m (T + t_qc + 24) 8 (QBv + nn + kBatchBytes) /\
val_mem tfibsegs m (T + t_cache + 1920) 4 (cnt - 1) /\
val_mem tfibsegs m NBv 8 0 /\ val_mem tfibsegs m (NBv + 8) 8 (nn + kBatchBytes) /\ val_mem tfibsegs m (NBv + 16) 8 1 /\ val_mem tfibsegs m (NBv + 24) 8 (u - 16) /\
(forall lastb initr, rev (qc_list q) = lastb :: initr -> val_mem tfibsegs m QLv 8 NBv).
Ltac finish_post HS MQ HARM :=
split; [reflexivity|];
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msR) =>
lazymatch goal with |- exists regs' mem' mat, {| cfg_ms := _; cfg_model := with_vm_backing _ ?matx _ |} = _ /\ _ =>
exists (ms_regs msR), (ms_mem msR), matx end end;
idtac "FINISH-REACHED".
Lemma segQH : 1 <= cnt -> SRr tfibsegs W cfg0 at_RETQ.
Proof.
intros Hc. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB. pose proof derived_ranges as DR.
pose proof (hit_ranges Hc) as HR. destruct (Hhit Hc) as (Vcsz & Vslot & C1 & C2 & C3 & B1 & B2 & B3 & Bpres & BL).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ0_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok0 E0 HE0) as SK0. pose proof (WSKN_ok E0 HE0 Hc) as SKN.
assert (R36 : rho_of E0 36%nat = QSZv) by (unfold rho_of; rewrite EqQSZ; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R40 : rho_of E0 40%nat = cnt) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R33 : rho_of E0 33%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R41 : rho_of E0 41%nat = CPv) by (unfold rho_of; rewrite EqCP; unfold w64; apply unsigned_lit_small; clear - HR; zlia).
assert (R43 : rho_of E0 43%nat = NBv) by (unfold rho_of; rewrite EqNB; unfold w64; apply unsigned_lit_small; clear - HR; numconst; zlia).
assert (R44 : rho_of E0 44%nat = CSLv) by (unfold rho_of; rewrite EqCSL; unfold w64; apply unsigned_lit_small; clear - HR LB; numconst; zlia).
assert (BV32 : bv_unsigned (ew E0 32) = T) by exact R32.
assert (BV38 : bv_unsigned (ew E0 38) = QLv) by (rewrite EqQL; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV43 : bv_unsigned (ew E0 43) = NBv) by exact R43.
assert (BV44 : bv_unsigned (ew E0 44) = CSLv) by exact R44.
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (QLF : forall lastb initr, rev (qc_list q) = lastb :: initr ->
ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\ (NBv + kBatchBytes <= QLv \/ QLv + kBatchBytes <= NBv)).
{ intros lb ini R. destruct (Hlast lb ini R) as (L1 & L2 & L3 & _ & _). pose proof (BL lb ini R). tauto. }
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
assert (HQE : qc_list q = []).
{ rewrite branch_eq_U in Hc0. apply Z.eqb_eq in Hc0. revert Hc0. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R36. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). unfold AFgq.QSZv. destruct (qc_list q); cbn [length]; [reflexivity | zlia]. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq0_acc SK0.
srr_branch_sh tfibtbl_rtF_ok HS.
{ exfalso. rewrite branch_eq_U in Hc1. apply Z.eqb_eq in Hc1. revert Hc1. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R40. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). clear - Hc. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms2 end.
apply (st_ok_add_region _ _ _ R_CSZ) in HS;
[ | reflexivity
| unfold AFgq.R_CSZ, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV32;
split; [clear - LB; numconst; zlia|]; split; [clear - LB; numconst; zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia |];
apply (VMQ _ _ 8%nat); [exact MQ | intros i Hi; split; [apply NW0; clear - Hi LB Hlo Hhi; numconst; zlia | clear - Hi LB; numconst; zlia]
| replace (T + (t_cache + 1928)) with (T + t_cache + 1928) by zlia; exact Vcsz]
| unfold AFgq.R_CSZ, AFgq.R_SLOT, AFgq.R_NB, AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV2;
clear - LB DR HR Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | reflexivity
| unfold AFgq.R_SLOT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV44;
split; [clear - HR LB; numconst; zlia|]; split; [clear - HR LB; numconst; zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqCP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - HR; cbn; zlia | cbn; zlia |];
apply (VMQ _ _ 4%nat); [exact MQ | intros i Hi; split; [apply NW0; clear - Hi HR LB Hlo Hhi; numconst; zlia | clear - Hi HR LB; numconst; zlia]
| rewrite !Z.add_0_r; exact Vslot]
| unfold AFgq.R_CSZ, AFgq.R_SLOT, AFgq.R_NB, AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV44, ?BV2;
clear - LB DR HR Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_NB) in HS;
[ | reflexivity
| unfold AFgq.R_NB, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV43;
split; [clear - HR; numconst; zlia|]; split; [clear - HR; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - HR Ho; numconst; zlia) | apply PRQ; [exact MQ | apply NW0; clear - Ho HR LB Hlo Hhi; numconst; zlia | clear - Ho HR; numconst; zlia | apply Bpres; zlia]] | apply Forall_nil]
| unfold AFgq.R_CSZ, AFgq.R_SLOT, AFgq.R_NB, AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV43, ?BV44, ?BV2;
clear - LB DR HR Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply MEQ0_MEQ in MQ.
srr_run_to_sh tfibtbl_rtF_ok HS 0x35824. meq_acc SKN.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 44%nat (-1936))) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R44, ?R32, ?R40, ?Z.add_0_r; land_lits;
change (Z.land (zcanon 32) 63) with 32; change (Z.land (zcanon 30) 63) with 30;
rewrite (zcanon_id cnt) by (clear - DR; unfold M64; zlia);
rewrite !Z.shiftl_mul_pow2 by zlia; rewrite (zcanon_id (cnt * 2 ^ 32)) by (clear - DR; unfold M64; zlia);
let c := eval vm_compute in (zcanon (-4294967296)) in change (zcanon (-4294967296)) with c;
replace (zcanon (cnt * 2 ^ 32 + 18446744069414584320)) with ((cnt - 1) * 2 ^ 32) by (unfold zcanon, M64; apply Z.mod_unique with (q := 1); clear - DR Hc; zlia);
rewrite !Z.shiftr_div_pow2 by zlia;
replace ((cnt - 1) * 2 ^ 32 / 2 ^ 30) with (4 * (cnt - 1)) by (apply Z.div_unique with (r := 0); zlia);
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HR)))))) as ECSL; clear - DR HR LB Hc ECSL; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x35854. meq_acc SKN.
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 43%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R43, ?R33, ?R41, ?Z.add_0_r; land_lits;
change (Z.land (zcanon 4) 63) with 4; rewrite (zcanon_id CPv) by (clear - HR; unfold M64; zlia);
rewrite !Z.shiftl_mul_pow2 by zlia; change (2 ^ 4) with 16;
pose proof (proj1 (proj2 (proj2 (proj2 HR)))) as ENB; clear - HR LB ENB; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq_acc SKN.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { intros r Hr. cbn [CALLEE_SAVED In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let R := fresh "RR" in rreg HS r R; rewrite R end;
first [ apply Er; reflexivity | rewrite Htp; reflexivity ]). }
split. { exact MQ. }
split. { intros a Ha. unfold AFgq.WIN, AFgq.WINT, AFgq.WINA in Ha. rewrite HQE in Ha.
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[[_ Ha]|[Hne _]]]]; [ | | | | | exfalso; exact (Hne eq_refl) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 6 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV43; clear - Ha; zlia | off_by ltac:(clear - Ha HR; numconst; zlia) ]. }
cbv zeta. unfold QF'. rewrite HQE.
assert (R35 : rho_of E0 35%nat = nn) by (unfold rho_of; rewrite EqN; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R39 : rho_of E0 39%nat = QBv) by (unfold rho_of; rewrite EqQB; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (Q0 : QSZv = 0) by (unfold AFgq.QSZv; rewrite HQE; reflexivity).
split. { memv HS 4%nat 2%nat; [rewrite BV32; numconst; zlia | rewrite Q0; reflexivity | rewrite Q0; zlia]. }
split. { memv HS 4%nat 3%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqNB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - HR; numconst; zlia]. }
split. { memv HS 4%nat 1%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqNB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - HR; numconst; zlia]. }
split. { memv HS 4%nat 0%nat; [rewrite BV32; numconst; zlia
| apply denot_by_zev; [reflexivity | clear - DR; numconst; zlia | cbn [zev zalu_raw]; unfold zalu_raw; rewrite R35, R39; clear - DR; numconst; zcanon_simp; zlia]
| clear - DR; numconst; zlia]. }
split. { memv HS 5%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR Hc; zlia]. }
split. { memv HS 0%nat 3%nat; [rewrite BV43; zlia | reflexivity | zlia]. }
split. { memv HS 0%nat 2%nat; [rewrite BV43; zlia | cbn [sv_denot]; rewrite EqN; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold kBatchBytes; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 0%nat 1%nat; [rewrite BV43; zlia | reflexivity | zlia]. }
split. { memv HS 0%nat 0%nat; [rewrite BV43; zlia | cbn [sv_denot]; rewrite EqU; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
intros lastb initr R. exfalso. rewrite ?HQE in R. cbn [rev app] in R. discriminate R. }
{
assert (HQF : qc_list q <> []).
{ rewrite branch_eq_U in Hc0. apply Z.eqb_neq in Hc0. revert Hc0. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R36. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). unfold AFgq.QSZv. destruct (qc_list q); cbn [length]; [zlia | intros _; discriminate]. }
destruct (rev (qc_list q)) as [|lastb initr] eqn:HR0; [exfalso; apply HQF; rewrite <- (rev_involutive (qc_list q)), HR0; reflexivity|].
destruct (Hlast lastb initr eq_refl) as (L1 & L2 & L3 & L4 & L5). destruct (QLF lastb initr eq_refl) as (_ & _ & _ & LNB).
pose proof Hnb as NBF. unfold need_new_batch in NBF. rewrite HR0 in NBF. apply Z.eqb_eq in NBF.
pose proof (WSKNL_ok E0 HE0 Hc HQF) as SKNL.
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms1 end.
apply (st_ok_add_region _ _ _ R_LAST) in HS;
[ | reflexivity
| unfold AFgq.R_LAST, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV38;
split; [clear - L1 LB; numconst; zlia|]; split; [clear - L1 L2 LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - L1 L2 LB Ho; numconst; zlia) | apply PRQ; [exact MQ | apply NW0; clear - Ho L1 L2 LB Hlo Hhi; numconst; zlia | clear - Ho L1 L2 LB; numconst; zlia | apply L5; zlia]]|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [reflexivity | unfold kBatchSlots; cbn; zlia | cbn; zlia |];
apply (VMQ _ _ 8%nat); [exact MQ | intros i Hi; split; [apply NW0; clear - Hi L1 L2 LB Hlo Hhi; numconst; zlia | clear - Hi L1 L2 LB; numconst; zlia] | exact L4]
| unfold AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV38, ?BV2;
clear - LB DR L1 L2 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms2' end.
apply (st_ok_add_region _ _ _ R_CSZ) in HS;
[ | reflexivity
| unfold AFgq.R_CSZ, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV32;
split; [clear - LB; numconst; zlia|]; split; [clear - LB; numconst; zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia |];
apply (VMQ _ _ 8%nat); [exact MQ | intros i Hi; split; [apply NW0; clear - Hi LB Hlo Hhi; numconst; zlia | clear - Hi LB; numconst; zlia]
| replace (T + (t_cache + 1928)) with (T + t_cache + 1928) by zlia; exact Vcsz]
| unfold AFgq.R_CSZ, AFgq.R_SLOT, AFgq.R_NB, AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV38, ?BV2;
clear - LB DR HR Hlo Hhi L1 L2 LNB; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | reflexivity
| unfold AFgq.R_SLOT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV44;
split; [clear - HR LB; numconst; zlia|]; split; [clear - HR LB; numconst; zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil];
eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqCP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - HR; cbn; zlia | cbn; zlia |];
apply (VMQ _ _ 4%nat); [exact MQ | intros i Hi; split; [apply NW0; clear - Hi HR LB Hlo Hhi; numconst; zlia | clear - Hi HR LB; numconst; zlia]
| rewrite !Z.add_0_r; exact Vslot]
| unfold AFgq.R_CSZ, AFgq.R_SLOT, AFgq.R_NB, AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV44, ?BV38, ?BV2;
clear - LB DR HR Hlo Hhi L1 L2 LNB; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_NB) in HS;
[ | reflexivity
| unfold AFgq.R_NB, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV43;
split; [clear - HR; numconst; zlia|]; split; [clear - HR; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - HR Ho; numconst; zlia) | apply PRQ; [exact MQ | apply NW0; clear - Ho HR LB Hlo Hhi; numconst; zlia | clear - Ho HR; numconst; zlia | apply Bpres; zlia]] | apply Forall_nil]
| unfold AFgq.R_CSZ, AFgq.R_SLOT, AFgq.R_NB, AFgq.R_LAST; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV43, ?BV44, ?BV38, ?BV2;
clear - LB DR HR Hlo Hhi L1 L2 LNB; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply MEQ0_MEQ in MQ.
srr_run_sh tfibtbl_rtF_ok HS. meq_acc SKNL.
srr_branch_sh tfibtbl_rtF_ok HS.
{ exfalso. rewrite branch_eq_U in Hc1. apply Z.eqb_eq in Hc1. revert Hc1. rewrite !U_zev by reflexivity. cbn [zev zalu_raw].
rewrite R40. rewrite ?zcanon_id by (clear - DR; unfold M64; zlia). clear - Hc. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x35824. meq_acc SKNL.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 44%nat (-1936))) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R44, ?R32, ?R40, ?Z.add_0_r; land_lits;
change (Z.land (zcanon 32) 63) with 32; change (Z.land (zcanon 30) 63) with 30;
rewrite (zcanon_id cnt) by (clear - DR; unfold M64; zlia);
rewrite !Z.shiftl_mul_pow2 by zlia; rewrite (zcanon_id (cnt * 2 ^ 32)) by (clear - DR; unfold M64; zlia);
let c := eval vm_compute in (zcanon (-4294967296)) in change (zcanon (-4294967296)) with c;
replace (zcanon (cnt * 2 ^ 32 + 18446744069414584320)) with ((cnt - 1) * 2 ^ 32) by (unfold zcanon, M64; apply Z.mod_unique with (q := 1); clear - DR Hc; zlia);
rewrite !Z.shiftr_div_pow2 by zlia;
replace ((cnt - 1) * 2 ^ 32 / 2 ^ 30) with (4 * (cnt - 1)) by (apply Z.div_unique with (r := 0); zlia);
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HR)))))) as ECSL; clear - DR HR LB Hc ECSL; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x35854. meq_acc SKNL.
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 43%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R43, ?R33, ?R41, ?Z.add_0_r; land_lits;
change (Z.land (zcanon 4) 63) with 4; rewrite (zcanon_id CPv) by (clear - HR; unfold M64; zlia);
rewrite !Z.shiftl_mul_pow2 by zlia; change (2 ^ 4) with 16;
pose proof (proj1 (proj2 (proj2 (proj2 HR)))) as ENB; clear - HR LB ENB; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq_acc SKNL.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { intros r Hr. cbn [CALLEE_SAVED In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
(lazymatch goal with |- getr _ ?r = _ => let R := fresh "RR" in rreg HS r R; rewrite R end;
first [ apply Er; reflexivity | rewrite Htp; reflexivity ]). }
split. { exact MQ. }
split. { intros a Ha. unfold AFgq.WIN, AFgq.WINT, AFgq.WINA in Ha.
destruct Ha as [Ha|[[Ha|[Ha|Ha]]|[[_ Ha]|[_ Ha]]]].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 6 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 7 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV43; clear - Ha; zlia | off_by ltac:(clear - Ha HR; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV38; clear - Ha; zlia | off_by ltac:(clear - Ha L1 L2 LB; numconst; zlia) ]. }
cbv zeta. unfold QF'. destruct (qc_list q) as [|b0 bt] eqn:HQL; [exfalso; exact (HQF eq_refl)|]. rewrite <- HQL in *. clear b0 bt HQL.
assert (R35 : rho_of E0 35%nat = nn) by (unfold rho_of; rewrite EqN; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R39 : rho_of E0 39%nat = QBv) by (unfold rho_of; rewrite EqQB; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
split. { memv HS 5%nat 2%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; zlia]. }
split. { memv HS 5%nat 3%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqQF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 5%nat 1%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqNB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - HR; numconst; zlia]. }
split. { memv HS 5%nat 0%nat; [rewrite BV32; numconst; zlia
| apply denot_by_zev; [reflexivity | clear - DR; numconst; zlia | cbn [zev zalu_raw]; unfold zalu_raw; rewrite R35, R39; clear - DR; numconst; zcanon_simp; zlia]
| clear - DR; numconst; zlia]. }
split. { memv HS 6%nat 0%nat; [rewrite BV32; numconst; zlia | cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR Hc; zlia]. }
split. { memv HS 0%nat 3%nat; [rewrite BV43; zlia | reflexivity | zlia]. }
split. { memv HS 0%nat 2%nat; [rewrite BV43; zlia | cbn [sv_denot]; rewrite EqN; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold kBatchBytes; zlia | clear - DR; numconst; zlia]. }
split. { memv HS 0%nat 1%nat; [rewrite BV43; zlia | reflexivity | zlia]. }
split. { memv HS 0%nat 0%nat; [rewrite BV43; zlia | cbn [sv_denot]; rewrite EqU; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - DR; numconst; zlia]. }
intros lastb' initr' _. memv HS 3%nat 0%nat; [rewrite BV38; zlia | cbn [sv_denot]; rewrite EqNB; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - HR; numconst; zlia]. }
Qed.
End WK.
End b.

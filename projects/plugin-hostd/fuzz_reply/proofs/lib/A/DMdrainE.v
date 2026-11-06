(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainE.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 1e5e2845a724) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the SEED of Quarantine::Drain's entry shell (YFgj.v, the walk at
   0x337ec), i.e. YFgj.free_hyps (YFgj.v:105-120) in full, from the facts DMiface.qview gives at Drain's entry
   (DMiface.v:75-107: the mutex bytes, both caches' headers, the batch cells, the two Quarantine constants, the
   thread header's presence) together with DMspec.drain_pre_cf's register and stack clauses and the two cache
   byte bounds of QB (CfF2b's QB_cf).  With it DMseg_dme.segDEm / DMseg_dmn.segDNm apply at the shared instance.
   rule 24: no function proved (kind: the seed of segments already walked, DMseg_dme.segDEm / DMseg_dmn.segDNm;
   the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle
   QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   The byte bounds are the released shell's (YFgj.v:114-115: the global cache at most 2 ^ 30, the thread cache at
   most 2 ^ 29).  They hold at the shared instance because Put enqueues no block above max_size = 2 ^ 28 (the
   test at 0x35f24) and the drain empties the thread cache, so QB_cf carries
   `qc_bytes (st_qthread X) <= kQuarantineCacheMax + kBatchBytes + NMAXD` and
   `qc_bytes (st_qglobal X) <= kQuarantineMax` (integrator 00:3xZ, a Theorem Labs lane's arithmetic and mine).  They
   enter here as the two hypotheses [HTB] and [HGB], nothing wider.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFff AFev AB13 AFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte).
Variables (gq tq : qcache).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m := mrestrict (w_H W) mem0.
Local Notation GSZv := (AFgj.GSZv gq).
Local Notation GFv := (AFgj.GFv ly gq).
Local Notation GLv := (AFgj.GLv ly gq).
Local Notation GBv := (AFgj.GBv gq).
Local Notation TSZv := (AFgj.TSZv tq).
Local Notation TFv := (AFgj.TFv ly tq).
Local Notation TLv := (AFgj.TLv ly tq).
Local Notation TBv := (AFgj.TBv tq).

(* the layout, as DMdeq.LYB derives it from layout_ok and img_cover *)
Hypothesis HLY : layout_ok ly.
Hypothesis HIMG : img_cover ly.
Hypothesis HT : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\ T mod 4096 = 0.
(* the thread object against the stack, and the stack in high memory (layout_ok's lo_disj / lo_top) *)
Hypothesis HTstk : T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T.
Hypothesis Hstklo : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
(* the thread object lies in one of the three application zones, all off the image window (YF0x.zone3; DMdrainG1
   derives it from layout_ok and img_cover by YF0x.zone3_intro) *)
Hypothesis HTz : zone3 T kThreadObjSize.
Hypothesis HSB : kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ SB mod 65536 = 0.
(* drain_pre_cf's registers and stack (DMspec.v:95-99) *)
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis Hsp_al : sp0 mod 16 = 0.
Hypothesis Hpres : forall a, sp0 - DSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hstk : kHighMemBeg + DSTACK <= sp0 /\ sp0 <= kHighMemEnd.
Hypothesis Ha0 : getr regs0 10 = w64 A_QUAR.
Hypothesis Ha1 : getr regs0 11 = w64 (T + t_qc).
Hypothesis Ha2 : getr regs0 12 = w64 (T + t_cache).
(* the two cache byte bounds (QB_cf) and the counts *)
Hypothesis HGB : 0 <= GBv <= 2 ^ 30.
Hypothesis HTB : kQuarantineCacheMax < TBv <= 2 ^ 29.
Hypothesis HGcnt : 0 <= GSZv < 2 ^ 40.
Hypothesis HTcnt : 1 <= TSZv < 2 ^ 40.
(* the batch addresses of the two caches (qview's geometry) *)
Hypothesis HGF : 0 <= GFv < ASAN_CEIL /\ GFv mod 8192 = 0.
Hypothesis HGL : 0 <= GLv < ASAN_CEIL /\ GLv mod 8192 = 0.
Hypothesis HTF : 0 <= TFv < ASAN_CEIL /\ TFv mod 8192 = 0.
Hypothesis HTL : 0 <= TLv < ASAN_CEIL /\ TLv mod 8192 = 0.
(* qview's cells: the mutex word, both headers, the two constants *)
Hypothesis VQW : val_mem tfibsegs m (A_QUAR + 152) 4 0.
Hypothesis VQG : val_mem tfibsegs m (A_QUAR + 160) 8 GSZv /\ val_mem tfibsegs m (A_QUAR + 168) 8 GFv /\
  val_mem tfibsegs m (A_QUAR + 176) 8 GLv /\ val_mem tfibsegs m (A_QUAR + 184) 8 GBv.
Hypothesis VQT : val_mem tfibsegs m (T + t_qc) 8 TSZv /\ val_mem tfibsegs m (T + t_qc + 8) 8 TFv /\
  val_mem tfibsegs m (T + t_qc + 16) 8 TLv /\ val_mem tfibsegs m (T + t_qc + 24) 8 TBv.
Hypothesis VMAX : val_mem tfibsegs m (A_QUAR + 64) 8 kQuarantineMax.
Hypothesis VMIN : val_mem tfibsegs m (A_QUAR + 72) 8 kQuarantineMin.
Hypothesis Hhpres : forall a, T + t_qc <= a < T + t_qc + 32 -> apresent (w_H W) mem0 a.
(* the global list's last batch (YFgj.fh_glast) *)
Hypothesis Hglast : forall lastb initr, rev (qc_list gq) = lastb :: initr ->
  ly_prim ly <= GLv /\ GLv + kBatchBytes <= SB + kSpaceSize /\ GLv mod 8192 = 0 /\
  val_mem tfibsegs m GLv 8 0 /\ (forall a, GLv <= a < GLv + 8 -> apresent (w_H W) mem0 a).

Local Notation E0 := (AFgj.E0 ly regs0 gq tq).
Lemma E0r (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (AFgj.Er ly regs0 gq tq k r Hk). Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Lemma chunk_atom1 : forall base a (w : BinNums.N) k0 x, ew E0 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m base (YP09.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
(* writability of a word the view shows, off the image (YFev.val_mem_writable, YFev.v:215-216) *)
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m o.
Proof. intros a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64.
Proof. unfold sp0. apply u64_range. Qed.

Lemma REG_ok : Forall (region_ok tfibsegs E0 m) AFgj.REG0.
Proof.
pose proof Usp as U. destruct Hstk as [S1 S2]. destruct HT as (T1 & T2 & T3). destruct HSB as (B1 & B2 & B3).
destruct VQG as (G0 & G1 & G2 & G3). destruct VQT as (Q0 & Q1 & Q2 & Q3).
destruct HGF as [F1 F2]. destruct HGL as [L1 L2]. destruct HTF as [N1 N2]. destruct HTL as [M1 M2].
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DSTACK, kThreadObjSize in *.
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0r 2 2%bv eq_refl); reflexivity).
assert (BVT : bv_unsigned (ew E0 32) = T) by (rewrite AFgj.EqT; unfold w64; apply unsigned_lit_small; lia).
unfold AFgj.REG0, AFgj.R_QW, AFgj.R_QG, AFgj.R_QT.
apply Forall_cons.
{ reg_intro. rewrite BV2. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; lia|].
  apply Hpres. unfold DSTACK. lia. }
apply Forall_cons.
{ reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split.
  { intros o Ho. apply rw_writable. unfold A_QUAR, A_ALLOCATOR, o_quar in Ho. lia. }
  apply Forall_cons; [|apply Forall_nil].
  eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VQW]. }
apply Forall_cons.
{ reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split.
  { intros o Ho. apply rw_writable. unfold A_QUAR, A_ALLOCATOR, o_quar in Ho. lia. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - apply (chunk_atom1 0 _ 8 34%nat GSZv); [reflexivity | lia | rewrite Z.add_0_l; exact G0 | r8 | cbn; lia].
  - apply (chunk_atom1 0 _ 8 35%nat GFv); [reflexivity | lia | rewrite Z.add_0_l; exact G1 | r8 | cbn; lia].
  - apply (chunk_atom1 0 _ 8 36%nat GLv); [reflexivity | lia | rewrite Z.add_0_l; exact G2 | r8 | cbn; lia].
  - apply (chunk_atom1 0 _ 8 37%nat GBv); [reflexivity | lia | rewrite Z.add_0_l; exact G3 | r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. rewrite BVT. split; [unfold t_qc; lia|]. split; [unfold t_qc; lia|]. split.
  { intros o Ho. destruct (Z_lt_le_dec o 88); [apply (val_mem_writable _ _ _ _ Q0) | destruct (Z_lt_le_dec o 96); [apply (val_mem_writable _ _ _ _ Q1) | destruct (Z_lt_le_dec o 104); [apply (val_mem_writable _ _ _ _ Q2) | apply (val_mem_writable _ _ _ _ Q3)]]];
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [unfold t_qc in *; lia | apply (zone3_off_img _ _ _ HTz); unfold t_qc in *; lia]. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - apply (chunk_atom1 _ _ 8 38%nat TSZv); [reflexivity | lia | | r8 | cbn; lia].
    cbn [N.to_nat]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + t_qc) by lia end. exact Q0.
  - apply (chunk_atom1 _ _ 8 39%nat TFv); [reflexivity | lia | | r8 | cbn; lia].
    cbn [N.to_nat]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + t_qc + 8) by lia end. exact Q1.
  - apply (chunk_atom1 _ _ 8 40%nat TLv); [reflexivity | lia | | r8 | cbn; lia].
    cbn [N.to_nat]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + t_qc + 16) by lia end. exact Q2.
  - apply (chunk_atom1 _ _ 8 41%nat TBv).
    + reflexivity.
    + pose proof HTB as TBr. unfold kQuarantineCacheMax in TBr. change (2 ^ 64) with 18446744073709551616. lia.
    + cbn [N.to_nat]. match goal with |- val_mem _ _ ?a _ _ => replace a with (T + t_qc + 24) by lia end. exact Q3.
    + change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616. pose proof HTB as TBr. unfold kQuarantineCacheMax in TBr. lia.
    + cbn. lia. }
apply Forall_cons.
{ unfold flit8. reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|].
  split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  eapply chunk_ok_val; [reflexivity | cbn; unfold kQuarantineMax; lia | cbn; lia | rewrite Z.add_0_l; exact VMAX]. }
apply Forall_cons; [|apply Forall_nil].
{ unfold flit8. reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|].
  split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  eapply chunk_ok_val; [reflexivity | cbn; unfold kQuarantineMin; lia | cbn; lia | rewrite Z.add_0_l; exact VMIN]. }
Qed.

Lemma PAIRS_ok : pairwise_disjoint E0 AFgj.REG0.
Proof.
pose proof Usp as U. destruct Hstk as [S1 S2]. destruct HT as (T1 & T2 & T3).
pose proof (lo_disj ly HLY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
apply pairwise_disjoint_of_extents. unfold AFgj.REG0, AFgj.R_QW, AFgj.R_QG, AFgj.R_QT, flit8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (E0r 2 2%bv eq_refl). fold sp0. rewrite AFgj.EqT. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DSTACK, kThreadObjSize, t_qc in *.
rewrite !unsigned_lit_small by lia. unfold A_QUAR, A_ALLOCATOR, o_quar.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct Hsp as [P1 P2]. unfold DSTACK in P1.
destruct Hstklo as [SL1 SL2]. destruct HTz as (Z0 & Z1 & Z2).
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in Z2. unfold kThreadObjSize in HTstk, Z0, Z1, Z2.
repeat split; lia.
Qed.

Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgj.FFD).
Proof.
pose proof Usp as U. destruct Hstk as [S1 S2]. destruct HT as (T1 & T2 & T3). destruct HSB as (B1 & B2 & B3).
destruct HGF as [F1 F2]. destruct HGL as [L1 L2]. destruct HTF as [N1 N2]. destruct HTL as [M1 M2].
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew E0 2 = w64 sp0) by (rewrite (E0r 2 2%bv eq_refl); unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
cbn [AFgj.FFD f_atoms atoms_ok].
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DSTACK, kThreadObjSize, kSpaceSize, kQuarantineCacheMax in *.
split. { apply (AF 2%nat sp0); [exact E2' | | | |]. all: first [lia | change (2 ^ 4) with 16; exact Hsp_al]. }
split. { apply (AF 32%nat T); [apply AFgj.EqT | | | |]. all: first [lia | change (2 ^ 12) with 4096; exact T3]. }
split. { apply (AF 33%nat SB); [apply AFgj.EqSB | | | |]. all: first [lia | change (2 ^ 16) with 65536; exact B3]. }
split. { apply (AF 34%nat GSZv); [apply AFgj.EqGSZ | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 35%nat GFv); [apply AFgj.EqGF | | | |]. all: first [lia | change (2 ^ 13) with 8192; exact F2]. }
split. { apply (AF 36%nat GLv); [apply AFgj.EqGL | | | |]. all: first [lia | change (2 ^ 13) with 8192; exact L2]. }
split. { apply (AF 37%nat GBv); [apply AFgj.EqGB | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat TSZv); [apply AFgj.EqTSZ | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 39%nat TFv); [apply AFgj.EqTF | | | |]. all: first [lia | change (2 ^ 13) with 8192; exact N2]. }
split. { apply (AF 40%nat TLv); [apply AFgj.EqTL | | | |]. all: first [lia | change (2 ^ 13) with 8192; exact M2]. }
split; [|exact I]. { apply (AF 41%nat TBv); [apply AFgj.EqTB | | | |]. all: first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
Qed.

Lemma dr_seed : st_ok tfibsegs E0 AFgj.SS0 (restrict (w_H W) (mkst regs0 (w64 0x337ec) mem0 (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold AFgj.SS0, AFgj.SR0, sr_set. cbn [bv_eqb]. unfold AFgj.E0, w64.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg
    | intros XX; discriminate | cbn [sv_denot]; exact Htp]
    | intros XX; discriminate | cbn [sv_denot]; exact Ha0]
    | intros XX; discriminate | cbn [sv_denot]; fold (AFgj.E0 ly regs0 gq tq); rewrite (AFgj.EqT ly regs0 gq tq); rewrite Ha1; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold T; lia]
    | intros XX; discriminate | cbn [sv_denot]; fold (AFgj.E0 ly regs0 gq tq); rewrite (AFgj.EqT ly regs0 gq tq); rewrite Ha2; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold T; lia].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.

Theorem drain_free_hyps : AFgj.free_hyps W ly regs0 mem0 gq tq.
Proof.
constructor.
- exact HLY.
- exact HIMG.
- exact Htp.
- exact Hra.
- exact Hra4096.
- exact Hsp.
- exact Hsp_al.
- exact Hpres.
- destruct HGF as [F1 F2]. splits; first [exact F2 | lia].
- destruct HTF as [N1 N2]. destruct HTL as [M1 M2]. splits; first [exact N2 | exact M2 | lia].
- exact Hglast.
- exact dr_seed.
Qed.
End d.
End c.

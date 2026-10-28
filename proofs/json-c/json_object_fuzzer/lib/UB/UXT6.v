(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rfree_sym := UKNz.rfree_sym.
Definition rmalloc_sym := UKNz.rmalloc_sym.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition RMALLOC_SYM : Z := 0x521f4.
Lemma gw_eq_RMALLOC_SYM : @RMALLOC_SYM = ltac:(GwInst.gw_term (@QDXD.Mq3.RMALLOC_SYM UKNz.rmalloc_sym) (@RMALLOC_SYM)). Proof. unfold RMALLOC_SYM, QDXD.Mq3.RMALLOC_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RMALLOC_SYM : gw_eqs.
Definition RFREE_SYM : Z := 0x520b4.
Lemma gw_eq_RFREE_SYM : @RFREE_SYM = ltac:(GwInst.gw_term (@QDXD.Mq3.RFREE_SYM UKNz.rfree_sym) (@RFREE_SYM)). Proof. unfold RFREE_SYM, QDXD.Mq3.RFREE_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RFREE_SYM : gw_eqs.
Definition RMALLOC_STACK : Z := 8192.
Lemma gw_eq_RMALLOC_STACK : @RMALLOC_STACK = ltac:(GwInst.gw_term (@QDXD.Mq3.RMALLOC_STACK) (@RMALLOC_STACK)). Proof. unfold RMALLOC_STACK, QDXD.Mq3.RMALLOC_STACK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RMALLOC_STACK : gw_eqs.
Definition RFREE_STACK : Z := 8192.
Lemma gw_eq_RFREE_STACK : @RFREE_STACK = ltac:(GwInst.gw_term (@QDXD.Mq3.RFREE_STACK) (@RFREE_STACK)). Proof. unfold RFREE_STACK, QDXD.Mq3.RFREE_STACK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RFREE_STACK : gw_eqs.

Definition ralloc_static (a : Z) : Prop :=
(RCTX <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4).
Lemma gw_eq_ralloc_static : @ralloc_static = ltac:(GwInst.gw_term (@QDXD.Mq3.ralloc_static UKNz.RATP) (@ralloc_static)). Proof. unfold ralloc_static, QDXD.Mq3.ralloc_static; ltac2:(GwEq.gw_rw [[@gw_eq_RERRNO__3; @gw_eq_RERRNO__2; @gw_eq_RERRNO]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ralloc_static : gw_eqs.

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
/\ HINV_from ref_reserved rc_secret st (ps_brk s) LB0.

#[using="Type"] Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.RHEAP_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.RHEAP_ext)]. Qed.

#[using="Type"] Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.RHEAP_perm) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.RHEAP_perm)]. Qed.

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (0x62000 <= a < 0x99000 /\ ~ ralloc_static a) \/ in_block LB a.
Lemma gw_eq_rclient_addr : @rclient_addr = ltac:(GwInst.gw_term (@QDXD.Mq3.rclient_addr UKNz.RATP UKNz.RIMG_HI UKNz.RDATA_LO) (@rclient_addr)). Proof. unfold rclient_addr, QDXD.Mq3.rclient_addr; rewrite ?gw_eq_ralloc_static; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rclient_addr : gw_eqs.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).
Lemma gw_eq_rheap_pres : @rheap_pres = ltac:(GwInst.gw_term (@QDXD.Mq3.rheap_pres rsegs UKNz.RATP UKNz.RIMG_HI UKNz.RDATA_LO) (@rheap_pres)). Proof. unfold rheap_pres, QDXD.Mq3.rheap_pres; rewrite ?gw_eq_rclient_addr; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rheap_pres : gw_eqs.

#[using="Type"] Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof. rewrite ?gw_eq_rheap_pres; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_refl) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_refl)]. Qed.

#[using="Type"] Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof. rewrite ?gw_eq_rheap_pres; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_trans) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_trans)]. Qed.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
#[using="Type"] Lemma rheap_pres_weaken : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq3.rheap_pres_weaken) [[@gw_eq_rheap_pres]; [@gw_eq_RMALLOC_SYM__3; @gw_eq_RMALLOC_SYM__2; @gw_eq_RMALLOC_SYM]; [@gw_eq_RFREE_SYM__3; @gw_eq_RFREE_SYM__2; @gw_eq_RFREE_SYM]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_ralloc_static__3; @gw_eq_ralloc_static__2; @gw_eq_ralloc_static]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]] '(@nil Z) '(Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@RHEAP) gwt_X)).
Proof. rewrite ?gw_eq_rheap_pres; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_weaken) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_weaken)]. Qed.

Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (0x62000 <= A /\ A + n <= 0x99000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
/\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A))
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).
Lemma gw_eq_rclient_range : @rclient_range = ltac:(GwInst.gw_term (@QDXD.Mq3.rclient_range UKNz.RATP UKNz.RGOT_SSP UKNz.RIMG_HI UKNz.RDATA_LO) (@rclient_range)). Proof. unfold rclient_range, QDXD.Mq3.rclient_range; ltac2:(GwEq.gw_rw [[@gw_eq_RERRNO__3; @gw_eq_RERRNO__2; @gw_eq_RERRNO]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rclient_range : gw_eqs.

#[using="Type"] Lemma rclient_range_addr : forall LB SP A n a,
rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof. rewrite ?gw_eq_rclient_addr, ?gw_eq_rclient_range; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rclient_range_addr) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rclient_range_addr)]. Qed.

#[using="Type"] Lemma rheap_pres_bytes_at : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq3.rheap_pres_bytes_at) [[@gw_eq_rheap_pres]; [@gw_eq_rclient_range]; [@gw_eq_RMALLOC_SYM__3; @gw_eq_RMALLOC_SYM__2; @gw_eq_RMALLOC_SYM]; [@gw_eq_RFREE_SYM__3; @gw_eq_RFREE_SYM__2; @gw_eq_RFREE_SYM]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_ralloc_static__3; @gw_eq_ralloc_static__2; @gw_eq_ralloc_static]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]] '(@nil Z) '(Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@RHEAP) gwt_X)).
Proof. rewrite ?gw_eq_rheap_pres, ?gw_eq_rclient_range; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_bytes_at) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_bytes_at)]. Qed.

#[using="Type"] Lemma rheap_pres_wr_at : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq3.rheap_pres_wr_at) [[@gw_eq_rheap_pres]; [@gw_eq_rclient_range]; [@gw_eq_RMALLOC_SYM__3; @gw_eq_RMALLOC_SYM__2; @gw_eq_RMALLOC_SYM]; [@gw_eq_RFREE_SYM__3; @gw_eq_RFREE_SYM__2; @gw_eq_RFREE_SYM]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_ralloc_static__3; @gw_eq_ralloc_static__2; @gw_eq_ralloc_static]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]] '(@nil Z) '(Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@RHEAP) gwt_X)).
Proof. rewrite ?gw_eq_rheap_pres, ?gw_eq_rclient_range; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_wr_at) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_wr_at)]. Qed.

#[using="Type"] Lemma rheap_pres_rw_cells : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq3.rheap_pres_rw_cells) [[@gw_eq_rheap_pres]; [@gw_eq_rclient_range]; [@gw_eq_RMALLOC_SYM__3; @gw_eq_RMALLOC_SYM__2; @gw_eq_RMALLOC_SYM]; [@gw_eq_RFREE_SYM__3; @gw_eq_RFREE_SYM__2; @gw_eq_RFREE_SYM]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_ralloc_static__3; @gw_eq_ralloc_static__2; @gw_eq_ralloc_static]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]] '(@nil Z) '(Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@RHEAP) gwt_X)).
Proof. rewrite ?gw_eq_rheap_pres, ?gw_eq_rclient_range; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_rw_cells) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_rw_cells)]. Qed.

#[using="Type"] Lemma rheap_pres_u8arr : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq3.rheap_pres_u8arr) [[@gw_eq_rheap_pres]; [@gw_eq_rclient_range]; [@gw_eq_RMALLOC_SYM__3; @gw_eq_RMALLOC_SYM__2; @gw_eq_RMALLOC_SYM]; [@gw_eq_RFREE_SYM__3; @gw_eq_RFREE_SYM__2; @gw_eq_RFREE_SYM]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_ralloc_static__3; @gw_eq_ralloc_static__2; @gw_eq_ralloc_static]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]] '(@nil Z) '(Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@RHEAP) gwt_X)).
Proof. rewrite ?gw_eq_rheap_pres, ?gw_eq_rclient_range; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_u8arr) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_u8arr)]. Qed.

#[using="Type"] Lemma rheap_pres_stk : forall LB SP m m' lo hi,
rheap_pres LB SP m m' -> stk rsegs m lo hi -> SP <= lo -> stk rsegs m' lo hi.
Proof. rewrite ?gw_eq_rheap_pres; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_stk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.rheap_pres_stk)]. Qed.

Definition rblock_range (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x99000 <= A).

Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
alloc_ceiling <= fst iv
\/ (0x62000 <= fst iv /\ snd iv <= 0x99000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
/\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init_s rc_secret (reservedZ rsegs)).

#[using="Type"] Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.raddr_exposed_big) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.raddr_exposed_big)]. Qed.
#[using="Type"] Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init_s rc_secret (reservedZ rsegs)) -> raddr_exposed s n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.raddr_exposed_init) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq3.raddr_exposed_init)]. Qed.

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 12 /\ RHEAP s' LB m'
| Some p => exists A junk,
a0 = Z_to_bv 64 A /\ rblock_range A n
/\ RHEAP s' ((p, A, n) :: LB) m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
/\ (raddr_exposed s n -> A = ptr_addr s' p)
/\ (forall g idx, (s_slots (ps_m s')) !! (fst p) = Some (g, idx) ->
is_allzero_ctrl (get_meta_rec (ps_m s') g) = true -> junk = zeros (Z.to_nat n))
end.

Definition rmalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM rsegs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
(r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rauxv_ok m' B
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM rsegs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).

Definition rfree_null_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).
Lemma gw_eq_rfree_null_stmt : @rfree_null_stmt = ltac:(GwInst.gw_term (@QDXD.Mq3.rfree_null_stmt rsegs UKNz.rfree_sym) (@rfree_null_stmt)). Proof. unfold rfree_null_stmt, QDXD.Mq3.rfree_null_stmt; rewrite ?gw_eq_RFREE_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rfree_null_stmt : gw_eqs.

#[using="Type"] Lemma rfree_null_spec : rfree_null_stmt.
Proof.
intros until m. intros ->. unfold RFREE_SYM.
step. step. if_true. step. apply evt_done. reflexivity.
Qed.

End RC__1.
Lemma gw_eq_RMALLOC_SYM__2 : @RMALLOC_SYM = ltac:(GwInst.gw_term (@QDXD.Mq3.RMALLOC_SYM UKNz.rmalloc_sym) (@RMALLOC_SYM)). Proof. unfold RMALLOC_SYM, QDXD.Mq3.RMALLOC_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RMALLOC_SYM__2 : gw_eqs.
Lemma gw_eq_RFREE_SYM__2 : @RFREE_SYM = ltac:(GwInst.gw_term (@QDXD.Mq3.RFREE_SYM UKNz.rfree_sym) (@RFREE_SYM)). Proof. unfold RFREE_SYM, QDXD.Mq3.RFREE_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RFREE_SYM__2 : gw_eqs.
Lemma gw_eq_RMALLOC_STACK__2 : @RMALLOC_STACK = ltac:(GwInst.gw_term (@QDXD.Mq3.RMALLOC_STACK) (@RMALLOC_STACK)). Proof. unfold RMALLOC_STACK, QDXD.Mq3.RMALLOC_STACK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RMALLOC_STACK__2 : gw_eqs.
Lemma gw_eq_RFREE_STACK__2 : @RFREE_STACK = ltac:(GwInst.gw_term (@QDXD.Mq3.RFREE_STACK) (@RFREE_STACK)). Proof. unfold RFREE_STACK, QDXD.Mq3.RFREE_STACK; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RFREE_STACK__2 : gw_eqs.
Lemma gw_eq_ralloc_static__2 : @ralloc_static = ltac:(GwInst.gw_term (@QDXD.Mq3.ralloc_static UKNz.RATP) (@ralloc_static)). Proof. unfold ralloc_static, QDXD.Mq3.ralloc_static; ltac2:(GwEq.gw_rw [[@gw_eq_RERRNO__3; @gw_eq_RERRNO__2; @gw_eq_RERRNO]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ralloc_static__2 : gw_eqs.
Lemma gw_eq_rclient_addr__2 : @rclient_addr = ltac:(GwInst.gw_term (@QDXD.Mq3.rclient_addr UKNz.RATP UKNz.RIMG_HI UKNz.RDATA_LO) (@rclient_addr)). Proof. unfold rclient_addr, QDXD.Mq3.rclient_addr; rewrite ?gw_eq_ralloc_static__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rclient_addr__2 : gw_eqs.
Lemma gw_eq_rheap_pres__2 : @rheap_pres = ltac:(GwInst.gw_term (@QDXD.Mq3.rheap_pres rsegs UKNz.RATP UKNz.RIMG_HI UKNz.RDATA_LO) (@rheap_pres)). Proof. unfold rheap_pres, QDXD.Mq3.rheap_pres; rewrite ?gw_eq_rclient_addr__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rheap_pres__2 : gw_eqs.
Lemma gw_eq_rclient_range__2 : @rclient_range = ltac:(GwInst.gw_term (@QDXD.Mq3.rclient_range UKNz.RATP UKNz.RGOT_SSP UKNz.RIMG_HI UKNz.RDATA_LO) (@rclient_range)). Proof. unfold rclient_range, QDXD.Mq3.rclient_range; ltac2:(GwEq.gw_rw [[@gw_eq_RERRNO__3; @gw_eq_RERRNO__2; @gw_eq_RERRNO]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rclient_range__2 : gw_eqs.
Lemma gw_eq_rfree_null_stmt__2 : @rfree_null_stmt = ltac:(GwInst.gw_term (@QDXD.Mq3.rfree_null_stmt rsegs UKNz.rfree_sym) (@rfree_null_stmt)). Proof. unfold rfree_null_stmt, QDXD.Mq3.rfree_null_stmt; rewrite ?gw_eq_RFREE_SYM__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rfree_null_stmt__2 : gw_eqs.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
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
Definition rcalloc_entry := UKNz.rcalloc_entry.
Definition rrealloc_sym := ltac:(let gw_v_ := eval cbv in ((UKNz.rrealloc_entry + -4)%Z) in exact gw_v_).
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition RCALLOC_SYM : Z := 0x51f7c.
Lemma gw_eq_RCALLOC_SYM : @RCALLOC_SYM = ltac:(GwInst.gw_term (@QkTt.Mq2.RCALLOC_SYM UKNz.rcalloc_entry) (@RCALLOC_SYM)). Proof. unfold RCALLOC_SYM, QkTt.Mq2.RCALLOC_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RCALLOC_SYM : gw_eqs.
Definition RREALLOC_SYM : Z := 0x53d40.
Lemma gw_eq_RREALLOC_SYM : @RREALLOC_SYM = ltac:(GwInst.gw_term (@QkTt.Mq2.RREALLOC_SYM ltac:(let gw_v_ := eval cbv in ((UKNz.rrealloc_entry + -4)%Z) in exact gw_v_)) (@RREALLOC_SYM)). Proof. unfold RREALLOC_SYM, QkTt.Mq2.RREALLOC_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RREALLOC_SYM : gw_eqs.
Definition RCALLOC_STACK : Z := RMALLOC_STACK + 32.
Lemma gw_eq_RCALLOC_STACK : @RCALLOC_STACK = ltac:(GwInst.gw_term (@QkTt.Mq2.RCALLOC_STACK) (@RCALLOC_STACK)). Proof. unfold RCALLOC_STACK, QkTt.Mq2.RCALLOC_STACK; ltac2:(GwEq.gw_rw [[@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RCALLOC_STACK : gw_eqs.
Definition RREALLOC_STACK : Z := RMALLOC_STACK + 64.
Lemma gw_eq_RREALLOC_STACK : @RREALLOC_STACK = ltac:(GwInst.gw_term (@QkTt.Mq2.RREALLOC_STACK) (@RREALLOC_STACK)). Proof. unfold RREALLOC_STACK, QkTt.Mq2.RREALLOC_STACK; ltac2:(GwEq.gw_rw [[@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RREALLOC_STACK : gw_eqs.

Definition rcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (N lo B : Z) (m : mem)
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
| Some p => exists A,
a0 = Z_to_bv 64 A /\ rblock_range A N
/\ RHEAP s' ((p, A, N) :: LB) m'
/\ rw_cells rsegs m' A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))]
end.

Definition rcalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 ->
implM rsegs (raw_calloc cnt sz) s
(rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom rsegs)).

Definition real_off (cs : mstate) (slot : cptr) (A : Z) : Z := (A - conc cs slot) / UNIT.
Lemma gw_eq_real_off : @real_off = ltac:(GwInst.gw_term (@QkTt.Mq2.real_off) (@real_off)). Proof. unfold real_off, QkTt.Mq2.real_off; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_real_off : gw_eqs.

Definition rrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (old : list byte) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None =>
a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 12 /\ RHEAP s' LB m' /\ rheap_pres LB (bv_unsigned sp) m m'
| Some p' => exists A' junk,
a0 = Z_to_bv 64 A' /\ rblock_range A' n
/\ RHEAP s' ((p', A', n) :: lb_remove p LB) m'
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ rw_cells rsegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n n0)) old ++ junk)]
end.

Definition rrealloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old junk0 : list byte),
RHEAP s LB m -> In (p, A, n0) LB ->
rw_cells rsegs m A [CB (Z.to_nat n0) (old ++ junk0)] ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
implM rsegs (raw_realloc (fst p) (real_off (ps_m s) (fst p) A) n) s
(rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom rsegs)).

End RC__1.
Lemma gw_eq_RCALLOC_SYM__2 : @RCALLOC_SYM = ltac:(GwInst.gw_term (@QkTt.Mq2.RCALLOC_SYM UKNz.rcalloc_entry) (@RCALLOC_SYM)). Proof. unfold RCALLOC_SYM, QkTt.Mq2.RCALLOC_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RCALLOC_SYM__2 : gw_eqs.
Lemma gw_eq_RREALLOC_SYM__2 : @RREALLOC_SYM = ltac:(GwInst.gw_term (@QkTt.Mq2.RREALLOC_SYM ltac:(let gw_v_ := eval cbv in ((UKNz.rrealloc_entry + -4)%Z) in exact gw_v_)) (@RREALLOC_SYM)). Proof. unfold RREALLOC_SYM, QkTt.Mq2.RREALLOC_SYM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RREALLOC_SYM__2 : gw_eqs.
Lemma gw_eq_RCALLOC_STACK__2 : @RCALLOC_STACK = ltac:(GwInst.gw_term (@QkTt.Mq2.RCALLOC_STACK) (@RCALLOC_STACK)). Proof. unfold RCALLOC_STACK, QkTt.Mq2.RCALLOC_STACK; ltac2:(GwEq.gw_rw [[@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RCALLOC_STACK__2 : gw_eqs.
Lemma gw_eq_RREALLOC_STACK__2 : @RREALLOC_STACK = ltac:(GwInst.gw_term (@QkTt.Mq2.RREALLOC_STACK) (@RREALLOC_STACK)). Proof. unfold RREALLOC_STACK, QkTt.Mq2.RREALLOC_STACK; ltac2:(GwEq.gw_rw [[@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RREALLOC_STACK__2 : gw_eqs.
Lemma gw_eq_real_off__2 : @real_off = ltac:(GwInst.gw_term (@QkTt.Mq2.real_off) (@real_off)). Proof. unfold real_off, QkTt.Mq2.real_off; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_real_off__2 : gw_eqs.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM21.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM03.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM18.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RASlot_W2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM10.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM20.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_W11.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01. Import MM01. Import MM01.ASlot_W11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM21.RF_mm_syscalls. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM18. Import PM18.RMallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RASlot_W2.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rsmall_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes (run_segments psegs rc_inp rc_sp rc_mb) RSMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes (run_segments psegs rc_inp rc_sp rc_mb) RMED_CNT 4 with Some bs => bs | None => [] end).

Lemma rsmall_cnt_ro : forall m, mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> ro_cells (run_segments psegs rc_inp rc_sp rc_mb) m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image (run_segments psegs rc_inp rc_sp rc_mb) m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
Lemma rmed_cnt_ro : forall m, mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> ro_cells (run_segments psegs rc_inp rc_sp rc_mb) m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image (run_segments psegs rc_inp rc_sp rc_mb) m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.

Lemma rsmall_cnt_read : forall m sc i, mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> 0 <= sc < 9 -> 0 <= i < 3 ->
  ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) m (wa (RSMALL_CNT + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof.
  intros m sc i MI Hsc Hi.
  destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
  rewrite (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
  unfold small_cnt. rewrite !Nat2Z.id.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.

Lemma rmed_cnt_read : forall m i, mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> 0 <= i < 4 ->
  ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) m (wa (RMED_CNT + i)) 1 = Some [b8 (med_cnt i)].
Proof.
  intros m i MI Hi.
  destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.

Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

Lemma rhalve_big_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists a2' a3',
      ms' = MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x1a3c0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x1a3ac) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
  - cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
    step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
    apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
  - cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
    assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
    step. rewrite (unsigned_lit (size * cnt)) by lia.
    step. rewrite (wz_unsigned cnt) by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    +
      rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
      rewrite (F_malloc_entry.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
      apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
      rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
    + rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
      apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
  intros H.
  assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|NE].
    - change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
    - replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
      rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
  rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists a3' a4',
      ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x1a3ac) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x1a384) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
  - change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
  - cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
    assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).
    step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
    +
      replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
      step. apply evt_done. do 2 eexists. reflexivity.
    + replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      step. rewrite (wz_unsigned cnt) by lia. rewrite (F_malloc_entry.srliw_small cnt 1) by lia.
      step. rewrite (wz_unsigned cnt) by lia. step.
      assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      *
        assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
        assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
        { rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
        change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
        apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
      *
        step.
        assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
        replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
        apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma rhalve_even_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists a3' a4',
      ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x1a3ac) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x1a37c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m; intros CR C32 MI; unfold rcnt_regs.
  step. rewrite (wz_unsigned cnt) by lia.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
  -
    assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
    replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
    step. step. apply evt_done. do 2 eexists. reflexivity.
  - assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
    destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
    apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
End HALVE2.
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
      first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
  - pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

Lemma rcount_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists a2' a3' a4',
      ms' = MS (rcnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x1a3c0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
             (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x1a320) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until fc. intros MI.
  pose proof (size_class_range sc SC) as SZR.
  pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
  pose proof rcnt0_range as C0R.
  unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.
  pose proof (rmrep_usage_read st m sc (wa (602752 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
  step. clear RDU.
  step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).
  step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
  -
    apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].
    step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
    step. clear RDM. rewrite zxb_b8 by lia.
    eapply evt_cut.
    { eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
    eapply evt_mono.
    { eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
  -
    assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
    unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
    pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
    replace (wa (74940 + 3 * sc + 0)) with (Z_to_bv 64 (74940 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
    step. clear RD0. rewrite zxb_b8 by lia.
    step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
    { replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
    replace (wa (74940 + 3 * sc + 1)) with (Z_to_bv 64 (74940 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
    step. clear RD1. rewrite zxb_b8 by lia.
    step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
    { replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
    replace (wa (74940 + 3 * sc + 2)) with (Z_to_bv 64 (74940 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
    step. clear RD2. rewrite zxb_b8 by lia. step.
    apply evt_done. do 3 eexists. reflexivity.
Qed.
End COUNT.
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

Lemma rcnt2_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' =>
      ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 (if big then 0x1a3e8 else 0x1a42c)) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x1a3c0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m. intros MI. unfold rcnt_regs.
  assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
  pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
  assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.
  step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  -
    assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).
    step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
  -
    step. rewrite ?unsigned_lit by lia. step. step.
    assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
    { unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
      destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
    assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
    { rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
      destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
    rewrite EV. clear EV.
    assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).
    step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.
End CANSEC1.
End RASlot_W11.

Module RF_ntf_E.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06. Import MM06. Import MM06.F_ntf_C. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM10. Import MM10. Import MM10.F_ntf_E. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM20. Import PM20.RF_ntf_A. Import PM20.RF_ntf_C.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
      apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x198c0) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -96)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some g ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x198b8) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX in *. atop_facts.
  st1.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ (actives st) sc (Z_to_bv 64 (602752 + sc * 8 + 80)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
  clear ACTS.
  rraw_store_finish (602752 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
  assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
  { unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
  rewrite EQ.
  apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + apply rfree_fp_ctx. unfold RCTX. lia. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  a2 = pw st (active st sc) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19834) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX in *. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (602752, 602752 + 928)]%Z m) as MU.
  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. clear CH.
  rmeta_open (conc st pv) MUp WMp.
  rmeta_chunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
  set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. clear CH.
  rmeta_open (conc st nx) MUn WMn.
  rmeta_chunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
  set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
  replace (wa (602752 + 80 + 8 * sc)) with (Z_to_bv 64 (602752 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
  assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
  assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
  st1. clear RDA.
  assert (EQmid : deq_mid (LActive sc) g st =
                  if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
  { unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
    rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }
  st1. if_cases K; zify_cond K.
  -
    assert (HA : optr_eqb (active st sc) (Some g) = false).
    { destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
      unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
    rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
  -
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
    rewrite HA, optr_eqb_refl in EQmid.
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. clear CH. st1.
    pose proof MR2 as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ (actives st2) sc (Z_to_bv 64 (602752 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
    clear ACTS.
    rraw_store_finish (602752 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
    rewrite <- EQmid in MR3. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
  intros Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
  le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof.
  intros Hf Hy Hz. apply le4_congr.
  pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
  assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
  assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
  { split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
  rewrite unsigned_lit, wz_unsigned by lia.
  rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19924) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -96)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
  let st1 := upd_meta g clr_links stm in
  rmrep stm m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot stm g -> 0 <= sc < 48 ->
  (if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
  (an = true -> forall a, active st1 sc = Some a ->
     meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
     /\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x198c0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX in *. atop_facts.
  pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.
  rmeta_open (conc stm g) MUg WMg.
  rmeta_chunk MR MSL CH.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st1 mX)
      by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; ftauto]);
    clear MUg WMg CH
  end.
  assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' ->
                 rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
  { intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
    cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
  assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
  assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).
  st1. if_cases K; zify_cond K.
  -
    destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
    cbn [pd_st].
    apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
  -
    destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
    cbn [pd_st].
    pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
    assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
    replace (wa (602752 + 80 + 8 * sc)) with (Z_to_bv 64 (602752 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    st1. destruct (active st1 sc) as [a|] eqn:HA1.
    + destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
      pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
      munch_grow MU (conc stm a, conc stm a + 40).
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
      rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.
      st1.
      destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
      rewrite Hconc in RD8.
      st1.
      pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
      assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
      { rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
      st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
      set (y := 2 ^ (g_active_idx gh + 1)).
      st1. st1. rewrite negw_word.
      clear CHa. rmeta_open (conc stm a) MUa WMa.
      rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
      pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
      st1. rewrite sx32_wz_sxv by lia.
      st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
      assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
      { apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
      amo_step AMO. rewrite ?sx32_wz_sxv by lia.
      st1. if_false.
      amo_step AMO.
      st1. if_false.
      st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
      st1. st1. st1.
      set (f := m_freed (get_meta_rec st1 a)) in *.
      assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ACT : act_of st1 a = y - 1).
      { unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
      assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
      assert (Y1 : 1 <= y <= 2^32).
      { unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
      pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
      pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
      pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
      end.
      { unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
        eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; ftauto].
        unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
        fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
        rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
      clear MUa WMa CHa.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
               cbn [ivs_covered]. repeat split; intros x Hx.
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSa | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR2.
    +
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR1.
Qed.
End CANSEC1.
End RF_ntf_E.

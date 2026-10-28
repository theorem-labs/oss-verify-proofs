(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup Exit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).

  Definition LO : Z := usp0 - 8388608.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (j8 : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells usegs mm (usp0 + -128)
      [CB 8 j8; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 PMAIN);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 PSTAGE2_RET)].

  (* [comment removed for export] *)
  Definition RSTAT (reg : bool) (mm : mem) : Prop :=
    rw_cells usegs mm 0x48130 [C8 (Z_to_bv 64 0x48130); C8 (Z_to_bv 64 0x48130); C8 (Z_to_bv 64 0x48130); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells usegs mm 0x68460 [C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x36e80 [C8 (Z_to_bv 64 0x36dd8); C8 (Z_to_bv 64 0x36dd0)]
    /\ rw_cells usegs mm 0x36dd0 [C8 (Z_to_bv 64 0x14318)]
    /\ rw_cells usegs mm 0x380e8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs mm 0x36e18 [C8 (Z_to_bv 64 PCXA_FIN); C8 (Z_to_bv 64 0)]     (* [comment removed for export] *)
    /\ rw_cells usegs mm 0x688b8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x688a8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x38090 [C8 (Z_to_bv 64 0x37fa8)]
    /\ rw_cells usegs mm 0x37fa0 [C8 (Z_to_bv 64 0x37eb8)]
    /\ rw_cells usegs mm 0x36e28 [C8 (Z_to_bv 64 0x36dd8)]
    /\ rw_cells usegs mm 0x36dd8 [C8 (Z_to_bv 64 0x37eb8)]
    /\ rw_cells usegs mm PDSO [C8 (Z_to_bv 64 PDSO)]                                 (* [comment removed for export] *)
    /\ atexit_cells reg mm                                                           (* [comment removed for export] *)
    /\ rw_cells usegs mm PAEF_INCB [C1 (Z_to_bv 8 0)].                                (* [comment removed for export] *)

  Definition rstat_addr (a : Z) : Prop :=
    (0x48130 <= a < 0x48154) \/ (0x68460 <= a < 0x68468) \/ (0x36e80 <= a < 0x36e90) \/ (0x36dd0 <= a < 0x36dd8)
    \/ (0x380e8 <= a < 0x380e9) \/ (0x36e18 <= a < 0x36e28) \/ (0x688a8 <= a < 0x688b0) \/ (0x688b8 <= a < 0x688c0)
    \/ (0x38090 <= a < 0x38098) \/ (0x37fa0 <= a < 0x37fa8) \/ (0x36e28 <= a < 0x36e30) \/ (0x36dd8 <= a < 0x36de8)
    \/ (0x37e90 <= a < 0x37e98) \/ (0x68240 <= a < 0x68268) \/ (0x68360 <= a < 0x68368) \/ (0x480f4 <= a < 0x480f5).  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rstat_addr0 (a : Z) : Prop :=
    (0x48130 <= a < 0x48154) \/ (0x68460 <= a < 0x68468) \/ (0x36e80 <= a < 0x36e90) \/ (0x36dd0 <= a < 0x36dd8)
    \/ (0x380e8 <= a < 0x380e9) \/ (0x36e18 <= a < 0x36e28) \/ (0x688a8 <= a < 0x688b0) \/ (0x688b8 <= a < 0x688c0)
    \/ (0x38090 <= a < 0x38098) \/ (0x37fa0 <= a < 0x37fa8) \/ (0x36e28 <= a < 0x36e30) \/ (0x36dd8 <= a < 0x36de8)
    \/ (0x37e90 <= a < 0x37e98).

  Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr, rstat_addr0; cbn in Ha; lia].

  Lemma RSTAT_agree : forall (P : Z -> Prop) reg m m', magree usegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT reg m -> RSTAT reg m'.
  Proof.
    intros P reg m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & [A14 A15] & A16). unfold RSTAT.
    unfold atexit_cells, PDSO, PATEXIT, PAEF_INCB in *.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12|].
    split; [tr AG HP A13|]. split; [split; [tr AG HP A14| tr AG HP A15]| tr AG HP A16].
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_agree0 : forall (P : Z -> Prop) reg reg' m m', magree usegs P m m' -> (forall a, rstat_addr0 a -> P a) ->
    atexit_cells reg' m' -> rw_cells usegs m' PAEF_INCB [C1 (Z_to_bv 8 0)] -> RSTAT reg m -> RSTAT reg' m'.
  Proof.
    intros P reg reg' m m' AG HP ATX INCB (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & _ & _). unfold RSTAT.
    unfold PDSO in *.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12|].
    split; [tr AG HP A13|]. split; [exact ATX| exact INCB].
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_heap_pres : forall reg LB SP m m', rheap_pres LB SP m m' -> RSTAT reg m -> RSTAT reg m'.
  Proof.
    intros reg LB SP m m' HP. apply (RSTAT_agree _ _ _ _ HP). intros a Ha. right; left.
    unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_drv_pres : forall reg LB SP m m', pdrv_pres LB SP m m' ->
    atexit_cells true m' -> rw_cells usegs m' PAEF_INCB [C1 (Z_to_bv 8 0)] -> RSTAT reg m -> RSTAT true m'.
  Proof.
    intros reg LB SP m m' HP ATX INCB. apply (RSTAT_agree0 _ _ _ _ _ (pdrv_pres_agree _ _ _ _ HP)); [| exact ATX| exact INCB]. intros a Ha. split.
    - right; left. unfold rstat_addr0, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
    - unfold rstat_addr0, pstdout_ivs, PINIT_FLAG, PATEXIT in *. cbn. lia.
  Qed.

  Lemma RSTAT_munch : forall reg W m m', munch W m m' -> wmono usegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT reg m -> RSTAT reg m'.
  Proof.
    intros reg W m m' MU WM HW. apply (RSTAT_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stdout_addr (a : Z) : Prop := (0x37fa8 <= a < 0x38090) \/ (0x688d0 <= a < 0x68cd0).
Definition stderr_addr (a : Z) : Prop := 0x37eb8 <= a < 0x37fa0.
Definition trun0_addr (a : Z) : Prop :=
  (PINIT_FLAG <= a < PINIT_FLAG + 1) \/ (PGOT_FUZZ_INIT <= a < PGOT_FUZZ_INIT + 8)
  \/ (PGOT_STDERR <= a < PGOT_STDERR + 8) \/ (PSTDERR_PTR <= a < PSTDERR_PTR + 8)
  \/ (PDCTX <= a < PDCTX + 8) \/ (PGOT_TRACE <= a < PGOT_TRACE + 16)       (* [comment removed for export] *)
  \/ (PATEXIT <= a < PATEXIT + 40) \/ (PATEXIT + 288 <= a < PATEXIT + 296) \/ (PAEF_INCB <= a < PAEF_INCB + 1).   (* [comment removed for export] *)

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  magree usegs P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_file0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros P m m' AG HP H. unfold stderr_file0 in *.
  eapply rw_cells_magree; [exact AG| exact H|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

Lemma trun_cells0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, trun0_addr a -> P a) -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A7 & A8 & A9 & A10 & [A11 A12] & A13). unfold trun_cells0, atexit_cells in *.
  Ltac tr2 AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold trun0_addr; cbn in Ha; lia].
  split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|]. split; [tr2 AG HP A7|]. split; [tr2 AG HP A8|]. split; [tr2 AG HP A9|]. split; [tr2 AG HP A10|].
  split; [split; [tr2 AG HP A11| tr2 AG HP A12]| tr2 AG HP A13].
Qed.

Lemma stdout_file_heap_pres : forall LB SP m m' so, rheap_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
  intros LB SP m m' so HP. apply (stdout_file_agree _ _ _ _ HP). intros a Ha. right; left.
  unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_file0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ HP). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_file0_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
  - right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  - unfold stderr_addr, pstdout_ivs, PINIT_FLAG, PATEXIT in *. cbn. lia.
Qed.
Lemma trun_cells0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros LB SP m m' HP. apply (trun_cells0_agree _ _ _ HP). intros a Ha. right; left.
  unfold trun0_addr, PINIT_FLAG, PGOT_FUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, PATEXIT, PAEF_INCB,
    ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono usegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_file0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_file0 m -> stderr_file0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_file0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma trun_cells0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, trun0_addr a -> outside W a) -> trun_cells0 m -> trun_cells0 m'.
Proof. intros W m m' MU WM HW. apply (trun_cells0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EXITS.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis HT : 0 < TID < 4194304.

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ ATOP <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0x69000 <= LO sp0.
  Proof. destruct VSP as ((A & B & C) & HATOP & _). unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.
  Lemma sp_atop : ATOP = LO sp0.
  Proof. destruct VSP as (_ & HATOP & _). unfold LO. exact HATOP. Qed.

  (* [comment removed for export] *)
  Lemma pat_exit_intro : forall (reg : bool) (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo SP -> lo <= SP - 176 -> 0x69000 <= lo -> 0 <= SP < 2^47 ->    (* [comment removed for export] *)
    RSTAT TID reg m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    pat_exit code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 PEXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST LOS LOLO SPR (TD & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _ & DSO & ATX & INCB) HP SOF SEF MI.
    destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC).
    pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2].
    unfold pat_exit. do 33 eexists. exists m, lo, TID, (Z_to_bv 64 0x48130), (Z_to_bv 64 0x48130), (Z_to_bv 64 0x48130), (Z_to_bv 64 0), CAN.
    exists cdt, thr, sec, tm1, reg.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
    split; [exact FIN|]. split; [exact GCX|]. split; [exact DSO|]. split; [exact ATX|]. split; [exact INCB|].
    split; [exact LC|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [lia|]. split; [lia|]. rewrite ?unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_return : forall (reg : bool) (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (j8 : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m j8 s7v s6v s5v s4v ->
    stk usegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID reg m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    evt usegs (pat_exit code s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x145a4) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros FR ST RS HP SOF SEF MI. pose proof sp_facts as SF. unfold LO in *. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x2dba4)) with (Z_to_bv 64 0x2dba4) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI].
  Qed.

  (* [comment removed for export] *)
  Lemma exit2_tail : forall (reg : bool) (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk usegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID reg m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    evt usegs (pat_exit 2 s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14630) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST RS HP SOF SEF MI. pose proof sp_facts as SF. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI].
  Qed.
End EXITS.
End CANSEC1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import DrvAgree Startup_kit STRW_tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PlainU0 Require Import PImg F_syscalls StdioFiles Startup Exit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PlainU0 Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_kit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT} {rl : runLaunchT}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).

  Definition LO : Z := usp0 - 6144513.

  Definition MFRAME (mm : mem) (j8 : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells psegs mm (usp0 + -128)
      [CB 8 j8; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 PMAIN);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 PSTAGE2_RET)].

  Definition RSTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0x3d6b8 [C8 (Z_to_bv 64 0x3d6b8); C8 (Z_to_bv 64 0x3d6b8); C8 (Z_to_bv 64 0x3d6b8); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells psegs mm 0x5d9e0 [C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x2c400 [C8 (Z_to_bv 64 0x2c210); C8 (Z_to_bv 64 0x2c208)]
    /\ rw_cells psegs mm 0x2c208 [C8 (Z_to_bv 64 0x15aa8)]
    /\ rw_cells psegs mm 0x2d668 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0x2c3a0 [C8 (Z_to_bv 64 0x23508); C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x2d410 [C8 (Z_to_bv 64 0x2d410)]
    /\ rw_cells psegs mm 0x5de38 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x5de28 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x2d610 [C8 (Z_to_bv 64 0x2d528)]
    /\ rw_cells psegs mm 0x2d520 [C8 (Z_to_bv 64 0x2d438)]
    /\ rw_cells psegs mm 0x2c3b0 [C8 (Z_to_bv 64 0x2c360)]
    /\ rw_cells psegs mm 0x2c360 [C8 (Z_to_bv 64 0x2d438)].

  Definition rstat_addr (a : Z) : Prop :=
    (0x3d6b8 <= a < 0x3d6dc) \/ (0x5d9e0 <= a < 0x5d9e8) \/ (0x2c400 <= a < 0x2c410) \/ (0x2c208 <= a < 0x2c210)
    \/ (0x2d668 <= a < 0x2d669) \/ (0x2c3a0 <= a < 0x2c3b0) \/ (0x5de28 <= a < 0x5de30) \/ (0x5de38 <= a < 0x5de40)
    \/ (0x2d610 <= a < 0x2d618) \/ (0x2d520 <= a < 0x2d528) \/ (0x2c3b0 <= a < 0x2c3b8) \/ (0x2c360 <= a < 0x2c370)
    \/ (0x2d410 <= a < 0x2d418) .

  Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr; cbn in Ha; lia].

  Lemma RSTAT_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A6b & A7 & A8 & A9 & A10 & A11 & A12). unfold RSTAT.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A6b|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11| tr AG HP A12].
  Qed.

  Lemma RSTAT_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ HP). intros a Ha. right; left.
    unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  Lemma RSTAT_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
    - right; left. unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
    - unfold rstat_addr, pstdout_ivs, PINIT_FLAG, PATX, HDATA, HDATA_N in *. cbn. lia.
  Qed.

  Lemma RSTAT_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros W m m' MU WM HW. apply (RSTAT_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.


Definition stdout_addr (a : Z) : Prop := (0x2d528 <= a < 0x2d610) \/ (0x5de50 <= a < 0x5e250).
Definition stderr_addr (a : Z) : Prop := 0x2d438 <= a < 0x2d520.
Definition trun0_addr (a : Z) : Prop :=
  (PINIT_FLAG <= a < PINIT_FLAG + 5) \/ (PGOT_FUZZ_INIT <= a < PGOT_FUZZ_INIT + 8) \/ (PRELRO_LO <= a < PRELRO_HI)
  \/ atx_addr a.

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  magree psegs P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
  - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_file0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros P m m' AG HP H. unfold stderr_file0 in *.
  eapply rw_cells_magree; [exact AG| exact H|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & H & FL & WE & E0). exists flags, mode, e, wend, tail. split; [| split; [exact FL| split; [exact WE| exact E0]]].
  eapply rw_cells_magree; [exact AG| exact H|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.
Lemma stderr_wfile0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_wfile0_agree _ _ _ HP). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma harness_cells_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, PRELRO_LO <= a < PRELRO_HI -> P a) -> harness_cells m -> harness_cells m'.
Proof.
  intros P m m' AG HP HC a Ha. destruct (AG a ltac:(unfold PRELRO_LO, PRELRO_HI in Ha; lia) (HP a Ha)) as [E _].
  unfold wa in E. rewrite <- (HC a Ha). exact E.
Qed.
Lemma harness_cells_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> harness_cells m -> harness_cells m'.
Proof.
  intros LB SP m m' HP. apply (harness_cells_agree _ _ _ HP). intros a Ha. right; left.
  unfold PRELRO_LO, PRELRO_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma harness_cells_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, PRELRO_LO <= a < PRELRO_HI -> outside W a) -> harness_cells m -> harness_cells m'.
Proof. intros W m m' MU WM HW. apply (harness_cells_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stdout_file_harness_pres : forall LB SP m m' so, harness_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
  intros LB SP m m' so HP. apply (stdout_file_agree (fun a => rclient_addr LB SP a /\ ~ hown_addr a)); [intros a Ha [Hc Hx]; apply HP; assumption|].
  intros a Ha. split.
  - right; left. unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  - unfold stdout_addr, hown_addr, HDATA, HDATA_N in *. lia.
Qed.
Lemma trun_cells0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, trun0_addr a -> P a) -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3 & A4). unfold trun_cells0.
  Ltac tr2 AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold trun0_addr; cbn in Ha; lia].
  split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|].
  split. { eapply harness_cells_agree; [exact AG| | exact A3]. intros a Ha. apply HP. unfold trun0_addr. right; right; left. exact Ha. }
  eapply atx_cells0_agree; [exact AG| | exact A4]. intros a Ha. apply HP. unfold trun0_addr. right; right; right. exact Ha.
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
Lemma trun_cells0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros LB SP m m' HP. apply (trun_cells0_agree _ _ _ HP). intros a Ha. right; left.
  unfold trun0_addr, atx_addr, PATX, PATX_N, PAEF_INCB, PINIT_FLAG, PGOT_FUZZ_INIT, PRELRO_LO, PRELRO_HI,
    ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono psegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_file0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_file0 m -> stderr_file0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_file0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma trun_cells0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, trun0_addr a -> outside W a) -> trun_cells0 m -> trun_cells0 m'.
Proof. intros W m m' MU WM HW. apply (trun_cells0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Lemma atx_cellsR_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> atx_cellsR m -> atx_cellsR m'.
Proof.
  intros LB SP m m' HP. apply (atx_cellsR_agree _ _ _ HP). intros a Ha. right; left.
  unfold atx_addr, PATX, PATX_N, PAEF_INCB, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma atx_cells0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> atx_cells0 m -> atx_cells0 m'.
Proof.
  intros LB SP m m' HP. apply (atx_cells0_agree _ _ _ HP). intros a Ha. right; left.
  unfold atx_addr, PATX, PATX_N, PAEF_INCB, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.

Section EXITS.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis HT : 0 < TID < 4194304.

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ ATOP <= LO sp0 /\ LO sp0 + 6144513 = usp0 /\ 0x5f000 <= LO sp0.
  Proof. destruct VSP as ((A & B & C) & HATOP & _). unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

  Lemma pat_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk psegs m lo SP -> lo <= SP - 176 -> 0x5f000 <= lo -> 0 <= SP < 2^47 ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    atx_cells0 m \/ atx_cellsR m ->
    pat_exit code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 PEXIT) fc None m (seg_rom psegs)).
  Proof.
    intros until lo. intros ST LOS LOLO SPR (TD & EXL & GF & FA & FIN & GCX & DSO & OFL & SIN & SOU & SEU & _ & _) HP SOF SEF MI ATX.
    destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC).
    pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2].
    unfold pat_exit. do 33 eexists. exists m, lo, TID, (Z_to_bv 64 0x3d6b8), (Z_to_bv 64 0x3d6b8), (Z_to_bv 64 0x3d6b8), (Z_to_bv 64 0), CAN.
    exists cdt, thr, sec, tm1.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
    split; [exact FIN|]. split; [exact GCX|]. split; [exact DSO|]. split; [exact LC|]. split; [exact ATX|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [lia|]. split; [lia|]. rewrite ?unsigned_lit by lia. lia.
  Qed.

  Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (j8 : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m j8 s7v s6v s5v s4v ->
    stk psegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    atx_cells0 m \/ atx_cellsR m ->
    evt psegs (pat_exit code s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15d34) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros FR ST RS HP SOF SEF MI ATX. pose proof sp_facts as SF. unfold LO in *. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x2318c)) with (Z_to_bv 64 0x2318c) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI| exact ATX].
  Qed.

  Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk psegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    atx_cells0 m \/ atx_cellsR m ->
    evt psegs (pat_exit 2 s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15dc0) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros ST RS HP SOF SEF MI ATX. pose proof sp_facts as SF. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI| exact ATX].
  Qed.
End EXITS.
End CANSEC1.

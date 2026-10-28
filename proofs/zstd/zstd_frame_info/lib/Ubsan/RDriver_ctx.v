(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Startup_kit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup F_atexit Exit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
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

  Definition RSTAT (mm : mem) : Prop :=
    rw_cells usegs mm 0x2df68 [C8 (Z_to_bv 64 0x2df68); C8 (Z_to_bv 64 0x2df68); C8 (Z_to_bv 64 0x2df68); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells usegs mm 0x4e290 [C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x1ccc0 [C8 (Z_to_bv 64 0x1cc28); C8 (Z_to_bv 64 0x1cc20)]
    /\ rw_cells usegs mm 0x1cc20 [C8 (Z_to_bv 64 0x1275c)]
    /\ rw_cells usegs mm 0x1df28 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs mm 0x1cc68 [C8 (Z_to_bv 64 0x14058); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x4e6e8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x4e6d8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs mm 0x1ded0 [C8 (Z_to_bv 64 0x1dde8)]
    /\ rw_cells usegs mm 0x1dde0 [C8 (Z_to_bv 64 0x1dcf8)]
    /\ rw_cells usegs mm 0x1cc78 [C8 (Z_to_bv 64 0x1cc28)]
    /\ rw_cells usegs mm 0x1cc28 [C8 (Z_to_bv 64 0x1dcf8)]
    (* [comment removed for export] *)
    /\ rw_cells usegs mm 0x1dcd0 [C8 (Z_to_bv 64 0x1dcd0)]
    /\ (exists reg : bool, atx_state reg mm).

  (* [comment removed for export] *)
  Definition RSTATX (mm : mem) : Prop := exists reg : bool, atx_state reg mm.

  Definition rstat_addr (a : Z) : Prop :=
    (0x2df68 <= a < 0x2df8c) \/ (0x4e290 <= a < 0x4e298) \/ (0x1ccc0 <= a < 0x1ccd0) \/ (0x1cc20 <= a < 0x1cc28)
    \/ (0x1df28 <= a < 0x1df29) \/ (0x1cc68 <= a < 0x1cc78) \/ (0x4e6d8 <= a < 0x4e6e0) \/ (0x4e6e8 <= a < 0x4e6f0)
    \/ (0x1ded0 <= a < 0x1ded8) \/ (0x1dde0 <= a < 0x1dde8) \/ (0x1cc78 <= a < 0x1cc80) \/ (0x1cc28 <= a < 0x1cc30)
    \/ (0x1dcd0 <= a < 0x1dcd8)
    \/ (0x4e070 <= a < 0x4e071) \/ (0x4e074 <= a < 0x4e07c) \/ (0x4e080 <= a < 0x4e098) \/ (0x4e190 <= a < 0x4e198) \/ (0x2df34 <= a < 0x2df35).

  #[using="Type"] Lemma atx_state_addr_rstat : forall a, atx_state_addr a -> rstat_addr a.
  Proof. intros a Ha. unfold atx_state_addr, atx_addr, PATX, PAEF_INCB in Ha. unfold rstat_addr. Local Ltac2 Set LiaHints.tbl := fun () => "0010=37684770740.7000004S2Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr; cbn in Ha; lia].

  #[using="Type"] Lemma RSTAT_agree : forall (P : Z -> Prop) m m', magree usegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & [reg A14]). unfold RSTAT.
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>37684770740.27000004S2Ha".
split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12|]. split; [tr AG HP A13|].
    exists reg. eapply atx_state_agree; [exact AG| intros a Ha; apply HP; apply atx_state_addr_rstat; exact Ha| exact A14].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="Type"] Lemma RSTAT_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ HP). intros a Ha. right; left.
    unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32162264840.12000004S2Ha".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="Type"] Lemma RSTAT_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> RSTAT m -> RSTATX m' -> RSTAT m'.
  Proof.
    intros LB SP m m' HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & _) X. unfold RSTAT.
    pose proof (pdrv_pres_agree _ _ _ _ HP) as AG.
    assert (HQ : forall a, ((0x2df68 <= a < 0x2df8c) \/ (0x4e290 <= a < 0x4e298) \/ (0x1ccc0 <= a < 0x1ccd0) \/ (0x1cc20 <= a < 0x1cc28)
    \/ (0x1df28 <= a < 0x1df29) \/ (0x1cc68 <= a < 0x1cc78) \/ (0x4e6d8 <= a < 0x4e6e0) \/ (0x4e6e8 <= a < 0x4e6f0)
    \/ (0x1ded0 <= a < 0x1ded8) \/ (0x1dde0 <= a < 0x1dde8) \/ (0x1cc78 <= a < 0x1cc80) \/ (0x1cc28 <= a < 0x1cc30)
    \/ (0x1dcd0 <= a < 0x1dcd8)) -> (fun a => rclient_addr LB SP a /\ ~ rin_ivs pstdout_ivs a) a).
    { intros a Ha. cbv beta. split.
      - right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0030>32162264840.2737684770740.2854721685382.2700000400800<S2HaS2HaS2Ha".
lia.
      - unfold pstdout_ivs, PINIT_FLAG, PAEF_INCB, PATX in *. cbn. lia. }
    Ltac tr3 AG HQ A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HQ; cbn in Ha; lia].
    split; [tr3 AG HQ A1|]. split; [tr3 AG HQ A2|]. split; [tr3 AG HQ A3|]. split; [tr3 AG HQ A4|].
    split; [tr3 AG HQ A5|]. split; [tr3 AG HQ A6|]. split; [tr3 AG HQ A7|]. split; [tr3 AG HQ A8|].
    split; [tr3 AG HQ A9|]. split; [tr3 AG HQ A10|]. split; [tr3 AG HQ A11|]. split; [tr3 AG HQ A12|]. split; [tr3 AG HQ A13|].
    exact X.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma RSTAT_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros W m m' MU WM HW. apply (RSTAT_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stdout_addr (a : Z) : Prop := (0x1dde8 <= a < 0x1ded0) \/ (0x4e700 <= a < 0x4eb00).
Definition stderr_addr (a : Z) : Prop := 0x1dcf8 <= a < 0x1dde0.
Definition trun0_addr (a : Z) : Prop :=
  (PINIT_FLAG <= a < PINIT_FLAG + 1) \/ (PGOT_FUZZ_INIT <= a < PGOT_FUZZ_INIT + 8)
  \/ (PGOT_STDERR <= a < PGOT_STDERR + 8) \/ (PSTDERR_PTR <= a < PSTDERR_PTR + 8)
  (* [comment removed for export] *)
  \/ (0x4e070 <= a < 0x4e071) \/ (0x4e074 <= a < 0x4e07c) \/ (0x4e080 <= a < 0x4e098) \/ (0x4e190 <= a < 0x4e198) \/ (0x2df34 <= a < 0x2df35).

#[using="Type"] Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  magree usegs P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>41827393648.199960875504.19 000004008S2HaS2Ha".
lia.
  - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma stderr_file0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros P m m' AG HP H. unfold stderr_file0 in *.
  eapply rw_cells_magree; [exact AG| exact H|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010=46430868464.9000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma trun_cells0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, trun0_addr a -> P a) -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A7 & A8 & AX). unfold trun_cells0.
  Ltac tr2 AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold trun0_addr; cbn in Ha; lia].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=1247325462.13000004S2Ha".
split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|]. split; [tr2 AG HP A7|]. split; [tr2 AG HP A8|].
  eapply atx_state_agree; [exact AG| | exact AX]. intros a Ha. apply HP. unfold atx_state_addr, atx_addr, PATX, PAEF_INCB in Ha. unfold trun0_addr. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma stdout_file_heap_pres : forall LB SP m m' so, rheap_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
  intros LB SP m m' so HP. apply (stdout_file_agree _ _ _ _ HP). intros a Ha. right; left.
  unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=32162264840.9000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stderr_file0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ HP). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=32162264840.8000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stderr_file0_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
  - right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020=32162264840.854721685382.8000004008S2HaS2Ha".
lia.
  - unfold stderr_addr, pstdout_ivs, PINIT_FLAG, PAEF_INCB, PATX in *. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma trun_cells0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros LB SP m m' HP. apply (trun_cells0_agree _ _ _ HP). intros a Ha. right; left.
  unfold trun0_addr, PINIT_FLAG, PGOT_FUZZ_INIT, PGOT_STDERR, PSTDERR_PTR,
    ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=32162264840.8000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono usegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
#[using="Type"] Lemma stderr_file0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_file0 m -> stderr_file0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_file0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
#[using="Type"] Lemma trun_cells0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, trun0_addr a -> outside W a) -> trun_cells0 m -> trun_cells0 m'.
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

  #[using="argv envp VSP"] Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ ATOP <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0x4f000 <= LO sp0.
  Proof. destruct VSP as ((A & B & C) & HATOP & _). unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.
  #[using="argv envp VSP"] Lemma sp_atop : ATOP = LO sp0.
  Proof. destruct VSP as (_ & HATOP & _). unfold LO. exact HATOP. Qed.

  (* [comment removed for export] *)
  #[using="HT"] Lemma pat_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo SP -> lo <= SP - 176 -> 0x4f000 <= lo -> 0 <= SP < 2^47 ->    (* [comment removed for export] *)
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    pat_exit code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 PEXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST LOS LOLO SPR (TD & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _ & DSO & AXS) HP SOF SEF MI.
    destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC).
    pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2].
    unfold pat_exit. do 33 eexists. exists m, lo, TID, (Z_to_bv 64 0x2df68), (Z_to_bv 64 0x2df68), (Z_to_bv 64 0x2df68), (Z_to_bv 64 0), CAN.
    exists cdt, thr, sec, tm1.
    split; [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "0040>30037621488.6942047885868.6942149033285.6948260482079.6900000500:00@00ES3SPRS3LOSS4LOLOS3SPR".
rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
    split; [exact FIN|]. split; [exact GCX|]. split; [exact LC|]. split; [exact DSO|]. split; [exact AXS|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [lia|]. split; [lia|]. rewrite ?unsigned_lit by lia. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="envp VSP HT"] Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (j8 : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m j8 s7v s6v s5v s4v ->
    stk usegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    evt usegs (pat_exit code s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x129e8) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros FR ST RS HP SOF SEF MI. pose proof sp_facts as SF. unfold LO in *. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    Local Ltac2 Set LiaHints.tbl := fun () => "00@0>19084113859.6224361825921.5331053909955.6133580666819.6239395881974.5739420439440.5344316162292.5348077244355.6248622319811.5950631462460.5256283539395.5958241529539.6066661700291.6167150197252.538278995601.53 8895973571.60 00000100500600700800900:00;00<00=00>00?00@00D00E00FSS2SFSSSSSSSSSSSS2SFSS".
do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x13cdc)) with (Z_to_bv 64 0x13cdc) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="argv envp VSP HT"] Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk usegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    evt usegs (pat_exit 2 s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12a74) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST RS HP SOF SEF MI. pose proof sp_facts as SF. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI].
  Qed.
End EXITS.
End CANSEC1.

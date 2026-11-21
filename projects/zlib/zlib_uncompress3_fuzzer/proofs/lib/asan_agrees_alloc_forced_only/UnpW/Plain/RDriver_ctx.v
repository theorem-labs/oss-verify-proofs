(* reloc-zl14c 6777947d839bc1c6c57754b144cb4bac *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree Startup_kit STRW_tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg F_syscalls StdioFiles Startup Exit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {rl : runLaunchT}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).

  Definition LO : Z := usp0 - 6144513.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (j8 : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells psegs mm (usp0 + -128)
      [CB 8 j8; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 PMAIN);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 PSTAGE2_RET)].

  Definition RSTAT (mm : mem) : Prop :=
    rw_cells psegs mm 0x72f68 [C8 (Z_to_bv 64 0x72f68); C8 (Z_to_bv 64 0x72f68); C8 (Z_to_bv 64 0x72f68); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells psegs mm 0x93290 [C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x21cb8 [C8 (Z_to_bv 64 0x21c20); C8 (Z_to_bv 64 0x21c18)]
    /\ rw_cells psegs mm 0x21c18 [C8 (Z_to_bv 64 0x14844)]
    /\ rw_cells psegs mm 0x22f28 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs mm 0x21c60 [C8 (Z_to_bv 64 0x19050); C8 (Z_to_bv 64 0)]      (* [comment removed for export] *)
    /\ rw_cells psegs mm 0x22cc8 [C8 (Z_to_bv 64 0x22cc8)]                     (* [comment removed for export] *)
    /\ rw_cells psegs mm 0x936e8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x936d8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells psegs mm 0x22ec8 [C8 (Z_to_bv 64 0x22de0)]
    /\ rw_cells psegs mm 0x22dd8 [C8 (Z_to_bv 64 0x22cf0)]
    /\ rw_cells psegs mm 0x21c70 [C8 (Z_to_bv 64 0x21c20)]
    /\ rw_cells psegs mm 0x21c20 [C8 (Z_to_bv 64 0x22cf0)].

  Definition rstat_addr (a : Z) : Prop :=
    (0x72f68 <= a < 0x72f8c) \/ (0x93290 <= a < 0x93298) \/ (0x21cb8 <= a < 0x21cc8) \/ (0x21c18 <= a < 0x21c20)
    \/ (0x22f28 <= a < 0x22f29) \/ (0x21c60 <= a < 0x21c70) \/ (0x936d8 <= a < 0x936e0) \/ (0x936e8 <= a < 0x936f0)
    \/ (0x22ec8 <= a < 0x22ed0) \/ (0x22dd8 <= a < 0x22de0) \/ (0x21c70 <= a < 0x21c78) \/ (0x21c20 <= a < 0x21c30)
    \/ (0x22cc8 <= a < 0x22cd0)   (* [comment removed for export] *).

  Ltac tr AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr; cbn in Ha; lia].

  Lemma RSTAT_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A6b & A7 & A8 & A9 & A10 & A11 & A12). unfold RSTAT.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A6b|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11| tr AG HP A12].
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ HP). intros a Ha. right; left.
    unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  Lemma RSTAT_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
    - right; left. unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
    - unfold rstat_addr, pstdout_ivs, PINIT_FLAG, PATX, HBUF, HBUF_N in *. cbn. lia.
  Qed.

  Lemma RSTAT_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros W m m' MU WM HW. apply (RSTAT_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stdout_addr (a : Z) : Prop := (0x22de0 <= a < 0x22ec8) \/ (0x93700 <= a < 0x93b00).
Definition stderr_addr (a : Z) : Prop := 0x22cf0 <= a < 0x22dd8.
Definition trun0_addr (a : Z) : Prop :=
  (PINIT_FLAG <= a < PINIT_FLAG + 5) \/ (PGOT_FUZZ_INIT <= a < PGOT_FUZZ_INIT + 8) \/ (PGOT_ZALLOC <= a < PGOT_ZALLOC + 16)    (* [comment removed for export] *)
  \/ atx_addr a.                                                                                                           (* [comment removed for export] *)

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

Lemma trun_cells0_agree : forall (P : Z -> Prop) m m',
  magree psegs P m m' -> (forall a, trun0_addr a -> P a) -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3 & A4). unfold trun_cells0.
  Ltac tr2 AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold trun0_addr; cbn in Ha; lia].
  split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|]. split; [tr2 AG HP A3|].
  eapply atx_cells0_agree; [exact AG| | exact A4]. intros a Ha. apply HP. unfold trun0_addr. right; right; right. exact Ha.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma harness_pres_magree : forall LB SP m m', harness_pres LB SP m m' ->
  magree psegs (fun a => rclient_addr LB SP a /\ ~ hbuf_addr a) m m'.
Proof. intros LB SP m m' H a Ha [Hc Hx]. apply H; assumption. Qed.
Lemma stdout_file_harness_pres : forall LB SP m m' so, harness_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
  intros LB SP m m' so HP. apply (stdout_file_agree _ _ _ _ (harness_pres_magree _ _ _ _ HP)). intros a Ha. split.
  - right; left. unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  - unfold stdout_addr, hbuf_addr, HBUF, HBUF_N in *. lia.
Qed.
Lemma stderr_file0_harness_pres : forall LB SP m m', harness_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ (harness_pres_magree _ _ _ _ HP)). intros a Ha. split.
  - right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  - unfold stderr_addr, hbuf_addr, HBUF, HBUF_N in *. lia.
Qed.
Lemma stderr_file0_drv_pres : forall LB SP m m', pdrv_pres LB SP m m' -> stderr_file0 m -> stderr_file0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_file0_agree _ _ _ (pdrv_pres_agree _ _ _ _ HP)). intros a Ha. split.
  - right; left. unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  - unfold stderr_addr, pstdout_ivs, PINIT_FLAG, PATX, HBUF, HBUF_N in *. cbn. lia.   (* [comment removed for export] *)
Qed.
Lemma trun_cells0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> trun_cells0 m -> trun_cells0 m'.
Proof.
  intros LB SP m m' HP. apply (trun_cells0_agree _ _ _ HP). intros a Ha. right; left.
  unfold trun0_addr, atx_addr, PATX, PATX_N, PAEF_INCB, PINIT_FLAG, PGOT_FUZZ_INIT, PGOT_ZALLOC,
    ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono psegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_file0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_file0 m -> stderr_file0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_file0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma trun_cells0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, trun0_addr a -> outside W a) -> trun_cells0 m -> trun_cells0 m'.
Proof. intros W m m' MU WM HW. apply (trun_cells0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
Lemma atx_cellsR_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> atx_cellsR m -> atx_cellsR m'.
Proof.
  intros LB SP m m' HP. apply (atx_cellsR_agree _ _ _ HP). intros a Ha. right; left.
  unfold atx_addr, PATX, PATX_N, PAEF_INCB, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma atx_cellsR_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, atx_addr a -> outside W a) -> atx_cellsR m -> atx_cellsR m'.
Proof. intros W m m' MU WM HW. apply (atx_cellsR_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma atx_cells0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> atx_cells0 m -> atx_cells0 m'.
Proof.
  intros LB SP m m' HP. apply (atx_cells0_agree _ _ _ HP). intros a Ha. right; left.
  unfold atx_addr, PATX, PATX_N, PAEF_INCB, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EXITS.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis HT : 0 < TID < 4194304.

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ ATOP <= LO sp0 /\ LO sp0 + 6144513 = usp0 /\ 0x94000 <= LO sp0.
  Proof. destruct VSP as ((A & B & C) & HATOP & _). unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.
  Lemma sp_atop : ATOP <= LO sp0.
  Proof. destruct VSP as (_ & HATOP & _). unfold LO. lia. Qed.

  (* [comment removed for export] *)
  Lemma pat_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk psegs m lo SP -> lo <= SP - 176 -> 0x94000 <= lo -> 0 <= SP < 2^47 ->    (* [comment removed for export] *)
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    atx_cells0 m \/ atx_cellsR m ->                                                   (* [comment removed for export] *)
    pat_exit code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 PEXIT) fc None m (seg_rom psegs)).
  Proof.
    intros until lo. intros ST LOS LOLO SPR (TD & EXL & GF & FA & FIN & GCX & DSO & OFL & SIN & SOU & SEU & _ & _) HP SOF SEF MI ATX.
    destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC).
    pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2].
    unfold pat_exit. do 33 eexists. exists m, lo, TID, (Z_to_bv 64 0x72f68), (Z_to_bv 64 0x72f68), (Z_to_bv 64 0x72f68), (Z_to_bv 64 0), CAN.
    exists cdt, thr, sec, tm1.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
    split; [exact FIN|]. split; [exact GCX|]. split; [exact DSO|]. split; [exact LC|]. split; [exact ATX|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [lia|]. split; [lia|]. rewrite ?unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (j8 : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m j8 s7v s6v s5v s4v ->
    stk psegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    atx_cells0 m \/ atx_cellsR m ->                                                   (* [comment removed for export] *)
    evt psegs (pat_exit code s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14ad0) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros FR ST RS HP SOF SEF MI ATX. pose proof sp_facts as SF. unfold LO in *. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x18cd4)) with (Z_to_bv 64 0x18cd4) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI| exact ATX].
  Qed.

  (* [comment removed for export] *)
  Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk psegs m (LO sp0) (usp0 + -128) ->
    RSTAT TID m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv psegs m ->
    atx_cells0 m \/ atx_cellsR m ->                                                   (* [comment removed for export] *)
    evt psegs (pat_exit 2 s)
      (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14b5c) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros ST RS HP SOF SEF MI ATX. pose proof sp_facts as SF. unfold LO in *.
    zstep. zstep.
    apply evt_done. eapply pat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI| exact ATX].
  Qed.
End EXITS.
End CANSEC1.

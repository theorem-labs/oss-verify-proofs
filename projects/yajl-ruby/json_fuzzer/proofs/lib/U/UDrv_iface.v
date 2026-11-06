(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes NodesCfg Decode Exec RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc Monad RawAlloc KLink MSuccIface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition HK_T : Type := PState -> list block -> mem -> Model -> Prop.
Definition GHOST_T : Type := PState -> Model -> Prop.
Definition HKG_T : Type := GHOST_T -> HK_T.

(* [comment removed for export] *)
Definition ps0 {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling} : PState := ps_init (reservedZ usegs).

(* [comment removed for export] *)
Definition G_fdfs (F : list (word * FdEntry)) (FS : Fs.Fs) : GHOST_T :=
  fun _ mo => m_fds mo = F /\ m_fs mo = FS.

Lemma frame_ok_G_fdfs : forall F FS, frame_ok (G_fdfs F FS).
Proof.
  intros F FS s s' mo mo' _ _ (E1 & E2 & _) [H1 H2]. unfold G_fdfs. rewrite E1, E2. auto.
Qed.

(* [comment removed for export] *)
Definition G_fs (FS : Fs.Fs) : GHOST_T := fun _ mo => m_fs mo = FS.

Lemma frame_ok_G_fs : forall FS, frame_ok (G_fs FS).
Proof. intros FS s s' mo mo' _ _ (E1 & E2 & _) H. unfold G_fs in *. rewrite E2. exact H. Qed.

Section Stmts.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PerHK.
Variable HK : HK_T.

(* [comment removed for export] *)
Definition HK_run_stmt : Prop :=
  forall s LB m mo, HK s LB m mo -> minv mo /\ m_halted mo = None /\ m_vm_lazy mo = [].

(* [comment removed for export] *)
Definition HK_ssp_stmt : Prop :=
  forall s LB m mo, HK s LB m mo ->
    rw_cells usegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)] /\ rw_cells usegs m RSSP_GUARD [C8 rc_guard]   (* [comment removed for export] *).
Definition HK_libc_head_stmt : Prop :=
  forall s LB m mo, HK s LB m mo ->
    exists cdt thr sec tm1, rw_cells usegs m RLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
End PerHK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable HKG : HKG_T.

(* [comment removed for export] *)
Definition HKG_G_stmt : Prop :=
  forall G s LB m mo, HKG G s LB m mo -> G s mo.
Definition HKG_weak_stmt : Prop :=
  forall (G G' : GHOST_T) s LB m mo, HKG G s LB m mo -> (G s mo -> G' s mo) -> HKG G' s LB m mo.

(* [comment removed for export] *)
Definition HKG_mo_stmt : Prop :=
  forall G s LB m mo n rsp mo' evs,
    HKG G s LB m mo -> lazy_free_node n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo ->
    G s mo' -> HKG G s LB m mo'.

End Stmts.

(* [comment removed for export] *)
Record drv_iface {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling} (HKG : HKG_T) : Prop := mkDrvIface {
  di_G : HKG_G_stmt HKG;
  di_weak : HKG_weak_stmt HKG;
  di_mo : HKG_mo_stmt HKG;
  di_run : forall G, HK_run_stmt (HKG G);
  di_ssp : forall G, HK_ssp_stmt (HKG G);
  di_libc_head : forall G, HK_libc_head_stmt (HKG G);
  di_perm : forall G, HK_perm_stmt (HKG G);
  di_frame : forall G, HK_frame_stmt (HKG G);
  di_blocks : forall G, HK_blocks_stmt (HKG G);
  di_malloc : forall G, frame_ok G -> rmalloc_rz_stmt (HKG G);
  di_free : forall G, frame_ok G -> rfree_rz_stmt (HKG G)
}.

(* [comment removed for export] *)
Section Proj.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Variable HKG : HKG_T.
Hypothesis DI : drv_iface HKG.

Lemma di_silent : forall G, HK_silent_stmt (HKG G).
Proof. intros G s LB m mo H. destruct (di_run HKG DI G s LB m mo H) as (_ & Hh & Hl). exact (conj Hh Hl). Qed.

(* [comment removed for export] *)
Lemma di_fdfs : forall F FS s LB m mo, HKG (G_fdfs F FS) s LB m mo -> m_fds mo = F /\ m_fs mo = FS.
Proof. intros F FS s LB m mo H. exact (di_G HKG DI _ _ _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma di_repin : forall G s LB m mo, HKG G s LB m mo -> HKG (G_fdfs (m_fds mo) (m_fs mo)) s LB m mo.
Proof. intros G s LB m mo H. eapply (di_weak HKG DI); [exact H|]. intros _. split; reflexivity. Qed.
Lemma di_pin_fds : forall FS s LB m mo, HKG (G_fs FS) s LB m mo -> HKG (G_fdfs (m_fds mo) FS) s LB m mo.
Proof. intros FS s LB m mo H. eapply (di_weak HKG DI); [exact H|]. intros E. split; [reflexivity | exact E]. Qed.
Lemma di_unpin_fds : forall F FS s LB m mo, HKG (G_fdfs F FS) s LB m mo -> HKG (G_fs FS) s LB m mo.
Proof. intros F FS s LB m mo H. eapply (di_weak HKG DI); [exact H|]. intros [_ E]. exact E. Qed.
Lemma di_fs : forall FS s LB m mo, HKG (G_fs FS) s LB m mo -> m_fs mo = FS.
Proof. intros FS s LB m mo H. exact (di_G HKG DI _ _ _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma di_mallocX : forall G, frame_ok G ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HKG G s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> HKG G s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells usegs m' A [CB (Z.to_nat n) junk]) ->
     realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RMALLOC_SYM) fc None m (seg_rom usegs)) mo) K.
Proof. intros G FG. exact (di_malloc HKG DI G FG). Qed.

Lemma di_freeX : forall G, frame_ok G ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HKG G s LB m mo -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz A ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv] ->
     rauxv_ok m' B -> rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     HKG G s' (lb_remove p LB) m' mo' ->
     realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RFREE_SYM) fc None m (seg_rom usegs)) mo) K.
Proof. intros G FG. exact (di_free HKG DI G FG). Qed.
End Proj.

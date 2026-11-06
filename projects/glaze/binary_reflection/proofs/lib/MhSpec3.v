(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition A_MALLOC : Z := 0x61c60.     (* [comment removed for export] *)
Definition A_FREE : Z := 0x61b20.       (* [comment removed for export] *)

Definition callee_saved_regs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Section Specs.
  Context {fx : FPState} {RN : run_ceil}.

  Definition regs_kept (R R' : bvmap 5 word) : Prop :=
    forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

  (* [comment removed for export] *)
  Definition ainv_t : Type := list (Z * Z) -> Z -> Z -> mem -> Model -> Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition malloc_pre (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (B C ret n sp : Z) : Prop :=
    m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\
    getr R 1 = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
    bv_unsigned (getr R 10) = n /\ 1 <= n <= MH_NMAX /\
    bv_unsigned (getr R 2) = sp /\ sp mod 16 = 0 /\ CEIL + stk <= sp /\
    getr R 4 = Z_to_bv 64 TPV /\
    (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) /\
    B + (n + MBLK) <= MH_GBUDGET /\ C + 1 <= LMAX.

  (* [comment removed for export] *)
  Definition malloc_ok (INV : ainv_t) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc : list (Z * Z)) (B C ret n sp : Z) (c' : config) : Prop :=
    exists R' M' mdl' (p : word),
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\ getr R' 10 = p /\
      bv_unsigned p mod 16 = 0 /\ blk_ok (bv_unsigned p) n /\
      (forall b m, In (b, m) Lc -> bv_unsigned p + n <= b \/ b + m <= bv_unsigned p) /\
      (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + n -> M' a <> None /\ store_ok RSEGS M' a 1%nat = true) /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      INV ((bv_unsigned p, n) :: Lc) (B + (n + MBLK)) (C + 1) M' mdl' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  (* [comment removed for export] *)
  Definition malloc_null (INV : ainv_t) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc : list (Z * Z)) (B C ret sp : Z) (c' : config) : Prop :=
    exists R' M' mdl',
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\ getr R' 10 = Z_to_bv 64 0 /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      INV Lc B C M' mdl' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  Definition malloc_cfg (R : bvmap 5 word) (M : mem) (mdl : Model) : config :=
    mkCfg (mkst R (Z_to_bv 64 A_MALLOC) M (seg_rom RSEGS)) mdl.


  (* [comment removed for export] *)
  Definition MALLOC_KATW (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      AINV Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      katw RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV stk R M mdl Lc B C ret n sp) (malloc_null AINV stk R M mdl Lc B C ret sp).


  (* [comment removed for export] *)
  Definition MALLOC_ALT_F (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      AINVF Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      kats RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV stk R M mdl Lc B C ret n sp) (malloc_null AINV stk R M mdl Lc B C ret sp).

  (* [comment removed for export] *)
  Definition MALLOC_BIG_R (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      MMAP_THRESHOLD <= n ->
      AINV_R Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      kats RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV_R stk R M mdl Lc B C ret n sp) (malloc_null AINV_R stk R M mdl Lc B C ret sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition free_pre (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc Lc' : list (Z * Z)) (B C B' C' ret sp : Z) (p : word) : Prop :=
    m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\
    getr R 1 = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
    getr R 10 = p /\
    ((p = Z_to_bv 64 0 /\ Lc' = Lc /\ B' = B /\ C' = C)
     \/ exists m L1 L2, Lc = L1 ++ (bv_unsigned p, m) :: L2 /\ Lc' = L1 ++ L2
                         /\ B' = Z.max 0 (B - (m + MBLK)) /\ C' = Z.max 0 (C - 1)) /\
    bv_unsigned (getr R 2) = sp /\ sp mod 16 = 0 /\ CEIL + stk <= sp /\
    getr R 4 = Z_to_bv 64 TPV /\
    (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true).

  Definition free_post (INV : ainv_t) (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model)
             (Lc' : list (Z * Z)) (B' C' ret sp : Z) (c' : config) : Prop :=
    exists R' M' mdl',
      c' = mkCfg (mkst R' (Z_to_bv 64 ret) M' (seg_rom RSEGS)) mdl' /\
      regs_kept R R' /\
      (forall a : word, M' a <> M a -> mh_changed stk Lc' sp a) /\
      (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M' a 1%nat = true) /\
      INV Lc' B' C' M' mdl' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

  Definition free_cfg (R : bvmap 5 word) (M : mem) (mdl : Model) : config :=
    mkCfg (mkst R (Z_to_bv 64 A_FREE) M (seg_rom RSEGS)) mdl.

  Definition FREE_KAT (stk : Z) : Prop :=
    forall R M mdl Lc Lc' B C B' C' ret sp p,
      AINV Lc B C M mdl -> free_pre stk R M mdl Lc Lc' B C B' C' ret sp p ->
      kat RSEGS (free_cfg R M mdl) (free_post AINV stk R M mdl Lc' B' C' ret sp).

  (* [comment removed for export] *)
  Definition FREE_R (stk : Z) : Prop :=
    forall R M mdl Lc Lc' B C B' C' ret sp p,
      AINV_R Lc B C M mdl -> free_pre stk R M mdl Lc Lc' B C B' C' ret sp p ->
      kat RSEGS (free_cfg R M mdl) (free_post AINV_R stk R M mdl Lc' B' C' ret sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition A_LIBC_AUXV : Z := 0xa67b8.
  Record first_env (M : mem) (mdl : Model) (auxw : Z) (avl : list (Z * Z)) : Prop := FE {
    fe_ctx : forall a, MLOCK <= a < CTX_END -> M (Z_to_bv 64 a) = None;    (* [comment removed for export] *)
    fe_auxv : cell M A_LIBC_AUXV 8 auxw;
    fe_av_rng : 0 <= auxw /\ auxw + 16 * (Z.of_nat (length avl) + 1) <= 2 ^ 63 /\ auxw mod 8 = 0;
    fe_av_keys : forall i kv, nth_error avl i = Some kv ->
                   cell M (auxw + 16 * Z.of_nat i) 8 (fst kv) /\ cell M (auxw + 16 * Z.of_nat i + 8) 8 (snd kv) /\
                   0 < fst kv < 2 ^ 64 /\ 0 <= snd kv < 2 ^ 64;
    fe_av_end : cell M (auxw + 16 * Z.of_nat (length avl)) 8 0;
    fe_av_rnd : forall kv, In kv avl -> fst kv = 25 ->
                  snd kv + 24 <= 2 ^ 63 /\ exists bs, length bs = 8%nat /\ rdn RSEGS M (Z_to_bv 64 (snd kv + 8)) 8%nat = Some bs;
    fe_pgsz : cell M A_PAGESIZE 8 4096;
    fe_locks : cell M A_NEED_LOCKS 1 0;
    fe_canary : exists v, cell M A_CANARY 8 v;
    fe_maps : vm_maps (m_vmmaps mdl) = [] /\ vm_noaccess (m_vmmaps mdl) = [];
    fe_brk : vm_brk (m_vmmaps mdl) = vm_start_brk (m_vmmaps mdl) /\
             bv_unsigned (vm_start_brk (m_vmmaps mdl)) mod 4096 = 0 /\
             IMG_HI <= bv_unsigned (vm_start_brk (m_vmmaps mdl)) /\
             bv_unsigned (vm_start_brk (m_vmmaps mdl)) + 2 ^ 31 + 8192 <= CEIL;
    fe_res : vm_reserved (m_vmmaps mdl) = segments_reserved RSEGS;
    fe_top : page_floor (alloc_top (m_vmmaps mdl)) = CEIL;
    fe_lim : VMLIM <= vm_limit (m_vmmaps mdl)
  }.


End Specs.

(* [comment removed for export] *)
Abbreviation MSTK := MSTK_M.

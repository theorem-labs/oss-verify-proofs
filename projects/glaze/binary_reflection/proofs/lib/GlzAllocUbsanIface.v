(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CTX : Z := 0xaae98.
               (* [comment removed for export] *)
Definition CTX_END : Z := CTX + 928.



        (* [comment removed for export] *)
Definition TPV : Z := 0x8ab90.                 (* [comment removed for export] *)
Definition A_ERRNO : Z := TPV - 164.



           (* [comment removed for export] *)
Definition HEAPLO : Z := 4096.
Abbreviation IMG_LO := 65536.              (* [comment removed for export] *)
Abbreviation IMG_HI := 704512.             (* [comment removed for export] *)
Abbreviation mh_run := run_ceil.

Definition mem := word -> option byte.
Definition cell (M : mem) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.
Definition LMAX : Z := 144.
Definition MSTK : Z := 2048.
Definition MH_GBUDGET : Z := 3 * 2 ^ 32.
Definition MH_NMAX : Z := 2 ^ 40.
Definition MSTK_M : Z := 1280.

Definition in_blocks (Lc : list (Z * Z)) (z : Z) : Prop := exists b n, In (b, n) Lc /\ b <= z < b + n.
Definition in_wins (Wl : list (Z * Z)) (z : Z) : Prop := exists lo hi, In (lo, hi) Wl /\ lo <= z < hi.

Section Defs.
  Context {RN : run_ceil}.
  (* [comment removed for export] *)
  Definition blk_ok (p n : Z) : Prop := HEAPLO + 16 <= p /\ p + n <= CEIL /\ (p + n <= IMG_LO \/ IMG_HI <= p).
  (* [comment removed for export] *)
  Definition mh_changed (stk : Z) (Lc : list (Z * Z)) (sp : Z) (a : word) : Prop :=
    (HEAPLO <= bv_unsigned a < CEIL /\ (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) /\ ~ in_blocks Lc (bv_unsigned a))
    \/ (sp - stk <= bv_unsigned a < sp)
    \/ (CTX <= bv_unsigned a < CTX_END) \/ (A_ERRNO <= bv_unsigned a < A_ERRNO + 4).
End Defs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_MALLOC : Z := 0x662d0.     (* [comment removed for export] *)
Definition A_FREE : Z := 0x66190.       (* [comment removed for export] *)
Definition callee_saved_regs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition ainv_t : Type := list (Z * Z) -> Z -> Z -> mem -> Model -> Prop.

Section Specs.
  Context {fx : FPState} {RN : run_ceil}.
  Variable AINV : ainv_t.

  Definition regs_kept (R R' : bvmap 5 word) : Prop :=
    forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

  Definition malloc_pre (stk : Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (B C ret n sp : Z) : Prop :=
    m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\
    getr R 1 = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
    bv_unsigned (getr R 10) = n /\ 1 <= n <= MH_NMAX /\
    bv_unsigned (getr R 2) = sp /\ sp mod 16 = 0 /\ CEIL + stk <= sp /\
    getr R 4 = Z_to_bv 64 TPV /\
    (forall a : word, sp - stk <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) /\
    B + (n + MBLK) <= MH_GBUDGET /\ C + 1 <= LMAX.

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


  Definition MALLOC_KATW (stk : Z) : Prop :=
    forall R M mdl Lc B C ret n sp,
      AINV Lc B C M mdl -> malloc_pre stk R M mdl B C ret n sp ->
      katw RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV stk R M mdl Lc B C ret n sp) (malloc_null AINV stk R M mdl Lc B C ret sp).


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

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Iface.
  Context {RN : run_ceil}.
  Variable AINV : ainv_t.
  (* [comment removed for export] *)
  Definition app_write (SWIN : list (Z * Z)) (L : list (Z * Z)) (M M' : mem) : Prop :=
    forall a : word, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None.
  (* [comment removed for export] *)
  Definition errno_write (M M' : mem) (e : Z) : Prop :=
    cell M' A_ERRNO 4 e /\
    forall a : word, M' a <> M a -> A_ERRNO <= bv_unsigned a < A_ERRNO + 4 /\ M' a <> None.

  Record ubmh (SWOK : list (Z * Z) -> Prop) : Prop := UBMH {
    um_malloc : forall fx : FPState, @MALLOC_KATW fx RN AINV MSTK_M;        (* [comment removed for export] *)
    um_free : forall fx : FPState, @FREE_KAT fx RN AINV MSTK_M;             (* [comment removed for export] *)
    um_frame : forall SWIN L B C M M' mdl,
        SWOK SWIN -> AINV L B C M mdl -> app_write SWIN L M M' -> AINV L B C M' mdl;     (* [comment removed for export] *)
    um_swok_nil : SWOK [];
    um_vm : forall L B C M mdl mdl', AINV L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINV L B C M mdl';   (* [comment removed for export] *)
    um_mono : forall L B C B' C' M mdl, AINV L B C M mdl -> B <= B' -> C <= C' -> AINV L B' C' M mdl;        (* [comment removed for export] *)
    um_zone : forall L B C M mdl b m, AINV L B C M mdl -> In (b, m) L -> blk_ok b m;                          (* [comment removed for export] *)
    um_disj : forall L B C M mdl L1 L2 b m b' m',
        AINV L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b;  (* [comment removed for export] *)
    um_perm : forall L L' B C M mdl, Permutation L L' -> AINV L B C M mdl -> AINV L' B C M mdl;              (* [comment removed for export] *)
    um_errno : forall L B C M M' mdl e, AINV L B C M mdl -> 0 <= e < 2 ^ 32 -> errno_write M M' e -> AINV L B C M' mdl   (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Lemma um_stack : forall SWOK, ubmh SWOK -> forall L B C M M' mdl,
    AINV L B C M mdl -> (forall a : word, M' a <> M a -> CEIL <= bv_unsigned a /\ M' a <> None) -> AINV L B C M' mdl.
  Proof.
    intros SWOK U L B C M M' mdl HA H. apply (um_frame SWOK U [] L B C M M' mdl (um_swok_nil SWOK U) HA).
    intros a NE. destruct (H a NE) as [X D]. split; [right; left; exact X | exact D].
  Qed.
End Iface.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Definition MSTK_SF : Z := 16.

Section SetShadow.
  Variable SEGS : list Segment.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.

  Definition setsh_post (h : option Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z))
             (B C K ret sp f m : Z) (c' : config) : Prop :=
    exists fx' R' M' mdl',
      c' = cfg SEGS fx' R' ret M' mdl' /\ FXOK fx' /\ regs_kept R R'
      /\ (forall a : word, M' a <> M a -> (sh_lo f <= u a < sh_lo f + m) \/ (sp - MSTK_SF <= u a < sp))
      /\ (forall a : word, M' a <> M a -> M' a <> None)
      /\ scratch_ok SEGS M' sp MSTK_SF
      /\ AAINVH h Lc FF B C K M' mdl'
      /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ m_halted mdl' = None.

  Definition SETSHADOW_AT (entry : Z) : Prop :=
    forall h fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp f k m : Z),
      FXOK fx -> m_halted mdl = None ->
      AAINVH h Lc FF B C K M mdl ->
      call_pre SEGS IA R M ret sp MSTK_SF ->
      In (f, k) FF ->
      u (getr R 10) = sh_lo f -> u (getr R 11) = m -> 1 <= m -> 8 * m <= FS k ->
      katD SEGS (cfg SEGS fx R entry M mdl) (setsh_post h R M mdl Lc FF B C K ret sp f m).
End SetShadow.

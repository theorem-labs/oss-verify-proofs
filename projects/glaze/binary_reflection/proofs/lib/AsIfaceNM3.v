(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsIfacePR3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ContractsPR.
  Variable SEGS : list Segment.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable fsbase : Z.

  (* [comment removed for export] *)
  Definition MALLOC_ALT_SEC (stk entry : Z) (fpcreq : bool) : Prop :=
    forall fx R M mdl Lc FF B C K ret n sp,
      malloc_pre SEGS FXOK IA AAINVH None stk fpcreq fx R M mdl Lc FF B C K ret n sp ->
      64512 < n ->
      katsD SEGS (cfg SEGS fx R entry M mdl)
            (malloc_ok SEGS FXOK IA AAINVH stk R M mdl Lc FF B C K ret n sp) (malloc_null SEGS FXOK IA AAINVH stk R M mdl Lc FF B C K ret n sp).

  (* [comment removed for export] *)
  Definition FREE_KAT_N (stk entry : Z) : Prop :=
    forall fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p,
      free_pre SEGS FXOK IA AAINVH None stk fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p ->
      katD SEGS (cfg SEGS fx R entry M mdl) (free_post SEGS FXOK IA AAINVH None stk R M mdl Lc' FF B' C' K' ret sp).

  Lemma FREE_KAT_N_of_KAT : forall stk entry, FREE_KAT SEGS FXOK IA AAINVH stk entry -> FREE_KAT_N stk entry.
  Proof. intros stk entry FK fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE. exact (FK None fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE). Qed.

  (* [comment removed for export] *)
  Record as_contracts_pr : Prop := ASCP {
    ascp_malloc_sec : MALLOC_ALT_SEC MSTK_A (ia_malloc IA) true;
    ascp_malloc_sec_thunk : MALLOC_ALT_SEC MSTK_A (ia_malloc_thunk IA) true;
    ascp_free : FREE_KAT_N MSTK_A (ia_free IA);
    ascp_free_thunk : FREE_KAT_N MSTK_A (ia_free_thunk IA);
    ascp_opdel : FREE_KAT_N MSTK_A (ia_opdel IA);                 (* [comment removed for export] *)
    ascp_opdel_sz : FREE_KAT_N MSTK_A (ia_opdel_sz IA);
    ascp_stkmal : forall k, 0 <= k <= KMAXCLASS -> STKMAL SEGS FXOK IA AAINVH fsbase k;
    ascp_fakerel : FAKEREL SEGS FXOK IA AAINVH;
    ascp_memcpy_icpt : MEMCPY_AT SEGS FXOK IA AAINVH (ia_memcpy_icpt IA);   ascp_asan_memcpy : MEMCPY_AT SEGS FXOK IA AAINVH (ia_asan_memcpy IA);
    ascp_memset_icpt : MEMSET_AT SEGS FXOK IA AAINVH (ia_memset_icpt IA);   ascp_asan_memset : MEMSET_AT SEGS FXOK IA AAINVH (ia_asan_memset IA);
    ascp_memmove_icpt : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_memmove_icpt IA); ascp_asan_memmove : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_asan_memmove IA);
    ascp_strlen : STRLEN_AT SEGS FXOK IA AAINVH (ia_strlen_icpt IA) }.
End ContractsPR.
End AsIfacePR3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 AsIfacePR3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ContractsNM.
  Variable SEGS : list Segment.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable IA : as_addrs.
  Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Z -> Prop.
  Variable fsbase : Z.

  Record as_contracts_n : Prop := ASCN {
    ascn_weaken : forall h Lc FF B C K M mdl, AAINVH None Lc FF B C K M mdl -> AAINVH h Lc FF B C K M mdl;
    ascn_malloc : MALLOC_KATW SEGS FXOK IA AAINVH MSTK_A (ia_malloc IA) true;
    ascn_malloc_thunk : MALLOC_KATW SEGS FXOK IA AAINVH MSTK_A (ia_malloc_thunk IA) true;
    ascn_malloc_alt : MALLOC_ALT SEGS FXOK IA AAINVH FRESH MSTK_A (ia_malloc IA) true;
    ascn_malloc_alt_thunk : MALLOC_ALT SEGS FXOK IA AAINVH FRESH MSTK_A (ia_malloc_thunk IA) true;
    ascn_free : FREE_KAT_N SEGS FXOK IA AAINVH MSTK_A (ia_free IA);
    ascn_free_thunk : FREE_KAT_N SEGS FXOK IA AAINVH MSTK_A (ia_free_thunk IA);
    ascn_opdel : FREE_KAT_N SEGS FXOK IA AAINVH MSTK_A (ia_opdel IA);
    ascn_opdel_sz : FREE_KAT_N SEGS FXOK IA AAINVH MSTK_A (ia_opdel_sz IA);
    ascn_stkmal : forall k, 0 <= k <= KMAXCLASS -> STKMAL SEGS FXOK IA AAINVH fsbase k;
    ascn_fakerel : FAKEREL SEGS FXOK IA AAINVH;
    ascn_memcpy_icpt : MEMCPY_AT SEGS FXOK IA AAINVH (ia_memcpy_icpt IA);   ascn_asan_memcpy : MEMCPY_AT SEGS FXOK IA AAINVH (ia_asan_memcpy IA);
    ascn_memset_icpt : MEMSET_AT SEGS FXOK IA AAINVH (ia_memset_icpt IA);   ascn_asan_memset : MEMSET_AT SEGS FXOK IA AAINVH (ia_asan_memset IA);
    ascn_memmove_icpt : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_memmove_icpt IA); ascn_asan_memmove : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_asan_memmove IA);
    ascn_strlen : STRLEN_AT SEGS FXOK IA AAINVH (ia_strlen_icpt IA) }.


  Record as_contracts_nm : Prop := ASCNM {
    ascnm_free : FREE_KAT SEGS FXOK IA AAINVH MSTK_A (ia_free IA);
    ascnm_free_thunk : FREE_KAT SEGS FXOK IA AAINVH MSTK_A (ia_free_thunk IA);
    ascnm_opdel : FREE_KAT SEGS FXOK IA AAINVH MSTK_A (ia_opdel IA);
    ascnm_opdel_sz : FREE_KAT SEGS FXOK IA AAINVH MSTK_A (ia_opdel_sz IA);
    ascnm_stkmal : forall k, 0 <= k <= KMAXCLASS -> STKMAL SEGS FXOK IA AAINVH fsbase k;
    ascnm_fakerel : FAKEREL SEGS FXOK IA AAINVH;
    ascnm_memcpy_icpt : MEMCPY_AT SEGS FXOK IA AAINVH (ia_memcpy_icpt IA);   ascnm_asan_memcpy : MEMCPY_AT SEGS FXOK IA AAINVH (ia_asan_memcpy IA);
    ascnm_memset_icpt : MEMSET_AT SEGS FXOK IA AAINVH (ia_memset_icpt IA);   ascnm_asan_memset : MEMSET_AT SEGS FXOK IA AAINVH (ia_asan_memset IA);
    ascnm_memmove_icpt : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_memmove_icpt IA); ascnm_asan_memmove : MEMMOVE_AT SEGS FXOK IA AAINVH (ia_asan_memmove IA);
    ascnm_strlen : STRLEN_AT SEGS FXOK IA AAINVH (ia_strlen_icpt IA) }.

End ContractsNM.

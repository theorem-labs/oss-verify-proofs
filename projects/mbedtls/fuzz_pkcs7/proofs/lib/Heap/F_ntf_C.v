(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B F_ntf_A F_ntf_B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac meta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : mrep st' mX)
      by (eapply mrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; tauto]);
    clear MUq WMq CH end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_ntf_C () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"].


(* [comment removed for export] *)
Definition qa_facts (st : mstate) (sc : Z) (g : aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_F_ntf_C ()) "Phead,$0.P,(1.$2.(3.O3.O2.)(4.$0.R1.))P,(5.(1.$0.R2.O1.))(6.(7.O3.R3.)(8.$0.Lpv,$0.(6.(1.$2.(9.(:.O3.R4.))(4.$0.R1.))(6.(5.(1.$0.R1.O1.))(7.O3.R1.)))))")
(* [comment removed for export] *).

Definition qpath_st (st : mstate) (sc : Z) (g : aptr) : mstate :=
  if optr_eqb (active st sc) (Some g) then st else queue_st (LActive sc) g st.



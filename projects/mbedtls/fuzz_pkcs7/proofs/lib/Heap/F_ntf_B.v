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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_ntf_B () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"].


(* [comment removed for export] *)
Definition fm_facts (st : mstate) (g : aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_F_ntf_B ()) "Phead,$0.P,(1.$2.(3.(4.O2.))(5.$0.R1.))(6.(7.(1.$0.R2.O1.))(6.(8.O2.R2.)(9.$0.Lpv,$0.(6.(1.$2.(:.(;.O2.R3.))(5.$0.R1.))(6.(7.(1.$0.R1.O1.))(8.O2.R1.))))))")
(* [comment removed for export] *).

Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac meta_open cq MUq WMq :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
    pose proof (wmono_refl asegs mX) as WMq end.

(* [comment removed for export] *)
Ltac meta_close MRold MSq MUq WMq CH st' MRnew :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : mrep st' mX)
      by (eapply mrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
    clear MUq WMq CH end.

(* [comment removed for export] *)
Ltac meta_chunk MR MSq CH :=
  pose proof (mrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
  rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.



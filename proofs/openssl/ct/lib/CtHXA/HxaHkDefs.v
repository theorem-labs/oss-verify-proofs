(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition hkA_malloc : @hook xcd := hk_at PC_MALLOC (hkx_malloc ctasegs TPV T_STK RT_STACK TRACES T_S0 IMG_TOP).
Definition hkA_realloc : @hook xcd := hk_at PC_REALLOC (hkx_realloc ctasegs TPV T_STK RT_STACK TRACES T_S0 IMG_TOP).
Definition hkA_free : @hook xcd := hk_at PC_FREE (hkx_free_null ctasegs TPV T_STK RT_STACK TRACES T_S0 IMG_TOP).
Definition hkA_memset : @hook xcd := hk_at PC_ASAN_MEMSET (hkx_memset8 ctasegs TPV T_STK RT_STACK).
Definition hkA_stack_malloc0 : @hook xcd := hk_at PC_STACK_MALLOC0 (hkx_stack_malloc0 TPV T_STK RT_STACK).
Definition hkA_release : @hook xcd := hkx_release ctasegs SHBW.
Definition hkA_stack_malloc1 : @hook xcd := hk_at PC_STACK_MALLOC1 (hkx_stack_malloc1 TPV T_STK RT_STACK).
Definition hkA_posix_memalign : @hook xcd := hk_at PC_POSIX_MEMALIGN (hkx_posix_memalign ctasegs TPV T_STK RT_STACK TRACES T_S0 IMG_TOP).
Definition hkA_memcpy : @hook xcd := hk_at PC_ASAN_MEMCPY (hkx_memcpy ctasegs TPV T_STK RT_STACK GDESC).
Definition hkA_strlen : @hook xcd := hk_at PC_STRLEN (hkx_strlen ctasegs TPV T_STK RT_STACK GDESC).

Definition hooksA : list (@hook xcd) :=
  [hkA_malloc; hkA_realloc; hkA_free; hkA_memset; hkA_stack_malloc0; hkA_release; hkA_stack_malloc1; hkA_posix_memalign; hkA_memcpy; hkA_strlen].   (* [comment removed for export] *)

Definition ixset (tr : itrie nat) (pcs : list int) (i : nat) : itrie nat := fold_left (fun tr p => iset ICD tr (ic_key (W false p)) i) pcs tr.
(* [comment removed for export] *)
Definition hookixA : itrie nat :=
  let tr := iset ICD IEmpty (ic_key PC_MALLOC) 0%nat in
  let tr := iset ICD tr (ic_key PC_REALLOC) 1%nat in
  let tr := iset ICD tr (ic_key PC_FREE) 2%nat in
  let tr := iset ICD tr (ic_key PC_ASAN_MEMSET) 3%nat in
  let tr := iset ICD tr (ic_key PC_STACK_MALLOC0) 4%nat in
  let tr := iset ICD tr (ic_key PC_STACK_MALLOC1) 6%nat in
  let tr := iset ICD tr (ic_key PC_POSIX_MEMALIGN) 7%nat in
  let tr := iset ICD tr (ic_key PC_ASAN_MEMCPY) 8%nat in
  let tr := iset ICD tr (ic_key PC_STRLEN) 9%nat in
  ixset (ixset (ixset tr REL0_PCS 5%nat) REL1_PCS 5%nat) REL2_PCS 5%nat.

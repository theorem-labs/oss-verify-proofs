(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep MallocKit_B.
From Stdlib Require Lia. 
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls F_malloc_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module F_ntf_B.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition fm_facts (st : mstate) (g : aptr) : Prop :=
  forall head, c_free_meta_head (ctx st) = Some head ->
    head <> g /\ meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End F_ntf_B.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition aor_st (st : mstate) (g : aptr) (i : Z) : mstate :=
  upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

(* [comment removed for export] *)
Definition act_st (st : mstate) (a : aptr) (act : Z) : mstate :=
  upd_meta a (fun r => m_set_avail (Z.land (m_freed r) act) (m_set_freed (Z.ldiff (m_freed r) act) r)) st.
Definition act_of (st : mstate) (a : aptr) : Z :=
  match m_mem (get_meta_rec st a) with
  | Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (get_meta_rec st a))))
  | None => 0 end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition deq_mid (h : lhead) (g : aptr) (st : mstate) : mstate :=
  let mr := get_meta_rec st g in
  if negb (optr_eqb (m_next mr) (Some g)) then
    let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end in
    let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end in
    if optr_eqb (get_head st2 h) (Some g) then set_head h (m_next mr) st2 else st2
  else set_head h None st.
Definition clr_links (r : meta) : meta := m_set_prev None (m_set_next None r).
Lemma dequeue_mid : forall h g st, dequeue h g st = upd_meta g clr_links (deq_mid h g st).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition pd_st (an : bool) (st1 : mstate) (sc : Z) : mstate :=
  if an then match active st1 sc with Some a => act_st st1 a (act_of st1 a) | None => st1 end else st1.

(* [comment removed for export] *)
Definition grp_del (st : mstate) (g p : aptr) : mstate :=
  del_slots p (get_stride (get_meta_rec st g)) (m_last_idx (get_meta_rec st g) + 1) (del_group p st).
Definition fg_usage_st (st : mstate) (g : aptr) : mstate :=
  let mr := get_meta_rec st g in
  if m_sizeclass mr <? 48 then set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st else st.

End ACeilS1.

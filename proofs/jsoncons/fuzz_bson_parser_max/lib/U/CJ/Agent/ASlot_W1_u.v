(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_enframe_u MallocTree_u MallocKit_A_u MallocFacts_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition ta_avz (st3 : mstate) (m3 : aptr) : Malloc.M R :=
  activate_group m3 st3 (fun st4 mask =>
    guard 40 (negb (mask =? 0)) (
      ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail.

(* [comment removed for export] *)
Definition ta_act (st2 : mstate) (m2 : aptr) (mask : Z) : Malloc.M R :=
  let mr2 := get_meta_rec st2 m2 in
  let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
  let '(st3, m3) :=
    if Z.land mask (mask_upto gai) =? 0 then
      if negb (optr_eqb (m_next mr2) (Some m2)) then
        match m_next mr2 with
        | Some mn => (set_active sc (Some mn) st2, mn)
        | None => (st2, m2)
        end
      else
        let cnt := gai + 2 in
        let size := size_class (m_sizeclass mr2) * UNIT in
        let span := UNIT + size * cnt in
        let cnt := span_loop 300%nat cnt span size in
        let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
        match m_mem mr2 with
        | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
        | None => (st2, m2)
        end
    else (st2, m2) in
  ta_avz st3 m3.

(* [comment removed for export] *)
Definition ta_m (st1 : mstate) (m1 : aptr) : Malloc.M R :=
  let mask := m_freed (get_meta_rec st1 m1) in
  let '(st2, m2, mask) :=
    let mr := get_meta_rec st1 m1 in
    if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
      match m_next mr with
      | Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
      | None => (st1, m1, mask)
      end
    else (st1, m1, mask) in
  ta_act st2 m2 mask.

(* [comment removed for export] *)
Lemma try_avail_eq st :
  try_avail sc st k bail =
  match active st sc with
  | None => k st 0
  | Some m =>
    if negb (m_avail (get_meta_rec st m) =? 0) then ta_fin st m (m_avail (get_meta_rec st m)) k else
    let step1 : option (mstate * aptr) :=
      if m_freed (get_meta_rec st m) =? 0 then
        let st1 := dequeue (LActive sc) m st in
        match active st1 sc with None => None | Some m1 => Some (st1, m1) end
      else
        match m_next (get_meta_rec st m) with
        | Some m1 => Some (set_active sc (Some m1) st, m1)
        | None => None
        end in
    match step1 with
    | None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
              else SVis (EUndef UBadPtr) (fun _ => bail)
    | Some (st1, m1) => ta_m st1 m1
    end
  end.
Proof. reflexivity. Qed.
End TA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_grp (st1 : mstate) : Malloc.M R :=
  alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
    match go with
    | None => k st2 (-1)
    | Some g =>
      let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
      queue (LActive sc) g st3 (fun st4 => k st4 0) bail
    end) bail.

Definition as_k (st1 : mstate) (first : Z) : Malloc.M R :=
  if negb (first =? 0) then k st1 (ctz32 first) else as_grp st1.

Lemma alloc_slot_S st : alloc_slot lay (S f) st sc req k bail = try_avail sc st as_k bail.
Proof. reflexivity. Qed.
End AS.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
  end.

(* [comment removed for export] *)
Definition span_fn (sc cnt : Z) : bool :=
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16).
Definition span_chk (sc : Z) : bool := forallb (span_fn sc) (zseq 2 32).

Lemma span_chk_true : forallb span_chk (zseq 1 47) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma span_fn_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 -> span_fn sc cnt = true.
Proof.
  intros Hsc Hc.
  pose proof (forallb_zseq span_chk 1 47 sc span_chk_true ltac:(lia) ltac:(lia)) as X. unfold span_chk in X.
  exact (forallb_zseq (span_fn sc) 2 32 cnt X ltac:(lia) ltac:(lia)).
Qed.

Lemma span_exit_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 ->
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16) = true.
Proof. intros Hsc Hc. exact (span_fn_ok sc cnt Hsc Hc). Qed.
End CEIL_WRAP_1.


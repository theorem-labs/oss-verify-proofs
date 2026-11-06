(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocKit_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
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
Definition deq_mid (h : lhead) (g : aptr) (st : mstate) : mstate :=
  let mr := get_meta_rec st g in
  if negb (optr_eqb (m_next mr) (Some g)) then
    let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end in
    let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end in
    if optr_eqb (get_head st2 h) (Some g) then set_head h (m_next mr) st2 else st2
  else set_head h None st.
Definition clr_links (r : meta) : meta := m_set_prev None (m_set_next None r).
Lemma dequeue_mid : forall h g st, dequeue h g st = upd_meta g clr_links (deq_mid h g st).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.

(* [comment removed for export] *)
Definition pd_st (an : bool) (st1 : mstate) (sc : Z) : mstate :=
  if an then match active st1 sc with Some a => act_st st1 a (act_of st1 a) | None => st1 end else st1.

(* [comment removed for export] *)
Definition grp_del (st : mstate) (g p : aptr) : mstate :=
  del_slots p (get_stride (get_meta_rec st g)) (m_last_idx (get_meta_rec st g) + 1) (del_group p st).
Definition fg_usage_st (st : mstate) (g : aptr) : mstate :=
  let mr := get_meta_rec st g in
  if m_sizeclass mr <? 48 then set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st else st.
End WithCeiling0.

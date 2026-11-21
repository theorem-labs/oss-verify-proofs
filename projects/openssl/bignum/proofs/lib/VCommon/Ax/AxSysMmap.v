(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the place_declined_b premise of mmap, Linux's mmap placement and mmap's MAP_FIXED overflow arm). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxAcct.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition null_ok (m : Model) (nZ : Z) (a : word) : Prop :=
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps m)
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.

Definition null_rw_model (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n (with_vmmaps (grant_maps m a n (vm_noaccess (m_vmmaps m))) m).

Definition null_na_model (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n (with_vmmaps (grant_maps m a n ((a, n) :: vm_noaccess (m_vmmaps m))) m).

Lemma errno_in_enomem (r : word) : errno_ret_in mmap_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros H. apply errno_ret_in_true in H as [e [[<-|[]] ->]]. reflexivity. Qed.

(* 727298f3 (#146).  The decline's FIRST conjunct is [negb (hint_address hint =? 0)]
   (Sys/Mm/Mmap.v:1376), so a NULL hint is undeclined by computation alone -- nothing
   about [nZ], the ledger or the guard band is needed.  Discharge through this lemma and
   never through [alloc_top]: #146 turned that bound from [alloc_top h] into
   [alloc_top h - stack_guard_gap_bytes kb], and a discharge aimed at the first conjunct
   survives the next such change.  Name agreed across the OSSV-266 unit owners. *)
Lemma place_declined_b_null (kb : KernelBuild) (h : VmMaps) (nZ : Z) :
  place_declined_b kb h (Z_to_bv 64 0) nZ = false.
Proof.
  unfold place_declined_b.
  assert (Hz : hint_address (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
  rewrite Hz. reflexivity.
Qed.

Section Null.
Variables addr len prot flags fd off : word.
Hypothesis Hoff : mmap_off_aligned_b off = true.
Hypothesis Hanon : mmap_anon_b flags = true.
Hypothesis Hlen : w_is0 len = false.

Local Notation nZ := (page_round_up_Z (bv_unsigned len)).
Local Notation n := (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).

Lemma chk_mmap_null_rw (eff : SyscallEffect) (m m' : Model) (evs : list event) :
  mmap_modeled_b prot flags off = true ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  evs = [] /\ ((eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
               \/ exists a, null_ok m nZ a /\ mmap_noreserve_backed_ok flags m nZ = true
                            /\ eff = mkEffect a [] [(a, n)] /\ m' = null_rw_model flags a n m).
Proof.
  (* 727298f3 (#144 + #146): [check_mmap] now answers [CheckUnmodeled] for a hint the
     model declines, ahead of the [match eff] -- Checks/Sys/Mm/Mmap.v:107 in the
     [mmap_modeled_b] arm.  This lemma CONSUMES a [CheckOk], so it needs no premise and
     keeps its full strength: the decline branch dies by discrimination. *)
  intros Hmod H. unfold check_mmap, check_mmap_fixed_overflow in H. rewrite Hoff, Hanon, Hlen, Hmod in H. cbn [negb] in H.
  destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr nZ) eqn:Edecl;
    [cbv beta iota zeta in H; discriminate H|].
  cbv beta iota zeta in H.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate H]. destruct us; [|discriminate H].
  destruct cs; [|discriminate H]. destruct ci; [|discriminate H].
  destruct (errno_ret_in mmap_errnos r) eqn:Ee.
  - destruct zs; [|discriminate H]. injection H as <- <-. split; [reflexivity|]. left.
    rewrite (errno_in_enomem r Ee). split; reflexivity.
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate H] end.
    injection H as <- <-. split; [reflexivity|]. right. exists r.
    apply andb_prop in Ec as [Ec E6]. apply andb_prop in Ec as [Ep E5].
    destruct (mmap_grant_len_ok len Hlen) as [Hp1 Hp2].
    destruct (linux_place_is_admissible _ _ _ _ _ Hp1 Hp2 Ep) as (E1 & E2 & E3 & E4).
    apply listNN_eqb_eq in E6. subst zs.
    split; [repeat split; assumption|]. split; [exact E5|]. split; reflexivity.
Qed.

Lemma chk_mmap_null_na (eff : SyscallEffect) (m m' : Model) (evs : list event) :
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = true ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  evs = [] /\ ((eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
               \/ exists a, null_ok m nZ a /\ eff = mkEffectU a [] [] [(a, n)] [] [] /\ m' = null_na_model flags a n m).
Proof.
  (* The same decline, in the [mmap_noaccess_b] arm: Checks/Sys/Mm/Mmap.v:135.  Consumer,
     so again no premise -- see [chk_mmap_null_rw]. *)
  intros Hmod Hna H. unfold check_mmap, check_mmap_fixed_overflow in H. rewrite Hoff, Hanon, Hlen, Hmod, Hna in H. cbn [negb] in H.
  destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr nZ) eqn:Edecl;
    [cbv beta iota zeta in H; discriminate H|].
  cbv beta iota zeta in H.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate H]. destruct zs; [|discriminate H].
  destruct cs; [|discriminate H]. destruct ci; [|discriminate H].
  destruct (errno_ret_in mmap_errnos r) eqn:Ee.
  - destruct us; [|discriminate H]. injection H as <- <-. split; [reflexivity|]. left.
    rewrite (errno_in_enomem r Ee). split; reflexivity.
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate H] end.
    injection H as <- <-. split; [reflexivity|]. right. exists r.
    apply andb_prop in Ec as [Ep E5].
    destruct (mmap_grant_len_ok len Hlen) as [Hp1 Hp2].
    destruct (linux_place_is_admissible _ _ _ _ _ Hp1 Hp2 Ep) as (E1 & E2 & E3 & E4).
    apply listNN_eqb_eq in E5. subst us.
    split; [repeat split; assumption|]. split; reflexivity.
Qed.

Lemma null_ok_not_errno (m : Model) (a : word) : 0 <= nZ -> null_ok m nZ a -> errno_ret_in mmap_errnos a = false.
Proof.
  intros Hn (_ & _ & H3 & _). apply errno_ret_in_below; [reflexivity|].
  pose proof (alloc_top_room (m_vmmaps m)) as R. unfold stack_max_size in R. lia.
Qed.

(* 727298f3: a lemma that PRODUCES a [CheckOk] is false without the decline premise --
   the model answers [CheckUnmodeled] for a declined hint whatever the effect is.  This
   is #144's own choice in [theories/Common/]: the obligation is a premise, visible at
   every call site, not a conjunct hidden in a unit-local grant predicate. *)
Lemma chk_mmap_grant_rw (m : Model) (a : word) :
  mmap_modeled_b prot flags off = true -> 0 <= nZ -> null_ok m nZ a -> mmap_noreserve_backed_ok flags m nZ = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ a = true ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr nZ = false ->
  check_mmap addr len prot flags fd off (mkEffect a [] [(a, n)]) m = CheckOk (null_rw_model flags a n m) [].
Proof.
  intros Hmod Hn Hok Hb Hp Hdecl. unfold check_mmap, check_mmap_fixed_overflow. rewrite Hoff, Hanon, Hlen, Hmod. cbn [negb].
  rewrite Hdecl. cbv beta iota zeta.
  rewrite (null_ok_not_errno m a Hn Hok), Hp, Hb.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma chk_mmap_grant_na (m : Model) (a : word) :
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = true -> 0 <= nZ -> null_ok m nZ a ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ a = true ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr nZ = false ->
  check_mmap addr len prot flags fd off (mkEffectU a [] [] [(a, n)] [] []) m = CheckOk (null_na_model flags a n m) [].
Proof.
  intros Hmod Hna Hn Hok Hp Hdecl. unfold check_mmap, check_mmap_fixed_overflow. rewrite Hoff, Hanon, Hlen, Hmod, Hna. cbn [negb].
  rewrite Hdecl. cbv beta iota zeta.
  rewrite (null_ok_not_errno m a Hn Hok), Hp.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

End Null.

Lemma chk_mmap_null_modeled (addr len prot flags fd off : word) (eff : SyscallEffect) (m : Model) :
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = true \/ (mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = true) ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = false ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  (* A no-unmodeled lemma is a producer in the sense that matters here: the decline arm
     IS [CheckUnmodeled], so without the premise the statement is false. *)
  intros Hoff Hanon Hlen Hsh Hdecl. unfold check_mmap, check_mmap_fixed_overflow. rewrite Hoff, Hanon, Hlen. cbn [negb]. cbv beta iota zeta.
  destruct Hsh as [Hmod|[Hmod Hna]].
  - rewrite Hmod, Hdecl. cbv beta iota zeta.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
    match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
  - rewrite Hmod, Hna, Hdecl. cbv beta iota zeta.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
    match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
Qed.

Lemma refusal_enomem : ret_in_errnos [ENOMEM] (errno_ret ENOMEM) = true.
Proof. reflexivity. Qed.

Lemma refusal_below (r : word) : bv_unsigned r <= two_pow_64 - 4096 -> ret_in_errnos [ENOMEM] r = false.
Proof. intros H. exact (errno_ret_in_below [ENOMEM] r eq_refl H). Qed.

Lemma materialize_nil (m : Model) : materialize_model_accesses m [] = Some m.
Proof. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma with_mmap_backing_fields (flags a n : word) (m : Model) :
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m /\ m_halted (with_mmap_backing flags a n m) = m_halted m
  /\ m_fds (with_mmap_backing flags a n m) = m_fds m /\ m_fs (with_mmap_backing flags a n m) = m_fs m
  /\ m_tid (with_mmap_backing flags a n m) = m_tid m
  /\ m_vm_lazy (with_mmap_backing flags a n m) = (if mmap_noreserve_b flags then lazy_interior a n ++ m_vm_lazy m else m_vm_lazy m).
Proof. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); repeat split; reflexivity. Qed.


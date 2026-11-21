(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (imports Placement; the mmap check lemmas take the place_declined_b premise of mmap and Linux's placement linux_place_is; check_mmap is unfolded with its MAP_FIXED 64-bit overflow arm, check_mmap_fixed_overflow). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition null_ok (m : Model) (nZ : Z) (a : word) : Prop :=
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps m)
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.

(* [comment removed for export] *)
Definition null_rw_model (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n (with_vmmaps (grant_maps m a n (vm_noaccess (m_vmmaps m))) m).

Definition null_na_model (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n (with_vmmaps (grant_maps m a n ((a, n) :: vm_noaccess (m_vmmaps m))) m).

Lemma errno_in_enomem (r : word) : errno_ret_in mmap_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros H. apply errno_ret_in_true in H as [e [[<-|[]] ->]]. reflexivity. Qed.

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
  intros Hmod H. unfold check_mmap, check_mmap_fixed_overflow in H. rewrite Hoff, Hanon, Hlen, Hmod in H. cbn [negb] in H. cbv beta iota zeta in H.
  (* LPS 727298f3 (#144, #146): [check_mmap] declines a hinted anonymous
     placement whose range ends in the band Linux may refuse, ahead of the
     [match] on the effect.  A [CheckOk] therefore says the call was NOT
     declined; discharge the declined arm and carry on. *)
  destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr nZ) eqn:Epd; [discriminate H|].
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
  intros Hmod Hna H. unfold check_mmap, check_mmap_fixed_overflow in H. rewrite Hoff, Hanon, Hlen, Hmod, Hna in H. cbn [negb] in H. cbv beta iota zeta in H.
  destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr nZ) eqn:Epd; [discriminate H|].
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

(* [comment removed for export] *)
Lemma null_ok_not_errno (m : Model) (a : word) : 0 <= nZ -> null_ok m nZ a -> errno_ret_in mmap_errnos a = false.
Proof.
  intros Hn (_ & _ & H3 & _). apply errno_ret_in_below; [reflexivity|].
  pose proof (alloc_top_room (m_vmmaps m)) as R. unfold stack_max_size in R. lia.
Qed.

(* [Hpd] is new at LPS 727298f3: [check_mmap] answers [CheckUnmodeled] for a
   hinted placement the model declines (#144, #146), so a lemma that PRODUCES
   a [CheckOk] must say the call was not declined.  Its callers discharge it
   by computation, the hint being NULL. *)
Lemma chk_mmap_grant_rw (m : Model) (a : word) :
  mmap_modeled_b prot flags off = true -> 0 <= nZ -> null_ok m nZ a -> mmap_noreserve_backed_ok flags m nZ = true ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr nZ = false ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ a = true ->
  check_mmap addr len prot flags fd off (mkEffect a [] [(a, n)]) m = CheckOk (null_rw_model flags a n m) [].
Proof.
  intros Hmod Hn Hok Hb Hpd Hp. unfold check_mmap, check_mmap_fixed_overflow. rewrite Hoff, Hanon, Hlen, Hmod. cbn [negb]. cbv beta iota zeta.
  rewrite Hpd. cbv iota.
  rewrite (null_ok_not_errno m a Hn Hok), Hp, Hb.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma chk_mmap_grant_na (m : Model) (a : word) :
  mmap_modeled_b prot flags off = false -> mmap_noaccess_b prot flags off = true -> 0 <= nZ -> null_ok m nZ a ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr nZ = false ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) addr nZ a = true ->
  check_mmap addr len prot flags fd off (mkEffectU a [] [] [(a, n)] [] []) m = CheckOk (null_na_model flags a n m) [].
Proof.
  intros Hmod Hna Hn Hok Hpd Hp. unfold check_mmap, check_mmap_fixed_overflow. rewrite Hoff, Hanon, Hlen, Hmod, Hna. cbn [negb]. cbv beta iota zeta.
  rewrite Hpd. cbv iota.
  rewrite (null_ok_not_errno m a Hn Hok), Hp.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

End Null.

(* [comment removed for export] *)
Lemma chk_mmap_null_modeled (addr len prot flags fd off : word) (eff : SyscallEffect) (m : Model) :
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true -> w_is0 len = false ->
  mmap_modeled_b prot flags off = true \/ (mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = true) ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = false ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros Hoff Hanon Hlen Hsh Hpd. unfold check_mmap, check_mmap_fixed_overflow. rewrite Hoff, Hanon, Hlen. cbn [negb]. cbv beta iota zeta.
  destruct Hsh as [Hmod|[Hmod Hna]].
  - rewrite Hmod, Hpd. cbv iota. destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
    match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
  - rewrite Hmod, Hna, Hpd. cbv iota. destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
    match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_enomem : ret_in_errnos [ENOMEM] (errno_ret ENOMEM) = true.
Proof. reflexivity. Qed.

Lemma refusal_below (r : word) : bv_unsigned r <= two_pow_64 - 4096 -> ret_in_errnos [ENOMEM] r = false.
Proof. intros H. exact (errno_ret_in_below [ENOMEM] r eq_refl H). Qed.

(* [comment removed for export] *)
Lemma materialize_nil (m : Model) : materialize_model_accesses m [] = Some m.
Proof. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma grant_accesses_rw (a n : word) : syscall_effect_accesses (mkEffect a [] [(a, n)]) = [].
Proof. reflexivity. Qed.

Lemma grant_accesses_na (a n : word) : syscall_effect_accesses (mkEffectU a [] [] [(a, n)] [] []) = [].
Proof. reflexivity. Qed.

Lemma ret_accesses (r : word) : syscall_effect_accesses (mkEffect r [] []) = [].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_mmap_backing_fields (flags a n : word) (m : Model) :
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m /\ m_halted (with_mmap_backing flags a n m) = m_halted m
  /\ m_fds (with_mmap_backing flags a n m) = m_fds m /\ m_fs (with_mmap_backing flags a n m) = m_fs m
  /\ m_tid (with_mmap_backing flags a n m) = m_tid m
  /\ m_vm_lazy (with_mmap_backing flags a n m) = (if mmap_noreserve_b flags then lazy_interior a n ++ m_vm_lazy m else m_vm_lazy m).
Proof. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); repeat split; reflexivity. Qed.

Lemma with_vmmaps_fields (h : VmMaps) (m : Model) :
  m_vmmaps (with_vmmaps h m) = h /\ m_halted (with_vmmaps h m) = m_halted m /\ m_fds (with_vmmaps h m) = m_fds m
  /\ m_fs (with_vmmaps h m) = m_fs m /\ m_tid (with_vmmaps h m) = m_tid m /\ m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. repeat split; reflexivity. Qed.

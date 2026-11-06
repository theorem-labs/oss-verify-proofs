(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import Monad MSafe.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require CfgStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require AllocRefusal.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w_is0_lit : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (TASK_SIZE <? bv_unsigned addr + nZ) then true
    else
      let n := Z_to_bv 64 nZ in
      map_has (vm_maps h) addr n || munmap_free_ok h addr nZ.

Definition mprotect_safe_b (addr len prot : word) (h : VmMaps) : bool :=
  if mprotect_grows_conflict_b prot then true
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
  else if w_is0 len then true
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
  else if mprotect_modeled_b prot then
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
    || (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n)
  else false.

(* [comment removed for export] *)
Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  if negb (mmap_off_aligned_b off) then mmap_pglen_ok_b len
  else if negb (mmap_anon_b flags) then false
  else if w_is0 len then mmap_plain_anon_b flags
  else
  mmap_modeled_b prot flags off
  || mmap_noaccess_b prot flags off
  || (if mmap_fixed_noaccess_b prot flags off then
        let nZ := page_round_up_Z (bv_unsigned len) in
        if (two_pow_64 <=? bv_unsigned addr + nZ) then true
        else if negb (bv_unsigned addr + nZ <=? alloc_top h) then false
        else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
        else if negb (0 <? bv_unsigned addr) then false
        else region_free (vm_reserved h) addr (Z_to_bv 64 nZ) && map_contains (vm_maps h) addr (Z_to_bv 64 nZ)
      else false).
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac crush_check H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (? & ? & ?); subst
          | (if ?x then _ else _) = _ => destruct x eqn:?
          | (match ?x with _ => _ end) = _ => destruct x eqn:?
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma vm_forget_range_only : forall lo hi m,
  m_fd (vm_forget_range lo hi m) = m_fd m /\ m_io (vm_forget_range lo hi m) = m_io m
  /\ m_fsys (vm_forget_range lo hi m) = m_fsys m /\ m_proc (vm_forget_range lo hi m) = m_proc m
  /\ m_lim (vm_forget_range lo hi m) = m_lim m /\ m_time (vm_forget_range lo hi m) = m_time m
  /\ m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m
  /\ (m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = []).
Proof.
  intros lo hi m. destruct m as [fd [maps lazy mat] io fs pr li ti]. cbn.
  repeat split; try reflexivity. cbn. intros ->. reflexivity.
Qed.

Lemma forget_vm_ranges_only : forall rs m,
  vm_only m (forget_vm_ranges rs m) /\ m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m
  /\ (m_vm_lazy m = [] -> m_vm_lazy (forget_vm_ranges rs m) = []).
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges].
  - split; [apply vm_only_refl|]. auto.
  - cps_destruct (IH (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)) as (V & M & L).
    cps_pose (vm_forget_range_only (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m) as (F1 & F2 & F3 & F4 & F5 & F6 & FM & FL).
    split; [|split].
    + unfold vm_only in *. cps_destruct V as (V1 & V2 & V3 & V4 & V5 & V6).
      rewrite V1, V2, V3, V4, V5, V6, F1, F2, F3, F4, F5, F6. repeat split; reflexivity.
    + rewrite M. exact FM.
    + intros Hl. apply L. apply FL. exact Hl.
Qed.

Lemma with_vmmaps_only : forall h m,
  vm_only m (with_vmmaps h m) /\ m_vmmaps (with_vmmaps h m) = h /\ m_vm_lazy (with_vmmaps h m) = m_vm_lazy m
  /\ m_halted (with_vmmaps h m) = m_halted m.
Proof. intros h m. destruct m as [fd [maps lazy mat] io fs pr li ti]. cbn. unfold vm_only. cbn. repeat split; reflexivity. Qed.

Lemma vm_add_lazy_only : forall a n m,
  vm_only m (vm_add_lazy a n m) /\ m_vmmaps (vm_add_lazy a n m) = m_vmmaps m /\ m_halted (vm_add_lazy a n m) = m_halted m.
Proof. intros a n m. destruct m as [fd [maps lazy mat] io fs pr li ti]. cbn. unfold vm_only. cbn. repeat split; reflexivity. Qed.

Lemma vm_only_halted : forall m m', vm_only m m' -> m_halted m' = m_halted m.
Proof. intros m m' H. apply Nodes.vm_only_halted. exact H. Qed.

(* [comment removed for export] *)
Definition mm_post (m m' : Model) (evs : list event) : Prop :=
  vm_only m m' /\ evs = [] /\ m_halted m' = m_halted m.

Lemma mm_post_of_vm_only : forall m m' evs, vm_only m m' -> evs = [] -> mm_post m m' evs.
Proof. intros m m' evs V E. split; [exact V|]. split; [exact E|]. apply vm_only_halted. exact V. Qed.

Lemma with_brk_next_only : forall m req r,
  vm_only m (with_brk_next m req r) /\ (m_vm_lazy m = [] -> m_vm_lazy (with_brk_next m req r) = [])
  /\ m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof.
  intros m req r. unfold with_brk_next.
  cps_destruct (forget_vm_ranges_only (brk_unmaps r (vm_brk (m_vmmaps m))) (with_vmmaps (brk_model_next (m_vmmaps m) req r) m)) as (V & M & L).
  cps_destruct (with_vmmaps_only (brk_model_next (m_vmmaps m) req r) m) as (V0 & M0 & L0 & _).
  split; [eapply vm_only_trans; [exact V0| exact V]|]. split.
  - intros Hl. apply L. rewrite L0. exact Hl.
  - rewrite M. exact M0.
Qed.

Lemma check_brk_shape : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  exists r, brk_r_ok m req r = true /\ m' = with_brk_next m req r
    /\ eff = mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m))) (brk_unmaps r (vm_brk (m_vmmaps m))) [] []
    /\ evs = [].
Proof.
  intros req eff m m' evs H. unfold check_brk in H. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok m req r) eqn:E1; [|discriminate].
  destruct (listNN_eqb zs _) eqn:E2; [|discriminate]. destruct (listNN_eqb us _) eqn:E3; [|discriminate].
  cbn [andb] in H. injection H as <- <-. apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst.
  exists r. repeat split; reflexivity || exact E1.
Qed.

Lemma check_brk_post : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> mm_post m m' evs /\ (m_vm_lazy m = [] -> m_vm_lazy m' = []).
Proof.
  intros req eff m m' evs H. cps_destruct (check_brk_shape _ _ _ _ _ H) as (r & _ & -> & _ & ->).
  cps_destruct (with_brk_next_only m req r) as (V & L & _). split; [apply mm_post_of_vm_only; [exact V| reflexivity]| exact L].
Qed.

(* [comment removed for export] *)
Lemma with_mmap_backing_only : forall flags a n m,
  vm_only m (with_mmap_backing flags a n m) /\ m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m
  /\ m_halted (with_mmap_backing flags a n m) = m_halted m
  /\ (mmap_noreserve_b flags = false -> m_vm_lazy (with_mmap_backing flags a n m) = m_vm_lazy m).
Proof.
  intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags).
  - cps_destruct (vm_add_lazy_only a n m) as (V & M & Hh). repeat split; auto. intros; discriminate.
  - repeat split; auto using vm_only_refl.
Qed.

Lemma with_mmap_destroyed_only : forall a n h m,
  vm_only m (with_mmap_destroyed a n h m) /\ m_vmmaps (with_mmap_destroyed a n h m) = h
  /\ m_halted (with_mmap_destroyed a n h m) = m_halted m
  /\ (m_vm_lazy m = [] -> m_vm_lazy (with_mmap_destroyed a n h m) = []).
Proof.
  intros a n h m. unfold with_mmap_destroyed.
  cps_pose (vm_forget_range_only (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h m)) as (F1 & F2 & F3 & F4 & F5 & F6 & FM & FL).
  cps_destruct (with_vmmaps_only h m) as (V0 & M0 & L0 & H0).
  split; [|split; [|split]].
  - unfold vm_only in *. cps_destruct V0 as (V1 & V2 & V3 & V4 & V5 & V6).
    rewrite F1, F2, F3, F4, F5, F6. repeat split; assumption.
  - rewrite FM. exact M0.
  - unfold m_halted. rewrite F4. fold (m_halted (with_vmmaps h m)). exact H0.
  - intros Hl. apply FL. rewrite L0. exact Hl.
Qed.

Lemma with_mmap_replacement_only : forall flags a n m,
  vm_only m (with_mmap_replacement flags a n m) /\ m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m
  /\ m_halted (with_mmap_replacement flags a n m) = m_halted m
  /\ (mmap_noreserve_b flags = false -> m_vm_lazy m = [] -> m_vm_lazy (with_mmap_replacement flags a n m) = []).
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  cps_pose (vm_forget_range_only (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m) as (F1 & F2 & F3 & F4 & F5 & F6 & FM & FL).
  cps_destruct (with_mmap_backing_only flags a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)) as (V & M & Hh & L).
  split; [|split; [|split]].
  - unfold vm_only in *. cps_destruct V as (V1 & V2 & V3 & V4 & V5 & V6).
    rewrite V1, V2, V3, V4, V5, V6, F1, F2, F3, F4, F5, F6. repeat split; reflexivity.
  - rewrite M. exact FM.
  - rewrite Hh. unfold m_halted. rewrite F4. reflexivity.
  - intros Hf Hl. rewrite (L Hf). apply FL. exact Hl.
Qed.

Lemma mprotect_model_next_only : forall m a n,
  vm_only m (mprotect_model_next m a n) /\ m_halted (mprotect_model_next m a n) = m_halted m
  /\ m_vm_lazy (mprotect_model_next m a n) = m_vm_lazy m.
Proof.
  intros m a n. unfold mprotect_model_next.
  match goal with |- context [with_vmmaps ?h m] => destruct (with_vmmaps_only h m) as (V & _ & L & Hh) end. auto.
Qed.
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac mm_post_leaf :=
  let V := ident:(V) in let Hh := ident:(Hh) in let L := ident:(L) in let V0 := ident:(V0) in let L0 := ident:(L0) in let H0 := ident:(H0) in lazymatch goal with
  | |- mm_post ?m ?m _ /\ _ => split; [apply mm_post_of_vm_only; [apply vm_only_refl| reflexivity]| auto]
  | |- mm_post ?m (with_mmap_backing ?f ?a ?n (with_vmmaps ?h ?m)) _ /\ _ =>
      cps_destruct (with_mmap_backing_only f a n (with_vmmaps h m)) as (V & _ & Hh & L);
      cps_destruct (with_vmmaps_only h m) as (V0 & _ & L0 & H0);
      split; [apply mm_post_of_vm_only; [eapply vm_only_trans; [exact V0| exact V]| reflexivity]|];
      intros Hf Hl; rewrite (L Hf), L0; exact Hl
  | |- mm_post ?m (with_mmap_destroyed ?a ?n ?h ?m) _ /\ _ =>
      cps_destruct (with_mmap_destroyed_only a n h m) as (V & _ & Hh & L);
      split; [apply mm_post_of_vm_only; [exact V| reflexivity]| intros _ Hl; apply L; exact Hl]
  | |- mm_post ?m (with_mmap_replacement ?f ?a ?n (with_vmmaps ?h ?m)) _ /\ _ =>
      cps_destruct (with_mmap_replacement_only f a n (with_vmmaps h m)) as (V & _ & Hh & L);
      cps_destruct (with_vmmaps_only h m) as (V0 & _ & L0 & H0);
      split; [apply mm_post_of_vm_only; [eapply vm_only_trans; [exact V0| exact V]| reflexivity]|];
      intros Hf Hl; apply (L Hf); rewrite L0; exact Hl
  | |- mm_post ?m (mprotect_model_next ?m ?a ?n) _ /\ _ =>
      cps_destruct (mprotect_model_next_only m a n) as (V & Hh & L);
      split; [apply mm_post_of_vm_only; [exact V| reflexivity]| intros _ Hl; rewrite L; exact Hl]
  end.
Section ACeilS3. Context {ACEIL__ : ACeil}.


Lemma check_mmap_shape : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  mm_post m m' evs /\ (mmap_noreserve_b flags = false -> m_vm_lazy m = [] -> m_vm_lazy m' = []).
Proof.
  intros until evs; intros H. unfold check_mmap in H. crush_check H; mm_post_leaf.
Qed.

Lemma check_munmap_shape : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  mm_post m m' evs /\ (True -> m_vm_lazy m = [] -> m_vm_lazy m' = []).
Proof.
  intros until evs; intros H. unfold check_munmap in H. crush_check H; mm_post_leaf.
Qed.

Lemma check_mprotect_shape : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  mm_post m m' evs /\ (True -> m_vm_lazy m = [] -> m_vm_lazy m' = []).
Proof.
  intros until evs; intros H. unfold check_mprotect in H. crush_check H; mm_post_leaf.
Qed.
End ACeilS3.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac no_unm :=
  repeat first [ apply check_ret_only_no_unmodeled
               | discriminate
               | match goal with |- (match ?x with _ => _ end) <> _ => destruct x end
               | match goal with |- (if ?x then _ else _) <> _ => destruct x end
               | progress cbv zeta beta iota ].
Section ACeilS4. Context {ACEIL__ : ACeil}.


Lemma check_brk_no_unmodeled : forall req eff m, check_brk req eff m <> CheckUnmodeled.
Proof. intros req [r ws zs us cs ci] m. unfold check_brk. no_unm. Qed.

Lemma munmap_safe_no_unmodeled : forall addr len eff m,
  munmap_safe_b addr len (m_vmmaps m) = true -> check_munmap addr len eff m <> CheckUnmodeled.
Proof.
  intros addr len eff m. unfold munmap_safe_b, check_munmap.
  destruct (negb _ || w_is0 len); [intros _; apply check_ret_only_no_unmodeled|]. cbv zeta.
  destruct (TASK_SIZE <? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (map_has _ _ _); [intros _; no_unm|]. cbn [orb]. intros ->. apply check_ret_only_no_unmodeled.
Qed.

Lemma mprotect_safe_no_unmodeled : forall addr len prot eff m,
  mprotect_safe_b addr len prot (m_vmmaps m) = true -> check_mprotect addr len prot eff m <> CheckUnmodeled.
Proof.
  intros addr len prot eff m. unfold mprotect_safe_b, check_mprotect.
  destruct (mprotect_grows_conflict_b prot); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (w_is0 len); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (mprotect_modeled_b prot); [|discriminate]. cbn [negb]. cbv zeta.
  destruct (map_contains (vm_noaccess _) _ _ && map_contains _ _ _); [intros _; no_unm|].
  cbn [orb]. intros ->. no_unm.
Qed.

Lemma mmap_safe_no_unmodeled : forall addr len prot flags fd off eff m,
  mmap_safe_b addr len prot flags fd off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros addr len prot flags fd off eff m. unfold mmap_safe_b, check_mmap.
  destruct (negb (mmap_off_aligned_b off)). { intros ->. apply check_ret_only_no_unmodeled. }
  destruct (negb (mmap_anon_b flags)). { discriminate. }
  destruct (w_is0 len). { intros ->. apply check_ret_only_no_unmodeled. }
  destruct (mmap_modeled_b prot flags off); [intros _; no_unm|].
  destruct (mmap_noaccess_b prot flags off); [intros _; no_unm|]. cbn [orb].
  destruct (mmap_fixed_noaccess_b prot flags off); [|discriminate]. cbv zeta.
  destruct (two_pow_64 <=? _); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (_ <=? alloc_top _)); [discriminate|].
  destruct (negb (bv_unsigned addr mod page_size =? 0)); [intros _; apply check_ret_only_no_unmodeled|].
  destruct (negb (0 <? bv_unsigned addr)); [discriminate|].
  intros ->. no_unm.
Qed.
End ACeilS4.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac dispatch_pure K :=
  unfold check_syscall; cbn [in_sysno pure_input];
  change (bv_unsigned (Z_to_bv 64 K)) with K; cbn [Z.eqb Pos.eqb in_arg in_args nth].
Section ACeilS5. Context {ACEIL__ : ACeil}.


Lemma check_syscall_brk : forall req eff mo,
  check_syscall (pure_input 214 [Z_to_bv 64 req]) eff mo = check_brk (Z_to_bv 64 req) eff mo.
Proof. intros. dispatch_pure 214. reflexivity. Qed.

Lemma check_syscall_mmap : forall addr len prot flags eff mo,
  check_syscall (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) eff mo
  = check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo.
Proof. intros. dispatch_pure 222. reflexivity. Qed.

Lemma check_syscall_munmap : forall addr len eff mo,
  check_syscall (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) eff mo = check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo.
Proof. intros. dispatch_pure 215. reflexivity. Qed.

Lemma check_syscall_mprotect : forall addr len prot eff mo,
  check_syscall (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) eff mo
  = check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo.
Proof. intros. dispatch_pure 226. reflexivity. Qed.

Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep (NBrk req) mo eff mo' evs <->
  check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs
  /\ ~ spurious_refusal_cfg CfgStep.kit_cfg (pure_input 214 [Z_to_bv 64 req]) mo eff.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff, check_syscall_brk.
  split; [tauto|]. intros [H Hns]. split; [| split; [exact H| exact Hns]]. destruct (check_brk_post _ _ _ _ _ H) as [(_ & E & _) _]. exact E.
Qed.

Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs <->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs
  /\ ~ spurious_refusal_cfg CfgStep.kit_cfg
         (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff, check_syscall_mmap.
  split; [tauto|]. intros [H Hns]. split; [| split; [exact H| exact Hns]]. destruct (check_mmap_shape _ _ _ _ _ _ _ _ _ _ H) as [(_ & E & _) _]. exact E.
Qed.

Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep (NMunmap addr len) mo eff mo' evs <->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs
  /\ ~ spurious_refusal_cfg CfgStep.kit_cfg (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo eff.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff, check_syscall_munmap.
  split; [tauto|]. intros [H Hns]. split; [| split; [exact H| exact Hns]]. destruct (check_munmap_shape _ _ _ _ _ _ H) as [(_ & E & _) _]. exact E.
Qed.

Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep (NMprotect addr len prot) mo eff mo' evs <->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs
  /\ ~ spurious_refusal_cfg CfgStep.kit_cfg
         (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo eff.
Proof.
  intros. cbn [nstep node_input]. rewrite <- check_syscall_ok_iff, check_syscall_mprotect.
  split; [tauto|]. intros [H Hns]. split; [| split; [exact H| exact Hns]]. destruct (check_mprotect_shape _ _ _ _ _ _ _ H) as [(_ & E & _) _]. exact E.
Qed.

Lemma nstep_mmap_refusal_absurd : forall addr len prot flags mo eff mo' evs eff' mo'',
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff' mo = CheckOk mo'' [] ->
  errno_ret_in mmap_errnos (eff_ret eff') = false ->
  False.
Proof.
  intros addr len prot flags mo eff mo' evs eff' mo'' H Hr Hc Hnr.
  apply nstep_mmap_iff in H as [_ Hns]. apply Hns.
  split; [reflexivity|]. split; [exact Hr|].
  exists eff', mo'', []. split; [| exact Hnr].
  apply check_syscall_ok_iff. rewrite check_syscall_mmap. exact Hc.
Qed.

Lemma nstep_mprotect_refusal_absurd : forall addr len prot mo eff mo' evs eff' mo'',
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  errno_ret_in mprotect_errnos (eff_ret eff) = true ->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff' mo = CheckOk mo'' [] ->
  errno_ret_in mprotect_errnos (eff_ret eff') = false ->
  False.
Proof.
  intros addr len prot mo eff mo' evs eff' mo'' H Hr Hc Hnr.
  apply nstep_mprotect_iff in H as [_ Hns]. apply Hns.
  split; [reflexivity|]. split; [exact Hr|].
  exists eff', mo'', []. split; [| exact Hnr].
  apply check_syscall_ok_iff. rewrite check_syscall_mprotect. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nsafe_brk : forall req mo, nsafe (NBrk req) mo.
Proof.
  intros req mo. unfold nsafe. cbn [node_input].
  rewrite <- (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])), check_syscall_brk. apply check_brk_no_unmodeled.
Qed.

Lemma nsafe_mmap : forall addr len prot flags mo,
  mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true ->
  nsafe (NMmap addr len prot flags) mo.
Proof.
  intros addr len prot flags mo Hs. unfold nsafe. cbn [node_input].
  rewrite <- (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])), check_syscall_mmap. apply mmap_safe_no_unmodeled. exact Hs.
Qed.

Lemma nsafe_munmap : forall addr len mo,
  munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true -> nsafe (NMunmap addr len) mo.
Proof.
  intros addr len mo Hs. unfold nsafe. cbn [node_input].
  rewrite <- (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])), check_syscall_munmap. apply munmap_safe_no_unmodeled. exact Hs.
Qed.

Lemma nsafe_mprotect : forall addr len prot mo,
  mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true -> nsafe (NMprotect addr len prot) mo.
Proof.
  intros addr len prot mo Hs. unfold nsafe. cbn [node_input].
  rewrite <- (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])), check_syscall_mprotect. apply mprotect_safe_no_unmodeled. exact Hs.
Qed.

(* [comment removed for export] *)
Lemma nsafe_mmap_rw : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
  intros addr len mo Hl. apply nsafe_mmap. unfold mmap_safe_b. rewrite w_is0_lit by lia.
  replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_off_aligned_b _) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b _) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b _ _ _) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma nsafe_mmap_none : forall addr len mo, 0 < len < 2^64 ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof.
  intros addr len mo Hl. apply nsafe_mmap. unfold mmap_safe_b. rewrite w_is0_lit by lia.
  replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_off_aligned_b _) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b _) with true by (vm_compute; reflexivity).
  replace (mmap_noaccess_b _ _ _) with true by (vm_compute; reflexivity).
  destruct (mmap_modeled_b _ _ _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nbenign_brk : forall req mo, m_halted mo = None -> m_vm_lazy mo = [] -> nbenign (NBrk req) mo.
Proof.
  intros req mo Hh Hl. unfold nbenign. cbn [node_input]. intros eff mo' evs H.
  apply check_syscall_ok_iff in H. rewrite check_syscall_brk in H.
  destruct (check_brk_post _ _ _ _ _ H) as [(V & -> & Hh') L]. rewrite Hh'. auto.
Qed.

Lemma nbenign_mmap : forall addr len prot flags mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  nbenign (NMmap addr len prot flags) mo.
Proof.
  intros addr len prot flags mo Hh Hl Hf. unfold nbenign. cbn [node_input]. intros eff mo' evs H.
  apply check_syscall_ok_iff in H. rewrite check_syscall_mmap in H.
  destruct (check_mmap_shape _ _ _ _ _ _ _ _ _ _ H) as [(V & -> & Hh') L]. rewrite Hh'. auto.
Qed.

Lemma nbenign_munmap : forall addr len mo, m_halted mo = None -> m_vm_lazy mo = [] -> nbenign (NMunmap addr len) mo.
Proof.
  intros addr len mo Hh Hl. unfold nbenign. cbn [node_input]. intros eff mo' evs H.
  apply check_syscall_ok_iff in H. rewrite check_syscall_munmap in H.
  destruct (check_munmap_shape _ _ _ _ _ _ H) as [(V & -> & Hh') L]. rewrite Hh'. auto.
Qed.

Lemma nbenign_mprotect : forall addr len prot mo, m_halted mo = None -> m_vm_lazy mo = [] -> nbenign (NMprotect addr len prot) mo.
Proof.
  intros addr len prot mo Hh Hl. unfold nbenign. cbn [node_input]. intros eff mo' evs H.
  apply check_syscall_ok_iff in H. rewrite check_syscall_mprotect in H.
  destruct (check_mprotect_shape _ _ _ _ _ _ _ H) as [(V & -> & Hh') L]. rewrite Hh'. auto.
Qed.

Lemma noreserve_MAPF : mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma noreserve_MAPFX : mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

Lemma region_free_In' : forall maps a n e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  (bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma avoids_of_region_free : forall maps a n avoid,
  region_free maps a n = true ->
  Forall (covered maps) avoid ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
  cps_pose (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
  pose proof (region_free_In' _ _ _ _ _ Hrf He) as [H|H].
  - apply orb_true_intro. left. apply Z.leb_le. lia.
  - apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ m_vmmaps mo' = brk_model_next (m_vmmaps mo) (Z_to_bv 64 0) (vm_brk (m_vmmaps mo))
  /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []).
Proof.
  intros mo rsp mo' evs H. apply -> nstep_brk_iff in H. destruct H as [H _].
  destruct (check_brk_post _ _ _ _ _ H) as [(Hv & -> & _) HL].
  cps_destruct (check_brk_shape _ _ _ _ _ H) as (r & E1 & -> & -> & _).
  unfold brk_r_ok in E1. change (w_is0 (Z_to_bv 64 0)) with true in E1. cbn [orb] in E1. apply bv_eqb_eq in E1. subst r.
  split; [reflexivity|]. split; [|split; [exact Hv| split; [apply (proj2 (proj2 (with_brk_next_only _ _ _)))| exact HL]]].
  unfold dec_brk0, brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb].
  unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _)%Z; reflexivity.
Qed.

Lemma brk_model_next_query : forall h,
  let h' := brk_model_next h (Z_to_bv 64 0) (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h.
Proof.
  intros h. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
  unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _)%Z; cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_next_init_sp : forall h req r, vm_init_sp (brk_model_next h req r) = vm_init_sp h.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_model_next_same : forall h req,
  let h' := brk_model_next h req (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h.
Proof.
  intros h req. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. cbn [app].
  unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _)%Z; cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_next_grown : forall h req,
  let b := bv_unsigned (vm_brk h) in
  (0 < b)%Z -> (b < req < 2^64)%Z ->
  let h' := brk_model_next h (Z_to_bv 64 req) (Z_to_bv 64 req) in
  vm_reserved h' = vm_reserved h
  /\ vm_maps h' = (vm_brk h, Z_to_bv 64 (req - b)) :: vm_maps h
  /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = Z_to_bv 64 req /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h.
Proof.
  intros h req b Hb Hreq h'. subst h'. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base].
  unfold brk_maps_next. rewrite unsigned_lit by lia. fold b.
  replace (0 <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? b)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
  unfold brk_grants, brk_is_grow. rewrite w_is0_lit by lia. replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite unsigned_lit by lia. fold b. replace (0 <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb app].
  unfold brk_unmaps, brk_page_range. rewrite unsigned_lit by lia. fold b.
  replace (page_round_up_Z req <? page_round_up_Z b)%Z with false.
  2:{ symmetry. apply Z.ltb_ge. apply page_round_up_Z_mono. lia. }
  assert (Hsub : (Z_to_bv 64 req - vm_brk h)%bv = Z_to_bv 64 (req - b)).
  { apply bv_eq. rewrite bv_sub_unsigned, unsigned_lit by lia. fold b. rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hsub. destruct (0 <? b)%Z; cbn; repeat split; reflexivity.
Qed.

Lemma brk_r_ok_grow : forall m req r,
  let h := m_vmmaps m in
  let b := bv_unsigned (vm_brk h) in
  (bv_unsigned (vm_start_brk h) <= b)%Z -> (b < req < 2^64)%Z ->
  brk_r_ok m (Z_to_bv 64 req) r = true ->
  (r = vm_brk h) \/ (r = Z_to_bv 64 req /\ brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true).
Proof.
  intros m req r h b Hs Hreq H. pose proof (bv_unsigned_in_range 64 (vm_brk h)) as Hr0. unfold bv_modulus in Hr0. fold b in Hr0.
  unfold brk_r_ok in H. fold h in H. rewrite w_is0_lit in H by lia.
  replace (req =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in H. rewrite unsigned_lit in H by lia.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in H by (symmetry; apply Z.ltb_ge; lia).
  fold b in H. replace (req <? b)%Z with false in H by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in H.
  apply andb_prop in H as [H1 H2]. apply orb_prop in H1 as [H1|H1]; apply bv_eqb_eq in H1; subst r; [right|left]; auto.
Qed.

(* [comment removed for export] *)
Lemma region_free_shrink : forall l (lo n n' : word),
  (bv_unsigned n' <= bv_unsigned n)%Z ->
  region_free l lo n = true -> region_free l lo n' = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n n' Hle H; [reflexivity|].
  cbn [region_free] in *. apply andb_prop in H as [H1 H2].
  rewrite (IH _ _ _ Hle H2), andb_true_r.
  unfold iv_overlap in *. apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff.
  apply Bool.andb_false_iff in H1. apply Bool.andb_false_iff.
  destruct H1 as [H1|H1]; [left; exact H1|right]. apply Z.ltb_ge in H1. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_facts : forall m req,
  let h := m_vmmaps m in
  let b := bv_unsigned (vm_brk h) in
  atop_ok h ->
  (0 < b)%Z -> (b < req < 2^64)%Z -> (b mod 4096 = 0)%Z -> (req mod 4096 = 0)%Z ->
  brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  (req <= alloc_ceiling)%Z /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true.
Proof.
  intros m req h b Hat Hb Hreq Hba Hra H. unfold brk_grow_ok in H. fold h in H. rewrite unsigned_lit in H by lia. fold b in H.
  replace (0 <? b)%Z with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req)%Z with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096)%Z with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096)%Z with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req)%Z with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  split.
  - rewrite <- Hat. exact H1.
  - pose proof alloc_ceiling_range as Hcr. rewrite <- Hat in Hcr.
    apply (region_free_shrink _ _ (Z_to_bv 64 (req + 4096 - b))); [| exact H2].
    rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) < req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => m_vmmaps mo' = brk_model_next h (Z_to_bv 64 req) (vm_brk h)
  | BrkGrown => m_vmmaps mo' = brk_model_next h (Z_to_bv 64 req) (Z_to_bv 64 req)
                /\ brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq H. apply -> nstep_brk_iff in H. destruct H as [H _].
  destruct (check_brk_post _ _ _ _ _ H) as [(Hv & -> & _) HL].
  cps_destruct (check_brk_shape _ _ _ _ _ H) as (r & E1 & -> & -> & _).
  split; [reflexivity|]. split; [exact Hv|]. split; [exact HL|].
  pose proof (proj2 (proj2 (with_brk_next_only mo (Z_to_bv 64 req) r))) as HM. fold h in HM |- *.
  destruct (brk_r_ok_grow mo req r Hsb Hreq E1) as [-> | [-> G]].
  - exists BrkSame. split; [| exact HM].
    unfold dec_brk, brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r.
    unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. rewrite Z.eqb_refl. destruct (0 <? _)%Z; reflexivity.
  - exists BrkGrown. split; [| auto].
    unfold dec_brk. unfold brk_unmaps, brk_page_range. rewrite unsigned_lit by lia.
    replace (page_round_up_Z req <? page_round_up_Z (bv_unsigned (vm_brk h)))%Z with false
      by (symmetry; apply Z.ltb_ge; apply page_round_up_Z_mono; lia).
    replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
    unfold brk_zeros, brk_is_grow. rewrite w_is0_lit by lia.
    replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite unsigned_lit by lia.
    replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [negb andb]. rewrite Z.eqb_refl. unfold brk_page_range, brk_new_pages, zeros_of, Mem.wa.
    destruct (_ <? _)%Z; cbn [andb]; rewrite (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_when_In : forall b e, In e (AllocRefusal.mmap_errnos_when b) -> In e mmap_errnos /\ b = true.
Proof. intros [|] e H; [split; [exact H| reflexivity]| destruct H]. Qed.
Lemma mprotect_when_In : forall b e, In e (AllocRefusal.mprotect_errnos_when b) -> In e mprotect_errnos /\ b = true.
Proof. intros [|] e H; [split; [exact H| reflexivity]| destruct H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  atop_ok h ->
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hat Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  apply -> nstep_mmap_iff in H. destruct H as [H _].
  destruct (check_mmap_shape _ _ _ _ _ _ _ _ _ _ H) as [(Hv & -> & _) HL].
  split; [reflexivity|]. split; [exact Hv|]. split; [intros Hl; apply HL; [apply noreserve_MAPF| exact Hl]|].
  destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H by (vm_compute; reflexivity).
  cbn [negb] in H. rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  cbv iota beta in H. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  match type of H with context [errno_ret_in ?l r] => destruct (errno_ret_in l r) eqn:Herr end.
  - destruct zs; [|discriminate]. injection H as <-.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    injection H as <-.
    apply andb_prop in E as [E E6]. apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E6. subst zs.
    rewrite (atop_ok_leb h _ Hat) in E3.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
      unfold with_mmap_backing. rewrite noreserve_MAPF. apply (proj1 (proj2 (with_vmmaps_only _ _))).
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  atop_ok h ->
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\
  exists x, dec_mmap_none len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hat Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  apply -> nstep_mmap_iff in H. destruct H as [H _].
  destruct (check_mmap_shape _ _ _ _ _ _ _ _ _ _ H) as [(Hv & -> & _) HL].
  split; [reflexivity|]. split; [exact Hv|]. split; [intros Hl; apply HL; [apply noreserve_MAPF| exact Hl]|].
  destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H by (vm_compute; reflexivity).
  cbn [negb] in H. rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with false in H by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  cbv iota beta in H. destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  match type of H with context [errno_ret_in ?l r] => destruct (errno_ret_in l r) eqn:Herr end.
  - destruct us; [|discriminate]. injection H as <-.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    injection H as <-.
    apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E5. subst us.
    rewrite (atop_ok_leb h _ Hat) in E3.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
      unfold with_mmap_backing. rewrite noreserve_MAPF. apply (proj1 (proj2 (with_vmmaps_only _ _))).
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\
  exists x, dec_munmap addr len rsp = Some x /\
  match x with
  | RgErr e => e = EINVAL /\ mo' = mo
  | RgDone false => mo' = mo /\ munmap_free_ok h a (mmap_len len) = true
  | RgDone true => map_has (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  apply -> nstep_munmap_iff in H. destruct H as [H _].
  destruct (check_munmap_shape _ _ _ _ _ _ H) as [(Hv & -> & _) HL].
  split; [reflexivity|]. split; [exact Hv|]. split; [intros Hl; apply HL; [exact I| exact Hl]|].
  destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  cbv zeta in H. destruct (TASK_SIZE <? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  destruct (map_has (vm_maps h) a n) eqn:Hhas.
  - destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:E; [|discriminate]. injection H as <-.
    apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
    exists (RgDone true). split; [|split; [reflexivity| apply (proj1 (proj2 (with_mmap_destroyed_only _ _ _ _)))]].
    unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - destruct (munmap_free_ok h a _) eqn:Hrf; [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgDone false). split; [reflexivity| auto].
Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => (e = EINVAL \/ e = ENOMEM) /\ mo' = mo
  | RgDone false => mo' = mo
  | RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  apply -> nstep_mprotect_iff in H. destruct H as [H _].
  destruct (check_mprotect_shape _ _ _ _ _ _ _ H) as [(Hv & -> & _) HL].
  split; [reflexivity|]. split; [exact Hv|]. split; [intros Hl; apply HL; [exact I| exact Hl]|].
  destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H by (vm_compute; reflexivity).
  cbn [negb] in H. cbv iota in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  destruct (two_pow_64 <=? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
  cbv zeta in H.
  destruct (map_contains (vm_noaccess h) a n && map_contains (vm_maps h) a n) eqn:Hc.
  - destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    match type of H with context [errno_ret_in ?l r] => destruct (errno_ret_in l r) eqn:Herr end.
    + destruct zs; [|discriminate]. injection H as <-.
      apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn.
      exists (RgErr e). split.
      * unfold dec_mprotect. rewrite errno_of_errno_ret; [reflexivity|].
        destruct HIn as [<-|[]]; unfold ENOMEM; lia.
      * split; [| reflexivity]. destruct HIn as [<-|[]]; auto.
    + destruct (mprotect_budget_ok mo a n && w_is0 r && listNN_eqb zs [(a, n)]) eqn:E; [|discriminate]. injection H as <-.
      apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1]. apply listNN_eqb_eq in E2. subst zs.
      unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
      apply andb_prop in Hc as [Hc1 Hc2].
      exists (RgDone true). split.
      * unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
      * split; [exact Hc1|]. split; [exact Hc2|]. unfold mprotect_model_next. apply (proj1 (proj2 (with_vmmaps_only _ _))).
  - destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. injection H as <-. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    exists (RgDone false). split; [reflexivity| reflexivity].
Qed.

End ACeilS5.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_top_mkVmMapsFull : forall rs maps na sb b lim mb isp,
  alloc_top (mkVmMapsFull rs maps na sb b lim mb isp) = bv_unsigned isp - stack_max_size.
Proof. reflexivity. Qed.

Lemma alloc_top_init : forall reserved brk0 mbase sp lim inp,
  alloc_top (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = bv_unsigned sp - stack_max_size.
Proof. intros. rewrite m_vmmaps_init_model. reflexivity. Qed.

Lemma stack_max_size_val : stack_max_size = 0x800000.
Proof. reflexivity. Qed.

Lemma CEIL_MIN_val : CEIL_MIN = sp_window_lo - stack_max_size.
Proof. reflexivity. Qed.

Lemma CEIL_MAX_val : CEIL_MAX = sp_window_hi - stack_max_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_range : forall sp,
  valid_sp sp -> CEIL_MIN <= bv_unsigned sp - stack_max_size <= CEIL_MAX.
Proof.
  intros sp (Hlo & Hhi & _). rewrite CEIL_MIN_val, CEIL_MAX_val. lia.
Qed.

Lemma alloc_top_mod16 : forall sp,
  valid_sp sp -> (bv_unsigned sp - stack_max_size) mod 16 = 0.
Proof.
  intros sp (_ & _ & Hal). rewrite stack_max_size_val.
  rewrite Zminus_mod, Hal. reflexivity.
Qed.

Lemma alloc_top_init_range : forall reserved brk0 mbase sp lim inp,
  valid_sp sp ->
  CEIL_MIN <= alloc_top (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) <= CEIL_MAX.
Proof. intros. rewrite alloc_top_init. apply alloc_top_range. assumption. Qed.

(* [comment removed for export] *)
Lemma CEIL_MIN_num : CEIL_MIN = 0x7fff7f800000. Proof. reflexivity. Qed.
Lemma CEIL_MAX_num : CEIL_MAX = 0x7fffff800000. Proof. reflexivity. Qed.
Lemma CEIL_BAND_num : CEIL_BAND = 0x800000000000. Proof. reflexivity. Qed.
Lemma alloc_ceiling_num : alloc_ceiling = 0x7fffff800000. Proof. reflexivity. Qed.
Lemma CEIL_MAX_lt_BAND : CEIL_MAX < CEIL_BAND. Proof. reflexivity. Qed.
Lemma alloc_top_lt_2p47 : forall h, CEIL_MIN <= alloc_top h <= CEIL_MAX -> alloc_top h < 2^47.
Proof. intros h H. rewrite CEIL_MAX_num in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alloc_top_with_fds : forall v m, alloc_top (m_vmmaps (with_fds v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_fds. reflexivity. Qed.
Lemma alloc_top_with_fs : forall v m, alloc_top (m_vmmaps (with_fs v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_fs. reflexivity. Qed.
Lemma alloc_top_with_stdin : forall v m, alloc_top (m_vmmaps (with_stdin v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_stdin. reflexivity. Qed.
Lemma alloc_top_with_halted : forall v m, alloc_top (m_vmmaps (with_halted v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_halted. reflexivity. Qed.
Lemma alloc_top_with_tid : forall v m, alloc_top (m_vmmaps (with_tid v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_tid. reflexivity. Qed.
Lemma alloc_top_with_pipes : forall v m, alloc_top (m_vmmaps (with_pipes v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_pipes. reflexivity. Qed.
Lemma alloc_top_with_killed : forall v m, alloc_top (m_vmmaps (with_killed v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_killed. reflexivity. Qed.
Lemma alloc_top_with_creds : forall v m, alloc_top (m_vmmaps (with_creds v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_creds. reflexivity. Qed.
Lemma alloc_top_with_clock : forall v m, alloc_top (m_vmmaps (with_clock v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_clock. reflexivity. Qed.
Lemma alloc_top_with_sigmask : forall v m, alloc_top (m_vmmaps (with_sigmask v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_sigmask. reflexivity. Qed.
Lemma alloc_top_with_sigabrt_pending : forall m, alloc_top (m_vmmaps (with_sigabrt_pending m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_sigabrt_pending. reflexivity. Qed.
Lemma alloc_top_with_abort_terminal : forall v m, alloc_top (m_vmmaps (with_abort_terminal v m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_abort_terminal. reflexivity. Qed.
Lemma alloc_top_with_statpin : forall p bs m, alloc_top (m_vmmaps (with_statpin p bs m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_statpin. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m_vmmaps_with_vm_backing : forall lz mt m, m_vmmaps (with_vm_backing lz mt m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_add_lazy : forall a n m, m_vmmaps (vm_add_lazy a n m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply m_vmmaps_vm_forget_range.
Qed.
Lemma m_vmmaps_with_mmap_backing : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma alloc_top_with_vmmaps : forall h m, alloc_top (m_vmmaps (with_vmmaps h m)) = alloc_top h.
Proof. intros. rewrite m_vmmaps_with_vmmaps. reflexivity. Qed.
Lemma alloc_top_with_vm_backing : forall lz mt m, alloc_top (m_vmmaps (with_vm_backing lz mt m)) = alloc_top (m_vmmaps m).
Proof. reflexivity. Qed.
Lemma alloc_top_vm_add_lazy : forall a n m, alloc_top (m_vmmaps (vm_add_lazy a n m)) = alloc_top (m_vmmaps m).
Proof. reflexivity. Qed.
Lemma alloc_top_vm_forget_range : forall lo hi m, alloc_top (m_vmmaps (vm_forget_range lo hi m)) = alloc_top (m_vmmaps m).
Proof. reflexivity. Qed.
Lemma alloc_top_forget_vm_ranges : forall rs m, alloc_top (m_vmmaps (forget_vm_ranges rs m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_forget_vm_ranges. reflexivity. Qed.
Lemma alloc_top_with_mmap_backing : forall flags a n m,
  alloc_top (m_vmmaps (with_mmap_backing flags a n m)) = alloc_top (m_vmmaps m).
Proof. intros. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_brk_model_next : forall h req r, alloc_top (brk_model_next h req r) = alloc_top h.
Proof. reflexivity. Qed.
Lemma alloc_top_with_brk_next : forall m req r,
  alloc_top (m_vmmaps (with_brk_next m req r)) = alloc_top (m_vmmaps m).
Proof.
  intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps.
  apply alloc_top_brk_model_next.
Qed.
Lemma alloc_top_with_mmap_replacement : forall flags a n m,
  alloc_top (m_vmmaps (with_mmap_replacement flags a n m)) = alloc_top (m_vmmaps m).
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.
Lemma alloc_top_with_mmap_destroyed : forall a n h' m,
  alloc_top (m_vmmaps (with_mmap_destroyed a n h' m)) = alloc_top h'.
Proof. intros. unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_destroyed_next : forall h addr n,
  alloc_top (mmap_fixed_destroyed_next h addr n) = alloc_top h.
Proof. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_rw_next : forall h addr n, alloc_top (mmap_fixed_rw_next h addr n) = alloc_top h.
Proof. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_rw_span_next : forall h addr n, alloc_top (mmap_fixed_rw_span_next h addr n) = alloc_top h.
Proof. reflexivity. Qed.
Lemma alloc_top_mmap_fixed_noaccess_span_next : forall h addr n,
  alloc_top (mmap_fixed_noaccess_span_next h addr n) = alloc_top h.
Proof. reflexivity. Qed.
Lemma alloc_top_mprotect_model_next : forall m addr n,
  alloc_top (m_vmmaps (mprotect_model_next m addr n)) = alloc_top (m_vmmaps m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_grant : forall h e na,
  alloc_top (mkVmMapsFull (vm_reserved h) (e :: vm_maps h) na (vm_start_brk h) (vm_brk h)
                          (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) = alloc_top h.
Proof. reflexivity. Qed.
Lemma alloc_top_same_sp : forall h rs maps na sb b lim mb,
  alloc_top (mkVmMapsFull rs maps na sb b lim mb (vm_init_sp h)) = alloc_top h.
Proof. reflexivity. Qed.

#[export] Hint Rewrite alloc_top_with_fds alloc_top_with_fs alloc_top_with_stdin alloc_top_with_halted
  alloc_top_with_tid alloc_top_with_pipes alloc_top_with_killed alloc_top_with_creds alloc_top_with_clock
  alloc_top_with_sigmask alloc_top_with_sigabrt_pending alloc_top_with_abort_terminal alloc_top_with_statpin
  alloc_top_with_vmmaps alloc_top_with_vm_backing alloc_top_vm_add_lazy alloc_top_vm_forget_range
  alloc_top_forget_vm_ranges alloc_top_with_mmap_backing alloc_top_with_brk_next alloc_top_with_mmap_replacement
  alloc_top_with_mmap_destroyed alloc_top_mmap_fixed_destroyed_next alloc_top_mmap_fixed_rw_next
  alloc_top_mmap_fixed_rw_span_next alloc_top_mmap_fixed_noaccess_span_next alloc_top_mprotect_model_next
  alloc_top_brk_model_next alloc_top_same_sp : alloc_top.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct AxMeasure.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fix_rw_shape (prot flags off : word) : bool :=
  mmap_off_aligned_b off && mmap_anon_b flags && negb (mmap_modeled_b prot flags off)
  && negb (mmap_noaccess_b prot flags off) && negb (mmap_fixed_noaccess_b prot flags off)
  && mmap_fixed_rw_b prot flags off.

Definition fix_none_shape (prot flags off : word) : bool :=
  mmap_off_aligned_b off && mmap_anon_b flags && negb (mmap_modeled_b prot flags off)
  && negb (mmap_noaccess_b prot flags off) && mmap_fixed_noaccess_b prot flags off.

(* [comment removed for export] *)
Lemma word_is0 (w : word) : bv_unsigned w = 0 -> w = Z_to_bv 64 0.
Proof. intros H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma fix_rw_shape_lit (prot flags off : word) :
  bv_unsigned prot = 3 -> (bv_unsigned flags = 50 \/ bv_unsigned flags = 16434) -> bv_unsigned off = 0 ->
  fix_rw_shape prot flags off = true.
Proof.
  intros Hp Hf Ho. unfold fix_rw_shape, mmap_off_aligned_b, mmap_anon_b, mmap_modeled_b, mmap_noaccess_b,
    mmap_fixed_noaccess_b, mmap_fixed_rw_b, mmap_flags_core, w_is0.
  rewrite Hp, Ho, (word_is0 off Ho). destruct Hf as [-> | ->]; reflexivity.
Qed.

Lemma fix_none_shape_lit (prot flags off : word) :
  bv_unsigned prot = 0 -> (bv_unsigned flags = 50 \/ bv_unsigned flags = 16434) -> bv_unsigned off = 0 ->
  fix_none_shape prot flags off = true.
Proof.
  intros Hp Hf Ho. unfold fix_none_shape, mmap_off_aligned_b, mmap_anon_b, mmap_modeled_b, mmap_noaccess_b,
    mmap_fixed_noaccess_b, mmap_flags_core, w_is0.
  rewrite Hp, Ho, (word_is0 off Ho). destruct Hf as [-> | ->]; reflexivity.
Qed.

(* [comment removed for export] *)
Definition fix_nZ (len : word) : Z := page_round_up_Z (bv_unsigned len).
Definition fix_n (len : word) : word := Z_to_bv 64 (fix_nZ len).

(* [comment removed for export] *)
Record fix_gate (m : Model) (addr len : word) : Prop := mkFixGate {
  fg_len : bv_unsigned len <> 0;
  fg_top : bv_unsigned addr + fix_nZ len <= alloc_top (m_vmmaps m);
  fg_al  : bv_unsigned addr mod 4096 = 0;
  fg_pos : 0 < bv_unsigned addr;
  fg_res : region_free (vm_reserved (m_vmmaps m)) addr (fix_n len) = true;
  fg_own : map_contains (vm_maps (m_vmmaps m)) addr (fix_n len) = true
}.

(* [comment removed for export] *)
Definition fix_rw_model (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m).

Definition fix_none_model (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
       ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
       (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma w_is0_false (w : word) : bv_unsigned w <> 0 -> w_is0 w = false.
Proof.
  intros H. unfold w_is0. destruct (bv_eqb w (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst w. exfalso. apply H. reflexivity.
Qed.

Section Gate.
Variables (m : Model) (addr len : word).
Hypothesis G : fix_gate m addr len.

Lemma fix_nZ_pos : 4096 <= fix_nZ len.
Proof.
  unfold fix_nZ, page_round_up_Z, page_size. pose proof (bv_unsigned_in_range 64 len) as Hl. pose proof (fg_len _ _ _ G) as Hn.
  assert (1 <= (bv_unsigned len + 4095) / 4096); [|lia].
  apply Z.div_le_lower_bound; lia.
Qed.

Lemma fix_nZ_mod : fix_nZ len mod 4096 = 0.
Proof. unfold fix_nZ, page_round_up_Z, page_size. apply Z_mod_mult. Qed.

Lemma fix_top_lt : bv_unsigned addr + fix_nZ len < two_pow_64 - 8388608.
Proof.
  pose proof (fg_top _ _ _ G) as Ht. pose proof (alloc_top_room (m_vmmaps m)) as Hr.
  unfold stack_max_size in Hr. lia.
Qed.

Lemma fix_n_unsigned : bv_unsigned (fix_n len) = fix_nZ len.
Proof.
  unfold fix_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof fix_nZ_pos. pose proof fix_top_lt. pose proof (fg_pos _ _ _ G). unfold two_pow_64 in *.
  change (bv_modulus 64) with 18446744073709551616. lia.
Qed.

Lemma fix_addr_not_errno : errno_ret_in mmap_errnos addr = false.
Proof.
  apply errno_ret_in_below; [reflexivity|]. pose proof fix_nZ_pos. pose proof fix_top_lt. lia.
Qed.

Lemma fix_gate_bools :
  w_is0 len = false
  /\ (two_pow_64 <=? bv_unsigned addr + fix_nZ len) = false
  /\ negb (bv_unsigned addr + fix_nZ len <=? alloc_top (m_vmmaps m)) = false
  /\ negb (bv_unsigned addr mod page_size =? 0) = false
  /\ negb (0 <? bv_unsigned addr) = false.
Proof.
  pose proof fix_top_lt as H1. destruct G as [g1 g2 g3 g4 g5 g6].
  split; [apply w_is0_false; exact g1|].
  split; [apply Z.leb_gt; lia|].
  split; [apply negb_false_iff, Z.leb_le; exact g2|].
  split; [apply negb_false_iff, Z.eqb_eq; exact g3|].
  apply negb_false_iff, Z.ltb_lt; exact g4.
Qed.

End Gate.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FixRw.
Variables (m : Model) (addr len prot flags fd off : word).
Hypothesis S : fix_rw_shape prot flags off = true.
Hypothesis G : fix_gate m addr len.

Lemma check_mmap_fix_rw (eff : SyscallEffect) :
  check_mmap addr len prot flags fd off eff m =
  match eff with
  | mkEffectU r [] zs us [] [] =>
      if errno_ret_in mmap_errnos r
      then match zs with
           | _ :: _ => CheckReject
           | [] => match us with
                   | [] => CheckOk m []
                   | _ => if listNN_eqb us [(addr, fix_n len)]
                          then CheckOk (with_mmap_destroyed addr (fix_n len)
                                         (mmap_fixed_destroyed_next (m_vmmaps m) addr (fix_n len)) m) []
                          else CheckReject
                   end
           end
      else match us with
           | _ :: _ => CheckReject
           | [] => if bv_eqb r addr && listNN_eqb zs [(addr, fix_n len)]
                      && mmap_fixed_rw_budget_ok flags m addr (fix_n len)
                   then CheckOk (fix_rw_model flags addr (fix_n len) m) []
                   else CheckReject
           end
  | _ => CheckReject
  end.
Proof.
  unfold fix_rw_shape in S.
  apply andb_prop in S as [S1 S6]. apply andb_prop in S1 as [S1 S5]. apply andb_prop in S1 as [S1 S4].
  apply andb_prop in S1 as [S1 S3]. apply andb_prop in S1 as [S1 S2].
  apply negb_true_iff in S3, S4, S5.
  destruct (fix_gate_bools m addr len G) as (B1 & B2 & B3 & B4 & B5).
  unfold check_mmap. rewrite S1, S2, B1, S3, S4, S5, S6. cbn [negb]. cbv zeta.
  fold (fix_nZ len). rewrite B2, B3, B4, B5. fold (fix_n len).
  rewrite (fg_res _ _ _ G), (fg_own _ _ _ G). cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma chk_fix_rw (eff : SyscallEffect) (m' : Model) (evs : list event) :
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = true
  \/ (eff = mkEffect addr [] [(addr, fix_n len)] /\ m' = fix_rw_model flags addr (fix_n len) m /\ evs = []
      /\ mmap_fixed_rw_budget_ok flags m addr (fix_n len) = true).
Proof.
  rewrite check_mmap_fix_rw. destruct eff as [r ws zs us cs ci]. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct cs; [|destruct zs, us; discriminate]. destruct ci; [|destruct zs, us; discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:E; [intros _; left; reflexivity|].
  destruct us; [|discriminate].
  destruct (bv_eqb r addr && listNN_eqb zs [(addr, fix_n len)] && mmap_fixed_rw_budget_ok flags m addr (fix_n len)) eqn:E2; [|discriminate].
  intros H. injection H as <- <-. right.
  apply andb_prop in E2 as [E2 E5]. apply andb_prop in E2 as [E3 E4].
  apply bv_eqb_eq in E3. apply listNN_eqb_eq in E4. subst r zs. repeat split; try reflexivity. exact E5.
Qed.

Lemma chk_fix_rw_grant :
  mmap_fixed_rw_budget_ok flags m addr (fix_n len) = true ->
  check_mmap addr len prot flags fd off (mkEffect addr [] [(addr, fix_n len)]) m
  = CheckOk (fix_rw_model flags addr (fix_n len) m) [].
Proof.
  intros Hb. rewrite check_mmap_fix_rw. rewrite (fix_addr_not_errno m addr len G).
  rewrite Hb. replace (bv_eqb addr addr) with true by (symmetry; apply bv_eqb_eq; reflexivity).
  replace (listNN_eqb [(addr, fix_n len)] [(addr, fix_n len)]) with true by (symmetry; apply listNN_eqb_eq; reflexivity).
  reflexivity.
Qed.

Lemma chk_fix_rw_modeled (eff : SyscallEffect) : check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  rewrite check_mmap_fix_rw. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct cs; [|destruct zs, us; discriminate]. destruct ci; [|destruct zs, us; discriminate].
  destruct (errno_ret_in mmap_errnos r).
  - destruct zs; [|discriminate]. destruct us; [discriminate|]. destruct (listNN_eqb _ _); discriminate.
  - destruct us; [|discriminate]. destruct (_ && _); discriminate.
Qed.

End FixRw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FixNone.
Variables (m : Model) (addr len prot flags fd off : word).
Hypothesis S : fix_none_shape prot flags off = true.
Hypothesis G : fix_gate m addr len.

Lemma check_mmap_fix_none (eff : SyscallEffect) :
  check_mmap addr len prot flags fd off eff m =
  match eff with
  | mkEffectU r [] [] us [] [] =>
      if errno_ret_in mmap_errnos r
      then match us with
           | [] => CheckOk m []
           | _ => if listNN_eqb us [(addr, fix_n len)]
                  then CheckOk (with_mmap_destroyed addr (fix_n len)
                                 (mmap_fixed_destroyed_next (m_vmmaps m) addr (fix_n len)) m) []
                  else CheckReject
           end
      else if bv_eqb r addr && listNN_eqb us [(addr, fix_n len)]
           then CheckOk (fix_none_model flags addr (fix_n len) m) []
           else CheckReject
  | _ => CheckReject
  end.
Proof.
  unfold fix_none_shape in S.
  apply andb_prop in S as [S1 S5]. apply andb_prop in S1 as [S1 S4].
  apply andb_prop in S1 as [S1 S3]. apply andb_prop in S1 as [S1 S2].
  apply negb_true_iff in S3, S4.
  destruct (fix_gate_bools m addr len G) as (B1 & B2 & B3 & B4 & B5).
  unfold check_mmap. rewrite S1, S2, B1, S3, S4, S5. cbn [negb]. cbv zeta.
  fold (fix_nZ len). rewrite B2, B3, B4, B5. fold (fix_n len).
  rewrite (fg_res _ _ _ G), (fg_own _ _ _ G). cbn [andb]. reflexivity.
Qed.

Lemma chk_fix_none (eff : SyscallEffect) (m' : Model) (evs : list event) :
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = true
  \/ (eff = mkEffectU addr [] [] [(addr, fix_n len)] [] [] /\ m' = fix_none_model flags addr (fix_n len) m /\ evs = []).
Proof.
  rewrite check_mmap_fix_none. destruct eff as [r ws zs us cs ci]. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate].
  destruct ci; [|destruct us; discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:E; [intros _; left; reflexivity|].
  destruct (bv_eqb r addr && listNN_eqb us [(addr, fix_n len)]) eqn:E2; [|discriminate].
  intros H. injection H as <- <-. right.
  apply andb_prop in E2 as [E3 E4].
  apply bv_eqb_eq in E3. apply listNN_eqb_eq in E4. subst r us. repeat split; reflexivity.
Qed.

Lemma chk_fix_none_grant :
  check_mmap addr len prot flags fd off (mkEffectU addr [] [] [(addr, fix_n len)] [] []) m
  = CheckOk (fix_none_model flags addr (fix_n len) m) [].
Proof.
  rewrite check_mmap_fix_none. rewrite (fix_addr_not_errno m addr len G).
  replace (bv_eqb addr addr) with true by (symmetry; apply bv_eqb_eq; reflexivity).
  replace (listNN_eqb [(addr, fix_n len)] [(addr, fix_n len)]) with true by (symmetry; apply listNN_eqb_eq; reflexivity).
  reflexivity.
Qed.

Lemma chk_fix_none_modeled (eff : SyscallEffect) : check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  rewrite check_mmap_fix_none. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate].
  destruct ci; [|destruct us; discriminate].
  destruct (errno_ret_in mmap_errnos r).
  - destruct us; [discriminate|]. destruct (listNN_eqb _ _); discriminate.
  - destruct (_ && _); discriminate.
Qed.

End FixNone.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_222 (i : SyscallInput) (m : Model) (r : word) :
  bv_unsigned (in_sysno i) = 222 -> refusal_b i m r = errno_ret_in mmap_errnos r.
Proof. intros H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_222_of_errno (i : SyscallInput) (m : Model) (r : word) :
  bv_unsigned (in_sysno i) = 222 -> errno_ret_in mmap_errnos r = true -> refusal_b i m r = true.
Proof. intros H E. rewrite (refusal_222 i m r H). exact E. Qed.

Lemma injected_off_222 (cfg : SpuriousCfg) (i : SyscallInput) :
  bv_unsigned (in_sysno i) = 222 -> sc_alloc cfg = false -> injected_family_off cfg i = true.
Proof. intros H Hc. unfold injected_family_off. rewrite H. cbn. rewrite Hc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spurious_222 (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (eff eff' : SyscallEffect) (m' : Model) (evs' : list event) :
  bv_unsigned (in_sysno i) = 222 -> sc_alloc cfg = false ->
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  check_syscall i eff' m = CheckOk m' evs' -> errno_ret_in mmap_errnos (eff_ret eff') = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros H Hc E Hok E'. split; [exact (injected_off_222 cfg i H Hc)|].
  split; [exact (refusal_222_of_errno i m _ H E)|].
  exists eff', m', evs'. split; [apply check_syscall_ok_iff; exact Hok | rewrite (refusal_222 i m _ H); exact E'].
Qed.
(* [comment removed for export] *)
Definition repl_lazy (flags a n : word) (lz : list (word * word)) : list (word * word) :=
  if mmap_noreserve_b flags
  then lazy_interior a n ++ maps_subtract lz (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  else maps_subtract lz (bv_unsigned a) (bv_unsigned a + bv_unsigned n).

Lemma repl_lazy_eq (flags a n : word) (m : Model) :
  m_vm_lazy (with_mmap_replacement flags a n m) = repl_lazy flags a n (m_vm_lazy m).
Proof.
  unfold with_mmap_replacement, with_mmap_backing, repl_lazy. destruct (mmap_noreserve_b flags); destruct m as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
Qed.

Lemma repl_mat_eq (flags a n : word) (m : Model) :
  m_vm_materialized (with_mmap_replacement flags a n m)
  = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof.
  unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); destruct m as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
Qed.

Lemma repl_vmmaps_eq (flags a n : word) (m : Model) : m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof.
  unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); destruct m as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
Qed.

Lemma repl_lazy_out (flags a n : word) (lz : list (word * word)) (x : Z) :
  nowrap lz -> bv_unsigned a + bv_unsigned n <= two64 -> inrb (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x = false ->
  inlb (repl_lazy flags a n lz) x = inlb lz x.
Proof.
  intros Hnw Ha Hx. pose proof (bv_unsigned_in_range 64 n) as Hn. unfold repl_lazy.
  destruct (mmap_noreserve_b flags).
  - rewrite inlb_app, (inlb_interior_out a n x Ha) by (apply inrb_false; exact Hx). cbn [orb].
    rewrite inlb_subtract by assumption. rewrite Hx, andb_true_r. reflexivity.
  - rewrite inlb_subtract by assumption. rewrite Hx, andb_true_r. reflexivity.
Qed.

Lemma repl_lazy_in (flags a n : word) (lz : list (word * word)) (x : Z) :
  mmap_noreserve_b flags = true -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  inrb (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x = true -> inlb (repl_lazy flags a n lz) x = true.
Proof.
  intros Hf Ha Hn Hx. unfold repl_lazy. rewrite Hf, inlb_app. apply inrb_iff in Hx.
  rewrite (lazy_interior_aligned a n ltac:(lia) Ha Hn). rewrite inlb_cons. unfold inpb. rewrite bas_mk, bsz_mk.
  replace (bv_unsigned a <=? x) with true by (symmetry; apply Z.leb_le; lia).
  replace (x <? bv_unsigned a + bv_unsigned n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma with_vmmaps_lazy_eq (h : VmMaps) (m : Model) : m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

Lemma with_vmmaps_mat_eq (h : VmMaps) (m : Model) : m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

Lemma with_vmmaps_vmmaps_eq (h : VmMaps) (m : Model) : m_vmmaps (with_vmmaps h m) = h.
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

Lemma repl_tid (flags a n : word) (m : Model) : m_tid (with_mmap_replacement flags a n m) = m_tid m.
Proof. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma repl_fds (flags a n : word) (m : Model) : m_fds (with_mmap_replacement flags a n m) = m_fds m.
Proof. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma repl_fs (flags a n : word) (m : Model) : m_fs (with_mmap_replacement flags a n m) = m_fs m.
Proof. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma repl_halted (flags a n : word) (m : Model) : m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_vmmaps_halted_eq (h : VmMaps) (m : Model) : m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.

Lemma destroyed_halted (a n : word) (h : VmMaps) (m : Model) : m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. reflexivity. Qed.

Lemma fix_rw_halted (flags a n : word) (m : Model) : m_halted (fix_rw_model flags a n m) = m_halted m.
Proof. unfold fix_rw_model. rewrite repl_halted. reflexivity. Qed.

Lemma fix_none_halted (flags a n : word) (m : Model) : m_halted (fix_none_model flags a n m) = m_halted m.
Proof. unfold fix_none_model. rewrite repl_halted. reflexivity. Qed.

Lemma chk_fix_rw_halted (m : Model) (addr len prot flags fd off : word) (eff : SyscallEffect) (m' : Model) (evs : list event) :
  fix_rw_shape prot flags off = true -> fix_gate m addr len ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> evs = [] /\ m_halted m' = m_halted m.
Proof.
  intros S G. rewrite (check_mmap_fix_rw m addr len prot flags fd off S G). destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct cs; [|destruct zs, us; discriminate]. destruct ci; [|destruct zs, us; discriminate].
  destruct (errno_ret_in mmap_errnos r).
  - destruct zs; [|discriminate]. destruct us.
    + intros H. injection H as <- <-. split; reflexivity.
    + destruct (listNN_eqb _ _); [|discriminate]. intros H. injection H as <- <-. split; reflexivity.
  - destruct us; [|discriminate]. destruct (_ && _); [|discriminate]. intros H. injection H as <- <-.
    split; [reflexivity | apply fix_rw_halted].
Qed.

Lemma chk_fix_none_halted (m : Model) (addr len prot flags fd off : word) (eff : SyscallEffect) (m' : Model) (evs : list event) :
  fix_none_shape prot flags off = true -> fix_gate m addr len ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> evs = [] /\ m_halted m' = m_halted m.
Proof.
  intros S G. rewrite (check_mmap_fix_none m addr len prot flags fd off S G). destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate].
  destruct ci; [|destruct us; discriminate].
  destruct (errno_ret_in mmap_errnos r).
  - destruct us.
    + intros H. injection H as <- <-. split; reflexivity.
    + destruct (listNN_eqb _ _); [|discriminate]. intros H. injection H as <- <-. split; reflexivity.
  - destruct (_ && _); [|discriminate]. intros H. injection H as <- <-. split; [reflexivity | apply fix_none_halted].
Qed.

Lemma fix_rw_vmmaps (flags a n : word) (m : Model) : m_vmmaps (fix_rw_model flags a n m) = mmap_fixed_rw_next (m_vmmaps m) a n.
Proof. unfold fix_rw_model. rewrite repl_vmmaps_eq. apply with_vmmaps_vmmaps_eq. Qed.

Lemma fix_none_vmmaps (flags a n : word) (m : Model) :
  m_vmmaps (fix_none_model flags a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
      ((a, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. unfold fix_none_model. rewrite repl_vmmaps_eq. apply with_vmmaps_vmmaps_eq. Qed.

Section UsedFix.
Variables (m : Model) (flags addr n : word).
Hypothesis Hmaps : nowrap (vm_maps (m_vmmaps m)).
Hypothesis Hna : nowrap (vm_noaccess (m_vmmaps m)).
Hypothesis Hlz : nowrap (m_vm_lazy m).
Hypothesis Hrange : bv_unsigned addr + bv_unsigned n <= two64.

Local Notation lo := (bv_unsigned addr).
Local Notation hi := (bv_unsigned addr + bv_unsigned n).

Lemma fix_rw_BWm (x : Z) :
  BWm (fix_rw_model flags addr n m) x
  = BW (vm_maps (m_vmmaps m)) (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi) (repl_lazy flags addr n (m_vm_lazy m)) x.
Proof. unfold BWm, fix_rw_model. rewrite repl_vmmaps_eq, repl_lazy_eq, with_vmmaps_vmmaps_eq, with_vmmaps_lazy_eq. reflexivity. Qed.

Lemma fix_none_BWm (x : Z) :
  BWm (fix_none_model flags addr n m) x
  = BW (vm_maps (m_vmmaps m)) ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) lo hi) (repl_lazy flags addr n (m_vm_lazy m)) x.
Proof. unfold BWm, fix_none_model. rewrite repl_vmmaps_eq, repl_lazy_eq, with_vmmaps_vmmaps_eq, with_vmmaps_lazy_eq. reflexivity. Qed.

Lemma fix_rw_maps : vm_maps (m_vmmaps (fix_rw_model flags addr n m)) = vm_maps (m_vmmaps m).
Proof. unfold fix_rw_model. rewrite repl_vmmaps_eq, with_vmmaps_vmmaps_eq. reflexivity. Qed.

Lemma fix_none_maps : vm_maps (m_vmmaps (fix_none_model flags addr n m)) = vm_maps (m_vmmaps m).
Proof. unfold fix_none_model. rewrite repl_vmmaps_eq, with_vmmaps_vmmaps_eq. reflexivity. Qed.

Lemma fix_rw_mat_le : (length (m_vm_materialized (fix_rw_model flags addr n m)) <= length (m_vm_materialized m))%nat.
Proof. unfold fix_rw_model. rewrite repl_mat_eq, with_vmmaps_mat_eq. apply filter_length_le'. Qed.

Lemma fix_none_mat_le : (length (m_vm_materialized (fix_none_model flags addr n m)) <= length (m_vm_materialized m))%nat.
Proof. unfold fix_none_model. rewrite repl_mat_eq, with_vmmaps_mat_eq. apply filter_length_le'. Qed.

(* [comment removed for export] *)
Lemma fix_BW_out (na' : list (word * word)) (x : Z) :
  inrb lo hi x = false -> inlb na' x = inlb (vm_noaccess (m_vmmaps m)) x ->
  BW (vm_maps (m_vmmaps m)) na' (repl_lazy flags addr n (m_vm_lazy m)) x = BWm m x.
Proof. intros E Ena. unfold BWm, BW. rewrite Ena, (repl_lazy_out flags addr n _ x Hlz Hrange E). reflexivity. Qed.

(* [comment removed for export] *)
Lemma used_fix_rw (K : Z) :
  0 <= K -> (forall x, lo <= x < hi -> SW (vm_maps (m_vmmaps m)) x <= K) ->
  vm_backing_used (fix_rw_model flags addr n m) <= vm_backing_used m + K * bv_unsigned n.
Proof.
  intros HK HSW. pose proof (bv_unsigned_in_range 64 n) as Hn.
  cut (vm_backing_used (fix_rw_model flags addr n m) <= vm_backing_used m + K * (hi - lo)).
  { intros X. replace (hi - lo) with (bv_unsigned n) in X by lia. exact X. }
  apply used_le_pw; try assumption; try lia.
  - rewrite fix_rw_maps. exact Hmaps.
  - intros x Hx. rewrite fix_rw_BWm. destruct (inrb lo hi x) eqn:E.
    + pose proof (BW_le_SW (vm_maps (m_vmmaps m)) (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi) (repl_lazy flags addr n (m_vm_lazy m)) x) as X1.
      pose proof (BW_nonneg (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) x) as X2. fold (BWm m x) in X2.
      apply inrb_iff in E. specialize (HSW x E). lia.
    + rewrite (fix_BW_out _ x E); [lia|]. rewrite inlb_subtract by assumption. rewrite E, andb_true_r. reflexivity.
  - exact fix_rw_mat_le.
Qed.

(* [comment removed for export] *)
Lemma used_fix_rw_lazy :
  mmap_noreserve_b flags = true -> bv_unsigned addr mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  vm_backing_used (fix_rw_model flags addr n m) <= vm_backing_used m.
Proof.
  intros Hf Ha Hn4. apply used_le_pw0; try assumption.
  - rewrite fix_rw_maps. exact Hmaps.
  - intros x Hx. rewrite fix_rw_BWm. destruct (inrb lo hi x) eqn:E.
    + unfold BW at 1. rewrite (repl_lazy_in flags addr n _ x Hf Ha Hn4 E).
      pose proof (BW_nonneg (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) x) as X2. fold (BWm m x) in X2.
      destruct (inlb _ x); lia.
    + rewrite (fix_BW_out _ x E); [lia|]. rewrite inlb_subtract by assumption. rewrite E, andb_true_r. reflexivity.
  - exact fix_rw_mat_le.
Qed.

(* [comment removed for export] *)
Lemma used_fix_none : vm_backing_used (fix_none_model flags addr n m) <= vm_backing_used m.
Proof.
  apply used_le_pw0; try assumption.
  - rewrite fix_none_maps. exact Hmaps.
  - intros x Hx. rewrite fix_none_BWm. destruct (inrb lo hi x) eqn:E.
    + unfold BW at 1. rewrite inlb_cons. unfold inpb. rewrite bas_mk, bsz_mk. fold (inrb lo hi x). rewrite E. cbn [orb].
      pose proof (BW_nonneg (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) x) as X2. fold (BWm m x) in X2. lia.
    + rewrite (fix_BW_out _ x E); [lia|]. rewrite inlb_cons. unfold inpb. rewrite bas_mk, bsz_mk. fold (inrb lo hi x). rewrite E. cbn [orb].
      rewrite inlb_subtract by assumption. rewrite E, andb_true_r. reflexivity.
  - exact fix_none_mat_le.
Qed.

End UsedFix.

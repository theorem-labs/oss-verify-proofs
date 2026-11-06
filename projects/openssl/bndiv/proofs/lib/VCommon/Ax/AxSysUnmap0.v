(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct AxMeasure AxSysFix.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_215 (i : SyscallInput) (m : Model) (r : word) : bv_unsigned (in_sysno i) = 215 -> refusal_b i m r = false.
Proof. intros H. unfold refusal_b. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) addr)
       (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
       (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Record unmap_gate (m : Model) (addr len : word) : Prop := mkUnmapGate {
  ug_len : bv_unsigned len <> 0;
  ug_al  : bv_unsigned addr mod 4096 = 0;
  ug_top : bv_unsigned addr + fix_nZ len <= TASK_SIZE;
  ug_has : map_has (vm_maps (m_vmmaps m)) addr (fix_n len) = true
}.

Section Unmap.
Variables (m : Model) (addr len : word).
Hypothesis G : unmap_gate m addr len.

Lemma check_munmap_has (eff : SyscallEffect) :
  check_munmap addr len eff m =
  match eff with
  | mkEffectU r [] [] us [] [] =>
      if w_is0 r && listNN_eqb us [(addr, fix_n len)] then CheckOk (munmap_model addr (fix_n len) m) [] else CheckReject
  | _ => CheckReject
  end.
Proof.
  destruct G as [g1 g2 g3 g4]. unfold check_munmap.
  replace (negb (bv_unsigned addr mod page_size =? 0)) with false by (symmetry; apply negb_false_iff, Z.eqb_eq; exact g2).
  rewrite (w_is0_false len g1). cbn [orb]. cbv zeta. fold (fix_nZ len).
  replace (TASK_SIZE <? bv_unsigned addr + fix_nZ len) with false by (symmetry; apply Z.ltb_ge; exact g3).
  fold (fix_n len). rewrite g4. reflexivity.
Qed.

Lemma chk_munmap (eff : SyscallEffect) (m' : Model) (evs : list event) :
  check_munmap addr len eff m = CheckOk m' evs ->
  eff = mkEffectU (Z_to_bv 64 0) [] [] [(addr, fix_n len)] [] [] /\ m' = munmap_model addr (fix_n len) m /\ evs = [].
Proof.
  rewrite check_munmap_has. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (w_is0 r && listNN_eqb us [(addr, fix_n len)]) eqn:E; [|discriminate].
  intros H. injection H as <- <-. apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1.
  apply listNN_eqb_eq in E2. subst r us. repeat split; reflexivity.
Qed.

Lemma chk_munmap_ok :
  check_munmap addr len (mkEffectU (Z_to_bv 64 0) [] [] [(addr, fix_n len)] [] []) m = CheckOk (munmap_model addr (fix_n len) m) [].
Proof.
  rewrite check_munmap_has.
  replace (w_is0 (Z_to_bv 64 0)) with true by reflexivity.
  replace (listNN_eqb [(addr, fix_n len)] [(addr, fix_n len)]) with true by (symmetry; apply listNN_eqb_eq; reflexivity).
  reflexivity.
Qed.

Lemma chk_munmap_modeled (eff : SyscallEffect) : check_munmap addr len eff m <> CheckUnmodeled.
Proof.
  rewrite check_munmap_has. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (_ && _); discriminate.
Qed.

End Unmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma destroyed_vmmaps_eq (a n : word) (h : VmMaps) (m : Model) : m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

Lemma destroyed_lazy_eq (a n : word) (h : VmMaps) (m : Model) :
  m_vm_lazy (with_mmap_destroyed a n h m) = maps_subtract (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

Lemma destroyed_mat_eq (a n : word) (h : VmMaps) (m : Model) :
  m_vm_materialized (with_mmap_destroyed a n h m)
  = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SW_filter_le (f : word * word -> bool) (l : list (word * word)) (x : Z) : SW (List.filter f l) x <= SW l x.
Proof.
  induction l as [|p r IH]; cbn [List.filter SW]; [lia|]. destruct (f p); cbn [SW]; destruct (inpb p x); lia.
Qed.

Lemma nowrap_filter (f : word * word -> bool) (l : list (word * word)) : nowrap l -> nowrap (List.filter f l).
Proof. intros H p Hp. apply filter_In in Hp as [Hp _]. exact (H p Hp). Qed.

Lemma SW_remove_in (l : list (word * word)) (addr : word) (lo hi x : Z) :
  (forall q, In q l -> fst q <> addr -> iv_disj lo hi q) -> lo <= x < hi -> SW (map_remove l addr) x = 0.
Proof.
  intros Hd Hx. apply SW_zero_iff. intros [q [Hq Hi]]. unfold map_remove in Hq. apply filter_In in Hq as [Hq Hne].
  apply negb_true_iff in Hne. assert (Hn : fst q <> addr).
  { intros E. rewrite E in Hne. assert (T : bv_eqb addr addr = true) by (apply bv_eqb_eq; reflexivity). congruence. }
  specialize (Hd q Hq Hn). unfold iv_disj in Hd. lia.
Qed.

Section UsedUnmap.
Variables (m : Model) (addr n : word).
Hypothesis Hmaps : nowrap (vm_maps (m_vmmaps m)).
Hypothesis Hna : nowrap (vm_noaccess (m_vmmaps m)).
Hypothesis Hlz : nowrap (m_vm_lazy m).
Hypothesis Hothers : forall q, In q (vm_maps (m_vmmaps m)) -> fst q <> addr ->
  iv_disj (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) q.

Local Notation lo := (bv_unsigned addr).
Local Notation hi := (bv_unsigned addr + bv_unsigned n).

Lemma used_munmap : vm_backing_used (munmap_model addr n m) <= vm_backing_used m.
Proof.
  apply used_le_pw0; try assumption.
  - unfold munmap_model. rewrite destroyed_vmmaps_eq. cbn [vm_maps]. apply nowrap_filter. exact Hmaps.
  - intros x Hx. unfold BWm at 1, munmap_model. rewrite destroyed_vmmaps_eq, destroyed_lazy_eq. cbn [vm_maps vm_noaccess].
    pose proof (BW_nonneg (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) x) as X2. fold (BWm m x) in X2.
    destruct (inrb lo hi x) eqn:E.
    + apply inrb_iff in E. pose proof (BW_le_SW (map_remove (vm_maps (m_vmmaps m)) addr) (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi)
        (maps_subtract (m_vm_lazy m) lo hi) x) as X1. rewrite (SW_remove_in _ addr lo hi x Hothers E) in X1. lia.
    + unfold BWm, BW. rewrite !inlb_subtract by assumption. rewrite E, !andb_true_r.
      pose proof (SW_filter_le (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps m)) x) as X3. fold (map_remove (vm_maps (m_vmmaps m)) addr) in X3.
      destruct (inlb (vm_noaccess (m_vmmaps m)) x); [lia|]. destruct (inlb (m_vm_lazy m) x); lia.
  - unfold munmap_model. rewrite destroyed_mat_eq. apply filter_length_le'.
Qed.

End UsedUnmap.

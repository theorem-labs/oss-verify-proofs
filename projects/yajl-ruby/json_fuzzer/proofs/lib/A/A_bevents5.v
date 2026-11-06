(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow NodesA_mm NodesA_mmW NodesA_madv BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase KLiveCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot
  AsanBudget AsanBudget2 AsanRepFrame AsanFrame AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_live A_policy5 A_budget5 A_slack5 A_bundle A_benv5 A_balloc5 A_mmchk5 AF_fakestack_rep AF_place.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)

Lemma eager_used_sem : forall m, model_ivs_wf m ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof. intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia. Qed.

(* [comment removed for export] *)
Ltac mproj := rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vm_materialized_vm_add_lazy,
                      ?m_vmmaps_vm_forget_range, ?m_vm_lazy_vm_forget_range, ?m_vm_materialized_vm_forget_range,
                      ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?m_vm_materialized_with_vmmaps,
                      ?m_vmmaps_with_vm_backing, ?m_vm_lazy_with_vm_backing, ?m_vm_materialized_with_vm_backing in *.

Section T.
Variables (m : Model) (A L : Z).
Hypothesis WF : model_ivs_wf m.
Hypothesis HA : 0 <= A.
Hypothesis HL : 0 < L.
Hypothesis HE : A + L < 2^64.
Hypothesis AA : A mod 4096 = 0.
Hypothesis LA : L mod 4096 = 0.
Let a : word := Z_to_bv 64 A.
Let n : word := Z_to_bv 64 L.
Let h' : VmMaps := mmap_fixed_rw_next (m_vmmaps m) a n.

Lemma ua : bv_unsigned a = A. Proof. apply u64_small. lia. Qed.
Lemma un : bv_unsigned n = L. Proof. apply u64_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition m_commit : Model := vm_forget_range A (A + L) (with_vmmaps h' m).

Lemma commit_maps : vm_maps (m_vmmaps m_commit) = vm_maps (m_vmmaps m).
Proof. unfold m_commit. mproj. reflexivity. Qed.
Lemma commit_reserved : vm_reserved (m_vmmaps m_commit) = vm_reserved (m_vmmaps m).
Proof. unfold m_commit. mproj. reflexivity. Qed.
Lemma commit_limit : vm_limit (m_vmmaps m_commit) = vm_limit (m_vmmaps m).
Proof. unfold m_commit. mproj. reflexivity. Qed.
Lemma commit_noaccess : vm_noaccess (m_vmmaps m_commit) = maps_subtract (vm_noaccess (m_vmmaps m)) A (A + L).
Proof. unfold m_commit. mproj. unfold h', mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ua, un. reflexivity. Qed.
Lemma commit_lazy : m_vm_lazy m_commit = maps_subtract (m_vm_lazy m) A (A + L).
Proof. unfold m_commit. mproj. reflexivity. Qed.
Lemma commit_mat : m_vm_materialized m_commit = List.filter (page_outside_range A (A + L)) (m_vm_materialized m).
Proof. unfold m_commit. mproj. reflexivity. Qed.
Lemma commit_wf : model_ivs_wf m_commit.
Proof.
  unfold m_commit. pose proof WF as (Wm & Wn & Wl & Wsp). unfold model_ivs_wf. mproj. unfold h', mmap_fixed_rw_next. cbn [vm_maps vm_noaccess vm_init_sp].
  rewrite ua, un. split; [exact Wm|]. split; [apply maps_subtract_wf; [exact Wn| lia]|]. split; [apply maps_subtract_wf; [exact Wl| lia]| exact Wsp].
Qed.
Lemma commit_eager : eager_used m_commit <= eager_used m + overlap_sum (vm_maps (m_vmmaps m)) A (A + L).
Proof.
  rewrite (eager_used_sem _ commit_wf), (eager_used_sem _ WF). rewrite commit_maps, commit_noaccess, commit_lazy.
  pose proof WF as (Wm & Wn & Wl & Wsp).
  destruct (maps_subtract_sem _ A (A + L) Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ A (A + L) Wl ltac:(lia)) as (_ & _ & Cl).
  unfold overlap_sum. eapply Z.le_trans; [| apply sum_count_or_le].
  apply sum_count_mono. intros x Hx. rewrite !covered_app in Hx. rewrite covered_app. rewrite Cn, Cl in Hx.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng A (A + L) x); cbn in Hx |- *; congruence.
Qed.

(* [comment removed for export] *)
Lemma commit_budget_ok : forall flags,
  mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  overlap_sum (vm_maps (m_vmmaps m)) A (A + L) <= L ->
  vm_backing_used m + L <= vm_limit (m_vmmaps m) ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) m a n = true.
Proof.
  intros flags NR OV B. apply mmap_fixed_rw_budget_ok_commit_intro; [exact NR| exact WF|]. rewrite ua, un. lia.
Qed.
(* [comment removed for export] *)
Lemma replacement_commit : forall flags, mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  with_mmap_replacement (Z_to_bv 64 flags) a n (with_vmmaps h' m) = m_commit.
Proof. intros flags NR. unfold with_mmap_replacement, with_mmap_backing, m_commit. rewrite NR, ua, un. reflexivity. Qed.
End T.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section T2.
Variables (m : Model) (R L : Z).     (* [comment removed for export] *)
Hypothesis WF : model_ivs_wf m.
Hypothesis HR : 0 <= R.
Hypothesis HL : 0 < L.
Hypothesis HE : R + L < 2^64.
Hypothesis RA : R mod 4096 = 0.
Hypothesis LA : L mod 4096 = 0.
Let r : word := Z_to_bv 64 R.
Let n : word := Z_to_bv 64 L.
Lemma ur : bv_unsigned r = R. Proof. apply u64_small. lia. Qed.
Lemma un2 : bv_unsigned n = L. Proof. apply u64_small. lia. Qed.
Let h2 : VmMaps := mkVmMapsFull (vm_reserved (m_vmmaps m)) ((r, n) :: vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m))
                                (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).

(* [comment removed for export] *)
Definition m_anon : Model := with_vmmaps h2 m.
(* [comment removed for export] *)
Definition m_anon_nr : Model := vm_add_lazy r n (with_vmmaps h2 m).

Lemma anon_maps : vm_maps (m_vmmaps m_anon) = (r, n) :: vm_maps (m_vmmaps m). Proof. reflexivity. Qed.
Lemma anon_reserved : vm_reserved (m_vmmaps m_anon) = vm_reserved (m_vmmaps m). Proof. reflexivity. Qed.
Lemma anon_limit : vm_limit (m_vmmaps m_anon) = vm_limit (m_vmmaps m). Proof. reflexivity. Qed.
Lemma anon_noaccess : vm_noaccess (m_vmmaps m_anon) = vm_noaccess (m_vmmaps m). Proof. reflexivity. Qed.
Lemma anon_lazy : m_vm_lazy m_anon = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma anon_mat : m_vm_materialized m_anon = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma anon_wf : model_ivs_wf m_anon.
Proof.
  pose proof WF as (Wm & Wn & Wl & Wsp). unfold model_ivs_wf, m_anon. mproj. cbn [vm_maps vm_noaccess vm_init_sp].
  split; [apply ivs_wf_cons; [unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S; cbn [fst snd]; rewrite ur, un2; lia| exact Wm]|]. split; [exact Wn|]. split; [exact Wl| exact Wsp].
Qed.
Lemma anon_eager : eager_used m_anon <= eager_used m + L.
Proof.
  rewrite (eager_used_sem _ anon_wf), (eager_used_sem _ WF). rewrite anon_maps, anon_noaccess, anon_lazy.
  cbn [sum_count]. pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (BackingAlgebra.B (r, n)) (Z.to_nat (BackingAlgebra.S (r, n)))) as ZL.
  unfold iv_count. unfold BackingAlgebra.S in *. cbn [snd] in *. rewrite un2 in *. rewrite Z2Nat.id in ZL by lia. lia.
Qed.

Lemma anr_maps : vm_maps (m_vmmaps m_anon_nr) = (r, n) :: vm_maps (m_vmmaps m). Proof. unfold m_anon_nr. mproj. reflexivity. Qed.
Lemma anr_reserved : vm_reserved (m_vmmaps m_anon_nr) = vm_reserved (m_vmmaps m). Proof. unfold m_anon_nr. mproj. reflexivity. Qed.
Lemma anr_limit : vm_limit (m_vmmaps m_anon_nr) = vm_limit (m_vmmaps m). Proof. unfold m_anon_nr. mproj. reflexivity. Qed.
Lemma anr_noaccess : vm_noaccess (m_vmmaps m_anon_nr) = vm_noaccess (m_vmmaps m). Proof. unfold m_anon_nr. mproj. reflexivity. Qed.
Lemma anr_lazy : m_vm_lazy m_anon_nr = (r, n) :: m_vm_lazy m.
Proof. unfold m_anon_nr. mproj. rewrite (lazy_interior_aligned r n) by (rewrite ?ur, ?un2; unfold page_size; lia). reflexivity. Qed.
Lemma anr_mat : m_vm_materialized m_anon_nr = m_vm_materialized m. Proof. unfold m_anon_nr. mproj. reflexivity. Qed.
Lemma anr_wf : model_ivs_wf m_anon_nr.
Proof.
  pose proof WF as (Wm & Wn & Wl & Wsp). pose proof anon_wf as (Wm' & _). unfold model_ivs_wf. rewrite anr_maps, anr_noaccess, anr_lazy.
  split; [exact Wm'|]. split; [exact Wn|]. split; [apply ivs_wf_cons; [unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S; cbn [fst snd]; rewrite ur, un2; lia| exact Wl]|].
  unfold m_anon_nr. mproj. exact Wsp.
Qed.
(* [comment removed for export] *)
Lemma anr_eager : eager_used m_anon_nr <= eager_used m.
Proof.
  rewrite (eager_used_sem _ anr_wf), (eager_used_sem _ WF). rewrite anr_maps, anr_noaccess, anr_lazy.
  cbn [sum_count].
  assert (Z0 : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ (r, n) :: m_vm_lazy m) x)) (r, n) = 0).
  { unfold iv_count. apply zcount_false. intros x Hx. unfold BackingAlgebra.B, BackingAlgebra.S in Hx. cbn [fst snd] in Hx.
    rewrite covered_app. unfold covered at 2. cbn [existsb]. unfold in_iv at 1, BackingAlgebra.B, BackingAlgebra.S. cbn [fst snd].
    unfold in_rng. rewrite Z2Nat.id in Hx by (rewrite un2; lia).
    replace ((bv_unsigned r <=? x) && (x <? bv_unsigned r + bv_unsigned n)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    cbn. rewrite Bool.orb_true_r. reflexivity. }
  rewrite Z0. cbn [Z.add].
  apply sum_count_mono. intros x Hx. rewrite covered_app in Hx |- *. unfold covered at 2 in Hx. cbn [existsb] in Hx. fold (covered (m_vm_lazy m) x) in Hx.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (in_iv (r, n) x), (covered (m_vm_lazy m) x); cbn in Hx |- *; congruence.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition m_unmap : Model := munmap_post R L m.

Lemma unmap_maps : vm_maps (m_vmmaps m_unmap) = map_remove (vm_maps (m_vmmaps m)) r.
Proof. unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. reflexivity. Qed.
Lemma unmap_reserved : vm_reserved (m_vmmaps m_unmap) = vm_reserved (m_vmmaps m).
Proof. unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. reflexivity. Qed.
Lemma unmap_limit : vm_limit (m_vmmaps m_unmap) = vm_limit (m_vmmaps m).
Proof. unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. reflexivity. Qed.
Lemma unmap_noaccess : vm_noaccess (m_vmmaps m_unmap) = maps_subtract (vm_noaccess (m_vmmaps m)) R (R + L).
Proof. unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. reflexivity. Qed.
Lemma unmap_lazy : m_vm_lazy m_unmap = maps_subtract (m_vm_lazy m) R (R + L).
Proof. unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. rewrite ur, un2. reflexivity. Qed.
Lemma unmap_mat : m_vm_materialized m_unmap = List.filter (page_outside_range R (R + L)) (m_vm_materialized m).
Proof. unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. rewrite ur, un2. reflexivity. Qed.
Lemma unmap_wf : model_ivs_wf m_unmap.
Proof.
  pose proof WF as (Wm & Wn & Wl & Wsp). unfold model_ivs_wf. rewrite unmap_maps, unmap_noaccess, unmap_lazy.
  split; [apply ivs_wf_filter; exact Wm|]. split; [apply maps_subtract_wf; [exact Wn| lia]|]. split; [apply maps_subtract_wf; [exact Wl| lia]|].
  unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. exact Wsp.
Qed.
(* [comment removed for export] *)
Lemma unmap_eager :
  (forall e, In e (map_remove (vm_maps (m_vmmaps m)) r) -> ehi e <= R \/ R + L <= elo e) ->
  eager_used m_unmap <= eager_used m.
Proof.
  intros DJ. rewrite (eager_used_sem _ unmap_wf), (eager_used_sem _ WF). rewrite unmap_maps, unmap_noaccess, unmap_lazy.
  pose proof WF as (Wm & Wn & Wl & Wsp).
  destruct (maps_subtract_sem _ R (R + L) Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ R (R + L) Wl ltac:(lia)) as (_ & _ & Cl).
  transitivity (sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (map_remove (vm_maps (m_vmmaps m)) r)).
  - (* [comment removed for export] *)
    apply Z.eq_le_incl. revert DJ. generalize (map_remove (vm_maps (m_vmmaps m)) r) as l.
    induction l as [|e l IH]; intros DJ; [reflexivity|]. cbn [sum_count]. rewrite (IH ltac:(intros e' He'; apply DJ; right; exact He')). f_equal.
    unfold iv_count. apply zcount_ext. intros x Hx. pose proof (DJ e (or_introl eq_refl)) as De.
    unfold elo, ehi, BackingAlgebra.B, BackingAlgebra.S in *. rewrite Z2Nat.id in Hx by (pose proof (bv_unsigned_in_range 64 (snd e)); lia).
    rewrite !covered_app, Cn, Cl. unfold in_rng.
    assert (FR : (R <=? x) && (x <? R + L) = false).
    { apply Bool.andb_false_iff. clear -De Hx. destruct De as [De|De]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia]. }
    rewrite FR. cbn [negb]. rewrite !Bool.andb_true_r. reflexivity.
  - (* [comment removed for export] *)
    unfold map_remove. generalize (vm_maps (m_vmmaps m)) as l. induction l as [|e l IH]; [reflexivity|].
    cbn [List.filter sum_count]. pose proof (zcount_nonneg (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (BackingAlgebra.B e) (Z.to_nat (BackingAlgebra.S e))).
    unfold iv_count in *. destruct (negb (bv_eqb (fst e) r)); cbn [sum_count]; unfold iv_count; lia.
Qed.
End T2.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_incl : forall a sz lo hi e', iv_wf (a, sz) -> 0 <= lo ->
  In e' (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e' /\ ehi e' <= bv_unsigned a + bv_unsigned sz
    /\ ((elo e' = bv_unsigned a /\ elo e' < lo /\ ehi e' <= lo) \/ (ehi e' = bv_unsigned a + bv_unsigned sz /\ hi <= elo e')).
Proof.
  intros a sz lo hi e' WFp Hlo H. unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in WFp. cbn [fst snd] in WFp.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
  unfold iv_subtract in H. apply in_app_iff in H. unfold elo, ehi.
  destruct H as [H|H].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct H]. apply Z.ltb_lt in E. destruct H as [<-|[]]. cbn [fst snd].
    rewrite u64_small by (clear -E Ra Rs WFp Hlo; lia). clear -E Ra Rs WFp Hlo. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct H]. apply Z.ltb_lt in E. destruct H as [<-|[]]. cbn [fst snd].
    rewrite !u64_small by (clear -E Ra Rs WFp Hlo; lia). clear -E Ra Rs WFp Hlo. lia.
Qed.

Lemma maps_subtract_incl : forall l lo hi e', ivs_wf l -> 0 <= lo ->
  In e' (maps_subtract l lo hi) -> exists e, In e l /\ elo e <= elo e' /\ ehi e' <= ehi e
    /\ ((elo e' = elo e /\ elo e' < lo /\ ehi e' <= lo) \/ (ehi e' = ehi e /\ hi <= elo e')).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi e' WF Hlo H; [destruct H|].
  cbn [maps_subtract] in H. apply in_app_iff in H. apply ivs_wf_cons_inv in WF as [W1 W2].
  destruct H as [H|H].
  - exists (a, sz). split; [left; reflexivity|]. exact (iv_subtract_incl a sz lo hi e' W1 Hlo H).
  - destruct (IH lo hi e' W2 Hlo H) as (e & He & R). exists e. split; [right; exact He| exact R].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_keeps : forall l lo hi e, ivs_wf l -> 0 <= lo -> lo <= hi ->
  In e l -> 0 < bv_unsigned (snd e) -> (ehi e <= lo \/ hi <= elo e) ->
  exists e', In e' (maps_subtract l lo hi) /\ elo e' = elo e /\ ehi e' = ehi e.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi e WF Hlo Hlh Hin Hpos Hd; [destruct Hin|].
  apply ivs_wf_cons_inv in WF as [W1 W2]. cbn [maps_subtract].
  destruct Hin as [<-|Hin].
  - unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in W1. unfold elo, ehi in *. cbn [fst snd] in *.
    pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
    unfold iv_subtract. destruct Hd as [Hd|Hd].
    + exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app fst snd].
      split; [left; reflexivity|]. rewrite u64_small by lia. split; [reflexivity| lia].
    + destruct (bv_unsigned a <? lo) eqn:E1; [apply Z.ltb_lt in E1; exfalso; lia|].
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
      exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)).
      split; [left; reflexivity|]. cbn [fst snd]. rewrite !u64_small by lia. lia.
  - destruct (IH lo hi e W2 Hlo Hlh Hin Hpos Hd) as (e' & He' & R). exists e'. split; [apply in_app_iff; right; exact He'| exact R].
Qed.

(* [comment removed for export] *)
Lemma inside_subtract : forall l lo hi p n, ivs_wf l -> 0 <= lo <= hi -> 0 < n ->
  inside l p n -> (p + n <= lo \/ hi <= p) -> inside (maps_subtract l lo hi) p n.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi p n WF LH Hn (e & He & R1 & R2) D; [destruct He|].
  apply ivs_wf_cons_inv in WF as [W1 W2]. cbn [maps_subtract].
  destruct He as [<-|He].
  - unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in W1. unfold elo, ehi in *. cbn [fst snd] in *.
    pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
    unfold iv_subtract. destruct D as [D|D].
    + exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app fst snd].
      split; [left; reflexivity|]. unfold elo, ehi. cbn [fst snd]. rewrite u64_small by lia. lia.
    + exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)).
      split; [apply in_app_iff; left; apply in_app_iff; right; rewrite (proj2 (Z.ltb_lt _ _)) by lia; left; reflexivity|]. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small by lia. lia.
  - destruct (IH lo hi p n W2 LH Hn (ex_intro _ e (conj He (conj R1 R2))) D) as (e' & He' & Q). exists e'. split; [apply in_app_iff; right; exact He'| exact Q].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_pos : forall l lo hi e', ivs_wf l -> 0 <= lo <= hi ->
  (forall e, In e l -> 0 < bv_unsigned (snd e)) -> In e' (maps_subtract l lo hi) -> 0 < bv_unsigned (snd e').
Proof.
  induction l as [|[a sz] l IH]; intros lo hi e' WF LH POS H; [destruct H|].
  apply ivs_wf_cons_inv in WF as [W1 W2]. cbn [maps_subtract] in H. apply in_app_iff in H. destruct H as [H|H].
  - unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in W1. cbn [fst snd] in W1.
    pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
    pose proof (POS _ (or_introl eq_refl)) as P0. cbn [snd] in P0.
    unfold iv_subtract in H. apply in_app_iff in H. destruct H as [H|H].
    + destruct (bv_unsigned a <? lo) eqn:E; [|destruct H]. apply Z.ltb_lt in E. destruct H as [<-|[]]. cbn [snd]. rewrite u64_small by lia. lia.
    + destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct H]. apply Z.ltb_lt in E. destruct H as [<-|[]]. cbn [snd]. rewrite u64_small by lia. lia.
  - eapply IH; [exact W2| exact LH| intros e He; apply POS; right; exact He| exact H].
Qed.

Lemma nao_subtract : forall noacc maps lo hi, ivs_wf noacc -> 0 <= lo <= hi ->
  nao noacc maps -> nao (maps_subtract noacc lo hi) maps.
Proof.
  intros noacc maps lo hi WF LH NA e' He'. split.
  - eapply maps_subtract_pos; [exact WF| exact LH| intros e He; exact (proj1 (NA e He))| exact He'].
  - destruct (maps_subtract_incl _ lo hi e' WF ltac:(lia) He') as (e & He & R1 & R2 & _).
    destruct (NA e He) as (_ & m & Hm & Q1 & Q2 & Q3). exists m. split; [exact Hm|]. split; [lia|]. split; [lia|].
    exact (shband_clear_sub e e' Q3 R1 R2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma clear_ofp_pieces : forall l l' x n,
  clear_ofp l x n -> (forall e', In e' l' -> exists e, In e l /\ elo e <= elo e' /\ ehi e' <= ehi e) -> clear_ofp l' x n.
Proof.
  intros l l' x n C P e' He' Hpos. destruct (P e' He') as (e & He & R1 & R2).
  pose proof (C e He) as Ce. unfold elo, ehi in *.
  assert (0 < bv_unsigned (snd e)) by lia. specialize (Ce ltac:(assumption)). lia.
Qed.
(* [comment removed for export] *)
Definition offband (x n : Z) : Prop := x + n <= 0x7fff7000 \/ kHighMemBeg <= x.
Lemma offband_high : forall x n, kHighMemBeg <= x -> offband x n.
Proof. intros x n H. right. exact H. Qed.
Lemma offband_app_mem : forall x n, app_mem x n -> offband x n.
Proof. intros x n H. unfold app_mem, offband in *. rewrite kLowAppEnd_val in H. lia. Qed.
Lemma clear_of_pieces_band : forall l l' x n,
  clear_of l x n -> offband x n ->
  (forall e', In e' l' -> (exists e, In e l /\ elo e <= elo e' /\ ehi e' <= ehi e) \/ (0x7fff7000 <= elo e' /\ ehi e' <= kHighMemBeg)) -> clear_of l' x n.
Proof.
  intros l l' x n C HK P e' He'. destruct (P e' He') as [(e & He & R1 & R2)|[B1 B2]].
  - pose proof (C e He). lia.
  - unfold offband in HK. lia.
Qed.
Lemma inside_same : forall l l' x n, l' = l -> inside l x n -> inside l' x n.
Proof. intros l l' x n -> H. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AKG.
Variables (E : aenv) (a a' : astate) (mo1 mo' : Model) (A L : Z).
Hypothesis K : AKern E a mo1.
Hypothesis WE : wf_env E.
Hypothesis MAPS : vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo1).
Hypothesis HA : 0 <= A.
Hypothesis HL : 0 < L.
Hypothesis WFN : ivs_wf (vm_noaccess (m_vmmaps mo1)).
Hypothesis NOACC : vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mo1)) A (A + L).
Lemma NAV : forall e', In e' (vm_noaccess (m_vmmaps mo')) -> exists e, In e (vm_noaccess (m_vmmaps mo1)) /\ elo e <= elo e' /\ ehi e' <= ehi e
                 /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + L <= elo e')).
Proof. intros e' He'. rewrite NOACC in He'. apply maps_subtract_incl; [exact WFN| exact HA| exact He']. Qed.
Hypothesis LAV : forall e', In e' (m_vm_lazy mo') -> exists e, In e (m_vm_lazy mo1) /\ elo e <= elo e' /\ ehi e' <= ehi e
                 /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + L <= elo e')).
(* [comment removed for export] *)
Hypothesis Esec : as_sec a' = as_sec a.
Hypothesis Enb : as_node_blocks a' = as_node_blocks a.
Hypothesis Esb : as_store_blocks a' = as_store_blocks a.

Lemma eager_rw_keep : forall x n, eager_rw mo1 x n -> eager_rw mo' x n.
Proof.
  intros x n (I1 & I2 & I3). split; [| split].
  - unfold inside in *. rewrite MAPS. exact I1.
  - eapply clear_ofp_pieces; [exact I2|]. intros e' He'. destruct (NAV e' He') as (e & He & R1 & R2 & _). exists e. auto.
  - intros e' He'. destruct (LAV e' He') as (e & He & R1 & R2 & _). pose proof (I3 e He). lia.
Qed.

(* [comment removed for export] *)
Lemma eager_rw_extend : forall x n, 0 <= n -> x + n = A ->
  (0 < n -> eager_rw mo1 x n) -> inside (vm_maps (m_vmmaps mo1)) x (n + L) -> eager_rw mo' x (n + L).
Proof.
  intros x n Hn HxA OLD INS. split; [| split].
  - unfold inside in *. rewrite MAPS. exact INS.
  - intros e' He' Hpos. destruct (NAV e' He') as (e & He & R1 & R2 & PC).
    destruct (Z.eq_dec n 0) as [->|NZ]; [lia|]. destruct (OLD ltac:(lia)) as (_ & C2 & _).
    pose proof (C2 e He) as Ce. assert (0 < bv_unsigned (snd e)) by (unfold elo, ehi in *; lia). specialize (Ce ltac:(assumption)). lia.
  - intros e' He'. destruct (LAV e' He') as (e & He & R1 & R2 & PC).
    destruct (Z.eq_dec n 0) as [->|NZ]; [lia|]. destruct (OLD ltac:(lia)) as (_ & _ & C3). pose proof (C3 e He). lia.
Qed.

Lemma lazy_keep5 : forall e', In e' (m_vm_lazy mo') ->
  exists e, In e (m_vm_lazy mo1) /\ elo e <= elo e' /\ ehi e' <= ehi e /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + L <= elo e')).
Proof. exact LAV. Qed.

(* [comment removed for export] *)
Lemma AKern_grow_user : forall c0,
  1 <= c0 <= kLargestClassID ->
  A = region_beg (ae_space_beg E) c0 + rg_mapped_user (get_region a c0) -> 0 <= rg_mapped_user (get_region a c0) ->
  rg_mapped_user (get_region a' c0) = rg_mapped_user (get_region a c0) + L ->
  rg_mapped_fa (get_region a' c0) = rg_mapped_fa (get_region a c0) ->
  (forall c, 1 <= c <= kLargestClassID -> c <> c0 -> get_region a' c = get_region a c) ->
  as_ptr_committed a' = as_ptr_committed a ->
  rg_mapped_user (get_region a c0) + L <= kFreeArrayOffset ->
  AKern E a' mo'.
Proof.
  intros c0 Hc0 HAe MU0 GU GF OTH PTR BND.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  pose proof alloc_ceiling_range as ACR.
  destruct K. pose proof ak_resv_geom as (G1 & G2 & G3).
  assert (SBH : kHighMemBeg <= ae_space_beg E) by lia.
  assert (RBc : forall c, 1 <= c <= kLargestClassID -> kHighMemBeg <= region_beg (ae_space_beg E) c) by (intros c Hc; unfold region_beg, kRegionSize; nia).
  constructor.
  - rewrite MAPS. exact ak_resv.
  - exact ak_resv_geom.
  - destruct ak_reginfo as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1|].
    eapply clear_ofp_pieces; [exact I2|]. intros e' He'. destruct (NAV e' He') as (e & He & R1 & R2 & _). exists e. auto.
  - intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
    + rewrite GU. apply eager_rw_extend; [exact MU0| rewrite HAe; reflexivity| intros Hp; exact (ak_user c0 Hc0 Hp)|].
      exists (went (ae_resv_beg E) kResvLen). split; [exact ak_resv|]. unfold went, kwz, elo, ehi, kResvLen, region_beg in *. cbn [fst snd].
      rewrite kHighMemBeg_val in *. rewrite !u64_small by lia. unfold kSpaceSize, kPageSize, kLargestClassID, kRegionSize, kFreeArrayOffset in *. clear -G1 G3 Hc0 MU0 BND HL. nia.
    + rewrite (OTH c Hc NE) in *. apply eager_rw_keep; exact (ak_user c Hc Hm).
  - intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
    + rewrite GF in *. apply eager_rw_keep; exact (ak_fa c0 Hc0 Hm).
    + rewrite (OTH c Hc NE) in *. apply eager_rw_keep; exact (ak_fa c Hc Hm).
  - rewrite MAPS. exact ak_ptr.
  - rewrite PTR. intros Hp. apply eager_rw_keep; exact (ak_ptr_head Hp).
  - rewrite PTR. intros p H1 H2 H3. destruct (ak_ptr_tail p H1 H2 H3) as (e & He & R1 & R2).
    (* [comment removed for export] *)
    assert (DJ : A + L <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= A).
    { unfold region_beg, kRegionSize, kFreeArrayOffset, kLargestClassID, kSpaceSize, kPageSize, kPtrArrayLen, kResvLen in *.
      clear -E20 G1 G3 HAe Hc0 MU0 BND HL. nia. }
    rewrite NOACC. apply inside_subtract; [exact WFN| lia| unfold kPageSize; lia| exists e; auto|].
    unfold kPageSize, kPtrArrayLen in *. clear -DJ H1 H2. destruct (as_ptr_committed a =? 0); unfold kPtrArrayCommit in *; lia.
  - intros sc Hsc. rewrite Esec in Hsc. destruct (ak_sec sc Hsc) as [S1 S2]. split; [rewrite MAPS; exact S1| apply eager_rw_keep; exact S2].
  - apply eager_rw_keep; exact ak_thread.
  - apply eager_rw_keep; exact ak_depot_nodes.
  - destruct ak_store as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1| eapply clear_ofp_pieces; [exact I2| intros e' He'; destruct (NAV e' He') as (e & He & R1 & R2 & _); exists e; auto]].
  - intros b Hb. rewrite Enb in Hb. destruct (ak_node_blocks b Hb) as [N1 N2]. split; [rewrite MAPS; exact N1|].
    apply eager_rw_keep. exact N2.
  - intros b Hb. rewrite Esb in Hb. destruct (ak_store_blocks b Hb) as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1| eapply clear_ofp_pieces; [exact I2| intros e' He'; destruct (NAV e' He') as (e & He & R1 & R2 & _); exists e; auto]].
  - intros b len Hb. rewrite Enb, Esb, Esec in *. exact (ak_blocks_sep b len Hb).
  - intros e' He'. destruct (LAV e' He') as (e & He & R1 & R2 & PC). rewrite Esb, PTR.
    destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]].
    + left. lia.
    + right; left. lia.
    + right; right; left. destruct X as (b & Hb & X1 & X2). exists b. split; [exact Hb| lia].
    + right; right; right; left. lia.
    + right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [lia|]. split; [lia|]. split.
      * intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
        -- rewrite GU in *. destruct (Z.eq_dec (rg_mapped_user (get_region a c0)) 0) as [Z0|NZ].
           ++ rewrite Z0 in *. clear -HAe PC R1 R2 HL. lia.
           ++ destruct (X2 c0 Hc0 ltac:(lia)); clear -HAe PC R1 R2 HL H MU0; lia.
        -- rewrite (OTH c Hc NE) in *. destruct (X2 c Hc Hm); lia.
      * intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
        -- rewrite GF in *. destruct (X3 c0 Hc0 Hm); lia.
        -- rewrite (OTH c Hc NE) in *. destruct (X3 c Hc Hm); lia.
  - rewrite Esec. exact ak_store_sep.
Qed.
Lemma AKern_grow_fa : forall c0,
  1 <= c0 <= kLargestClassID ->
  A = free_array (ae_space_beg E) c0 + rg_mapped_fa (get_region a c0) -> 0 <= rg_mapped_fa (get_region a c0) ->
  rg_mapped_fa (get_region a' c0) = rg_mapped_fa (get_region a c0) + L ->
  rg_mapped_user (get_region a' c0) = rg_mapped_user (get_region a c0) ->
  (forall c, 1 <= c <= kLargestClassID -> c <> c0 -> get_region a' c = get_region a c) ->
  as_ptr_committed a' = as_ptr_committed a ->
  rg_mapped_fa (get_region a c0) + L <= kRegionSize - kFreeArrayOffset ->
  AKern E a' mo'.
Proof.
  intros c0 Hc0 HAe MU0 GU GF OTH PTR BND.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  pose proof alloc_ceiling_range as ACR.
  destruct K. pose proof ak_resv_geom as (G1 & G2 & G3).
  assert (SBH : kHighMemBeg <= ae_space_beg E) by lia.
  assert (RBc : forall c, 1 <= c <= kLargestClassID -> kHighMemBeg <= region_beg (ae_space_beg E) c) by (intros c Hc; unfold region_beg, kRegionSize; nia).
  constructor.
  - rewrite MAPS. exact ak_resv.
  - exact ak_resv_geom.
  - destruct ak_reginfo as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1|].
    eapply clear_ofp_pieces; [exact I2|]. intros e' He'. destruct (NAV e' He') as (e & He & R1 & R2 & _). exists e. auto.
  - intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
    + rewrite GF in *. apply eager_rw_keep; exact (ak_user c0 Hc0 Hm).
    + rewrite (OTH c Hc NE) in *. apply eager_rw_keep; exact (ak_user c Hc Hm).
  - intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
    + rewrite GU. apply eager_rw_extend; [exact MU0| rewrite HAe; reflexivity| intros Hp; exact (ak_fa c0 Hc0 Hp)|].
      exists (went (ae_resv_beg E) kResvLen). split; [exact ak_resv|]. unfold went, kwz, elo, ehi, kResvLen, free_array, region_beg in *. cbn [fst snd].
      rewrite kHighMemBeg_val in *. rewrite !u64_small by lia. unfold kSpaceSize, kPageSize, kLargestClassID, kRegionSize, kFreeArrayOffset in *. clear -G1 G3 Hc0 MU0 BND HL. nia.
    + rewrite (OTH c Hc NE) in *. apply eager_rw_keep; exact (ak_fa c Hc Hm).
  - rewrite MAPS. exact ak_ptr.
  - rewrite PTR. intros Hp. apply eager_rw_keep; exact (ak_ptr_head Hp).
  - rewrite PTR. intros p H1 H2 H3. destruct (ak_ptr_tail p H1 H2 H3) as (e & He & R1 & R2).
    (* [comment removed for export] *)
    assert (DJ : A + L <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= A).
    { unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kLargestClassID, kSpaceSize, kPageSize, kPtrArrayLen, kResvLen in *.
      clear -E20 G1 G3 HAe Hc0 MU0 BND HL. nia. }
    rewrite NOACC. apply inside_subtract; [exact WFN| lia| unfold kPageSize; lia| exists e; auto|].
    unfold kPageSize, kPtrArrayLen in *. clear -DJ H1 H2. destruct (as_ptr_committed a =? 0); unfold kPtrArrayCommit in *; lia.
  - intros sc Hsc. rewrite Esec in Hsc. destruct (ak_sec sc Hsc) as [S1 S2]. split; [rewrite MAPS; exact S1| apply eager_rw_keep; exact S2].
  - apply eager_rw_keep; exact ak_thread.
  - apply eager_rw_keep; exact ak_depot_nodes.
  - destruct ak_store as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1| eapply clear_ofp_pieces; [exact I2| intros e' He'; destruct (NAV e' He') as (e & He & R1 & R2 & _); exists e; auto]].
  - intros b Hb. rewrite Enb in Hb. destruct (ak_node_blocks b Hb) as [N1 N2]. split; [rewrite MAPS; exact N1|].
    apply eager_rw_keep. exact N2.
  - intros b Hb. rewrite Esb in Hb. destruct (ak_store_blocks b Hb) as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1| eapply clear_ofp_pieces; [exact I2| intros e' He'; destruct (NAV e' He') as (e & He & R1 & R2 & _); exists e; auto]].
  - intros b len Hb. rewrite Enb, Esb, Esec in *. exact (ak_blocks_sep b len Hb).
  - intros e' He'. destruct (LAV e' He') as (e & He & R1 & R2 & PC). rewrite Esb, PTR.
    destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]].
    + left. lia.
    + right; left. lia.
    + right; right; left. destruct X as (b & Hb & X1 & X2). exists b. split; [exact Hb| lia].
    + right; right; right; left. lia.
    + right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [lia|]. split; [lia|]. split.
      * intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
        -- rewrite GF in *. destruct (X2 c0 Hc0 Hm); lia.
        -- rewrite (OTH c Hc NE) in *. destruct (X2 c Hc Hm); lia.
      * intros c Hc Hm. destruct (Z.eq_dec c c0) as [->|NE].
        -- rewrite GU in *. destruct (Z.eq_dec (rg_mapped_fa (get_region a c0)) 0) as [Z0|NZ].
           ++ rewrite Z0 in *. clear -HAe PC R1 R2 HL. lia.
           ++ destruct (X3 c0 Hc0 ltac:(lia)); clear -HAe PC R1 R2 HL H MU0; lia.
        -- rewrite (OTH c Hc NE) in *. destruct (X3 c Hc Hm); lia.
  - rewrite Esec. exact ak_store_sep.
Qed.

(* [comment removed for export] *)
Lemma AKern_commit_ptr :
  A = ae_ptr_array E -> L = kPtrArrayCommit -> as_ptr_committed a = 0 -> as_ptr_committed a' = kChunksBlockCount ->
  (forall c, 1 <= c <= kLargestClassID -> get_region a' c = get_region a c) ->
  AKern E a' mo'.
Proof.
  intros HAe HLe P0 P1 REG.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  pose proof alloc_ceiling_range as ACR.
  destruct K. pose proof ak_resv_geom as (G1 & G2 & G3).
  assert (SBH : kHighMemBeg <= ae_space_beg E) by lia.
  assert (RBc : forall c, 1 <= c <= kLargestClassID -> kHighMemBeg <= region_beg (ae_space_beg E) c) by (intros c Hc; unfold region_beg, kRegionSize; nia).
  constructor.
  - rewrite MAPS. exact ak_resv.
  - exact ak_resv_geom.
  - destruct ak_reginfo as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1|].
    eapply clear_ofp_pieces; [exact I2|]. intros e' He'. destruct (NAV e' He') as (e & He & R1 & R2 & _). exists e. auto.
  - intros c Hc Hm. rewrite (REG c Hc) in *. apply eager_rw_keep; exact (ak_user c Hc Hm).
  - intros c Hc Hm. rewrite (REG c Hc) in *. apply eager_rw_keep; exact (ak_fa c Hc Hm).
  - rewrite MAPS. exact ak_ptr.
  - intros _. replace kPtrArrayCommit with (0 + L) by lia. rewrite <- HAe. apply eager_rw_extend; [lia| lia| intros X; lia|].
    exists (went (ae_ptr_array E) kPtrArrayLen). split; [exact ak_ptr|]. unfold went, kwz, elo, ehi, kPtrArrayLen, kPtrArrayCommit in *. cbn [fst snd].
    rewrite kHighMemBeg_val in *. rewrite !u64_small by lia. lia.
  - rewrite P1. intros p H1 H2 H3. change (kChunksBlockCount =? 0) with false in H1. cbn in H1.
    pose proof (ak_ptr_tail p) as T. rewrite P0 in T. cbn in T. specialize (T ltac:(lia) H2 H3).
    rewrite NOACC. apply inside_subtract; [exact WFN| lia| unfold kPageSize; lia| exact T| right; lia].
  - intros sc Hsc. rewrite Esec in Hsc. destruct (ak_sec sc Hsc) as [S1 S2]. split; [rewrite MAPS; exact S1| apply eager_rw_keep; exact S2].
  - apply eager_rw_keep; exact ak_thread.
  - apply eager_rw_keep; exact ak_depot_nodes.
  - destruct ak_store as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1| eapply clear_ofp_pieces; [exact I2| intros e' He'; destruct (NAV e' He') as (e & He & R1 & R2 & _); exists e; auto]].
  - intros b Hb. rewrite Enb in Hb. destruct (ak_node_blocks b Hb) as [N1 N2]. split; [rewrite MAPS; exact N1|].
    apply eager_rw_keep. exact N2.
  - intros b Hb. rewrite Esb in Hb. destruct (ak_store_blocks b Hb) as [I1 I2]. split; [unfold inside in *; rewrite MAPS; exact I1| eapply clear_ofp_pieces; [exact I2| intros e' He'; destruct (NAV e' He') as (e & He & R1 & R2 & _); exists e; auto]].
  - intros b len Hb. rewrite Enb, Esb, Esec in *. exact (ak_blocks_sep b len Hb).
  - intros e' He'. destruct (LAV e' He') as (e & He & R1 & R2 & PC). rewrite Esb, P1. change (kChunksBlockCount =? 0) with false. cbn iota.
    destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]].
    + left. lia.
    + right; left. lia.
    + right; right; left. destruct X as (b & Hb & X1 & X2). exists b. split; [exact Hb| lia].
    + right; right; right; left. rewrite P0 in X. cbn in X. clear -X HAe HLe PC R1 R2 HL. unfold kPtrArrayCommit in *. lia.
    + right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [lia|]. split; [lia|]. split.
      * intros c Hc Hm. rewrite (REG c Hc) in *. destruct (X2 c Hc Hm); lia.
      * intros c Hc Hm. rewrite (REG c Hc) in *. destruct (X3 c Hc Hm); lia.
  - rewrite Esec. exact ak_store_sep.
Qed.
End AKG.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_size_val : page_size = 4096. Proof. reflexivity. Qed.

Lemma LI_filter : forall Sx N EB mo mo' f,
  LI Sx N EB mo -> m_vm_materialized mo' = List.filter f (m_vm_materialized mo) ->
  eager_used mo' <= EB -> vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) -> LI Sx N EB mo'.
Proof.
  intros Sx N EB mo mo' f L HM HE HL. eapply LI_transfer; [exact L| | | exact HE| exact HL].
  - intros p Hp. rewrite HM in Hp. apply filter_In in Hp. tauto.
  - rewrite HM. apply NoDup_filter. exact (li_nodup _ _ _ _ L).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ev.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
(* [comment removed for export] *)
Hypothesis LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0.              (* [comment removed for export] *)
Hypothesis GS_L0 : In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 (2^41)) L0.              (* [comment removed for export] *)
Hypothesis HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0.     (* [comment removed for export] *)
Hypothesis RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0.
Hypothesis RES0_cover : forall x, 0x10000 <= x < 0x603000 -> exists e, In e RES0 /\ elo e <= x < ehi e.
Hypothesis RSVD : forall rr x, In rr (ae_reserved E0) -> fst rr <= x < fst rr + snd rr ->
  (exists e, In e (RES0 ++ L0) /\ elo e <= x < ehi e) \/ alloc_ceiling <= x.
Hypothesis RSVD_pos : Forall (fun rr => 0 < snd rr) (ae_reserved E0).

#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aNzc := (A_bundle.aNz E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).
Ltac cstat := try clear HR0_ok.

Lemma RES0_free : forall mo a A L, KVM L0 RES0 mo a -> 0x603000 <= A -> 0 < L -> A + L < 2^64 ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true.
Proof.
  cstat. intros mo a A L (KR & _) HA HL HE. rewrite KR. apply region_free_intro. intros b sz Hin.
  pose proof (proj1 (Forall_forall _ _) RES0_low _ Hin) as [_ R]. unfold ehi in R. cbn [fst snd] in R.
  pose proof (bv_unsigned_in_range 64 b). pose proof (bv_unsigned_in_range 64 sz).
  unfold iv_overlap. rewrite !u64_small by lia. apply Bool.andb_false_iff. left. apply Z.ltb_ge. unfold bv_modulus in *. lia.
Qed.

Lemma L0_in_maps : forall mo a e, KVM L0 RES0 mo a -> In e L0 -> In e (vm_maps (m_vmmaps mo)).
Proof.
  cstat. intros mo a e (_ & (fog & PM & _) & _) He. eapply Permutation_in; [apply Permutation_sym; exact PM|]. apply in_app_iff. left. exact He.
Qed.

Lemma map_contains_intro : forall l (A L : Z) e, In e l -> elo e <= A -> A + L <= ehi e -> 0 <= A -> 0 <= L -> A + L < 2^64 ->
  map_contains l (Z_to_bv 64 A) (Z_to_bv 64 L) = true.
Proof.
  cstat. intros l A L e He R1 R2 HA HL HE. unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
  unfold elo, ehi in *. rewrite !u64_small by lia. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_apart_pt : forall l (r : word) L e x, 0 < L -> bv_unsigned r + L < 2^64 ->
  region_free l r (Z_to_bv 64 L) = true -> In e l -> elo e <= x < ehi e -> ~ (bv_unsigned r <= x < bv_unsigned r + L).
Proof.
  cstat. intros l r L [b sz] x HL HE RF He Hx IN.
  pose proof (State.region_free_In _ _ _ _ _ RF He) as OV. unfold iv_overlap in OV. unfold elo, ehi in Hx. cbn [fst snd] in Hx.
  pose proof (bv_unsigned_in_range 64 r). pose proof (bv_unsigned_in_range 64 sz). pose proof (bv_unsigned_in_range 64 b). unfold bv_modulus in *.
  rewrite !u64_small in OV by lia. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.

(* [comment removed for export] *)
Lemma grant_placed : forall mo a (r : word) L,
  KVM L0 RES0 mo a -> 0x10000 <= L -> 0 < bv_unsigned r -> bv_unsigned r + L <= alloc_top (m_vmmaps mo) ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L) = true ->
  placed (bv_unsigned r) L.
Proof.
  cstat. intros mo a r L KV HL R0 RC RF. pose proof KV as (KR & _ & _ & _ & _ & TOP). rewrite TOP in RC. pose proof alloc_ceiling_range as CR.
  assert (HE : bv_unsigned r + L < 2^64) by lia.
  assert (APT : forall e x, In e (RES0 ++ L0) -> elo e <= x < ehi e -> ~ (bv_unsigned r <= x < bv_unsigned r + L)).
  { intros e x He Hx. eapply (region_free_apart_pt _ r L e x ltac:(lia) HE RF); [| exact Hx].
    apply in_app_iff in He. apply in_app_iff. destruct He as [He|He]; [left; rewrite KR; exact He| right; exact (L0_in_maps _ _ _ KV He)]. }
  unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. split; [| split; [exact RC|]].
  - (* [comment removed for export] *)
    destruct (Z_lt_dec (bv_unsigned r) 0x603000) as [LT|]; [exfalso| lia].
    destruct (RES0_cover (Z.max (bv_unsigned r) 0x10000) ltac:(lia)) as (e & He & Hx).
    apply (APT e (Z.max (bv_unsigned r) 0x10000) ltac:(apply in_app_iff; left; exact He) Hx). lia.
  - (* [comment removed for export] *)
    destruct (Z_le_dec (bv_unsigned r + L) 0x7fff7000) as [|A1]; [left; assumption|].
    destruct (Z_le_dec 0x10007fff8000 (bv_unsigned r)) as [|A2]; [right; assumption|]. exfalso.
    set (x := Z.max (bv_unsigned r) 0x7fff7000).
    assert (Hx : bv_unsigned r <= x < bv_unsigned r + L /\ 0x7fff7000 <= x < 0x10007fff8000) by (subst x; lia).
    destruct (Z_lt_dec x 0x8fff7000) as [B1|B1].
    + apply (APT _ x ltac:(apply in_app_iff; right; exact LS_L0)); [| exact (proj1 Hx)]. unfold elo, ehi; cbn [fst snd]. rewrite !u64_small by lia. lia.
    + destruct (Z_lt_dec x 0x2008fff7000) as [B2|B2].
      * apply (APT _ x ltac:(apply in_app_iff; right; exact GS_L0)); [| exact (proj1 Hx)]. unfold elo, ehi; cbn [fst snd]. rewrite !u64_small by lia. lia.
      * apply (APT _ x ltac:(apply in_app_iff; right; exact HS_L0)); [| exact (proj1 Hx)]. unfold elo, ehi; cbn [fst snd]. rewrite !u64_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_apart_reserved : forall mo a (r : word) L rr,
  KVM L0 RES0 mo a -> 0 < L -> bv_unsigned r + L <= alloc_top (m_vmmaps mo) ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L) = true ->
  In rr (ae_reserved E0) -> bv_unsigned r + L <= fst rr \/ fst rr + snd rr <= bv_unsigned r.
Proof.
  cstat. intros mo a r L rr KV HL RC RF Hrr. pose proof KV as (KR & _ & _ & _ & _ & TOP). rewrite TOP in RC. pose proof alloc_ceiling_range as CR.
  assert (HE : bv_unsigned r + L < 2^64) by lia.
  destruct (Z_le_dec (bv_unsigned r + L) (fst rr)) as [|A1]; [left; assumption|].
  destruct (Z_le_dec (fst rr + snd rr) (bv_unsigned r)) as [|A2]; [right; assumption|]. exfalso.
  pose proof (proj1 (Forall_forall _ _) RSVD_pos rr Hrr) as POS. cbn beta in POS.
  set (x := Z.max (bv_unsigned r) (fst rr)).
  destruct (RSVD rr x Hrr ltac:(subst x; lia)) as [(e & He & Hx)|ST]; [| subst x; lia].
  eapply (region_free_apart_pt _ r L e x HL HE RF); [| exact Hx| subst x; lia].
  apply in_app_iff in He. apply in_app_iff. destruct He as [He|He]; [left; rewrite KR; exact He| right; exact (L0_in_maps _ _ _ KV He)].
Qed.

(* [comment removed for export] *)
Lemma noacc_band_free : forall mo a A L, KVM L0 RES0 mo a -> 0 < L ->
  ((0x7fff7000 <= A /\ A + L <= 0x8fff7000) \/ (0x2008fff7000 <= A /\ A + L <= 0x10007fff8000)) ->
  region_free (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true.
Proof.
  cstat. intros mo a A L (_ & _ & _ & _ & KNA & _) HL AH. apply region_free_intro. intros b sz Hin.
  destruct (KNA _ Hin) as (P0 & m & _ & _ & _ & [C1 C2]). unfold ehi, elo in C1, C2. cbn [fst snd] in P0, C1, C2.
  pose proof (bv_unsigned_in_range 64 b). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  unfold iv_overlap. rewrite !u64_small by lia. apply Bool.andb_false_iff.
  destruct AH as [[AH1 AH2]|[AH1 AH2]].
  - destruct C1 as [C1|C1]; [left| right]; apply Z.ltb_ge; lia.
  - destruct C2 as [C2|C2]; [left| right]; apply Z.ltb_ge; lia.
Qed.

Theorem ev_madvise_band : forall R R' s mo mo1 (A L : Z),
  ATOKc R R' s mo -> AKern E0 (aps_alloc s) mo ->
  magree mo mo1 -> KIA (aSc s) (aNc s) (aEBc s) mo1 ->
  0 < L ->
  ((0x7fff7000 <= A /\ A + L <= 0x8fff7000) \/ (0x2008fff7000 <= A /\ A + L <= kHighMemBeg)) ->
  madvise_gate mo1 A L /\ ATOKc R R' s (m_madv mo1 A L) /\ AKern E0 (aps_alloc s) (m_madv mo1 A L).
Proof.
  intros R R' s mo mo1 A L TOK K Hag KIA1 L0p AH.
  pose proof (ATOK_magree E0 FSB0 HR0 L0 RES0 EB0 R R' s mo mo1 TOK Hag KIA1) as TOK1.
  pose proof (ATOK_KVM E0 FSB0 HR0 L0 RES0 EB0 R R' s mo1 TOK1) as KV1.
  pose proof (magree_frame _ _ Hag) as (Ffds & Fvm & Flz & _).
  assert (K1 : AKern E0 (aps_alloc s) mo1) by (eapply AKern_frame; [exact Fvm| exact Flz| exact K]).
  rewrite kHighMemBeg_val in AH.
  assert (HE : A + L < 2^64) by lia.
  split; [| split].
  - apply madvise_gate_intro.
    + eapply RES0_free; [exact KV1| lia| lia| lia].
    + destruct AH as [[AH1 AH2]|[AH1 AH2]].
      * eapply map_contains_intro; [exact (L0_in_maps _ _ _ KV1 LS_L0)| | | lia| lia| lia]; unfold elo, ehi; cbn [fst snd]; rewrite ?u64_small by lia; lia.
      * eapply map_contains_intro; [exact (L0_in_maps _ _ _ KV1 HS_L0)| | | lia| lia| lia]; unfold elo, ehi; cbn [fst snd]; rewrite ?u64_small by lia; lia.
    + eapply noacc_band_free; [exact KV1| exact L0p| exact AH].
  - destruct TOK1 as ((LI1 & MI1 & HH1) & OS1 & EV1 & LIM1 & KVM1 & PS1).
    pose proof (m_madv_vmmaps mo1 A L) as EV. pose proof (m_madv_lazy mo1 A L) as EL.
    split; [split; [apply LI_madvise; exact LI1| split; [apply minvA_with_vm_backing; exact MI1| rewrite (proj1 (proj2 (proj2 (m_madv_frame mo1 A L)))); exact HH1]]|].
    split; [unfold OSL in *; rewrite EV; exact OS1|]. split; [exact EV1|]. split; [rewrite EV; exact LIM1|].
    split; [eapply KVM_frame; [exact EV| exact EL| exact KVM1]| rewrite EV; exact PS1].
  - eapply AKern_frame; [apply m_madv_vmmaps| apply m_madv_lazy| exact K1].
Qed.

(* [comment removed for export] *)
Theorem ev_madvise : forall R R' s mo mo1 (sc : secchunk) (PB PL : Z) (Pq : list Z) (Dq : list batch),
  ATOKc R R' s mo -> AKern E0 (aps_alloc s) mo -> AWf E0 Pq Dq (aps_alloc s) -> In sc (as_sec (aps_alloc s)) ->
  magree mo mo1 -> KIA (aSc s) (aNc s) (aEBc s) mo1 ->
  PB mod 4096 = 0 -> PL mod 4096 = 0 -> 0 < PL ->
  kShadowBase + sc_map_beg sc / 8 <= PB -> PB + PL <= kShadowBase + sc_map_beg sc / 8 + sc_map_size sc / 8 ->
  madvise_gate mo1 PB PL /\ ATOKc R R' s (m_madv mo1 PB PL) /\ AKern E0 (aps_alloc s) (m_madv mo1 PB PL).
Proof.
  intros R R' s mo mo1 sc PB PL Pq Dq TOK K WF Hsc Hag KIA1 _ _ L0p B1 B2.
  apply (ev_madvise_band R R' s mo mo1 PB PL TOK K Hag KIA1 L0p).
  pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & SC3 & _) & _).
  destruct (SC3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & _). change kPageSize with 4096 in *.
  pose proof alloc_ceiling_range as CR.
  unfold app_mem in M2. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in *. unfold kShadowBase in *.
  clear -M1 M2 M3 M4 M5 B1 B2 L0p CR. destruct M2 as [M2|M2]; [left| right]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_inside_one : forall l E A L,
  mwf l -> In E l -> elo E <= A -> A + L <= ehi E -> 0 <= L -> overlap_sum l A (A + L) <= L.
Proof.
  cstat. intros l E A L [DJ _] HE R1 R2 HL.
  apply in_split in HE as (l1 & l2 & ->).
  assert (Z0 : forall e, In e (l1 ++ l2) -> iv_count (in_rng A (A + L)) e = 0).
  { intros e He. apply iv_count_in_rng_disjoint. unfold BackingAlgebra.B, BackingAlgebra.S.
    assert (exists i, nth_error (l1 ++ E :: l2) i = Some e /\ i <> length l1) as (i & Hi & Ni).
    { apply in_app_iff in He. destruct He as [He|He].
      - apply In_nth_error in He as (i & Hi).
        assert (Li : (i < length l1)%nat) by (apply (proj1 (nth_error_Some l1 i)); rewrite Hi; discriminate).
        exists i. split; [rewrite nth_error_app1; [exact Hi| exact Li]| lia].
      - apply In_nth_error in He as (i & Hi). exists (length l1 + Datatypes.S i)%nat. split; [| lia].
        rewrite nth_error_app2 by lia. replace (length l1 + Datatypes.S i - length l1)%nat with (Datatypes.S i) by lia. cbn. exact Hi. }
    assert (HEi : nth_error (l1 ++ E :: l2) (length l1) = Some E) by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
    pose proof (DJ _ _ _ _ Hi HEi Ni) as D. unfold elo, ehi in *. lia. }
  unfold overlap_sum in *. rewrite sum_count_app. cbn [sum_count].
  assert (S1 : sum_count (in_rng A (A + L)) l1 = 0).
  { clear -Z0. induction l1 as [|e l1 IH]; [reflexivity|]. cbn [sum_count]. rewrite (Z0 e ltac:(apply in_app_iff; left; left; reflexivity)).
    rewrite IH; [reflexivity|]. intros e' He'. apply Z0. apply in_app_iff in He'. apply in_app_iff. destruct He'; [left; right; assumption| right; assumption]. }
  assert (S2 : sum_count (in_rng A (A + L)) l2 = 0).
  { assert (Z2 : forall e, In e l2 -> iv_count (in_rng A (A + L)) e = 0) by (intros e He; apply Z0; apply in_app_iff; right; exact He).
    clear -Z2. induction l2 as [|e l2 IH]; [reflexivity|]. cbn [sum_count]. rewrite (Z2 e ltac:(left; reflexivity)). rewrite IH; [reflexivity|]. intros e' He'. apply Z2. right. exact He'. }
  rewrite S1, S2. pose proof (iv_count_in_rng_le E A (A + L) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma placed_app_mem : forall X n, placed X n -> app_mem X n.
Proof. cstat. intros X n (P1 & P2 & P3). unfold app_mem, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. rewrite kLowAppEnd_val, kHighMemBeg_val. lia. Qed.
Lemma ptr_placed : forall s, wf_env E0 -> ENVOK E0 FSB0 s -> placed (ae_ptr_array E0) kPtrArrayLen.
Proof.
  cstat. intros s WE EV. pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E16 & E17 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
  destruct EV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  unfold app_mem, img_sep in *. rewrite EI1 in E33. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kPtrArrayLen in *.
  rewrite kLowAppEnd_val, kHighMemBeg_val in E16. clear -E16 E17 E33 EI2. lia.
Qed.

(* [comment removed for export] *)
Definition commit_site (a : astate) (A L : Z) : Prop :=
  (ae_resv_beg E0 <= A /\ A + L <= ae_resv_beg E0 + kResvLen
     /\ (A + L <= ae_ptr_array E0 + (if as_ptr_committed a =? 0 then 0 else kPtrArrayCommit) \/ ae_ptr_array E0 + kPtrArrayLen <= A))
  \/ (A = ae_ptr_array E0 /\ L = kPtrArrayCommit /\ as_ptr_committed a = 0).

Theorem ev_commit_kernel : forall R R' s mo mo1 (A L : Z) (Pq : list Z) (Dq : list batch) (a0 : astate),
  let a := aps_alloc s in
  ATOKc R R' s mo -> AKern E0 a mo -> AWf E0 Pq Dq a0 ->     (* [comment removed for export] *)
  magree mo mo1 -> KIA (aSc s) (aNc s) (aEBc s) mo1 ->
  A mod 4096 = 0 -> L mod 4096 = 0 -> 0 < L -> L <= 4096 * R -> commit_site a A L ->
     (forall eff, mmap_CHK A L 3 0x32 mo1 eff <> CheckUnmodeled)
  /\ (exists eff mo', mmap_CHK A L 3 0x32 mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap A L 3 0x32) mo1 (eff_ret eff) = false)
  /\ (forall eff mo', mmap_CHK A L 3 0x32 mo1 eff = CheckOk mo' [] -> node_refusal (NMmap A L 3 0x32) mo1 (eff_ret eff) = false ->
        eff = mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] [] /\ mm_answer mo1 eff mo' []
        /\ mo' = m_commit mo1 A L
        /\ KIA (aSc s) (aNc s) (aEBc s + L) mo' /\ KVM L0 RES0 mo' a /\ vm_limit (m_vmmaps mo') = 2^39
        /\ OSL aEBc aNzc R s mo' /\ PSL R' (m_vmmaps mo')
        /\ (forall e', In e' (vm_noaccess (m_vmmaps mo')) -> exists e, In e (vm_noaccess (m_vmmaps mo1)) /\ elo e <= elo e' /\ ehi e' <= ehi e
                          /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + L <= elo e')))
        /\ (forall e', In e' (m_vm_lazy mo') -> exists e, In e (m_vm_lazy mo1) /\ elo e <= elo e' /\ ehi e' <= ehi e
                          /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + L <= elo e')))).
Proof.
  intros R R' s mo mo1 A L Pq Dq a0 a TOK K WF Hag KIA1 AA LA L0p LR SITE.
  pose proof (ATOK_magree E0 FSB0 HR0 L0 RES0 EB0 R R' s mo mo1 TOK Hag KIA1) as TOK1.
  pose proof (ATOK_KVM E0 FSB0 HR0 L0 RES0 EB0 R R' s mo1 TOK1) as KV1.
  pose proof (magree_frame _ _ Hag) as (Ffds & Fvm & Flz & _).
  assert (K1 : AKern E0 a mo1) by (eapply AKern_frame; [exact Fvm| exact Flz| exact K]).
  pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & SC3 & _) & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & _).
  pose proof KV1 as (KR & KP & KW & KWF & KNA & TOP). pose proof alloc_ceiling_range as CR.
  pose proof (ptr_placed s WE (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ TOK1)) as PP. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in PP.
  rewrite kHighMemBeg_val in *. unfold commit_site, kResvLen, kPtrArrayLen, kPtrArrayCommit in SITE.
  (* [comment removed for export] *)
  assert (ENT : exists E, In E (vm_maps (m_vmmaps mo1)) /\ elo E <= A /\ A + L <= ehi E /\ 0x603000 <= A /\ A + L <= alloc_ceiling).
  { destruct SITE as [(S1 & S2 & _)|(-> & -> & _)].
    - exists (went (ae_resv_beg E0) kResvLen). split; [exact (ak_resv _ _ _ K1)|]. unfold went, kwz, elo, ehi, kResvLen. cbn [fst snd].
      rewrite !u64_small by lia. lia.
    - exists (went (ae_ptr_array E0) kPtrArrayLen). split; [exact (ak_ptr _ _ _ K1)|]. unfold went, kwz, elo, ehi, kPtrArrayLen in *. cbn [fst snd].
      rewrite !u64_small by lia. lia. }
  destruct ENT as (E & HEin & ER1 & ER2 & ALO & AHI).
  assert (HE : A + L < 2^64) by lia.
  assert (RF : region_free (vm_reserved (m_vmmaps mo1)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true) by (eapply RES0_free; [exact KV1| lia| lia| lia]).
  assert (MC : map_contains (vm_maps (m_vmmaps mo1)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true) by (eapply map_contains_intro; [exact HEin| exact ER1| exact ER2| lia| lia| lia]).
  pose proof (chk_fixed_rw_red A L mo1 AA LA ltac:(lia) L0p ltac:(rewrite TOP; lia) ltac:(rewrite TOP; lia) RF MC) as RED.
  pose proof (ATOK_backing_room E0 FSB0 HR0 L0 RES0 EB0 HR0_ok R R' s mo1 L TOK1 ltac:(lia)) as B1.
  destruct TOK1 as ((LI1 & MI1 & HH1) & [O0 OS1] & EV1 & LIM1 & KVM1 & [P0 PS1]).
  assert (OV : overlap_sum (vm_maps (m_vmmaps mo1)) A (A + L) <= L) by (eapply overlap_sum_inside_one; [exact KW| exact HEin| exact ER1| exact ER2| lia]).
  assert (A0 : 0 <= A) by lia.
  pose proof (commit_budget_ok mo1 A L KWF A0 L0p HE 0x32 (proj1 (proj2 (proj2 (proj2 (proj2 cls_fixed_rw))))) OV B1) as RB.
  split; [| split].
  - intros eff. rewrite RED. apply fixed_match_nu.
  - exists (mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] []). eexists. rewrite RED. split; [apply fixed_match_grant; first [exact RB| rewrite ?TOP; lia]|].
    rewrite refusal_errno. cbn [eff_ret]. apply errno_ret_in_lit. lia.
  - intros eff mo' HC NR. pose proof HC as HC0. rewrite RED in HC. rewrite refusal_errno in NR.
    apply (fixed_match_ok A L mo1) in HC as (_ & -> & BOK & C4); [| exact NR].
    split; [reflexivity|]. pose proof (check_mmap_only _ _ _ _ _ _ _ _ _ _ HC0) as MMA. split; [exact MMA|].
    unfold fixed_post in C4. rewrite (replacement_commit mo1 A L A0 L0p HE 0x32 (proj1 (proj2 (proj2 (proj2 (proj2 cls_fixed_rw)))))) in C4. subst mo'.
    split; [reflexivity|].
    assert (LI' : LI (aSc s) (aNc s) (aEBc s + L) (m_commit mo1 A L)).
    { destruct LI1 as [Q1 Q2 Q3 Q4 Q5]. constructor.
      - rewrite commit_mat. apply NoDup_filter. exact Q1.
      - rewrite commit_mat. apply Forall_forall. intros p Hp. apply filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) Q2 p Hp).
      - exact Q3.
      - pose proof (commit_eager mo1 A L KWF A0 L0p HE). lia.
      - rewrite commit_limit, LIM1, page_size_val. unfold OSL in OS1. rewrite LIM1 in OS1. pose proof (AHK_aN_bound E0 FSB0 HR0 HR0_ok s) as NB.
        change (A_bundle.aN E0 FSB0 HR0 s) with (aNc s) in NB. change (A_bundle.aNz E0 FSB0 HR0 s) with (aNzc s) in OS1. clear -OS1 NB LR L0p. nia. }
    split; [split; [exact LI'| split; [eapply mm_answer_minvA; [exact MMA| exact MI1]| rewrite (mm_answer_halted _ _ _ _ MMA); exact HH1]]|].
    split. { unfold KVM. rewrite commit_reserved, commit_maps. split; [exact KR|]. split; [exact KP|]. split; [exact KW|].
             split; [apply commit_wf; assumption|]. split; [| unfold m_commit; mproj; exact TOP].
             rewrite (commit_noaccess mo1 A L) by lia. apply nao_subtract; [exact (proj1 (proj2 KWF))| lia| exact KNA]. }
    split; [rewrite commit_limit; exact LIM1|].
    split; [unfold OSL in *; rewrite commit_limit; exact OS1|].
    split; [eapply PSL_same; [apply commit_reserved| apply commit_maps| unfold m_commit; mproj; reflexivity| exact PS1]|].
    split.
    + intros e' He'. rewrite (commit_noaccess mo1 A L) in He' by lia. exact (maps_subtract_incl _ A (A + L) e' (proj1 (proj2 KWF)) ltac:(lia) He').
    + intros e' He'. rewrite (commit_lazy mo1 A L) in He'. exact (maps_subtract_incl _ A (A + L) e' (proj1 (proj2 (proj2 KWF))) ltac:(lia) He').
Qed.

(* [comment removed for export] *)
Lemma ATOK_commit : forall R R' s a' mo' L,
  KIA (aSc s) (aNc s) (aEBc s + L) mo' -> KVM L0 RES0 mo' (aps_alloc s) -> vm_limit (m_vmmaps mo') = 2^39 ->
  0 <= R -> OSL aEBc aNzc R s mo' -> ENVOK E0 FSB0 s -> 0 <= R' -> PSL R' (m_vmmaps mo') ->
  a_eager_bytes a' = a_eager_bytes (aps_alloc s) + L ->
  as_sec a' = as_sec (aps_alloc s) -> as_residue a' = as_residue (aps_alloc s) ->
  as_node_blocks a' = as_node_blocks (aps_alloc s) -> as_store_blocks a' = as_store_blocks (aps_alloc s) ->
  0 < L -> L mod 4096 = 0 -> L <= 4096 * R ->
  ATOKc (R - L / 4096) R' (sA a' s) mo'.
Proof.
  cstat. intros R R' s a' mo' L KI KV LIM O0 O1 EV P0 P1 EB Es Er En Est HL LA LR.
  assert (ES : forall w, aSc s w <-> aSc (sA a' s) w).
  { intros w. unfold A_bundle.aS, A_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores. cbn [aps_alloc]. rewrite Es, Er, Est. split; intros X; exact X. }
  assert (EN : aNc (sA a' s) = aNc s).
  { unfold A_bundle.aN, A_policy5.aN, aNa, cover, cover_int, cover_res, cover_st, sA, aps_set_alloc. cbn [aps_alloc]. rewrite Es, Er, Est. reflexivity. }
  assert (EE : aEBc (sA a' s) = aEBc s + L).
  { unfold A_bundle.aEB, A_policy5.aEB, aEBa, sA, aps_set_alloc. cbn [aps_alloc]. rewrite EB, En. lia. }
  assert (EZ : aNzc (sA a' s) = aNzc s).
  { unfold A_bundle.aNz, A_policy5.aNz, aNza, interiors_bound, sA, aps_set_alloc. cbn [aps_alloc]. rewrite Es, Er, Est. reflexivity. }
  split; [| split; [| split; [| split; [| split]]]].
  - destruct KI as (L1 & M1 & H1). split; [| split; [exact M1| exact H1]]. rewrite EN, EE. eapply LI_ext; [exact ES| exact L1].
  - unfold OSL in *. rewrite EE, EZ. split; [clear -HL LA LR O0; Z.div_mod_to_equations; nia| clear -O1 LA LR HL; Z.div_mod_to_equations; nia].
  - unfold ENVOK, sA, aps_set_alloc in *. cbn [aps_env aps_fsbase] in *. exact EV.
  - exact LIM.
  - unfold sA, aps_set_alloc. cbn [aps_alloc]. unfold KVM, amaps in *. rewrite Es, En, Est. exact KV.
  - split; [exact P0| exact P1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ev_anon_rw : forall R R' s mo mo1 (L : Z),
  let a := aps_alloc s in
  ATOKc R R' s mo -> magree mo mo1 -> KIA (aSc s) (aNc s) (aEBc s) mo1 ->
  L mod 4096 = 0 -> 0x10000 <= L <= NMAXA -> L <= 4096 * R ->
     (forall eff, mmap_CHK 0 L 3 0x22 mo1 eff <> CheckUnmodeled)
  /\ (exists eff mo', mmap_CHK 0 L 3 0x22 mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap 0 L 3 0x22) mo1 (eff_ret eff) = false)
  /\ (forall eff mo', mmap_CHK 0 L 3 0x22 mo1 eff = CheckOk mo' [] -> node_refusal (NMmap 0 L 3 0x22) mo1 (eff_ret eff) = false ->
        mm_answer mo1 eff mo' [] /\ exists r, eff = mkEffectU r [] [(r, Z_to_bv 64 L)] [] [] []
        /\ bv_unsigned r mod 4096 = 0 /\ placed (bv_unsigned r) L
        /\ (forall rr, In rr (ae_reserved E0) -> bv_unsigned r + L <= fst rr \/ fst rr + snd rr <= bv_unsigned r)
        /\ region_free (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) r (Z_to_bv 64 L) = true
        /\ r = Z_to_bv 64 (bv_unsigned r)
        /\ mo' = m_anon mo1 (bv_unsigned r) L
        /\ KIA (aSc s) (aNc s) (aEBc s + L) mo' /\ vm_limit (m_vmmaps mo') = 2^39
        /\ vm_maps (m_vmmaps mo') = (r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1)
        /\ vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo1) /\ m_vm_lazy mo' = m_vm_lazy mo1
        /\ vm_reserved (m_vmmaps mo') = RES0 /\ model_ivs_wf mo' /\ alloc_top (m_vmmaps mo') = alloc_ceiling
        /\ nao (vm_noaccess (m_vmmaps mo')) (vm_maps (m_vmmaps mo')) /\ mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1))
        /\ OSL aEBc aNzc R s mo' /\ PSL (R' - (L + NMAXA + 4095)) (m_vmmaps mo')).
Proof.
  intros R R' s mo mo1 L a TOK Hag KIA1 LA HL LR.
  pose proof (ATOK_magree E0 FSB0 HR0 L0 RES0 EB0 R R' s mo mo1 TOK Hag KIA1) as TOK1.
  pose proof (ATOK_backing_room E0 FSB0 HR0 L0 RES0 EB0 HR0_ok R R' s mo1 L TOK1 ltac:(lia)) as B1.
  pose proof (ATOK_window E0 FSB0 HR0 L0 RES0 EB0 R R' s mo1 L TOK1 ltac:(lia)) as WIN.
  destruct TOK1 as ((LI1 & MI1 & HH1) & [O0 OS1] & EV1 & LIM1 & KVM1 & [P0 PS1]). pose proof KVM1 as (KR & KP & KW & KWF & KNA & TOP).
  pose proof alloc_ceiling_range as CR.
  assert (LB : L < 2^47) by (unfold NMAXA in HL; lia).
  pose proof (chk_anon_rw_red L mo1 LA ltac:(lia) LB) as RED.
  assert (PR : page_round_up_Z L = L) by (apply page_round_up_aligned; exact LA).
  split; [| split].
  - intros eff. rewrite RED. apply anon_match_nu.
  - pose proof (mmap_grant_null_rw L mo1 ltac:(lia)) as G. cbv zeta in G. rewrite PR in G.
    exact (G ltac:(rewrite TOP; lia) WIN B1).
  - intros eff mo' HC NR. pose proof HC as HC0. rewrite RED in HC. rewrite refusal_errno in NR.
    apply (anon_match_ok L mo1) in HC as (_ & r & -> & RA & R0 & RC & RF & NB & C4); [| exact NR].
    pose proof (check_mmap_only _ _ _ _ _ _ _ _ _ _ HC0) as MMA. split; [exact MMA|]. exists r. split; [reflexivity|].
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr.
    pose proof (grant_placed mo1 a r L KVM1 ltac:(lia) R0 RC RF) as PL.
    assert (Er : r = Z_to_bv 64 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EM : mo' = m_anon mo1 (bv_unsigned r) L).
    { rewrite C4. unfold anon_post, with_mmap_backing. rewrite (proj1 (proj2 cls_anon_rw)). unfold m_anon. rewrite <- Er. reflexivity. }
    split; [exact RA|]. split; [exact PL|].
    split; [intros rr Hrr; exact (grant_apart_reserved mo1 a r L rr KVM1 ltac:(lia) RC RF Hrr)|].
    split; [exact RF|]. split; [exact Er|]. split; [exact EM|]. clear C4. subst mo'. rewrite TOP in RC.
    assert (WF' : model_ivs_wf (m_anon mo1 (bv_unsigned r) L)) by (apply anon_wf; try assumption; lia).
    assert (MW : mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1))).
    { destruct KW as [D1 D2]. split.
      - intros i j e1 e2 Hi Hj NE. destruct i as [|i]; destruct j as [|j].
        + exfalso; exact (NE eq_refl).
        + cbn in Hi. injection Hi as <-. cbn in Hj. destruct e2 as [b2 s2].
          pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; eapply nth_error_In; exact Hj)) as OV.
          unfold iv_overlap in OV. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small in OV |- * by lia.
          pose proof (bv_unsigned_in_range 64 s2). apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
        + cbn in Hj. injection Hj as <-. cbn in Hi. destruct e1 as [b1 s1].
          pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; eapply nth_error_In; exact Hi)) as OV.
          unfold iv_overlap in OV. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small in OV |- * by lia.
          pose proof (bv_unsigned_in_range 64 s1). apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
        + cbn in Hi, Hj. exact (D1 i j e1 e2 Hi Hj ltac:(lia)).
      - constructor; [| exact D2]. unfold elo, ehi. cbn [fst snd]. rewrite !u64_small by lia. lia. }
    split.
    + split; [| split; [eapply mm_answer_minvA; [exact MMA| exact MI1]| rewrite (mm_answer_halted _ _ _ _ MMA); exact HH1]].
      destruct LI1 as [Q1 Q2 Q3 Q4 Q5]. constructor; rewrite ?anon_mat, ?anon_limit; try assumption.
      * pose proof (anon_eager mo1 (bv_unsigned r) L KWF ltac:(lia) ltac:(lia) ltac:(lia)). lia.
      * rewrite LIM1, page_size_val. unfold OSL in OS1. rewrite LIM1 in OS1. pose proof (AHK_aN_bound E0 FSB0 HR0 HR0_ok s) as NBd.
        change (A_bundle.aN E0 FSB0 HR0 s) with (aNc s) in NBd. change (A_bundle.aNz E0 FSB0 HR0 s) with (aNzc s) in OS1. clear -OS1 NBd LR HL. nia.
    + split; [rewrite anon_limit; exact LIM1|]. split; [rewrite anon_maps; rewrite <- Er; reflexivity|].
      split; [apply anon_noaccess|]. split; [apply anon_lazy|]. split; [rewrite anon_reserved; exact KR|]. split; [exact WF'|].
      split; [unfold m_anon; mproj; cbn; exact TOP|]. split; [| split; [exact MW| split]].
      * rewrite anon_noaccess, anon_maps. rewrite <- Er. intros e He. destruct (KNA e He) as (Q1 & m1 & Hm1 & Q2 & Q3).
        split; [exact Q1|]. exists m1. split; [right; exact Hm1| exact (conj Q2 Q3)].
      * unfold OSL in *. rewrite anon_limit. exact OS1.
      * pose proof (PSL_grant R' (m_vmmaps mo1) (m_vmmaps (m_anon mo1 (bv_unsigned r) L)) r (Z_to_bv 64 L)
                      (anon_reserved _ _ _) ltac:(rewrite anon_maps, <- Er; reflexivity) ltac:(unfold m_anon; mproj; cbn; reflexivity) PS1) as X.
        rewrite u64_small in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Definition cost2 (L : Z) : Z := L / 4096 + (if kBigMapSize <=? L then L / 32768 else 0) + (if L <? kBigMapSize then 20 else 2).

Section Sec2.
Variables (s : aps) (a2 : astate) (mo1 mo' : Model) (r : word) (L : Z) (sc : secchunk) (R R' : Z).
Let a := aps_alloc s.
Let rZ := bv_unsigned r.
Hypothesis SC1 : sc_map_beg sc = rZ.
Hypothesis SC2 : sc_map_size sc = L.
Hypothesis Esec : as_sec a2 = as_sec a ++ [sc].
Hypothesis Eres : as_residue a2 = as_residue a ++ residue_pages rZ L.
Hypothesis Ereg : forall c, get_region a2 c = get_region a c.
Hypothesis Eptr : as_ptr_committed a2 = as_ptr_committed a.
Hypothesis Enb : as_node_blocks a2 = as_node_blocks a.
Hypothesis Esb : as_store_blocks a2 = as_store_blocks a.
Hypothesis HL : 0 < L.
Hypothesis LA : L mod 4096 = 0.
Hypothesis RA : rZ mod 4096 = 0.
Hypothesis RP : placed rZ L.
(* [comment removed for export] *)
Hypothesis KI : KIA (aSc s) (aNc s) (aEBc s + L) mo'.
Hypothesis LIM : vm_limit (m_vmmaps mo') = 2^39.
Hypothesis MAPS : vm_maps (m_vmmaps mo') = (r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1).
Hypothesis NOACC : vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo1).
Hypothesis LAZY : m_vm_lazy mo' = m_vm_lazy mo1.
Hypothesis RES : vm_reserved (m_vmmaps mo') = RES0.
Hypothesis WF' : model_ivs_wf mo'.
Hypothesis TOP' : alloc_top (m_vmmaps mo') = alloc_ceiling.
Hypothesis NA' : nao (vm_noaccess (m_vmmaps mo')) (vm_maps (m_vmmaps mo')).
Hypothesis MW' : mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1)).
Hypothesis RF : region_free (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) r (Z_to_bv 64 L) = true.
(* [comment removed for export] *)
Hypothesis KV1 : KVM L0 RES0 mo1 a.
Hypothesis OS1 : 0 <= R /\ OSL aEBc aNzc R s mo'.
Hypothesis PS1 : 0 <= R' /\ PSL R' (m_vmmaps mo').
Hypothesis EV1 : ENVOK E0 FSB0 s.
Hypothesis CR : cost2 L <= R.

Lemma regions_bytes_a2 : regions_bytes a2 = regions_bytes a.
Proof. cstat. unfold regions_bytes. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite Ereg, IH. reflexivity. Qed.

Lemma aEB_a2 : aEBc (sA a2 s) = aEBc s + L.
Proof.
  cstat. unfold A_bundle.aEB, A_policy5.aEB, aEBa, a_eager_bytes, sA, aps_set_alloc. cbn [aps_alloc]. rewrite regions_bytes_a2, Eptr, Enb.
  unfold AsanState.sec_bytes. fold a. rewrite Esec, fold_right_app. cbn [fold_right]. rewrite SC2.
  assert (G : forall l z, fold_right (fun c acc => sc_map_size c + acc) z l = fold_right (fun c acc => sc_map_size c + acc) 0 l + z).
  { induction l as [|x l IH]; intros z; cbn; [lia| rewrite IH; lia]. }
  rewrite G. lia.
Qed.

Lemma aS_a2_grow : forall w, aSc s w -> aSc (sA a2 s) w.
Proof.
  cstat. intros w [M H]. unfold A_bundle.aS, A_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *. cbn [aps_alloc] in *.
  split; [exact M|]. fold a. fold a in H. rewrite Esec, Eres, Esb.
  destruct H as [H|[H|[H|H]]]; [left; exact H| | | right; right; right; exact H].
  - right; left. destruct H as (sc' & Hin & X). exists sc'. split; [apply in_app_iff; left; exact Hin| exact X].
  - right; right; left. apply in_app_iff. left. exact H.
Qed.

Lemma aNz_a2 : aNzc (sA a2 s) <= aNzc s + (cost2 L - L / 4096).
Proof.
  cstat. unfold A_bundle.aNz, A_policy5.aNz, aNza, interiors_bound, sA, aps_set_alloc, cost2. cbn [aps_alloc]. fold a. rewrite Esec, Eres, Esb.
  rewrite fold_right_app. cbn [fold_right]. rewrite SC2.
  assert (G : forall l z, fold_right (fun c acc => (if kBigMapSize <=? sc_map_size c then sc_map_size c / 32768 else 0) + acc) z l
                       = fold_right (fun c acc => (if kBigMapSize <=? sc_map_size c then sc_map_size c / 32768 else 0) + acc) 0 l + z).
  { induction l as [|x l IH]; intros z; cbn -[Z.add Z.div Z.leb]; [lia| rewrite IH; lia]. }
  rewrite G. unfold zlen. rewrite length_app, Nat2Z.inj_add.
  pose proof (residue_pages_len rZ L HL) as RL. unfold zlen in RL. lia.
Qed.

Lemma ATOK_sec_append : ATOKc (R - cost2 L) R' (sA a2 s) mo'.
Proof.
  pose proof KV1 as (KR & (fog & PM & FG1 & FG2) & KW & KWF & KNA & KT). destruct OS1 as [O0 O1].
  assert (CL : L / 4096 <= cost2 L).
  { unfold cost2. pose proof (Z.div_pos L 32768 ltac:(lia) ltac:(lia)). destruct (kBigMapSize <=? L); destruct (L <? kBigMapSize); lia. }
  pose proof aNz_a2 as NZ. pose proof aEB_a2 as EB2. pose proof (AHK_aN_bound E0 FSB0 HR0 HR0_ok (sA a2 s)) as NB.
  change (A_bundle.aN E0 FSB0 HR0 (sA a2 s)) with (aNc (sA a2 s)) in NB. change (A_bundle.aNz E0 FSB0 HR0 (sA a2 s)) with (aNzc (sA a2 s)) in NB.
  split; [| split; [| split; [| split; [| split]]]].
  - destruct KI as (L1 & M1 & H1). split; [| split; [exact M1| exact H1]].
    eapply LI_grow; [exact L1| exact aS_a2_grow| intros l ND HF; exact (aS_card (A0 E0 FSB0 HR0) (aps_alloc (sA a2 s)) l ND HF)| rewrite EB2; lia|].
    rewrite LIM, EB2, page_size_val. unfold OSL in O1. rewrite LIM in O1. clear -O1 NZ NB CR CL HL LA. Z.div_mod_to_equations. nia.
  - unfold OSL in *. rewrite EB2. split; [lia|]. clear -O1 NZ CR CL HL LA. Z.div_mod_to_equations. nia.
  - unfold ENVOK, sA, aps_set_alloc in *. cbn [aps_env aps_fsbase] in *. exact EV1.
  - exact LIM.
  - unfold KVM. split; [exact RES|]. split; [| split; [rewrite MAPS; exact MW'| split; [exact WF'| split; [exact NA'| exact TOP']]]].
    exists fog. split; [| split; [exact FG1| exact FG2]]. rewrite MAPS.
    unfold sA, aps_set_alloc, amaps. cbn [aps_alloc]. fold a. rewrite Esec, Enb, Esb, map_app. cbn [map].
    assert (EW : went (sc_map_beg sc) (sc_map_size sc) = (r, Z_to_bv 64 L)).
    { unfold went, kwz. rewrite SC1, SC2. unfold rZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    rewrite EW. eapply Permutation_trans; [apply Permutation_cons; [reflexivity| exact PM]|].
    unfold amaps.
    set (MS := map (fun sc0 => went (sc_map_beg sc0) (sc_map_size sc0)) (as_sec a)).
    set (NBk := map (fun b => went b kDepotNodeBlockBytes) (as_node_blocks a)).
    set (SBk := map (fun b => went b kStoreBlockBytes) (as_store_blocks a)).
    replace (L0 ++ fog ++ MS ++ NBk ++ SBk) with ((L0 ++ fog ++ MS) ++ (NBk ++ SBk)) by (rewrite <- !app_assoc; reflexivity).
    replace (L0 ++ fog ++ (MS ++ [(r, Z_to_bv 64 L)]) ++ NBk ++ SBk) with ((L0 ++ fog ++ MS) ++ (r, Z_to_bv 64 L) :: (NBk ++ SBk)) by (rewrite <- !app_assoc; reflexivity).
    apply Permutation_middle.
  - exact PS1.
Qed.

(* [comment removed for export] *)
Lemma fresh_eager_rw : forall P D,
  AKern E0 a mo1 -> AWf E0 P D a -> eager_rw mo' rZ L.
Proof.
  cstat. intros P D K1 WF. pose proof KV1 as (KR & KP & KW & KWF & KNA & KT).
  pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. pose proof alloc_ceiling_range as ACR.
  pose proof RP as (RP1 & RP2 & RP3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, rZ in RP1, RP2, RP3.
  assert (DJ : forall m, In m (vm_maps (m_vmmaps mo1)) -> ehi m <= rZ \/ rZ + L <= elo m).
  { intros [b sz] Hm. pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; exact Hm)) as OV.
    unfold iv_overlap in OV. unfold elo, ehi, rZ in *. cbn [fst snd]. pose proof (bv_unsigned_in_range 64 sz).
    rewrite !u64_small in OV by lia. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
  split; [| split].
  - exists (r, Z_to_bv 64 L). rewrite MAPS. split; [left; reflexivity|]. unfold elo, ehi, rZ. cbn [fst snd]. rewrite u64_small by lia. lia.
  - rewrite NOACC. intros e He Hpos. destruct (KNA e He) as (_ & m & Hm & Q1 & Q2). pose proof (DJ m Hm). lia.
  - rewrite LAZY. intros e He. destruct K1.
    assert (INM : forall x n, inside (vm_maps (m_vmmaps mo1)) x n -> x <= elo e -> ehi e <= x + n -> rZ + L <= elo e \/ ehi e <= rZ).
    { intros x n (m & Hm & X1 & X2) Y1 Y2. pose proof (DJ m Hm). lia. }
    destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]].
    + rewrite kHighMemBeg_val in *. unfold rZ. clear -X RP3. lia.
    + eapply INM; [exact (proj1 ak_store)| lia| lia].
    + destruct X as (b & Hb & X1 & X2). eapply INM; [exact (proj1 (ak_store_blocks b Hb))| lia| lia].
    + eapply (INM (ae_ptr_array E0) kPtrArrayLen); [exists (went (ae_ptr_array E0) kPtrArrayLen); split; [exact ak_ptr|]| |].
      * unfold went, kwz, elo, ehi, kPtrArrayLen. cbn [fst snd]. pose proof WF as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E16 & E17 & _) & _).
        unfold app_mem in E16. rewrite kLowAppEnd_val, kHighMemBeg_val in E16. rewrite !u64_small by lia. lia.
      * destruct (as_ptr_committed a =? 0); unfold kPtrArrayCommit in *; lia.
      * lia.
    + destruct X as (X0 & X1 & _). eapply (INM (ae_resv_beg E0) kResvLen); [exists (went (ae_resv_beg E0) kResvLen); split; [exact ak_resv|]| lia| lia].
      unfold went, kwz, elo, ehi, kResvLen. cbn [fst snd]. pose proof WF as ((_ & E2 & _ & _ & E5 & _) & _).
      rewrite kHighMemBeg_val in E2. rewrite !u64_small by lia. lia.
Qed.

Lemma AKern_sec_append : forall P D,
  AKern E0 a mo1 -> AWf E0 P D a -> AKern E0 a2 mo'.
Proof.
  cstat. pose proof LA as LA0. clear LA0. intros P D K1 WF. pose proof (fresh_eager_rw P D K1 WF) as FR. pose proof KV1 as (KR & KP & KW & KWF & KNA & KT).
  pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. pose proof alloc_ceiling_range as ACR.
  pose proof RP as (RP1 & RP2 & RP3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, rZ in RP1, RP2, RP3.
  assert (DJ : forall m, In m (vm_maps (m_vmmaps mo1)) -> ehi m <= rZ \/ rZ + L <= elo m).
  { intros [b sz] Hm. pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; exact Hm)) as OV.
    unfold iv_overlap in OV. unfold elo, ehi, rZ in *. cbn [fst snd]. pose proof (bv_unsigned_in_range 64 sz).
    rewrite !u64_small in OV by lia. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
  assert (ERW : forall x n, eager_rw mo1 x n -> eager_rw mo' x n).
  { intros x n (I1 & I2 & I3). split; [| split]; [| rewrite NOACC; exact I2| rewrite LAZY; exact I3].
    destruct I1 as (m & Hm & X). exists m. rewrite MAPS. split; [right; exact Hm| exact X]. }
  assert (INS : forall x n, inside (vm_maps (m_vmmaps mo1)) x n -> inside (vm_maps (m_vmmaps mo')) x n).
  { intros x n (m & Hm & X). exists m. rewrite MAPS. split; [right; exact Hm| exact X]. }
  destruct K1. constructor.
  - rewrite MAPS. right. exact ak_resv.
  - exact ak_resv_geom.
  - destruct ak_reginfo as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - intros c Hc Hm. rewrite Ereg in *. apply ERW. exact (ak_user c Hc Hm).
  - intros c Hc Hm. rewrite Ereg in *. apply ERW. exact (ak_fa c Hc Hm).
  - rewrite MAPS. right. exact ak_ptr.
  - rewrite Eptr. intros Hp. apply ERW. exact (ak_ptr_head Hp).
  - rewrite Eptr, NOACC. exact ak_ptr_tail.
  - intros sc' Hsc'. rewrite Esec in Hsc'. apply in_app_iff in Hsc'. destruct Hsc' as [Hsc'|[<-|[]]].
    + destruct (ak_sec sc' Hsc') as [S1 S2]. split; [rewrite MAPS; right; exact S1| apply ERW; exact S2].
    + rewrite SC1, SC2. split; [| exact FR]. rewrite MAPS. left. unfold went, kwz, rZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - apply ERW. exact ak_thread.
  - apply ERW. exact ak_depot_nodes.
  - destruct ak_store as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - rewrite Enb. intros b Hb. destruct (ak_node_blocks b Hb) as [N1 N2]. split; [rewrite MAPS; right; exact N1| apply ERW; exact N2].
  - rewrite Esb. intros b Hb. destruct (ak_store_blocks b Hb) as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - rewrite Enb, Esb. intros b len Hb. destruct (ak_blocks_sep b len Hb) as (B1 & B2 & B3 & B4 & B5 & B6). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [| exact B6].
    intros sc' Hsc'. rewrite Esec in Hsc'. apply in_app_iff in Hsc'. destruct Hsc' as [Hsc'|[<-|[]]]; [exact (B5 sc' Hsc')|]. rewrite SC1, SC2.
    (* [comment removed for export] *)
    assert (IN : exists m, In m (vm_maps (m_vmmaps mo1)) /\ elo m <= b /\ b + len <= ehi m).
    { destruct Hb as [[Hb ->]|[Hb ->]]; [exists (went b kDepotNodeBlockBytes); split; [exact (proj1 (ak_node_blocks b Hb))|]| exact (proj1 (ak_store_blocks b Hb))].
      unfold went, kwz, elo, ehi. cbn [fst snd]. pose proof (ak_blocks_sep b _ (or_introl (conj Hb eq_refl))) as (Y1 & Y2 & _).
      unfold app_mem in Y1. rewrite kLowAppEnd_val, kHighMemBeg_val in Y1. unfold kDepotNodeBlockBytes in *. pose proof alloc_ceiling_range as CRR. rewrite !u64_small by (clear -Y1 Y2 CRR; lia). clear -Y1 Y2. lia. }
    destruct IN as (m & Hm & X1 & X2). pose proof (DJ m Hm) as D0. clear -X1 X2 D0. lia.   (* [comment removed for export] *)
  - rewrite LAZY, Esb, Eptr. intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left; exact X| right; left; exact X| right; right; left; exact X| right; right; right; left; exact X|].
    right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [exact X0|]. split; [exact X1|]. split; intros c Hc Hm; rewrite Ereg in *; [exact (X2 c Hc Hm)| exact (X3 c Hc Hm)].
  - destruct ak_store_sep as (T1 & T2 & T3 & T4 & T5). split; [exact T1|]. split; [| split; [exact T3| split; [exact T4| exact T5]]].
    intros sc' Hsc'. rewrite Esec in Hsc'. apply in_app_iff in Hsc'. destruct Hsc' as [Hsc'|[<-|[]]]; [exact (T2 sc' Hsc')|]. rewrite SC1, SC2.
    destruct (proj1 ak_store) as (m & Hm & X1 & X2). pose proof (DJ m Hm). lia.
Qed.
End Sec2.

(* [comment removed for export] *)
Section Node4.
Variables (s : aps) (a2 : astate) (mo1 mo' : Model) (r : word) (R R' : Z).
Let a := aps_alloc s.
Let rZ := bv_unsigned r.
Let L := kDepotNodeBlockBytes.
Hypothesis Enb : as_node_blocks a2 = as_node_blocks a ++ [rZ].
Hypothesis Esec : as_sec a2 = as_sec a.
Hypothesis Eres : as_residue a2 = as_residue a.
Hypothesis Ereg : forall c, get_region a2 c = get_region a c.
Hypothesis Eptr : as_ptr_committed a2 = as_ptr_committed a.
Hypothesis Esb : as_store_blocks a2 = as_store_blocks a.
Hypothesis RA : rZ mod 4096 = 0.
Hypothesis RP : placed rZ L.
Hypothesis RSV : forall rr, In rr (ae_reserved E0) -> rZ + L <= fst rr \/ fst rr + snd rr <= rZ.
Hypothesis KI : KIA (aSc s) (aNc s) (aEBc s + L) mo'.
Hypothesis LIM : vm_limit (m_vmmaps mo') = 2^39.
Hypothesis MAPS : vm_maps (m_vmmaps mo') = (r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1).
Hypothesis NOACC : vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo1).
Hypothesis LAZY : m_vm_lazy mo' = m_vm_lazy mo1.
Hypothesis RES : vm_reserved (m_vmmaps mo') = RES0.
Hypothesis WF' : model_ivs_wf mo'.
Hypothesis TOP' : alloc_top (m_vmmaps mo') = alloc_ceiling.
Hypothesis NA' : nao (vm_noaccess (m_vmmaps mo')) (vm_maps (m_vmmaps mo')).
Hypothesis MW' : mwf ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo1)).
Hypothesis RF : region_free (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) r (Z_to_bv 64 L) = true.
Hypothesis KV1 : KVM L0 RES0 mo1 a.
Hypothesis OS1 : 0 <= R /\ OSL aEBc aNzc R s mo'.
Hypothesis PS1 : 0 <= R' /\ PSL R' (m_vmmaps mo').
Hypothesis EV1 : ENVOK E0 FSB0 s.
Hypothesis CR : 256 <= R.

Lemma regions_bytes_n2 : regions_bytes a2 = regions_bytes a.
Proof. cstat. unfold regions_bytes. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite Ereg, IH. reflexivity. Qed.

Lemma ATOK_node_append : ATOKc (R - 256) R' (sA a2 s) mo'.
Proof.
  cstat. pose proof KV1 as (KR & (fog & PM & FG1 & FG2) & KW & KWF & KNA & KT). destruct OS1 as [O0 O1].
  assert (ES : forall w, aSc s w <-> aSc (sA a2 s) w).
  { intros w. unfold A_bundle.aS, A_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores. cbn [aps_alloc]. fold a. rewrite Esec, Eres, Esb. split; intros X; exact X. }
  assert (EN : aNc (sA a2 s) = aNc s).
  { unfold A_bundle.aN, A_policy5.aN, aNa, cover, cover_int, cover_res, cover_st, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite Esec, Eres, Esb. reflexivity. }
  assert (EE : aEBc (sA a2 s) = aEBc s + L).
  { unfold A_bundle.aEB, A_policy5.aEB, aEBa, a_eager_bytes, AsanState.sec_bytes, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite regions_bytes_n2, Esec, Eptr, Enb.
    unfold zlen, L. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn. unfold kDepotNodeBlockBytes. lia. }
  assert (EZ : aNzc (sA a2 s) = aNzc s).
  { unfold A_bundle.aNz, A_policy5.aNz, aNza, interiors_bound, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite Esec, Eres, Esb. reflexivity. }
  split; [| split; [| split; [| split; [| split]]]].
  - destruct KI as (L1 & M1 & H1). split; [| split; [exact M1| exact H1]]. rewrite EN, EE. eapply LI_ext; [exact ES| exact L1].
  - unfold OSL in *. rewrite EE, EZ. unfold L, kDepotNodeBlockBytes. split; [clear -O0 CR; lia| clear -O1 CR; lia].
  - unfold ENVOK, sA, aps_set_alloc in *. cbn [aps_env aps_fsbase] in *. exact EV1.
  - exact LIM.
  - unfold KVM. split; [exact RES|]. split; [| split; [rewrite MAPS; exact MW'| split; [exact WF'| split; [exact NA'| exact TOP']]]].
    exists fog. split; [| split; [exact FG1| exact FG2]]. rewrite MAPS.
    unfold sA, aps_set_alloc, amaps. cbn [aps_alloc]. fold a. rewrite Esec, Enb, Esb, map_app. cbn [map].
    assert (EW : went rZ kDepotNodeBlockBytes = (r, Z_to_bv 64 L)) by (unfold went, kwz, rZ, L; rewrite Z_to_bv_bv_unsigned; reflexivity).
    rewrite EW. eapply Permutation_trans; [apply Permutation_cons; [reflexivity| exact PM]|].
    unfold amaps.
    set (MS := map (fun sc0 => went (sc_map_beg sc0) (sc_map_size sc0)) (as_sec a)).
    set (NBk := map (fun b => went b kDepotNodeBlockBytes) (as_node_blocks a)).
    set (SBk := map (fun b => went b kStoreBlockBytes) (as_store_blocks a)).
    replace (L0 ++ fog ++ MS ++ NBk ++ SBk) with ((L0 ++ fog ++ MS ++ NBk) ++ SBk) by (rewrite <- !app_assoc; reflexivity).
    replace (L0 ++ fog ++ MS ++ (NBk ++ [(r, Z_to_bv 64 L)]) ++ SBk) with ((L0 ++ fog ++ MS ++ NBk) ++ (r, Z_to_bv 64 L) :: SBk) by (rewrite <- !app_assoc; reflexivity).
    apply Permutation_middle.
  - exact PS1.
Qed.

Lemma AKern_node_append : forall P D,
  AKern E0 a mo1 -> AWf E0 P D a -> AKern E0 a2 mo'.
Proof.
  cstat. intros P D K1 WF. pose proof KV1 as (KR & KP & KW & KWF & KNA & KT).
  pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. pose proof alloc_ceiling_range as ACR.
  pose proof RP as (RP1 & RP2 & RP3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, rZ, L, kDepotNodeBlockBytes in RP1, RP2, RP3.
  assert (DJ : forall m, In m (vm_maps (m_vmmaps mo1)) -> ehi m <= rZ \/ rZ + L <= elo m).
  { intros [b sz] Hm. pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; exact Hm)) as OV.
    unfold iv_overlap in OV. unfold elo, ehi, rZ, L, kDepotNodeBlockBytes in *. cbn [fst snd]. pose proof (bv_unsigned_in_range 64 sz).
    rewrite !u64_small in OV by lia. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
  assert (FR : eager_rw mo' rZ L).
  { split; [| split].
    - exists (r, Z_to_bv 64 L). rewrite MAPS. split; [left; reflexivity|]. unfold elo, ehi, rZ, L, kDepotNodeBlockBytes. cbn [fst snd]. rewrite u64_small by lia. lia.
    - rewrite NOACC. intros e He Hpos. destruct (KNA e He) as (_ & m & Hm & Q1 & Q2). pose proof (DJ m Hm). lia.
    - rewrite LAZY. intros e He. destruct K1.
      assert (INM : forall x n, inside (vm_maps (m_vmmaps mo1)) x n -> x <= elo e -> ehi e <= x + n -> rZ + L <= elo e \/ ehi e <= rZ).
      { intros x n (m & Hm & X1 & X2) Y1 Y2. pose proof (DJ m Hm). lia. }
      destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]].
      + rewrite kHighMemBeg_val in *. unfold rZ, L, kDepotNodeBlockBytes. clear -X RP3. lia.
      + eapply INM; [exact (proj1 ak_store)| lia| lia].
      + destruct X as (b & Hb & X1 & X2). eapply INM; [exact (proj1 (ak_store_blocks b Hb))| lia| lia].
      + eapply (INM (ae_ptr_array E0) kPtrArrayLen); [exists (went (ae_ptr_array E0) kPtrArrayLen); split; [exact ak_ptr|]| |].
        * unfold went, kwz, elo, ehi, kPtrArrayLen. cbn [fst snd]. pose proof WF as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E16 & E17 & _) & _).
          unfold app_mem in E16. rewrite kLowAppEnd_val, kHighMemBeg_val in E16. rewrite !u64_small by lia. lia.
        * destruct (as_ptr_committed a =? 0); unfold kPtrArrayCommit in *; lia.
        * lia.
      + destruct X as (X0 & X1 & _). eapply (INM (ae_resv_beg E0) kResvLen); [exists (went (ae_resv_beg E0) kResvLen); split; [exact ak_resv|]| lia| lia].
        unfold went, kwz, elo, ehi, kResvLen. cbn [fst snd]. pose proof WF as ((_ & E2 & _ & _ & E5 & _) & _).
        rewrite kHighMemBeg_val in E2. rewrite !u64_small by lia. lia. }
  assert (ERW : forall x n, eager_rw mo1 x n -> eager_rw mo' x n).
  { intros x n (I1 & I2 & I3). split; [| split]; [| rewrite NOACC; exact I2| rewrite LAZY; exact I3].
    destruct I1 as (m & Hm & X). exists m. rewrite MAPS. split; [right; exact Hm| exact X]. }
  assert (INS : forall x n, inside (vm_maps (m_vmmaps mo1)) x n -> inside (vm_maps (m_vmmaps mo')) x n).
  { intros x n (m & Hm & X). exists m. rewrite MAPS. split; [right; exact Hm| exact X]. }
  destruct K1. constructor.
  - rewrite MAPS. right. exact ak_resv.
  - exact ak_resv_geom.
  - destruct ak_reginfo as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - intros c Hc Hm. rewrite Ereg in *. apply ERW. exact (ak_user c Hc Hm).
  - intros c Hc Hm. rewrite Ereg in *. apply ERW. exact (ak_fa c Hc Hm).
  - rewrite MAPS. right. exact ak_ptr.
  - rewrite Eptr. intros Hp. apply ERW. exact (ak_ptr_head Hp).
  - rewrite Eptr, NOACC. exact ak_ptr_tail.
  - rewrite Esec. intros sc' Hsc'. destruct (ak_sec sc' Hsc') as [S1 S2]. split; [rewrite MAPS; right; exact S1| apply ERW; exact S2].
  - apply ERW. exact ak_thread.
  - apply ERW. exact ak_depot_nodes.
  - destruct ak_store as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - rewrite Enb. intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]].
    + destruct (ak_node_blocks b Hb) as [N1 N2]. split; [rewrite MAPS; right; exact N1| apply ERW; exact N2].
    + split; [| exact FR]. rewrite MAPS. left. unfold went, kwz, rZ, L. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite Esb. intros b Hb. destruct (ak_store_blocks b Hb) as [I1 I2]. split; [apply INS; exact I1| rewrite NOACC; exact I2].
  - rewrite Enb, Esb, Esec. intros b len Hb.
    assert (OLD : (In b (as_node_blocks a) /\ len = kDepotNodeBlockBytes) \/ (In b (as_store_blocks a) /\ len = kStoreBlockBytes) \/ (b = rZ /\ len = L)).
    { destruct Hb as [[Hb E]|[Hb E]]; [apply in_app_iff in Hb; destruct Hb as [Hb|[<-|[]]]; [left; auto| right; right; auto]| right; left; auto]. }
    destruct OLD as [Hb'|[Hb'|[-> ->]]]; [exact (ak_blocks_sep b len (or_introl Hb'))| exact (ak_blocks_sep b len (or_intror Hb'))|].
    split; [exact (placed_app_mem _ _ RP)|]. split; [exact (proj1 (proj2 RP))|]. split; [unfold kPageSize; exact RA|].
    split. { pose proof (DJ _ ak_resv) as DR. unfold went, kwz, elo, ehi, kResvLen in DR. cbn [fst snd] in DR.
             pose proof WF as ((_ & E2 & _ & _ & E5 & _) & _). rewrite kHighMemBeg_val in E2.
             rewrite !u64_small in DR by lia. unfold kResvLen. clear -DR. lia. }
    split. { intros sc' Hsc'. destruct (ak_sec sc' Hsc') as [S1 _]. pose proof (DJ _ S1) as DS. unfold went, kwz, elo, ehi in DS. cbn [fst snd] in DS.
             pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & SC3 & _) & _). destruct (SC3 sc' Hsc') as (_ & Q2 & Q3 & Q4 & _).
             unfold app_mem in Q2. rewrite kLowAppEnd_val, kHighMemBeg_val in Q2. pose proof alloc_ceiling_range as CRR. rewrite !u64_small in DS by (clear -Q2 Q3 Q4 CRR; lia). clear -DS. lia. }
    exact RSV.
  - rewrite LAZY, Esb, Eptr. intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left; exact X| right; left; exact X| right; right; left; exact X| right; right; right; left; exact X|].
    right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [exact X0|]. split; [exact X1|]. split; intros c Hc Hm; rewrite Ereg in *; [exact (X2 c Hc Hm)| exact (X3 c Hc Hm)].
  - rewrite Esec. exact ak_store_sep.
Qed.
End Node4.
End Ev.
End RC__1.

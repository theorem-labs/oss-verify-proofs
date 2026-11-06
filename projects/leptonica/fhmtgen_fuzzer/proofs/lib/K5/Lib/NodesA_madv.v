(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape AsanCeil BackingAlgebra.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes RelSpec RzCPS NodesA NodesA_mm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mdl_madvise (mo : Model) (addr n : word) : Model := madvise_dontneed_next mo addr n.

Section Proj.
Variables (mo : Model) (a n : word).

Lemma mdl_madvise_same : same_but_materialized mo (mdl_madvise mo a n).
Proof. unfold mdl_madvise, madvise_dontneed_next. apply with_vm_backing_same. Qed.

Lemma mdl_madvise_vmmaps : m_vmmaps (mdl_madvise mo a n) = m_vmmaps mo.
Proof. exact (proj1 (proj2 (same_but_materialized_frame _ _ mdl_madvise_same))). Qed.
Lemma mdl_madvise_lazy : m_vm_lazy (mdl_madvise mo a n) = m_vm_lazy mo.
Proof. exact (proj1 (proj2 (proj2 (same_but_materialized_frame _ _ mdl_madvise_same)))). Qed.
Lemma mdl_madvise_mat : m_vm_materialized (mdl_madvise mo a n)
  = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo).
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma mdl_madvise_fds : m_fds (mdl_madvise mo a n) = m_fds mo.
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma mdl_madvise_fs : m_fs (mdl_madvise mo a n) = m_fs mo.
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma mdl_madvise_halted : m_halted (mdl_madvise mo a n) = m_halted mo.
Proof. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma mdl_madvise_eager : eager_used (mdl_madvise mo a n) = eager_used mo.
Proof. unfold eager_used. rewrite mdl_madvise_vmmaps, mdl_madvise_lazy. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mdl_madvise_mat_incl : incl (m_vm_materialized (mdl_madvise mo a n)) (m_vm_materialized mo).
Proof. rewrite mdl_madvise_mat. intros p Hp. apply filter_In in Hp. exact (proj1 Hp). Qed.

Lemma mdl_madvise_backing_le : vm_backing_used (mdl_madvise mo a n) <= vm_backing_used mo.
Proof.
  rewrite !vm_backing_used_split, mdl_madvise_eager, mdl_madvise_mat.
  pose proof (filter_length_le (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo)).
  unfold page_size. lia.
Qed.
End Proj.

(* [comment removed for export] *)
Lemma mat_stable_madvise : forall (KM : Model -> Prop) mo a n, mat_stable KM -> KM mo -> KM (mdl_madvise mo a n).
Proof. intros KM mo a n HKM H. exact (HKM mo _ (mdl_madvise_same mo a n) H). Qed.

(* [comment removed for export] *)
Lemma model_ivs_wf_madvise : forall mo a n, model_ivs_wf mo -> model_ivs_wf (mdl_madvise mo a n).
Proof. intros mo a n H. unfold model_ivs_wf in *. rewrite mdl_madvise_vmmaps, mdl_madvise_lazy. exact H. Qed.

Lemma lazy_in_maps_madvise : forall mo a n, lazy_in_maps mo -> lazy_in_maps (mdl_madvise mo a n).
Proof. intros mo a n H. unfold lazy_in_maps in *. rewrite mdl_madvise_vmmaps, mdl_madvise_lazy. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_233 : forall i m o,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_char : forall segs ms mo addr len o,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len < 2^64 ->
  areg ms 10 = Z_to_bv 64 addr -> areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 4 ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  syscall_spec (sys_input segs ms (Z_to_bv 64 233)) mo o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
         (mdl_madvise mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) [].
Proof.
  intros segs ms mo addr len o Hlen Hpos Hal Hend H10 H11 H12 Hok.
  pose proof (page_round_up_Z_ge_all len) as HnZ.
  rewrite syscall_spec_233 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, H10, H11, H12.
  unfold madvise_spec.
  assert (E0 : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (E2 : madvise_dontneed_b (int32 (Z_to_bv 64 4)) = true) by (vm_compute; reflexivity).
  assert (E3 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  rewrite E0, E1, E2, E3, (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
  rewrite bind_get_model. cbv zeta. rewrite Hok.
  unfold mdl_madvise. sys_unfold. split.
  - intros H. destruct o as [y m2 evs|]; inv_sys; reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RuleMadvise.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

(* [comment removed for export] *)
Lemma madv_req_facts : forall addr len, 0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= 2^47 ->
  bv_unsigned (Z_to_bv 64 addr) = addr /\ bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len
  /\ 0 < page_round_up_Z len /\ page_round_up_Z len mod 4096 = 0 /\ addr mod 4096 = 0 /\ (addr + page_round_up_Z len) mod 4096 = 0.
Proof.
  intros addr len Hlen Hpos Hal Htop.
  pose proof (page_round_up_Z_ge_all len). pose proof (page_round_up_Z_aligned' len) as Hnl. unfold page_size in Hnl, Hal.
  repeat split; try (apply unsigned_lit); try lia.
Qed.

(* [comment removed for export] *)
Theorem ast_madvise_dontneed : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len <= 2^47 ->
  (forall p : word, addr <= bv_unsigned p -> bv_unsigned p + 4096 <= addr + page_round_up_Z len -> page_allowedb A p = true) ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 233) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 4
       /\ K (nretA ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo ->
       madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ KM (mdl_madvise mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len Hlen Hpos Hal Htop Hvis Hm HM T [ms mo] Hc Hk.
  pose proof Hc as (Hmc & HPm & HPMmo & _). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  destruct (Hm _ HPm) as (Hsvc & H10 & H11 & H12 & HK). rewrite restrict_svc in Hsvc. rewrite restrict_areg in H10, H11, H12.
  destruct (HM _ HPMmo) as (Hok & HKM).
  destruct (madv_req_facts addr len Hlen Hpos Hal Htop) as (Ea & En & HnP & Hnl & Hlo & Hhi).
  set (nZ := page_round_up_Z len) in *. set (a := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 nZ) in *.
  assert (Hchar : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 233)) mo o <->
                    o = Ok (mkEffect (Z_to_bv 64 0) [] [(a, n)]) (mdl_madvise mo a n) []).
  { intros o. apply (madvise_dontneed_char segs ms mo addr len o Hlen Hpos Hal ltac:(fold nZ; lia) H10 H11 H12 Hok). }
  assert (HID_in : forall x, addr <= bv_unsigned x < addr + nZ -> HID A (mdl_madvise mo a n) x = false).
  { intros x Hx. unfold HID, mkH. destruct (page_of_byte_in_aligned' x addr (addr + nZ) Hlo Hhi Hx) as [P1 P2].
    rewrite (Hvis (page_base x) P1 P2). rewrite andb_false_r. cbn [orb]. apply Z.leb_gt. lia. }
  apply (ast_node_mm segs segtop A A Pm PM unit tt (fun _ => K) (fun _ => KM) ms mo (Z_to_bv 64 233)
           (fun _ => Z_to_bv 64 0) (fun _ => [(a, n)]) (fun _ => []) (fun _ => mdl_madvise mo a n) T Hc Hsvc).
  - vm_compute; reflexivity.
  - intros []. apply Hchar. reflexivity.
  - intros o Ho. exists tt. exact (proj1 (Hchar o) Ho).
  - intros []. split; [exact HAwf|]. split; [|split; [rewrite mdl_madvise_halted; exact Hh|]].
    + apply (MInv_cut A A mo _ addr (addr + nZ) HMInv (fun p H => H) Hlo Hhi); [rewrite mdl_madvise_mat, Ea, En; reflexivity| |].
      * intros p _ Hin. rewrite mdl_madvise_lazy. exact Hin.
      * rewrite mdl_madvise_eager, mdl_madvise_vmmaps. exact (minv_budget _ _ HMInv).
    + split; [rewrite mdl_madvise_lazy; exact Hr| exact Ht].
  - intros [] x Hx. rewrite zeros_cover_one, Ea, En in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    apply HID_in. lia.
  - intros [] x Hx. discriminate Hx.
  - intros [] x _ _. rewrite mdl_madvise_lazy. reflexivity.
  - intros [] x _. rewrite mdl_madvise_vmmaps. reflexivity.
  - intros []. exact HK.
  - intros []. exact HKM.
  - intros [] c' Hc'. exact (Hk c' Hc').
Qed.

(* [comment removed for export] *)
Corollary ast_madvise_dontneed_ms : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len <= 2^47 ->
  (forall p : word, addr <= bv_unsigned p -> bv_unsigned p + 4096 <= addr + page_round_up_Z len -> page_allowedb A p = true) ->
  mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 233) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 4
       /\ K (nretA ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo ->
       madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true /\ KM mo) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len Hlen Hpos Hal Htop Hvis HKMs Hm HM.
  apply (ast_madvise_dontneed A Pm PM K KM addr len Hlen Hpos Hal Htop Hvis Hm).
  intros mo HPM. destruct (HM mo HPM) as [Hok HKM]. split; [exact Hok|]. apply mat_stable_madvise; assumption.
Qed.

(* [comment removed for export] *)
Theorem ast_madvise_dontneed_grow : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len <= 2^47 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 233) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 4
       /\ K (nretA ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo ->
       madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ eager_used mo + page_round_up_Z len + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ KM (mdl_madvise mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  cps segs (AST segtop A Pm PM) (AST segtop ((addr, addr + page_round_up_Z len) :: A) K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len Hlen Hpos Hal Htop Hm HM T [ms mo] Hc Hk.
  pose proof Hc as (Hmc & HPm & HPMmo & _). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  destruct (Hm _ HPm) as (Hsvc & H10 & H11 & H12 & HK). rewrite restrict_svc in Hsvc. rewrite restrict_areg in H10, H11, H12.
  destruct (HM _ HPMmo) as (Hok & Hbud & HKM).
  destruct (madv_req_facts addr len Hlen Hpos Hal Htop) as (Ea & En & HnP & Hnl & Hlo & Hhi).
  set (nZ := page_round_up_Z len) in *. set (a := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 nZ) in *.
  assert (Hchar : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 233)) mo o <->
                    o = Ok (mkEffect (Z_to_bv 64 0) [] [(a, n)]) (mdl_madvise mo a n) []).
  { intros o. apply (madvise_dontneed_char segs ms mo addr len o Hlen Hpos Hal ltac:(fold nZ; lia) H10 H11 H12 Hok). }
  set (A' := (addr, addr + nZ) :: A).
  assert (HID_in : forall x, addr <= bv_unsigned x < addr + nZ -> HID A' (mdl_madvise mo a n) x = false).
  { intros x Hx. unfold HID, mkH. destruct (page_of_byte_in_aligned' x addr (addr + nZ) Hlo Hhi Hx) as [P1 P2].
    unfold A'. rewrite (page_allowedb_cons_in addr (addr + nZ) A (page_base x) P1 P2). rewrite andb_false_r. cbn [orb].
    apply Z.leb_gt. lia. }
  assert (HID_out : forall x, bv_unsigned x < addr \/ addr + nZ <= bv_unsigned x ->
                      mkH (m_vm_lazy (mdl_madvise mo a n)) A' x = mkH (m_vm_lazy mo) A x).
  { intros x Hx. pose proof (page_of_byte_out_aligned' x addr (addr + nZ) Hlo Hhi Hx) as Hpo.
    unfold mkH. rewrite mdl_madvise_lazy. unfold A'. rewrite (page_allowedb_cons_out addr (addr + nZ) A _ Hpo ltac:(lia)). reflexivity. }
  apply (ast_node_mm segs segtop A A' Pm PM unit tt (fun _ => K) (fun _ => KM) ms mo (Z_to_bv 64 233)
           (fun _ => Z_to_bv 64 0) (fun _ => [(a, n)]) (fun _ => []) (fun _ => mdl_madvise mo a n) T Hc Hsvc).
  - vm_compute; reflexivity.
  - intros []. apply Hchar. reflexivity.
  - intros o Ho. exists tt. exact (proj1 (Hchar o) Ho).
  - intros []. split; [|split; [|split; [rewrite mdl_madvise_halted; exact Hh|]]].
    + unfold A'. constructor; [cbn [fst snd]; unfold page_size; repeat split; first [exact Hlo| exact Hhi| lia]| exact HAwf].
    + apply (MInv_cut A A' mo _ addr (addr + nZ) HMInv); [| exact Hlo| exact Hhi| rewrite mdl_madvise_mat, Ea, En; reflexivity| |].
      * intros p Hp. unfold A', page_allowedb. cbn [existsb]. unfold page_allowedb in Hp. rewrite Hp. apply orb_true_r.
      * intros p _ Hin. rewrite mdl_madvise_lazy. exact Hin.
      * rewrite mdl_madvise_eager, mdl_madvise_vmmaps. unfold A'. cbn [A_bytes fst snd]. lia.
    + split; [rewrite mdl_madvise_lazy; exact Hr| exact Ht].
  - intros [] x Hx. rewrite zeros_cover_one, Ea, En in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    apply HID_in. lia.
  - intros [] x Hx. discriminate Hx.
  - intros [] x Hx _. rewrite zeros_cover_one, Ea, En in Hx. apply andb_false_iff in Hx. apply HID_out.
    destruct Hx as [Hx|Hx]; [apply Z.leb_gt in Hx| apply Z.ltb_ge in Hx]; lia.
  - intros [] x _. rewrite mdl_madvise_vmmaps. reflexivity.
  - intros []. exact HK.
  - intros []. exact HKM.
  - intros [] c' Hc'. exact (Hk c' Hc').
Qed.

End RuleMadvise.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma madvise_dontneed_ok_intro : forall h (a n : word) e,
  In e (vm_maps h) ->
  bv_unsigned (fst e) <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
  region_free (vm_reserved h) a n = true ->
  region_free (vm_noaccess h) a n = true ->
  madvise_dontneed_ok h a n = true.
Proof.
  intros h a n e Hin H1 H2 Hr Hn. unfold madvise_dontneed_ok. rewrite Hr, Hn, andb_true_r. cbn [andb].
  unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
  apply andb_true_intro. split; apply Z.leb_le; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition noaccess_pos (mo : Model) : Prop :=
  Forall (fun iv : word * word => 0 < bv_unsigned (snd iv)) (vm_noaccess (m_vmmaps mo)).

Lemma region_free_of_uncovered : forall l (lo n : word),
  Forall (fun iv : word * word => 0 < bv_unsigned (snd iv)) l -> 0 < bv_unsigned n ->
  (forall z, bv_unsigned lo <= z < bv_unsigned lo + bv_unsigned n -> covered l z = false) ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hpos Hn Hunc; [reflexivity|].
  apply Forall_cons_iff in Hpos as [Hp Hl]. cbn [fst snd] in Hp. cbn [region_free].
  apply andb_true_intro. split.
  - apply negb_true_iff. unfold iv_overlap.
    destruct (Z.ltb_spec (bv_unsigned lo) (bv_unsigned a + bv_unsigned sz)) as [H1|H1]; [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned lo + bv_unsigned n)) as [H2|H2]; [|reflexivity].
    exfalso. specialize (Hunc (Z.max (bv_unsigned lo) (bv_unsigned a)) ltac:(lia)).
    unfold covered in Hunc. cbn [existsb] in Hunc. apply orb_false_iff in Hunc as [Hunc _].
    unfold in_iv, in_rng, B, S in Hunc. cbn [fst snd] in Hunc.
    apply andb_false_iff in Hunc as [Hunc|Hunc]; [apply Z.leb_gt in Hunc| apply Z.ltb_ge in Hunc]; lia.
  - apply IH; [exact Hl| exact Hn|]. intros z Hz. specialize (Hunc z Hz). unfold covered in *. cbn [existsb] in Hunc.
    apply orb_false_iff in Hunc as [_ Hunc]. exact Hunc.
Qed.

(* [comment removed for export] *)
Lemma region_free_noaccess_of_uncovered : forall mo (lo n : word),
  noaccess_pos mo -> 0 < bv_unsigned n -> bv_unsigned lo + bv_unsigned n <= 2^64 ->
  (forall a : word, bv_unsigned lo <= bv_unsigned a < bv_unsigned lo + bv_unsigned n ->
     covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = false) ->
  region_free (vm_noaccess (m_vmmaps mo)) lo n = true.
Proof.
  intros mo lo n Hpos Hn Hend Hunc. apply region_free_of_uncovered; [exact Hpos| exact Hn|].
  intros z Hz. pose proof (u64_range lo) as Rl.
  specialize (Hunc (Z_to_bv 64 z)). rewrite unsigned_lit in Hunc by lia. exact (Hunc Hz).
Qed.

Lemma iv_subtract_pos' : forall (a sz : word) lo hi q,
  iv_wf (a, sz) -> 0 < bv_unsigned sz -> In q (iv_subtract a sz lo hi) -> 0 < bv_unsigned (snd q).
Proof.
  intros a sz lo hi q Hwf Hs Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_pos' : forall l lo hi,
  ivs_wf l -> Forall (fun iv : word * word => 0 < bv_unsigned (snd iv)) l ->
  Forall (fun iv : word * word => 0 < bv_unsigned (snd iv)) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hwf Hpos; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. apply Forall_cons_iff in Hpos as [Hh Ht]. cbn [maps_subtract].
  apply Forall_app. split; [|exact (IH lo hi Hl Ht)].
  apply Forall_forall. intros q Hq. exact (iv_subtract_pos' a sz lo hi q Ha Hh Hq).
Qed.

(* [comment removed for export] *)
Lemma noaccess_pos_mmap_rw : forall mo a n, noaccess_pos mo -> noaccess_pos (mdl_mmap_rw mo a n).
Proof. intros mo a n H. unfold noaccess_pos. rewrite mdl_mmap_rw_vmmaps. exact H. Qed.

Lemma noaccess_pos_fixed : forall flags mo a n, model_ivs_wf mo -> noaccess_pos mo -> noaccess_pos (mdl_fixed flags mo a n).
Proof.
  intros flags mo a n (_ & Wn & _) H. unfold noaccess_pos. rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_noaccess].
  apply maps_subtract_pos'; assumption.
Qed.

Lemma noaccess_pos_munmap : forall mo a n, model_ivs_wf mo -> noaccess_pos mo -> noaccess_pos (mdl_munmap mo a n).
Proof.
  intros mo a n (_ & Wn & _) H. unfold noaccess_pos. rewrite mdl_munmap_vmmaps. cbn [vm_noaccess].
  apply maps_subtract_pos'; assumption.
Qed.

Lemma noaccess_pos_madvise : forall mo a n, noaccess_pos mo -> noaccess_pos (mdl_madvise mo a n).
Proof. intros mo a n H. unfold noaccess_pos. rewrite mdl_madvise_vmmaps. exact H. Qed.

(* [comment removed for export] *)
Lemma mat_stable_noaccess_pos : mat_stable noaccess_pos.
Proof.
  intros mo mo' Hs H. unfold noaccess_pos in *.
  rewrite (proj1 (proj2 (same_but_materialized_frame _ _ Hs))). exact H.
Qed.

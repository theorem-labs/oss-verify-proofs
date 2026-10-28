(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotalCore AsanNodeSem AsanTotal.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AProto ATsafeCore ATsafeEv.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition MOK (mo : Model) : Prop :=
  m_vm_materialized mo = []
  /\ vm_limit (m_vmmaps mo) = LIMIT
  /\ model_ivs_wf mo
  /\ seps (vm_maps (m_vmmaps mo))
  /\ Forall (entry_ok ATOP) (vm_maps (m_vmmaps mo))
  /\ alloc_top (m_vmmaps mo) = ATOP.      (* [comment removed for export] *)

Lemma MOK_nonlazy : forall mo, MOK mo -> nonlazy_bytes mo = vm_backing_used mo.
Proof. intros mo (M1 & _). symmetry. apply vm_backing_used_canon. exact M1. Qed.

(* [comment removed for export] *)
Lemma map_contains_true : forall l (a n : word),
  map_contains l a n = true -> exists e, In e l /\ B e <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= B e + S e.
Proof.
  intros l a n H. unfold map_contains in H. apply existsb_exists in H as (e & Hin & He).
  apply andb_true_iff in He as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists e. unfold B, S. auto.
Qed.

Lemma map_has_true : forall l (a n : word), map_has l a n = true -> In (a, n) l.
Proof.
  intros l a n H. unfold map_has in H. apply existsb_exists in H as ([b s] & Hin & He). cbn in He.
  apply andb_true_iff in He as [H1 H2]. apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma in_iv_subtract : forall a sz lo hi q,
  iv_wf (a, sz) -> lo <= hi -> In q (iv_subtract a sz lo hi) ->
  B (a, sz) <= B q /\ B q + S q <= B (a, sz) + S (a, sz) /\ (B q + S q <= lo \/ hi <= B q).
Proof.
  intros a sz lo hi q Hwf Hlh Hin. unfold iv_wf, B, S in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in Ha, Hs.
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite !unsigned_lit by lia. lia.
Qed.

Lemma in_maps_subtract : forall l lo hi q,
  ivs_wf l -> lo <= hi -> In q (maps_subtract l lo hi) ->
  exists e, In e l /\ B e <= B q /\ B q + S q <= B e + S e /\ (B q + S q <= lo \/ hi <= B q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hlh Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. apply in_iv_subtract; assumption.
  - destruct (IH lo hi q Hl Hlh Hin) as (e & He & H). exists e. split; [right; exact He| exact H].
Qed.

(* [comment removed for export] *)
Lemma page_in_maps_subtract : forall l lo hi p,
  ivs_wf l -> lo <= hi ->
  page_in_ranges p (maps_subtract l lo hi) = true ->
  page_in_ranges p l = true /\ (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p).
Proof.
  intros l lo hi p Hwf Hlh H.
  unfold page_in_ranges in *. apply existsb_exists in H as (q & Hin & Hp). cbv zeta in Hp.
  apply andb_true_iff in Hp as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2.
  destruct (in_maps_subtract l lo hi q Hwf Hlh Hin) as (e & He & E1 & E2 & E3). unfold B, S in *.
  pose proof (bv_unsigned_in_range 64 p). assert (PS : 0 < page_size) by (unfold page_size; lia).
  split; [| lia].
  apply existsb_exists. exists e. split; [exact He|]. cbv zeta. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_lazy_interior : forall (a n p : word),
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  page_in_ranges p (lazy_interior a n) = true ->
  bv_unsigned a <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n.
Proof.
  intros a n p Hal Hnl Hn Hhi H. rewrite (lazy_interior_aligned a n Hal Hnl Hn Hhi) in H.
  unfold page_in_ranges in H. cbn [existsb fst snd] in H. rewrite Bool.orb_false_r in H.
  apply andb_true_iff in H as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_grant : forall mo z nZ,
  MOK mo -> z mod 4096 = 0 -> 0 < z -> z + nZ <= ATOP -> nZ mod 4096 = 0 -> 0 < nZ ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ) = true ->
  MOK (grant_model mo z nZ)
  /\ nonlazy_bytes (grant_model mo z nZ) <= nonlazy_bytes mo + nZ
  /\ m_vm_lazy (grant_model mo z nZ) = m_vm_lazy mo
  /\ vm_maps (m_vmmaps (grant_model mo z nZ)) = (Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo)
  /\ vm_limit (m_vmmaps (grant_model mo z nZ)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo z nZ (M1 & M2 & M3 & M4 & M5 & M6) Hal Hz Hce Hnl Hn Hrf.
  atop_facts. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (WF' : model_ivs_wf (grant_model mo z nZ)).
  { unfold model_ivs_wf, grant_model. model_proj. cbn [vm_maps vm_noaccess]. split; [| split; [exact Wn| split; [exact Wl| exact Wsp]]].
    apply ivs_wf_cons; [| exact Wm]. apply iv_wf_intro. cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  assert (MOK' : MOK (grant_model mo z nZ)).
  { unfold MOK, grant_model. model_proj. cbn [vm_maps vm_limit]. split; [exact M1|]. split; [exact M2|]. split; [exact WF'|]. split; [| split; [| exact M6]].
    - constructor; [| exact M4]. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf]. apply region_free_wsep. exact Hrf.
    - constructor; [| exact M5]. unfold entry_ok. cbn [fst snd]. rewrite !unsigned_lit by lia. atop_facts. repeat split; lia. }
  split; [exact MOK'|]. split; [| split; [reflexivity| split; reflexivity]].
  rewrite <- (vm_backing_used_canon _ M1). rewrite <- (vm_backing_used_canon (grant_model mo z nZ)) by (unfold grant_model; model_proj; exact M1).
  rewrite (vm_backing_used_sem _ WF'), (vm_backing_used_sem _ M3). unfold grant_model. model_proj. cbn [vm_maps vm_noaccess].
  rewrite sum_count_cons. pose proof (iv_count_le_S (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (Z_to_bv 64 z, Z_to_bv 64 nZ)) as IC.
  unfold S in IC. cbn [snd] in IC. rewrite unsigned_lit in IC by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_commit : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  MOK (fixed_model mo F_FIXED a n)
  /\ nonlazy_bytes (fixed_model mo F_FIXED a n) <= nonlazy_bytes mo + n
  /\ m_vm_lazy (fixed_model mo F_FIXED a n) = maps_subtract (m_vm_lazy mo) a (a + n)
  /\ vm_maps (m_vmmaps (fixed_model mo F_FIXED a n)) = vm_maps (m_vmmaps mo)
  /\ vm_limit (m_vmmaps (fixed_model mo F_FIXED a n)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hmc. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (map_contains_true _ _ _ Hmc) as (E & HinE & HE1 & HE2). rewrite ?Ua, ?Un in HE1. rewrite ?Ua, ?Un in HE2.
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXED)) with false. cbv iota.
  rewrite !Ua, !Un.
  assert (WF' : model_ivs_wf (vm_forget_range a (a + n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) mo))).
  { unfold model_ivs_wf, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_noaccess]. rewrite ?Ua, ?Un.
    split; [exact Wm|]. split; [|split]; [apply maps_subtract_wf; [assumption| lia] | apply maps_subtract_wf; [assumption| lia] | exact Wsp]. }
  split; [| split; [| split; [| split]]].
  - unfold MOK, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_limit]. rewrite M1. cbn [List.filter].
    split; [reflexivity|]. split; [exact M2|]. split; [exact WF'|]. split; [exact M4| split; [exact M5| exact M6]].
  - rewrite <- (vm_backing_used_canon _ M1).
    rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
    eapply Z.le_trans. { apply backing_forget_commit_le; [exact M3| lia| reflexivity|]. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity. }
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + n) M4 HinE HE1 HE2 ltac:(lia)). lia.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_recommit : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 -> a mod 4096 = 0 -> n mod 4096 = 0 ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  MOK (fixed_model mo F_FIXNORES a n)
  /\ nonlazy_bytes (fixed_model mo F_FIXNORES a n) <= nonlazy_bytes mo
  /\ m_vm_lazy (fixed_model mo F_FIXNORES a n) = lazy_interior (Z_to_bv 64 a) (Z_to_bv 64 n) ++ maps_subtract (m_vm_lazy mo) a (a + n)
  /\ vm_maps (m_vmmaps (fixed_model mo F_FIXNORES a n)) = vm_maps (m_vmmaps mo)
  /\ vm_limit (m_vmmaps (fixed_model mo F_FIXNORES a n)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hal Hnl Hmc. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXNORES)) with true. cbv iota.
  rewrite !Ua, !Un.
  pose proof (lazy_interior_aligned (Z_to_bv 64 a) (Z_to_bv 64 n)) as HLI. rewrite !Ua, !Un in HLI.
  specialize (HLI ltac:(unfold page_size; lia) ltac:(unfold page_size; lia) Hn ltac:(lia)).
  assert (WF' : model_ivs_wf (vm_add_lazy (Z_to_bv 64 a) (Z_to_bv 64 n) (vm_forget_range a (a + n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) mo)))).
  { unfold model_ivs_wf, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_noaccess]. rewrite ?Ua, ?Un. rewrite HLI.
    split; [exact Wm|]. split; [apply maps_subtract_wf; [assumption| lia]|]. split; [| exact Wsp].
    apply ivs_wf_cons; [apply iv_wf_intro; rewrite Ua, Un; lia| apply maps_subtract_wf; [assumption| lia]]. }
  split; [| split; [| split; [| split]]].
  - unfold MOK, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_limit]. rewrite M1. cbn [List.filter].
    split; [reflexivity|]. split; [exact M2|]. split; [exact WF'|]. split; [exact M4| split; [exact M5| exact M6]].
  - rewrite <- (vm_backing_used_canon _ M1).
    rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
    pose proof (backing_recommit_lazy_le mo (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) (Z_to_bv 64 a) (Z_to_bv 64 n)) as BR.
    rewrite !Ua, !Un in BR. apply BR; auto; try (unfold page_size; lia); try lia.
    unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seps_filter' : forall f l, seps l -> seps (List.filter f l).
Proof. intros. apply seps_filter. assumption. Qed.

Lemma MOK_munmap : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  MOK (munmap_model mo a n)
  /\ nonlazy_bytes (munmap_model mo a n) <= nonlazy_bytes mo
  /\ m_vm_lazy (munmap_model mo a n) = maps_subtract (m_vm_lazy mo) a (a + n)
  /\ (forall e, In e (vm_maps (m_vmmaps (munmap_model mo a n))) -> In e (vm_maps (m_vmmaps mo)))
  /\ vm_limit (m_vmmaps (munmap_model mo a n)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hmh. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  apply map_has_true in Hmh.
  (* [comment removed for export] *)
  destruct (in_split _ _ Hmh) as (l1 & l2 & EL).
  assert (HP : Permutation (vm_maps (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 n) :: (l1 ++ l2))).
  { rewrite EL. apply Permutation_sym. apply Permutation_middle. }
  assert (HF2 : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (l1 ++ l2)).
  { assert (HF : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_maps (m_vmmaps mo))).
    { eapply Forall_impl; [|exact M5]. intros e (He & _). exact He. }
    pose proof (Permutation_Forall HP HF) as X. apply Forall_cons_iff in X as [_ X]. exact X. }
  pose proof (map_remove_perm _ _ _ _ HP M4 ltac:(rewrite Un; lia) HF2) as HR.
  pose proof (seps_perm _ _ HP M4) as Hs2. apply seps_cons_inv in Hs2 as [Hfar Hs12].
  unfold munmap_model, with_mmap_destroyed. rewrite !Ua, !Un.
  set (h' := mkVmMapsFull _ _ _ _ _ _ _ _).
  assert (WF' : model_ivs_wf (vm_forget_range a (a + n) (with_vmmaps h' mo))).
  { unfold model_ivs_wf, h'. model_proj. cbn [vm_maps vm_noaccess].
    split; [unfold map_remove; apply ivs_wf_filter; exact Wm|]. split; [|split]; [apply maps_subtract_wf; [assumption| lia] | apply maps_subtract_wf; [assumption| lia] | exact Wsp]. }
  split; [| split; [| split; [| split]]].
  - unfold MOK, h'. model_proj. cbn [vm_maps vm_limit]. rewrite M1. cbn [List.filter].
    split; [reflexivity|]. split; [exact M2|]. split; [exact WF'|]. split; [| split; [| exact M6]].
    + unfold map_remove. apply seps_filter'. exact M4.
    + unfold map_remove. rewrite Forall_forall in *. intros e He. apply M5. apply (incl_filter _ _ _ He).
  - rewrite <- (vm_backing_used_canon _ M1).
    rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
    rewrite (vm_backing_used_sem _ WF'), (vm_backing_used_sem _ M3). unfold h'. model_proj. cbn [vm_maps vm_noaccess]. rewrite M1. cbn [List.filter length Z.of_nat Z.mul].
    destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
    rewrite (sum_count_perm _ _ _ HR). rewrite (sum_count_perm _ _ _ HP). rewrite sum_count_cons.
    pose proof (sum_count_nonneg (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) [(Z_to_bv 64 a, Z_to_bv 64 n)]) as NN.
    rewrite sum_count_cons in NN. cbn [sum_count] in NN.
    rewrite (sum_count_ext_on _ (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (l1 ++ l2)); [lia|].
    intros e x He Hx. rewrite !covered_app, Cn, Cl.
    pose proof (proj1 (Forall_forall _ _) Hfar e He) as Hw. unfold wsep, B, S in Hw. cbn [fst snd] in Hw. rewrite Ua, Un in Hw.
    replace (in_rng a (a + n) x) with false.
    2:{ symmetry. unfold in_rng. apply andb_false_iff. unfold B, S in Hx. destruct Hw; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia. }
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x); reflexivity.
  - model_proj. reflexivity.
  - unfold h'. model_proj. cbn [vm_maps]. intros e He. unfold map_remove in He. apply (incl_filter _ _ _ He).
  - unfold h'. model_proj. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_count_nonneg : forall P e, 0 <= iv_count P e.
Proof. intros. unfold iv_count. apply zcount_nonneg. Qed.

Lemma iv_count_rng_split : forall e lo m hi, lo <= m <= hi ->
  iv_count (in_rng lo hi) e = iv_count (in_rng lo m) e + iv_count (in_rng m hi) e.
Proof.
  intros e lo m hi Hm. unfold iv_count. rewrite (zcount_and_split (in_rng lo hi) (in_rng lo m)).
  f_equal.
  - apply zcount_ext. intros x _. unfold in_rng.
    destruct (Z.leb_spec lo x), (Z.ltb_spec x hi), (Z.ltb_spec x m); cbn; try reflexivity; lia.
  - apply zcount_ext. intros x _. unfold in_rng.
    destruct (Z.leb_spec lo x), (Z.ltb_spec x hi), (Z.ltb_spec x m), (Z.leb_spec m x); cbn; try reflexivity; lia.
Qed.

Lemma overlap_sum_split : forall l lo m hi, lo <= m <= hi ->
  overlap_sum l lo hi = overlap_sum l lo m + overlap_sum l m hi.
Proof.
  induction l as [|e l IH]; intros lo m hi Hm; [rewrite !overlap_sum_nil; lia|].
  rewrite !overlap_sum_cons, (IH lo m hi Hm), (iv_count_rng_split e lo m hi Hm). lia.
Qed.

Lemma overlap_sum_nonneg : forall l lo hi, 0 <= overlap_sum l lo hi.
Proof. intros. unfold overlap_sum. apply sum_count_nonneg. Qed.

Lemma iv_count_in_rng_le0 : forall p lo hi, lo <= hi -> 0 <= iv_count (in_rng lo hi) p <= hi - lo.
Proof. intros. split; [apply iv_count_nonneg| apply iv_count_in_rng_le; assumption]. Qed.

(* [comment removed for export] *)
Lemma overlap_sum_seps : forall l lo hi, seps l -> lo <= hi -> overlap_sum l lo hi <= hi - lo.
Proof.
  induction l as [|e l IH]; intros lo hi Hs Hlh; [rewrite overlap_sum_nil; lia|].
  apply seps_cons_inv in Hs as [Hf Hs]. rewrite overlap_sum_cons.
  set (a := B e). set (s := S e).
  pose proof (B_range e) as Ha. pose proof (S_range e) as Hsz. fold a in Ha. fold s in Hsz.
  set (m1 := Z.max lo (Z.min hi a)). set (m2 := Z.min hi (Z.max lo (a + s))).
  assert (Hm : lo <= m1 /\ m1 <= m2 /\ m2 <= hi) by lia.
  rewrite (overlap_sum_split l lo m1 hi) by lia. rewrite (overlap_sum_split l m1 m2 hi) by lia.
  rewrite (iv_count_rng_split e lo m1 hi) by lia. rewrite (iv_count_rng_split e m1 m2 hi) by lia.
  (* [comment removed for export] *)
  assert (MID : overlap_sum l m1 m2 = 0).
  { destruct (Z.eq_dec m1 m2) as [E|NE].
    - pose proof (overlap_sum_nonneg l m1 m2). unfold overlap_sum in *.
      pose proof (sum_count_mono (in_rng m1 m2) (fun _ => false) l ltac:(intros x Hx; exfalso; unfold in_rng in Hx; destruct (Z.leb_spec m1 x), (Z.ltb_spec x m2); cbn in Hx; try discriminate; lia)).
      assert (Z0 : sum_count (fun _ : Z => false) l = 0).
      { clear. induction l as [|q l IH2]; [reflexivity|]. rewrite sum_count_cons, IH2. unfold iv_count. rewrite zcount_const_false. lia. }
      lia.
    - unfold overlap_sum. clear IH Hs. induction l as [|q l IH2]; [reflexivity|].
      apply Forall_cons_iff in Hf as [Hq Hf]. rewrite sum_count_cons, (IH2 Hf).
      rewrite iv_count_in_rng_disjoint; [lia|]. unfold wsep in Hq. unfold B, S in *. lia. }
  (* [comment removed for export] *)
  assert (E1 : iv_count (in_rng lo m1) e = 0).
  { destruct (Z.eq_dec lo m1) as [E|NE].
    - pose proof (iv_count_in_rng_le0 e lo m1 ltac:(lia)). lia.
    - apply iv_count_in_rng_disjoint. fold a s. lia. }
  assert (E3 : iv_count (in_rng m2 hi) e = 0).
  { destruct (Z.eq_dec m2 hi) as [E|NE].
    - pose proof (iv_count_in_rng_le0 e m2 hi ltac:(lia)). lia.
    - apply iv_count_in_rng_disjoint. fold a s. lia. }
  pose proof (iv_count_in_rng_le e m1 m2 ltac:(lia)).
  pose proof (IH lo m1 Hs ltac:(lia)). pose proof (IH m2 hi Hs ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma nonlazy_fixed_repl_le : forall mo flags a n,
  MOK mo -> mmap_noreserve_b (Z_to_bv 64 flags) = false -> 0 <= a -> 0 <= n -> a + n < 2^64 ->
  nonlazy_bytes (fixed_model mo flags a n) <= nonlazy_bytes mo + n.
Proof.
  intros mo flags a n (M1 & M2 & M3 & M4 & M5 & M6) Hnr Ha Hn Hhi.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. rewrite Hnr. rewrite !Ua, !Un.
  rewrite <- (vm_backing_used_canon _ M1).
  rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
  eapply Z.le_trans.
  { apply backing_forget_commit_le; [exact M3| lia| reflexivity|]. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity. }
  pose proof (overlap_sum_seps (vm_maps (m_vmmaps mo)) a (a + n) M4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma backing_forget_span_le : forall m h' lo hi e,
  model_ivs_wf m -> lo <= hi -> hi <= 2^64 ->
  B e = lo -> S e = hi - lo ->
  vm_maps h' = e :: maps_subtract (vm_maps (m_vmmaps m)) lo hi ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ->
  vm_backing_used (vm_forget_range lo hi (with_vmmaps h' m))
  <= vm_backing_used m + (hi - lo).
Proof.
  intros m h' lo hi e Hwf Hlh Hhi HB HS Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  destruct (maps_subtract_sem _ lo hi Wm Hlh) as (Wm' & Smm & _).
  assert (He : iv_wf e) by (unfold iv_wf; lia).
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_forget_range lo hi (with_vmmaps h' m))))).
  { model_proj. rewrite Hmaps. apply ivs_wf_cons; [exact He | exact Wm']. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  rewrite sum_count_cons, Smm.
  lazymatch goal with |- iv_count ?P e + _ + _ <= _ =>
    assert (E1 : iv_count P e <= hi - lo)
      by (unfold iv_count; rewrite HS; eapply Z.le_trans; [apply zcount_le_len|]; rewrite Z2Nat.id by lia; lia);
    assert (E2 : sum_count (fun x => P x && negb (in_rng lo hi x)) (vm_maps (m_vmmaps m))
                 <= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)))
      by (apply sum_count_mono; intros x; rewrite !covered_app, Cn, Cl;
          destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence)
  end.
  unfold page_size in *. nia.
Qed.

(* [comment removed for export] *)
Lemma backing_recommit_span_lazy_le : forall m h' (a n : word),
  model_ivs_wf m ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = (a, n) :: maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  vm_backing_used (vm_add_lazy a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' m)))
  <= vm_backing_used m.
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  set (lo := bv_unsigned a) in *. set (hi := (lo + bv_unsigned n)%Z) in *.
  assert (Hlh : lo <= hi) by (pose proof (bv_unsigned_in_range 64 n); lia).
  pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
  destruct (maps_subtract_sem _ lo hi Wm Hlh) as (Wm' & Smm & _).
  assert (He : iv_wf (a, n)) by (unfold iv_wf, B, S; cbn [fst snd]; lia).
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m)))))).
  { model_proj. rewrite Hmaps. apply ivs_wf_cons; [exact He | exact Wm']. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna, Hli.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  rewrite sum_count_cons, Smm.
  lazymatch goal with |- iv_count ?P (a, n) + _ + _ <= _ =>
    assert (E1 : iv_count P (a, n) = 0)
      by (unfold iv_count; apply zcount_false; intros x Hx; unfold B, S in Hx; cbn [fst snd] in Hx;
          pose proof (bv_unsigned_in_range 64 n); rewrite Z2Nat.id in Hx by lia;
          rewrite !covered_app; unfold covered at 2; cbn [existsb]; unfold in_iv, B, S; cbn [fst snd]; unfold in_rng;
          replace (bv_unsigned a <=? x) with true by (symmetry; apply Z.leb_le; lia);
          replace (x <? bv_unsigned a + bv_unsigned n) with true by (symmetry; apply Z.ltb_lt; lia);
          cbn; rewrite ?Bool.orb_true_r; reflexivity);
    assert (E2 : sum_count (fun x => P x && negb (in_rng lo hi x)) (vm_maps (m_vmmaps m))
                 <= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)))
      by (apply sum_count_mono; intros x; rewrite !covered_app; unfold covered at 2; cbn [existsb]; fold (covered (maps_subtract (m_vm_lazy m) lo hi) x);
          rewrite Cn, Cl; destruct (in_iv (a, n) x), (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence)
  end.
  unfold page_size in *. nia.
Qed.

(* [comment removed for export] *)
Lemma nonlazy_fixed_span_repl_le : forall mo flags a n,
  MOK mo -> mmap_noreserve_b (Z_to_bv 64 flags) = false -> 0 <= a -> 0 <= n -> a + n < 2^64 ->
  nonlazy_bytes (mmap_fixed_span_repl (Z_to_bv 64 flags) (Z_to_bv 64 a) (Z_to_bv 64 n) mo) <= nonlazy_bytes mo + n.
Proof.
  intros mo flags a n (M1 & M2 & M3 & M4 & M5 & M6) Hnr Ha Hn Hhi.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold mmap_fixed_span_repl, with_mmap_replacement, with_mmap_backing. rewrite Hnr. rewrite !Ua, !Un.
  rewrite <- (vm_backing_used_canon _ M1).
  rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
  eapply Z.le_trans.
  { apply (backing_forget_span_le mo _ a (a + n) (Z_to_bv 64 a, Z_to_bv 64 n));
      [exact M3| lia| lia| unfold B; cbn [fst]; exact Ua| unfold S; cbn [snd]; rewrite Un; lia| |];
      unfold mmap_fixed_rw_span_next; cbn [vm_maps vm_noaccess]; rewrite ?Ua, ?Un; reflexivity. }
  lia.
Qed.

Lemma nonlazy_fixed_span_repl_lazy_le : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 -> a mod 4096 = 0 -> n mod 4096 = 0 ->
  nonlazy_bytes (mmap_fixed_span_repl (Z_to_bv 64 F_FIXNORES) (Z_to_bv 64 a) (Z_to_bv 64 n) mo) <= nonlazy_bytes mo.
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hal Hnl.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold mmap_fixed_span_repl, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXNORES)) with true. cbv iota.
  rewrite !Ua, !Un.
  rewrite <- (vm_backing_used_canon _ M1).
  rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
  pose proof (backing_recommit_span_lazy_le mo (mmap_fixed_rw_span_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) (Z_to_bv 64 a) (Z_to_bv 64 n)) as BR.
  rewrite !Ua, !Un in BR. apply BR; auto; try (unfold page_size; lia); try lia.
  - unfold mmap_fixed_rw_span_next. cbn [vm_maps]. rewrite ?Ua, ?Un. reflexivity.
  - unfold mmap_fixed_rw_span_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fp_ok_mono2 : forall lz lz' (A A' : alw),
  (forall p, page_in_ranges p lz' = true -> page_in_ranges p lz = true \/ A' p) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
  intros lz lz' A A' SUB LE b j H k Hk Hb.
  destruct (H k Hk Hb) as [NL | AL].
  - destruct (page_in_ranges (page_base_of (b + Z.of_nat k)) lz') eqn:E; [|left; exact E]. destruct (SUB _ E) as [E'|HA]; [congruence| right; exact HA].
  - right. apply LE, AL.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_app : forall p l1 l2, page_in_ranges p (l1 ++ l2) = page_in_ranges p l1 || page_in_ranges p l2.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcost (len : Z) : Z := len / 4096 + len / 32768 + 4.
Fixpoint gcost (ga : list Z) : Z := match ga with [] => 0 | l :: ga' => pcost l + gcost ga' end.
Lemma pcost_nonneg : forall l, 0 <= l -> 0 <= pcost l.
Proof. intros. unfold pcost. pose proof (Z.div_pos l 4096). pose proof (Z.div_pos l 32768). lia. Qed.

(* [comment removed for export] *)
Definition GA (G : list (Z * Z)) (A : alw) : Prop :=
  forall g, In g G ->
    0 <= fst g /\ 0 <= snd g /\ fst g + snd g <= ATOP
    /\ (forall z, fst g <= z < fst g + snd g -> A (page_base_of z))
    /\ (forall z', shad (fst g) <= z' < shad (fst g + snd g) -> A (page_base_of z')).

Lemma GA_nil : forall A, GA [] A. Proof. intros A g []. Qed.
Lemma GA_le : forall G A A', GA G A -> alw_le A A' -> GA G A'.
Proof.
  intros G A A' H LE g Hg. destruct (H g Hg) as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; intros; apply LE; auto.
Qed.

Section Ops.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
(* [comment removed for export] *)
Variable NLK : Z.
Let NMAXZ : Z := Z.of_nat NMAX.
Hypothesis HLIM : NLK + NMAXZ * 4096 <= LIMIT.
Hypothesis HNLK : 0 <= NLK.
(* [comment removed for export] *)
Hypothesis ABASE_SH : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.

Definition KI (b : Z) (G : list (Z * Z)) (A : alw) (k : Z) (mo : Model) : Prop :=
  MOK mo /\ 0 <= b /\ nonlazy_bytes mo + b <= NLK /\ alw_le Abase A /\ GA G A /\ abud A k /\ 0 <= k.

Lemma KI_acct_ok : forall b G A k mo, KI b G A k mo -> k <= NMAXZ -> acct_ok NMAX (fp_ok (m_vm_lazy mo) A) A mo.
Proof.
  intros b G A k mo (M & Hb & HN & _ & _ & (L & ND & HL & HAL) & Hk) Hkc. pose proof M as (_ & M2 & _).
  split; [apply footprint_ok_fp_ok|]. split.
  - exists L. split; [exact ND|]. split; [| exact HAL]. subst NMAXZ. lia.
  - rewrite M2. unfold page_size. subst NMAXZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma adec_mmap_ret : forall len rsp z, adec_mmap ATOP len PROT_RW rsp = Some z -> bv_unsigned (eff_ret rsp) = z.
Proof.
  intros len rsp z H. unfold adec_mmap in H. change (PROT_RW =? 0) with false in H. cbv iota in H.
  unfold dec_mmap in H. destruct rsp as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct zs as [|[a n] zs].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); discriminate.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    match type of H with (match (if ?c then _ else _) with _ => _ end) = _ => destruct c; [|discriminate] end. cbn [eff_ret]. injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_len_lit : forall len, 0 < len < 2^63 -> len mod 4096 = 0 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = len.
Proof. intros len H1 H2. rewrite mmap_len_eq by lia. apply mmap_len_id; lia. Qed.

Lemma shad_div8 : forall a, shad a = 2147450880 + a / 8.
Proof. intros. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shlen_div8 : forall l, shlen l = l / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_bounds : forall a, 0 <= a <= 2^47 -> 2147450880 <= shad a <= 2147450880 + 2^44.
Proof.
  intros a Ha. rewrite shad_div8. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (2^47) 8 ltac:(lia) ltac:(lia)). change (2^47/8) with (2^44) in H0. lia.
Qed.
Lemma shlen_bounds : forall l, 0 <= l -> 0 <= shlen l <= l.
Proof. intros l Hl. rewrite shlen_div8. pose proof (Z.div_pos l 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound l 8 l ltac:(lia) ltac:(lia)). lia. Qed.
Lemma shad_le_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma shad_plus : forall a n, a mod 8 = 0 -> shad (a + n) = shad a + Z.shiftr n 3.
Proof.
  intros a n Ha. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  pose proof (Z.div_mod a 8 ltac:(lia)). rewrite Ha, Z.add_0_r in H.
  rewrite H at 1. rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma robust_le : forall x, x <= NLK -> robust NMAX x LIMIT.
Proof. intros x Hx. left. unfold page_size. subst NMAXZ. lia. Qed.

Lemma nsafeA_grant : forall b G A k mo len,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 -> len <= b ->
  nsafeA NMAX (NMmap 0 len PROT_RW F_ANON) mo.
Proof.
  intros b G A k mo len HK Hlen Hal Hlb. pose proof HK as (M & Hb & HN & _). pose proof M as (M1 & M2 & _).
  split.
  - cbn [nsafeA0]. unfold mmap_safeA_b.   (* [comment removed for export] *)
    pose proof (nsafe_mmap_rw 0 len mo ltac:(lia)) as X. cbn [nsafe] in X.
    change PROT_RW with (PROT_READ + PROT_WRITE). change F_ANON with (MAP_PRIVATE + MAP_ANONYMOUS). exact X.
  - cbn [nslack]. rewrite (mmap_len_lit len) by lia. cbv zeta. rewrite M2. split.
    + right. apply robust_le. lia.
    + split.
      * change (mmap_fixed_repl (Z_to_bv 64 F_ANON) (Z_to_bv 64 0) (Z_to_bv 64 len) mo) with (fixed_model mo F_ANON 0 len).
        apply robust_le. pose proof (nonlazy_fixed_repl_le mo F_ANON 0 len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.
      * (* [comment removed for export] *)
        apply robust_le. pose proof (nonlazy_fixed_span_repl_le mo F_ANON 0 len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma NSAFEA_FIXED : forall a len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len -> len mod 4096 = 0 -> 0 < a -> a mod 4096 = 0 -> a + len <= ATOP ->
  alloc_top (m_vmmaps mo) = ATOP ->      (* [comment removed for export] *)
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  nslack NMAX (NMmap a len PROT_RW flags) mo ->
  nsafeA NMAX (NMmap a len PROT_RW flags) mo.
Proof.
  intros a len flags mo Hfl Hlen Hal Ha Haal Hce Htop Hrf Hmc Hsl. split; [| exact Hsl].
  atop_facts.
  assert (Hlen2 : len < 2^47) by lia.
  pose proof (nsafeA0_mmap_fixed_rw a len flags mo) as X. cbv zeta in X. rewrite (mmap_len_lit len) in X by lia.
  change PROT_RW with (PROT_READ + PROT_WRITE). apply X.
  - destruct Hfl as [E | E]; rewrite E; vm_compute; reflexivity.
  - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - exact Ha.
  - unfold page_size. exact Haal.
  - rewrite Htop. lia.
  - left. split; [exact Hrf | exact Hmc].
Qed.

Lemma nsafeA_fixed : forall b G A k mo a len flags,
  KI b G A k mo -> (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len < 2^41 -> len mod 4096 = 0 ->
  0 < a -> a mod 4096 = 0 -> a + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  (flags = F_FIXED -> len <= b) ->
  nsafeA NMAX (NMmap a len PROT_RW flags) mo.
Proof.
  intros b G A k mo a len flags HK Hfl Hlen Hal Ha Haal Hce Hrf Hmc Hlb. pose proof HK as (M & Hb & HN & _). pose proof M as (M1 & M2 & _ & _ & _ & M6).
  apply NSAFEA_FIXED; auto; try lia.
  cbn [nslack]. rewrite (mmap_len_lit len) by lia. cbv zeta. rewrite M2.
  change (mmap_fixed_repl (Z_to_bv 64 flags) (Z_to_bv 64 a) (Z_to_bv 64 len) mo) with (fixed_model mo flags a len).
  atop_facts. destruct Hfl as [-> | ->].
  - specialize (Hlb eq_refl). split; [| split].
    + right. apply robust_le. lia.
    + apply robust_le. pose proof (nonlazy_fixed_repl_le mo F_FIXED a len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.
    + apply robust_le. pose proof (nonlazy_fixed_span_repl_le mo F_FIXED a len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.   (* [comment removed for export] *)
  - split; [| split].
    + left. reflexivity.
    + apply robust_le. destruct (MOK_recommit mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Haal Hal Hmc) as (_ & X & _). lia.
    + apply robust_le. pose proof (nonlazy_fixed_span_repl_lazy_le mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Haal Hal). lia.   (* [comment removed for export] *)
Qed.

Lemma nsafeA_munmap : forall mo a len,
  0 < len <= 2^40 -> 0 <= a -> a mod 4096 = 0 -> a + mmap_len len <= ATOP ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true ->
  nsafeA NMAX (NMunmap a len) mo.
Proof.
  intros mo a len Hlen Ha Haal Hce Hmh. atop_facts. pose proof (mmap_len_bounds len ltac:(lia)) as ML. split; [| exact I].
  cbn [nsafeA0 nsafe]. unfold munmap_safe_b. rewrite (unsigned_lit a) by lia. unfold page_size. rewrite Haal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia.
  rewrite Hmh. destruct (TASK_SIZE <? a + mmap_len len); reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma nsafeA_madvise : forall mo a len,
  0 < len <= 2^40 -> 0 <= a -> a mod 4096 = 0 -> a + mmap_len len <= 2^47 ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true ->
  nsafeA NMAX (NMadvise a len) mo.
Proof.
  intros mo a len Hlen Ha Haal Hce Hok. pose proof (mmap_len_bounds len ltac:(lia)) as ML. split; [| exact I].
  cbn [nsafeA0 nsafe]. unfold madvise_safe_b. rewrite (unsigned_lit a) by lia. unfold page_size. rewrite Haal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb Z.eqb].
  rewrite mmap_len_eq by lia. rewrite Hok. destruct (two_pow_64 <=? a + mmap_len len); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_base_of_aligned : forall y, bv_unsigned (page_base_of y) mod 4096 = 0.
Proof.
  intros y. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.mod_mod_divide by (exists 4503599627370496; reflexivity). apply Z_mod_mult.
Qed.

Lemma page_base_of_self : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base_of (bv_unsigned p) = p.
Proof.
  intros p Hp. unfold page_base_of, page_size.
  replace (bv_unsigned p / 4096 * 4096) with (bv_unsigned p) by (pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)); lia).
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma page_base_of_page : forall y, page_base_of (bv_unsigned (page_base_of y)) = page_base_of y.
Proof. intros. apply page_base_of_self. apply page_base_of_aligned. Qed.

(* [comment removed for export] *)
Lemma fp_ok_mono3 : forall lz lz' (A A' : alw),
  (forall y, page_in_ranges (page_base_of y) lz' = true -> page_in_ranges (page_base_of y) lz = true \/ A' (page_base_of y)) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
  intros lz lz' A A' SUB LE b j H k Hk Hb.
  destruct (H k Hk Hb) as [NL | AL].
  - destruct (page_in_ranges (page_base_of (b + Z.of_nat k)) lz') eqn:E; [|left; exact E]. destruct (SUB _ E) as [E'|HA]; [congruence| right; exact HA].
  - right. apply LE, AL.
Qed.

(* [comment removed for export] *)
Lemma page_notin_subtract : forall l lo len z,
  ivs_wf l -> 0 <= len -> lo <= z < lo + len -> 0 <= lo -> lo + len <= 2^64 ->
  page_in_ranges (page_base_of z) (maps_subtract l lo (lo + len)) = false.
Proof.
  intros l lo len z Hwf Hlen Hz Hlo Hhi.
  destruct (page_in_ranges (page_base_of z) (maps_subtract l lo (lo + len))) eqn:E; [|reflexivity]. exfalso.
  apply page_in_maps_subtract in E as [_ E]; [| exact Hwf| lia].
  pose proof (page_base_of_range z ltac:(lia)). unfold page_size in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma step_grant : forall b G A k mo len z rsp,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 -> len <= b ->
  z mod 4096 = 0 -> 0 < z -> z + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 len) = true ->
  adec_mmap ATOP len PROT_RW rsp = Some z ->
  let A' := aunion A (range_pages z len ++ range_pages (shad z) (shlen len)) in
  let mo' := grant_model mo z len in
  fstepS (NMmap 0 len PROT_RW F_ANON) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A')
  /\ alw_le A A'
  /\ KI (b - len) ((z, len) :: G) A' (k + pcost len) mo'.
Proof.
  intros b G A k mo len z rsp HK Hlen Hlal Hlb Hzal Hz Hce Hrf Hdec A' mo'. subst mo'.
  pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk). atop_facts.
  destruct (MOK_grant mo z len M Hzal Hz ltac:(atop_facts; lia) Hlal ltac:(lia) Hrf) as (M' & NL' & LZ' & _ & _).
  pose proof (adec_mmap_ret _ _ _ Hdec) as RET.
  assert (LE : alw_le A A') by apply aunion_le.
  assert (SH8 : shad (z + len) = shad z + shlen len).
  { unfold shlen. apply shad_plus. replace z with (z / 4096 * 512 * 8); [apply Z_mod_mult|]. pose proof (Z.div_mod z 4096 ltac:(lia)). lia. }
  pose proof (shad_bounds z ltac:(lia)) as SZ0. pose proof (shlen_bounds len ltac:(lia)) as SL.
  assert (SHI : shad z + shlen len <= 2^64).
  { rewrite <- SH8. pose proof (shad_bounds (z + len) ltac:(lia)). lia. }
  split; [| split; [exact LE|]].
  - (* [comment removed for export] *)
    unfold grant_model in LZ' |- *. rewrite LZ'. split; [split|split].
    + apply fp_ok_mono; [auto| exact LE].
    + intros _ _. rewrite RET. rewrite (mmap_len_lit len) by lia. apply rng_fp_ok_union; [lia| lia|].
      intros y Hy. apply in_app_iff. left. apply range_pages_spec; lia.
    + intros _ _ _. rewrite RET. rewrite (mmap_len_lit len) by lia. apply rng_fp_ok_union; [lia| lia|].
      intros y Hy. apply in_app_iff. right. apply range_pages_spec; lia.
    + apply fp_ok_bw.
  - (* [comment removed for export] *)
    split; [exact M'|]. split; [lia|]. split; [lia|]. split; [eapply alw_le_trans; [exact HAB| exact LE]|]. split; [|split].
    + intros g [<-|Hg].
      * cbn [fst snd]. split; [lia|]. split; [lia|]. split; [atop_facts; lia|]. split.
        -- intros y Hy. apply aunion_in. apply in_app_iff. left. apply range_pages_spec; lia.
        -- intros y Hy. rewrite SH8 in Hy. apply aunion_in. apply in_app_iff. right. apply range_pages_spec; lia.
      * apply (GA_le G A A' HGA LE g Hg).
    + eapply abud_mono; [apply abud_union; exact HBU|].
      rewrite length_app, Nat2Z.inj_add.
      pose proof (range_pages_length z len ltac:(lia) ltac:(lia)).
      assert (Z.of_nat (length (range_pages (shad z) (shlen len))) <= len / 32768 + 2).
      { destruct (Z.eq_dec (shlen len) 0) as [E0|NE].
        - rewrite E0. unfold range_pages. rewrite pages_from_length.
          replace ((shad z + 0 - 1) / 4096 - shad z / 4096 + 1) with ((shad z - 1) / 4096 - shad z / 4096 + 1) by (f_equal; f_equal; f_equal; lia).
          pose proof (Z.div_pos len 32768). 
          assert ((shad z - 1) / 4096 <= shad z / 4096) by (apply Z.div_le_mono; lia). lia.
        - pose proof (range_pages_length (shad z) (shlen len) ltac:(lia) ltac:(lia)) as RPL.
          unfold shlen in RPL |- *. rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
          rewrite Z.div_div in RPL by lia. change (8 * 4096) with 32768 in RPL. lia. }
      unfold pcost. lia.
    + pose proof (pcost_nonneg len ltac:(lia)). lia.
Qed.

Lemma shad8 : forall a len, a mod 4096 = 0 -> shad (a + len) = shad a + shlen len.
Proof.
  intros a len Ha. unfold shlen. apply shad_plus. replace a with (a / 4096 * 512 * 8); [apply Z_mod_mult|].
  pose proof (Z.div_mod a 4096 ltac:(lia)). lia.
Qed.

Lemma step_commit : forall b G A k mo a len rsp,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 -> len <= b ->
  0 < a -> a mod 4096 = 0 -> a + len <= ATOP -> inAP SB PA a len ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  adec_mmap ATOP len PROT_RW rsp = Some a ->
  let mo' := fixed_model mo F_FIXED a len in
  fstepS (NMmap a len PROT_RW F_FIXED) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A)
  /\ KI (b - len) G A k mo'.
Proof.
  intros b G A k mo a len rsp HK Hlen Hlal Hlb Ha Haal Hce HAP Hmc Hdec mo'. subst mo'.
  pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk). atop_facts. pose proof M as (_ & _ & (_ & _ & Wl & _) & _).
  destruct (MOK_commit mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Hmc) as (M' & NL' & LZ' & _ & _).
  pose proof (adec_mmap_ret _ _ _ Hdec) as RET.
  pose proof (shad8 a len Haal) as SH8.
  pose proof (shad_bounds a ltac:(lia)) as SZ0. pose proof (shlen_bounds len ltac:(lia)) as SL.
  pose proof (shad_bounds (a + len) ltac:(lia)) as SZ1.
  split.
  - rewrite LZ'. split; [split|split].
    + apply fp_ok_mono; [| apply alw_le_refl]. intros p Hp. apply page_in_maps_subtract in Hp as [Hp _]; [exact Hp| exact Wl| lia].
    + intros _ _. rewrite RET. rewrite (mmap_len_lit len) by lia. apply rng_fp_ok; [lia| lia|].
      intros y Hy. left. apply page_notin_subtract; auto; lia.
    + intros _ _ _. rewrite RET. rewrite (mmap_len_lit len) by lia. apply rng_fp_ok; [lia| lia|].
      intros y Hy. right. apply HAB. apply ABASE_SH. rewrite SH8 in SZ1.
      destruct HAP as [[P1 P2]|[P1 P2]].
      * left. pose proof (shad_le_mono SB a P1). pose proof (shad_le_mono (a + len) (SB + K_SPACE_SIZE) P2). lia.
      * right. pose proof (shad_le_mono PA a P1). pose proof (shad_le_mono (a + len) (PA + K_PTRARR_RESERVE) P2). lia.
    + apply fp_ok_bw.
  - split; [exact M'|]. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

Lemma step_recommit : forall b G A k mo a len rsp,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 ->
  0 < a -> a mod 4096 = 0 -> a + len <= ATOP -> covG G a len ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  adec_mmap ATOP len PROT_RW rsp = Some a ->
  let mo' := fixed_model mo F_FIXNORES a len in
  fstepS (NMmap a len PROT_RW F_FIXNORES) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A)
  /\ KI b G A k mo'.
Proof.
  intros b G A k mo a len rsp HK Hlen Hlal Ha Haal Hce HCG Hmc Hdec mo'. subst mo'.
  pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk). atop_facts. pose proof M as (_ & _ & (_ & _ & Wl & _) & _).
  destruct (MOK_recommit mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Haal Hlal Hmc) as (M' & NL' & LZ' & _ & _).
  pose proof (adec_mmap_ret _ _ _ Hdec) as RET.
  destruct HCG as (g & Hg & Hg0 & Hg1 & Hg2). destruct (HGA g Hg) as (G1 & G2 & G3 & G4 & G5).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (INA : forall y, a <= y < a + len -> A (page_base_of y)).
  { intros y Hy. apply G5. lia. }
  split.
  - rewrite LZ'. split; [split|split].
    + apply fp_ok_mono3; [| apply alw_le_refl]. intros y Hy. rewrite page_in_ranges_app in Hy. apply Bool.orb_true_iff in Hy as [Hy|Hy].
      * right. apply page_in_lazy_interior in Hy; rewrite ?Ua, ?Un in *; try (unfold page_size; lia).
        rewrite <- page_base_of_page. apply INA. unfold page_size in Hy. lia.
      * left. apply page_in_maps_subtract in Hy as [Hy _]; [exact Hy| exact Wl| lia].
    + intros _ _. rewrite RET. rewrite (mmap_len_lit len) by lia. apply rng_fp_ok; [lia| lia|].
      intros y Hy. right. apply INA. exact Hy.
    + intros HNR. exfalso. vm_compute in HNR. discriminate.
    + apply fp_ok_bw.
  - split; [exact M'|]. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

Lemma step_munmap : forall b G A k mo a len rsp,
  KI b G A k mo -> 0 < len <= 2^40 -> 0 <= a -> a + mmap_len len <= ATOP ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true ->
  let mo' := munmap_model mo a (mmap_len len) in
  fstepS (NMunmap a len) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A)
  /\ KI b G A k mo'.
Proof.
  intros b G A k mo a len rsp HK Hlen Ha Hce Hmh mo'. subst mo'. pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk). atop_facts. pose proof M as (_ & _ & (_ & _ & Wl & _) & _).
  destruct (MOK_munmap mo a (mmap_len len) M ltac:(lia) ltac:(lia) ltac:(lia) Hmh) as (M' & NL' & LZ' & _ & _).
  split.
  - assert (LE : fp_le (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy (munmap_model mo a (mmap_len len))) A)).
    { apply fp_ok_mono; [| apply alw_le_refl].
      rewrite LZ'. intros p Hp. apply page_in_maps_subtract in Hp as [Hp _]; [exact Hp| exact Wl| lia]. }
    split; [| exact LE]. cbn [fstepA]. intros b0 j Hb0 _. exact (LE _ _ Hb0).   (* [comment removed for export] *)
  - split; [exact M'|]. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TS_event : forall {R} n (d : resp -> option Z) (f : Z -> itree node (exc R)) RNG A mo Q,
  acct_ok NMAX RNG A mo -> nsafeA NMAX n mo ->
  (forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     exists z RNG' A', d rsp = Some z /\ fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS NMAX RNG' A' (f z) mo' Q) ->
  TS NMAX RNG A (ebind (enode n d) f) mo Q.
Proof.
  intros R n d f RNG A mo Q HA HS HK. unfold ebind, enode. cbn [bind]. apply TS_unfold_vis.
  split; [exact HA|]. split; [exact HS|].
  intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (z & RNG' & A' & Hd & HF & HL & HT).
  exists RNG', A'. rewrite Hd. cbn [bind]. split; [exact HF|]. split; [exact HL| exact HT].
Qed.

Lemma gcost_nonneg : forall ga, Forall (fun l => 0 <= l) ga -> 0 <= gcost ga.
Proof. induction ga as [|l ga IH]; intros H; cbn; [lia|]. apply Forall_cons_iff in H as [H1 H2]. pose proof (pcost_nonneg l H1). specialize (IH H2). lia. Qed.

(* [comment removed for export] *)
Definition KPOST {R} (RP : list (Z * Z) -> R -> Prop) (Post : R -> Model -> Prop) (G : list (Z * Z)) (KCAP : Z) : postT (exc R) :=
  EQ (fun r RNG' A' mo' => exists G' b' k', RP G' r /\ Post r mo' /\ KI b' G' A' k' mo' /\ k' <= KCAP /\ incl G G' /\ RNG' = fp_ok (m_vm_lazy mo') A').

Lemma KPOST_mono_G : forall {R} RP Post (G G1 : list (Z * Z)) KCAP (r : exc R) RNG A mo,
  incl G G1 -> KPOST RP Post G1 KCAP r RNG A mo -> KPOST (R:=R) RP Post G KCAP r RNG A mo.
Proof.
  intros R RP Post G G1 KCAP [|r] RNG A mo HI H; cbn in *; [exact I|].
  destruct H as (G' & b' & k' & H1 & H2 & H3 & H4 & H5 & H6). exists G', b', k'. repeat (split; [assumption|]).
  split; [eapply incl_tran; eauto| exact H6].
Qed.

Theorem TS_aembed : forall {R} (t : AM R) (RP : list (Z * Z) -> R -> Prop) Post ga G b A k KCAP mo,
  atotal (aok ATOP) (apost ATOP) t mo Post -> evq SB PA RP ga G b t -> KI b G A k mo ->
  Forall (fun l => 0 <= l) ga -> k + gcost ga <= KCAP -> KCAP <= NMAXZ ->
  TS NMAX (fp_ok (m_vm_lazy mo) A) A (aembed ATOP t) mo (KPOST RP Post G KCAP).
Proof.
  intros R t. induction t as [r | e k0 IH]; intros RP Post ga G b A k KCAP mo HT HE HK Hga Hk HKC.
  - rewrite aembed_ret. pose proof (gcost_nonneg ga Hga). apply TS_ret_ok.
    + eapply KI_acct_ok; [exact HK| lia].
    + cbn in HT, HE. exists G, b, k. split; [exact HE|]. split; [exact HT|]. split; [exact HK|]. split; [lia|]. split; [apply incl_refl| reflexivity].
  - cbn [atotal] in HT. destruct HT as [Hok HT]. pose proof (gcost_nonneg ga Hga) as GC0.
    assert (HAT : atop_ok ATOP) by (unfold atop_ok, AsanInv.ACEIL, AsanInv.ATOP_MAX; atop_facts; lia).
    pose proof (asan_node_sound ATOP HAT e mo Hok) as (n & d & En & Hans & _ & _).
    pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk0).
    destruct e as [t0|b0|a len prot flags|a len|a l p|a len|w]; cbn [aok] in Hok; try contradiction.
    + (* [comment removed for export] *)
      destruct Hok as (-> & Hlen & Htop & Hc). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE. destruct HE as (_ & _ & Hlal & HE).
      rewrite aembed_vis. cbn [aev_tree].
      assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
      destruct HE as [(-> & -> & HE)|[(-> & HAP & Hlb & HE)|(-> & HCG & HE)]].
      * (* [comment removed for export] *)
        rewrite Z.eqb_refl in Hc. destruct Hc as (_ & Hbud & Hgap).
        destruct ga as [|l0 ga']; [destruct HE|]. destruct HE as (<- & Hlb & HE). cbn [gcost] in Hk. apply Forall_cons_iff in Hga as [_ Hga].
        pose proof (pcost_nonneg len ltac:(lia)). pose proof (gcost_nonneg ga' Hga).
        apply TS_event.
        -- eapply KI_acct_ok; [exact HK| lia].
        -- eapply nsafeA_grant; [exact HK| lia| exact Hlal| exact Hlb].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost. rewrite ML in Hpost.
           destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).   (* [comment removed for export] *)
           destruct (step_grant b G A k mo len z rsp HK ltac:(lia) Hlal Hlb Z1 Z2 Z3 Z4 Hd) as (HF & HL & HK').
           eexists z, _, _. split; [exact Hd|]. split; [exact HF|]. split; [exact HL|].
           eapply TS_EQ_mono.
           ++ eapply (IH z RP Post ga' ((z, len) :: G) (b - len) _ (k + pcost len) KCAP).
              ** apply HT. exact Hpost'.
              ** specialize (HE z). rewrite is_err_small in HE by (unfold TWO64; atop_facts; lia). exact HE.
              ** exact HK'.
              ** exact Hga.
              ** lia.
              ** exact HKC.
           ++ intros x RNG' A'' mo'' _ HP. apply (KPOST_mono_G RP Post G ((z, len) :: G) KCAP (Ok x)); [| exact HP]. intros g Hg. right; exact Hg.
      * (* [comment removed for export] *)
        destruct (Z.eqb_spec a 0) as [->|Hnz]. { destruct Hc as (Hc & _). exfalso. revert Hc. cbv. discriminate. }
        destruct Hc as (_ & Ha & Haal & Hce & Hrf & Hmc & _). rewrite ML in Hce, Hrf, Hmc.
        apply TS_event.
        -- eapply KI_acct_ok; [exact HK| lia].
        -- eapply nsafeA_fixed; [exact HK| left; reflexivity| lia| exact Hlal| exact Ha| exact Haal| exact Hce| exact Hrf| exact Hmc| intros _; exact Hlb].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. replace (a =? 0) with false in Hpost by (symmetry; apply Z.eqb_neq; exact Hnz).
           rewrite ML in Hpost. destruct Hpost as (-> & ->).
           destruct (step_commit b G A k mo a len rsp HK ltac:(lia) Hlal Hlb Ha Haal ltac:(exact Hce) HAP Hmc Hd) as (HF & HK').
           eexists a, _, A. split; [exact Hd|]. split; [exact HF|]. split; [apply alw_le_refl|].
           eapply (IH a RP Post ga G (b - len) A k KCAP).
           ++ apply HT. exact Hpost'.
           ++ specialize (HE a). rewrite is_err_small in HE by (unfold TWO64; atop_facts; lia). exact HE.
           ++ exact HK'.
           ++ exact Hga.
           ++ exact Hk.
           ++ exact HKC.
      * (* [comment removed for export] *)
        destruct (Z.eqb_spec a 0) as [->|Hnz]. { destruct Hc as (Hc & _). exfalso. revert Hc. cbv. discriminate. }
        destruct Hc as (_ & Ha & Haal & Hce & Hrf & Hmc & _). rewrite ML in Hce, Hrf, Hmc.
        apply TS_event.
        -- eapply KI_acct_ok; [exact HK| lia].
        -- eapply nsafeA_fixed; [exact HK| right; reflexivity| lia| exact Hlal| exact Ha| exact Haal| exact Hce| exact Hrf| exact Hmc| intros X; discriminate].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. replace (a =? 0) with false in Hpost by (symmetry; apply Z.eqb_neq; exact Hnz).
           rewrite ML in Hpost. destruct Hpost as (-> & ->).
           destruct (step_recommit b G A k mo a len rsp HK ltac:(lia) Hlal Ha Haal ltac:(exact Hce) HCG Hmc Hd) as (HF & HK').
           eexists a, _, A. split; [exact Hd|]. split; [exact HF|]. split; [apply alw_le_refl|].
           eapply (IH a RP Post ga G b A k KCAP).
           ++ apply HT. exact Hpost'.
           ++ exact (HE a).
           ++ exact HK'.
           ++ exact Hga.
           ++ exact Hk.
           ++ exact HKC.
    + (* [comment removed for export] *)
      destruct Hok as (Hlen & Ha & Haal & Hce & Hmh). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE.
      rewrite aembed_vis. cbn [aev_tree]. apply TS_event.
      * eapply KI_acct_ok; [exact HK| lia].
      * eapply nsafeA_munmap; eauto.
      * intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
        pose proof Hpost as Hpost'. cbn [apost] in Hpost. destruct Hpost as (-> & ->).
        destruct (step_munmap b G A k mo a len rsp HK Hlen Ha Hce Hmh) as (HF & HK').
        eexists 0, _, A. split; [exact Hd|]. split; [exact HF|]. split; [apply alw_le_refl|].
        eapply (IH 0 RP Post ga G b A k KCAP).
        -- apply HT. exact Hpost'.
        -- exact (HE 0).
        -- exact HK'.
        -- exact Hga.
        -- exact Hk.
        -- exact HKC.
    + (* [comment removed for export] *)
      destruct Hok as (Hlen & Ha & Haal & Hce & Hcan & Hmok). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE.
      rewrite aembed_vis. cbn [aev_tree]. apply TS_event.
      * eapply KI_acct_ok; [exact HK| lia].
      * eapply nsafeA_madvise; eauto.
      * intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
        pose proof Hpost as Hpost'. cbn [apost] in Hpost. destruct Hpost as (-> & ->).
        eexists 0, _, A. split; [exact Hd|]. split; [apply fstepS_id; exact I|]. split; [apply alw_le_refl|].
        eapply (IH 0 RP Post ga G b A k KCAP).
        -- apply HT. exact Hpost'.
        -- exact (HE 0).
        -- exact HK.
        -- exact Hga.
        -- exact Hk.
        -- exact HKC.
Qed.
End Ops.
End CANSEC1.

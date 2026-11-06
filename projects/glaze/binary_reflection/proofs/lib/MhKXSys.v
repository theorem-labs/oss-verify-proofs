(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhGap.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply u_Z2bv; lia. Qed.
Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.



Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.







(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.



(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.






(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.


Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.


(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GAPLO : Z := 2 ^ 46.
Lemma GAPLO_val : GAPLO = 70368744177664. Proof. reflexivity. Qed.

Definition cand (N : Z) (j : nat) : Z := GAPLO + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand. rewrite GAPLO_val. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : forall N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand N j) n p -> zconflict (cand N k) n p -> j = k.
Proof.
  intros N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* [comment removed for export] *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : forall (N n : Z) (l : list (word * word)) (js : list nat),
  0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  List.NoDup js -> (length l < length js)%nat ->
  exists j, In j js /\ forall p, In p l -> ~ zconflict (cand N j) n p.
Proof.
  intros N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.

Lemma region_free_of_noconflict : forall l (a n : Z),
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall p, In p l -> ~ zconflict a n p) ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
  cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  rewrite !u64_lit by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_na_gen : forall (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  GAPLO + C * (2 * N) + N <= CEIL0 -> CEIL0 <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na_pin m a n = true /\ GAPLO <= bv_unsigned a /\ bv_unsigned a + n <= CEIL0.
Proof.
  intros m N n C HN HNal Hn Hsz Hcnt Hband Htop.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand N j)).
  pose proof GAPLO_val as Hfv.
  assert (Hc : GAPLO <= cand N j <= GAPLO + C * (2 * N)) by (unfold cand; nia).
  unfold grant_ok_na_pin. rewrite !u64_lit by lia.
  assert (E1 : cand N j mod page_size = 0).
  { unfold cand. rewrite Hfv. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  fold l. rewrite (region_free_of_noconflict l (cand N j) n) by (first [lia | exact Hfree]).
  split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma grant_exists_gen : forall hint (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  GAPLO + C * (2 * N) + N <= CEIL0 -> CEIL0 <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true /\ GAPLO <= bv_unsigned a /\ bv_unsigned a + n <= CEIL0.
Proof.
  intros hint m N n C HN HNal Hn Hsz Hcnt Hband Htop Hlive.
  destruct (grant_exists_na_gen m N n C HN HNal Hn Hsz Hcnt Hband Htop) as (a & Ha & Hr).
  exists a. split; [| exact Hr]. unfold grant_ok. unfold grant_ok_na_pin in Ha.
  rewrite Ha. rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma band_250 : GAPLO + 250 * (2 * 2 ^ 35) + 2 ^ 35 <= CEIL0.
Proof. rewrite GAPLO_val. cbn. lia. Qed.

Lemma grant_exists_big : forall hint (m : Model) (n : Z),
  0 <= n <= 2 ^ 35 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 250 ->
  CEIL0 <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true /\ GAPLO <= bv_unsigned a /\ bv_unsigned a + n <= CEIL0.
Proof.
  intros hint m n Hn Hsz Hcnt Htop Hlive.
  apply (grant_exists_gen hint m (2 ^ 35) n 250); try assumption; try lia.
  - reflexivity.
  - exact band_250.
Qed.

Lemma grant_exists_na_big : forall (m : Model) (n : Z),
  0 <= n <= 2 ^ 35 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 250 ->
  CEIL0 <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na_pin m a n = true /\ GAPLO <= bv_unsigned a /\ bv_unsigned a + n <= CEIL0.
Proof.
  intros m n Hn Hsz Hcnt Htop.
  apply (grant_exists_na_gen m (2 ^ 35) n 250); try assumption; try lia.
  - reflexivity.
  - exact band_250.
Qed.

(* [comment removed for export] *)
Lemma alloc_top_ge_CEIL0 : forall {RN : run_ceil} (h : VmMaps), page_floor (alloc_top h) = CEIL -> CEIL0 <= alloc_top h.
Proof. intros RN h E. pose proof (@ceil_rng RN). pose proof (page_floor_le (alloc_top h)). lia. Qed.

Lemma grant_end_le_CEIL : forall {RN : run_ceil} (h : VmMaps) (a n : Z),
  page_floor (alloc_top h) = CEIL -> (a + n) mod 4096 = 0 -> a + n <= alloc_top h -> a + n <= CEIL.
Proof. intros RN h a n E Hal Hle. rewrite <- E. apply page_floor_bound; [exact Hal | exact Hle]. Qed.

End MhGap.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhBrkK.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys MhGap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition brk_grow_vm (h : VmMaps) (d : Z) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((vm_brk h, Z_to_bv 64 d) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
               (Z_to_bv 64 (bv_unsigned (vm_brk h) + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
Lemma brk_grow_ok_facts : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  0 < d -> 0 < bv_unsigned b -> bv_unsigned b + d < 2 ^ 64 ->
  bv_unsigned b mod page_size = 0 -> d mod page_size = 0 ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  bv_unsigned b + d <= alloc_top h /\
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true /\
  vm_backing_used m + d <= vm_limit h.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal Hg.
  pose proof (u64_range b) as Hbr.
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in Hg. fold h in Hg. fold b in Hg.
  rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned b)) Hb0) in Hg. rewrite u64_lit in Hg by lia.
  rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned b + d))) in Hg by lia. cbn [andb] in Hg.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hg by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in Hg
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned b + d))) in Hg by lia.
  apply andb_true_iff in Hg. destruct Hg as [Hg Hbud]. apply andb_true_iff in Hg. destruct Hg as [Hce Hrf].
  apply Z.leb_le in Hce. apply Z.leb_le in Hbud.
  replace (bv_unsigned b + d + page_size - bv_unsigned b) with (d + page_size) in Hrf by lia.
  rewrite (Z_to_bv_u_eq' b (bv_unsigned b) eq_refl) in Hrf.
  split; [exact Hce|]. split; [exact Hrf|].
  rewrite bv_sub_unsigned, u64_lit in Hbud by lia. rewrite bv_wrap_small in Hbud by (unfold bv_modulus; lia). lia.
Qed.

Section FPGen.
  Context {fx : FPState}.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Lemma P_brk_query : forall (P : config -> Prop) regs pc mem rom model w,
    kclosed segs P ->
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 214 -> getr regs 10 = Z_to_bv 64 0 ->
    P (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) ->
    P (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros P regs pc mem rom model w HP Hh Hl HF HE H17 H10 Hk.
    apply (P_brk segs P regs pc mem rom model w HP Hh Hl HF HE H17).
    intros r Hr. rewrite H10 in Hr.
    assert (Er : r = vm_brk (m_vmmaps model)).
    { unfold brk_resolution_ok, Mmap.brk_r_ok in Hr. cbv zeta in Hr.
      replace (w_is0 (Z_to_bv 64 0)) with true in Hr by reflexivity. cbn [orb] in Hr. apply bv_eqb_eq in Hr. exact Hr. }
    subst r. rewrite H10, brk_zeros_query, brk_unmaps_keep.
    rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta. rewrite adv_retU_epend. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma P_brk_grow : forall (P : config -> Prop) regs pc mem rom model w (d : Z),
    kclosed segs P ->
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 214 ->
    let h := m_vmmaps model in
    let b := vm_brk h in
    bv_unsigned b mod page_size = 0 -> d mod page_size = 0 -> 0 < d ->
    0 < bv_unsigned b -> bv_unsigned b + d < 2 ^ 64 ->
    bv_unsigned (vm_start_brk h) <= bv_unsigned b + d ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
    (* [comment removed for export] *)
    P (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) ->
    (* [comment removed for export] *)
    (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
     P (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                    (zfill b (Z_to_bv 64 d) mem) rom)
             (with_vmmaps (brk_grow_vm h d) model))) ->
    P (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros P regs pc mem rom model w d HP Hh Hl HF HE H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 KA KB.
    unfold b, h in *. clear b h. set (b := vm_brk (m_vmmaps model)) in *.
    pose proof (u64_range b) as Hbr.
    set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
    assert (Hureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; lia).
    apply (P_brk segs P regs pc mem rom model w HP Hh Hl HF HE H17).
    intros r Hr. rewrite H10 in Hr |- *.
    destruct (proj1 (brk_r_ok_grow_cases model req r ltac:(rewrite Hureq; lia) ltac:(rewrite Hureq; exact Hs) ltac:(rewrite Hureq; unfold b in *; lia)) Hr)
      as [-> | [-> Hg]].
    - (* [comment removed for export] *)
      rewrite brk_zeros_keep, brk_unmaps_keep, adv_retU_epend. unfold b. rewrite brk_model_keep. exact KA.
    - (* [comment removed for export] *)
      fold b.
      rewrite (brk_unmaps_grow req b) by (rewrite Hureq; lia).
      assert (Hreq0 : req <> Z_to_bv 64 0).
      { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
      rewrite (brk_zeros_grow req req b Hreq0 Hb0) by (rewrite Hureq; lia).
      rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
      rewrite Hureq, (page_round_up_Z_aligned (bv_unsigned b + d))
        by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      unfold brk_page_range. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      replace (bv_unsigned b + d - bv_unsigned b) with d by lia.
      rewrite (Z_to_bv_u_eq' b (bv_unsigned b) eq_refl).
      rewrite adv_zerosr_epend.
      unfold req, b. rewrite (brk_model_grow_eq model d Hd Hb0 Hnw Hbal Hdal).
      apply KB. exact Hg.
  Qed.
End FPGen.
End MhBrkK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhKX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section KX.
  Variable segs : list Segment.
  #[local] Notation kclosed := (kclosed segs).
  #[local] Notation kat := (kat segs).
  #[local] Notation kfam_laws := (kfam_laws segs).

  Definition kfx (F : kfam) (b : bool) : config -> Prop := if b then Kp F else Kw F.

  Variable F : kfam.
  Hypothesis HL : kfam_laws F.

  Lemma kfx_closed : forall b, kclosed (kfx F b).
  Proof. intros [|]; cbn; [exact (kl_p segs F HL) | exact (kl_w segs F HL)]. Qed.

  Lemma kfx_of_p : forall b c, Kp F c -> kfx F b c.
  Proof. intros [|] c H; cbn; [exact H | exact (kl_pw segs F HL c H)]. Qed.

  Lemma kw_of_kfx : forall b c, kfx F b c -> Kw F c.
  Proof. intros [|] c H; cbn in H; [exact (kl_pw segs F HL c H) | exact H]. Qed.

  Lemma kw_of_ok : forall c, Kok F c -> Kw F c.
  Proof. intros c H. exact (kl_okw segs F HL c H). Qed.

  (* [comment removed for export] *)
  Lemma kfx_mono : forall bi bo c, (bo = true -> bi = true) -> kfx F bi c -> kfx F bo c.
  Proof.
    intros [|] [|] c Hs H; cbn in *; try exact H.
    - exact (kl_pw segs F HL c H).
    - discriminate (Hs eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma kfx_kat : forall b c (Q : config -> Prop),
    kat c Q -> (forall c', Q c' -> kfx F b c') -> kfx F b c.
  Proof. intros b c Q Hk HQ. exact (Hk (kfx F b) (kfx_closed b) HQ). Qed.

  Lemma kf_kat : forall c (Q : config -> Prop),
    kat c Q -> (forall c', Q c' -> Kf F c') -> Kf F c.
  Proof. intros c Q Hk HQ. exact (Hk (Kf F) (kl_f segs F HL) HQ). Qed.

  Lemma kfx_msteps : forall b ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
    kfx F b (mkCfg ms' model) -> kfx F b (mkCfg ms model).
  Proof.
    intros b ms ms' model Hh Hl Hms Hk. apply (kfx_kat b _ (fun c => c = mkCfg ms' model)); [|intros c' ->; exact Hk].
    apply (kat_msteps segs ms ms' model _ Hh Hl Hms). apply kat_refl. reflexivity.
  Qed.

  Lemma kf_msteps : forall ms ms' model,
    m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
    Kf F (mkCfg ms' model) -> Kf F (mkCfg ms model).
  Proof.
    intros ms ms' model Hh Hl Hms Hk. apply (kf_kat _ (fun c => c = mkCfg ms' model)); [|intros c' ->; exact Hk].
    apply (kat_msteps segs ms ms' model _ Hh Hl Hms). apply kat_refl. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma kfx_node : forall b c (I : Type) (i0 : I) (nx : I -> config),
    node_ok segs c I (fun _ => []) nx -> (forall i, kfx F b (nx i)) -> kfx F b c.
  Proof. intros b c I i0 nx Hn Hs. exact (kfx_closed b c I i0 nx Hn Hs). Qed.

  (* [comment removed for export] *)
  Lemma kfx_of_w : forall b c, Kw F c -> kfx F b c.
  Proof. intros b c H. apply kfx_of_p. exact (kl_wp segs F HL c H). Qed.

  Lemma kfx_any : forall bi b c, kfx F bi c -> kfx F b c.
  Proof. intros bi b c H. apply kfx_of_w. exact (kw_of_kfx bi c H). Qed.

  (* [comment removed for export] *)
  Lemma kfx_grant_node : forall bi b c (I : Type) (i0 : I) (nx : I -> config),
    node_ok segs c I (fun _ => []) nx ->
    (forall g, kfx F bi (nx g)) ->
    kfx F b c.
  Proof.
    intros bi b c I i0 nx Hn Hg. apply (kfx_any bi b). exact (kfx_closed bi c I i0 nx Hn Hg).
  Qed.
End KX.

(* [comment removed for export] *)
Section TopLevel.
  Variable segs : list Segment.


End TopLevel.
End MhKX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhK MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys MhBrkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section KXS.
  Context {fx : FPState}.
  Variable segs : list Segment.
  Variable F : kfam.
  Hypothesis HL : kfam_laws segs F.
  #[local] Notation kfx := (kfx F).

  (* [comment removed for export] *)
  Lemma kfx_sys : forall b regs pc mem rom model w,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    kfx b (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
    kfx b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros b regs pc mem rom model w Hh Hl HF HE Hk.
    exact (P_sys segs (kfx b) regs pc mem rom model w (kfx_closed segs F HL b) Hh Hl HF HE Hk).
  Qed.

  (* [comment removed for export] *)
  Lemma kfx_mmap_na : forall bi b regs pc mem rom model w len,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 222 -> getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
    getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
    (exists a, grant_ok_na_pin model a (page_round_up_Z len) = true) ->
    Kf F (mmna_fail regs pc mem rom model ENOMEM) ->
    (forall a, grant_ok_na_pin model a (page_round_up_Z len) = true -> kfx bi (mmna_grant regs pc mem rom model len a)) ->
    kfx b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros bi b regs pc mem rom model w len Hh Hl HF HE H17 H11 Hlen H12 H13 H14 H15 [a0 Ha0] _ Hg.
    apply (kfx_sys b regs pc mem rom model w Hh Hl HF HE).
    apply (kfx_grant_node segs F HL bi b _ _ (exist _ a0 Ha0) _
             (node_mmap_na_grant segs regs pc mem rom model len Hh H17 H11 Hlen H12 H13 H14 H15
                (grant_na_pin_not_refusable model len a0 Ha0))).
    intros [a Ha]. exact (Hg a Ha).
  Qed.


  (* [comment removed for export] *)
  Lemma kfx_mprotect : forall bi b regs pc mem rom model w addr len,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 226 -> getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 ->
    getr regs 11 = Z_to_bv 64 len -> 0 < len -> bv_unsigned addr + page_round_up_Z len < two_pow_64 ->
    getr regs 12 = Z_to_bv 64 3 ->
    map_contains (vm_noaccess (m_vmmaps model)) addr (Z_to_bv 64 (page_round_up_Z len)) = true ->
    map_contains (vm_maps (m_vmmaps model)) addr (Z_to_bv 64 (page_round_up_Z len)) = true ->
    mprotect_budget_ok model addr (Z_to_bv 64 (page_round_up_Z len)) = true ->
    Kf F (mpr_fail regs pc mem rom model ENOMEM) ->
    kfx bi (mpr_ok regs pc mem rom model addr len) ->
    kfx b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros bi b regs pc mem rom model w addr len Hh Hl HF HE H17 H10 Hal H11 Hlen Hnw H12 Hna Hma Hb _ Hg.
    apply (kfx_sys b regs pc mem rom model w Hh Hl HF HE).
    apply (kfx_grant_node segs F HL bi b _ _ tt _
             (node_mprotect_grant segs regs pc mem rom model addr len Hh H17 H10 Hal H11 Hlen Hnw H12 Hna Hma Hb)).
    intros []. exact Hg.
  Qed.

  (* [comment removed for export] *)
  Lemma kfx_mmap_fixed : forall b regs pc mem rom model w addr len,
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 222 -> getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
    getr regs 11 = Z_to_bv 64 len -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model) ->
    getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 -> getr regs 15 = Z_to_bv 64 0 ->
    region_free (vm_reserved (m_vmmaps model)) addr (Z_to_bv 64 (page_round_up_Z len)) = true ->
    map_contains (vm_maps (m_vmmaps model)) addr (Z_to_bv 64 (page_round_up_Z len)) = true ->
    (forall e, In e mmap_errnos -> kfx b (mmfx_fail regs pc mem rom model e)) ->
    kfx b (mmfx_ok regs pc mem rom model addr len) ->
    (forall e, In e mmap_errnos -> kfx b (mmfx_gone regs pc mem rom model addr len e)) ->
    kfx b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros b regs pc mem rom model w addr len Hh Hl Hmat HF HE H17 H10 Hal Hpos H11 Hlen Htop H12 H13 H15 Hrf Hmc Kf Kok Kg.
    apply (kfx_sys b regs pc mem rom model w Hh Hl HF HE).
    apply (kfx_node segs F HL b _ _ tt _
             (node_mmap_fixed segs regs pc mem rom model addr len Hh Hl Hmat H17 H10 Hal Hpos H11 Hlen Htop H12 H13 H15 Hrf Hmc)).
    intros []. exact Kok.
  Qed.

  (* [comment removed for export] *)
  Lemma mmap_errno_is : forall e, In e mmap_errnos -> errno_ret e = Z_to_bv 64 (2 ^ 64 - 12).
  Proof. intros e He. rewrite (mmap_errnos_ENOMEM e He). apply bv_eq. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma kfx_brk_query : forall b regs pc mem rom model w,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 214 -> getr regs 10 = Z_to_bv 64 0 ->
    kfx b (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) ->
    kfx b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros b regs pc mem rom model w Hh Hl HF HE H17 H10 Hk.
    exact (P_brk_query segs (kfx b) regs pc mem rom model w (kfx_closed segs F HL b) Hh Hl HF HE H17 H10 Hk).
  Qed.

  (* [comment removed for export] *)
  Lemma kfx_brk_grow : forall b regs pc mem rom model w (d : Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 214 ->
    let h := m_vmmaps model in
    let bk := vm_brk h in
    bv_unsigned bk mod page_size = 0 -> d mod page_size = 0 -> 0 < d ->
    0 < bv_unsigned bk -> bv_unsigned bk + d < 2 ^ 64 ->
    bv_unsigned (vm_start_brk h) <= bv_unsigned bk + d ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned bk + d) ->
    kfx b (mkCfg (mkst (regupd regs 10 bk) (v_addi pc 4) mem rom) model) ->
    (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned bk + d)) (Z_to_bv 64 (bv_unsigned bk + d)) = true ->
     kfx b (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned bk + d))) (v_addi pc 4) (zfill bk (Z_to_bv 64 d) mem) rom)
                  (with_vmmaps (brk_grow_vm h d) model))) ->
    kfx b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros b regs pc mem rom model w d Hh Hl HF HE H17 h bk Hbal Hdal Hd Hb0 Hnw Hs H10 KA KB.
    exact (P_brk_grow segs (kfx b) regs pc mem rom model w d (kfx_closed segs F HL b) Hh Hl HF HE H17 Hbal Hdal Hd Hb0 Hnw Hs H10 KA KB).
  Qed.
End KXS.

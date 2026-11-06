(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhList.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= lia_nd.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition dllf (nx pv : Z -> Z) (l : list Z) : Prop :=
  forall k, 0 <= k < zlen l ->
    nx (znth l k) = znth l ((k + 1) mod zlen l) /\ pv (znth l k) = znth l ((k - 1) mod zlen l).

Lemma dll_dllf : forall st l, dll st l <-> dllf (fun x => mr_next (s_meta st x)) (fun x => mr_prev (s_meta st x)) l.
Proof. intros st l. unfold dll, dllf. tauto. Qed.

(* [comment removed for export] *)
Lemma zlen_app : forall l1 l2, zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_cons : forall a l, zlen (a :: l) = zlen l + 1.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : zlen [] = 0. Proof. reflexivity. Qed.
Lemma zlen_nonneg : forall l, 0 <= zlen l. Proof. intros; unfold zlen; lia. Qed.

Lemma znth_app_l : forall l1 l2 k, 0 <= k < zlen l1 -> znth (l1 ++ l2) k = znth l1 k.
Proof. intros l1 l2 k Hk. unfold znth, zlen in *. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma znth_app_r : forall l1 l2 k, zlen l1 <= k -> znth (l1 ++ l2) k = znth l2 (k - zlen l1).
Proof.
  intros l1 l2 k Hk. unfold znth, zlen in *. rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma znth_single0 : forall m, znth [m] 0 = m. Proof. reflexivity. Qed.
Lemma znth_cons0 : forall a l, znth (a :: l) 0 = a. Proof. reflexivity. Qed.
Lemma znth_cons_S : forall a l k, 0 < k -> znth (a :: l) k = znth l (k - 1).
Proof.
  intros a l k Hk. unfold znth. replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. reflexivity.
Qed.

Lemma In_znth : forall l x, In x l -> exists k, 0 <= k < zlen l /\ znth l k = x.
Proof.
  intros l x Hin. apply In_nth with (d := 0) in Hin. destruct Hin as (n & Hn & Hx).
  exists (Z.of_nat n). unfold znth, zlen. rewrite Nat2Z.id. split; [lia | exact Hx].
Qed.
Lemma znth_In : forall l k, 0 <= k < zlen l -> In (znth l k) l.
Proof. intros l k Hk. unfold znth, zlen in *. apply nth_In. lia. Qed.

Lemma NoDup_znth_inj : forall l j k, NoDup l -> 0 <= j < zlen l -> 0 <= k < zlen l -> znth l j = znth l k -> j = k.
Proof.
  intros l j k ND Hj Hk E. unfold znth, zlen in *.
  pose proof (proj1 (NoDup_nth l 0) ND (Z.to_nat j) (Z.to_nat k) ltac:(lia) ltac:(lia) E). lia.
Qed.

(* [comment removed for export] *)
Definition rot (k : nat) (l : list Z) : list Z := skipn k l ++ firstn k l.

Lemma zlen_rot : forall k l, zlen (rot k l) = zlen l.
Proof. intros k l. unfold rot. rewrite zlen_app. unfold zlen. rewrite length_skipn, length_firstn. lia. Qed.

Lemma znth_rot : forall k l j, (k <= length l)%nat -> 0 <= j < zlen l ->
  znth (rot k l) j = znth l ((j + Z.of_nat k) mod zlen l).
Proof.
  intros k l j Hk Hj. unfold rot.
  assert (Hs : zlen (skipn k l) = zlen l - Z.of_nat k) by (unfold zlen; rewrite length_skipn; lia).
  destruct (Z.lt_ge_cases j (zlen l - Z.of_nat k)) as [A|A].
  - rewrite znth_app_l by lia. rewrite Z.mod_small by lia.
    unfold znth. rewrite nth_skipn. f_equal. lia.
  - rewrite znth_app_r by lia. rewrite Hs.
    assert (E : (j + Z.of_nat k) mod zlen l = j + Z.of_nat k - zlen l).
    { unfold zlen in *. symmetry. apply Z.mod_unique with (q := 1); lia. }
    rewrite E.
    unfold znth. rewrite nth_firstn. unfold zlen in *.
    replace (PeanoNat.Nat.ltb (Z.to_nat (j - (Z.of_nat (length l) - Z.of_nat k))) k) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; lia).
    f_equal. lia.
Qed.

Lemma dllf_rot : forall nx pv k l, (k <= length l)%nat -> dllf nx pv l -> dllf nx pv (rot k l).
Proof.
  intros nx pv k l Hk D j Hj. rewrite zlen_rot in Hj |- *.
  assert (Hn : 0 < zlen l) by lia.
  pose proof (Z.mod_pos_bound (j + Z.of_nat k) (zlen l) Hn) as Hm.
  pose proof (Z.mod_pos_bound (j + 1) (zlen l) Hn) as Hm1.
  pose proof (Z.mod_pos_bound (j - 1) (zlen l) Hn) as Hm2.
  rewrite !znth_rot by lia.
  destruct (D ((j + Z.of_nat k) mod zlen l) Hm) as [N P]. rewrite N, P. split; f_equal.
  - rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_l. f_equal. lia.
  - rewrite Zminus_mod_idemp_l, Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma rot_perm_In : forall k l x, In x (rot k l) <-> In x l.
Proof. intros k l x. unfold rot. rewrite in_app_iff. rewrite <- (firstn_skipn k l) at 3. rewrite in_app_iff. tauto. Qed.

Lemma rot_perm : forall k l, Permutation l (rot k l).
Proof. intros k l. unfold rot. rewrite <- (firstn_skipn k l) at 1. apply Permutation_app_comm. Qed.

Lemma NoDup_rot : forall k l, NoDup l -> NoDup (rot k l).
Proof. intros k l ND. eapply Permutation_NoDup; [apply rot_perm | exact ND]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dllf_app_tail : forall (nx pv nx' pv' : Z -> Z) (l : list Z) (m : Z),
  dllf nx pv l -> 0 < zlen l -> NoDup l -> ~ In m l ->
  (forall k, 0 <= k < zlen l - 1 -> nx' (znth l k) = nx (znth l k)) ->
  nx' (znth l (zlen l - 1)) = m -> nx' m = znth l 0 ->
  (forall k, 0 < k < zlen l -> pv' (znth l k) = pv (znth l k)) ->
  pv' (znth l 0) = m -> pv' m = znth l (zlen l - 1) ->
  dllf nx' pv' (l ++ [m]).
Proof.
  intros nx pv nx' pv' l m D Hn ND Hm Hnx Hnt Hnm Hpv Hph Hpm j Hj.
  rewrite zlen_app in Hj |- *. change (zlen [m]) with 1 in *.
  set (n := zlen l) in *.
  assert (Z1 : forall k, 0 <= k < n -> znth (l ++ [m]) k = znth l k) by (intros; apply znth_app_l; lia).
  assert (Z2 : znth (l ++ [m]) n = m) by (rewrite znth_app_r by lia; subst n; rewrite Z.sub_diag; reflexivity).
  destruct (Z.lt_ge_cases j n) as [A|A].
  - rewrite Z1 by lia. destruct (D j ltac:(lia)) as [N P]. fold n in N, P. split.
    + destruct (Z.eq_dec j (n - 1)) as [->|B].
      * rewrite Hnt. replace ((n - 1 + 1) mod (n + 1)) with n by (symmetry; rewrite Z.mod_small; lia). symmetry. exact Z2.
      * rewrite Hnx by lia. rewrite N. rewrite (Z.mod_small (j+1) n) by lia. rewrite (Z.mod_small (j+1) (n+1)) by lia.
        symmetry. apply Z1. lia.
    + destruct (Z.eq_dec j 0) as [->|B].
      * rewrite Hph. replace ((0 - 1) mod (n + 1)) with n by (apply Z.mod_unique with (q := -1); lia). symmetry. exact Z2.
      * rewrite Hpv by lia. rewrite P. rewrite (Z.mod_small (j-1) n) by lia. rewrite (Z.mod_small (j-1) (n+1)) by lia.
        symmetry. apply Z1. lia.
  - assert (E : j = n) by lia. rewrite E, Z2. split.
    + rewrite Hnm. replace ((n + 1) mod (n + 1)) with 0 by (symmetry; apply Z.mod_same; lia). symmetry. apply Z1. lia.
    + rewrite Hpm. rewrite (Z.mod_small (n - 1) (n + 1)) by lia. symmetry. apply Z1. lia.
Qed.

(* [comment removed for export] *)
Lemma dllf_single : forall (nx pv : Z -> Z) m, nx m = m -> pv m = m -> dllf nx pv [m].
Proof.
  intros nx pv m Hn Hp j Hj. change (zlen [m]) with 1 in *. assert (E : j = 0) by lia. rewrite E.
  rewrite znth_single0. change ((0 + 1) mod 1) with 0. change ((0 - 1) mod 1) with 0. rewrite znth_single0. split; assumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dllf_remove_last : forall (nx pv nx' pv' : Z -> Z) (l : list Z) (m : Z),
  dllf nx pv (l ++ [m]) -> 0 < zlen l -> NoDup (l ++ [m]) ->
  (forall k, 0 <= k < zlen l - 1 -> nx' (znth l k) = nx (znth l k)) ->
  nx' (znth l (zlen l - 1)) = znth l 0 ->
  (forall k, 0 < k < zlen l -> pv' (znth l k) = pv (znth l k)) ->
  pv' (znth l 0) = znth l (zlen l - 1) ->
  dllf nx' pv' l.
Proof.
  intros nx pv nx' pv' l m D Hn ND Hnx Hnt Hpv Hph j Hj.
  set (n := zlen l) in *.
  assert (Z1 : forall k, 0 <= k < n -> znth (l ++ [m]) k = znth l k) by (intros; apply znth_app_l; lia).
  assert (Dj := D j). rewrite zlen_app in Dj. change (zlen [m]) with 1 in Dj. fold n in Dj.
  destruct (Dj ltac:(lia)) as [N P]. rewrite Z1 in N, P by lia.
  split.
  - destruct (Z.eq_dec j (n - 1)) as [->|B].
    + rewrite Hnt. replace ((n - 1 + 1) mod n) with 0 by (symmetry; replace (n - 1 + 1) with n by lia; apply Z.mod_same; lia). reflexivity.
    + rewrite Hnx by lia. rewrite N. rewrite (Z.mod_small (j+1) (n+1)) by lia. rewrite (Z.mod_small (j+1) n) by lia. apply Z1. lia.
  - destruct (Z.eq_dec j 0) as [->|B].
    + rewrite Hph. replace ((0 - 1) mod n) with (n - 1) by (apply Z.mod_unique with (q := -1); lia). reflexivity.
    + rewrite Hpv by lia. rewrite P. rewrite (Z.mod_small (j-1) (n+1)) by lia. rewrite (Z.mod_small (j-1) n) by lia. apply Z1. lia.
Qed.

(* [comment removed for export] *)
Lemma dllf_ends : forall nx pv l, dllf nx pv l -> 0 < zlen l ->
  nx (znth l (zlen l - 1)) = znth l 0 /\ pv (znth l 0) = znth l (zlen l - 1).
Proof.
  intros nx pv l D Hn. destruct (D (zlen l - 1) ltac:(lia)) as [N _]. destruct (D 0 ltac:(lia)) as [_ P].
  rewrite N, P. split; f_equal.
  - replace (zlen l - 1 + 1) with (zlen l) by lia. apply Z.mod_same. lia.
  - symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.

(* [comment removed for export] *)
Lemma dllf_links_In : forall nx pv l m, dllf nx pv l -> In m l -> In (nx m) l /\ In (pv m) l.
Proof.
  intros nx pv l m D Hin. destruct (In_znth _ _ Hin) as (k & Hk & <-).
  assert (Hn : 0 < zlen l) by lia.
  destruct (D k Hk) as [N P]. rewrite N, P.
  split; apply znth_In; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; lia.
Qed.

Lemma dllf_self_iff : forall nx pv l m, dllf nx pv l -> NoDup l -> In m l -> (nx m = m <-> zlen l = 1).
Proof.
  intros nx pv l m D ND Hin. destruct (In_znth _ _ Hin) as (k & Hk & <-).
  assert (Hn : 0 < zlen l) by lia.
  destruct (D k Hk) as [N _]. rewrite N. split.
  - intros E. apply NoDup_znth_inj in E; [ | exact ND | apply Z.mod_pos_bound; lia | lia ].
    destruct (Z.eq_dec (zlen l) 1) as [|B]; [assumption|]. exfalso.
    destruct (Z.lt_ge_cases (k + 1) (zlen l)) as [A|A].
    + rewrite Z.mod_small in E by lia. lia.
    + replace (k + 1) with (zlen l) in E by lia. rewrite Z.mod_same in E by lia. lia.
  - intros E. rewrite E. replace k with 0 by lia. reflexivity.
Qed.

Lemma dllf_prev_self_iff : forall nx pv l m, dllf nx pv l -> NoDup l -> In m l -> (pv m = m <-> zlen l = 1).
Proof.
  intros nx pv l m D ND Hin. destruct (In_znth _ _ Hin) as (k & Hk & <-).
  assert (Hn : 0 < zlen l) by lia.
  destruct (D k Hk) as [_ P]. rewrite P. split.
  - intros E. apply NoDup_znth_inj in E; [ | exact ND | apply Z.mod_pos_bound; lia | lia ].
    destruct (Z.eq_dec (zlen l) 1) as [|B]; [assumption|]. exfalso.
    destruct (Z.lt_ge_cases 0 k) as [A|A].
    + rewrite Z.mod_small in E by lia. lia.
    + replace k with 0 in E by lia.
      assert (E2 : (0 - 1) mod zlen l = zlen l - 1) by (symmetry; apply Z.mod_unique with (q := -1); lia). lia.
  - intros E. rewrite E. replace k with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma rot_split : forall (l1 l2 : list Z) m,
  rot (length l1 + 1) (l1 ++ m :: l2) = (l2 ++ l1) ++ [m].
Proof.
  intros l1 l2 m. unfold rot.
  replace (length l1 + 1)%nat with (length (l1 ++ [m]))%nat by (rewrite length_app; cbn; lia).
  replace (l1 ++ m :: l2) with ((l1 ++ [m]) ++ l2) by (rewrite <- app_assoc; reflexivity).
  rewrite skipn_app, skipn_all, PeanoNat.Nat.sub_diag. cbn [skipn].
  rewrite firstn_app, firstn_all, PeanoNat.Nat.sub_diag. cbn [firstn]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.

Lemma rot_app : forall (l1 l2 : list Z), rot (length l1) (l1 ++ l2) = l2 ++ l1.
Proof.
  intros l1 l2. unfold rot. rewrite skipn_app, skipn_all, PeanoNat.Nat.sub_diag. cbn [skipn].
  rewrite firstn_app, firstn_all, PeanoNat.Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dllf_remove : forall (nx pv nx' pv' : Z -> Z) (l1 l2 : list Z) (m : Z),
  dllf nx pv (l1 ++ m :: l2) -> NoDup (l1 ++ m :: l2) -> 0 < zlen (l1 ++ l2) ->
  (forall x, In x (l1 ++ l2) -> x <> pv m -> nx' x = nx x) ->
  nx' (pv m) = nx m ->
  (forall x, In x (l1 ++ l2) -> x <> nx m -> pv' x = pv x) ->
  pv' (nx m) = pv m ->
  dllf nx' pv' (l1 ++ l2).
Proof.
  intros nx pv nx' pv' l1 l2 m D ND Hn Hnx Hnt Hpv Hph.
  assert (Hlen : (length l1 + 1 <= length (l1 ++ m :: l2))%nat) by (rewrite length_app; cbn; lia).
  pose proof (dllf_rot nx pv (length l1 + 1) _ Hlen D) as D1. rewrite rot_split in D1.
  pose proof (NoDup_rot (length l1 + 1) _ ND) as ND1. rewrite rot_split in ND1.
  set (L := l2 ++ l1) in *.
  assert (HL : zlen L = zlen (l1 ++ l2)) by (subst L; rewrite !zlen_app; lia).
  assert (HinL : forall x, In x L <-> In x (l1 ++ l2)) by (intros x; subst L; rewrite !in_app_iff; tauto).
  set (n := zlen L) in *.
  (* [comment removed for export] *)
  assert (Dm := D1 n). rewrite zlen_app in Dm. change (zlen [m]) with 1 in Dm. fold n in Dm.
  destruct (Dm ltac:(lia)) as [Nm Pm].
  rewrite znth_app_r in Nm, Pm by lia. fold n in Nm, Pm. rewrite Z.sub_diag, znth_single0 in Nm, Pm.
  rewrite Z.mod_same in Nm by lia.
  replace ((n - 1) mod (n + 1)) with (n - 1) in Pm by (symmetry; apply Z.mod_small; lia).
  rewrite znth_app_l in Nm by lia. rewrite znth_app_l in Pm by lia.
  (* [comment removed for export] *)
  assert (D2 : dllf nx' pv' L).
  { eapply dllf_remove_last with (nx := nx) (pv := pv) (m := m); try assumption; try lia.
    - intros k Hk. apply Hnx. apply HinL. apply znth_In; lia.
      rewrite Pm. intros E. apply NoDup_znth_inj in E; try lia.
      eapply NoDup_app_remove_r. exact ND1.
    - fold n. rewrite <- Pm, Hnt, Nm. reflexivity.
    - intros k Hk. apply Hpv. apply HinL. apply znth_In; lia.
      rewrite Nm. intros E. apply NoDup_znth_inj in E; try lia.
      eapply NoDup_app_remove_r. exact ND1.
    - fold n. rewrite <- Nm, Hph, Pm. reflexivity. }
  pose proof (dllf_rot nx' pv' (length l2) L ltac:(subst L; rewrite length_app; lia) D2) as D3.
  subst L. rewrite rot_app in D3. exact D3.
Qed.

(* [comment removed for export] *)
Lemma dllf_remove_head : forall nx pv l2 m,
  dllf nx pv (m :: l2) -> 0 < zlen l2 -> nx m = znth l2 0.
Proof.
  intros nx pv l2 m D Hn. destruct (D 0) as [N _]. { rewrite zlen_cons. lia. }
  rewrite znth_cons0 in N. rewrite N. rewrite zlen_cons. rewrite Z.mod_small by lia.
  rewrite znth_cons_S by lia. f_equal.
Qed.


(* [comment removed for export] *)
Definition zremove (g : Z) (l : list Z) : list Z := List.filter (fun x => negb (Z.eqb x g)) l.

Lemma zremove_notin : forall g l, ~ In g l -> zremove g l = l.
Proof.
  intros g l H. unfold zremove. induction l as [|a l IH]; [reflexivity|]. cbn.
  destruct (Z.eqb_spec a g) as [->|Hne]; [exfalso; apply H; left; reflexivity|]. cbn. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma zremove_app : forall g l1 l2, zremove g (l1 ++ l2) = zremove g l1 ++ zremove g l2.
Proof. intros. unfold zremove. apply filter_app. Qed.

Lemma zremove_split : forall g l, List.NoDup l -> In g l ->
  exists l1 l2, l = l1 ++ g :: l2 /\ zremove g l = l1 ++ l2 /\ ~ In g l1 /\ ~ In g l2.
Proof.
  intros g l ND Hin. destruct (in_split g l Hin) as (l1 & l2 & E). subst l.
  pose proof (NoDup_remove_2 l1 l2 g ND) as NI. rewrite in_app_iff in NI.
  exists l1, l2. split; [reflexivity|]. split; [|tauto].
  rewrite zremove_app. cbn. rewrite Z.eqb_refl. cbn. fold (zremove g l2). rewrite !zremove_notin by tauto. reflexivity.
Qed.

Lemma zremove_In : forall g l x, In x (zremove g l) <-> In x l /\ x <> g.
Proof.
  intros g l x. unfold zremove. rewrite filter_In. destruct (Z.eqb_spec x g); cbn; split; try tauto. intros [_ H]; discriminate H.
Qed.

Lemma zremove_NoDup : forall g l, List.NoDup l -> List.NoDup (zremove g l).
Proof. intros. unfold zremove. apply NoDup_filter. assumption. Qed.

Lemma zlen_zremove : forall g l, List.NoDup l -> In g l -> zlen (zremove g l) = zlen l - 1.
Proof.
  intros g l ND Hin. destruct (zremove_split g l ND Hin) as (l1 & l2 & E & R & _). rewrite R, E.
  rewrite !zlen_app, zlen_cons. lia.
Qed.
End MhList.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhCover.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= lia_nd.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition childless (st : mst) (g : Z) : Prop :=
  forall k c o, 0 <= k <= g_lastidx st g -> s_slot st g k <> SHost c o.

Definition free_or_junk (st : mst) (g : Z) : Prop :=
  forall k, 0 <= k <= g_lastidx st g ->
    s_slot st g k = SAvail \/ s_slot st g k = SFreed \/ exists o, s_slot st g k = SJunk o.

Lemma free_or_junk_childless : forall st g, free_or_junk st g -> childless st g.
Proof. intros st g F k c o Hk E. destruct (F k Hk) as [A|[A|[o' A]]]; rewrite E in A; discriminate A. Qed.

Section Cover.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)).
  Hypothesis HWF : WF st L.

  Lemma glast_rng : forall g, 0 <= g_lastidx st g < 32.
  Proof using. intros g. unfold g_lastidx, w_lastidx. apply Z.mod_pos_bound. lia. Qed.

  Lemma span_cover : forall g a, is_group st g -> free_or_junk st g ->
    g_mem st g <= a -> (a < gspan st g - 1 \/ (a = gspan st g - 1 /\ endb_own st g)) ->
    gcell st g a \/ exists k, garbage st g k a.
  Proof using HWF L RN.
    intros g a Hg FJ Hlo Hhi.
    pose proof (wG_each st L (WF_groups st L HWF) g Hg) as WG.
    pose proof (wg_stride st L g WG) as [S16 Smod]. pose proof (glast_rng g) as GL.
    set (G := g_mem st g) in *. set (S := g_stride st g) in *.
    assert (Ess : forall k, g_slot_start st g k = G + 16 + S * k) by (intros; unfold g_slot_start, UNIT; subst G S; lia).
    assert (Ese : forall k, g_slot_end st g k = G + 16 + S * k + S - 4) by (intros; unfold g_slot_end, IB; rewrite Ess; lia).
    assert (Esp : gspan st g = G + 16 + S * (g_lastidx st g + 1) - 3).
    { unfold gspan, g_span_end, g_cnt, UNIT, IB. subst G S. lia. }
    destruct (Z.lt_ge_cases a (G + 12)) as [Hhdr|Hge].
    { left. unfold gcell. left. subst G. lia. }
    set (t := a - (G + 12)). set (k := t / S). set (r := t mod S).
    assert (Hr : 0 <= r < S) by (subst r; apply Z.mod_pos_bound; lia).
    assert (Ea : a = G + 12 + S * k + r) by (subst k r t; pose proof (Z.div_mod (a - (G + 12)) S ltac:(lia)); lia).
    assert (Hk0 : 0 <= k) by (subst k; apply Z.div_pos; lia).
    assert (Hkc : k <= g_lastidx st g + 1).
    { subst k. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. destruct Hhi as [Hhi|[Hhi _]]; nia. }
    destruct (Z.eq_dec r 0) as [Hr0|Hr0].
    - (* [comment removed for export] *)
      left. unfold gcell. right. left. exists k. rewrite Ess. unfold g_cnt. split; [lia|]. split; [lia|].
      destruct (Z.eq_dec k (g_lastidx st g + 1)) as [Ek|Nk]; [|left; lia].
      right. destruct Hhi as [Hhi|[_ E]]; [exfalso; nia | exact E].
    - assert (Hklt : k <= g_lastidx st g) by (destruct Hhi as [Hhi|[Hhi _]]; nia).
      destruct (FJ k ltac:(lia)) as [A|[A|[o A]]].
      + right. exists k. unfold garbage. rewrite A, Ess, Ese. split; [lia | nia].
      + right. exists k. unfold garbage. rewrite A, Ess, Ese. split; [lia | nia].
      + (* [comment removed for export] *)
        destruct (Z.lt_ge_cases a (G + 16 + S * k + 16 * o - 4)) as [B|B].
        * right. exists k. unfold garbage. rewrite A, Ess, Ese. split; [lia|]. left. nia.
        * destruct (Z.lt_ge_cases a (G + 16 + S * k + 16 * o)) as [C|C].
          -- left. unfold gcell. right. right. left. exists k, (g_slot_start st g k + 16 * o).
             unfold slot_ptr. rewrite A, Ess. repeat split; try lia.
          -- right. exists k. unfold garbage. rewrite A, Ess, Ese. split; [lia|]. right. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma span_in_host : forall x hm j o, is_group st x -> s_kind st x = GNest hm j o ->
    is_group st hm /\ hm <> x /\ g_mem st hm + 16 <= g_mem st x /\ gspan st x <= gspan st hm.
  Proof using HWF L RN.
    intros x hm j o Hx K.
    pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    pose proof (wg_kind st L x WG) as KD. rewrite K in KD.
    destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    pose proof (ge_span st (WF_geom st L HWF) x Hx) as SP. rewrite K in SP. destruct SP as [SP1 SP2].
    pose proof (wG_each st L (WF_groups st L HWF) hm K2) as WH.
    pose proof (wg_stride st L hm WH) as [S16 _]. pose proof (glast_rng hm).
    split; [exact K2|]. split; [exact K3|].
    assert (0 <= g_stride st hm * j) by nia.
    assert (g_stride st hm * (j + 1) <= g_stride st hm * (g_lastidx st hm + 1)) by nia.
    unfold gspan, g_span_end, g_slot_end, g_slot_start, g_cnt, UNIT, IB in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma top_range_free : forall g, is_group st g -> s_kind st g = GTop -> childless st g ->
    forall fuel x, nest_depth_le st fuel x -> is_group st x -> x <> g ->
    gspan st x <= g_mem st g \/ g_map_end st g <= g_mem st x.
  Proof using HWF L RN.
    intros g Hg Kg CH. induction fuel as [|f IH]; intros x D Hx Hne.
    - cbn in D. destruct (s_kind st x) as [|hm j o] eqn:Kx; [|destruct D].
      (* [comment removed for export] *)
      pose proof (wg_kind st L x (wG_each st L (WF_groups st L HWF) x Hx)) as KX. rewrite Kx in KX.
      pose proof (wg_kind st L g (wG_each st L (WF_groups st L HWF) g Hg)) as KG. rewrite Kg in KG.
      destruct KX as (X1 & X2 & X3 & X4). destruct KG as (G1 & G2 & G3 & G4).
      pose proof (ge_span st (WF_geom st L HWF) x Hx) as SPx. rewrite Kx in SPx.
      pose proof (wr_disj st (WF_regions st L HWF) _ _ X2 G2 ltac:(intros E; injection E; intros; exact (Hne ltac:(assumption)))) as DJ.
      cbn [rg_base rg_len] in DJ. unfold g_map_end. lia.
    - cbn in D. destruct (s_kind st x) as [|hm j o] eqn:Kx.
      + apply (IH x); [destruct f; cbn; rewrite Kx; exact I | exact Hx | exact Hne].
      + destruct (span_in_host x hm j o Hx Kx) as (Hh & Hhx & LO & HI).
        assert (Hhg : hm <> g).
        { intros ->. pose proof (wg_kind st L x (wG_each st L (WF_groups st L HWF) x Hx)) as KX. rewrite Kx in KX.
          destruct KX as (_ & _ & _ & K4 & _ & K6 & _). exact (CH j x o K4 K6). }
        destruct (IH hm D Hh Hhg) as [A|A]; [left; lia | right; lia].
  Qed.

  Lemma top_range_free8 : forall g x, is_group st g -> s_kind st g = GTop -> childless st g ->
    is_group st x -> x <> g -> gspan st x <= g_mem st g \/ g_map_end st g <= g_mem st x.
  Proof using HWF L RN.
    intros g x Hg Kg CH Hx Hne. apply (top_range_free g Hg Kg CH 8%nat); [|exact Hx|exact Hne].
    exact (wg_depth st L x (wG_each st L (WF_groups st L HWF) x Hx)).
  Qed.
End Cover.
End MhCover.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhExt.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition slot_sim (a b : slot_st) : Prop := a = b \/ ((a = SAvail \/ a = SFreed) /\ (b = SAvail \/ b = SFreed)).
Lemma slot_sim_refl : forall a, slot_sim a a. Proof. intros; left; reflexivity. Qed.


Record same_layout (st1 st2 : mst) : Prop := SL {
  sl_areas : s_areas st2 = s_areas st1;
  sl_groups : s_groups st2 = s_groups st1;
  sl_kind : forall x, s_kind st2 x = s_kind st1 x;
  sl_slot : forall x k, slot_sim (s_slot st1 x k) (s_slot st2 x k);
  sl_mem : forall x, is_group st1 x -> mr_mem (s_meta st2 x) = mr_mem (s_meta st1 x);
  sl_W : forall x, is_group st1 x -> mr_W (s_meta st2 x) = mr_W (s_meta st1 x);
  sl_regions : s_regions st2 = s_regions st1;
  sl_brk : s_brk st2 = s_brk st1
}.

Section Ext.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st1 st2 : mst) (L : list (Z * Z)).
  Hypothesis S : same_layout st1 st2.
  Hypothesis HWF1 : WF st1 L.

  Lemma x_host_group : forall y hm j o, is_group st1 y -> s_kind st1 y = GNest hm j o -> is_group st1 hm.
  Proof.
    intros y hm j o Hy K. pose proof (wg_kind st1 L y (wG_each st1 L (WF_groups st1 L HWF1) y Hy)) as KD.
    rewrite K in KD. exact (proj1 (proj2 KD)).
  Qed.
  Lemma x_child_group : forall x k c o, is_group st1 x -> 0 <= k <= g_lastidx st1 x -> s_slot st1 x k = SHost c o -> is_group st1 c.
  Proof.
    intros x k c o Hx Hk E. pose proof (wg_slots st1 L x (wG_each st1 L (WF_groups st1 L HWF1) x Hx) k Hk) as SW.
    rewrite E in SW. exact (proj1 (proj2 SW)).
  Qed.
  Lemma x_region_group : forall b len m, In (RG b len (RGroup m)) (s_regions st1) -> is_group st1 m.
  Proof. intros b len m Hin. exact (proj1 (wG_regions st1 L (WF_groups st1 L HWF1) b len m Hin)). Qed.

  Lemma x_gW : forall x, is_group st1 x -> g_W st2 x = g_W st1 x. Proof. intros; unfold g_W; apply (sl_W _ _ S); assumption. Qed.
  Lemma x_gmem : forall x, is_group st1 x -> g_mem st2 x = g_mem st1 x. Proof. intros; unfold g_mem; apply (sl_mem _ _ S); assumption. Qed.
  Lemma x_glast : forall x, is_group st1 x -> g_lastidx st2 x = g_lastidx st1 x. Proof. intros; unfold g_lastidx; rewrite x_gW by assumption; reflexivity. Qed.
  Lemma x_gcnt : forall x, is_group st1 x -> g_cnt st2 x = g_cnt st1 x. Proof. intros; unfold g_cnt; rewrite x_glast by assumption; reflexivity. Qed.
  Lemma x_gsc : forall x, is_group st1 x -> g_sc st2 x = g_sc st1 x. Proof. intros; unfold g_sc; rewrite x_gW by assumption; reflexivity. Qed.
  Lemma x_gml : forall x, is_group st1 x -> g_maplen st2 x = g_maplen st1 x. Proof. intros; unfold g_maplen; rewrite x_gW by assumption; reflexivity. Qed.
  Lemma x_gstride : forall x, is_group st1 x -> g_stride st2 x = g_stride st1 x.
  Proof. intros; unfold g_stride; rewrite x_gml, x_glast, x_gsc by assumption; reflexivity. Qed.
  Lemma x_gss : forall x k, is_group st1 x -> g_slot_start st2 x k = g_slot_start st1 x k.
  Proof. intros; unfold g_slot_start; rewrite x_gmem, x_gstride by assumption; reflexivity. Qed.
  Lemma x_gse : forall x k, is_group st1 x -> g_slot_end st2 x k = g_slot_end st1 x k.
  Proof. intros; unfold g_slot_end; rewrite x_gss, x_gstride by assumption; reflexivity. Qed.
  Lemma x_gspan : forall x, is_group st1 x -> gspan st2 x = gspan st1 x.
  Proof. intros; unfold gspan, g_span_end; rewrite x_gmem, x_gstride, x_gcnt by assumption; reflexivity. Qed.
  Lemma x_inband : forall x q, is_group st1 x -> inband st2 x q = inband st1 x q.
  Proof. intros; unfold inband; rewrite x_gmem by assumption; reflexivity. Qed.
  Lemma x_ptr_ok : forall x k q, is_group st1 x -> (ptr_ok st2 x k q <-> ptr_ok st1 x k q).
  Proof. intros; unfold ptr_ok; rewrite x_gmem, x_inband, x_gsc, x_gml by assumption; tauto. Qed.
  Lemma x_endb : forall x, is_group st1 x -> (endb_own st2 x <-> endb_own st1 x).
  Proof.
    intros x Hx; unfold endb_own; rewrite (sl_kind _ _ S), x_gspan by assumption.
    destruct (s_kind st1 x) as [|hm j o] eqn:K; [tauto|]. rewrite x_gse by (eapply x_host_group; eassumption). tauto.
  Qed.
  Lemma x_is_group : forall x, is_group st2 x <-> is_group st1 x. Proof. intros; unfold is_group; rewrite (sl_groups _ _ S); tauto. Qed.
  Lemma x_slot_cases : forall x k, s_slot st2 x k = s_slot st1 x k \/
    ((s_slot st1 x k = SAvail \/ s_slot st1 x k = SFreed) /\ (s_slot st2 x k = SAvail \/ s_slot st2 x k = SFreed)).
  Proof. intros x k. destruct (sl_slot _ _ S x k) as [E|E]; [left; symmetry; exact E | right; exact E]. Qed.
  Lemma x_slot_ptr : forall x k, is_group st1 x -> slot_ptr st2 x k = slot_ptr st1 x k.
  Proof.
    intros x k Hx; unfold slot_ptr. rewrite x_gss by assumption.
    destruct (x_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; reflexivity.
  Qed.
  Lemma x_user : forall x k q n o r, s_slot st2 x k = SUser q n o r <-> s_slot st1 x k = SUser q n o r.
  Proof.
    intros x k q n o r. destruct (x_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; split; intro H; try exact H; discriminate.
  Qed.

  Lemma x_junk : forall x k o, s_slot st2 x k = SJunk o <-> s_slot st1 x k = SJunk o.
  Proof.
    intros x k o. destruct (x_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; split; intro H; try exact H; discriminate.
  Qed.
  Lemma x_gcell : forall x a, is_group st1 x -> (gcell st2 x a <-> gcell st1 x a).
  Proof.
    intros x a Hx. unfold gcell. rewrite x_gmem, x_gcnt, x_glast by assumption.
    assert (E2 : forall k, (k < g_cnt st1 x \/ endb_own st2 x) <-> (k < g_cnt st1 x \/ endb_own st1 x)) by (intros; rewrite x_endb by assumption; tauto).
    split; intros [G|[G|[G|G]]].
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite x_gss in B by assumption. rewrite <- E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite x_slot_ptr in B by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite x_user in B. rewrite x_gse in C by assumption. tauto.
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite x_gss by assumption. rewrite E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite x_slot_ptr by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite x_user, x_gse by assumption. tauto.
  Qed.
  Lemma x_appb : forall a, appb st2 a <-> appb st1 a.
  Proof.
    intros a. unfold appb. split; intros (x & k & q & n & o & r & A & B & C & D).
    - apply x_is_group in A. exists x, k, q, n, o, r. rewrite x_glast in B by exact A. rewrite x_user in C. tauto.
    - exists x, k, q, n, o, r. rewrite x_glast, x_user by exact A. split; [apply x_is_group; exact A | tauto].
  Qed.
  Lemma x_garbage : forall x k a, is_group st1 x -> (garbage st2 x k a <-> garbage st1 x k a).
  Proof.
    intros x k a Hx. unfold garbage. rewrite x_glast, x_gss, x_gse by assumption.
    destruct (x_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; [|tauto..].
    destruct (s_slot st1 x k) as [| |q n o r|c o|o] eqn:Sk; try tauto.
    destruct (Z.le_gt_cases 0 k) as [Hk0|Hk0]; [|split; intros [Hk _]; lia].
    destruct (Z.le_gt_cases k (g_lastidx st1 x)) as [Hk1|Hk1]; [|split; intros [Hk _]; lia].
    rewrite x_gspan by (eapply (x_child_group x k); [exact Hx | lia | exact Sk]). tauto.
  Qed.
  Lemma x_areab : forall a, areab st2 a <-> areab st1 a.
  Proof. intros; unfold areab; rewrite (sl_areas _ _ S); tauto. Qed.

  Lemma x_depth : forall f x, nest_depth_le st2 f x <-> nest_depth_le st1 f x.
  Proof.
    induction f as [|f IH]; intros x; cbn; rewrite (sl_kind _ _ S); destruct (s_kind st1 x) as [|hm j o]; try tauto. apply IH.
  Qed.

  Lemma x_slot_wf_same : forall x k sl, is_group st1 x -> slot_wf st1 L x k sl -> slot_wf st2 L x k sl.
  Proof.
    intros x k sl Hx SW. destruct sl as [| |q n o r|c o|o]; cbn [slot_wf] in *; try exact I.
    - rewrite x_gss, x_gstride by assumption. destruct SW as (A & B & C & D & E & F & G). repeat (split; [assumption|]).
      split; [apply x_ptr_ok; [exact Hx | exact F] | exact G].
    - rewrite x_gss, (sl_kind _ _ S) by assumption. destruct SW as (A & B & C & D & E). repeat (split; [first [assumption | apply x_is_group; assumption]|]).
      apply x_ptr_ok; [exact Hx | exact E].
    - rewrite x_gss, x_gstride by assumption. destruct SW as (A & B & C). split; [exact A|]. split; [exact B|]. apply x_ptr_ok; [exact Hx | exact C].
  Qed.
  Lemma x_slot_wf : forall x k, is_group st1 x -> slot_wf st1 L x k (s_slot st1 x k) -> slot_wf st2 L x k (s_slot st2 x k).
  Proof.
    intros x k Hx SW. destruct (x_slot_cases x k) as [E|[_ [E2|E2]]]; rewrite ?E, ?E2; [apply x_slot_wf_same; [exact Hx | exact SW] | exact I | exact I].
  Qed.

  Lemma wf_areas_ext : wf_areas st1 -> wf_areas st2.
  Proof. intros [A B C D]. constructor; rewrite ?(sl_areas _ _ S), ?(sl_regions _ _ S), ?(sl_brk _ _ S); assumption. Qed.

  Lemma wf_geom_ext : wf_geom st1 -> wf_geom st2.
  Proof.
    intros [INR CELLS AREA APC APA APD GC GA GAR SPAN]. constructor; rewrite ?(sl_regions _ _ S).
    - intros x Hx. apply x_is_group in Hx. rewrite x_gmem, x_gspan by exact Hx. apply INR. exact Hx.
    - intros m1 m2 a H1 H2 Hne G1 G2. apply x_is_group in H1. apply x_is_group in H2.
      apply x_gcell in G1; [|exact H1]. apply x_gcell in G2; [|exact H2]. eauto.
    - intros x a Hx R Ar. apply x_is_group in Hx. rewrite x_gmem, x_gspan in R by exact Hx. apply x_areab in Ar. eauto.
    - intros x a Hx G Ap. apply x_is_group in Hx. apply x_gcell in G; [|exact Hx]. apply x_appb in Ap. eauto.
    - intros a Ap Ar. apply x_appb in Ap. apply x_areab in Ar. eauto.
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply x_is_group in H1. apply x_is_group in H2. rewrite x_glast in Hk1 by exact H1. rewrite x_glast in Hk2 by exact H2.
      rewrite x_user in S1, S2. eauto.
    - intros x k a x2 Hx G H2 C. apply x_is_group in Hx. apply x_is_group in H2. apply x_garbage in G; [|exact Hx]. apply x_gcell in C; [|exact H2]. eauto.
    - intros x k a Hx G Ap. apply x_is_group in Hx. apply x_garbage in G; [|exact Hx]. apply x_appb in Ap. eauto.
    - intros x k a Hx G Ar. apply x_is_group in Hx. apply x_garbage in G; [|exact Hx]. apply x_areab in Ar. eauto.
    - intros x Hx. apply x_is_group in Hx. rewrite (sl_kind _ _ S), x_gspan, x_gmem, x_gml by exact Hx.
      pose proof (SPAN x Hx) as SP. destruct (s_kind st1 x) as [|hm j o] eqn:K; [exact SP|].
      pose proof (x_host_group x hm j o Hx K) as Hh. rewrite x_gss, x_gse by exact Hh. exact SP.
  Qed.

  Lemma wf_live_ext : wf_live st1 L -> wf_live st2 L.
  Proof.
    intros [IN ND FUN LEN]. constructor.
    - intros p n Hin. destruct (IN p n Hin) as (x & k & o & r & A & B & C). exists x, k, o, r.
      rewrite x_glast, x_user by exact A. split; [apply x_is_group; exact A | tauto].
    - exact ND.
    - intros m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      apply x_is_group in H1. apply x_is_group in H2. rewrite x_glast in Hk1 by exact H1. rewrite x_glast in Hk2 by exact H2.
      rewrite x_user in S1, S2. eauto.
    - exact LEN.
  Qed.

  Lemma wf_img_ext : wf_img st1 -> wf_img st2.
  Proof.
    intros [A R]. constructor; rewrite ?(sl_regions _ _ S), ?(sl_areas _ _ S); assumption.
  Qed.

  Lemma wf_regions_ext : c_shift (s_ctx st2) = c_shift (s_ctx st1) -> wf_regions st1 -> wf_regions st2.
  Proof.
    intros Hsh [RNG DISJ ND LEN GB G63 MT MC BRK BL]. constructor; rewrite ?(sl_regions _ _ S), ?(sl_brk _ _ S), ?(sl_areas _ _ S), ?Hsh; try assumption.
    - intros b len x Hin. rewrite x_gsc by (eapply x_region_group; exact Hin). eauto.
    - intros b len x Hin H63. rewrite x_gsc in H63 by (eapply x_region_group; exact Hin).
      destruct (G63 b len x Hin H63) as [(p & n & o & r & A & B)|(o & A)].
      + left. exists p, n, o, r. rewrite x_user. tauto.
      + right. exists o. rewrite x_junk. exact A.
  Qed.
End Ext.
End MhExt.
Module MhRepT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen MhList.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mr_set_links (r : meta_rec) (pv nx : Z) : meta_rec :=
  MR pv nx (mr_mem r) (mr_avail r) (mr_freed r) (mr_W r).

Definition cx_set_active (cx : ctx_rec) (f : Z -> Z) : ctx_rec :=
  CX (c_secret cx) (c_mmap_ctr cx) (c_free_head cx) (c_avail_meta cx) (c_avail_cnt cx)
     (c_area_cnt cx) (c_shift cx) (c_area_head cx) (c_area_tail cx) (c_cursor cx)
     f (c_usage cx) (c_unmap_seq cx) (c_bounces cx) (c_seq cx) (c_brk cx).

Definition cx_set_fhead (cx : ctx_rec) (h : Z) : ctx_rec :=
  CX (c_secret cx) (c_mmap_ctr cx) h (c_avail_meta cx) (c_avail_cnt cx)
     (c_area_cnt cx) (c_shift cx) (c_area_head cx) (c_area_tail cx) (c_cursor cx)
     (c_active cx) (c_usage cx) (c_unmap_seq cx) (c_bounces cx) (c_seq cx) (c_brk cx).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma head_of_znth : forall l, l <> [] -> head_of l = znth l 0.
Proof. intros [|a l] H; [congruence | reflexivity]. Qed.

Lemma head_of_app_nonnil : forall l m, l <> [] -> head_of (l ++ [m]) = head_of l.
Proof. intros [|a l] m H; [congruence | reflexivity]. Qed.


Lemma head_of_In : forall l, l <> [] -> In (head_of l) l.
Proof. intros [|a l] H; [congruence | left; reflexivity]. Qed.

Lemma zlen_pos : forall l : list Z, l <> [] -> 0 < zlen l.
Proof. intros [|a l] H; [congruence|]. unfold zlen. cbn [length]. lia. Qed.

Lemma last_In : forall l : list Z, l <> [] -> In (znth l (zlen l - 1)) l.
Proof. intros l H. apply znth_In. pose proof (zlen_pos l H). lia. Qed.

Lemma dll_ext : forall st st' l,
  (forall x, In x l -> mr_next (s_meta st' x) = mr_next (s_meta st x) /\ mr_prev (s_meta st' x) = mr_prev (s_meta st x)) ->
  dll st l -> dll st' l.
Proof.
  intros st st' l E D k Hk. destruct (D k Hk) as [N P].
  destruct (E (znth l k) (znth_In l k Hk)) as [EN EP]. rewrite EN, EP. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WFFacts.
  Context {RN : mh_run}.
  Variables (st : mst) (L : list (Z * Z)).
  Hypothesis HWF : WF st L.

  Lemma alist_member : forall sc x, In x (s_alist st sc) ->
    0 <= sc < 48 /\ is_group st x /\ g_sc st x = sc /\ metaU st x /\ listed st x.
  Proof.
    intros sc x Hin. destruct (wl_aU st (WF_lists st L HWF) sc x Hin) as (A & B & C).
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split.
    - exact (wg_U st L x (wG_each st L (WF_groups st L HWF) x B)).
    - right. exists sc. split; assumption.
  Qed.

  Lemma metaU_rng : forall x, metaU st x -> HEAPLO + 24 <= x /\ x + 40 <= CEIL /\ x mod 8 = 0.
  Proof.
    intros x U. destruct (metaU_area st L HWF x U) as (ar & k & Har & Hk & Hx & Hal & Hlo & Hhi & H1 & H2 & _).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    unfold meta_addr, AREA_HDR, META_SZ in Hx. subst x. repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Lemma metaU_sep : forall x y, metaU st x -> metaU st y -> x <> y -> x + 40 <= y \/ y + 40 <= x.
  Proof.
    intros x y Ux Uy Hne.
    destruct (metaU_area st L HWF x Ux) as (ar & k & Har & Hk & Hx & Hal & Hlo & Hhi & H1 & H2 & _).
    destruct (metaU_area st L HWF y Uy) as (ar' & k' & Har' & Hk' & Hy & Hal' & Hlo' & Hhi' & H1' & H2' & _).
    unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *.
    destruct (Z.eq_dec ar ar') as [<-|Hna].
    - assert (k <> k') by (intros <-; apply Hne; lia). subst x y. nia.
    - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (ar + 4096 <= ar' \/ ar' + 4096 <= ar) by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      lia.
  Qed.

  (* [comment removed for export] *)
  Lemma metaU_not_hdr : forall x ar a, metaU st x -> In ar (s_areas st) -> x <= a < x + 40 -> ar <= a < ar + 24 -> False.
  Proof.
    intros x ar a Ux Har Hx Ha.
    destruct (metaU_area st L HWF x Ux) as (ar0 & k & Har0 & Hk & Hx0 & Hal0 & Hlo0 & Hhi0 & H1 & H2 & _).
    destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
    unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *.
    destruct (Z.eq_dec ar ar0) as [->|Hna]; [lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (ar + 4096 <= ar0 \/ ar0 + 4096 <= ar) by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma metaU_owner : forall x ar k a, metaU st x -> In ar (s_areas st) -> 0 <= k < NSLOTS ->
    x <= a < x + 40 -> meta_addr ar k <= a < meta_addr ar k + 40 -> x = meta_addr ar k.
  Proof.
    intros x ar k a Ux Har Hk Hx Ha.
    destruct (Z.eq_dec x (meta_addr ar k)) as [E|NE]; [exact E|]. exfalso.
    assert (Uy : metaU st (meta_addr ar k)) by (exists ar, k; repeat split; try assumption; lia).
    destruct (metaU_sep x (meta_addr ar k) Ux Uy NE); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gcell_not_meta : forall g x a, is_group st g -> gcell st g a -> metaU st x -> x <= a < x + 40 -> False.
  Proof.
    intros g x a Hg G Ux Hx.
    destruct (metaU_area st L HWF x Ux) as (ar & k & Har & Hk & Hx0 & Hal & Hlo & Hhi & H1 & H2 & _).
    apply (ge_area st (WF_geom st L HWF) g a Hg).
    - exact (gcell_in_span st L HWF g a Hg G).
    - exists ar. split; [exact Har | lia].
  Qed.

  Lemma group_metaU : forall g, is_group st g -> metaU st g.
  Proof. intros g Hg. exact (wg_U st L g (wG_each st L (WF_groups st L HWF) g Hg)). Qed.

  Lemma group_pos : forall g, is_group st g -> HEAPLO + 24 <= g.
  Proof. intros g Hg. destruct (metaU_rng g (group_metaU g Hg)). lia. Qed.
End WFFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RepT.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st st' : mst) (L : list (Z * Z)) (M M' : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  (* [comment removed for export] *)
  Definition dfoot (a : Z) : Prop :=
    (A_ERRNO <= a < A_ERRNO + 4) \/ (CTX <= a < CTX_END) \/ areab st a \/
    (exists x, is_group st x /\ s_kind st x = GTop /\ g_mem st x <= a < g_mem st x + 4096 * g_maplen st x).
  Hypothesis HMkeep : forall a, dfoot a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.

  Lemma dkeep_defined : forall lo hi, (forall a, lo <= a < hi -> dfoot a) -> defined M lo hi -> defined M' lo hi.
  Proof. intros lo hi HF D a Ha. apply HMkeep; [apply HF; exact Ha | apply D; exact Ha]. Qed.

  (* [comment removed for export] *)
  Definition statb (a : Z) : Prop :=
    a = A_NEED_LOCKS \/ (A_PAGESIZE <= a < A_PAGESIZE + 8) \/ (MLOCK <= a < MLOCK + 4) \/ (A_CANARY <= a < A_CANARY + 8) \/
    (A_GOT_CANARY <= a < A_GOT_CANARY + 8) \/ (A_ERRNO <= a < A_ERRNO + 4) \/
    (A_TAB_CTZ <= a < A_TAB_CTZ + 32) \/ (A_TAB_SC <= a < A_TAB_MED + 4).

  (* [comment removed for export] *)
  Lemma rep_statics_tr_s :
    agree_on statb M M' -> s_canary st' = s_canary st -> s_errno st' = s_errno st ->
    rep_statics st' M'.
  Proof.
    intros AG Ec Ee. pose proof HMkeep as KEEP. (* [comment removed for export] *)
    pose proof (rp_statics st M HREP) as [A1 A2 A3 A4 A5 A6 A7 A8].
    assert (LOW : forall a k v, (forall y, a <= y < a + Z.of_nat k -> statb y) -> 0 <= a -> a + Z.of_nat k <= CTX -> cell M a k v -> cell M' a k v).
    { intros a k v Hk Ha Hc C. eapply cell_agree; [exact Ha | unfold CTX in *; lia | | exact C].
      eapply agree_on_mono; [exact AG|]. exact Hk. }
    constructor; rewrite ?Ec, ?Ee;
      try (eapply LOW; [ unfold statb; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, A_TAB_CTZ, A_TAB_SC, A_TAB_MED; intros; lia
                       | unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                       | cbn; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, CTX; lia
                       | eassumption]).
    - eapply img_clear_agree; [unfold A_TAB_CTZ; lia | unfold A_TAB_CTZ; lia | | eassumption].
      eapply agree_on_mono; [exact AG|]. intros y Hy. unfold statb. do 6 right. left. exact Hy.
    - eapply img_clear_agree; [unfold A_TAB_SC; lia | unfold A_TAB_MED; lia | | eassumption].
      eapply agree_on_mono; [exact AG|]. intros y Hy. unfold statb. do 7 right. exact Hy.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rep_statics_tr :
    agree_on (fun a => IMG_LO <= a < CTX) M M' -> s_canary st' = s_canary st -> s_errno st' = s_errno st ->
    rep_statics st' M'.
  Proof.
    intros AG Ec Ee. apply rep_statics_tr_s; [|exact Ec|exact Ee].
    eapply agree_on_mono; [exact AG|]. intros a Ha. unfold statb in Ha. cbv beta.
    unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, A_TAB_CTZ, A_TAB_SC, A_TAB_MED, CTX in *. lia.
  Qed.

  (* [comment removed for export] *)
  Variable XA : Z -> bool.      (* [comment removed for export] *)
  Variable XF : bool.           (* [comment removed for export] *)
  Lemma rep_ctx_tr :
    agree_on (fun a => CTX <= a < CTX_END /\
                       ~ (exists sc, 0 <= sc < 48 /\ XA sc = true /\ ctx_active sc <= a < ctx_active sc + 8) /\
                       ~ (XF = true /\ ctx_free_meta_head <= a < ctx_free_meta_head + 8)) M M' ->
    (forall sc, 0 <= sc < 48 -> (XA sc = true /\ cell M' (ctx_active sc) 8 (c_active (s_ctx st') sc))
                             \/ (XA sc = false /\ c_active (s_ctx st') sc = c_active (s_ctx st) sc)) ->
    ((XF = true /\ cell M' ctx_free_meta_head 8 (c_free_head (s_ctx st'))) \/ (XF = false /\ c_free_head (s_ctx st') = c_free_head (s_ctx st))) ->
    c_secret (s_ctx st') = c_secret (s_ctx st) -> c_mmap_ctr (s_ctx st') = c_mmap_ctr (s_ctx st) ->
    c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st) -> c_avail_cnt (s_ctx st') = c_avail_cnt (s_ctx st) ->
    c_area_cnt (s_ctx st') = c_area_cnt (s_ctx st) -> c_shift (s_ctx st') = c_shift (s_ctx st) ->
    c_area_head (s_ctx st') = c_area_head (s_ctx st) -> c_area_tail (s_ctx st') = c_area_tail (s_ctx st) ->
    c_cursor (s_ctx st') = c_cursor (s_ctx st) -> (forall sc, c_usage (s_ctx st') sc = c_usage (s_ctx st) sc) ->
    (forall i, c_unmap_seq (s_ctx st') i = c_unmap_seq (s_ctx st) i) -> (forall i, c_bounces (s_ctx st') i = c_bounces (s_ctx st) i) ->
    c_seq (s_ctx st') = c_seq (s_ctx st) -> c_brk (s_ctx st') = c_brk (s_ctx st) ->
    rep_ctx st' M'.
  Proof.
    intros AG HA HF E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14. pose proof HMkeep as KEEP. (* [comment removed for export] *)
    pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
    assert (TR : forall a k v, CTX <= a -> a + Z.of_nat k <= CTX_END ->
              (a + Z.of_nat k <= CTX + 80 /\ (CTX + 24 <= a \/ a + Z.of_nat k <= CTX + 16)) \/ CTX + 464 <= a ->
              cell M a k v -> cell M' a k v).
    { intros a k v H1 H2 H3 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; cbn; lia | | exact C].
      eapply agree_on_mono; [exact AG|]. cbn. intros b Hb. split; [lia|]. split.
      - intros (sc & Hsc & _ & Hr). unfold ctx_active in Hr. lia.
      - intros [_ Hr]. unfold ctx_free_meta_head in Hr. lia. }
    Ltac ctxf TR := eapply TR; [ cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | eauto ].
    constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E13, ?E14; try (ctxf TR).
    - (* [comment removed for export] *)
      destruct HF as [[_ C]|[NX E]]; [exact C|]. rewrite E.
      eapply cell_agree; [unfold ctx_free_meta_head, CTX; lia | unfold ctx_free_meta_head, CTX; cbn; lia | | exact C4].
      eapply agree_on_mono; [exact AG|]. cbn. intros b Hb. unfold ctx_free_meta_head, ctx_active, CTX_END, CTX in *.
      split; [lia|]. split; [intros (sc & Hsc & _ & Hr); lia | intros [X _]; rewrite NX in X; discriminate X].
    - (* [comment removed for export] *)
      intros sc Hsc. destruct (HA sc Hsc) as [[_ C]|[NX E]]; [exact C|]. rewrite E.
      eapply cell_agree; [unfold ctx_active, CTX; lia | unfold ctx_active, CTX; cbn; lia | | exact (C12 sc Hsc)].
      eapply agree_on_mono; [exact AG|]. cbn. intros b Hb. unfold ctx_free_meta_head, ctx_active, CTX_END, CTX in *.
      split; [lia|]. split; [|intros [_ Hr]; lia].
      intros (sc' & Hsc' & X' & Hr). assert (sc' = sc) by lia. subst sc'. rewrite NX in X'; discriminate X'.
    - intros sc Hsc. rewrite E10. ctxf TR.
    - intros i Hi. rewrite E11. ctxf TR.
    - intros i Hi. rewrite E12. ctxf TR.
  Qed.

  (* [comment removed for export] *)
  Variable XM : Z -> bool.
  Lemma rep_areas_tr :
    s_areas st' = s_areas st -> c_secret (s_ctx st') = c_secret (s_ctx st) ->
    (forall ar a, In ar (s_areas st) -> ar <= a < ar + 4096 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
       exists x, metaU st x /\ XM x = true /\ x <= a < x + 40) ->
    (forall x, metaU st x -> XM x = true -> rep_meta M' x (s_meta st' x)) ->
    (forall x, metaU st x -> XM x = false -> s_meta st' x = s_meta st x) ->
    forall ar, In ar (s_areas st') -> rep_area st' M' ar.
  Proof.
    intros Ea Es Hwr HX HnX ar Har. rewrite Ea in Har.
    pose proof (rp_areas st M HREP ar Har) as [CK NS DF MT].
    destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi). hsep; ceil; unfold HEAPLO in Hlo, Hhi.
    assert (HDR : agree_on (fun a => ar <= a < ar + 24) M M').
    { intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (Hwr ar a Har ltac:(lia) NE) as (x & Ux & Xx & Hx).
      exact (metaU_not_hdr st L HWF x ar a Ux Har Hx Ha). }
    constructor.
    - cbn. rewrite Es. eapply cell_agree; [lia | cbn; lia | | exact CK]. eapply agree_on_mono; [exact HDR|]. cbn; intros; lia.
    - eapply cell_agree; [lia | cbn; lia | | exact NS]. eapply agree_on_mono; [exact HDR|]. cbn; intros; lia.
    - eapply dkeep_defined; [|exact DF]. intros a Ha. right; right; left. exists ar. split; [exact Har | exact Ha].
    - intros k Hk. set (x := meta_addr ar k).
      assert (Ux : metaU st x) by (exists ar, k; repeat split; try assumption; lia).
      destruct (XM x) eqn:Xx.
      + exact (HX x Ux Xx).
      + rewrite (HnX x Ux Xx).
        apply (rep_meta_agree M M'); [unfold x, meta_addr, AREA_HDR, META_SZ; lia | unfold x, meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia | | exact (MT k Hk)].
        intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (Hwr ar a Har ltac:(unfold x, meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia) NE) as (y & Uy & Xy & Hy).
        rewrite (metaU_owner st L HWF y ar k a Uy Har ltac:(lia) Hy Ha) in Xy. subst x. rewrite Xx in Xy. discriminate Xy.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_groups_tr :
    (forall x, is_group st' x -> is_group st x) ->
    (forall x, is_group st' x -> mr_mem (s_meta st' x) = mr_mem (s_meta st x) /\ mr_W (s_meta st' x) = mr_W (s_meta st x) /\
                                 s_ai st' x = s_ai st x /\ s_kind st' x = s_kind st x) ->
    (forall x, is_group st' x -> endb_own st' x -> endb_own st x) ->
    (forall x k, is_group st' x -> 0 <= k <= g_lastidx st x ->
        s_slot st' x k = s_slot st x k \/ s_slot st' x k = SAvail \/ s_slot st' x k = SFreed \/
        (exists c o, s_slot st x k = SHost c o /\ s_slot st' x k = SJunk o)) ->
    (forall x a, is_group st' x -> gcell st' x a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall x a, is_group st' x -> gcell st' x a -> gcell st x a \/ (exists k c o, 0 <= k <= g_lastidx st x /\
        s_slot st x k = SHost c o /\ s_slot st' x k = SJunk o /\ g_slot_start st x k + 16 * o - 4 <= a < g_slot_start st x k + 16 * o)) ->
    forall x, is_group st' x -> rep_group st' M' x.
  Proof.
    intros SUB GEO ENDB SL AG BACK x Hx'. pose proof (SUB x Hx') as Hx.
    destruct (GEO x Hx') as (Em & EW & Eai & Ek).
    assert (EgW : g_W st' x = g_W st x) by (unfold g_W; exact EW).
    assert (Egm : g_mem st' x = g_mem st x) by (unfold g_mem; exact Em).
    assert (Egl : g_lastidx st' x = g_lastidx st x) by (unfold g_lastidx; rewrite EgW; reflexivity).
    assert (Egc : g_cnt st' x = g_cnt st x) by (unfold g_cnt; rewrite Egl; reflexivity).
    assert (Egs : g_stride st' x = g_stride st x) by (unfold g_stride, g_maplen, g_sc; rewrite Egl, EgW; reflexivity).
    assert (Ess : forall k, g_slot_start st' x k = g_slot_start st x k) by (intros; unfold g_slot_start; rewrite Egm, Egs; reflexivity).
    assert (Ese : forall k, g_slot_end st' x k = g_slot_end st x k) by (intros; unfold g_slot_end; rewrite Ess, Egs; reflexivity).
    destruct (group_range st L HWF x Hx) as [R1 R2].
    pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
    pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (X1 & X2 & X3).
    pose proof (rp_groups st M HREP x Hx) as RG.
    (* [comment removed for export] *)
    assert (T : rep_group st' M' x \/ True) by (right; exact I). clear T.
    destruct RG as [Hm Hai Hh Hd Hs].
    assert (Gagree : forall a, gcell st' x a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a G; exact (AG x a Hx' G)).
    assert (CR : forall a, gcell st' x a -> 0 <= a < 2 ^ 64).
    { intros a G. destruct (BACK x a Hx' G) as [G0 | (k & c & o & Hk & S0 & S1 & Ha)].
      - pose proof (gcell_in_span st L HWF x a Hx G0). hsep; ceil; unfold HEAPLO in *; lia.
      - assert (G0 : gcell st x a).
        { unfold gcell. right. right. left. exists k, (g_slot_start st x k + 16 * o). unfold slot_ptr. rewrite S0. repeat split; lia. }
        pose proof (gcell_in_span st L HWF x a Hx G0). hsep; ceil; unfold HEAPLO in *; lia. }
    assert (byte_tr : forall a b, gcell st' x a -> byte_at M a b -> byte_at M' a b).
    { intros a b G B. unfold byte_at in *. rewrite (Gagree a G). exact B. }
    assert (cell_tr : forall a n v, (forall y, a <= y < a + Z.of_nat n -> gcell st' x y) -> 0 < Z.of_nat n -> cell M a n v -> cell M' a n v).
    { intros a n v G Hn C. pose proof (CR a (G a ltac:(lia))). pose proof (CR (a + Z.of_nat n - 1) (G (a + Z.of_nat n - 1) ltac:(lia))).
      eapply cell_agree; [lia | lia | | exact C]. intros y Hy Hr. apply Gagree. apply G. exact Hr. }
    assert (hdr_tr : forall k q rc, 0 <= k <= g_lastidx st x -> slot_ptr st' x k = Some q -> rep_hdr st M x k q rc -> rep_hdr st' M' x k q rc).
    { intros k q rc Hk Hq [A B C].
      assert (G : forall a, q - 4 <= a < q -> gcell st' x a).
      { intros a Ha. unfold gcell. right. right. left. exists k, q. rewrite Egl. repeat split; try lia. exact Hq. }
      constructor.
      - apply byte_tr; [apply G; lia | exact A].
      - apply byte_tr; [apply G; lia | exact B].
      - replace (inband st' x q) with (inband st x q) by (unfold inband; rewrite Egm; reflexivity).
        apply cell_tr; [cbn; intros y Hy; apply G; lia | cbn; lia | exact C]. }
    assert (Gh : forall a, g_mem st x <= a < g_mem st x + 12 -> gcell st' x a) by (intros a Ha; unfold gcell; left; rewrite Egm; exact Ha).
    constructor.
    - rewrite Egm. apply cell_tr; [cbn; intros y Hy; apply Gh; lia | cbn; lia | exact Hm].
    - rewrite Egm, Eai. destruct Hai as (b & Hb & Hba & Hmod). exists b. split; [exact Hb|]. split; [|exact Hmod].
      apply byte_tr; [apply Gh; lia | exact Hba].
    - intros k Hk Hend. rewrite Ess. rewrite Egc in Hk, Hend.
      assert (G : gcell st' x (g_slot_start st x k - 4)).
      { unfold gcell. right. left. exists k. rewrite Egc, Ess. repeat split; try lia.
        destruct Hend as [H|H]; [left; exact H | right; exact H]. }
      apply byte_tr; [exact G|]. apply Hh; [exact Hk|]. destruct Hend as [H|H]; [left; exact H | right; exact (ENDB x Hx' H)].
    - rewrite Ek. destruct (s_kind st x) eqn:Kx; [|exact I]. rewrite Egm. unfold g_maplen. rewrite EgW.
      eapply dkeep_defined; [|exact Hd]. intros a Ha. right; right; right. exists x. split; [exact Hx|]. split; [exact Kx|].
      unfold g_maplen. exact Ha.
    - intros k Hk. rewrite Egl in Hk.
      destruct (SL x k Hx' Hk) as [E | [E | [E | (c & o & S0 & S1)]]]; rewrite ?E; [| exact I | exact I |].
      + pose proof (Hs k Hk) as RS. destruct (s_slot st x k) as [| |q n o r|c o|o] eqn:Sk; cbn [rep_slot] in *; try exact I.
        * destruct RS as (RH & Rz & R5).
          assert (Hq : slot_ptr st' x k = Some q) by (unfold slot_ptr; rewrite E; reflexivity).
          assert (Gf : forall a, ((0 < r /\ a = q + n) \/ (5 <= r /\ g_slot_end st x k - 5 <= a < g_slot_end st x k)) -> gcell st' x a).
          { intros a Ha. unfold gcell. right. right. right. exists k, q, n, o, r. rewrite Egl, Ese. split; [lia|]. split; [exact E | exact Ha]. }
          split; [exact (hdr_tr k q _ Hk Hq RH)|]. split.
          -- intros Hr. apply byte_tr; [apply Gf; left; lia | exact (Rz Hr)].
          -- intros Hr. destruct (R5 Hr) as [C B]. rewrite Ese. split.
             ++ apply cell_tr; [cbn; intros y Hy; apply Gf; right; lia | cbn; lia | exact C].
             ++ apply byte_tr; [apply Gf; right; lia | exact B].
        * destruct RS as (rc & Hrc & RH). exists rc. split; [exact Hrc|]. rewrite Ess.
          apply (hdr_tr k _ rc Hk); [|exact RH]. unfold slot_ptr. rewrite E, Ess. reflexivity.
      + rewrite S1. cbn [rep_slot]. exact I.
  Qed.
End RepT.

Lemma dkeep_of_grows : forall st (M M' : mem), mem_grows M M' ->
  forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
Proof. intros st M M' G a _ D. exact (G _ D). Qed.
End MhRepT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen MhExt MhList MhRepT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Rotate.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (sc h : Z) (rest : list Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hl : s_alist st sc = h :: rest.
  Hypothesis Hav0 : mr_avail (s_meta st h) = 0.
  Hypothesis Hfr : mr_freed (s_meta st h) <> 0.
  #[local] Notation l := (s_alist st sc).
  Definition l' : list Z := rest ++ [h].
  Definition nh : Z := head_of l'.
  Definition st' : mst :=
    MST (cx_set_active (s_ctx st) (fupd (c_active (s_ctx st)) sc nh))
        (s_areas st) (s_meta st) (s_flist st) (fupd (s_alist st) sc l') (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).
  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition r_wr (a : Z) : Prop := (sp - MSTK <= a < sp) \/ (ctx_active sc <= a < ctx_active sc + 8).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> r_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMact : cell M' (ctx_active sc) 8 nh.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma l_dll : dll st l. Proof. exact (wl_adll st (WF_lists st L HWF) sc Hsc). Qed.

  Lemma l'_rot : l' = rot 1 l.
  Proof. unfold l'. rewrite Hl. symmetry. exact (rot_app [h] rest). Qed.
  Lemma in_l' : forall x, In x l' <-> In x l.
  Proof. intros x. rewrite l'_rot. apply rot_perm_In. Qed.


  (* [comment removed for export] *)
  Lemma nh_next : nh = mr_next (s_meta st h).
  Proof.
    unfold nh, l'. pose proof (proj1 (dll_dllf st l) l_dll) as D. rewrite Hl in D.
    destruct (D 0 ltac:(rewrite zlen_cons; pose proof (zlen_nonneg rest); lia)) as [N _]. rewrite znth_cons0 in N. rewrite N.
    rewrite zlen_cons. destruct rest as [|x r].
    - cbn. reflexivity.
    - rewrite zlen_cons. rewrite Z.mod_small by (pose proof (zlen_nonneg r); lia). rewrite znth_cons_S by lia. replace (0 + 1 - 1) with 0 by lia.
      rewrite znth_cons0. reflexivity.
  Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_alist : forall s, s_alist st' s = if s =? sc then l' else s_alist st s. Proof. reflexivity. Qed.
  Lemma e_alist_sc : s_alist st' sc = l'. Proof. rewrite e_alist, Z.eqb_refl. reflexivity. Qed.
  Lemma e_alist_other : forall s, s <> sc -> s_alist st' s = s_alist st s.
  Proof. intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc); [contradiction | reflexivity]. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x.
  Proof.
    intros x. unfold in_alist. split; intros (s & Hs & Hin); exists s; split; [exact Hs| |exact Hs|]; rewrite e_alist in *;
      destruct (Z.eqb_spec s sc) as [->|]; try exact Hin; [apply in_l'; exact Hin | apply in_l' in Hin; exact Hin].
  Qed.
  Lemma e_in_alist_same : forall x s, In x (s_alist st' s) <-> In x (s_alist st s).
  Proof. intros x s. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|]; [apply in_l' | tauto]. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x.
  Proof. intros x. unfold listed, in_flist. cbn [s_flist st']. rewrite e_in_alist. tauto. Qed.
  Lemma SL : same_layout st st'.
  Proof. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of Z.of_nat l']; try assumption.
    intros s Hs. unfold fupd. destruct (Z.eqb_spec s sc) as [->|Hne]; [reflexivity | exact (A4 s Hs)].
  Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; cbn [s_flist st' s_meta s_groups]; try assumption.
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (D2 s Hs)].
      rewrite l'_rot. apply (proj2 (dll_dllf st' (rot 1 l))). apply dllf_rot; [rewrite Hl; cbn; lia|]. exact (proj1 (dll_dllf st l) (D2 sc Hsc)).
    - intros s. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (ND2 s)]. rewrite l'_rot. apply (proj2 (NoDup_ListNoDup _)). apply NoDup_rot. apply (proj1 (NoDup_ListNoDup _)). exact (ND2 sc).
    - intros s x Hin. change (is_group st x /\ _) with (is_group st x /\ g_sc st x = s). rewrite e_alist in Hin.
      destruct (Z.eqb_spec s sc) as [->|Hne]; [apply in_l' in Hin|]; exact (AU _ x Hin).
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [exfalso; lia | exact (AN s Hs)].
    - intros x U NL. apply LK; [exact U | intros Hl'; apply NL; apply e_listed; exact Hl'].
    - intros x Hl'. apply LKD. apply e_listed. exact Hl'.
    - intros s x Hin Hne. rewrite e_alist in Hin, Hne. destruct (Z.eqb_spec s sc) as [->|Hs]; [|exact (RS s x Hin Hne)].
      apply in_l' in Hin. fold nh in Hne. destruct (Z.eq_dec x h) as [->|Hxh]; [split; [exact Hav0 | exact Hfr]|].
      apply (RS sc x Hin). rewrite Hl. cbn. exact Hxh.
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L x.
  Proof.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; try assumption.
    - intros Hal. apply e_in_alist_same. apply Lsc. apply e_in_alist. exact Hal.
    - intros H63 Hl'. apply (S63 H63). apply e_listed. exact Hl'.
    - intros Hp. apply e_in_alist_same. exact (Part Hp).
    - intros Hall Hne Hl'. apply e_listed in Hl'.
      (* [comment removed for export] *)
      destruct (Z.eq_dec x h) as [->|Hxh].
      + exfalso. apply Hfr. apply Z.bits_inj_0. intros j. destruct (Z.lt_ge_cases j 0) as [Hj|Hj]; [apply Z.testbit_neg_r; exact Hj|].
        destruct (Z.testbit (mr_freed (s_meta st h)) j) eqn:T; [|reflexivity]. exfalso.
        apply (proj1 (Fr j Hj)) in T. destruct T as [T1 T2]. exact (proj2 (Hall j (conj Hj T1)) T2).
      + apply (Full Hall); [|exact Hl']. revert Hne. cbn [s_alist st']. unfold fupd. change (g_sc st' x) with (g_sc st x).
        destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|intros Hne; exact Hne]. intros _. rewrite E, Hl. cbn. exact Hxh.
    - intros Hall. destruct (FF Hall) as (K & S48 & Hin). split; [exact K|]. split; [exact S48|]. apply e_in_alist_same. exact Hin.
  Qed.

  Lemma t_WF : WF st' L.
  Proof.
    pose proof HWF as (C & A & Ls & G & Ge & Lv & R & WI).
    split; [exact t_wf_ctx|]. split; [exact (wf_areas_ext st st' SL A)|]. split; [exact t_wf_lists|].
    split.
    { destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      - intros x Hx. apply t_wf_group. exact Hx.
      - intros x Hlim. destruct (LIM x Hlim) as (A1 & B1 & C1 & D1). split; [exact A1|]. split; [exact B1|]. split; [|exact D1].
        intros Hl'. apply C1. apply e_listed. exact Hl'. }
    split; [exact (wf_geom_ext st st' L SL HWF Ge)|].
    split; [exact (wf_live_ext st st' L SL Lv) |]. split; [exact (wf_regions_ext st st' L SL HWF eq_refl R) | exact (wf_img_ext st st' SL (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma HMkeep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Proof. exact (dkeep_of_grows st M M' HMgrow). Qed.

  Lemma t_agree : agree_on (fun a => a < CEIL /\ ~ (ctx_active sc <= a < ctx_active sc + 8)) M M'.
  Proof.
    intros a Hr [Ha Hn]. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
    destruct (HMwr a Hr NE) as [W|W]; [ceil; unfold MSTK in *; lia | exact (Hn W)].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof.
    constructor.
    - apply (rep_statics_tr st st' M M' HREP HMkeep); [|reflexivity|reflexivity].
      eapply agree_on_mono; [exact t_agree|]. intros a Ha. cbv beta in Ha. ceil; unfold ctx_active, CTX in *. lia.
    - apply (rep_ctx_tr st st' M M' HREP HMkeep (fun s => s =? sc) false); try reflexivity.
      + eapply agree_on_mono; [exact t_agree|]. intros a (Ha & Hn & _). cbv beta. split; [ceil; unfold CTX_END, CTX in *; lia|].
        intros W. apply Hn. exists sc. split; [exact Hsc|]. split; [apply Z.eqb_refl | exact W].
      + intros s Hs. cbn [s_ctx st' cx_set_active c_active]. unfold fupd. destruct (Z.eqb_spec s sc) as [->|Hne]; [left | right]; split; try reflexivity. exact HMact.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st' L M M' HWF HREP HMkeep (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        destruct (HMwr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; hsep; ceil; unfold ctx_active, CTX, HEAPLO, MSTK in *; lia.
      + intros x Ux X. discriminate X.
    - apply (rep_groups_tr st st' L M M' HWF HREP HMkeep); try (intros; reflexivity).
      + intros x Hx. exact Hx.
      + intros x Hx. repeat split; reflexivity.
      + intros x Hx E. exact E.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. pose proof (gcell_in_span st L HWF x a Hx G). destruct (group_range st L HWF x Hx).
        apply t_agree; [hsep; ceil; unfold HEAPLO in *; lia|]. split; [lia|]. hsep; unfold ctx_active, CTX, HEAPLO in *. lia.
      + intros x a Hx G. left. exact G.
  Qed.

  Theorem rotate_close : WF st' L /\ REP st' M'.
  Proof. split; [exact t_WF | exact t_REP]. Qed.

End Rotate.

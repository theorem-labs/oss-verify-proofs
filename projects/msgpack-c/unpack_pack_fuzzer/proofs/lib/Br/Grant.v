(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState NodesM DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Ceiling.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue MPath Room.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn [live_bytes app]; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn [live_bytes]; [lia|]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?unsigned_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  cbn [maps_subtract_all]. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used, vm_live_bytes, vm_backed_maps. rewrite Hl, Hm.
  cbn [maps_subtract_all length Z.of_nat Z.mul]. rewrite Z.add_0_r. apply live_bytes_maps_subtract_all_le.
Qed.

Lemma grant_budget_intro : forall m n, mo_ok m ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hmo H. pose proof (vm_backing_used_le_live m (mo_ok_lazy _ Hmo) (mo_ok_materialized _ Hmo)). lia. Qed.

Lemma mprotect_budget_ok_intro : forall m addr n, mo_ok m ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hmo Hlive. unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [exact (mo_ok_lazy _ Hmo) | exact (mo_ok_materialized _ Hmo)]|].
  unfold mprotect_model_next. cbn [m_vmmaps vm_live_bytes vm_maps vm_limit with_vmmaps vmst_maps m_vm]. exact Hlive.
Qed.

Definition FLOOR : Z := 2 ^ 32.
Definition cand (N : Z) (j : nat) : Z := FLOOR + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.
Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof. intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto. Qed.

Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand. nia. Qed.

Lemma conflict_unique : forall N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand N j) n p -> zconflict (cand N k) n p -> j = k.
Proof.
  intros N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - assert (Hall : forall k, In k js -> P k = false).
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
  rewrite !unsigned_lit by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

Lemma grant_exists_gen : forall (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  FLOOR + C * (2 * N) + N <= alloc_ceiling -> ceil_ok (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok m a n.
Proof.
  intros m N n C HN HNal Hn Hsz Hcnt Hband Hck Hlive.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand N j)).
  pose_ceil. unfold ceil_ok in Hck.
  assert (Hc : FLOOR <= cand N j <= FLOOR + C * (2 * N)) by (unfold cand; nia).
  unfold grant_ok. unfold FLOOR in *. rewrite !unsigned_lit by lia.
  assert (E1 : cand N j mod page_size = 0).
  { unfold cand, FLOOR. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  split; [exact E1|]. split; [lia|]. split; [lia|]. split; [| exact Hlive].
  fold l. apply (region_free_of_noconflict l (cand N j) n); first [lia | exact Hfree].
Qed.

Lemma grant_exists : forall (m : Model) (n : Z),
  0 <= n <= 2 ^ 30 ->
  sizes_le (2 ^ 30) (vmaps m) ->
  Z.of_nat (length (vmaps m)) <= 40000 ->
  ceil_ok (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok m a n.
Proof.
  intros m n Hn Hsz Hcnt Hck Hlive.
  apply (grant_exists_gen m (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - pose_ceil. unfold FLOOR. lia.
Qed.

Lemma room_grant : forall mo j nZ,
  room mo j -> 0 <= j <= 27 -> mo_ok mo -> ceil_ok (m_vmmaps mo) -> 0 <= nZ <= 2 ^ 27 ->
  exists a, grant_ok mo a nZ.
Proof.
  intros mo j nZ [Rs Rc Rl Rm] Hj Hmo Hck Hn.
  apply (grant_exists mo nZ ltac:(lia) Rs); [lia | exact Hck|].
  apply grant_budget_intro; [exact Hmo|]. nia.
Qed.

End CEIL.

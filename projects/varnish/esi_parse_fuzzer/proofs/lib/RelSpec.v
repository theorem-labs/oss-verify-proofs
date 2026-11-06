(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Module Foott1g.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).
End Foott1g.

Module Gap04.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pru_spec : forall x, x <= page_round_up_Z x <= x + 4095 /\ page_round_up_Z x mod 4096 = 0.
Proof.
  intros x. unfold page_round_up_Z. change page_size with 4096.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)) as M.
  split; [lia|]. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)

Lemma pru_le_aligned : forall x a, x <= a -> a mod 4096 = 0 -> page_round_up_Z x <= a.
Proof.
  intros x a Hle Ha. unfold page_round_up_Z. change page_size with 4096.
  pose proof (Z.div_mod a 4096 ltac:(lia)) as D. rewrite Ha, Z.add_0_r in D.
  assert ((x + 4096 - 1) / 4096 < a / 4096 + 1) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma find_none_forall {A} : forall (P : A -> bool) (l : list A),
  List.find P l = None -> forall x, In x l -> P x = false.
Proof.
  induction l as [|y l IH]; intros Hf x Hin; [contradiction|].
  cbn in Hf. destruct (P y) eqn:Py; [discriminate|].
  destruct Hin as [<-|Hin]; [exact Py | exact (IH Hf x Hin)].
Qed.

Lemma fold_max_ge_seed : forall l s, s <= fold_left Z.max l s.
Proof. induction l as [|x l IH]; intros s; cbn; [lia|]. specialize (IH (Z.max s x)). lia. Qed.

Lemma fold_max_ge_in : forall l s x, In x l -> x <= fold_left Z.max l s.
Proof.
  induction l as [|y l IH]; intros s x Hin; [destruct Hin|]. cbn. destruct Hin as [<-|Hin].
  - pose proof (fold_max_ge_seed l (Z.max s y)). lia.
  - apply IH. exact Hin.
Qed.

Lemma fold_max_le : forall l s b, s <= b -> (forall x, In x l -> x <= b) -> fold_left Z.max l s <= b.
Proof.
  induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|]. apply IH; [pose proof (Hl y (or_introl eq_refl)); lia|].
  intros x Hx. apply Hl. right. exact Hx.
Qed.

Lemma fold_max_in_or_seed : forall l s, fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
  induction l as [|y l IH]; intros s; cbn; [left; reflexivity|].
  destruct (IH (Z.max s y)) as [E|E].
  - rewrite E. destruct (Z.max_spec s y) as [[_ ->]|[_ ->]]; [right; left; reflexivity| left; reflexivity].
  - right. right. exact E.
Qed.

(* [comment removed for export] *)
Definition zsumf {A} (f : A -> Z) (l : list A) : Z := fold_right (fun x acc => f x + acc) 0 l.

Lemma zsumf_app {A} (f : A -> Z) l1 l2 : zsumf f (l1 ++ l2) = zsumf f l1 + zsumf f l2.
Proof. unfold zsumf. induction l1 as [|x l1 IH]; cbn; [lia| rewrite IH; lia]. Qed.

Lemma zsumf_nonneg {A} (f : A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= zsumf f l.
Proof.
  unfold zsumf. induction l as [|x l IH]; intros H; cbn; [lia|]. pose proof (H x (or_introl eq_refl)).
  pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition iv_end_up (iv : word * word) : Z :=
  page_round_up_Z (bv_unsigned (fst iv) + bv_unsigned (snd iv)).

Lemma vm_base_ok_intro : forall h nZ (c : word),
  bv_unsigned c mod page_size = 0 -> 0 < bv_unsigned c -> bv_unsigned c + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) c (Z_to_bv 64 nZ) = true ->
  vm_base_ok h nZ c = true.
Proof.
  intros h nZ c H1 H2 H3 H4. unfold vm_base_ok.
  rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4. reflexivity.
Qed.

Lemma alloc_top_lt : forall h, alloc_top h < 2 ^ 64.
Proof. intros h. pose proof (alloc_top_room h). unfold two_pow_64, stack_max_size in *. lia. Qed.

(* [comment removed for export] *)
Theorem vm_gap_available_complete : forall h nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ a HnZ Hal Hpos Hce Hfree. pose proof (alloc_top_lt h) as Hc64.
  change page_size with 4096 in Hal.
  set (L := vm_reserved h ++ vm_maps h) in *.
  set (aZ := bv_unsigned a) in *.
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  set (cs := List.filter (fun e => e <=? aZ) (map iv_end_up L)).
  set (c := fold_left Z.max cs 4096).
  assert (Hcs : forall x, In x cs <-> In x (map iv_end_up L) /\ (x <=? aZ) = true)
    by (intro x; unfold cs; exact (filter_In _ x _)).
  assert (Hclo : 4096 <= c) by (unfold c; apply fold_max_ge_seed).
  assert (Ha4 : 4096 <= aZ) by (pose proof (Z.div_mod aZ 4096 ltac:(lia)); nia).
  assert (Hchi : c <= aZ).
  { unfold c. apply fold_max_le; [lia|]. intros x Hx. apply Hcs in Hx. apply Z.leb_le. exact (proj2 Hx). }
  assert (HcW : bv_unsigned (Z_to_bv 64 c) = c)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (Hcal : c mod 4096 = 0).
  { destruct (fold_max_in_or_seed cs 4096) as [Heq|Hin].
    - fold c in Heq. rewrite Heq. reflexivity.
    - fold c in Hin. apply Hcs in Hin as [Hin _]. apply in_map_iff in Hin as (p & Hp & _).
      rewrite <- Hp. apply (proj2 (pru_spec _)). }
  assert (Hmax : forall p, In p L -> iv_end_up p <= aZ -> iv_end_up p <= c).
  { intros p Hp Hle. unfold c. apply fold_max_ge_in. apply Hcs. split; [apply in_map; exact Hp | apply Z.leb_le; exact Hle]. }
  assert (Hcfree : region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HnW in Hno. fold aZ in Hno. rewrite HcW, HnW.
    apply andb_false_iff in Hno. apply andb_false_iff.
    destruct Hno as [Hno|Hno].
    - apply Z.ltb_ge in Hno. left. apply Z.ltb_ge.
      assert (Hr : iv_end_up (b, s) <= aZ) by (unfold iv_end_up; cbn [fst snd]; apply pru_le_aligned; [lia | exact Hal]).
      pose proof (Hmax _ Hin Hr) as Hrc. unfold iv_end_up in Hrc. cbn [fst snd] in Hrc.
      pose proof (proj1 (pru_spec (bv_unsigned b + bv_unsigned s))). lia.
    - apply Z.ltb_ge in Hno. right. apply Z.ltb_ge. lia. }
  unfold vm_gap_available, vm_find_base.
  destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) as [x|] eqn:Hf; [reflexivity|].
  exfalso.
  assert (Hin : In (Z_to_bv 64 c) (vm_base_candidates h)).
  { unfold vm_base_candidates. fold L.
    destruct (fold_max_in_or_seed cs 4096) as [Heq|Hin].
    - left. fold c in Heq. rewrite Heq. reflexivity.
    - right. fold c in Hin. apply Hcs in Hin as [Hin _]. apply in_map_iff in Hin as (p & Hp & HinL).
      apply in_map_iff. exists p. split; [|exact HinL]. rewrite <- Hp. reflexivity. }
  pose proof (find_none_forall _ _ Hf _ Hin) as Hbad.
  rewrite (vm_base_ok_intro h nZ (Z_to_bv 64 c)) in Hbad; [discriminate| | | |]; rewrite ?HcW; change page_size with 4096; try lia.
  exact Hcfree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition esz (e : word * word) : Z := bv_unsigned (snd e).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).

(* [comment removed for export] *)
Definition zover (a nZ : Z) (e : word * word) : bool := (a <? elo e + esz e) && (elo e <? a + nZ).

(* [comment removed for export] *)
Definition jcost (nZ : Z) (e : word * word) : Z := esz e + nZ + 4095.

Lemma sweep : forall nZ, 0 <= nZ -> forall (E : list (word * word)) (a : Z), a mod 4096 = 0 ->
  exists a', a <= a' /\ a' mod 4096 = 0 /\ a' <= a + zsumf (jcost nZ) E /\ forall e, In e E -> zover a' nZ e = false.
Proof.
  intros nZ HnZ E. remember (length E) as k eqn:Hk. revert E Hk.
  induction k as [k IH] using (well_founded_induction (Wf_nat.lt_wf)). intros E Hk a Ha.
  assert (Hcost : forall l, 0 <= zsumf (jcost nZ) l).
  { intros l. apply zsumf_nonneg. intros e _. unfold jcost, esz. pose proof (bv_unsigned_in_range 64 (snd e)). lia. }
  destruct (List.existsb (zover a nZ) E) eqn:Hex.
  - apply existsb_exists in Hex as (e0 & Hin & Hov).
    apply in_split in Hin as (l1 & l2 & ->).
    set (a1 := page_round_up_Z (elo e0 + esz e0)).
    pose proof (pru_spec (elo e0 + esz e0)) as [[R1 R2] R3]. fold a1 in R1, R2, R3.
    unfold zover in Hov. apply andb_prop in Hov as [O1 O2]. apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
    destruct (IH (length (l1 ++ l2))) with (E := l1 ++ l2) (a := a1) as (a' & A1 & A2 & A3 & A4);
      [rewrite Hk, !length_app; cbn; lia| reflexivity| exact R3|].
    exists a'. split; [lia|]. split; [exact A2|]. split.
    + rewrite zsumf_app in *. cbn [zsumf fold_right] in *. fold (zsumf (jcost nZ) l2) in *.
      unfold jcost at 2. pose proof (Hcost l1). pose proof (Hcost l2). lia.
    + intros e He. apply in_app_or in He as [He|[<-|He]]; [apply A4; apply in_or_app; left; exact He| |apply A4; apply in_or_app; right; exact He].
      unfold zover. apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - exists a. split; [lia|]. split; [exact Ha|]. split; [pose proof (Hcost E); lia|].
    intros e He. destruct (zover a nZ e) eqn:E'; [|reflexivity]. exfalso.
    assert (existsb (zover a nZ) E = true) by (apply existsb_exists; exists e; auto). congruence.
Qed.

(* [comment removed for export] *)
Theorem vm_gap_available_of_sum : forall h nZ,
  0 <= nZ ->
  4096 + zsumf (jcost nZ) (vm_reserved h ++ vm_maps h) + nZ <= alloc_top h ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ HnZ Hroom. pose proof (alloc_top_lt h) as Hc64.
  destruct (sweep nZ HnZ (vm_reserved h ++ vm_maps h) 4096 eq_refl) as (a' & A1 & A2 & A3 & A4).
  assert (HaW : bv_unsigned (Z_to_bv 64 a') = a')
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  apply (vm_gap_available_complete h nZ (Z_to_bv 64 a')); rewrite ?HaW; change page_size with 4096; try lia; try exact A2.
  apply region_free_intro. intros b s Hin. specialize (A4 (b, s) Hin). unfold zover, elo, esz in A4. cbn [fst snd] in A4.
  unfold iv_overlap. rewrite HaW, HnW. exact A4.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsumf_jcost : forall nZ l, zsumf (jcost nZ) l = zsumf esz l + Z.of_nat (length l) * (nZ + 4095).
Proof. intros nZ l. induction l as [|e l IH]; cbn [zsumf fold_right length]; [lia|]. fold (zsumf (jcost nZ) l) (zsumf esz l) in *. rewrite IH. unfold jcost. lia. Qed.

(* [comment removed for export] *)
Corollary vm_gap_available_of_bounds : forall h nZ K S,
  0 <= nZ ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= K ->
  zsumf esz (vm_reserved h ++ vm_maps h) <= S ->
  4096 + S + K * (nZ + 4095) + nZ <= alloc_top h ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ K S HnZ HK HS Hroom. apply vm_gap_available_of_sum; [exact HnZ|].
  rewrite zsumf_jcost. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsumf_esz_live : forall l, zsumf esz l = live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [reflexivity|]. fold (zsumf esz l). rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_grant_not_refusable : forall flags m nZ,
  vm_gap_available (m_vmmaps m) nZ = true ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m) ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ Hg Hb. unfold mmap_grant_refusable. rewrite Hg.
  unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b flags); [reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.

Lemma mmap_reserve_not_refusable : forall m nZ,
  vm_gap_available (m_vmmaps m) nZ = true -> mmap_reserve_refusable m nZ = false.
Proof. intros m nZ Hg. unfold mmap_reserve_refusable. rewrite Hg. reflexivity. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End Gap04.

Module Speco6o.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.
End Speco6o.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb_refl : forall {n : N} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

Lemma word_unsigned_range : forall (w : word),
  (0 <= bv_unsigned w < two_pow_64)%Z.
Proof.
  intros w. pose proof (bv_unsigned_in_range _ w) as H.
  unfold two_pow_64. unfold bv_modulus in H.
  change (Z.of_N 64) with 64%Z in H. exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition errnos_ok (es : list Z) : bool :=
  forallb (fun e => (1 <=? e)%Z && (e <=? 4095)%Z) es.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_bytes_aux_prefix : forall k n mp a w,
  (k <= n)%nat -> read_bytes_aux mp a n = Some w ->
  read_bytes_aux mp a k = Some (firstn k w).
Proof.
  induction k as [|k IH]; intros n mp a w Hk Hw; [reflexivity|].
  destruct n as [|n]; [lia|].
  cbn in Hw. destruct (mp a) as [b|] eqn:Hb; [|discriminate].
  destruct (read_bytes_aux mp (a + 1) n) as [r|] eqn:Hr; [|discriminate].
  inversion Hw; subst w.
  cbn. rewrite Hb. rewrite (IH n mp (a + 1) r ltac:(lia) Hr). reflexivity.
Qed.

Lemma read_bytes_map_prefix : forall mp a len k w,
  (bv_unsigned k <= bv_unsigned len)%Z -> read_bytes_map mp a len = Some w ->
  read_bytes_map mp a k = Some (firstn (word_to_nat k) w).
Proof.
  intros mp a len k w Hk Hw. rewrite read_bytes_map_eq in *.
  unfold word_to_nat in *.
  apply read_bytes_aux_prefix with (n := Z.to_nat (bv_unsigned len));
    [lia | assumption].
Qed.

Lemma read_bytes_aux_length : forall mp k a w,
  read_bytes_aux mp a k = Some w -> length w = k.
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in Hw.
  - inversion Hw. reflexivity.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. cbn. now rewrite (IH _ _ Hr).
Qed.

Lemma read_bytes_map_length : forall mp a len w,
  read_bytes_map mp a len = Some w -> Z.of_nat (length w) = bv_unsigned len.
Proof.
  intros mp a len w Hw. rewrite read_bytes_map_eq in Hw.
  unfold word_to_nat in Hw.
  rewrite (read_bytes_aux_length _ _ _ _ Hw).
  pose proof (word_unsigned_range len). lia.
Qed.

Lemma readable_bytes_aux_full : forall mp k a w,
  read_bytes_aux mp a k = Some w -> readable_bytes_aux mp a k = w.
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in *.
  - now inversion Hw.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. now rewrite (IH _ _ Hr).
Qed.

Lemma readable_bytes_full : forall mp a len w,
  read_bytes_map mp a len = Some w -> readable_bytes mp a len = w.
Proof.
  intros. rewrite read_bytes_map_eq in *. rewrite readable_bytes_eq.
  now apply readable_bytes_aux_full.
Qed.

Lemma len_word_unsigned : forall {A} (l : list A),
  (Z.of_nat (length l) < two_pow_64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l Hl. unfold len_word.
  rewrite Z_to_bv_small; [reflexivity|].
  unfold bv_modulus. change (Z.of_N 64) with 64%Z.
  unfold two_pow_64 in Hl. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gather_prefix_full : forall mp iovs bs,
  gather_iovecs mp iovs = Some bs -> gather_prefix mp iovs = bs.
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite (readable_bytes_full _ _ _ _ Hw).
    rewrite (read_bytes_map_length _ _ _ _ Hw), Z.eqb_refl.
    now rewrite (IH _ eq_refl).
Qed.

Lemma gather_iovecs_length : forall mp iovs bs,
  gather_iovecs mp iovs = Some bs -> Z.of_nat (length bs) = iovs_total iovs.
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite length_app, Nat2Z.inj_add.
    rewrite (read_bytes_map_length _ _ _ _ Hw), (IH _ eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)

Lemma page_round_up_Z_mono : forall a b,
  (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|].
  apply Z.div_le_mono; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_unfold :=
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from, lowest_fd,
    set_fds, set_vmmaps, forget_vm_range,
    set_stdin, set_fs, set_halted, set_tid,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

(* [comment removed for export] *)
Lemma Ok_inj {A} : forall (x x' : A) m m' e e',
  Ok x m e = Ok x' m' e' -> x = x' /\ m = m' /\ e = e'.
Proof. intros x x' m m' e e' H. injection H. auto. Qed.

Lemma Ok_Unmodeled {A} : forall (x : A) m e, Ok x m e = Unmodeled -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Unmodeled_Ok {A} : forall (x : A) m e, Unmodeled = Ok x m e -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Some_inj' {A} : forall (x y : A), Some x = Some y -> x = y.
Proof. intros x y H. injection H. auto. Qed.

Lemma Some_None {A} : forall (x : A), Some x = None -> False.
Proof. intros x H. discriminate H. Qed.

Lemma None_Some {A} : forall (x : A), None = Some x -> False.
Proof. intros x H. discriminate H. Qed.

(* [comment removed for export] *)
Ltac inv_sys :=
  repeat first
  [ progress subst
  | match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : Ok _ _ _ = Ok _ _ _ |- _ => apply Ok_inj in H; destruct H as (? & ? & ?); subst
    | H : Ok _ _ _ = Unmodeled |- _ => exfalso; exact (Ok_Unmodeled _ _ _ H)
    | H : Unmodeled = Ok _ _ _ |- _ => exfalso; exact (Unmodeled_Ok _ _ _ H)
    | H : Some _ = Some _ |- _ => apply Some_inj' in H; subst
    | H : Some _ = None |- _ => exfalso; exact (Some_None _ H)
    | H : None = Some _ |- _ => exfalso; exact (None_Some _ H)
    | H : False |- _ => contradiction
    | H : true = false |- _ => exfalso; exact (Bool.diff_true_false H)
    | H : false = true |- _ => exfalso; exact (Bool.diff_false_true H)
    | H : _ \/ _ |- _ => destruct H
    end
  | progress cbv beta zeta in * ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition out_det (eff : SyscallEffect) (m' : Model) (evs : list event)
    (o : outcome SyscallEffect) : Prop :=
  o = Ok eff m' evs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_29 : forall i m o,
  bv_unsigned (in_sysno i) = 29%Z ->
  syscall_spec i m o <-> ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_56 : forall i m o,
  bv_unsigned (in_sysno i) = 56%Z ->
  syscall_spec i m o <-> openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_57 : forall i m o,
  bv_unsigned (in_sysno i) = 57%Z ->
  syscall_spec i m o <-> close_spec (fd32 (in_arg i 0)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_63 : forall i m o,
  bv_unsigned (in_sysno i) = 63%Z ->
  syscall_spec i m o <-> read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)

Lemma syscall_spec_66 : forall i m o,
  bv_unsigned (in_sysno i) = 66%Z ->
  syscall_spec i m o <-> writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_96 : forall i m o,
  bv_unsigned (in_sysno i) = 96%Z ->
  syscall_spec i m o <-> set_tid_address_spec i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_214 : forall i m o,
  bv_unsigned (in_sysno i) = 214%Z ->
  syscall_spec i m o <-> brk_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_215 : forall i m o,
  bv_unsigned (in_sysno i) = 215%Z ->
  syscall_spec i m o <-> munmap_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_222 : forall i m o,
  bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec i m o <->
  mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_226 : forall i m o,
  bv_unsigned (in_sysno i) = 226%Z ->
  syscall_spec i m o <-> mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma close_outcome : forall fd i m e o,
  fd_lookup (m_fds m) fd = Some e ->
  close_spec fd i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds m) fd) m) [].
Proof.
  intros fd i m e o Hlk. unfold close_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ioctl_tty_outcome : forall fd req i m (c : word) o,
  fd_lookup (m_fds m) fd = Some (FdChannel c) ->
  tty_only_request req = true ->
  ioctl_spec fd req i m o <->
  o = Ok (mkEffect (errno_ret ENOTTY) [] []) m [].
Proof.
  intros fd req i m c o Hlk Hreq. unfold ioctl_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *;
      rewrite ?Hreq in *; inv_sys; reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. rewrite ?Hreq; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma set_tid_fresh_outcome : forall i m o,
  m_tid m = None ->
  set_tid_address_spec i m o <->
  exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
            /\ o = Ok (mkEffect t [] []) (with_tid t m) [].
Proof.
  intros i m o Htid. unfold set_tid_address_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys.
    eexists; split; [split; eassumption|reflexivity].
  - intros (t & Ht & ->). eexists _, _, _, _. split; [reflexivity|]. rewrite Htid.
    split; [|reflexivity]. eexists _, _, _, _. split; [exists t; split; [exact Ht|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma brk_outcome : forall req i m o,
  brk_spec req i m o <->
  exists r, brk_r_ok m req r = true
            /\ o = Ok (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
                                   (brk_unmaps r (vm_brk (m_vmmaps m))) [] [])
                      (with_brk_next m req r) [].
Proof.
  intros req i m o. unfold brk_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    eexists; split; [eassumption|reflexivity].
  - intros (r & Hr & ->). eexists _, _, _, _. split; [reflexivity|].
    split; [|reflexivity]. eexists _, _, _, _. split; [exists r; split; [exact Hr|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munmap_exact_outcome : forall addr len i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  map_has (vm_maps (m_vmmaps m)) addr n = true ->
  munmap_spec addr len i m o <->
  o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
         (with_mmap_destroyed addr n
            (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) addr)
               (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m) [].
Proof.
  intros addr len i m o Hal Hlen Hnw. cbv zeta. intros Hhas. unfold munmap_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), Hlen. cbn [negb orb].
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hhas in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hhas.
    split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_err_out (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

(* [comment removed for export] *)
Definition mmap_err_out_when (C : bool) (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists e, In e (mmap_errnos_when C) /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

Lemma mmap_errnos_when_In : forall C e, In e (mmap_errnos_when C) -> e = ENOMEM /\ C = true.
Proof.
  intros C e H. destruct C; cbn in H; [|contradiction].
  destruct H as [<-|[]]. split; reflexivity.
Qed.

Lemma mmap_errnos_when_sub : forall C e, In e (mmap_errnos_when C) -> In e mmap_errnos.
Proof. intros C e H. destruct C; [exact H | contradiction]. Qed.

(* [comment removed for export] *)

Lemma mmap_errnos_when_false : forall e, ~ In e (mmap_errnos_when false).
Proof. intros e H. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma mmap_err_out_when_false : forall m o, ~ mmap_err_out_when false m o.
Proof. intros m o (e & He & _). exact He. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma mprotect_errnos_when_sub : forall C e, In e (mprotect_errnos_when C) -> In e mprotect_errnos.
Proof. intros C e H. destruct C; [exact H | contradiction]. Qed.

Lemma acfg_lift_enomem : forall i m (Ref Grant : outcome SyscallEffect -> Prop) (forced : bool),
  (bv_unsigned (in_sysno i) = 222%Z \/ bv_unsigned (in_sysno i) = 226%Z) ->
  (forall o, syscall_spec i m o <-> Ref o \/ Grant o) ->
  (forall o, Ref o -> exists eff m' evs, o = Ok eff m' evs /\ eff_ret eff = errno_ret ENOMEM
                                         /\ m_halted m' = None) ->
  (forall o, Grant o -> exists eff m' evs, o = Ok eff m' evs
                                           /\ (bv_unsigned (eff_ret eff) mod page_size = 0)%Z
                                           /\ m_halted m' = None) ->
  (forall o, Grant o -> forced = false) ->
  (forced = false -> exists o, Grant o) ->
  forall o, syscall_spec_acfg i m o <-> (forced = true /\ Ref o) \/ Grant o.
Proof.
  intros i m Ref Grant forced Hno Hchar HR HG Hgf Hfg.
  refine (acfg_char_split i m Ref Grant forced _ Hchar _ _ _ Hgf Hfg).
  - destruct Hno as [E|E]; apply (acfg_family_off_no _ _ E); apply alloc_no_b_In; reflexivity.
  - intros eff m' evs Hs. apply Hchar in Hs.
    destruct Hs as [Hs|Hs]; [destruct (HR _ Hs) as (eff0 & m0 & evs0 & Heq & _ & Hh0)
                            | destruct (HG _ Hs) as (eff0 & m0 & evs0 & Heq & _ & Hh0)];
      apply Ok_inj in Heq as (_ & E & _); rewrite E; exact Hh0.
  - intros o Hr. destruct (HR o Hr) as (eff & m' & evs & -> & Hret & _).
    exists eff, m', evs. split; [reflexivity|]. rewrite Hret.
    destruct Hno as [E|E]; [rewrite (refusal_b_222 _ _ _ E) | rewrite (refusal_b_226 _ _ _ E)];
      apply ret_in_errnos_errno; left; reflexivity.
  - intros o Hg. destruct (HG o Hg) as (eff & m' & evs & -> & Hal & _).
    exists eff, m', evs. split; [reflexivity|].
    destruct Hno as [E|E]; [rewrite (refusal_b_222 _ _ _ E) | rewrite (refusal_b_226 _ _ _ E)];
      exact (ret_in_errnos_ENOMEM_aligned _ Hal).
Qed.

Lemma acfg_lift_mmap_when : forall i m (G : outcome SyscallEffect -> Prop) (forced : bool),
  bv_unsigned (in_sysno i) = 222%Z ->
  m_halted m = None ->
  (forall o, syscall_spec i m o <->
     (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m []) \/ G o) ->
  (forall o, G o -> exists eff m' evs, o = Ok eff m' evs
                                       /\ (bv_unsigned (eff_ret eff) mod page_size = 0)%Z
                                       /\ m_halted m' = None) ->
  (forall o, G o -> forced = false) ->
  (forced = false -> exists o, G o) ->
  forall o, syscall_spec_acfg i m o <->
    (exists e, In e (mmap_errnos_when forced) /\ o = Ok (mkEffect (errno_ret e) [] []) m []) \/ G o.
Proof.
  intros i m G forced Hno Hh Hchar HG Hgf Hfg o.
  assert (HR : forall o', (exists e, In e mmap_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m []) ->
             exists eff m' evs, o' = Ok eff m' evs /\ eff_ret eff = errno_ret ENOMEM /\ m_halted m' = None).
  { intros o' (e & He & ->). exists (mkEffect (errno_ret e) [] []), m, [].
    split; [reflexivity|]. split; [|exact Hh].
    destruct He as [<-|[]]. reflexivity. }
  rewrite (acfg_lift_enomem i m
             (fun o' => exists e, In e mmap_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m [])
             G forced (or_introl Hno) Hchar HR HG Hgf Hfg o).
  split.
  - intros [[Hf (e & He & ->)] | HG']; [left | right; exact HG'].
    exists e. split; [rewrite Hf; exact He | reflexivity].
  - intros [(e & He & ->) | HG']; [left | right; exact HG'].
    split; [destruct forced; [reflexivity | destruct He] |].
    exists e. split; [exact (mmap_errnos_when_sub _ _ He) | reflexivity].
Qed.

Lemma acfg_lift_mprotect_when : forall i m (G : outcome SyscallEffect -> Prop) (forced : bool),
  bv_unsigned (in_sysno i) = 226%Z ->
  m_halted m = None ->
  (forall o, syscall_spec i m o <->
     (exists e, In e mprotect_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m []) \/ G o) ->
  (forall o, G o -> exists eff m' evs, o = Ok eff m' evs
                                       /\ (bv_unsigned (eff_ret eff) mod page_size = 0)%Z
                                       /\ m_halted m' = None) ->
  (forall o, G o -> forced = false) ->
  (forced = false -> exists o, G o) ->
  forall o, syscall_spec_acfg i m o <->
    (exists e, In e (mprotect_errnos_when forced) /\ o = Ok (mkEffect (errno_ret e) [] []) m []) \/ G o.
Proof.
  intros i m G forced Hno Hh Hchar HG Hgf Hfg o.
  assert (HR : forall o', (exists e, In e mprotect_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m []) ->
             exists eff m' evs, o' = Ok eff m' evs /\ eff_ret eff = errno_ret ENOMEM /\ m_halted m' = None).
  { intros o' (e & He & ->). exists (mkEffect (errno_ret e) [] []), m, [].
    split; [reflexivity|]. split; [|exact Hh].
    destruct He as [<-|[]]. reflexivity. }
  rewrite (acfg_lift_enomem i m
             (fun o' => exists e, In e mprotect_errnos /\ o' = Ok (mkEffect (errno_ret e) [] []) m [])
             G forced (or_intror Hno) Hchar HR HG Hgf Hfg o).
  split.
  - intros [[Hf (e & He & ->)] | HG']; [left | right; exact HG'].
    exists e. split; [rewrite Hf; exact He | reflexivity].
  - intros [(e & He & ->) | HG']; [left | right; exact HG'].
    split; [destruct forced; [reflexivity | destruct He] |].
    exists e. split; [exact (mprotect_errnos_when_sub _ _ He) | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mmap_anon_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply Bool.negb_true_iff. apply Z.eqb_neq.
  intros H0.
  assert (Hf : Z.testbit (bv_unsigned flags) 5 = true).
  { rewrite <- Hc in Hb. unfold mmap_flags_core in Hb. rewrite Z.ldiff_spec in Hb.
    apply andb_true_iff in Hb as [Hb _]. exact Hb. }
  assert (Ht : Z.testbit (Z.land (bv_unsigned flags) MAP_ANONYMOUS) 5 = true).
  { rewrite Z.land_spec, Hf. reflexivity. }
  rewrite H0, Z.bits_0 in Ht. discriminate Ht.
Qed.

Lemma mmap_shape_gates : forall (p : bool) flags c off,
  p && Z.eqb (mmap_flags_core flags) c && w_is0 off = true ->
  Z.testbit c 5 = true ->
  negb (mmap_off_aligned_b off) = false /\ negb (mmap_anon_b flags) = false.
Proof.
  intros p flags c off H Hb.
  apply andb_true_iff in H as [H Hoff]. apply andb_true_iff in H as [_ Hc].
  apply Z.eqb_eq in Hc. split.
  - unfold mmap_off_aligned_b. unfold w_is0 in Hoff. apply bv_eqb_eq in Hoff. rewrite Hoff.
    reflexivity.
  - rewrite (mmap_anon_of_core _ _ Hc Hb). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_outcome : forall addr len prot flags fd off i m o,
  w_is0 len = false ->
  mmap_modeled_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z
                /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ mmap_noreserve_backed_ok flags m nZ = true)
               /\ o = Ok (mkEffect a [] [(a, n)])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                               (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hlen Hmod. cbv zeta.
  destruct (mmap_shape_gates _ _ _ _ Hmod eq_refl) as [G1 G2].
  unfold mmap_spec. rewrite G1, G2, Hlen, Hmod. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    all: first
      [ solve [left; eexists; split; [eassumption|reflexivity]]
      | solve [right; eexists; split; [|reflexivity]; repeat split; assumption] ].
  - (* [comment removed for export] *)
    intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
      eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noaccess_outcome : forall addr len prot flags fd off i m o,
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z
                /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
               /\ o = Ok (mkEffectU a [] [] [(a, n)] [] [])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
                               (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hlen Hmod Hna. cbv zeta.
  destruct (mmap_shape_gates _ _ _ _ Hna eq_refl) as [G1 G2].
  unfold mmap_spec. rewrite G1, G2, Hlen, Hmod, Hna. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    all: first
      [ solve [left; eexists; split; [eassumption|reflexivity]]
      | solve [right; eexists; split; [|reflexivity]; repeat split; assumption] ].
  - (* [comment removed for export] *)
    intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
      eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition mmap_fixed_destr_out (m : Model) (addr n : word)
    (o : outcome SyscallEffect) : Prop :=
  exists e, In e mmap_errnos
            /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                      (with_mmap_destroyed addr n
                         (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) [].

(* [comment removed for export] *)
Definition spec_destructive_fixed : Prop :=
  forall addr len prot flags fd off i m e,
    bv_unsigned (in_sysno i) = 222%Z ->
    in_args i = [addr; len; prot; flags; fd; off] ->
    m_halted m = None ->
    w_is0 len = false ->
    mmap_modeled_b prot flags off = false ->
    mmap_noaccess_b prot flags off = false ->
    mmap_fixed_noaccess_b prot flags off = true ->
    let h := m_vmmaps m in
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (bv_unsigned addr + nZ <= alloc_top h)%Z ->
    (bv_unsigned addr mod page_size = 0)%Z ->
    (0 < bv_unsigned addr)%Z ->
    region_free (vm_reserved h) addr n = true ->
    map_contains (vm_maps h) addr n = true ->
    In e mmap_errnos ->
    syscall_spec_acfg i m
      (Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
          (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []).

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_outcome_nf : forall addr len prot flags fd off i m o,
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_replacement flags addr n
              (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                 ((addr, n) :: maps_subtract (vm_noaccess h)
                                 (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h)
                 (vm_init_sp h)) m)) []
  \/ mmap_fixed_destr_out m addr n o.
Proof.
  intros addr len prot flags fd off i m o Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  destruct (mmap_shape_gates _ _ _ _ Hfx eq_refl) as [G1 G2].
  unfold mmap_spec. rewrite G1, G2, Hlen, Hmod, Hna, Hfx. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. lia. }
  rewrite E1. cbn [negb]. rewrite bind_get_model. cbv beta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    Hrf, Hmc.
  cbn [negb andb]. unfold mmap_err_out, mmap_fixed_destr_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    all: first
      [ solve [left; eexists; split; [eassumption|reflexivity]]
      | solve [right; left; reflexivity]
      | solve [right; right; eexists; split; [eassumption|reflexivity]] ].
  - intros [(e & He & ->) | [-> | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right; left; eexists _, _, _, _; repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_outcome : forall addr len prot flags fd off i m o,
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  (mmap_err_out m o \/ mmap_fixed_destr_out m addr n o)
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_replacement flags addr n
              (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                 ((addr, n) :: maps_subtract (vm_noaccess h)
                                 (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h)
                 (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
  pose proof (mmap_fixed_noaccess_outcome_nf addr len prot flags fd off i m o Hlen Hmod Hna Hfx
                Hce Hal Hpos Hrf Hmc) as NF. cbv zeta in NF.
  rewrite NF. tauto.
Qed.

(* [comment removed for export] *)
Lemma spec_destructive_fixed_false : Model -> ~ spec_destructive_fixed.
Proof.
  intros m0 SDF.
  set (A := Z_to_bv 64 4096).
  set (h := mkVmMapsFull [] [(A, A)] [] (vm_start_brk (m_vmmaps m0)) (vm_brk (m_vmmaps m0))
              (vm_limit (m_vmmaps m0)) (vm_mmap_base (m_vmmaps m0)) (Z_to_bv 64 (2 ^ 40))).
  set (m := mkModel [] h IEof [] None None None).
  set (i := mkInput (Z_to_bv 64 222) [A; A; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]
              (fun _ => None) (fun _ => None)).
  assert (Hm : m_vmmaps m = h) by reflexivity.
  assert (HA : bv_unsigned A = 4096%Z) by reflexivity.
  assert (Hr : page_round_up_Z (bv_unsigned A) = 4096%Z) by (rewrite HA; vm_compute; reflexivity).
  assert (Htop : alloc_top h = (2 ^ 40 - stack_max_size)%Z) by reflexivity.
  assert (G1 : w_is0 A = false) by (vm_compute; reflexivity).
  assert (G2 : mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
  assert (G3 : mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
  assert (G4 : mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0) = true) by (vm_compute; reflexivity).
  assert (P1 : (bv_unsigned A + page_round_up_Z (bv_unsigned A) <= alloc_top (m_vmmaps m))%Z).
  { rewrite Hm, Htop, Hr, HA. unfold stack_max_size. lia. }
  assert (P2 : (bv_unsigned A mod page_size = 0)%Z) by (rewrite HA; vm_compute; reflexivity).
  assert (P3 : (0 < bv_unsigned A)%Z) by (rewrite HA; lia).
  assert (P4 : region_free (vm_reserved (m_vmmaps m)) A (Z_to_bv 64 (page_round_up_Z (bv_unsigned A))) = true)
    by (rewrite Hm; reflexivity).
  assert (P5 : map_contains (vm_maps (m_vmmaps m)) A (Z_to_bv 64 (page_round_up_Z (bv_unsigned A))) = true)
    by (rewrite Hm, Hr; vm_compute; reflexivity).
  assert (Hno : bv_unsigned (in_sysno i) = 222%Z) by (vm_compute; reflexivity).
  pose proof (SDF A A (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i m ENOMEM
                Hno eq_refl eq_refl G1 G2 G3 G4 P1 P2 P3 P4 P5 (or_introl eq_refl)) as Hs.
  pose proof (proj2 (mmap_fixed_noaccess_outcome_nf A A (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                  i m _ G1 G2 G3 G4 P1 P2 P3 P4 P5) (or_intror (or_introl eq_refl))) as Hg.
  apply (proj2 (syscall_spec_222 i m _ Hno)) in Hg.
  pose proof (acfg_refusal_forced i m _ _ _ Hs eq_refl
                (acfg_family_off_no i 222 Hno (proj1 (alloc_no_b_In 222) eq_refl))
                ltac:(rewrite (refusal_b_222 _ _ _ Hno);
                      exact (ret_in_errnos_errno mmap_errnos ENOMEM (or_introl eq_refl)))
                _ _ _ Hg) as Hall.
  rewrite (refusal_b_222 _ _ _ Hno) in Hall.
  exact (Bool.diff_true_false (eq_trans (eq_sym Hall) (ret_in_errnos_ENOMEM_aligned A P2))).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mprotect_expose_outcome : forall addr len prot i m o,
  mprotect_grows_conflict_b prot = false ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  mprotect_modeled_b prot = true ->
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  map_contains (vm_noaccess h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mprotect_spec addr len prot i m o <->
  (exists e, In e mprotect_errnos
             /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (mprotect_budget_ok m addr n = true
      /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) []).
Proof.
  intros addr len prot i m o Hgc Hal Hlen Hnw Hmod. cbv zeta. intros Hna Hma.
  unfold mprotect_spec.
  rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod. cbn [negb].
  sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hna, Hma in *; cbn [andb] in *; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hb & ->)]; eexists _, _, _, _; (split; [reflexivity|]);
      rewrite Hna, Hma; cbn [andb]; (split; [|reflexivity]).
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_grant_not_refusable : forall flags m nZ a,
  let h := m_vmmaps m in
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a h H1 H2 H3 H4 H5. unfold mmap_grant_refusable. rewrite H5.
  rewrite (proj2 (vm_gap_available_iff (m_vmmaps m) nZ)); [reflexivity|].
  exists a. auto.
Qed.

Lemma mmap_grant_refusable_false : forall flags m nZ,
  mmap_grant_refusable flags m nZ = false ->
  mmap_noreserve_backed_ok flags m nZ = true /\
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros flags m nZ H. unfold mmap_grant_refusable in H.
  apply Bool.orb_false_iff in H as [Hb Hg].
  apply Bool.negb_false_iff in Hb. apply Bool.negb_false_iff in Hg.
  split; [exact Hb|]. exact (proj1 (vm_gap_available_iff _ _) Hg).
Qed.

Lemma mmap_reserve_not_refusable : forall m nZ a,
  let h := m_vmmaps m in
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a h H1 H2 H3 H4. unfold mmap_reserve_refusable.
  rewrite (proj2 (vm_gap_available_iff (m_vmmaps m) nZ)); [reflexivity|].
  exists a. auto.
Qed.

Lemma mmap_reserve_refusable_false : forall m nZ,
  mmap_reserve_refusable m nZ = false ->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros m nZ H. unfold mmap_reserve_refusable in H. apply Bool.negb_false_iff in H.
  exact (proj1 (vm_gap_available_iff _ _) H).
Qed.

Lemma mprotect_not_refusable : forall m addr n,
  mprotect_budget_ok m addr n = true -> mprotect_refusable m addr n = false.
Proof. intros m addr n H. unfold mprotect_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_dir_outcome : forall fd buf count i m o,
  fd_lookup (m_fds m) fd = Some FdDir ->
  access_okb buf (bv_unsigned count) = true ->
  read_spec fd buf count i m o <->
  o = Ok (mkEffect (errno_ret EISDIR) [] []) m [].
Proof.
  intros fd buf count i m o Hlk Hacc. unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, ?Hacc in *; cbn [negb] in *; inv_sys.
    reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_file_outcome : forall fd buf count i m o p off data w,
  fd_lookup (m_fds m) fd = Some (FdFile p off) ->
  access_okb buf (bv_unsigned count) = true ->
  fs_lookup (m_fs m) p = Some data ->
  let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
  read_bytes_map (in_wmem i) buf (len_word bs) = Some w ->
  read_spec fd buf count i m o <->
  o = Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
         (with_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) m) [].
Proof.
  intros fd buf count i m o p off data w Hlk Hacc Hfs. cbv zeta. intros Hw.
  unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, Hacc in *; cbn [negb] in *;
      rewrite Hfs in *; cbv zeta in *; rewrite Hw in *; inv_sys; reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
    eexists _, _, _, _. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb].
    rewrite Hfs. cbv zeta. rewrite Hw.
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_reads (i : SyscallInput) (pathp : word) : list (word * nat) :=
  [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)].

(* [comment removed for export] *)
Definition after_copyins (R : list (word * nat)) (body : outcome SyscallEffect -> Prop)
    (o : outcome SyscallEffect) : Prop :=
  match o with
  | Ok eff m' evs => exists core, body (Ok core m' evs)
                                  /\ eff = with_copyins (R ++ eff_copyins core) core
  | Unmodeled => body Unmodeled
  end.

Lemma record_copyins_iff : forall R (spec : Sys SyscallEffect) i m o,
  record_copyins R spec i m o <-> after_copyins R (spec i m) o.
Proof.
  intros R spec i m o. unfold record_copyins, after_copyins, bind, pure.
  destruct o as [eff m' evs|]; split.
  - intros (core & m1 & evs1 & evs2 & Hc & Hp & ->). apply Ok_inj in Hp as (-> & -> & ->).
    exists core. rewrite app_nil_r. auto.
  - intros (core & Hc & ->). exists core, m', evs, []. rewrite app_nil_r. auto.
  - intros [H | (core & m1 & evs1 & _ & Hp)]; [exact H|]. exfalso. exact (Unmodeled_Ok _ _ _ Hp).
  - intros H. left. exact H.
Qed.

(* [comment removed for export] *)
Lemma after_copyins_det : forall R body r m0 evs0,
  (forall o, body o <-> o = Ok (mkEffect r [] []) m0 evs0) ->
  forall o, after_copyins R body o <-> o = Ok (with_copyins R (mkEffect r [] [])) m0 evs0.
Proof.
  intros R body r m0 evs0 Hb o. unfold after_copyins. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply Hb in Hc. apply Ok_inj in Hc as (-> & -> & ->).
    cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->). exists (mkEffect r [] []).
    split; [apply Hb; reflexivity|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Hb in H. exfalso. exact (Unmodeled_Ok _ _ _ H).
  - intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Definition open_res (m : Model) (mk : word -> Model) (o : outcome SyscallEffect) : Prop :=
  (exists e, In e openat_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
      /\ o = Ok (mkEffect (alloc_fd (m_fds m)) [] []) (mk (alloc_fd (m_fds m))) []).

(* [comment removed for export] *)
Definition open_out (R : list (word * nat)) (m : Model) (mk : word -> Model)
    (o : outcome SyscallEffect) : Prop :=
  (exists e, In e openat_errnos
             /\ o = Ok (with_copyins R (mkEffect (errno_ret e) [] [])) m [])
  \/ (fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None
      /\ o = Ok (with_copyins R (mkEffect (alloc_fd (m_fds m)) [] []))
                (mk (alloc_fd (m_fds m))) []).

Lemma open_result_outcome : forall m (mk : word -> Model -> Model) i o,
  open_result_spec m mk i m o <-> open_res m (fun fd => mk fd m) o.
Proof.
  intros m mk i o. unfold open_result_spec, open_res. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hfree & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [eexists; split; [split; [exact Hfree|reflexivity]|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma after_copyins_open : forall R body m mk,
  (forall o, body o <-> open_res m mk o) ->
  forall o, after_copyins R body o <-> open_out R m mk o.
Proof.
  intros R body m mk Hb o. unfold after_copyins, open_out. destruct o as [eff m' evs|]; split.
  - intros (core & Hc & ->). apply Hb in Hc.
    destruct Hc as [(e & He & Hc) | (Hfree & Hc)]; apply Ok_inj in Hc as (-> & -> & ->);
      cbn [eff_copyins]; rewrite app_nil_r.
    + left. exists e. auto.
    + right. auto.
  - intros [(e & He & H) | (Hfree & H)]; apply Ok_inj in H as (-> & -> & ->).
    + exists (mkEffect (errno_ret e) [] []). split; [apply Hb; left; exists e; auto|].
      cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
    + exists (mkEffect (alloc_fd (m_fds m)) [] []). split; [apply Hb; right; auto|].
      cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Hb in H. destruct H as [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
  - intros [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma openat_spec_body : forall dirfd pathp flags i m o,
  modeled_open_flags flags = true ->
  openat_spec dirfd pathp flags i m o <->
  after_copyins (open_reads i pathp) (openat_body_spec i m dirfd pathp flags i m) o.
Proof.
  intros dirfd pathp flags i m o Hfl. unfold openat_spec.
  transitivity (record_copyins (open_reads i pathp) (openat_core_spec dirfd pathp flags) i m o).
  { unfold bind, input, open_reads. destruct o as [eff m' evs|]; split.
    - intros (i0 & m1 & evs1 & evs2 & Hi & Hk & ->). apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
    - intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
    - intros [H | (i0 & m1 & evs1 & Hi & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H)|].
      apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
    - intros Hk. right. exists i, m, []. split; [reflexivity|exact Hk]. }
  rewrite record_copyins_iff.
  assert (Hcore : forall o', openat_core_spec dirfd pathp flags i m o' <->
                            openat_body_spec i m dirfd pathp flags i m o').
  { intros o'. unfold openat_core_spec. rewrite Hfl. cbn [negb].
    unfold bind, input, get_model. destruct o' as [eff m' evs|]; split.
    - intros (i0 & m1 & evs1 & evs2 & Hi & (m0 & m2 & evs3 & evs4 & Hm & Hb & ->) & ->).
      apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
    - intros Hb. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
      exists m, m, [], evs. split; [reflexivity|]. split; [exact Hb|reflexivity].
    - intros [H | (i0 & m1 & evs1 & Hi & [H | (m0 & m2 & evs2 & Hm & Hb)])];
        [exfalso; exact (Unmodeled_Ok _ _ _ H)| exfalso; exact (Unmodeled_Ok _ _ _ H)|].
      apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
    - intros Hb. right. exists i, m, []. split; [reflexivity|]. right.
      exists m, m, []. split; [reflexivity|exact Hb]. }
  unfold after_copyins. destruct o as [eff m' evs|]; [|apply Hcore].
  split; intros (core & Hc & ->); exists core; (split; [apply Hcore; exact Hc|reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma err_ret_outcome : forall e i m o,
  err_ret e i m o <-> o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof. intros. unfold err_ret, ret_only, pure. reflexivity. Qed.

Section Openat.
  Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
  Hypothesis Hfl : modeled_open_flags flags = true.

  (* [comment removed for export] *)
  Lemma openat_toolong_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrTooLong ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [].
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_empty_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk [] ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. cbn [path_eqb]. apply err_ret_outcome.
  Qed.

  Hypothesis Hdir : dirfd = AT_FDCWD32.
  Hypothesis Hrd : Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z.

  (* [comment removed for export] *)
  Lemma openat_body_resolved : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> path_has_slash p = false ->
    openat_body_spec i m dirfd pathp flags i m o <-> openat_read_spec p m i m o.
  Proof.
    intros p o Hp Hne Hsl. unfold openat_body_spec. rewrite Hp.
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec. rewrite Hsl, Hrd.
    reflexivity.
  Qed.

  Lemma path_is_dirref_false : forall p,
    p <> dot_path -> path_eqb p dotdot_path = false -> path_is_dirref p = false.
  Proof.
    intros p Hnd Hndd. unfold path_is_dirref. rewrite Hndd.
    destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_absent_outcome : forall p o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> p <> dot_path ->
    path_eqb p dotdot_path = false -> path_has_slash p = false ->
    fs_lookup (m_fs m) p = None ->
    openat_spec dirfd pathp flags i m o <->
    o = Ok (with_copyins (open_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
  Proof.
    intros p o Hp Hne Hnd Hndd Hsl Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl).
    apply after_copyins_det.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite (path_is_dirref_false p Hnd Hndd), Hfs. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_dot_outcome : forall o,
    read_cstr (in_mem i) pathp = CstrOk dot_path ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m) o.
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    assert (Hdr : path_is_dirref dot_path = true).
    { unfold path_is_dirref. rewrite path_eqb_refl. reflexivity. }
    intros o'. rewrite (openat_body_resolved dot_path o' Hp ltac:(discriminate)
                          (path_is_dirref_no_slash _ Hdr)).
    unfold openat_read_spec. rewrite Hdr. apply open_result_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_file_outcome : forall p d o,
    read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> p <> dot_path ->
    path_eqb p dotdot_path = false -> path_has_slash p = false ->
    fs_lookup (m_fs m) p = Some d ->
    openat_spec dirfd pathp flags i m o <->
    open_out (open_reads i pathp) m
      (fun fd => with_fds (fd_insert (m_fds m) fd (FdFile p (Z_to_bv 64 0))) m) o.
  Proof.
    intros p d o Hp Hne Hnd Hndd Hsl Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl).
    apply after_copyins_open.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite (path_is_dirref_false p Hnd Hndd), Hfs. apply open_result_outcome.
  Qed.
End Openat.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma import_iovecs_of_copy : forall mp a n iovs,
  w_is0 n = false ->
  (bv_unsigned n <= IOV_MAX)%Z ->
  access_okb a (16 * bv_unsigned n) = true ->
  copy_iovecs_aux mp a (word_to_nat n) = ImpOk iovs ->
  iovs_access_okb iovs = true ->
  import_iovecs mp a n = ImpOk iovs
  /\ import_iovecs_accesses mp a n = copy_iovecs_accesses mp a (word_to_nat n).
Proof.
  intros mp a n iovs Hn0 Hmax Hacc Hcopy Hok. unfold import_iovecs, import_iovecs_accesses.
  unfold w_is0 in Hn0. rewrite Hn0.
  destruct (bv_eqb n (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. subst n.
    assert (H1 : bv_unsigned (Z_to_bv 64 1) = 1%Z).
    { apply Z_to_bv_small. unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia. }
    rewrite H1 in Hacc. change (16 * 1)%Z with 16%Z in Hacc. rewrite Hacc. cbn [negb].
    unfold word_to_nat in *. rewrite H1 in *. change (Z.to_nat 1) with 1%nat in *.
    cbn [copy_iovecs_aux] in Hcopy. cbn [copy_iovecs_accesses].
    destruct (read_iovec_entry mp a) as [base len| |] eqn:Hre; [|discriminate Hcopy|discriminate Hcopy].
    cbn in Hcopy. injection Hcopy as <-. cbn [copy_iovecs_accesses].
    cbn in Hok. rewrite andb_true_r in Hok.
    assert (Hok' : access_okb base (Z.min (bv_unsigned len) MAX_RW_COUNT) = true).
    { unfold access_okb in *. apply andb_true_iff in Hok as [Hl Hb].
      apply Z.leb_le in Hl. apply Z.leb_le in Hb.
      apply andb_true_iff; split; apply Z.leb_le; lia. }
    rewrite Hok'. split; reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _) Hmax), Hacc. cbn [negb]. rewrite Hcopy, Hok.
    split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma writev_chan_zero_outcome : forall fd iov iovcnt i m o ch iovs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  w_is0 ch = false ->
  iovcnt32 iovcnt = iovcnt ->
  w_is0 iovcnt = false ->
  (bv_unsigned iovcnt <= IOV_MAX)%Z ->
  access_okb iov (16 * bv_unsigned iovcnt) = true ->
  copy_iovecs_aux (in_mem i) iov (word_to_nat iovcnt) = ImpOk iovs ->
  iovs_access_okb iovs = true ->
  iovs_total iovs = 0%Z ->
  (0 <= rw_bytes_max)%Z ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (copy_iovecs_accesses (in_mem i) iov (word_to_nat iovcnt))
                       (mkEffect (Z_to_bv 64 0) [] [])) m [].
Proof.
  intros fd iov iovcnt i m o ch iovs Hfd Hch Hcnt32 Hcnt0 Hcntmax Hacc Hcopy Hokb Htot Hmax.
  destruct (import_iovecs_of_copy _ _ _ _ Hcnt0 Hcntmax Hacc Hcopy Hokb) as [Himp Hacs].
  unfold writev_spec. rewrite Hcnt32.
  transitivity
    (record_copyins (copy_iovecs_accesses (in_mem i) iov (word_to_nat iovcnt))
       (ret_only (Z_to_bv 64 0)) i m o).
  { assert (Hbody : forall (k : SyscallInput -> Model -> Sys SyscallEffect),
      (bind input (fun i0 => bind get_model (fun m0 => k i0 m0))) i m o <-> k i m i m o).
    { intros k. unfold bind, input, get_model. destruct o as [eff m' evs|]; split.
      - intros (i0 & m1 & e1 & e2 & Hi & (m0 & m2 & e3 & e4 & Hm & Hk & ->) & ->).
        apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
      - intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
        exists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
      - intros [H | (i0 & m1 & e1 & Hi & [H | (m0 & m2 & e2 & Hm & Hk)])];
          [exfalso; exact (Unmodeled_Ok _ _ _ H) | exfalso; exact (Unmodeled_Ok _ _ _ H) |].
        apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
      - intros Hk. right. exists i, m, []. split; [reflexivity|]. right.
        exists m, m, []. split; [reflexivity| exact Hk]. }
    rewrite (Hbody (fun i0 m0 => _)). cbv beta.
    rewrite Hfd, Hch, Himp, Hacs. cbv zeta.
    rewrite iovs_total_cap, Htot. cbn [Z.min Z.eqb].
    reflexivity. }
  rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.

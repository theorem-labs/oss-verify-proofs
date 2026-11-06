(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pru_spec : forall x, x <= page_round_up_Z x <= x + 4095 /\ page_round_up_Z x mod 4096 = 0.
Proof.
  intros x. unfold page_round_up_Z. change page_size with 4096.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)) as M.
  split; [lia|]. apply Z_mod_mult.
Qed.

Lemma pru_of_aligned : forall x, x mod 4096 = 0 -> page_round_up_Z x = x.
Proof.
  intros x Hx. unfold page_round_up_Z. change page_size with 4096.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
  replace (x + 4096 - 1) with (x / 4096 * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

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
Theorem vm_gap_available_of_sum_from : forall h nZ a0,
  0 <= nZ -> 4096 <= a0 -> a0 mod 4096 = 0 ->
  (forall e, In e (vm_reserved h) -> elo e + esz e <= a0) ->
  a0 + zsumf (jcost nZ) (vm_maps h) + nZ <= alloc_top h ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ a0 HnZ Ha0 Hal0 Hres Hroom. pose proof (alloc_top_lt h) as Hc64.
  destruct (sweep nZ HnZ (vm_maps h) a0 Hal0) as (a' & A1 & A2 & A3 & A4).
  assert (HaW : bv_unsigned (Z_to_bv 64 a') = a')
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  apply (vm_gap_available_complete h nZ (Z_to_bv 64 a')); rewrite ?HaW; change page_size with 4096; try lia; try exact A2.
  apply region_free_intro. intros b s Hin. unfold iv_overlap. rewrite HaW, HnW. apply in_app_or in Hin as [Hin|Hin].
  - specialize (Hres (b, s) Hin). unfold elo, esz in Hres. cbn [fst snd] in Hres.
    apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - specialize (A4 (b, s) Hin). unfold zover, elo, esz in A4. cbn [fst snd] in A4. exact A4.
Qed.

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
Lemma count_le_bytes : forall l, (forall e, In e l -> 4096 <= esz e) -> 4096 * Z.of_nat (length l) <= zsumf esz l.
Proof.
  induction l as [|e l IH]; intros H; cbn [zsumf fold_right length]; [lia|]. fold (zsumf esz l).
  pose proof (H e (or_introl eq_refl)). pose proof (IH (fun x Hx => H x (or_intror Hx))). lia.
Qed.

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

Lemma mprotect_not_refusable : forall m addr n,
  mprotect_budget_ok m addr n = true -> mprotect_refusable m addr n = false.
Proof. intros m addr n H. unfold mprotect_refusable. rewrite H. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary vm_gap_available_of_count : forall h nZ K S,
  0 <= nZ ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= K ->
  zsumf esz (vm_reserved h ++ vm_maps h) <= S ->
  page_size + S + (K + 1) * (nZ + 4095) <= alloc_top h ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ K S HnZ HK HS Hroom. apply (vm_gap_available_of_bounds h nZ K S HnZ HK HS).
  change page_size with 4096 in Hroom. lia.
Qed.

(* [comment removed for export] *)
Corollary mmap_reserve_not_refusable_of_base : forall m nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a HnZ Hal Hpos Htop Hfree. apply mmap_reserve_not_refusable.
  exact (vm_gap_available_complete (m_vmmaps m) nZ a HnZ Hal Hpos Htop Hfree).
Qed.

Corollary mmap_grant_not_refusable_of_base : forall flags m nZ (a : word),
  0 <= nZ ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a HnZ Hal Hpos Htop Hfree Hbk. unfold mmap_grant_refusable.
  rewrite (vm_gap_available_complete (m_vmmaps m) nZ a HnZ Hal Hpos Htop Hfree), Hbk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_fresh_not_refusable : forall flags m nZ,
  mmap_noreserve_backed_ok flags m nZ = true -> mmap_fixed_fresh_refusable flags m nZ = false.
Proof. intros flags m nZ H. unfold mmap_fixed_fresh_refusable. rewrite H. reflexivity. Qed.

Lemma mmap_fixed_commit_not_refusable : forall flags m addr n,
  mmap_fixed_rw_budget_ok flags m addr n = true -> mmap_fixed_commit_refusable flags m addr n = false.
Proof. intros flags m addr n H. unfold mmap_fixed_commit_refusable. rewrite H. reflexivity. Qed.

Lemma mmap_fixed_span_not_refusable : forall flags m addr n,
  mmap_fixed_rw_span_budget_ok flags m addr n = true -> mmap_fixed_span_refusable flags m addr n = false.
Proof. intros flags m addr n H. unfold mmap_fixed_span_refusable. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof. reflexivity. Qed.

Lemma mmap_errnos_when_true : mmap_errnos_when true = mmap_errnos.
Proof. reflexivity. Qed.

Lemma mmap_destructive_errnos_nil : mmap_destructive_errnos = [].
Proof. reflexivity. Qed.

Lemma mprotect_errnos_when_false : mprotect_errnos_when false = [].
Proof. reflexivity. Qed.

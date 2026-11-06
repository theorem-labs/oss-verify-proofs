(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.

Module Lazylo0.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim MmapSim ShapeAlg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.
Import ListNotations.
Open Scope bv_scope.

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

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).

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

End WithSegs.
End Lazylo0.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Ledger.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull.Lazylo0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_modulus : bv_modulus 64 = (2 ^ 64)%Z.
Proof. reflexivity. Qed.

Lemma page_size_pos : (0 < page_size)%Z.
Proof. unfold page_size; lia. Qed.

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

Lemma u64_bound : forall w : word, (0 <= bv_unsigned w < 2 ^ 64)%Z.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w). rewrite two64_modulus in H. exact H. Qed.

Lemma Z_to_bv64_unsigned_small : forall z,
  (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  rewrite two64_modulus. exact Hz.
Qed.

(* [comment removed for export] *)
Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
  intros a. unfold woff. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma woff_unsigned : forall a k,
  bv_unsigned (woff a k) = ((bv_unsigned a + Z.of_nat k) mod 2 ^ 64)%Z.
Proof.
  intros a k. unfold woff. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma woff_small : forall a k,
  (bv_unsigned a + Z.of_nat k < 2 ^ 64)%Z ->
  bv_unsigned (woff a k) = (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  intros a k H. rewrite woff_unsigned. apply Z.mod_small.
  pose proof (u64_bound a). lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_of_unsigned : forall z,
  (0 <= z)%Z ->
  bv_unsigned (page_base_of z) = ((z mod 2 ^ 64) / page_size * page_size)%Z.
Proof.
  intros z Hz. unfold page_base_of. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64_modulus, two64_as_pages.
  set (M := (2 ^ 52)%Z).
  assert (HM : (0 < M)%Z) by (unfold M; lia).
  pose proof page_size_pos as Hps.
  rewrite (Z.rem_mul_r z page_size M) by lia.
  replace (z / page_size * page_size)%Z with (page_size * (z / page_size))%Z by lia.
  rewrite Zmult_mod_distr_l.
  replace (z mod page_size + page_size * (z / page_size mod M))%Z
    with ((z / page_size mod M) * page_size + z mod page_size)%Z by lia.
  rewrite Z.div_add_l by lia.
  rewrite (Z.div_small (z mod page_size) page_size) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

Lemma page_base_of_aligned : forall z,
  (0 <= z)%Z -> (bv_unsigned (page_base_of z) mod page_size = 0)%Z.
Proof.
  intros z Hz. rewrite (page_base_of_unsigned z Hz). apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma page_base_of_brackets : forall a k,
  let p := bv_unsigned (page_base_of (bv_unsigned a + Z.of_nat k)) in
  let x := bv_unsigned (woff a k) in
  (p <= x < p + page_size)%Z.
Proof.
  intros a k. cbn. pose proof (u64_bound a) as Ha.
  rewrite page_base_of_unsigned by lia. rewrite woff_unsigned.
  set (x := ((bv_unsigned a + Z.of_nat k) mod 2 ^ 64)%Z).
  assert (Hx : (0 <= x)%Z) by (unfold x; apply Z.mod_pos_bound; lia).
  pose proof page_size_pos.
  pose proof (Z.div_mod x page_size ltac:(lia)).
  pose proof (Z.mod_pos_bound x page_size ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hull := list (Z * Z).

Definition in_ivb (x : Z) (iv : Z * Z) : bool :=
  ((fst iv <=? x) && (x <? snd iv))%Z.

Definition in_hullb (A : hull) (x : Z) : bool := existsb (in_ivb x) A.

(* [comment removed for export] *)
Definition page_meets_ivb (p : Z) (iv : Z * Z) : bool :=
  ((fst iv <? p + page_size) && (p <? snd iv))%Z.

Definition page_hullb (A : hull) (p : Z) : bool := existsb (page_meets_ivb p) A.

(* [comment removed for export] *)
Definition hull_npages (iv : Z * Z) : nat :=
  Z.to_nat ((snd iv - 1) / page_size - fst iv / page_size + 1)%Z.

Fixpoint hull_bytes (A : hull) : Z :=
  match A with
  | [] => 0%Z
  | iv :: A' => (page_size * Z.of_nat (hull_npages iv) + hull_bytes A')%Z
  end.

Lemma in_ivb_true : forall x lo hi,
  in_ivb x (lo, hi) = true <-> (lo <= x < hi)%Z.
Proof.
  intros. unfold in_ivb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma in_hullb_true : forall A x,
  in_hullb A x = true <-> exists lo hi, In (lo, hi) A /\ (lo <= x < hi)%Z.
Proof.
  intros A x. unfold in_hullb. rewrite existsb_exists. split.
  - ((first [ intro dR_11; dand3 dR_11 as [lo hi] Hin Hb | intros ([lo hi] & Hin & Hb) ])). exists lo, hi. split; [exact Hin | apply in_ivb_true; exact Hb].
  - ((first [ intro dR_12; dex2 dR_12 as lo hi; destruct dR_12 as [Hin Hb] | intro dR_12; dand4 dR_12 as lo hi Hin Hb | intros (lo & hi & Hin & Hb) ])). exists (lo, hi). split; [exact Hin | apply in_ivb_true; exact Hb].
Qed.

Lemma in_hullb_intro : forall A x lo hi,
  In (lo, hi) A -> (lo <= x < hi)%Z -> in_hullb A x = true.
Proof. intros. apply in_hullb_true. eauto. Qed.

Lemma page_meets_ivb_true : forall p lo hi,
  page_meets_ivb p (lo, hi) = true <-> (lo < p + page_size /\ p < hi)%Z.
Proof.
  intros. unfold page_meets_ivb. cbn [fst snd]. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma page_hullb_true : forall A p,
  page_hullb A p = true <-> exists lo hi, In (lo, hi) A /\ (lo < p + page_size /\ p < hi)%Z.
Proof.
  intros A p. unfold page_hullb. rewrite existsb_exists. split.
  - ((first [ intro dR_13; dand3 dR_13 as [lo hi] Hin Hb | intros ([lo hi] & Hin & Hb) ])). exists lo, hi. split; [exact Hin | apply page_meets_ivb_true; exact Hb].
  - ((first [ intro dR_14; dex2 dR_14 as lo hi; destruct dR_14 as [Hin Hb] | intro dR_14; dand4 dR_14 as lo hi Hin Hb | intros (lo & hi & Hin & Hb) ])). exists (lo, hi). split; [exact Hin | apply page_meets_ivb_true; exact Hb].
Qed.

(* [comment removed for export] *)
Lemma page_hullb_of_byte : forall A x p,
  in_hullb A x = true -> (p <= x < p + page_size)%Z -> page_hullb A p = true.
Proof.
  intros A x p Hx Hpx. apply in_hullb_true in Hx as (lo & hi & Hin & Hlohi).
  apply page_hullb_true. exists lo, hi. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Definition hull_le (A A' : hull) : Prop :=
  forall lo hi, In (lo, hi) A -> exists lo' hi', In (lo', hi') A' /\ (lo' <= lo)%Z /\ (hi <= hi')%Z.

Lemma hull_le_refl : forall A, hull_le A A.
Proof. intros A lo hi Hin. exists lo, hi. split; [exact Hin | lia]. Qed.

Lemma hull_le_incl : forall A A', incl A A' -> hull_le A A'.
Proof. intros A A' Hincl lo hi Hin. exists lo, hi. split; [apply Hincl; exact Hin | lia]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_hullb_mono : forall A A' x,
  hull_le A A' -> in_hullb A x = true -> in_hullb A' x = true.
Proof.
  intros A A' x Hle Hx. apply in_hullb_true in Hx as (lo & hi & Hin & Hb).
  (first [ pose proof ((Hle lo hi Hin)) as dR_3; dex2 dR_3 as lo' hi'; dand3 dR_3 as Hin' Hl Hh | pose proof ((Hle lo hi Hin)) as dR_3; dand5 dR_3 as lo' hi' Hin' Hl Hh | destruct (Hle lo hi Hin) as (lo' & hi' & Hin' & Hl & Hh) ]).
  apply in_hullb_true. exists lo', hi'. split; [exact Hin' | lia].
Qed.

Lemma page_hullb_mono : forall A A' p,
  hull_le A A' -> page_hullb A p = true -> page_hullb A' p = true.
Proof.
  intros A A' p Hle Hp. apply page_hullb_true in Hp as (lo & hi & Hin & Hb).
  (first [ pose proof ((Hle lo hi Hin)) as dR_4; dex2 dR_4 as lo' hi'; dand3 dR_4 as Hin' Hl Hh | pose proof ((Hle lo hi Hin)) as dR_4; dand5 dR_4 as lo' hi' Hin' Hl Hh | destruct (Hle lo hi Hin) as (lo' & hi' & Hin' & Hl & Hh) ]).
  apply page_hullb_true. exists lo', hi'. split; [exact Hin' | lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma hull_bytes_app : forall A B, hull_bytes (A ++ B) = (hull_bytes A + hull_bytes B)%Z.
Proof. induction A as [|iv A IH]; intros B; cbn [hull_bytes app]; [lia | rewrite IH; lia]. Qed.

Lemma hull_bytes_cons : forall iv A,
  hull_bytes (iv :: A) = (page_size * Z.of_nat (hull_npages iv) + hull_bytes A)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hull_npages_le : forall lo hi,
  (lo <= hi)%Z ->
  (page_size * Z.of_nat (hull_npages (lo, hi)) <= hi - lo + 2 * page_size)%Z.
Proof.
  intros lo hi Hle. unfold hull_npages. cbn [fst snd].
  pose proof page_size_pos as Hps.
  pose proof (Z.div_mod (hi - 1) page_size ltac:(lia)) as H1.
  pose proof (Z.mod_pos_bound (hi - 1) page_size ltac:(lia)) as H2.
  pose proof (Z.div_mod lo page_size ltac:(lia)) as H3.
  pose proof (Z.mod_pos_bound lo page_size ltac:(lia)) as H4.
  nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint hull_page_idx (A : hull) : list Z :=
  match A with
  | [] => []
  | iv :: A' =>
      map (fun i => (fst iv / page_size + Z.of_nat i)%Z) (seq 0 (hull_npages iv))
      ++ hull_page_idx A'
  end.

Lemma hull_page_idx_length : forall A,
  (page_size * Z.of_nat (length (hull_page_idx A)) = hull_bytes A)%Z.
Proof.
  induction A as [|iv A IH]; cbn [hull_page_idx hull_bytes]; [reflexivity|].
  rewrite length_app, length_map, length_seq, Nat2Z.inj_add. lia.
Qed.

Lemma hull_page_idx_in : forall A p,
  (p mod page_size = 0)%Z ->
  page_hullb A p = true ->
  In (p / page_size)%Z (hull_page_idx A).
Proof.
  induction A as [|[lo hi] A IH]; intros p Hal Hp; [discriminate|].
  cbn [hull_page_idx fst snd]. apply in_or_app.
  unfold page_hullb in Hp. cbn [existsb] in Hp. apply orb_true_iff in Hp as [Hp | Hp].
  - left. apply page_meets_ivb_true in Hp as [H1 H2].
    pose proof page_size_pos as Hps.
    pose proof (Z.div_mod p page_size ltac:(lia)) as Hdm. rewrite Hal in Hdm.
    set (q := (p / page_size)%Z) in *.
    assert (Hlo : (lo / page_size <= q)%Z).
    { apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
    assert (Hhi : (q <= (hi - 1) / page_size)%Z).
    { apply Z.div_le_lower_bound; lia. }
    apply in_map_iff. exists (Z.to_nat (q - lo / page_size)). split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. unfold hull_npages. cbn [fst snd]. lia.
  - right. apply IH; assumption.
Qed.

Lemma NoDup_map_div_aligned : forall (l : list word),
  List.NoDup l ->
  (forall p, In p l -> (bv_unsigned p mod page_size = 0)%Z) ->
  List.NoDup (map (fun p : word => (bv_unsigned p / page_size)%Z) l).
Proof.
  intros l Hnd Hal. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
    apply Hx. replace x with y; [exact Hiny|].
    apply bv_eq. pose proof page_size_pos.
    pose proof (Z.div_mod (bv_unsigned x) page_size ltac:(lia)) as Dx.
    pose proof (Z.div_mod (bv_unsigned y) page_size ltac:(lia)) as Dy.
    rewrite (Hal x (or_introl eq_refl)) in Dx. rewrite (Hal y (or_intror Hiny)) in Dy. lia.
  - apply IH. intros p Hp. apply Hal. right. exact Hp.
Qed.

Theorem hull_pages_bound : forall A (pages : list word),
  List.NoDup pages ->
  (forall p, In p pages -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p pages -> page_hullb A (bv_unsigned p) = true) ->
  (Z.of_nat (length pages) * page_size <= hull_bytes A)%Z.
Proof.
  intros A pages Hnd Hal Hin.
  rewrite <- hull_page_idx_length.
  assert (Hlen : (length pages <= length (hull_page_idx A))%nat).
  { rewrite <- (length_map (fun p : word => (bv_unsigned p / page_size)%Z) pages).
    apply NoDup_incl_length.
    - apply NoDup_map_div_aligned; assumption.
    - intros q Hq. apply in_map_iff in Hq as (p & <- & Hp).
      apply hull_page_idx_in; [exact (Hal p Hp) | exact (Hin p Hp)]. }
  pose proof page_size_pos. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bytes_in_hull (A : hull) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> in_hullb A (bv_unsigned (woff a k)) = true.

Definition accs_in_hull (A : hull) (accs : list (word * nat)) : Prop :=
  forall a n, In (a, n) accs -> bytes_in_hull A a n.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma bytes_in_hull_shrink : forall A a n n',
  (n' <= n)%nat -> bytes_in_hull A a n -> bytes_in_hull A a n'.
Proof. intros A a n n' Hle H k Hk. apply H. lia. Qed.

Lemma accs_in_hull_nil : forall A, accs_in_hull A [].
Proof. intros A a n []. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma accs_in_hull_app : forall A accs1 accs2,
  accs_in_hull A accs1 -> accs_in_hull A accs2 -> accs_in_hull A (accs1 ++ accs2).
Proof.
  intros A l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

Lemma accs_in_hull_app_inv : forall A accs1 accs2,
  accs_in_hull A (accs1 ++ accs2) -> accs_in_hull A accs1 /\ accs_in_hull A accs2.
Proof.
  intros A l1 l2 H. split; intros a n Hin; apply H; apply in_or_app; [left | right]; exact Hin.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition charged_pages_in_hull (A : hull) (lazy : list (word * word))
    (accs : list (word * nat)) : Prop :=
  forall p, In p (accesses_pages accs []) ->
            page_in_ranges p lazy = true ->
            page_hullb A (bv_unsigned p) = true.

Lemma charged_pages_in_hull_of_accs : forall A lazy accs,
  accs_in_hull A accs -> charged_pages_in_hull A lazy accs.
Proof.
  intros A lazy accs H p Hp _.
  destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
  pose proof (page_base_of_brackets a k) as Hb. cbn in Hb.
  eapply page_hullb_of_byte; [exact (H a n Hin k Hk) | exact Hb].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition acc_hull_or_outside (A : hull) (lazy : list (word * word))
    (a : word) (n : nat) : Prop :=
  bytes_in_hull A a n \/ (forall lo sz, In (lo, sz) lazy -> access_outside_range a n lo sz).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lazy_free (lazy : list (word * word)) (lo hi : Z) : Prop :=
  forall x, (lo <= x < hi)%Z -> zcovb lazy x = false.

(* [comment removed for export] *)
Definition iv_sub (AL : hull) (lo hi : Z) : Prop :=
  exists lo' hi', In (lo', hi') AL /\ (lo' <= lo)%Z /\ (hi <= hi')%Z.

(* [comment removed for export] *)
Definition hull_cover (A AL : hull) (lazy : list (word * word)) : Prop :=
  forall lo hi, In (lo, hi) A -> iv_sub AL lo hi \/ lazy_free lazy lo hi.

Lemma iv_sub_In : forall AL lo hi, In (lo, hi) AL -> iv_sub AL lo hi.
Proof. intros AL lo hi H. exists lo, hi. split; [exact H | lia]. Qed.

Lemma iv_sub_shrink : forall AL lo hi lo' hi',
  iv_sub AL lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> iv_sub AL lo' hi'.
Proof.
  intros AL lo hi lo' hi' (l & h & Hin & Hl & Hh) H1 H2. exists l, h. split; [exact Hin | lia].
Qed.

Lemma iv_sub_mono : forall AL AL' lo hi, hull_le AL AL' -> iv_sub AL lo hi -> iv_sub AL' lo hi.
Proof.
  intros AL AL' lo hi Hle (l & h & Hin & Hl & Hh).
  destruct (Hle l h Hin) as (l' & h' & Hin' & Hl' & Hh'). exists l', h'. split; [exact Hin' | lia].
Qed.

Lemma iv_sub_trans : forall A AL lo hi,
  iv_sub A lo hi -> (forall l h, In (l, h) A -> iv_sub AL l h) -> iv_sub AL lo hi.
Proof.
  intros A AL lo hi (l & h & Hin & Hl & Hh) HA.
  destruct (HA l h Hin) as (l' & h' & Hin' & Hl' & Hh'). exists l', h'. split; [exact Hin' | lia].
Qed.

Lemma iv_sub_app_l : forall AL1 AL2 lo hi, iv_sub AL1 lo hi -> iv_sub (AL1 ++ AL2) lo hi.
Proof. intros AL1 AL2 lo hi (l & h & Hin & X). exists l, h. split; [apply in_or_app; left; exact Hin | exact X]. Qed.

Lemma iv_sub_app_r : forall AL1 AL2 lo hi, iv_sub AL2 lo hi -> iv_sub (AL1 ++ AL2) lo hi.
Proof. intros AL1 AL2 lo hi (l & h & Hin & X). exists l, h. split; [apply in_or_app; right; exact Hin | exact X]. Qed.

Lemma lazy_free_nil : forall lo hi, lazy_free [] lo hi.
Proof. intros lo hi x _. reflexivity. Qed.

Lemma lazy_free_empty : forall lazy lo hi, (hi <= lo)%Z -> lazy_free lazy lo hi.
Proof. intros lazy lo hi H x Hx. lia. Qed.

Lemma lazy_free_shrink : forall lazy lo hi lo' hi',
  lazy_free lazy lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> lazy_free lazy lo' hi'.
Proof. intros lazy lo hi lo' hi' H H1 H2 x Hx. apply H. lia. Qed.

(* [comment removed for export] *)
Definition lazy_sub (lazy' lazy : list (word * word)) : Prop :=
  forall x, zcovb lazy' x = true -> zcovb lazy x = true.

Lemma lazy_sub_refl : forall lazy, lazy_sub lazy lazy.
Proof. intros lazy x H. exact H. Qed.

Lemma lazy_sub_eq : forall lazy lazy', lazy' = lazy -> lazy_sub lazy' lazy.
Proof. intros lazy lazy' ->. apply lazy_sub_refl. Qed.

Lemma lazy_sub_trans : forall l1 l2 l3, lazy_sub l1 l2 -> lazy_sub l2 l3 -> lazy_sub l1 l3.
Proof. intros l1 l2 l3 H1 H2 x Hx. exact (H2 x (H1 x Hx)). Qed.

Lemma lazy_sub_nil_app : forall lazy, lazy_sub ([] ++ lazy) lazy.
Proof. intros lazy x H. exact H. Qed.

Lemma lazy_sub_subtract : forall lazy l h,
  entries_nowrap lazy -> (0 <= l)%Z -> (l <= h)%Z -> lazy_sub (maps_subtract lazy l h) lazy.
Proof.
  intros lazy l h Hnw Hl Hh x Hx. rewrite (zcovb_maps_subtract lazy l h x Hnw Hl Hh) in Hx.
  apply andb_true_iff in Hx as [Hx _]. exact Hx.
Qed.

Lemma lazy_free_mono : forall lazy lazy' lo hi,
  lazy_sub lazy' lazy -> lazy_free lazy lo hi -> lazy_free lazy' lo hi.
Proof.
  intros lazy lazy' lo hi Hs H x Hx. destruct (zcovb lazy' x) eqn:E; [|reflexivity].
  pose proof (Hs x E) as C. rewrite (H x Hx) in C. discriminate C.
Qed.

Lemma lazy_free_app : forall l1 l2 lo hi,
  lazy_free l1 lo hi -> lazy_free l2 lo hi -> lazy_free (l1 ++ l2) lo hi.
Proof. intros l1 l2 lo hi H1 H2 x Hx. rewrite zcovb_app, (H1 x Hx), (H2 x Hx). reflexivity. Qed.

(* [comment removed for export] *)
Lemma lazy_free_subtract : forall lazy l h,
  entries_nowrap lazy -> (0 <= l)%Z -> (l <= h)%Z -> lazy_free (maps_subtract lazy l h) l h.
Proof.
  intros lazy l h Hnw Hl Hh x Hx. rewrite (zcovb_maps_subtract lazy l h x Hnw Hl Hh).
  replace (zinb l h x) with true; [apply andb_false_r|]. symmetry. apply zinb_true. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma lazy_free_page : forall lazy lo hi (p : word) x,
  lazy_free lazy lo hi -> (lo <= x < hi)%Z ->
  (bv_unsigned p <= x < bv_unsigned p + page_size)%Z ->
  page_in_ranges p lazy = true -> False.
Proof.
  intros lazy lo hi p x Hf Hx Hpx Hpg.
  unfold page_in_ranges in Hpg. apply existsb_exists in Hpg as [[b k] [Hin Hb]]. cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  assert (C : zcovb lazy x = true).
  { apply zcovb_true. exists (b, k). split; [exact Hin|]. unfold Ledger.lo, Ledger.hi. cbn [fst snd]. lia. }
  rewrite (Hf x Hx) in C. discriminate C.
Qed.

(* [comment removed for export] *)
Lemma hull_cover_nil : forall AL lazy, hull_cover [] AL lazy.
Proof. intros AL lazy lo hi []. Qed.

Lemma hull_cover_self : forall A lazy, hull_cover A A lazy.
Proof. intros A lazy lo hi Hin. left. apply iv_sub_In. exact Hin. Qed.

Lemma hull_cover_of_incl : forall A AL lazy, incl A AL -> hull_cover A AL lazy.
Proof. intros A AL lazy Hincl lo hi Hin. left. apply iv_sub_In. apply Hincl. exact Hin. Qed.

Lemma hull_cover_app : forall A1 A2 AL lazy,
  hull_cover A1 AL lazy -> hull_cover A2 AL lazy -> hull_cover (A1 ++ A2) AL lazy.
Proof.
  intros A1 A2 AL lazy H1 H2 lo hi Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 lo hi Hin) | exact (H2 lo hi Hin)].
Qed.

Lemma hull_cover_app_inv : forall A1 A2 AL lazy,
  hull_cover (A1 ++ A2) AL lazy -> hull_cover A1 AL lazy /\ hull_cover A2 AL lazy.
Proof.
  intros A1 A2 AL lazy H. split; intros lo hi Hin; apply H; apply in_or_app; [left | right]; exact Hin.
Qed.

Lemma hull_cover_cons : forall iv A AL lazy,
  (iv_sub AL (fst iv) (snd iv) \/ lazy_free lazy (fst iv) (snd iv)) ->
  hull_cover A AL lazy -> hull_cover (iv :: A) AL lazy.
Proof.
  intros [lo0 hi0] A AL lazy H0 H lo hi [E|Hin]; [injection E as <- <-; exact H0 | exact (H lo hi Hin)].
Qed.

Lemma hull_cover_cons_inv : forall iv A AL lazy,
  hull_cover (iv :: A) AL lazy ->
  (iv_sub AL (fst iv) (snd iv) \/ lazy_free lazy (fst iv) (snd iv)) /\ hull_cover A AL lazy.
Proof.
  intros [lo0 hi0] A AL lazy H. split; [exact (H lo0 hi0 (or_introl eq_refl))|].
  intros lo hi Hin. exact (H lo hi (or_intror Hin)).
Qed.

(* [comment removed for export] *)
Lemma hull_cover_hull_le : forall A A' AL lazy,
  hull_le A' A -> hull_cover A AL lazy -> hull_cover A' AL lazy.
Proof.
  intros A A' AL lazy Hle H lo hi Hin.
  destruct (Hle lo hi Hin) as (l & h & Hin0 & Hl & Hh).
  destruct (H l h Hin0) as [S|F].
  - left. exact (iv_sub_shrink AL l h lo hi S Hl Hh).
  - right. exact (lazy_free_shrink lazy l h lo hi F Hl Hh).
Qed.

Lemma hull_cover_incl : forall A A' AL lazy, incl A' A -> hull_cover A AL lazy -> hull_cover A' AL lazy.
Proof. intros A A' AL lazy Hi. apply hull_cover_hull_le. apply hull_le_incl. exact Hi. Qed.

(* [comment removed for export] *)
Lemma hull_cover_mono_AL : forall A AL AL' lazy,
  hull_le AL AL' -> hull_cover A AL lazy -> hull_cover A AL' lazy.
Proof.
  intros A AL AL' lazy Hle H lo hi Hin. destruct (H lo hi Hin) as [S|F]; [left; exact (iv_sub_mono AL AL' lo hi Hle S) | right; exact F].
Qed.

(* [comment removed for export] *)
Lemma hull_cover_lazy_mono : forall A AL lazy lazy',
  lazy_sub lazy' lazy -> hull_cover A AL lazy -> hull_cover A AL lazy'.
Proof.
  intros A AL lazy lazy' Hs H lo hi Hin. destruct (H lo hi Hin) as [S|F]; [left; exact S | right; exact (lazy_free_mono lazy lazy' lo hi Hs F)].
Qed.

(* [comment removed for export] *)
Lemma hull_cover_grow : forall A AL A' AL' lazy,
  hull_cover A AL lazy -> hull_le AL AL' ->
  (forall lo hi, In (lo, hi) A' -> iv_sub A lo hi \/ iv_sub AL' lo hi \/ lazy_free lazy lo hi) ->
  hull_cover A' AL' lazy.
Proof.
  intros A AL A' AL' lazy H Hle HX lo hi Hin. destruct (HX lo hi Hin) as [S|[S|F]]; [| left; exact S | right; exact F].
  destruct S as (l & h & Hin0 & Hl & Hh). destruct (H l h Hin0) as [S0|F0].
  - left. apply (iv_sub_mono AL AL' lo hi Hle). exact (iv_sub_shrink AL l h lo hi S0 Hl Hh).
  - right. exact (lazy_free_shrink lazy l h lo hi F0 Hl Hh).
Qed.

(* [comment removed for export] *)
Lemma charged_pages_in_hull_of_cover : forall A AL lazy accs,
  hull_cover A AL lazy -> accs_in_hull A accs -> charged_pages_in_hull AL lazy accs.
Proof.
  intros A AL lazy accs HC H p Hp Hpg.
  destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
  pose proof (page_base_of_brackets a k) as Hb. cbn in Hb.
  pose proof (H a n Hin k Hk) as Hx. apply in_hullb_true in Hx as (lo & hi & Hlh & Hxin).
  destruct (HC lo hi Hlh) as [(l & h & HinL & Hl & Hh) | F].
  - apply page_hullb_true. exists l, h. split; [exact HinL | lia].
  - exfalso. exact (lazy_free_page lazy lo hi _ _ F Hxin Hb Hpg).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record MInv (A AL : hull) (E : Z) (m : Model) : Prop := mkMInv {
  minv_nodup     : List.NoDup (m_vm_materialized m);
  minv_aligned   : forall p, In p (m_vm_materialized m) -> (bv_unsigned p mod page_size = 0)%Z;
  minv_hull      : forall p, In p (m_vm_materialized m) -> page_hullb AL (bv_unsigned p) = true;
  minv_cover     : hull_cover A AL (m_vm_lazy m);
  minv_lazy_nw   : entries_nowrap (m_vm_lazy m);
  minv_maps_nw   : entries_nowrap (vm_maps (m_vmmaps m));
  minv_noacc_nw  : entries_nowrap (vm_noaccess (m_vmmaps m));
  minv_nooverlap : nooverlap (vm_maps (m_vmmaps m));
  minv_eager     : (eager_used m <= E)%Z;
  minv_budget    : (E + hull_bytes AL <= vm_limit (m_vmmaps m))%Z
}.

Arguments minv_nodup {A AL E m} _.
Arguments minv_aligned {A AL E m} _.
Arguments minv_hull {A AL E m} _.
Arguments minv_cover {A AL E m} _.
Arguments minv_lazy_nw {A AL E m} _.
Arguments minv_maps_nw {A AL E m} _.
Arguments minv_noacc_nw {A AL E m} _.
Arguments minv_nooverlap {A AL E m} _.
Arguments minv_eager {A AL E m} _.
Arguments minv_budget {A AL E m} _.

(* [comment removed for export] *)
Lemma MInv_backing_used_le : forall A AL E m,
  MInv A AL E m -> (vm_backing_used m <= E + hull_bytes AL)%Z.
Proof.
  intros A AL E m HI. rewrite vm_backing_used_split.
  pose proof (hull_pages_bound AL (m_vm_materialized m) (minv_nodup HI) (minv_aligned HI) (minv_hull HI)).
  pose proof (minv_eager HI). lia.
Qed.

(* [comment removed for export] *)
Lemma MInv_cover_In : forall A AL E m lo hi,
  MInv A AL E m -> In (lo, hi) A -> iv_sub AL lo hi \/ lazy_free (m_vm_lazy m) lo hi.
Proof. intros A AL E m lo hi HI Hin. exact (minv_cover HI lo hi Hin). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem MInv_hull_mono : forall A AL A' AL' E E' m,
  MInv A AL E m ->
  hull_le AL AL' ->
  (forall lo hi, In (lo, hi) A' -> iv_sub A lo hi \/ iv_sub AL' lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  (E <= E')%Z ->
  (E' + hull_bytes AL' <= vm_limit (m_vmmaps m))%Z ->
  MInv A' AL' E' m.
Proof.
  intros A AL A' AL' E E' m HI Hle HX HE Hb. constructor.
  - exact (minv_nodup HI).
  - exact (minv_aligned HI).
  - intros p Hp. exact (page_hullb_mono AL AL' _ Hle (minv_hull HI p Hp)).
  - exact (hull_cover_grow A AL A' AL' _ (minv_cover HI) Hle HX).
  - exact (minv_lazy_nw HI).
  - exact (minv_maps_nw HI).
  - exact (minv_noacc_nw HI).
  - exact (minv_nooverlap HI).
  - pose proof (minv_eager HI). lia.
  - exact Hb.
Qed.

(* [comment removed for export] *)
Corollary MInv_hull_mono_incl : forall A AL A' AL' E E' m,
  MInv A AL E m ->
  incl AL AL' ->
  (forall lo hi, In (lo, hi) A' -> In (lo, hi) A \/ In (lo, hi) AL' \/ lazy_free (m_vm_lazy m) lo hi) ->
  (E <= E')%Z ->
  (E' + hull_bytes AL' <= vm_limit (m_vmmaps m))%Z ->
  MInv A' AL' E' m.
Proof.
  intros A AL A' AL' E E' m HI Hincl HX HE Hb.
  apply (MInv_hull_mono A AL A' AL' E E' m HI (hull_le_incl _ _ Hincl)); [| exact HE | exact Hb].
  intros lo hi Hin. destruct (HX lo hi Hin) as [H|[H|H]];
    [left; apply iv_sub_In; exact H | right; left; apply iv_sub_In; exact H | right; right; exact H].
Qed.

(* [comment removed for export] *)
Corollary MInv_hull_mono_same : forall A AL E E' m,
  MInv A AL E m -> (E <= E')%Z -> (E' + hull_bytes AL <= vm_limit (m_vmmaps m))%Z -> MInv A AL E' m.
Proof.
  intros A AL E E' m HI HE Hb.
  apply (MInv_hull_mono A AL A AL E E' m HI (hull_le_refl AL)); [| exact HE | exact Hb].
  intros lo hi Hin. left. apply iv_sub_In. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma MInv_vm_frame : forall A AL E m m',
  m_vm m' = m_vm m -> MInv A AL E m -> MInv A AL E m'.
Proof.
  intros A AL E m m' Hvm HI.
  assert (H1 : m_vm_materialized m' = m_vm_materialized m) by (unfold m_vm_materialized; rewrite Hvm; reflexivity).
  assert (H2 : m_vm_lazy m' = m_vm_lazy m) by (unfold m_vm_lazy; rewrite Hvm; reflexivity).
  assert (H3 : m_vmmaps m' = m_vmmaps m) by (unfold m_vmmaps; rewrite Hvm; reflexivity).
  assert (H4 : eager_used m' = eager_used m) by (unfold eager_used; rewrite H2, H3; reflexivity).
  constructor; rewrite ?H1, ?H2, ?H3, ?H4;
    [exact (minv_nodup HI) | exact (minv_aligned HI) | exact (minv_hull HI) | exact (minv_cover HI)
    | exact (minv_lazy_nw HI) | exact (minv_maps_nw HI) | exact (minv_noacc_nw HI)
    | exact (minv_nooverlap HI) | exact (minv_eager HI) | exact (minv_budget HI)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma MInv_with_fds : forall A AL E x m, MInv A AL E m -> MInv A AL E (with_fds x m).
Proof. intros A AL E x m H. apply (MInv_vm_frame A AL E m); [reflexivity | exact H]. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 ->
  same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : forall m mat',
  same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity. Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m
  /\ m_nofile m' = m_nofile m /\ m_abort_terminal m' = m_abort_terminal m   (* [comment removed for export] *)
  /\ m_fds m' = m_fds m /\ m_pipes m' = m_pipes m /\ m_stdin m' = m_stdin m
  /\ m_net m' = m_net m /\ m_conn_ix m' = m_conn_ix m
  /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m
  /\ m_creds m' = m_creds m /\ m_setsid_succeeded m' = m_setsid_succeeded m
  /\ m_has_children m' = m_has_children m
  /\ m_rlimit_core m' = m_rlimit_core m /\ m_clock m' = m_clock m
  /\ m_sigmask m' = m_sigmask m /\ m_killed m' = m_killed m   (* [comment removed for export] *)
  /\ m_sigabrt_pending m' = m_sigabrt_pending m   (* [comment removed for export] *)
  /\ eager_used m' = eager_used m /\ vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

Lemma same_but_materialized_halted : forall m m',
  same_but_materialized m m' -> m_halted m' = m_halted m.
Proof. intros m m' H. apply (same_but_materialized_frame m m' H). Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_vmmaps : forall m m',
  same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof. intros m m' H. apply (same_but_materialized_frame m m' H). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : forall l X m, m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma eager_used_wvb : forall X m,
  eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. reflexivity. Qed.
(* [comment removed for export] *)

Lemma MInv_wvb : forall A AL E m X,
  List.NoDup X ->
  (forall p, In p X -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p X -> page_hullb AL (bv_unsigned p) = true) ->
  MInv A AL E m ->
  MInv A AL E (with_vm_backing (m_vm_lazy m) X m).
Proof.
  intros A AL E m X H1 H2 H3 HI. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb; try assumption;
    [exact (minv_cover HI) | exact (minv_lazy_nw HI) | exact (minv_maps_nw HI) | exact (minv_noacc_nw HI)
    | exact (minv_nooverlap HI) | exact (minv_eager HI) | exact (minv_budget HI)].
Qed.

(* [comment removed for export] *)
Lemma NoDup_filter' : forall (A : Type) (f : A -> bool) (l : list A),
  List.NoDup l -> List.NoDup (List.filter f l).
Proof.
  intros A0 f l H. induction H as [|x l Hx H IH]; cbn; [constructor|].
  destruct (f x); [|exact IH]. constructor; [|exact IH].
  intros Hin. apply filter_In in Hin. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_mem_false_not_in : forall p pages,
  page_mem p pages = false -> ~ In p pages.
Proof.
  intros p pages H Hin. unfold page_mem in H.
  assert (existsb (bv_eqb p) pages = true); [|congruence].
  apply existsb_exists. exists p. split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl].
Qed.

(* [comment removed for export] *)

Lemma page_insert_nodup : forall p pages,
  List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages H. unfold page_insert. destruct (page_mem p pages) eqn:E; [exact H|].
  constructor; [apply page_mem_false_not_in; exact E | exact H].
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages H; cbn; [exact H|].
  apply IH. apply page_insert_nodup. exact H.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages H; cbn; [exact H|].
  apply IH. apply access_pages_acc_nodup. exact H.
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : forall A lazy mat accs,
  charged_pages_in_hull A lazy accs ->
  let new := newly_materialized_pages lazy mat accs in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ (forall p, In p new -> (bv_unsigned p mod page_size = 0)%Z)
  /\ (forall p, In p new -> page_in_ranges p lazy = true)
  /\ (forall p, In p new -> page_hullb A (bv_unsigned p) = true).
Proof.
  intros A lazy mat accs Hch new.
  assert (Hchar : forall p, In p new ->
            In p (accesses_pages accs []) /\ page_in_ranges p lazy = true /\ page_mem p mat = false).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hin|]. split; [exact Hl|]. destruct (page_mem p mat); [discriminate | reflexivity]. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter'. apply accesses_pages_nodup. constructor.
  - intros p Hp. (first [ pose proof ((Hchar p Hp)) as dR_6; dand3 dR_6 as _ _ Hm | destruct (Hchar p Hp) as (_ & _ & Hm) ]). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. (first [ pose proof ((Hchar p Hp)) as dR_7; dand3 dR_7 as Hin _ _ | destruct (Hchar p Hp) as (Hin & _ & _) ]).
    destruct (accesses_pages_in accs [] p Hin) as [[] | (a & n & k & _ & _ & ->)].
    apply page_base_of_aligned. pose proof (u64_bound a). lia.
  - intros p Hp. (first [ pose proof ((Hchar p Hp)) as dR_8; dand3 dR_8 as _ Hl _ | destruct (Hchar p Hp) as (_ & Hl & _) ]). exact Hl.
  - intros p Hp. (first [ pose proof ((Hchar p Hp)) as dR_9; dand3 dR_9 as Hin Hl _ | destruct (Hchar p Hp) as (Hin & Hl & _) ]). exact (Hch p Hin Hl).
Qed.

(* [comment removed for export] *)
Definition mat_after (lazy : list (word * word)) (mat : list word)
    (accs : list (word * nat)) : list word :=
  newly_materialized_pages lazy mat accs ++ mat.

Definition model_after (m : Model) (accs : list (word * nat)) : Model :=
  with_vm_backing (m_vm_lazy m) (mat_after (m_vm_lazy m) (m_vm_materialized m) accs) m.

Lemma model_after_same : forall m accs, same_but_materialized m (model_after m accs).
Proof. intros m accs. unfold model_after. apply with_vm_backing_same. Qed.

(* [comment removed for export] *)
Theorem materialize_charged : forall A AL E m accs,
  MInv A AL E m ->
  charged_pages_in_hull AL (m_vm_lazy m) accs ->
  materialize_model_accesses m accs = Some (model_after m accs)
  /\ MInv A AL E (model_after m accs).
Proof.
  intros A AL E m accs HI Hch.
  (first [ pose proof ((new_pages_props AL (m_vm_lazy m) (m_vm_materialized m) accs Hch)) as dR_10; dand5 dR_10 as Nnd Nfresh Nal Nlz Nh | destruct (new_pages_props AL (m_vm_lazy m) (m_vm_materialized m) accs Hch)
    as (Nnd & Nfresh & Nal & Nlz & Nh) ]).
  pose proof (minv_nodup HI) as Hnd. pose proof (minv_aligned HI) as Hal.
  pose proof (minv_hull HI) as Hh. pose proof (minv_eager HI) as HE.
  pose proof (minv_budget HI) as Hb. pose proof (minv_lazy_nw HI) as Hnw.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) -> (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_h : forall p, In p (new ++ m_vm_materialized m) -> page_hullb AL (bv_unsigned p) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nh p Hp) | exact (Hh p Hp)]. }
  assert (HI' : MInv A AL E (model_after m accs)).
  { unfold model_after, mat_after. fold new. apply MInv_wvb; assumption. }
  split; [|exact HI'].
  pose proof (hull_pages_bound AL (new ++ m_vm_materialized m) Happ_nd Happ_al Happ_h) as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  unfold materialize_model_accesses, materialize_accesses. fold new.
  unfold model_after, mat_after. fold new.
  destruct new as [|p0 new'] eqn:Enew.
  - cbn [app]. reflexivity.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true; [reflexivity|].
    symmetry. apply Z.leb_le. pose proof page_size_pos. nia.
Qed.

(* [comment removed for export] *)
Theorem materialize_hull : forall A AL E m accs,
  MInv A AL E m ->
  accs_in_hull A accs ->
  materialize_model_accesses m accs = Some (model_after m accs)
  /\ MInv A AL E (model_after m accs).
Proof.
  intros A AL E m accs HI Ha.
  exact (materialize_charged A AL E m accs HI (charged_pages_in_hull_of_cover A AL _ accs (minv_cover HI) Ha)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Theorem account_step_charged : forall A AL E ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  MInv A AL E model ->
  charged_pages_in_hull AL (m_vm_lazy model) ranges ->
  mi_account_step segs ms model = MachineOk (ms', model_after model ranges)
  /\ MInv A AL E (model_after model ranges).
Proof.
  intros A AL E ms model ms' ranges Hstep HI Hch.
  destruct (materialize_charged A AL E model ranges HI Hch) as [Hmat HI'].
  split; [|exact HI'].
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep), Hmat. reflexivity.
Qed.

Theorem account_step_hull : forall A AL E ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  MInv A AL E model ->
  accs_in_hull A ranges ->
  mi_account_step segs ms model = MachineOk (ms', model_after model ranges)
  /\ MInv A AL E (model_after model ranges).
Proof.
  intros A AL E ms model ms' ranges Hstep HI Ha.
  exact (account_step_charged A AL E ms model ms' ranges Hstep HI (charged_pages_in_hull_of_cover A AL _ _ (minv_cover HI) Ha)).
Qed.

(* [comment removed for export] *)
Lemma sstep_account_det : forall ms model ms1 model1 e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms1, model1) ->
  sstep segs (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms1 model1).
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss.
  inversion Hss; subst; try congruence.
  match goal with
  | H : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Hacc in H; injection H; intros; subst
  end.
  split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_account : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros ms model ms' model' Hh Hsvc Hacc. split.
  - intros []. apply (sstep_cfg_instr segs ACFG ms model ms' model'); assumption.
  - intros e st Hss. destruct (sstep_account_det ms model ms' model' e st Hsvc Hacc (sstep_cfg_sub segs ACFG _ _ _ Hss)) as [-> ->].
    exists tt. split; reflexivity.
Qed.

Theorem node_instr_hull : forall A AL E ms model ms' ranges,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  MInv A AL E model ->
  accs_in_hull A ranges ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' (model_after model ranges))
  /\ MInv A AL E (model_after model ranges).
Proof.
  intros A AL E ms model ms' ranges Hh Hsvc Hstep HI Ha.
  destruct (account_step_hull A AL E ms model ms' ranges Hstep HI Ha) as [Hacc HI'].
  split; [apply node_account; assumption | exact HI'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ts_step_hull : forall A AL E ms model ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  MInv A AL E model ->
  accs_in_hull A ranges ->
  (MInv A AL E (model_after model ranges) -> to_spin segs ms' (model_after model ranges)) ->
  to_spin segs ms model.
Proof.
  intros A AL E ms model ms' ranges Hsvc Hstep HI Ha Hk.
  destruct (account_step_hull A AL E ms model ms' ranges Hstep HI Ha) as [Hacc HI'].
  exact (ts_step segs ms model ms' _ Hsvc Hacc (Hk HI')).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem ts_msteps_hull : forall A AL E ms ms' accs model,
  msteps_acc segs ms ms' accs ->
  MInv A AL E model ->
  accs_in_hull A accs ->
  (forall model', MInv A AL E model' -> same_but_materialized model model' ->
                  to_spin segs ms' model') ->
  to_spin segs ms model.
Proof.
  intros A AL E ms ms' accs model Hms. revert model.
  induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH]; intros model HI Ha Hk.
  - apply Hk; [exact HI | apply same_but_materialized_refl].
  - destruct (accs_in_hull_app_inv A ranges accs Ha) as [Hr Hrest].
    eapply ts_step_hull; [exact Hsvc | exact Hstep | exact HI | exact Hr |].
    intros HI'. apply IH; [exact HI' | exact Hrest | ].
    intros model'' HI'' Hsame. apply Hk; [exact HI''|].
    eapply same_but_materialized_trans; [apply model_after_same | exact Hsame].
Qed.

(* [comment removed for export] *)
Definition silent_closed (P : config -> Prop) : Prop :=
  forall c c', node_ok segs c unit (fun _ => []) (fun _ => c') -> P c' -> P c.

(* [comment removed for export] *)

Lemma silent_closed_srealizes : forall T, silent_closed (fun c => srealizes segs c T).
Proof. intros T c c' Hn Hc. eapply srz_silent1; [exact Hn | exact Hc]. Qed.

Theorem acct_step_hull : forall (P : config -> Prop) A AL E ms model ms' ranges,
  silent_closed P ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  MInv A AL E model ->
  accs_in_hull A ranges ->
  (MInv A AL E (model_after model ranges) -> P (mkCfg ms' (model_after model ranges))) ->
  P (mkCfg ms model).
Proof.
  intros P A AL E ms model ms' ranges T Hh Hsvc Hstep HI Ha Hk.
  destruct (node_instr_hull A AL E ms model ms' ranges Hh Hsvc Hstep HI Ha) as [Hn HI'].
  exact (T _ _ Hn (Hk HI')).
Qed.

Theorem acct_msteps_hull : forall (P : config -> Prop) A AL E ms ms' accs model,
  silent_closed P ->
  m_halted model = None ->
  msteps_acc segs ms ms' accs ->
  MInv A AL E model ->
  accs_in_hull A accs ->
  (forall model', MInv A AL E model' -> same_but_materialized model model' ->
                  P (mkCfg ms' model')) ->
  P (mkCfg ms model).
Proof.
  intros P A AL E ms ms' accs model HP Hh Hms. revert model Hh.
  induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH]; intros model Hh HI Ha Hk.
  - apply Hk; [exact HI | apply same_but_materialized_refl].
  - destruct (accs_in_hull_app_inv A ranges accs Ha) as [Hr Hrest].
    eapply (acct_step_hull P); [exact HP | exact Hh | exact Hsvc | exact Hstep | exact HI | exact Hr |].
    intros HI'. apply IH; [ | exact HI' | exact Hrest | ].
    + rewrite (same_but_materialized_halted model (model_after model ranges) (model_after_same model ranges)). exact Hh.
    + intros model'' HI'' Hsame. apply Hk; [exact HI''|].
      eapply same_but_materialized_trans; [apply model_after_same | exact Hsame].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma mat_filter_nodup : forall f (l : list word), List.NoDup l -> List.NoDup (List.filter f l).
Proof. intros. apply NoDup_filter'. assumption. Qed.

Lemma mat_filter_forall : forall (P : word -> Prop) f (l : list word),
  (forall p, In p l -> P p) -> forall p, In p (List.filter f l) -> P p.
Proof. intros P f l H p Hp. apply filter_In in Hp. apply H. tauto. Qed.

(* [comment removed for export] *)
Lemma MInv_rebuild : forall A AL E E' m m' (f : option (word -> bool)),
  MInv A AL E m ->
  m_vm_materialized m' = match f with
                         | Some g => List.filter g (m_vm_materialized m)
                         | None => m_vm_materialized m end ->
  lazy_sub (m_vm_lazy m') (m_vm_lazy m) ->
  entries_nowrap (m_vm_lazy m') ->
  entries_nowrap (vm_maps (m_vmmaps m')) ->
  entries_nowrap (vm_noaccess (m_vmmaps m')) ->
  nooverlap (vm_maps (m_vmmaps m')) ->
  eager_used m' <= E' ->
  vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m) ->
  E' + hull_bytes AL <= vm_limit (m_vmmaps m) ->
  MInv A AL E' m'.
Proof.
  intros A AL E E' m m' f HI Hmat Hls Hl Hm Hn Ho He Hlim Hb.
  constructor; try assumption.
  - rewrite Hmat. destruct f; [apply mat_filter_nodup|]; exact (minv_nodup HI).
  - rewrite Hmat. destruct f; [apply mat_filter_forall|]; exact (minv_aligned HI).
  - rewrite Hmat. destruct f; [apply (mat_filter_forall (fun p => page_hullb AL (bv_unsigned p) = true))|]; exact (minv_hull HI).
  - exact (hull_cover_lazy_mono A AL _ _ Hls (minv_cover HI)).
  - rewrite Hlim. exact Hb.
Qed.

Lemma lo_hi_range : forall (addr n : word),
  0 <= bv_unsigned addr /\ bv_unsigned addr <= bv_unsigned addr + bv_unsigned n.
Proof. intros. pose proof (u64_bound addr). pose proof (u64_bound n). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma grant_lazy_nowrap : forall flags a n na m,
  entries_nowrap (m_vm_lazy m) -> entry_nowrap (a, n) ->
  entries_nowrap (m_vm_lazy (grant_model flags a n na m)).
Proof.
  intros flags a n na m HL He. rewrite grant_model_lazy. apply entries_nowrap_app. split; [|exact HL].
  destruct (mmap_noreserve_b flags); [apply entries_nowrap_lazy_interior; exact He | intros e []].
Qed.

(* [comment removed for export] *)
Lemma grant_model_lazy_plain : forall flags a n na m,
  mmap_noreserve_b flags = false -> m_vm_lazy (grant_model flags a n na m) = m_vm_lazy m.
Proof. intros flags a n na m Hnr. rewrite grant_model_lazy, Hnr. reflexivity. Qed.

Lemma lazy_free_grant : forall flags a n na m lo hi,
  mmap_noreserve_b flags = false ->
  lazy_free (m_vm_lazy m) lo hi -> lazy_free (m_vm_lazy (grant_model flags a n na m)) lo hi.
Proof. intros flags a n na m lo hi Hnr H. rewrite (grant_model_lazy_plain flags a n na m Hnr). exact H. Qed.

(* [comment removed for export] *)
Theorem MInv_grant_rw : forall A AL E flags a n m,
  MInv A AL E m ->
  mmap_noreserve_b flags = false ->
  bv_unsigned a + bv_unsigned n <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a n = true ->
  E + bv_unsigned n + hull_bytes AL <= vm_limit (m_vmmaps m) ->
  MInv A AL (E + bv_unsigned n) (grant_model flags a n false m).
Proof.
  intros A AL E flags a n m HI Hnr Hce Hrf Hb.
  pose proof (entry_nowrap_below_ceiling _ a n Hce) as He.
  apply (MInv_rebuild A AL E (E + bv_unsigned n) m _ None HI).
  - apply grant_model_materialized.
  - apply lazy_sub_eq. apply grant_model_lazy_plain. exact Hnr.
  - apply grant_lazy_nowrap; [exact (minv_lazy_nw HI) | exact He].
  - rewrite grant_model_vmmaps. cbn. apply entries_nowrap_cons. split; [exact He | exact (minv_maps_nw HI)].
  - rewrite grant_model_vmmaps. cbn. exact (minv_noacc_nw HI).
  - rewrite grant_model_vmmaps. cbn. apply nooverlap_cons_region_free;
      [exact (region_free_app_r _ _ _ _ Hrf) | exact (minv_nooverlap HI)].
  - pose proof (eager_used_grant_rw_le flags a n m Hnr (minv_maps_nw HI) He). pose proof (minv_eager HI). lia.
  - rewrite grant_model_vmmaps. reflexivity.
  - exact Hb.
Qed.

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

Lemma commit_lazy_nowrap : forall flags addr n na m,
  entries_nowrap (m_vm_lazy m) -> entry_nowrap (addr, n) ->
  entries_nowrap (m_vm_lazy (commit_model flags addr n na m)).
Proof.
  intros flags addr n na m HL He. rewrite commit_model_lazy. apply entries_nowrap_app. split.
  - destruct (mmap_noreserve_b flags); [apply entries_nowrap_lazy_interior; exact He | intros e []].
  - apply maps_subtract_nowrap; [exact HL | apply (lo_hi_range addr n) | apply (lo_hi_range addr n)].
Qed.

Lemma commit_noacc_nowrap : forall flags addr n na m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entry_nowrap (addr, n) ->
  entries_nowrap (vm_noaccess (m_vmmaps (commit_model flags addr n na m))).
Proof.
  intros flags addr n na m HN He. rewrite commit_model_vmmaps. cbn. apply entries_nowrap_app. split.
  - destruct na; [apply entries_nowrap_cons; split; [exact He | intros e []] | intros e []].
  - apply maps_subtract_nowrap; [exact HN | apply (lo_hi_range addr n) | apply (lo_hi_range addr n)].
Qed.

(* [comment removed for export] *)
Lemma commit_model_lazy_plain : forall flags addr n na m,
  mmap_noreserve_b flags = false ->
  m_vm_lazy (commit_model flags addr n na m)
  = maps_subtract (m_vm_lazy m) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. intros flags addr n na m Hnr. rewrite commit_model_lazy, Hnr. reflexivity. Qed.

Lemma lazy_sub_commit : forall flags addr n na m,
  mmap_noreserve_b flags = false -> entries_nowrap (m_vm_lazy m) ->
  lazy_sub (m_vm_lazy (commit_model flags addr n na m)) (m_vm_lazy m).
Proof.
  intros flags addr n na m Hnr Hnw. rewrite (commit_model_lazy_plain flags addr n na m Hnr).
  apply lazy_sub_subtract; [exact Hnw | apply (lo_hi_range addr n) | apply (lo_hi_range addr n)].
Qed.

Lemma lazy_free_commit : forall flags addr n na m lo hi,
  mmap_noreserve_b flags = false -> entries_nowrap (m_vm_lazy m) ->
  lazy_free (m_vm_lazy m) lo hi -> lazy_free (m_vm_lazy (commit_model flags addr n na m)) lo hi.
Proof.
  intros flags addr n na m lo hi Hnr Hnw H. exact (lazy_free_mono _ _ lo hi (lazy_sub_commit flags addr n na m Hnr Hnw) H).
Qed.

Theorem commit_lazy_free : forall flags addr n na m,
  mmap_noreserve_b flags = false -> entries_nowrap (m_vm_lazy m) ->
  lazy_free (m_vm_lazy (commit_model flags addr n na m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof.
  intros flags addr n na m Hnr Hnw. rewrite (commit_model_lazy_plain flags addr n na m Hnr).
  apply lazy_free_subtract; [exact Hnw | apply (lo_hi_range addr n) | apply (lo_hi_range addr n)].
Qed.

Lemma MInv_commit_lazy_free : forall A AL E flags addr n na m,
  MInv A AL E m -> mmap_noreserve_b flags = false ->
  lazy_free (m_vm_lazy (commit_model flags addr n na m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. intros A AL E flags addr n na m HI Hnr. exact (commit_lazy_free flags addr n na m Hnr (minv_lazy_nw HI)). Qed.

(* [comment removed for export] *)
Theorem MInv_commit_rw : forall A AL E flags addr n m,
  MInv A AL E m ->
  mmap_noreserve_b flags = false ->
  bv_unsigned addr + bv_unsigned n <= alloc_top (m_vmmaps m) ->
  map_contains (vm_maps (m_vmmaps m)) addr n = true ->
  E + bv_unsigned n + hull_bytes AL <= vm_limit (m_vmmaps m) ->
  MInv A AL (E + bv_unsigned n) (commit_model flags addr n false m).
Proof.
  intros A AL E flags addr n m HI Hnr Hce Hmc Hb.
  pose proof (entry_nowrap_below_ceiling _ addr n Hce) as He.
  apply (MInv_rebuild A AL E (E + bv_unsigned n) m _
           (Some (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))) HI).
  - apply commit_model_materialized.
  - apply lazy_sub_commit; [exact Hnr | exact (minv_lazy_nw HI)].
  - apply commit_lazy_nowrap; [exact (minv_lazy_nw HI) | exact He].
  - rewrite commit_model_vmmaps. cbn. exact (minv_maps_nw HI).
  - apply commit_noacc_nowrap; [exact (minv_noacc_nw HI) | exact He].
  - rewrite commit_model_vmmaps. cbn. exact (minv_nooverlap HI).
  - pose proof (eager_used_commit_rw_le flags addr n m (minv_maps_nw HI) (minv_noacc_nw HI)
                  (minv_lazy_nw HI) (minv_nooverlap HI) (map_contains_In _ _ _ Hmc)).
    pose proof (minv_eager HI). lia.
  - rewrite commit_model_vmmaps. reflexivity.
  - exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma filter_length_le : forall (X : Type) (f : X -> bool) (l : list X),
  (length (List.filter f l) <= length l)%nat.
Proof. intros X f l. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

(* [comment removed for export] *)
Lemma gate_fixed_rw_budget_ok : forall A AL E flags addr n m,
  MInv A AL E m ->
  bv_unsigned addr + bv_unsigned n <= alloc_top (m_vmmaps m) ->
  map_contains (vm_maps (m_vmmaps m)) addr n = true ->
  (  (mmap_noreserve_b flags = true /\ lazy_interior addr n = [(addr, n)])
   \/ E + hull_bytes AL + bv_unsigned n <= vm_limit (m_vmmaps m)) ->
  mmap_fixed_rw_budget_ok flags m addr n = true.
Proof.
  intros A AL E flags addr n m HI Hce Hmc Hroom.
  unfold mmap_fixed_rw_budget_ok. rewrite mmap_fixed_rw_commit_model.
  unfold vm_backing_within_limit. apply Z.leb_le.
  rewrite vm_backing_used_split, commit_model_vmmaps, commit_model_materialized. cbn [vm_limit commit_vmmaps].
  pose proof (filter_length_le _ (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                (m_vm_materialized m)) as Hlen.
  pose proof (hull_pages_bound AL (m_vm_materialized m) (minv_nodup HI) (minv_aligned HI) (minv_hull HI)) as Hpg.
  pose proof (minv_eager HI) as HE. pose proof (minv_budget HI) as HB. pose proof page_size_pos.
  pose proof (entry_nowrap_below_ceiling _ addr n Hce) as He.
  destruct Hroom as [Hnr | Hroom].
  - pose proof (eager_used_commit_covered_le flags addr n false m (minv_maps_nw HI) (minv_noacc_nw HI)
                  (minv_lazy_nw HI) (or_intror Hnr)). nia.
  - pose proof (eager_used_commit_rw_le flags addr n m (minv_maps_nw HI) (minv_noacc_nw HI)
                  (minv_lazy_nw HI) (minv_nooverlap HI) (map_contains_In _ _ _ Hmc)). nia.
Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma page_hullb_app : forall A B p, page_hullb (A ++ B) p = page_hullb A p || page_hullb B p.
Proof. intros. unfold page_hullb. apply existsb_app. Qed.

Lemma page_hullb_cons : forall iv A p, page_hullb (iv :: A) p = page_meets_ivb p iv || page_hullb A p.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem MInv_rehull : forall A AL A' AL' E E' m,
  MInv A AL E m ->
  (forall p, In p (m_vm_materialized m) -> page_hullb AL' (bv_unsigned p) = true) ->
  hull_cover A' AL' (m_vm_lazy m) ->
  E <= E' ->
  E' + hull_bytes AL' <= vm_limit (m_vmmaps m) ->
  MInv A' AL' E' m.
Proof.
  intros A AL A' AL' E E' m HI Hcov HC HE Hb. constructor.
  - exact (minv_nodup HI).
  - exact (minv_aligned HI).
  - exact Hcov.
  - exact HC.
  - exact (minv_lazy_nw HI).
  - exact (minv_maps_nw HI).
  - exact (minv_noacc_nw HI).
  - exact (minv_nooverlap HI).
  - pose proof (minv_eager HI). lia.
  - exact Hb.
Qed.

(* [comment removed for export] *)
Theorem MInv_rehull_AL : forall A AL AL' E E' m,
  MInv A AL E m ->
  (forall p, In p (m_vm_materialized m) -> page_hullb AL' (bv_unsigned p) = true) ->
  (forall lo hi, In (lo, hi) A -> iv_sub AL lo hi -> iv_sub AL' lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  E <= E' ->
  E' + hull_bytes AL' <= vm_limit (m_vmmaps m) ->
  MInv A AL' E' m.
Proof.
  intros A AL AL' E E' m HI Hcov HX HE Hb.
  apply (MInv_rehull A AL A AL' E E' m HI Hcov); [| exact HE | exact Hb].
  intros lo hi Hin. destruct (minv_cover HI lo hi Hin) as [S|F]; [exact (HX lo hi Hin S) | right; exact F].
Qed.

(* [comment removed for export] *)
Theorem MInv_access_rehull : forall A A' AL E m,
  MInv A AL E m ->
  (forall lo hi, In (lo, hi) A' -> iv_sub A lo hi \/ iv_sub AL lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  MInv A' AL E m.
Proof.
  intros A A' AL E m HI HX.
  apply (MInv_hull_mono A AL A' AL E E m HI (hull_le_refl AL) HX (Z.le_refl E) (minv_budget HI)).
Qed.

Theorem MInv_hull_remove : forall A1 iv A2 AL E m,
  MInv (A1 ++ iv :: A2) AL E m -> MInv (A1 ++ A2) AL E m.
Proof.
  intros A1 iv A2 AL E m HI. apply (MInv_access_rehull _ (A1 ++ A2) AL E m HI).
  intros lo hi Hin. left. apply iv_sub_In. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin].
Qed.

Theorem MInv_hull_remove_all : forall A1 B A2 AL E m,
  MInv (A1 ++ B ++ A2) AL E m -> MInv (A1 ++ A2) AL E m.
Proof.
  intros A1 B A2 AL E m HI. apply (MInv_access_rehull _ (A1 ++ A2) AL E m HI).
  intros lo hi Hin. left. apply iv_sub_In. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; apply in_or_app; right; exact Hin].
Qed.

(* [comment removed for export] *)
Theorem MInv_lhull_remove : forall A AL1 iv AL2 E m,
  MInv A (AL1 ++ iv :: AL2) E m ->
  (forall p, In p (m_vm_materialized m) -> page_meets_ivb (bv_unsigned p) iv = false) ->
  (forall lo hi, In (lo, hi) A -> iv_sub (AL1 ++ iv :: AL2) lo hi ->
                 iv_sub (AL1 ++ AL2) lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  MInv A (AL1 ++ AL2) E m.
Proof.
  intros A AL1 iv AL2 E m HI Hno HX.
  apply (MInv_rehull_AL A (AL1 ++ iv :: AL2) (AL1 ++ AL2) E E m HI).
  - intros p Hp. pose proof (minv_hull HI p Hp) as H.
    rewrite page_hullb_app, page_hullb_cons, (Hno p Hp) in H. rewrite page_hullb_app.
    destruct (page_hullb AL1 (bv_unsigned p)); [reflexivity | exact H].
  - exact HX.
  - lia.
  - pose proof (minv_budget HI) as Hb. rewrite hull_bytes_app, hull_bytes_cons in Hb. rewrite hull_bytes_app.
    pose proof page_size_pos. nia.
Qed.

(* [comment removed for export] *)
Theorem MInv_lhull_remove_all : forall A AL1 B AL2 E m,
  MInv A (AL1 ++ B ++ AL2) E m ->
  (forall p iv, In p (m_vm_materialized m) -> In iv B -> page_meets_ivb (bv_unsigned p) iv = false) ->
  (forall lo hi, In (lo, hi) A -> iv_sub (AL1 ++ B ++ AL2) lo hi ->
                 iv_sub (AL1 ++ AL2) lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  MInv A (AL1 ++ AL2) E m.
Proof.
  intros A AL1 B AL2 E m HI Hno HX.
  apply (MInv_rehull_AL A (AL1 ++ B ++ AL2) (AL1 ++ AL2) E E m HI).
  - intros p Hp. pose proof (minv_hull HI p Hp) as H. rewrite !page_hullb_app in H. rewrite page_hullb_app.
    apply orb_true_iff in H as [H|H]; [rewrite H; reflexivity|].
    apply orb_true_iff in H as [H|H]; [| rewrite H; apply orb_true_r].
    exfalso. apply page_hullb_true in H as (lo & hi & Hin & Hm).
    pose proof (Hno p (lo, hi) Hp Hin) as X. apply (proj2 (page_meets_ivb_true _ lo hi)) in Hm. congruence.
  - exact HX.
  - lia.
  - pose proof (minv_budget HI) as Hb. rewrite !hull_bytes_app in Hb. rewrite hull_bytes_app.
    assert (0 <= hull_bytes B); [|lia]. clear. induction B as [|iv B IH]; cbn [hull_bytes]; [lia|]. pose proof page_size_pos. nia.
Qed.

(* [comment removed for export] *)
Theorem MInv_hulls_remove_all : forall A1 B A2 AL1 AL2 E m,
  MInv (A1 ++ B ++ A2) (AL1 ++ B ++ AL2) E m ->
  (forall p iv, In p (m_vm_materialized m) -> In iv B -> page_meets_ivb (bv_unsigned p) iv = false) ->
  (forall lo hi, In (lo, hi) (A1 ++ A2) -> iv_sub (AL1 ++ B ++ AL2) lo hi ->
                 iv_sub (AL1 ++ AL2) lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  MInv (A1 ++ A2) (AL1 ++ AL2) E m.
Proof.
  intros A1 B A2 AL1 AL2 E m HI Hno HX.
  apply (MInv_lhull_remove_all (A1 ++ A2) AL1 B AL2 E m); [| exact Hno | exact HX].
  exact (MInv_hull_remove_all A1 B A2 _ E m HI).
Qed.

(* [comment removed for export] *)
Lemma forgotten_pages_avoid : forall (lo hi l h : Z) (mat : list word) p,
  lo mod page_size = 0 -> lo <= l -> h <= hi ->
  (forall q, In q mat -> bv_unsigned q mod page_size = 0) ->
  In p (List.filter (page_outside_range lo hi) mat) ->
  page_meets_ivb (bv_unsigned p) (l, h) = false.
Proof.
  intros lo hi l h mat p Hlo Hl Hh Hal Hin.
  apply filter_In in Hin as [Hin Hout]. specialize (Hal p Hin).
  unfold page_outside_range in Hout. apply negb_true_iff in Hout.
  destruct (page_meets_ivb (bv_unsigned p) (l, h)) eqn:E; [|reflexivity]. exfalso.
  apply page_meets_ivb_true in E as [E1 E2].
  apply andb_false_iff in Hout as [Hout | Hout].
  - apply Z.leb_gt in Hout. pose proof page_size_pos.
    (* [comment removed for export] *)
    pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as Dp.
    pose proof (Z.div_mod lo page_size ltac:(lia)) as Dl.
    rewrite Hal in Dp. rewrite Hlo in Dl.
    assert (bv_unsigned p / page_size < lo / page_size) by nia. nia.
  - apply Z.ltb_ge in Hout. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition region := (Z * Z)%type.   (* [comment removed for export] *)

Definition hull_of (R : list region) : hull := map (fun r => (fst r, fst r + snd r)) R.

Fixpoint regions_weight (R : list region) : Z :=
  match R with
  | [] => 0
  | r :: R' => (snd r + 2 * page_size) + regions_weight R'
  end.

Lemma hull_of_app : forall R1 R2, hull_of (R1 ++ R2) = hull_of R1 ++ hull_of R2.
Proof. intros. unfold hull_of. apply map_app. Qed.

Lemma regions_weight_app : forall R1 R2,
  regions_weight (R1 ++ R2) = regions_weight R1 + regions_weight R2.
Proof. induction R1 as [|r R1 IH]; intros R2; cbn [regions_weight app]; [lia | rewrite IH; lia]. Qed.

Lemma hull_bytes_of_regions : forall R,
  (forall b s, In (b, s) R -> 0 <= s) ->
  hull_bytes (hull_of R) <= regions_weight R.
Proof.
  induction R as [|[b s] R IH]; intros Hpos; cbn [hull_of map regions_weight fst snd]; [cbn; lia|].
  rewrite hull_bytes_cons.
  pose proof (hull_npages_le b (b + s) ltac:(specialize (Hpos b s (or_introl eq_refl)); lia)).
  specialize (IH ltac:(intros b' s' Hin; exact (Hpos b' s' (or_intror Hin)))).
  unfold hull_of in IH. cbn [fst snd]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. lia. Qed.

Lemma u64_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma page_round_up_Z_aligned : forall z, page_round_up_Z z mod page_size = 0.
Proof. intros z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma lenZ_aligned : forall len, lenZ len mod page_size = 0.
Proof. intros len. unfold lenZ. apply page_round_up_Z_aligned. Qed.

Lemma lenZ_nonneg : forall len, 0 <= lenZ len.
Proof.
  intros len. unfold lenZ, page_round_up_Z. pose proof (u64_range (Z_to_bv 64 len)). unfold page_size.
  apply Z.mul_nonneg_nonneg; [| lia]. apply Z.div_pos; lia.
Qed.

Lemma page_base_facts : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
  /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma page_of_byte_in_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned x < hi ->
  lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= hi.
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma page_of_byte_out_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  bv_unsigned (page_base x) + 4096 <= lo \/ hi <= bv_unsigned (page_base x).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma aligned_in_or_out : forall p lo hi,
  p mod 4096 = 0 -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  (lo <= p /\ p + 4096 <= hi) \/ (p + 4096 <= lo \/ hi <= p).
Proof.
  intros p lo hi Hp Hlo Hhi.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma page_in_ranges_cons : forall p iv l,
  page_in_ranges p (iv :: l)
  = (((bv_unsigned (fst iv) <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned (fst iv) + bv_unsigned (snd iv)))
     || page_in_ranges p l)%bool.
Proof. reflexivity. Qed.

Lemma page_in_ranges_app : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_in_ranges_true : forall p l,
  page_in_ranges p l = true <->
  exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_false : forall p l,
  page_in_ranges p l = false <->
  forall iv, In iv l -> ~ (bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Proof.
  intros p l. split.
  - intros H iv Hin Hc. assert (T : page_in_ranges p l = true) by (apply (proj2 (page_in_ranges_true p l)); exists iv; tauto). congruence.
  - intros H. destruct (page_in_ranges p l) eqn:E; [|reflexivity]. exfalso.
    apply page_in_ranges_true in E as (iv & Hin & H1 & H2). exact (H iv Hin (conj H1 H2)).
Qed.

Lemma page_in_ranges_covers : forall p l z,
  page_in_ranges p l = true -> bv_unsigned p <= z < bv_unsigned p + page_size -> covered l z = true.
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  unfold covered. apply existsb_exists. exists iv. split; [exact Hin|]. unfold in_iv, in_rng, B, S.
  apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma page_in_ranges_subtract_out : forall (p : word) l lo hi,
  ivs_wf l -> lo <= hi ->
  (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l.
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
  - destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

Lemma page_in_ranges_subtract_in : forall (p : word) l lo hi,
  ivs_wf l -> lo <= bv_unsigned p < hi ->
  page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
  destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.

Lemma page_in_ranges_cons_in : forall (p a n : word) l,
  bv_unsigned a <= bv_unsigned p -> bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = true.
Proof.
  intros p a n l H1 H2. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. left.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_cons_out : forall (p a n : word) l,
  (bv_unsigned p + page_size <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned p) ->
  0 < bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = page_in_ranges p l.
Proof.
  intros p a n l H Hn. rewrite page_in_ranges_cons. cbn [fst snd]. unfold page_size in *.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.

Lemma page_in_lazy_meets_maps : forall mo (p : word) z,
  lazy_in_maps mo -> page_in_ranges p (m_vm_lazy mo) = true ->
  bv_unsigned p <= z < bv_unsigned p + page_size -> covered (vm_maps (m_vmmaps mo)) z = true.
Proof.
  intros mo p z HL Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (HL iv z Hin). lia.
Qed.

Lemma pagesN_length : forall lo k, length (pagesN lo k) = k.
Proof. intros lo k. revert lo. induction k; intros lo; cbn; [reflexivity| rewrite IHk; reflexivity]. Qed.

Lemma pagesN_in : forall lo k p,
  In p (pagesN lo k) <-> exists j, (j < k)%nat /\ p = Z_to_bv 64 (lo + page_size * Z.of_nat j).
Proof.
  intros lo k. revert lo. induction k as [|k IH]; intros lo p; cbn [pagesN].
  - split; [intros []| intros (j & Hj & _); lia].
  - split.
    + intros [<-|Hin].
      * exists 0%nat. split; [lia|]. f_equal. lia.
      * apply IH in Hin as (j & Hj & ->). exists (Datatypes.S j). split; [lia|]. f_equal. lia.
    + intros (j & Hj & ->). destruct j as [|j].
      * left. f_equal. lia.
      * right. apply IH. exists j. split; [lia|]. f_equal. lia.
Qed.

Lemma pages_of_in : forall lo hi p,
  lo mod page_size = 0 -> hi mod page_size = 0 -> lo <= hi ->
  In p (pages_of lo hi) <-> exists z, lo <= z /\ z + page_size <= hi /\ z mod page_size = 0 /\ p = Z_to_bv 64 z.
Proof.
  intros lo hi p Hlo Hhi Hlh. unfold pages_of. rewrite pagesN_in.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split.
  - intros (j & Hj & ->). exists (lo + page_size * Z.of_nat j). unfold page_size in *.
    split; [lia|]. split; [nia|]. split; [| reflexivity].
    rewrite (Z.mul_comm 4096), Z_mod_plus_full. exact Hlo.
  - intros (z & H1 & H2 & H3 & ->). exists (Z.to_nat ((z - lo) / page_size)). unfold page_size in *. split; [| f_equal]; nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pages_of_length : forall lo hi,
  lo mod page_size = 0 -> hi mod page_size = 0 -> lo <= hi ->
  Z.of_nat (length (pages_of lo hi)) * page_size = hi - lo.
Proof.
  intros lo hi Hlo Hhi Hlh. unfold pages_of. rewrite pagesN_length. unfold page_size in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pages_of_aligned : forall lo hi, lo mod page_size = 0 -> 0 <= lo -> hi <= 2^64 -> P_aligned (pages_of lo hi).
Proof.
  intros lo hi Hlo H0 Hhi. unfold P_aligned, pages_of. apply Forall_forall. intros p Hp.
  apply pagesN_in in Hp as (j & Hj & ->).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit by (unfold page_size in *; nia). unfold page_size in *.
  rewrite (Z.mul_comm 4096), Z_mod_plus_full. exact Hlo.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma page_base_in_pages_of : forall (w : word) lo hi,
  lo mod page_size = 0 -> hi mod page_size = 0 -> 0 <= lo -> hi <= 2^64 ->
  lo <= bv_unsigned w < hi -> In (page_base w) (pages_of lo hi).
Proof.
  intros w lo hi Hlo Hhi H0 H64 Hw. pose proof (page_base_facts w) as (P1 & P2 & P3).
  destruct (page_of_byte_in_aligned w lo hi Hlo Hhi Hw) as [Q1 Q2].
  apply (proj2 (pages_of_in lo hi (page_base w) Hlo Hhi ltac:(lia))).
  exists (bv_unsigned (page_base w)). split; [lia|]. split; [unfold page_size; lia|]. split; [exact P3|].
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma cut_pages_in : forall lo hi P p,
  In p (cut_pages lo hi P) <-> In p P /\ (bv_unsigned p < lo \/ hi <= bv_unsigned p).
Proof.
  intros lo hi P p. unfold cut_pages. rewrite filter_In. unfold page_outside_range.
  rewrite negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. tauto.
Qed.

Lemma cut_pages_aligned : forall lo hi P, P_aligned P -> P_aligned (cut_pages lo hi P).
Proof. intros lo hi P HP. unfold P_aligned, cut_pages in *. apply incl_Forall with (l1 := P); [| exact HP]. apply incl_filter. Qed.

Lemma cut_pages_length : forall lo hi P, (length (cut_pages lo hi P) <= length P)%nat.
Proof. intros lo hi P. unfold cut_pages. apply filter_length_le. Qed.

Lemma P_aligned_app : forall P Q, P_aligned P -> P_aligned Q -> P_aligned (P ++ Q).
Proof. intros P Q HP HQ. unfold P_aligned in *. apply Forall_app. split; assumption. Qed.

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l H. induction H as [|p l Hp Hl IH]; cbn; [constructor|].
  destruct (f p); [| exact IH]. constructor; [| exact IH].
  apply incl_Forall with (l1 := l); [apply incl_filter| exact Hp].
Qed.

Lemma seps_cons_free : forall l (a n : word),
  region_free l a n = true -> seps l -> seps ((a, n) :: l).
Proof.
  intros l a n Hrf Hs. constructor; [| exact Hs]. apply Forall_forall. intros [e sz] Hin.
  pose proof (Decode.region_free_In l a n e sz Hrf Hin) as D. unfold iv_disjoint. cbn [fst snd]. lia.
Qed.

Lemma seps_in_disjoint : forall l p q, seps l -> In p l -> In q l -> p = q \/ iv_disjoint p q.
Proof.
  intros l p q H. induction H as [|r l Hr Hl IH]; intros Hp Hq; [destruct Hp|].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - left; reflexivity.
  - right. exact (proj1 (Forall_forall _ _) Hr q Hq).
  - right. pose proof (proj1 (Forall_forall _ _) Hr p Hp) as D. unfold iv_disjoint in *. lia.
  - exact (IH Hp Hq).
Qed.

Lemma sum_count_mono_in : forall P Q l,
  (forall e x, In e l -> B e <= x < B e + S e -> P x = true -> Q x = true) ->
  sum_count P l <= sum_count Q l.
Proof.
  intros P Q l H. induction l as [|e l IH]; cbn -[Z.add]; [lia|].
  pose proof (S_range e).
  pose proof (zcount_mono P Q (B e) (Z.to_nat (S e)) ltac:(intros x Hx; apply (H e x (or_introl eq_refl)); lia)).
  specialize (IH ltac:(intros e' x He' Hx; apply (H e' x (or_intror He') Hx))). unfold iv_count. lia.
Qed.

Lemma sum_count_ext_in : forall P Q l,
  (forall e x, In e l -> B e <= x < B e + S e -> P x = Q x) ->
  sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. pose proof (sum_count_mono_in P Q l ltac:(intros e x He Hx; rewrite (H e x He Hx); auto)).
  pose proof (sum_count_mono_in Q P l ltac:(intros e x He Hx; rewrite (H e x He Hx); auto)). lia.
Qed.

Lemma sum_count_filter_le : forall P f l, sum_count P (List.filter f l) <= sum_count P l.
Proof.
  intros P f l. induction l as [|e l IH]; cbn -[Z.add]; [lia|].
  pose proof (zcount_nonneg P (B e) (Z.to_nat (S e))).
  destruct (f e); cbn -[Z.add]; unfold iv_count in *; lia.
Qed.

Lemma eager_used_sem : forall m,
  ivs_wf (vm_maps (m_vmmaps m)) ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hwf. pose proof (vm_backing_used_sem_maps m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Lemma eager_used_munmap_le : forall m (A n : word),
  model_ivs_wf m -> seps (vm_maps (m_vmmaps m)) -> In (A, n) (vm_maps (m_vmmaps m)) ->
  let h := m_vmmaps m in
  let lo := bv_unsigned A in let hi := lo + bv_unsigned n in
  let h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) A)
              (maps_subtract (vm_noaccess h) lo hi)
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
  eager_used (vm_forget_range lo hi (with_vmmaps h' m)) <= eager_used m.
Proof.
  intros m A n (Wm & Wn & Wl & _) Hs Hin. cbv zeta. pose proof (u64_range A) as RA. pose proof (u64_range n) as Rn.
  assert (Wm' : ivs_wf (map_remove (vm_maps (m_vmmaps m)) A)) by (unfold map_remove; apply ivs_wf_filter; exact Wm).
  rewrite (eager_used_sem m Wm). rewrite eager_used_sem by (model_proj; cbn [vm_maps]; exact Wm').
  model_proj. cbn [vm_maps vm_noaccess].
  destruct (maps_subtract_sem (vm_noaccess (m_vmmaps m)) (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem (m_vm_lazy m) (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wl ltac:(lia)) as (_ & _ & Cl).
  etransitivity; [| apply (sum_count_filter_le _ (fun p => negb (bv_eqb (fst p) A)))]. unfold map_remove.
  apply Z.eq_le_incl. apply sum_count_ext_in. intros e x He Hx.
  apply filter_In in He as [He Hne]. rewrite !covered_app, Cn, Cl.
  assert (Hout : in_rng (bv_unsigned A) (bv_unsigned A + bv_unsigned n) x = false).
  { destruct (seps_in_disjoint _ _ _ Hs He Hin) as [->|D].
    - cbn [fst] in Hne. rewrite bv_eqb_refl in Hne. discriminate.
    - unfold iv_disjoint, B, S in *. cbn [fst snd] in D. unfold in_rng. apply andb_false_iff.
      destruct D as [D|D]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia]. }
  rewrite Hout. cbn [negb]. rewrite !andb_true_r. reflexivity.
Qed.

Lemma eager_used_grant_rw_le : forall m (a n : word),
  ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (a, n) ->
  eager_used (with_vmmaps (grant_maps (m_vmmaps m) a n) m) <= eager_used m + bv_unsigned n.
Proof.
  intros m a n Wm Wa. pose proof (u64_range n) as Rn.
  rewrite (eager_used_sem m Wm). rewrite eager_used_sem by (model_proj; cbn [vm_maps grant_maps]; apply ivs_wf_cons; assumption).
  model_proj. cbn [vm_maps vm_noaccess grant_maps sum_count].
  pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (B (a, n)) (Z.to_nat (S (a, n)))) as L.
  unfold iv_count. unfold S in L |- *. cbn [snd] in L |- *. rewrite Z2Nat.id in L by lia. lia.
Qed.

Lemma eager_used_grant_none_le : forall m (a n : word),
  ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (a, n) ->
  let h := m_vmmaps m in
  let h' := mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
  eager_used (with_vmmaps h' m) <= eager_used m.
Proof.
  intros m a n Wm Wa. cbv zeta. pose proof (u64_range n) as Rn. pose proof (u64_range a) as Ra.
  rewrite (eager_used_sem m Wm). rewrite eager_used_sem by (model_proj; cbn [vm_maps]; apply ivs_wf_cons; assumption).
  model_proj. cbn [vm_maps vm_noaccess sum_count].
  unfold iv_count at 1. rewrite zcount_false.
  2:{ intros x Hx. unfold B, S in Hx. cbn [fst snd] in Hx. rewrite Z2Nat.id in Hx by lia.
      apply negb_false_iff. cbn [app]. unfold covered. cbn [existsb]. unfold in_iv at 1. unfold in_rng, B, S. cbn [fst snd].
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Z.add_0_l. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  cbn [app] in Hx. unfold covered in Hx |- *. cbn [existsb] in Hx. apply orb_false_iff in Hx as [_ Hx]. exact Hx.
Qed.

Lemma eager_used_grant_nr_le : forall m (a n : word),
  ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (a, n) ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n ->
  eager_used (vm_add_lazy a n (with_vmmaps (grant_maps (m_vmmaps m) a n) m)) <= eager_used m.
Proof.
  intros m a n Wm Wa Hal Hnl Hpos. pose proof (u64_range n) as Rn. pose proof (u64_range a) as Ra.
  unfold iv_wf, B, S in Wa. cbn [fst snd] in Wa.
  rewrite (eager_used_sem m Wm). rewrite eager_used_sem by (model_proj; cbn [vm_maps grant_maps]; apply ivs_wf_cons; [unfold iv_wf, B, S; cbn; lia| assumption]).
  model_proj. cbn [vm_maps vm_noaccess grant_maps sum_count]. rewrite (lazy_interior_aligned a n Hal Hnl Hpos Wa).
  unfold iv_count at 1. rewrite zcount_false.
  2:{ intros x Hx. unfold B, S in Hx. cbn [fst snd] in Hx. rewrite Z2Nat.id in Hx by lia.
      apply negb_false_iff. rewrite covered_app. apply orb_true_iff. right. cbn [app]. unfold covered. cbn [existsb].
      unfold in_iv at 1. unfold in_rng, B, S. cbn [fst snd].
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Z.add_0_l. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  rewrite covered_app in Hx |- *. apply orb_false_iff in Hx as [H1 H2]. apply orb_false_iff. split; [exact H1|].
  cbn [app] in H2. unfold covered in H2. cbn [existsb] in H2. apply orb_false_iff in H2 as [_ H2]. exact H2.
Qed.

Lemma eager_used_guard_le : forall m (A n : word),
  model_ivs_wf m ->
  let h := m_vmmaps m in
  let lo := bv_unsigned A in let hi := lo + bv_unsigned n in
  let h' := mkVmMapsFull (vm_reserved h) (vm_maps h) ((A, n) :: maps_subtract (vm_noaccess h) lo hi)
              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
  eager_used (vm_forget_range lo hi (with_vmmaps h' m)) <= eager_used m.
Proof.
  intros m A n (Wm & Wn & Wl & _). cbv zeta. pose proof (u64_range A) as RA. pose proof (u64_range n) as Rn.
  rewrite (eager_used_sem m Wm). rewrite eager_used_sem by (model_proj; cbn [vm_maps]; exact Wm).
  model_proj. cbn [vm_maps vm_noaccess].
  destruct (maps_subtract_sem (vm_noaccess (m_vmmaps m)) (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem (m_vm_lazy m) (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wl ltac:(lia)) as (_ & _ & Cl).
  apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  rewrite covered_app in Hx |- *. cbn [app] in Hx.
  change (covered ((A, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned A) (bv_unsigned A + bv_unsigned n)) x)
    with (in_iv (A, n) x || covered (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned A) (bv_unsigned A + bv_unsigned n)) x)%bool in Hx.
  rewrite Cn, Cl in Hx. apply orb_false_iff in Hx as [H1 H2]. apply orb_false_iff in H1 as [H0 H1].
  unfold in_iv, B, S in H0. cbn [fst snd] in H0.
  destruct (in_rng (bv_unsigned A) (bv_unsigned A + bv_unsigned n) x) eqn:R.
  - discriminate.
  - cbn [negb] in H1, H2. rewrite andb_true_r in H1, H2. rewrite H1, H2. reflexivity.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require LZPages.
Import ListNotations.
Open Scope Z_scope.

Definition madv_post (mo : Model) (lo hi : Z) : Model :=
  with_vm_backing (m_vm_lazy mo) (cut_pages lo hi (m_vm_materialized mo)) mo.

Lemma filter_partition_length {A} : forall (f : A -> bool) l,
  (length (List.filter f l) + length (List.filter (fun x => negb (f x)) l) = length l)%nat.
Proof. intros f l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f x); cbn; lia. Qed.

Definition pages_in (lo hi : Z) (P : list word) : list word := List.filter (fun p => negb (page_outside_range lo hi p)) P.

Lemma cut_pages_length_eq : forall lo hi P,
  Z.of_nat (length (cut_pages lo hi P)) + Z.of_nat (length (pages_in lo hi P)) = Z.of_nat (length P).
Proof. intros lo hi P. unfold cut_pages, pages_in. pose proof (filter_partition_length (page_outside_range lo hi) P). lia. Qed.

Lemma madv_post_used : forall mo lo hi,
  vm_backing_used (madv_post mo lo hi) + Z.of_nat (length (pages_in lo hi (m_vm_materialized mo))) * page_size = vm_backing_used mo.
Proof.
  intros mo lo hi. unfold vm_backing_used, madv_post.
  rewrite m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing, m_vm_materialized_with_vm_backing.
  pose proof (cut_pages_length_eq lo hi (m_vm_materialized mo)). unfold page_size. lia.
Qed.

Lemma pages_in_ge : forall lo hi P (ps : list word),
  List.NoDup ps -> (forall q, In q ps -> In q P /\ lo <= bv_unsigned q < hi) ->
  Z.of_nat (length ps) <= Z.of_nat (length (pages_in lo hi P)).
Proof.
  intros lo hi P ps ND H. apply Nat2Z.inj_le. apply NoDup_incl_length; [exact ND|].
  intros q Hq. destruct (H q Hq) as [Hin Hr]. unfold pages_in. apply filter_In. split; [exact Hin|].
  unfold page_outside_range. rewrite negb_involutive. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma pagesN_NoDup : forall k lo, 0 <= lo -> lo + Z.of_nat k * page_size <= 2^64 -> List.NoDup (pagesN lo k).
Proof.
  induction k as [|k IH]; intros lo Hlo Hhi; cbn [pagesN]; [constructor|]. unfold page_size in *.
  constructor.
  - intros Hin. apply LZPages.pagesN_in in Hin. destruct Hin as (i & Hi & E).
    apply (f_equal bv_unsigned) in E. rewrite !fg_lit in E by (unfold page_size in *; lia). unfold page_size in *. lia.
  - apply IH; unfold page_size; lia.
Qed.

Definition sub_iv (e' e : word * word) : Prop := vlo e <= vlo e' /\ vhi e' <= vhi e.

Lemma iv_subtract_sub : forall (a sz : word) lo hi e',
  bv_unsigned a + bv_unsigned sz <= 2^64 -> In e' (iv_subtract a sz lo hi) -> sub_iv e' (a, sz).
Proof.
  intros a sz lo hi e' Hwf Hin. unfold iv_subtract in Hin. cbv zeta in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
  change (2 ^ Z.of_N 64) with (2^64) in Ra, Rs.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [Hlt|]; [| destruct Hin]. destruct Hin as [<-|[]].
    unfold sub_iv, vhi, vlo, vsz. cbn [fst snd].
    destruct (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)) as [[? E]|[? E]]; rewrite E; rewrite fg_lit by lia; lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Hlt|]; [| destruct Hin]. destruct Hin as [<-|[]].
    unfold sub_iv, vhi, vlo, vsz. cbn [fst snd].
    destruct (Z.max_spec (bv_unsigned a) hi) as [[? E]|[? E]]; rewrite E; rewrite !fg_lit by lia; lia.
Qed.

Lemma maps_subtract_sub : forall l lo hi e', ivs_wf l -> In e' (maps_subtract l lo hi) -> exists e, In e l /\ sub_iv e' e.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi e' Hwf Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin. destruct (ivs_wf_cons_inv _ _ Hwf) as [Wp Wl]. destruct Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. apply (iv_subtract_sub a sz lo hi e'); [exact Wp| exact Hin].
  - destruct (IH lo hi e' Wl Hin) as (e & He & Hs). exists e. split; [right; exact He| exact Hs].
Qed.

Definition off_band (bl bh : Z) (e : word * word) : Prop := vhi e <= bl \/ bh <= vlo e.

Lemma off_band_sub : forall bl bh e e', sub_iv e' e -> vlo e' <= vhi e' -> off_band bl bh e -> off_band bl bh e'.
Proof. intros bl bh e e' [H1 H2] H3 [H|H]; [left| right]; lia. Qed.

Lemma maps_subtract_off_band : forall bl bh l lo hi, ivs_wf l -> lo <= hi ->
  Forall (off_band bl bh) l -> Forall (off_band bl bh) (maps_subtract l lo hi).
Proof.
  intros bl bh l lo hi Hwf Hlh HF. apply Forall_forall. intros e' Hin.
  destruct (maps_subtract_sub l lo hi e' Hwf Hin) as (e & He & Hs).
  apply (off_band_sub bl bh e e' Hs); [| exact (proj1 (Forall_forall _ _) HF e He)].
  unfold vhi. pose proof (vsz_nonneg e'). lia.
Qed.

Lemma region_free_off_band : forall bl bh l (a n : word),
  Forall (off_band bl bh) l -> bl <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bh -> region_free l a n = true.
Proof.
  intros bl bh l a n HF Hlo Hhi. induction HF as [|[b s] l He Hl IH]; [reflexivity|].
  cbn [region_free]. rewrite IH, andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  unfold off_band, vhi, vlo, vsz in He. cbn [fst snd] in He. destruct He; [left| right]; apply Z.ltb_ge; lia.
Qed.

Definition SHOFF : Z := 0x7fff8000.
Definition shZ (x : Z) : Z := x / 8 + SHOFF.
Definition pgupZ (x : Z) : Z := ((x + 4096 - 1) / 4096) * 4096.
Definition pgdnZ (x : Z) : Z := (x / 4096) * 4096.

Lemma shw_lo_pgdn : forall a, shw_lo SHOFF a = pgdnZ (shZ a).
Proof. reflexivity. Qed.
Lemma shw_hi_pgup : forall a n, shw_hi SHOFF a n = pgupZ (shZ (a + n)).
Proof. intros. unfold shw_hi, pgupZ, shZ, page_size. f_equal. f_equal. lia. Qed.

Definition inner_range (p n : Z) : option (Z * Z) :=
  let pb := pgupZ (shZ p) in let pe := pgdnZ (shZ (p + n)) in if pe <=? pb then None else Some (pb, pe).
Definition inner_pages (p n : Z) : list word :=
  match inner_range p n with None => [] | Some (pb, pe) => pages_of pb pe end.
Definition inner_bytes (p n : Z) : Z := Z.of_nat (length (inner_pages p n)) * page_size.
Definition hull_pages (p n : Z) : list word := pages_of (shw_lo SHOFF p) (shw_hi SHOFF p n).

Lemma pg_facts : forall x, 0 <= x ->
  pgdnZ x <= x /\ x <= pgupZ x /\ pgupZ x < x + 4096 /\ x - 4096 < pgdnZ x /\ pgdnZ x mod 4096 = 0 /\ pgupZ x mod 4096 = 0 /\ 0 <= pgdnZ x
  /\ pgupZ x <= pgdnZ x + 4096.
Proof.
  intros x Hx. unfold pgdnZ, pgupZ.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; try (rewrite Z.mod_mul by lia; reflexivity); nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma shZ_mono : forall x y, x <= y -> shZ x <= shZ y.
Proof. intros x y H. unfold shZ. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

Lemma inner_pages_in : forall p n q, 0 <= p -> 0 <= n -> In q (inner_pages p n) ->
  exists z, q = Z_to_bv 64 z /\ z mod 4096 = 0 /\ shZ p <= z /\ z + 4096 <= shZ (p + n).
Proof.
  intros p n q Hp Hn Hin. unfold inner_pages, inner_range in Hin. cbv zeta in Hin.
  assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 Hp ltac:(lia)); lia).
  assert (He : 0 <= shZ (p + n)) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia)); lia).
  destruct (pg_facts (shZ p) Hs) as (_ & S2 & _ & _ & _ & S6 & _ & _).
  destruct (pg_facts (shZ (p + n)) He) as (E1 & _ & _ & _ & E5 & _ & _ & _).
  destruct (Z.leb_spec (pgdnZ (shZ (p + n))) (pgupZ (shZ p))) as [|Hlt]; [destruct Hin|].
  apply LZPages.pages_of_in in Hin; [| exact S6| exact E5| lia].
  destruct Hin as (z & Z1 & Z2 & Z3 & ->). exists z. unfold page_size in *. repeat split; try assumption; lia.
Qed.

Lemma inner_in_hull : forall p n q, 0 <= p -> 0 <= n -> In q (inner_pages p n) -> In q (hull_pages p n).
Proof.
  intros p n q Hp Hn Hin. destruct (inner_pages_in p n q Hp Hn Hin) as (z & -> & Z1 & Z2 & Z3).
  assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 Hp ltac:(lia)); lia).
  assert (He : 0 <= shZ (p + n)) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia)); lia).
  destruct (pg_facts (shZ p) Hs) as (S1 & _ & _ & _ & S5 & _ & _ & _).
  destruct (pg_facts (shZ (p + n)) He) as (_ & E2 & _ & _ & _ & E6 & _ & _).
  pose proof (shZ_mono p (p + n) ltac:(lia)).
  unfold hull_pages. rewrite shw_lo_pgdn, shw_hi_pgup. apply LZPages.pages_of_in; [exact S5| exact E6| lia|].
  exists z. unfold page_size. repeat split; try assumption; lia.
Qed.

Lemma inner_pages_NoDup : forall p n, 0 <= p -> 0 <= n -> p + n <= 2^47 -> List.NoDup (inner_pages p n).
Proof.
  intros p n Hp Hn H47. unfold inner_pages, inner_range. cbv zeta.
  assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 Hp ltac:(lia)); lia).
  assert (He : 0 <= shZ (p + n) <= 2^45) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia));
     pose proof (Z.div_le_mono (p + n) (2^47) 8 ltac:(lia) H47); change (2^47 / 8) with (2^44) in *; lia).
  destruct (pg_facts (shZ p) Hs) as (_ & S2 & _ & _ & _ & S6 & _ & _).
  destruct (pg_facts (shZ (p + n)) ltac:(lia)) as (E1 & _ & _ & _ & E5 & _ & _ & _).
  destruct (Z.leb_spec (pgdnZ (shZ (p + n))) (pgupZ (shZ p))) as [|Hlt]; [constructor|].
  unfold pages_of. apply pagesN_NoDup; [lia|].
  rewrite Z2Nat.id by (apply Z.div_pos; unfold page_size; lia). unfold page_size.
  pose proof (Z.mul_div_le (pgdnZ (shZ (p + n)) - pgupZ (shZ p)) 4096 ltac:(lia)). lia.
Qed.

Lemma hull_inner_edge : forall p n, 0 <= p -> 0 <= n ->
  Z.of_nat (length (hull_pages p n)) * page_size <= inner_bytes p n + 8192.
Proof.
  intros p n Hp Hn. unfold inner_bytes, inner_pages, inner_range, hull_pages. cbv zeta. rewrite shw_lo_pgdn, shw_hi_pgup.
  assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 Hp ltac:(lia)); lia).
  assert (He : 0 <= shZ (p + n)) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia)); lia).
  pose proof (shZ_mono p (p + n) ltac:(lia)) as Hm.
  destruct (pg_facts (shZ p) Hs) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct (pg_facts (shZ (p + n)) He) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  rewrite (LZPages.pages_of_length _ _ S5 E6 ltac:(lia)).
  destruct (Z.leb_spec (pgdnZ (shZ (p + n))) (pgupZ (shZ p))) as [Hle|Hlt].
  - cbn [length]. lia.
  - rewrite (LZPages.pages_of_length _ _ S6 E5 ltac:(lia)). lia.
Qed.

Definition pos_list (l : list (word * word)) : Prop := Forall (fun q => 0 < S q) l.

Lemma seps_same_base : forall l e e', seps l -> pos_list l -> In e l -> In e' l -> fst e = fst e' -> e = e'.
Proof.
  intros l e e' Hs Hp He He' Hb. destruct (LZPages.seps_in_disjoint l e e' Hs He He') as [E|D]; [exact E|].
  exfalso. pose proof (proj1 (Forall_forall _ _) Hp e He) as P1. pose proof (proj1 (Forall_forall _ _) Hp e' He') as P2.
  unfold iv_disjoint in D. unfold S in P1, P2. rewrite Hb in D. lia.
Qed.

Lemma seps_head_notin : forall e l, seps (e :: l) -> 0 < S e -> ~ In e l.
Proof.
  intros e l Hs Hp Hin. inversion Hs as [|e0 l0 HF _]; subst.
  pose proof (proj1 (Forall_forall _ _) HF e Hin) as D. unfold iv_disjoint in D. unfold S in Hp. lia.
Qed.

Lemma map_remove_perm : forall l (A n : word), seps l -> pos_list l -> In (A, n) l ->
  Permutation l ((A, n) :: map_remove l A).
Proof.
  induction l as [|e l IH]; intros A n Hs Hp Hin; [destruct Hin|].
  inversion Hs as [|e0 l0 HF Hs']; subst. inversion Hp as [|e1 l1 Pe Pl]; subst.
  unfold map_remove. cbn [List.filter]. destruct Hin as [->|Hin].
  - cbn [fst]. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. apply perm_skip.

    rewrite forallb_filter_id; [reflexivity|]. apply forallb_forall. intros q Hq.
    apply negb_true_iff. apply Z.eqb_neq. intros E.
    pose proof (proj1 (Forall_forall _ _) HF q Hq) as D. pose proof (proj1 (Forall_forall _ _) Pl q Hq) as Pq.
    unfold iv_disjoint in D. unfold S in Pe, Pq. cbn [fst snd] in D, Pe. lia.
  - assert (Hne : bv_eqb (fst e) A = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros E.
      pose proof (proj1 (Forall_forall _ _) HF (A, n) Hin) as D. pose proof (proj1 (Forall_forall _ _) Pl (A, n) Hin) as Pq.
      unfold iv_disjoint in D. unfold S in Pe, Pq. cbn [fst snd] in D, Pq. lia. }
    rewrite Hne. cbn [negb]. eapply perm_trans; [apply perm_skip; exact (IH A n Hs' Pl Hin)|]. apply perm_swap.
Qed.

Lemma Forall_permP {A} : forall (P : A -> Prop) l l', Permutation l l' -> Forall P l -> Forall P l'.
Proof. intros P l l' HP HF. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF). apply (Permutation_in _ (Permutation_sym HP)). exact Hx. Qed.

Lemma seps_perm : forall l1 l2, Permutation l1 l2 -> seps l1 -> seps l2.
Proof.
  intros l1 l2 HP. induction HP as [| x l1 l2 HP IH | x y l | l1 l2 l3 _ IH1 _ IH2]; intros H.
  - exact H.
  - inversion H as [|? ? HF Hs]; subst. constructor; [exact (Forall_permP _ _ _ HP HF)| exact (IH Hs)].
  - inversion H as [|? ? HF Hs]; subst. inversion Hs as [|? ? HF' Hs']; subst. inversion HF as [|? ? Dxy HFl]; subst.
    constructor; [constructor; [unfold iv_disjoint in *; lia| exact HF']| constructor; [exact HFl| exact Hs']].
  - exact (IH2 (IH1 H)).
Qed.

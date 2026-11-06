(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxAcct AxMeasure AxSysFix.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BIGMIN : Z := 65536.

(* [comment removed for export] *)
Definition lzfull (e : aent) : bool := aent_eqb e ls_ent || aent_eqb e hs_ent.

Lemma lzfull_cases (e : aent) : lzfull e = true -> e = ls_ent \/ e = hs_ent.
Proof. unfold lzfull. intros H. apply orb_true_iff in H as [H|H]; apply aent_eqb_eq in H; auto. Qed.

Lemma lzfull_not_var (e : aent) : lzfull e = true -> var_ent e = false.
Proof. intros H. destruct (lzfull_cases e H) as [->| ->]; reflexivity. Qed.

Lemma lzfull_var (e : aent) : var_ent e = true -> lzfull e = false.
Proof. intros H. destruct (lzfull e) eqn:E; [|reflexivity]. rewrite (lzfull_not_var e E) in H. discriminate H. Qed.

Lemma lzfull_na (e : aent) : ae_na e = true -> lzfull e = false.
Proof. intros H. destruct (lzfull e) eqn:E; [|reflexivity]. destruct (lzfull_cases e E) as [->| ->]; discriminate H. Qed.

Lemma lzfull_not_na (e : aent) : lzfull e = true -> ae_na e = false.
Proof. intros H. destruct (lzfull_cases e H) as [->| ->]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma lzfull_aligned (ρ : valuation) (e : aent) : lzfull e = true ->
  leval ρ (ae_base e) mod 4096 = 0 /\ (leval ρ (ae_base e) + ae_size e) mod 4096 = 0 /\ 0 <= leval ρ (ae_base e)
  /\ leval ρ (ae_base e) + ae_size e < two64.
Proof.
  intros H. destruct (lzfull_cases e H) as [->| ->]; unfold leval, ls_ent, hs_ent, two64; cbn [ae_base ae_size fst snd teval];
    rewrite Z.add_0_r; repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma lzfull_in_span (ρ : valuation) (e : aent) : lzfull e = true ->
  sh_lo <= leval ρ (ae_base e) /\ leval ρ (ae_base e) + ae_size e <= sh_hi.
Proof.
  intros H. destruct (lzfull_cases e H) as [->| ->]; unfold leval, ls_ent, hs_ent, sh_lo, sh_hi; cbn [ae_base ae_size fst snd teval]; lia.
Qed.

Section Raw.
Variable ρ : valuation.

Definition ent_lo (e : aent) : Z := leval ρ (ae_base e).
Definition ent_hi (e : aent) : Z := leval ρ (ae_base e) + ae_size e.

(* [comment removed for export] *)
Definition pos_al (q : word * word) : Prop := 0 < bsz q /\ bas q mod 4096 = 0 /\ bsz q mod 4096 = 0.

Definition LZr (ents : list aent) (lazy noacc : list (word * word)) : Prop :=
  (forall p, In p lazy -> 0 < bsz p ->
     exists e, In e ents /\ BIGMIN <= ae_size e /\ ent_lo e <= bas p /\ bas p + bsz p <= ent_hi e)
  /\ (forall e, In e ents -> lzfull e = true -> forall a : word, ent_lo e <= bv_unsigned a < ent_hi e ->
        page_in_ranges (page_base a) lazy = true /\ ~ inl noacc (bv_unsigned a))
  /\ Forall pos_al noacc
  (* [comment removed for export] *)
  /\ Forall pos_al lazy.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_base_val (a : word) : bv_unsigned (page_base a) = bv_unsigned a / 4096 * 4096.
Proof.
  unfold page_base, page_base_of, page_size. pose proof (bv_unsigned_in_range 64 a) as Ha. rewrite two64_mod in Ha.
  apply u_Z_to_bv. pose proof (Z.mul_div_le (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.div_pos (bv_unsigned a) 4096 ltac:(lia) ltac:(lia)).
  unfold two64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_aligned (a : word) (lo hi : Z) : lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned a < hi ->
  lo <= bv_unsigned (page_base a) /\ bv_unsigned (page_base a) + 4096 <= hi.
Proof.
  intros Hlo Hhi Ha. rewrite page_base_val.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)) as M.
  apply Z.mod_divide in Hlo; [|lia]. apply Z.mod_divide in Hhi; [|lia]. destruct Hlo as [ql ->]. destruct Hhi as [qh ->].
  set (q := bv_unsigned a / 4096) in *. assert (ql <= q) by nia. assert (q < qh) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma page_out_aligned (a : word) (lo hi : Z) : lo mod 4096 = 0 -> hi mod 4096 = 0 -> ~ (lo <= bv_unsigned a < hi) ->
  bv_unsigned (page_base a) + 4096 <= lo \/ hi <= bv_unsigned (page_base a).
Proof.
  intros Hlo Hhi Ha. rewrite page_base_val.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)) as M.
  apply Z.mod_divide in Hlo; [|lia]. apply Z.mod_divide in Hhi; [|lia]. destruct Hlo as [ql ->]. destruct Hhi as [qh ->].
  set (q := bv_unsigned a / 4096) in *.
  destruct (Z_lt_le_dec (bv_unsigned a) (ql * 4096)) as [L|L]; [left; assert (q < ql) by nia; nia|].
  right. assert (qh * 4096 <= bv_unsigned a) by lia. assert (qh <= q) by nia. nia.
Qed.

Lemma pir_app_r (p : word) (l1 l2 : list (word * word)) : page_in_ranges p l2 = true -> page_in_ranges p (l1 ++ l2) = true.
Proof. unfold page_in_ranges. rewrite existsb_app. intros ->. apply orb_true_r. Qed.

Lemma pir_app_l (p : word) (l1 l2 : list (word * word)) : page_in_ranges p l1 = true -> page_in_ranges p (l1 ++ l2) = true.
Proof. unfold page_in_ranges. rewrite existsb_app. intros ->. reflexivity. Qed.

Lemma pir_incl (p : word) (l1 l2 : list (word * word)) : (forall q, In q l1 -> In q l2) -> page_in_ranges p l1 = true -> page_in_ranges p l2 = true.
Proof.
  unfold page_in_ranges. intros Hi H. apply existsb_exists in H as [q [Hq Hb]]. apply existsb_exists. exists q. split; [exact (Hi q Hq) | exact Hb].
Qed.

Lemma pir_spec (p : word) (l : list (word * word)) :
  page_in_ranges p l = true <-> exists q, In q l /\ bas q <= bv_unsigned p /\ bv_unsigned p + 4096 <= bas q + bsz q.
Proof.
  unfold page_in_ranges, page_size, bas, bsz. split.
  - intros H. apply existsb_exists in H as [q [Hq Hb]]. exists q. split; [exact Hq|]. cbv zeta in Hb.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - intros [q [Hq [H1 H2]]]. apply existsb_exists. exists q. split; [exact Hq|]. cbv zeta.
    apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma pir_subtract_out (p : word) (l : list (word * word)) (lo hi : Z) : nowrap l ->
  bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p ->
  page_in_ranges p l = true -> page_in_ranges p (maps_subtract l lo hi) = true.
Proof.
  intros Hnw Hout H. apply pir_spec in H as [q [Hq [H1 H2]]]. apply pir_spec.
  induction l as [|[a sz] r IH]; [destruct Hq|]. apply nowrap_inv in Hnw as [Hn1 Hn2]. cbn [maps_subtract].
  destruct Hq as [<-|Hq].
  - unfold bas, bsz in H1, H2, Hn1. cbn [fst snd] in H1, H2, Hn1.
    pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. rewrite two64_mod in Ha, Hs.
    unfold iv_subtract. cbv zeta. destruct Hout as [Ho|Ho].
    + (* [comment removed for export] *)
      assert (E : (bv_unsigned a <? lo) = true) by (apply Z.ltb_lt; lia). rewrite E.
      exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). split; [apply in_or_app; left; apply in_or_app; left; left; reflexivity|].
      rewrite bas_mk, bsz_mk. rewrite u_Z_to_bv by (unfold two64 in *; lia). lia.
    + (* [comment removed for export] *)
      assert (E : (hi <? bv_unsigned a + bv_unsigned sz) = true) by (apply Z.ltb_lt; lia). rewrite E.
      exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)).
      split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      rewrite bas_mk, bsz_mk. rewrite !u_Z_to_bv by (unfold two64 in *; lia). lia.
  - destruct (IH Hn2 Hq) as [q' [Hq' X]]. exists q'. split; [apply in_or_app; right; exact Hq' | exact X].
Qed.

(* [comment removed for export] *)
Lemma pir_interior (p : word) (addr nw : word) : bv_unsigned addr mod 4096 = 0 -> bv_unsigned nw mod 4096 = 0 ->
  bv_unsigned addr + bv_unsigned nw <= two64 ->
  bv_unsigned addr <= bv_unsigned p -> bv_unsigned p + 4096 <= bv_unsigned addr + bv_unsigned nw ->
  page_in_ranges p (lazy_interior addr nw) = true.
Proof.
  intros Ha Hn H64 H1 H2. apply pir_spec. unfold lazy_interior, page_size. cbv zeta.
  pose proof (bv_unsigned_in_range 64 addr) as Ra. pose proof (bv_unsigned_in_range 64 nw) as Rn. rewrite two64_mod in Ra, Rn.
  assert (E1 : (bv_unsigned addr + 4096 - 1) / 4096 * 4096 = bv_unsigned addr).
  { apply Z.mod_divide in Ha; [|lia]. destruct Ha as [q ->]. replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (E2 : (bv_unsigned addr + bv_unsigned nw) / 4096 * 4096 = bv_unsigned addr + bv_unsigned nw).
  { assert (Hs : (bv_unsigned addr + bv_unsigned nw) mod 4096 = 0) by (rewrite Z.add_mod, Ha, Hn by lia; reflexivity).
    apply Z.mod_divide in Hs; [|lia]. destruct Hs as [q ->]. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E1, E2. assert (E : (bv_unsigned addr <? bv_unsigned addr + bv_unsigned nw) = true) by (apply Z.ltb_lt; lia). rewrite E.
  eexists. split; [left; reflexivity|]. rewrite bas_mk, bsz_mk. rewrite !u_Z_to_bv by (unfold two64 in *; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma posal_iv_subtract (a sz : word) (lo hi : Z) (p : word * word) : bv_unsigned a + bv_unsigned sz <= two64 ->
  pos_al (a, sz) -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> In p (iv_subtract a sz lo hi) -> pos_al p.
Proof.
  intros Hnw (P1 & P2 & P3) Hlo Hhi Hin. rewrite bas_mk in P2. rewrite bsz_mk in P1, P3.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. rewrite two64_mod in Ha, Hs.
  apply Z.mod_divide in P2; [|lia]. apply Z.mod_divide in P3; [|lia]. apply Z.mod_divide in Hlo; [|lia]. apply Z.mod_divide in Hhi; [|lia].
  destruct P2 as [qa Ea]. destruct P3 as [qs Es]. destruct Hlo as [ql El]. destruct Hhi as [qh Eh].
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]].
    unfold pos_al. rewrite bas_mk, bsz_mk. rewrite u_Z_to_bv by (unfold two64 in *; lia).
    split; [lia|]. split; [rewrite Ea; apply Z_mod_mult|].
    destruct (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)) as [[_ ->]|[_ ->]]; [rewrite Es; apply Z_mod_mult|].
    rewrite El, Ea. replace (ql * 4096 - qa * 4096) with ((ql - qa) * 4096) by lia. apply Z_mod_mult.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]].
    unfold pos_al. rewrite bas_mk, bsz_mk. rewrite !u_Z_to_bv by (unfold two64 in *; lia).
    split; [lia|]. destruct (Z.max_spec (bv_unsigned a) hi) as [[_ ->]|[_ ->]].
    + split; [rewrite Eh; apply Z_mod_mult|]. rewrite Ea, Es, Eh. replace (qa * 4096 + qs * 4096 - qh * 4096) with ((qa + qs - qh) * 4096) by lia. apply Z_mod_mult.
    + split; [rewrite Ea; apply Z_mod_mult|]. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia. rewrite Es. apply Z_mod_mult.
Qed.

Lemma posal_subtract (l : list (word * word)) (lo hi : Z) : nowrap l -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  Forall pos_al l -> Forall pos_al (maps_subtract l lo hi).
Proof.
  intros Hnw Hlo Hhi H. induction l as [|[a sz] r IH]; [constructor|]. apply nowrap_inv in Hnw as [N1 N2]. rewrite bas_mk, bsz_mk in N1.
  inversion H as [|? ? Hp Hr]; subst. cbn [maps_subtract]. apply Forall_app. split; [|exact (IH N2 Hr)].
  apply Forall_forall. intros p Hp'. exact (posal_iv_subtract a sz lo hi p N1 Hp Hlo Hhi Hp').
Qed.

(* [comment removed for export] *)
Lemma posal_interior (a n : word) : bv_unsigned a + bv_unsigned n <= two64 -> Forall pos_al (lazy_interior a n).
Proof.
  intros H64. unfold lazy_interior, page_size. cbv zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 n) as Hn. rewrite two64_mod in Ha, Hn.
  set (lo' := (bv_unsigned a + 4096 - 1) / 4096 * 4096). set (hi' := (bv_unsigned a + bv_unsigned n) / 4096 * 4096).
  destruct (lo' <? hi') eqn:E; [|constructor]. apply Z.ltb_lt in E. constructor; [|constructor].
  assert (L1 : 0 <= lo') by (unfold lo'; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  assert (L2 : hi' <= bv_unsigned a + bv_unsigned n) by (unfold hi'; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  unfold pos_al. rewrite bas_mk, bsz_mk. rewrite !u_Z_to_bv by (unfold two64 in *; lia).
  split; [lia|]. split; [unfold lo'; apply Z_mod_mult|]. unfold lo', hi'.
  replace ((bv_unsigned a + bv_unsigned n) / 4096 * 4096 - (bv_unsigned a + 4096 - 1) / 4096 * 4096)
    with (((bv_unsigned a + bv_unsigned n) / 4096 - (bv_unsigned a + 4096 - 1) / 4096) * 4096) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma lazy_piece (l : list (word * word)) (lo hi : Z) (p : word * word) : nowrap l -> In p (maps_subtract l lo hi) -> 0 < bsz p ->
  exists q, In q l /\ 0 < bsz q /\ bas q <= bas p /\ bas p + bsz p <= bas q + bsz q /\ (bas p + bsz p <= lo \/ hi <= bas p).
Proof.
  intros Hnw Hp Hpos. destruct (maps_subtract_in l lo hi p Hnw Hp) as (Hout & q & Hq & H1 & H2 & _).
  exists q. repeat split; try assumption. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LZr_nil : LZr [] [] [].
Proof. split; [intros p []|]. split; [intros e []|]. split; constructor. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LZr_grant (ents : list aent) (lazy noacc lazy' noacc' : list (word * word)) (e : aent) (a nZ : Z) :
  LZr ents lazy noacc ->
  ent_lo e = a -> ae_size e = nZ ->
  (forall e', In e' ents -> ent_hi e' <= a \/ a + nZ <= ent_lo e') ->
  (forall p, In p lazy' -> In p lazy \/ (a <= bas p /\ bas p + bsz p <= a + nZ /\ BIGMIN <= nZ)) ->
  (forall p, In p lazy -> In p lazy') ->
  (forall z, inl noacc' z -> inl noacc z \/ a <= z < a + nZ) ->
  Forall pos_al noacc' -> Forall pos_al lazy' ->
  (lzfull e = true -> forall x : word, a <= bv_unsigned x < a + nZ -> page_in_ranges (page_base x) lazy' = true /\ ~ inl noacc' (bv_unsigned x)) ->
  LZr (e :: ents) lazy' noacc'.
Proof.
  intros (Z1 & Z2 & Z4 & Z6) Elo Esz Hdisj Hlz Hmono Hna Hpos Hposl Hfull. split; [|split; [|split; [exact Hpos | exact Hposl]]].
  - intros p Hp Hpp. destruct (Hlz p Hp) as [Hp'|(L1 & L2 & L3)].
    + destruct (Z1 p Hp' Hpp) as (e' & He' & X). exists e'. split; [right; exact He' | exact X].
    + exists e. split; [left; reflexivity|]. unfold ent_hi. rewrite Esz. fold (ent_lo e). rewrite Elo. lia.
  - intros e' [<-|He'] Hf x Hx.
    + unfold ent_hi in Hx. fold (ent_lo e) in Hx. rewrite Esz, Elo in Hx. exact (Hfull Hf x Hx).
    + destruct (Z2 e' He' Hf x Hx) as [P1 P2]. split; [exact (pir_incl _ lazy lazy' Hmono P1)|].
      intros Hi. destruct (Hna _ Hi) as [Hi'|Hr]; [exact (P2 Hi')|]. destruct (Hdisj e' He'); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Cut.
Variables (ents : list aent) (lazy noacc : list (word * word)).
Hypothesis HZ : LZr ents lazy noacc.
Hypothesis Hlnw : nowrap lazy.
Hypothesis Hnnw : nowrap noacc.
Variable e0 : aent.
Hypothesis He0 : In e0 ents.
(* [comment removed for export] *)
Hypothesis Hdisj : forall e, In e ents -> e <> e0 -> ent_hi e <= ent_lo e0 \/ ent_hi e0 <= ent_lo e.
Variables addr nw : word.
Hypothesis Hin : ent_lo e0 <= bv_unsigned addr /\ bv_unsigned addr + bv_unsigned nw <= ent_hi e0.
Hypothesis Hn : 0 < bv_unsigned nw.
Hypothesis H64 : bv_unsigned addr + bv_unsigned nw <= two64.
(* [comment removed for export] *)
Hypothesis Hal : bv_unsigned addr mod 4096 = 0 /\ bv_unsigned nw mod 4096 = 0.

Notation lo := (bv_unsigned addr).
Notation hi := (bv_unsigned addr + bv_unsigned nw).

(* [comment removed for export] *)
Lemma cut_Z1 (flags : word) : (mmap_noreserve_b flags = true -> BIGMIN <= ae_size e0) ->
  forall p, In p (repl_lazy flags addr nw lazy) -> 0 < bsz p ->
    exists e, In e ents /\ BIGMIN <= ae_size e /\ ent_lo e <= bas p /\ bas p + bsz p <= ent_hi e.
Proof.
  intros Hbig p Hp Hpp. destruct HZ as (Z1 & _ & _).
  assert (Hsub : In p (maps_subtract lazy lo hi) -> exists e, In e ents /\ BIGMIN <= ae_size e /\ ent_lo e <= bas p /\ bas p + bsz p <= ent_hi e).
  { intros Hp'. destruct (lazy_piece lazy lo hi p Hlnw Hp' Hpp) as (q & Hq & Hqp & Q1 & Q2 & _).
    destruct (Z1 q Hq Hqp) as (e & He & Hb & E1 & E2). exists e. repeat split; try assumption; lia. }
  unfold repl_lazy in Hp. destruct (mmap_noreserve_b flags) eqn:Ef; [|exact (Hsub Hp)].
  apply in_app_or in Hp as [Hp|Hp]; [|exact (Hsub Hp)].
  destruct (lazy_interior_within addr nw p H64 Hp) as (_ & L1 & L2).
  exists e0. split; [exact He0|]. split; [exact (Hbig eq_refl)|]. lia.
Qed.

(* [comment removed for export] *)
Lemma cut_Z2_lazy (flags : word) :
  (lzfull e0 = true -> mmap_noreserve_b flags = true /\ lo mod 4096 = 0 /\ bv_unsigned nw mod 4096 = 0) ->
  forall e, In e ents -> lzfull e = true -> forall a : word, ent_lo e <= bv_unsigned a < ent_hi e ->
    page_in_ranges (page_base a) (repl_lazy flags addr nw lazy) = true.
Proof.
  intros Hfull e He Hf a Ha. destruct HZ as (_ & Z2 & _). destruct (Z2 e He Hf a Ha) as [P1 _].
  destruct (lzfull_aligned ρ e Hf) as (A1 & A2 & A3 & A4). fold (ent_lo e) in A1, A3. fold (ent_hi e) in A2, A4.
  destruct (page_in_aligned a (ent_lo e) (ent_hi e) A1 A2 Ha) as [G1 G2].
  assert (Hout : bv_unsigned (page_base a) + 4096 <= lo \/ hi <= bv_unsigned (page_base a) ->
                 page_in_ranges (page_base a) (repl_lazy flags addr nw lazy) = true).
  { intros Ho. unfold repl_lazy. destruct (mmap_noreserve_b flags); [apply pir_app_r|]; exact (pir_subtract_out _ lazy lo hi Hlnw Ho P1). }
  destruct (aent_eq_dec e e0) as [->|Hd].
  - destruct (Hfull Hf) as (Fn & Fa & Fz).
    assert (Fh : hi mod 4096 = 0) by (rewrite Z.add_mod, Fa, Fz by lia; reflexivity).
    destruct (Z_lt_le_dec (bv_unsigned a) lo) as [L|L]; [apply Hout; apply (page_out_aligned a lo hi Fa Fh); lia|].
    destruct (Z_lt_le_dec (bv_unsigned a) hi) as [L2|L2]; [|apply Hout; apply (page_out_aligned a lo hi Fa Fh); lia].
    destruct (page_in_aligned a lo hi Fa Fh ltac:(lia)) as [I1 I2].
    unfold repl_lazy. rewrite Fn. apply pir_app_l. exact (pir_interior _ addr nw Fa Fz H64 I1 I2).
  - apply Hout. destruct (Hdisj e He Hd); lia.
Qed.

(* [comment removed for export] *)
Lemma cut_Z2_na_sub : forall e, In e ents -> lzfull e = true -> forall a : word, ent_lo e <= bv_unsigned a < ent_hi e ->
  ~ inl (maps_subtract noacc lo hi) (bv_unsigned a).
Proof.
  intros e He Hf a Ha Hi. destruct HZ as (_ & Z2 & _). destruct (Z2 e He Hf a Ha) as [_ P2].
  apply (inl_subtract1 _ _ _ _ Hnnw) in Hi as [Hi _]. exact (P2 Hi).
Qed.

(* [comment removed for export] *)
Lemma cut_Z2_na_cons : lzfull e0 = false -> forall e, In e ents -> lzfull e = true -> forall a : word, ent_lo e <= bv_unsigned a < ent_hi e ->
  ~ inl ((addr, nw) :: maps_subtract noacc lo hi) (bv_unsigned a).
Proof.
  intros Hnf e He Hf a Ha Hi. apply inl_cons in Hi as [Hi|Hi]; [|exact (cut_Z2_na_sub e He Hf a Ha Hi)].
  rewrite bas_mk, bsz_mk in Hi. assert (Hd : e <> e0) by (intros ->; rewrite Hf in Hnf; discriminate Hnf).
  destruct (Hdisj e He Hd); lia.
Qed.

Lemma cut_hi_al : hi mod 4096 = 0.
Proof. destruct Hal as [A1 A2]. rewrite Z.add_mod, A1, A2 by lia. reflexivity. Qed.

Lemma cut_Z4_sub : Forall pos_al (maps_subtract noacc lo hi).
Proof. destruct HZ as (_ & _ & Z4 & _). exact (posal_subtract noacc lo hi Hnnw (proj1 Hal) cut_hi_al Z4). Qed.

Lemma cut_Z6 (flags : word) : Forall pos_al (repl_lazy flags addr nw lazy).
Proof.
  destruct HZ as (_ & _ & _ & Z6). pose proof (posal_subtract lazy lo hi Hlnw (proj1 Hal) cut_hi_al Z6) as X.
  unfold repl_lazy. destruct (mmap_noreserve_b flags); [apply Forall_app; split; [exact (posal_interior addr nw H64) | exact X] | exact X].
Qed.

(* [comment removed for export] *)
Theorem LZr_fix (flags : word) :
  (mmap_noreserve_b flags = true -> BIGMIN <= ae_size e0) ->
  (lzfull e0 = true -> mmap_noreserve_b flags = true /\ lo mod 4096 = 0 /\ bv_unsigned nw mod 4096 = 0) ->
  LZr ents (repl_lazy flags addr nw lazy) (maps_subtract noacc lo hi).
Proof.
  intros Hbig Hfull. split; [exact (cut_Z1 flags Hbig)|]. split; [|split; [exact cut_Z4_sub | exact (cut_Z6 flags)]].
  intros e He Hf a Ha. split; [exact (cut_Z2_lazy flags Hfull e He Hf a Ha) | exact (cut_Z2_na_sub e He Hf a Ha)].
Qed.

(* [comment removed for export] *)
Theorem LZr_none (flags : word) :
  (mmap_noreserve_b flags = true -> BIGMIN <= ae_size e0) -> lzfull e0 = false ->
  LZr ents (repl_lazy flags addr nw lazy) ((addr, nw) :: maps_subtract noacc lo hi).
Proof.
  intros Hbig Hnf. split; [exact (cut_Z1 flags Hbig)|]. split.
  - intros e He Hf a Ha. split; [|exact (cut_Z2_na_cons Hnf e He Hf a Ha)].
    refine (cut_Z2_lazy flags _ e He Hf a Ha). intros X. rewrite X in Hnf. discriminate Hnf.
  - split; [|exact (cut_Z6 flags)]. constructor; [|exact cut_Z4_sub]. unfold pos_al. rewrite bas_mk, bsz_mk. destruct Hal as [A1 A2]. auto.
Qed.

(* [comment removed for export] *)
Theorem LZr_prot : LZr ents lazy (maps_subtract noacc lo hi).
Proof.
  destruct HZ as (Z1 & Z2 & Z4 & Z6). split; [exact Z1|]. split; [|split; [exact cut_Z4_sub | exact Z6]].
  intros e He Hf a Ha. split; [exact (proj1 (Z2 e He Hf a Ha)) | exact (cut_Z2_na_sub e He Hf a Ha)].
Qed.

End Cut.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem LZr_unmap (ents : list aent) (lazy noacc : list (word * word)) (e0 : aent) :
  LZr ents lazy noacc -> nowrap lazy -> nowrap noacc -> In e0 ents ->
  (forall e, In e ents -> e <> e0 -> ent_hi e <= ent_lo e0 \/ ent_hi e0 <= ent_lo e) ->
  lzfull e0 = false -> 0 < ae_size e0 -> ent_lo e0 mod 4096 = 0 -> ent_hi e0 mod 4096 = 0 ->
  LZr (List.filter (fun e => negb (aent_eqb e e0)) ents) (maps_subtract lazy (ent_lo e0) (ent_hi e0)) (maps_subtract noacc (ent_lo e0) (ent_hi e0)).
Proof.
  intros (Z1 & Z2 & Z4 & Z6) Hlnw Hnnw He0 Hdisj Hnf Hsz Hal0 Hal1.
  assert (Hfl : forall e, In e (List.filter (fun e => negb (aent_eqb e e0)) ents) <-> In e ents /\ e <> e0).
  { intros e. rewrite filter_In. split; intros [H1 H2]; (split; [exact H1|]).
    - intros ->. rewrite aent_eqb_refl in H2. discriminate H2.
    - destruct (aent_eqb e e0) eqn:E; [apply aent_eqb_eq in E; contradiction | reflexivity]. }
  split; [|split; [|split; [exact (posal_subtract noacc _ _ Hnnw Hal0 Hal1 Z4) | exact (posal_subtract lazy _ _ Hlnw Hal0 Hal1 Z6)]]].
  - intros p Hp Hpp. destruct (lazy_piece lazy _ _ p Hlnw Hp Hpp) as (q & Hq & Hqp & Q1 & Q2 & Qout).
    destruct (Z1 q Hq Hqp) as (e & He & Hb & E1 & E2). exists e. split; [|repeat split; try assumption; lia].
    apply (proj2 (Hfl e)). split; [exact He|]. intros ->. lia.
  - intros e He Hf a Ha. apply (proj1 (Hfl e)) in He as [He Hd]. destruct (Z2 e He Hf a Ha) as [P1 P2].
    destruct (lzfull_aligned ρ e Hf) as (A1 & A2 & A3 & A4). fold (ent_lo e) in A1, A3. fold (ent_hi e) in A2, A4.
    destruct (page_in_aligned a (ent_lo e) (ent_hi e) A1 A2 Ha) as [G1 G2]. split.
    + apply (pir_subtract_out _ lazy _ _ Hlnw); [|exact P1]. destruct (Hdisj e He Hd); lia.
    + intros Hi. apply (inl_subtract1 _ _ _ _ Hnnw) in Hi as [Hi _]. exact (P2 Hi).
Qed.

End Raw.

(* [comment removed for export] *)
Lemma LZr_ext (ρ ρ' : valuation) (ents : list aent) (lazy noacc : list (word * word)) :
  (forall e, In e ents -> leval ρ' (ae_base e) = leval ρ (ae_base e)) -> LZr ρ ents lazy noacc -> LZr ρ' ents lazy noacc.
Proof.
  intros Hag (Z1 & Z2 & Z46). split; [|split; [|exact Z46]].
  - intros p Hp Hpp. destruct (Z1 p Hp Hpp) as (e & He & Hb & E1 & E2). exists e. unfold ent_lo, ent_hi in *. rewrite (Hag e He). auto.
  - intros e He Hf a Ha. unfold ent_lo, ent_hi in *. rewrite (Hag e He) in Ha. exact (Z2 e He Hf a Ha).
Qed.

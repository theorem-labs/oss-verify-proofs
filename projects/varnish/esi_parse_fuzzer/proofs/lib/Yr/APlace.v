(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietlt6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietlt6.dlia_stock.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zone : Type := (Z * Z)%type.

(* [comment removed for export] *)
Definition zclamp (z : zone) (x y : Z) : Z :=
  Z.max 0 (Z.min (snd z) y - Z.max (fst z) x).

(* [comment removed for export] *)
Definition zmeets (z : zone) (x y : Z) : Prop :=
  fst z < snd z /\ fst z < y /\ x < snd z.

Lemma zmeets_dec : forall z x y, {zmeets z x y} + {~ zmeets z x y}.
Proof.
  intros [lo hi] x y. unfold zmeets. cbn.
  destruct (Z_lt_le_dec lo hi); [|right; lia].
  destruct (Z_lt_le_dec lo y); [|right; lia].
  destruct (Z_lt_le_dec x hi); [left; lia|right; lia].
Qed.

Fixpoint zsum_in (zs : list zone) (x y : Z) : Z :=
  match zs with [] => 0 | z :: r => zclamp z x y + zsum_in r x y end.

Fixpoint zcount (zs : list zone) (x y : Z) : Z :=
  match zs with [] => 0 | z :: r => (if zmeets_dec z x y then 1 else 0) + zcount r x y end.

(* [comment removed for export] *)
Definition zapart (z z' : zone) : Prop :=
  snd z <= fst z' \/ snd z' <= fst z \/ snd z <= fst z \/ snd z' <= fst z'.

Fixpoint zdisj (zs : list zone) : Prop :=
  match zs with
  | [] => True
  | z :: r => (forall z', In z' r -> zapart z z') /\ zdisj r
  end.

(* [comment removed for export] *)
Definition zavoids (g K : Z) (z : zone) : Prop :=
  fst z < snd z -> snd z <= g \/ g + K <= fst z.

Lemma zclamp_nonneg : forall z x y, 0 <= zclamp z x y.
Proof. intros. unfold zclamp. lia. Qed.

Lemma zsum_in_nonneg : forall zs x y, 0 <= zsum_in zs x y.
Proof. induction zs as [|z r IH]; intros; cbn; [lia|]. pose proof (zclamp_nonneg z x y). specialize (IH x y). lia. Qed.

Lemma zcount_nonneg : forall zs x y, 0 <= zcount zs x y.
Proof. induction zs as [|z r IH]; intros; cbn; [lia|]. specialize (IH x y). destruct (zmeets_dec z x y); lia. Qed.

Lemma zclamp_notmeets : forall z x y, ~ zmeets z x y -> zclamp z x y = 0.
Proof. intros [lo hi] x y H. unfold zmeets, zclamp in *. cbn in *. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zsplit1 : forall (z : zone) (l h x y : Z),
  zapart (l, h) z -> l < h -> l < y -> x < h ->
  zclamp z x (Z.max l x) + zclamp z (Z.min h y) y <= zclamp z x y
  /\ (zmeets z x (Z.max l x) -> zmeets z x y)
  /\ (zmeets z (Z.min h y) y -> zmeets z x y)
  /\ ~ (zmeets z x (Z.max l x) /\ zmeets z (Z.min h y) y).
Proof.
  intros [lo hi] l h x y Hz Hlh Hly Hxh. unfold zapart, zclamp, zmeets in *. cbn in *.
  destruct (Z.le_ge_cases l x) as [Lx|Lx];
    [rewrite (Z.max_r l x) by lia | rewrite (Z.max_l l x) by lia];
  destruct (Z.le_ge_cases h y) as [Hy|Hy];
    [rewrite (Z.min_l h y) by lia | rewrite (Z.min_r h y) by lia
    |rewrite (Z.min_l h y) by lia | rewrite (Z.min_r h y) by lia];
  (destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [ | | lia | ]);
  (split; [|split; [|split]]; try lia).
Qed.

Lemma zsplit : forall zs (l h x y : Z),
  (forall z', In z' zs -> zapart (l, h) z') -> l < h -> l < y -> x < h ->
  zsum_in zs x (Z.max l x) + zsum_in zs (Z.min h y) y <= zsum_in zs x y
  /\ zcount zs x (Z.max l x) + zcount zs (Z.min h y) y <= zcount zs x y.
Proof.
  induction zs as [|z r IH]; intros l h x y Hap Hlh Hly Hxh; cbn; [lia|].
  destruct (IH l h x y ltac:(intros z' Hz'; apply Hap; right; exact Hz') Hlh Hly Hxh) as [IHs IHc].
  (first [ pose proof ((zsplit1 z l h x y ltac:(apply Hap; left; reflexivity) Hlh Hly Hxh)) as dR_1; dand4 dR_1 as S1 M1 M2 M12 | destruct (zsplit1 z l h x y ltac:(apply Hap; left; reflexivity) Hlh Hly Hxh) as (S1 & M1 & M2 & M12) ]).
  split; [lia|].
  destruct (zmeets_dec z x (Z.max l x)) as [A|A];
  destruct (zmeets_dec z (Z.min h y) y) as [B|B];
  destruct (zmeets_dec z x y) as [C|C]; try lia.
  all: exfalso; first [exact (M12 (conj A B)) | exact (C (M1 A)) | exact (C (M2 B))].
Qed.

(* [comment removed for export] *)
Lemma zone_gap : forall zs x y K,
  0 < K -> zdisj zs ->
  zsum_in zs x y + (zcount zs x y + 1) * K <= y - x ->
  exists g, x <= g /\ g + K <= y /\ forall z, In z zs -> zavoids g K z.
Proof.
  induction zs as [|z r IH]; intros x y K HK Hd Hlen.
  - exists x. cbn in Hlen. split; [lia|]. split; [lia|]. intros z [].
  - cbn in Hlen. destruct Hd as [Hap Hd].
    pose proof (zsum_in_nonneg r x y) as S0. pose proof (zcount_nonneg r x y) as C0.
    pose proof (zclamp_nonneg z x y) as Z0.
    destruct (zmeets_dec z x y) as [M|M].
    + (* [comment removed for export] *)
      destruct z as [l h]. unfold zmeets in M. cbn in M.
      set (l' := Z.max l x). set (h' := Z.min h y).
      assert (Hl' : x <= l' /\ l' < h' /\ h' <= y) by (unfold l', h'; lia).
      assert (Ecl : zclamp (l, h) x y = h' - l') by (unfold zclamp, l', h'; cbn; lia).
      destruct (zsplit r l h x y Hap ltac:(lia) ltac:(lia) ltac:(lia)) as [Ss Sc].
      fold l' h' in Ss, Sc.
      pose proof (zsum_in_nonneg r x l') as S1. pose proof (zsum_in_nonneg r h' y) as S2.
      pose proof (zcount_nonneg r x l') as C1. pose proof (zcount_nonneg r h' y) as C2.
      destruct (Z_lt_le_dec (l' - x) (zsum_in r x l' + (zcount r x l' + 1) * K)) as [LT|GE].
      * (* [comment removed for export] *)
        assert (HR : zsum_in r h' y + (zcount r h' y + 1) * K <= y - h') by nia.
        (first [ pose proof ((IH h' y K HK Hd HR)) as dR_2; dex1 dR_2 as g; dand3 dR_2 as G1 G2 G3 | pose proof ((IH h' y K HK Hd HR)) as dR_2; dand4 dR_2 as g G1 G2 G3 | destruct (IH h' y K HK Hd HR) as (g & G1 & G2 & G3) ]).
        exists g. split; [lia|]. split; [lia|].
        intros z [<-|Hz]; [|apply G3; exact Hz].
        unfold zavoids. cbn. intros _. left. unfold h' in G1.
        (* [comment removed for export] *)
        nia.
      * (first [ pose proof ((IH x l' K HK Hd GE)) as dR_3; dex1 dR_3 as g; dand3 dR_3 as G1 G2 G3 | pose proof ((IH x l' K HK Hd GE)) as dR_3; dand4 dR_3 as g G1 G2 G3 | destruct (IH x l' K HK Hd GE) as (g & G1 & G2 & G3) ]).
        exists g. split; [lia|]. split; [lia|].
        intros z [<-|Hz]; [|apply G3; exact Hz].
        unfold zavoids. cbn. intros _. right. unfold l' in G2. nia.
    + (* [comment removed for export] *)
      rewrite (zclamp_notmeets _ _ _ M) in Hlen.
      (first [ pose proof ((IH x y K HK Hd ltac:(lia))) as dR_4; dex1 dR_4 as g; dand3 dR_4 as G1 G2 G3 | pose proof ((IH x y K HK Hd ltac:(lia))) as dR_4; dand4 dR_4 as g G1 G2 G3 | destruct (IH x y K HK Hd ltac:(lia)) as (g & G1 & G2 & G3) ]).
      exists g. split; [lia|]. split; [lia|].
      intros z' [<-|Hz]; [|apply G3; exact Hz].
      destruct z as [l h]. unfold zavoids, zmeets in *. cbn in *. intros Hlh. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz.
Qed.

Lemma page_round_up_Z_lt : forall z, page_round_up_Z z < z + page_size.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Section Placement.
  Variables (h : VmMaps) (zs : list zone) (L U nZ : Z).
  Let maps := vm_reserved h ++ vm_maps h.

  Hypothesis HnZ : 0 < nZ.
  Hypothesis HnAl : nZ mod page_size = 0.
  Hypothesis HL : 0 <= L.
  Hypothesis HU : U <= 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis Hdisj : zdisj zs.
  (* [comment removed for export] *)
  Hypothesis Hcover : forall b s, In (b, s) maps ->
    bv_unsigned b < U -> L < bv_unsigned b + bv_unsigned s ->
    exists z, In z zs /\ fst z < snd z /\ fst z <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= snd z.

  (* [comment removed for export] *)
  Definition ztotal : Z := zsum_in zs L U.
  Definition znum : Z := zcount zs L U.

  (* [comment removed for export] *)
  #[using="Hcover HU HL HnAl HnZ"] Lemma free_window_of_gap : forall g,
    L <= g -> g + (nZ + page_size) <= U ->
    (forall z, In z zs -> zavoids g (nZ + page_size) z) ->
    let g' := page_round_up_Z g in
    g' mod page_size = 0 /\ g <= g' /\ g' + nZ < U
    /\ region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ) = true.
  Proof.
    intros g HLg Hg Hav g'.
    pose proof (page_round_up_Z_ge g) as G1. pose proof (page_round_up_Z_lt g) as G2.
    unfold page_size in *. subst g'.
    split; [apply page_round_up_Z_aligned|]. split; [lia|]. split; [lia|].
    apply region_free_intro. intros b s Hin.
    pose proof (bv_unsigned_in_range 64 b) as Rb. pose proof (bv_unsigned_in_range 64 s) as Rs. unfold bv_modulus in Rb, Rs.
    unfold iv_overlap. rewrite !u64_lit by lia.
    destruct (Z.ltb_spec (page_round_up_Z g) (bv_unsigned b + bv_unsigned s)) as [O1|O1]; [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned b) (page_round_up_Z g + nZ)) as [O2|O2]; [|reflexivity].
    exfalso.
    (first [ pose proof ((Hcover b s Hin ltac:(lia) ltac:(lia))) as dR_5; dex1 dR_5 as z; dand4 dR_5 as Hz NE Zlo Zhi | pose proof ((Hcover b s Hin ltac:(lia) ltac:(lia))) as dR_5; dand5 dR_5 as z Hz NE Zlo Zhi | destruct (Hcover b s Hin ltac:(lia) ltac:(lia)) as (z & Hz & NE & Zlo & Zhi) ]).
    destruct (Hav z Hz NE) as [A|A]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hcover Hdisj HU HL HnAl HnZ"] Theorem grant_exists :
    L + ztotal + (znum + 1) * (nZ + page_size) <= U ->
    exists g, g mod page_size = 0 /\ L <= g /\ g + nZ <= U
              /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros Hslack.
    pose proof (zsum_in_nonneg zs L U) as T0. pose proof (zcount_nonneg zs L U) as C0. fold ztotal in T0. fold znum in C0.
    (first [ pose proof ((zone_gap zs L U (nZ + page_size) ltac:(unfold page_size; lia) Hdisj)) as dR_6; dex1 dR_6 as g; dand3 dR_6 as G1 G2 G3 | pose proof ((zone_gap zs L U (nZ + page_size) ltac:(unfold page_size; lia) Hdisj)) as dR_6; dand4 dR_6 as g G1 G2 G3 | destruct (zone_gap zs L U (nZ + page_size) ltac:(unfold page_size; lia) Hdisj) as (g & G1 & G2 & G3) ]).
    { unfold ztotal, znum in Hslack. lia. }
    (first [ pose proof ((free_window_of_gap g G1 G2 G3)) as dR_7; dand4 dR_7 as A1 A2 A3 FREE | destruct (free_window_of_gap g G1 G2 G3) as (A1 & A2 & A3 & FREE) ]).
    cbv zeta in A1, A2, A3, FREE.
    exists (page_round_up_Z g). split; [exact A1|]. split; [lia|]. split; [lia| exact FREE].
  Qed.

  (* [comment removed for export] *)
  #[using="Hcover Hdisj HU HL HnAl HnZ"] Corollary grant_exists_TC : forall T C : Z,
    ztotal <= T -> znum <= C ->
    L + T + (C + 1) * (nZ + page_size) <= U ->
    exists g, g mod page_size = 0 /\ L <= g /\ g + nZ <= U
              /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros T C HT HC Hslack.
    pose proof (zcount_nonneg zs L U) as C0. fold znum in C0.
    assert (M : (znum + 1) * (nZ + page_size) <= (C + 1) * (nZ + page_size)) by (apply Z.mul_le_mono_nonneg_r; unfold page_size; lia).
    apply grant_exists. lia.
  Qed.
End Placement.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.

(* [comment removed for export] *)
Corollary asan_grant_exists : forall (h : VmMaps) (zs : list zone) (nZ T C : Z),
  0 < nZ -> nZ mod page_size = 0 -> zdisj zs ->
  (forall b s, In (b, s) (vm_reserved h ++ vm_maps h) ->
     bv_unsigned b < alloc_top h -> kHighMemBeg < bv_unsigned b + bv_unsigned s ->
     exists z, In z zs /\ fst z < snd z /\ fst z <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= snd z) ->
  ztotal zs kHighMemBeg (alloc_top h) <= T -> znum zs kHighMemBeg (alloc_top h) <= C ->
  kHighMemBeg + T + (C + 1) * (nZ + page_size) <= alloc_top h ->
  exists g, g mod page_size = 0 /\ 0 < g /\ kHighMemBeg <= g /\ g + nZ <= alloc_top h
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros h zs nZ T C HnZ HnAl Hd Hcov HT HC Hroom.
  pose proof (alloc_top_lt h) as Htop. unfold two_pow_64 in Htop.
  (first [ pose proof ((grant_exists_TC h zs kHighMemBeg (alloc_top h) nZ HnZ HnAl ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hd Hcov T C HT HC Hroom)) as dR_8; dex1 dR_8 as g; dand4 dR_8 as G1 G2 G3 G4 | pose proof ((grant_exists_TC h zs kHighMemBeg (alloc_top h) nZ HnZ HnAl ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hd Hcov T C HT HC Hroom)) as dR_8; dand5 dR_8 as g G1 G2 G3 G4 | destruct (grant_exists_TC h zs kHighMemBeg (alloc_top h) nZ HnZ HnAl ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hd Hcov T C HT HC Hroom)
    as (g & G1 & G2 & G3 & G4) ]).
  exists g. unfold kHighMemBeg in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition nm3_sz (l : list (Z * Z)) (q : Z) : Z := zsum snd (filter (fun t => fst t =? q) l).

Definition nm3_has (l : list (Z * Z)) (c q : Z) : bool := existsb (fun t => (fst t =? q) && (band (snd t) =? c)) l.

Lemma nm3_sz_b L A q : nc_sz L A q = nm3_sz (blocks L A) q.
Proof. reflexivity. Qed.

Lemma nm3_has_b L A c q : nc_has L A c q = nm3_has (blocks L A) c q.
Proof. reflexivity. Qed.

Lemma nm3_perm {X : Type} (f : X -> Z) l l' : Permutation l l' -> zsum f l = zsum f l'.
Proof.
  intros H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - rewrite !zsum_cons, IH. reflexivity.
  - rewrite !zsum_cons. lia.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma nm3_ext {X : Type} (f g : X -> Z) l : (forall x, In x l -> f x = g x) -> zsum f l = zsum g l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. rewrite !zsum_cons, (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma nm3_cnt V L A c : nc_cnt V L A c = zsum (fun q => if nc_has L A c q then 1 else 0) (rv_nc V).
Proof. unfold nc_cnt, zlen. exact (xf_len (nc_has L A c) (rv_nc V)). Qed.

Lemma nm3_sz_app l1 l2 q : nm3_sz (l1 ++ l2) q = nm3_sz l1 q + nm3_sz l2 q.
Proof. unfold nm3_sz. rewrite filter_app. apply zsum_app. Qed.

Lemma nm3_sz_cons a n l q : nm3_sz ((a, n) :: l) q = (if a =? q then n else 0) + nm3_sz l q.
Proof. unfold nm3_sz. cbn [filter fst]. destruct (a =? q); [rewrite zsum_cons; reflexivity|cbv iota; lia]. Qed.

Lemma nm3_sz_none l q : ~ In q (map fst l) -> nm3_sz l q = 0.
Proof.
  induction l as [|[a n] l IH]; intros H; [reflexivity|]. rewrite nm3_sz_cons. cbn [map fst] in H.
  destruct (Z.eqb_spec a q) as [E|E]; [exfalso; apply H; left; exact E|]. cbv iota. rewrite IH; [lia|].
  intros X. apply H. right. exact X.
Qed.

Lemma nm3_has_app l1 l2 c q : nm3_has (l1 ++ l2) c q = nm3_has l1 c q || nm3_has l2 c q.
Proof. unfold nm3_has. apply existsb_app. Qed.

Lemma nm3_has_cons a n l c q : nm3_has ((a, n) :: l) c q = ((a =? q) && (band n =? c)) || nm3_has l c q.
Proof. reflexivity. Qed.

Lemma nm3_has_none l c q : ~ In q (map fst l) -> nm3_has l c q = false.
Proof.
  induction l as [|[a n] l IH]; intros H; [reflexivity|]. rewrite nm3_has_cons. cbn [map fst] in H.
  destruct (Z.eqb_spec a q) as [E|E]; [exfalso; apply H; left; exact E|]. cbn [andb orb]. apply IH.
  intros X. apply H. right. exact X.
Qed.

Lemma nm3_sz_mid l1 l2 a n q : nm3_sz (l1 ++ (a, n) :: l2) q = nm3_sz (l1 ++ l2) q + (if a =? q then n else 0).
Proof. rewrite !nm3_sz_app, nm3_sz_cons. lia. Qed.

Lemma nm3_has_mid l1 l2 a n c q :
  nm3_has (l1 ++ (a, n) :: l2) c q = nm3_has (l1 ++ l2) c q || ((a =? q) && (band n =? c)).
Proof.
  rewrite !nm3_has_app, nm3_has_cons.
  destruct (nm3_has l1 c q), ((a =? q) && (band n =? c)), (nm3_has l2 c q); reflexivity.
Qed.

Lemma nm3_mid_out (l1 l2 : list (Z * Z)) (a n : Z) :
  List.NoDup (map fst (l1 ++ (a, n) :: l2)) -> ~ In a (map fst (l1 ++ l2)).
Proof.
  intros H. rewrite map_app in H. cbn [map fst] in H. apply List.NoDup_remove_2 in H. rewrite map_app. exact H.
Qed.

Lemma nm3_pt_ne l1 l2 a n q : a <> q ->
  nm3_sz (l1 ++ (a, n) :: l2) q = nm3_sz (l1 ++ l2) q /\
  forall c, nm3_has (l1 ++ (a, n) :: l2) c q = nm3_has (l1 ++ l2) c q.
Proof.
  intros Hq. apply Z.eqb_neq in Hq. split.
  - rewrite nm3_sz_mid, Hq. cbv iota. lia.
  - intros c. rewrite nm3_has_mid, Hq. cbn [andb]. apply orb_false_r.
Qed.

Lemma nm3_pt_at (l1 l2 : list (Z * Z)) (a n : Z) : List.NoDup (map fst (l1 ++ (a, n) :: l2)) ->
  nm3_sz (l1 ++ (a, n) :: l2) a = n /\ nm3_sz (l1 ++ l2) a = 0 /\
  (forall c, (if nm3_has (l1 ++ (a, n) :: l2) c a then 1 else 0) = one_if c (band n)) /\
  (forall c, nm3_has (l1 ++ l2) c a = false).
Proof.
  intros ND. pose proof (nm3_mid_out _ _ _ _ ND) as NI. pose proof (nm3_sz_none _ _ NI) as S0.
  split; [rewrite nm3_sz_mid, S0, Z.eqb_refl; cbv iota; lia|]. split; [exact S0|]. split.
  - intros c. rewrite nm3_has_mid, (nm3_has_none _ c _ NI), Z.eqb_refl. cbn [andb orb]. unfold one_if.
    rewrite (Z.eqb_sym (band n) c). reflexivity.
  - intros c. exact (nm3_has_none _ c _ NI).
Qed.

Lemma nm3_gone L A D : (forall g, In g D -> ~ In g (map fst (blocks L A))) ->
  zsum (nc_sz L A) D = 0 /\ forall c, zsum (fun q => if nc_has L A c q then 1 else 0) D = 0.
Proof.
  induction D as [|g D IH]; intros H; [split; [reflexivity|intros c; reflexivity]|].
  assert (H' : forall x, In x D -> ~ In x (map fst (blocks L A))) by (intros x Hx; apply H; right; exact Hx).
  destruct (IH H') as (I1 & I2).
  pose proof (H g (or_introl eq_refl)) as Hg. split.
  - rewrite zsum_cons, I1, nm3_sz_b, (nm3_sz_none _ _ Hg). reflexivity.
  - intros c. rewrite zsum_cons, (I2 c). cbv beta. rewrite nm3_has_b, (nm3_has_none _ c _ Hg). reflexivity.
Qed.

Lemma ncm3_core V L A V' L' A' R D N :
  Permutation (rv_nc V) (D ++ R) -> Permutation (rv_nc V') (N ++ R) ->
  (forall q, In q R -> nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q) ->
  ncs V' L' A' + zsum (nc_sz L A) D = ncs V L A + zsum (nc_sz L' A') N /\
  forall c, nc_cnt V' L' A' c + zsum (fun q => if nc_has L A c q then 1 else 0) D =
    nc_cnt V L A c + zsum (fun q => if nc_has L' A' c q then 1 else 0) N.
Proof.
  intros HV HV' HR. split.
  - unfold ncs. rewrite (nm3_perm _ _ _ HV), (nm3_perm _ _ _ HV'), !zsum_app.
    rewrite (nm3_ext (nc_sz L' A') (nc_sz L A) R) by (intros q Hq; exact (proj1 (HR q Hq))). lia.
  - intros c. rewrite !nm3_cnt, (nm3_perm _ _ _ HV), (nm3_perm _ _ _ HV'), !zsum_app.
    rewrite (nm3_ext (fun q => if nc_has L' A' c q then 1 else 0) (fun q => if nc_has L A c q then 1 else 0) R)
      by (intros q Hq; cbv beta; rewrite (proj2 (HR q Hq) c); reflexivity). lia.
Qed.

Lemma nm3_malloc_pt L A L' A' b1 b2 res n q :
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 -> res <> q ->
  nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q.
Proof.
  intros HB' HB Hq. destruct (nm3_pt_ne b1 b2 res n q Hq) as (P1 & P2). split.
  - rewrite !nm3_sz_b, HB, HB'. exact P1.
  - intros c. rewrite !nm3_has_b, HB, HB'. exact (P2 c).
Qed.

Lemma nm3_free_pt L A L' A' b1 b2 a n q :
  blocks L A = b1 ++ (a, n) :: b2 -> blocks L' A' = b1 ++ b2 -> a <> q ->
  nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q.
Proof.
  intros HB HB' Hq. destruct (nm3_pt_ne b1 b2 a n q Hq) as (P1 & P2). split.
  - rewrite !nm3_sz_b, HB, HB'. symmetry. exact P1.
  - intros c. rewrite !nm3_has_b, HB, HB'. symmetry. exact (P2 c).
Qed.

Lemma nm3_realloc_pt L A L' A' b1 b2 c1 c2 a k res n q :
  blocks L A = b1 ++ (a, k) :: b2 -> blocks L' A' = c1 ++ (res, n) :: c2 -> c1 ++ c2 = b1 ++ b2 ->
  a <> q -> res <> q ->
  nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q.
Proof.
  intros HB HB' HC Ha Hr. destruct (nm3_pt_ne b1 b2 a k q Ha) as (P1 & P2).
  destruct (nm3_pt_ne c1 c2 res n q Hr) as (Q1 & Q2). split.
  - rewrite !nm3_sz_b, HB, HB', Q1, HC. symmetry. exact P1.
  - intros c. rewrite !nm3_has_b, HB, HB', (Q2 c), HC. symmetry. exact (P2 c).
Qed.

Theorem ncm3_malloc_g V L A V' L' A' b1 b2 res n R gone :
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 -> List.NoDup (map fst (blocks L' A')) ->
  Permutation (rv_nc V) (gone ++ R) -> Permutation (rv_nc V') (res :: R) -> ~ In res R ->
  (forall g, In g gone -> ~ In g (map fst (blocks L A))) ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c + one_if c (band n)) /\ ncs V' L' A' = ncs V L A + n.
Proof.
  intros HB' HB ND HV HV' HR HG. rewrite HB' in ND. destruct (nm3_pt_at _ _ _ _ ND) as (A1 & _ & A3 & _).
  destruct (nm3_gone L A gone HG) as (G1 & G2).
  assert (PT : forall q, In q R -> nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q).
  { intros q Hq. apply (nm3_malloc_pt L A L' A' b1 b2 res n q HB' HB). intros E. subst q. exact (HR Hq). }
  destruct (ncm3_core V L A V' L' A' R gone [res] HV HV' PT) as (C1 & C2).
  split.
  - intros c. specialize (C2 c). rewrite (G2 c), zsum_cons, zsum_nil in C2. cbv beta in C2.
    rewrite nm3_has_b, HB', (A3 c) in C2. lia.
  - rewrite G1, zsum_cons, zsum_nil, nm3_sz_b, HB', A1 in C1. lia.
Qed.

Theorem ncm3_free_g V L A V' L' A' b1 b2 a n R gone :
  blocks L A = b1 ++ (a, n) :: b2 -> blocks L' A' = b1 ++ b2 -> List.NoDup (map fst (blocks L A)) ->
  Permutation (rv_nc V) (a :: gone ++ R) -> Permutation (rv_nc V') R -> ~ In a R ->
  (forall g, In g gone -> ~ In g (map fst (blocks L A))) ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c - one_if c (band n)) /\ ncs V' L' A' = ncs V L A - n.
Proof.
  intros HB HB' ND HV HV' HR HG. pose proof ND as ND0. rewrite HB in ND0.
  destruct (nm3_pt_at _ _ _ _ ND0) as (A1 & _ & A3 & _).
  destruct (nm3_gone L A gone HG) as (G1 & G2).
  assert (PT : forall q, In q R -> nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q).
  { intros q Hq. apply (nm3_free_pt L A L' A' b1 b2 a n q HB HB'). intros E. subst q. exact (HR Hq). }
  destruct (ncm3_core V L A V' L' A' R (a :: gone) [] HV HV' PT) as (C1 & C2).
  split.
  - intros c. specialize (C2 c). rewrite zsum_cons, (G2 c), zsum_nil in C2. cbv beta in C2.
    rewrite nm3_has_b, HB, (A3 c) in C2. lia.
  - rewrite zsum_cons, G1, zsum_nil, nm3_sz_b, HB, A1 in C1. lia.
Qed.

Theorem ncm3_realloc_g V L A V' L' A' b1 b2 c1 c2 a k res n R gone :
  blocks L A = b1 ++ (a, k) :: b2 -> blocks L' A' = c1 ++ (res, n) :: c2 -> c1 ++ c2 = b1 ++ b2 ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  Permutation (rv_nc V) (a :: gone ++ R) -> Permutation (rv_nc V') (res :: R) -> ~ In a R -> ~ In res R ->
  (forall g, In g gone -> ~ In g (map fst (blocks L A))) ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c + (one_if c (band n) - one_if c (band k))) /\
  ncs V' L' A' = ncs V L A + (n - k).
Proof.
  intros HB HB' HC ND ND' HV HV' HRa HRr HG. pose proof ND as ND0. rewrite HB in ND0.
  pose proof ND' as ND1. rewrite HB' in ND1.
  destruct (nm3_pt_at _ _ _ _ ND0) as (A1 & _ & A3 & _).
  destruct (nm3_pt_at _ _ _ _ ND1) as (B1 & _ & B3 & _).
  destruct (nm3_gone L A gone HG) as (G1 & G2).
  assert (PT : forall q, In q R -> nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q).
  { intros q Hq. apply (nm3_realloc_pt L A L' A' b1 b2 c1 c2 a k res n q HB HB' HC).
    - intros E. subst q. exact (HRa Hq).
    - intros E. subst q. exact (HRr Hq). }
  destruct (ncm3_core V L A V' L' A' R (a :: gone) [res] HV HV' PT) as (C1 & C2).
  split.
  - intros c. specialize (C2 c). rewrite !zsum_cons, (G2 c), !zsum_nil in C2. cbv beta in C2.
    rewrite !nm3_has_b, HB, HB', (A3 c), (B3 c) in C2. lia.
  - rewrite !zsum_cons, G1, !zsum_nil, !nm3_sz_b, HB, HB', A1, B1 in C1. lia.
Qed.

Lemma nm3_not_in (x : Z) l : List.NoDup (x :: l) -> ~ In x l.
Proof. intros H. apply List.NoDup_cons_iff in H. exact (proj1 H). Qed.

Theorem ncm3_malloc V L A V' L' A' b1 b2 res n :
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 -> List.NoDup (map fst (blocks L' A')) ->
  List.NoDup (rv_nc V') -> Permutation (rv_nc V') (res :: rv_nc V) ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c + one_if c (band n)) /\ ncs V' L' A' = ncs V L A + n.
Proof.
  intros HB' HB ND NV HV'.
  apply (ncm3_malloc_g V L A V' L' A' b1 b2 res n (rv_nc V) [] HB' HB ND (Permutation_refl (rv_nc V)) HV');
    [|intros g []].
  exact (nm3_not_in _ _ (Permutation_NoDup HV' NV)).
Qed.

Theorem ncm3_free V L A V' L' A' b1 b2 a n :
  blocks L A = b1 ++ (a, n) :: b2 -> blocks L' A' = b1 ++ b2 -> List.NoDup (map fst (blocks L A)) ->
  List.NoDup (rv_nc V) -> Permutation (rv_nc V) (a :: rv_nc V') ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c - one_if c (band n)) /\ ncs V' L' A' = ncs V L A - n.
Proof.
  intros HB HB' ND NV HV.
  apply (ncm3_free_g V L A V' L' A' b1 b2 a n (rv_nc V') [] HB HB' ND HV (Permutation_refl (rv_nc V')));
    [|intros g []].
  exact (nm3_not_in _ _ (Permutation_NoDup HV NV)).
Qed.

Theorem ncm3_realloc V L A V' L' A' b1 b2 c1 c2 a k res n R :
  blocks L A = b1 ++ (a, k) :: b2 -> blocks L' A' = c1 ++ (res, n) :: c2 -> c1 ++ c2 = b1 ++ b2 ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  List.NoDup (rv_nc V) -> List.NoDup (rv_nc V') ->
  Permutation (rv_nc V) (a :: R) -> Permutation (rv_nc V') (res :: R) ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c + (one_if c (band n) - one_if c (band k))) /\
  ncs V' L' A' = ncs V L A + (n - k).
Proof.
  intros HB HB' HC ND ND' NV NV' HV HV'.
  apply (ncm3_realloc_g V L A V' L' A' b1 b2 c1 c2 a k res n R [] HB HB' HC ND ND' HV HV');
    [exact (nm3_not_in _ _ (Permutation_NoDup HV NV))|exact (nm3_not_in _ _ (Permutation_NoDup HV' NV'))|].
  intros g [].
Qed.

Theorem ncm3_copy V L A V' L' A' b1 b2 res n :
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 -> 0 <= n -> Permutation (rv_nc V) (rv_nc V') ->
  (forall c, nc_cnt V L A c <= nc_cnt V' L' A' c) /\ ncs V L A <= ncs V' L' A'.
Proof.
  intros HB' HB Hn HV. split.
  - intros c. rewrite !nm3_cnt, (nm3_perm _ _ _ HV). apply zsum_le'. intros q _. cbv beta.
    rewrite !nm3_has_b, HB, HB', nm3_has_mid.
    destruct (nm3_has (b1 ++ b2) c q), ((res =? q) && (band n =? c)); cbn [orb]; lia.
  - unfold ncs. rewrite (nm3_perm _ _ _ HV). apply zsum_le'. intros q _.
    rewrite !nm3_sz_b, HB, HB', nm3_sz_mid. destruct (res =? q); cbv iota; lia.
Qed.

Theorem ncm3_copy_eq V L A V' L' A' b1 b2 res n :
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 -> ~ In res (rv_nc V) ->
  Permutation (rv_nc V) (rv_nc V') ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c) /\ ncs V' L' A' = ncs V L A.
Proof.
  intros HB' HB HR HV.
  assert (PT : forall q, In q (rv_nc V) -> nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q).
  { intros q Hq. apply (nm3_malloc_pt L A L' A' b1 b2 res n q HB' HB). intros E. subst q. exact (HR Hq). }
  destruct (ncm3_core V L A V' L' A' (rv_nc V) [] [] (Permutation_refl (rv_nc V)) (Permutation_sym HV) PT)
    as (C1 & C2).
  split.
  - intros c. specialize (C2 c). rewrite !zsum_nil in C2. lia.
  - rewrite !zsum_nil in C1. lia.
Qed.

Theorem ncm3_free_out V L A V' L' A' b1 b2 a n :
  blocks L A = b1 ++ (a, n) :: b2 -> blocks L' A' = b1 ++ b2 -> ~ In a (rv_nc V) ->
  Permutation (rv_nc V) (rv_nc V') ->
  (forall c, nc_cnt V' L' A' c = nc_cnt V L A c) /\ ncs V' L' A' = ncs V L A.
Proof.
  intros HB HB' HR HV.
  assert (PT : forall q, In q (rv_nc V) -> nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q).
  { intros q Hq. apply (nm3_free_pt L A L' A' b1 b2 a n q HB HB'). intros E. subst q. exact (HR Hq). }
  destruct (ncm3_core V L A V' L' A' (rv_nc V) [] [] (Permutation_refl (rv_nc V)) (Permutation_sym HV) PT)
    as (C1 & C2).
  split.
  - intros c. specialize (C2 c). rewrite !zsum_nil in C2. lia.
  - rewrite !zsum_nil in C1. lia.
Qed.

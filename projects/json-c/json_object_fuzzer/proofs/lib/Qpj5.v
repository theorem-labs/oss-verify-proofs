(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QKyU QPa2 QOb0 Qt4u Q6sh QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QCiC QKyU QPa2 QOb0.Mq0 Qt4u.Mq0.
Import Q6sh.
Import QQwg.
Import ListNotations. Open Scope Z_scope.
Local Open Scope amodel_scope.

Lemma round_up_shift t m a : 0 < a -> (a | m) -> m + round_up (t - m) a = round_up t a.
Proof.
intros Ha [k ->]. unfold round_up.
replace (t - k * a + a - 1) with (t + a - 1 + (- k) * a) by lia.
rewrite Z.div_add by lia. lia.
Qed.
Lemma div_add_le a b s : 0 < s -> a / s + b / s <= (a + b) / s.
Proof.
intros Hs. apply Z.div_le_lower_bound; [lia|].
pose proof (Z.mul_div_le a s ltac:(lia)). pose proof (Z.mul_div_le b s ltac:(lia)). lia.
Qed.
Lemma div_le_of_mul_le q x s : 0 < s -> s * q <= x -> q <= x / s.
Proof. intros Hs H. apply Z.div_le_lower_bound; lia. Qed.

Section Ops.
Variable L : ALay.
Variable aok : evA -> ansA -> Prop.

Hypothesis aok_fixed : forall a l, aok (EvMapFixed a l) AErr -> False.

Local Ltac kconst := unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset, kPage in *.

Lemma ensure_fa_spec s c nf :
cwf c (cls s c) -> 0 <= nf -> 4 * nf <= kFreeArraySize ->
tall aok (rok (fun r => let '(ok, s') := r in
only_cls c s s' /\
c_mapped_user (cls s' c) = c_mapped_user (cls s c) /\ c_alloc_user (cls s' c) = c_alloc_user (cls s c) /\
c_num_freed (cls s' c) = c_num_freed (cls s c) /\ c_count (cls s' c) = c_count (cls s c) /\
c_mapped_fa (cls s c) <= c_mapped_fa (cls s' c) <= kFreeArraySize /\ (kFreeArrayMapSize | c_mapped_fa (cls s' c)) /\
(ok = true -> 4 * nf <= c_mapped_fa (cls s' c))))
(ensure_fa L s c nf).
Proof.
intros W Hnf Hcap. unfold ensure_fa.
destruct (Z.leb_spec (4 * nf) (c_mapped_fa (cls s c))) as [Hle|Hgt].
- apply tall_rok_ret. split; [apply only_cls_refl|]. pose proof (cw_fa _ _ W). pose proof (cw_fa_al _ _ W). repeat split; auto; lia.
- assert (Hru : round_up (4 * nf) kFreeArrayMapSize <= kFreeArraySize).
{ apply round_up_le_mul; kconst; [lia| exists 2048; reflexivity| lia]. }
destruct (Z.ltb_spec kFreeArraySize (round_up (4 * nf) kFreeArrayMapSize)); [lia|].
apply tall_vis. intros a _.
pose proof (cw_fa _ _ W) as Wfa. pose proof (cw_fa_al _ _ W) as Wal.
pose proof (round_up_ge (4 * nf) kFreeArrayMapSize ltac:(kconst; lia)) as Hge.
pose proof (round_up_mul (4 * nf) kFreeArrayMapSize ltac:(kconst; lia)) as Hmul.
destruct a as [|b]; cbn [fixed_ok]; apply tall_rok_ret.
+ split; [apply only_cls_refl|]. repeat split; auto; try lia; try discriminate.
+ split; [apply only_cls_set_cls|]. rewrite cls_set_cls_eq; cbn; repeat split; auto; try lia; try discriminate.
Qed.

Definition populate_post (s : AState) (c req : Z) (r : bool * AState) : Prop :=
let '(ok, s') := r in
let x := cls s c in let x' := cls s' c in
only_cls c s s' /\ cwf c x' /\
c_count x' = c_count x /\ c_mapped_user x <= c_mapped_user x' /\
class_size c * c_num_freed x' <= c_alloc_user x' /\
c_alloc_user x' - class_size c * c_num_freed x' = c_alloc_user x - class_size c * c_num_freed x /\
c_num_freed x <= c_num_freed x' /\
(ok = true -> c_num_freed x + req <= c_num_freed x').

Lemma populate_spec s c req :
1 <= c <= 31 -> cwf c (cls s c) -> 1 <= req ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
c_alloc_user (cls s c) + req * class_size c <= kFreeArrayOffset ->
tall aok (rok (populate_post s c req)) (populate L s c req).
Proof.
intros Hc W Hreq Hnf Hroom. unfold populate.
pose proof (class_facts c Hc) as (Hsz & _ & _).
pose proof (cw_au _ _ W) as Wau. pose proof (cw_mu _ _ W) as Wmu. pose proof (cw_nf _ _ W) as Wnf.
pose proof (cw_mu_al _ _ W) as Wmal. pose proof (cw_fa _ _ W) as Wfa. pose proof (cw_fa_al _ _ W) as Wfal. pose proof (cw_cnt _ _ W) as Wcnt.
set (x := cls s c) in *. set (size := class_size c) in *.
set (total := c_alloc_user x + req * size).

set (P1 := fun (r : bool * AState) => let '(ok, s1) := r in
only_cls c s s1 /\ cwf c (cls s1 c) /\
c_alloc_user (cls s1 c) = c_alloc_user x /\ c_num_freed (cls s1 c) = c_num_freed x /\ c_count (cls s1 c) = c_count x /\
c_mapped_user x <= c_mapped_user (cls s1 c) /\ (ok = true -> total <= c_mapped_user (cls s1 c))).
eapply (tall_bind_rok aok P1).
{ destruct (Z.ltb_spec (c_mapped_user x) total) as [Hlt|Hge].
- set (msz := round_up (total - c_mapped_user x) kUserMapSize).
assert (Hshift : c_mapped_user x + msz = round_up total kUserMapSize).
{ subst msz. apply round_up_shift; [kconst; lia| exact Wmal]. }
assert (Hru : round_up total kUserMapSize <= kFreeArrayOffset).
{ apply round_up_le_mul; [kconst; lia| exists 14336; reflexivity| subst total size; lia]. }
assert (Hmsz : (kUserMapSize | msz)) by (subst msz; apply round_up_mul; kconst; lia).
pose proof (round_up_ge total kUserMapSize ltac:(kconst; lia)) as Hge'.
destruct (Z.ltb_spec kFreeArrayOffset (c_mapped_user x + msz)); [lia|].
apply tall_vis. intros a _.
destruct a as [|b]; cbn [fixed_ok]; apply tall_rok_ret; subst P1; cbn beta iota.
+ split; [apply only_cls_refl|]. subst x. split; [exact W|]. repeat split; try lia. all: intros; discriminate.
+ split; [apply only_cls_set_cls|]. rewrite cls_set_cls_eq. cbn. subst x.
split; [constructor; cbn; auto; try lia|]; [|repeat split; try lia].
destruct Wmal as [k Hk]. destruct Hmsz as [k' Hk']. exists (k + k'). lia.
- apply tall_rok_ret. subst P1. cbn beta iota. split; [apply only_cls_refl|]. subst x. repeat split; auto; try lia. }

intros [ok s1] H1. subst P1. cbn beta iota in H1. destruct H1 as (Ho1 & W1 & Eau & Enf & Ecnt & Hmu1 & Hok1).
destruct ok; cbn [negb].
2: { apply tall_rok_ret. unfold populate_post. subst x. split; [exact Ho1|]. split; [exact W1|].
rewrite Eau, Enf, Ecnt. repeat split; try lia. all: intros; discriminate. }
specialize (Hok1 eq_refl).
set (x1 := cls s1 c) in *.
set (newc := (c_mapped_user x1 - c_alloc_user x1) / size).
pose proof (cw_au _ _ W1) as W1au. pose proof (cw_mu _ _ W1) as W1mu.
assert (Hnewc : 0 <= newc) by (subst newc; apply Z.div_pos; lia).
assert (Hnewc2 : newc * size <= c_mapped_user x1 - c_alloc_user x1).
{ subst newc. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (Hreq2 : req <= newc).
{ subst newc. apply div_le_of_mul_le; [lia|]. subst total. rewrite Eau. lia. }
assert (Htf : 4 * (c_num_freed x1 + newc) <= kFreeArraySize).
{ assert (c_num_freed x1 <= c_alloc_user x1 / size) by (apply div_le_of_mul_le; [lia|]; rewrite Enf, Eau; subst x; lia).
pose proof (div_add_le (c_alloc_user x1) (c_mapped_user x1 - c_alloc_user x1) size ltac:(lia)) as Hd.
replace (c_alloc_user x1 + (c_mapped_user x1 - c_alloc_user x1)) with (c_mapped_user x1) in Hd by lia.
assert (c_mapped_user x1 / size <= kFreeArrayOffset / 32).
{ etransitivity; [apply Z.div_le_mono; [lia| exact W1mu]|]. apply Z.div_le_compat_l; kconst; lia. }
subst newc. kconst. change (3758096384 / 32) with 117440512 in *. lia. }
eapply tall_bind_rok.
{ apply (ensure_fa_spec s1 c); [exact W1| pose proof (cw_nf _ _ W1); lia| exact Htf]. }
intros [ok2 s2] (Ho2 & Emu2 & Eau2 & Enf2 & Ecnt2 & Hfa2 & Hfal2 & Hok2). cbn beta iota.
pose proof (cw_fa _ _ W1) as W1fa. pose proof (cw_cnt _ _ W1) as W1cnt. pose proof (cw_nf _ _ W1) as W1nf.
destruct ok2; cbn [negb].
- apply tall_rok_ret. specialize (Hok2 eq_refl). unfold populate_post.
split; [apply only_cls_set_cls'; eapply only_cls_trans; [exact Ho1| exact Ho2]|].
rewrite cls_set_cls_eq. cbn. subst x x1.
pose proof (cw_mu_al _ _ W1) as W1mal. rewrite <- Emu2 in W1mal.
split.
+ constructor; cbn; rewrite ?Ecnt2, ?Enf2, ?Eau2, ?Ecnt, ?Enf, ?Eau in *; try lia; auto.
+ rewrite ?Ecnt2, ?Emu2, ?Enf2, ?Eau2, ?Ecnt, ?Enf, ?Eau in *. repeat split; try lia.
- apply tall_rok_ret. unfold populate_post. split; [eapply only_cls_trans; [exact Ho1| exact Ho2]|].
subst x x1.
pose proof (cw_mu_al _ _ W1) as W1mal. rewrite <- Emu2 in W1mal.
split.
+ constructor; cbn; rewrite ?Ecnt2, ?Enf2, ?Eau2, ?Ecnt, ?Enf, ?Eau in *; try lia; auto.
+ rewrite ?Ecnt2, ?Emu2, ?Enf2, ?Eau2, ?Ecnt, ?Enf, ?Eau in *. repeat split; try lia. all: intros; discriminate.
Qed.

Definition gfa_post (s : AState) (c k : Z) (r : bool * AState) : Prop :=
let '(ok, s') := r in
let x := cls s c in let x' := cls s' c in
only_cls c s s' /\ cwf c x' /\
c_count x' = c_count x /\ c_mapped_user x <= c_mapped_user x' /\
class_size c * c_num_freed x' <= c_alloc_user x' /\
c_alloc_user x' - class_size c * c_num_freed x' =
c_alloc_user x - class_size c * c_num_freed x + (if ok then class_size c * k else 0).

Lemma get_from_allocator_spec s c k :
1 <= c <= 31 -> cwf c (cls s c) -> 1 <= k ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
(c_num_freed (cls s c) < k -> c_alloc_user (cls s c) + k * class_size c <= kFreeArrayOffset) ->
tall aok (rok (gfa_post s c k)) (get_from_allocator L s c k).
Proof.
intros Hc W Hk Hnf Hroom. unfold get_from_allocator.
pose proof (class_facts c Hc) as (Hsz & _ & _). pose proof (cw_nf _ _ W) as Wnf.
eapply (tall_bind_rok aok (fun r => populate_post s c (k - c_num_freed (cls s c)) r /\
(fst r = true -> k <= c_num_freed (cls (snd r) c)))).
{ destruct (Z.ltb_spec (c_num_freed (cls s c)) k) as [Hlt|Hge].
- specialize (Hroom Hlt). eapply tall_mono; [apply populate_spec; auto; try lia; nia|].
intros [[ok s1]| |w]; cbn; auto. intros H. split; [exact H|]. intros ->.
destruct H as (_ & _ & _ & _ & _ & _ & _ & H8). specialize (H8 eq_refl). lia.
- apply tall_rok_ret. split; [|cbn; intros _; lia]. unfold populate_post.
split; [apply only_cls_refl|]. split; [exact W|]. repeat split; try lia. }
intros [ok s1] [H1 Hk1]. cbn [fst snd] in Hk1. unfold populate_post in H1.
destruct H1 as (Ho1 & W1 & Ecnt & Hmu & Hnf1 & Hacc & Hnfle & Hok).
destruct ok; cbn [negb].
2: { apply tall_rok_ret. unfold gfa_post. split; [exact Ho1|]. split; [exact W1|]. repeat split; try lia. }
specialize (Hk1 eq_refl).
destruct (Z.ltb_spec (c_num_freed (cls s1 c)) k); [lia|].
apply tall_rok_ret. unfold gfa_post. split; [apply only_cls_set_cls'; exact Ho1|].
rewrite cls_set_cls_eq. cbn.
pose proof (cw_fa _ _ W1). pose proof (cw_cnt _ _ W1). pose proof (cw_au _ _ W1). pose proof (cw_mu _ _ W1).
split; [constructor; cbn; try lia; [apply (cw_mu_al _ _ W1)| apply (cw_fa_al _ _ W1)]|].
repeat split; try lia.
Qed.

Definition refill_post (s : AState) (c : Z) (r : bool * AState) : Prop :=
let '(ok, s') := r in
let x := cls s c in let x' := cls s' c in
only_cls c s s' /\ cwf c x' /\ c_mapped_user x <= c_mapped_user x' /\
class_size c * c_num_freed x' <= c_alloc_user x' /\
acc c x' = acc c x /\
c_count x' = (if ok then max_count c / 2 else 0).

Lemma refill_spec s c :
1 <= c <= 31 -> cwf c (cls s c) -> c_count (cls s c) = 0 ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
(c_num_freed (cls s c) < 8 -> c_alloc_user (cls s c) + 8 * class_size c <= kFreeArrayOffset) ->
tall aok (rok (refill_post s c)) (refill L s c).
Proof.
intros Hc W Hcnt Hnf Hroom. unfold refill.
pose proof (class_facts c Hc) as (Hsz & Hmc & Hev).
eapply tall_bind_rok.
{ apply (get_from_allocator_spec (set_inited s) c (max_count c / 2)); rewrite ?cls_set_inited; auto; try lia. intros Hlt. specialize (Hroom ltac:(lia)). nia. }
intros [ok s1] H1. unfold gfa_post in H1. rewrite !cls_set_inited in H1.
destruct H1 as (Ho1 & W1 & Ecnt & Hmu & Hnf1 & Hacc).
destruct ok; cbn [negb].
- apply tall_rok_ret. unfold refill_post. split; [apply only_cls_upd_cls'; eapply only_cls_trans; [apply only_cls_set_inited| exact Ho1]|].
rewrite cls_upd_cls_eq. cbn. pose proof (cw_fa _ _ W1). pose proof (cw_au _ _ W1). pose proof (cw_mu _ _ W1). pose proof (cw_nf _ _ W1).
split; [constructor; cbn; try lia; [apply (cw_mu_al _ _ W1)| apply (cw_fa_al _ _ W1)]|].
unfold acc. cbn. repeat split; try lia.
- apply tall_rok_ret. unfold refill_post. split; [eapply only_cls_trans; [apply only_cls_set_inited| exact Ho1]|].
split; [exact W1|]. unfold acc. repeat split; try lia.
Qed.

Definition cache_alloc_post (s : AState) (c : Z) (r : bool * AState) : Prop :=
let '(ok, s') := r in
let x := cls s c in let x' := cls s' c in
only_cls c s s' /\ cwf c x' /\ c_mapped_user x <= c_mapped_user x' /\
class_size c * c_num_freed x' <= c_alloc_user x' /\
acc c x' = acc c x + (if ok then class_size c else 0).

Lemma cache_alloc_spec s c :
1 <= c <= 31 -> cwf c (cls s c) ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
(c_count (cls s c) = 0 -> c_num_freed (cls s c) < 8 -> c_alloc_user (cls s c) + 8 * class_size c <= kFreeArrayOffset) ->
tall aok (rok (cache_alloc_post s c)) (cache_alloc L s c).
Proof.
intros Hc W Hnf Hroom. unfold cache_alloc.
pose proof (class_facts c Hc) as (Hsz & Hmc & Hev).
eapply (tall_bind_rok aok (fun r => refill_post s c r \/ (fst r = true /\ snd r = s /\ 0 < c_count (cls s c)))).
{ destruct (Z.eqb_spec (c_count (cls s c)) 0) as [H0|Hn0].
- eapply tall_mono; [apply refill_spec; auto|]. intros [r| |w]; cbn; auto.
- apply tall_rok_ret. right. cbn. pose proof (cw_cnt _ _ W). repeat split; lia. }
intros [ok s1] [H1|(E1 & E2 & Hpos)]; cbn [fst snd] in *; [|subst ok s1].
- unfold refill_post in H1. destruct H1 as (Ho1 & W1 & Hmu & Hnf1 & Hacc & Hcnt).
destruct ok; cbn [negb].
+ apply tall_rok_ret. unfold cache_alloc_post. split; [apply only_cls_upd_cls'; exact Ho1|].
rewrite cls_upd_cls_eq. cbn. pose proof (cw_fa _ _ W1). pose proof (cw_au _ _ W1). pose proof (cw_mu _ _ W1). pose proof (cw_nf _ _ W1). pose proof (cw_cnt _ _ W1).
split; [constructor; cbn; try lia; [apply (cw_mu_al _ _ W1)| apply (cw_fa_al _ _ W1)]|].
unfold acc in *. cbn. repeat split; try lia.
+ apply tall_rok_ret. unfold cache_alloc_post. split; [exact Ho1|]. split; [exact W1|]. unfold acc in *. repeat split; try lia.
- cbn [negb]. apply tall_rok_ret. unfold cache_alloc_post. split; [apply only_cls_upd_cls|].
rewrite cls_upd_cls_eq. cbn. pose proof (cw_fa _ _ W). pose proof (cw_au _ _ W). pose proof (cw_mu _ _ W). pose proof (cw_nf _ _ W). pose proof (cw_cnt _ _ W).
split; [constructor; cbn; try lia; [apply (cw_mu_al _ _ W)| apply (cw_fa_al _ _ W)]|].
unfold acc. cbn. repeat split; try lia.
Qed.

Definition rta_post (s : AState) (c k : Z) (s' : AState) : Prop :=
let x := cls s c in let x' := cls s' c in
only_cls c s s' /\ cwf c x' /\
c_num_freed x' = c_num_freed x + k /\ c_count x' = c_count x /\
c_alloc_user x' = c_alloc_user x /\ c_mapped_user x' = c_mapped_user x.

Lemma return_to_allocator_spec s c k :
1 <= c <= 31 -> cwf c (cls s c) -> 0 <= k ->
class_size c * (c_num_freed (cls s c) + k) <= c_alloc_user (cls s c) ->
tall aok (rok (rta_post s c k)) (return_to_allocator L s c k).
Proof.
intros Hc W Hk Hle. unfold return_to_allocator.
pose proof (class_facts c Hc) as (Hsz & _ & _).
pose proof (cw_nf _ _ W) as Wnf. pose proof (cw_au _ _ W) as Wau. pose proof (cw_mu _ _ W) as Wmu.
assert (Htf : 4 * (c_num_freed (cls s c) + k) <= kFreeArraySize).
{ assert (c_num_freed (cls s c) + k <= c_alloc_user (cls s c) / class_size c) by (apply div_le_of_mul_le; lia).
assert (c_alloc_user (cls s c) / class_size c <= kFreeArrayOffset / 32).
{ etransitivity; [apply (Z.div_le_mono _ kFreeArrayOffset); lia|]. apply Z.div_le_compat_l; kconst; lia. }
kconst. change (3758096384 / 32) with 117440512 in *. lia. }
eapply tall_bind_rok; [apply (ensure_fa_spec s c); [exact W| lia| exact Htf]|].
intros [ok s1] (Ho1 & Emu & Eau & Enf & Ecnt & Hfa & Hfal & Hok). cbn beta iota.
destruct ok; cbn [negb]; [|apply tall_rok_spin].
specialize (Hok eq_refl). apply tall_rok_ret. unfold rta_post.
split; [apply only_cls_upd_cls'; exact Ho1|]. rewrite cls_upd_cls_eq. cbn.
pose proof (cw_cnt _ _ W).
split; [constructor; cbn; rewrite ?Emu, ?Eau, ?Ecnt; try lia; [apply (cw_mu_al _ _ W)| exact Hfal]|].
repeat split; lia.
Qed.

Definition cache_dealloc_post (s : AState) (c : Z) (s' : AState) : Prop :=
let x := cls s c in let x' := cls s' c in
only_cls c s s' /\ cwf c x' /\
acc c x' = acc c x - class_size c /\
c_alloc_user x' = c_alloc_user x /\ c_mapped_user x' = c_mapped_user x.

Lemma cache_dealloc_spec s c :
1 <= c <= 31 -> cwf c (cls s c) ->
class_size c * (c_num_freed (cls s c) + c_count (cls s c)) + class_size c <= c_alloc_user (cls s c) ->
tall aok (rok (cache_dealloc_post s c)) (cache_dealloc L s c).
Proof.
intros Hc W Hle. unfold cache_dealloc. rewrite !cls_set_inited.
pose proof (class_facts c Hc) as (Hsz & Hmc & Hev).
pose proof (cw_nf _ _ W) as Wnf. pose proof (cw_au _ _ W) as Wau. pose proof (cw_mu _ _ W) as Wmu. pose proof (cw_cnt _ _ W) as Wcnt. pose proof (cw_fa _ _ W) as Wfa.
eapply (tall_bind_rok aok (fun s1 => only_cls c s s1 /\ cwf c (cls s1 c) /\
c_alloc_user (cls s1 c) = c_alloc_user (cls s c) /\ c_mapped_user (cls s1 c) = c_mapped_user (cls s c) /\
c_count (cls s1 c) + 1 <= max_count c /\
class_size c * (c_num_freed (cls s1 c) + c_count (cls s1 c)) = class_size c * (c_num_freed (cls s c) + c_count (cls s c)))).
{ destruct (Z.eqb_spec (c_count (cls s c)) (max_count c)) as [Heq|Hne].
- eapply tall_mono.
+ apply (return_to_allocator_spec (upd_cls c (set_count (c_count (cls s c) - max_count c / 2)) (set_inited s)) c (max_count c / 2));
rewrite ?cls_upd_cls_eq, ?cls_set_inited; cbn; auto; try lia.
constructor; cbn; try lia; [apply (cw_mu_al _ _ W)| apply (cw_fa_al _ _ W)].
+ intros [s1| |w]; cbn; auto. unfold rta_post. rewrite !cls_upd_cls_eq. cbn. rewrite !cls_set_inited.
intros (Ho1 & W1 & Enf & Ecnt & Eau & Emu). split.
{ eapply only_cls_trans; [apply only_cls_set_inited|]. eapply only_cls_trans; [apply only_cls_upd_cls| exact Ho1]. }
split; [exact W1|]. repeat split; lia.
- apply tall_rok_ret. rewrite !cls_set_inited. split; [apply only_cls_set_inited|]. split; [exact W|]. repeat split; lia. }
intros s1 (Ho1 & W1 & Eau & Emu & Hcnt & Heq). apply tall_rok_ret. unfold cache_dealloc_post.
split; [apply only_cls_upd_cls'; exact Ho1|]. rewrite cls_upd_cls_eq. cbn.
pose proof (cw_nf _ _ W1). pose proof (cw_au _ _ W1). pose proof (cw_mu _ _ W1). pose proof (cw_cnt _ _ W1). pose proof (cw_fa _ _ W1).
split; [constructor; cbn; try lia; [apply (cw_mu_al _ _ W1)| apply (cw_fa_al _ _ W1)]|].
unfold acc. cbn. repeat split; try lia.
Qed.

Lemma clear_shadow_spec a sz : tall aok (rok (fun _ => True)) (clear_shadow a sz).
Proof.
unfold clear_shadow. destruct (remap_range a sz) as [[pb len]|]; [|apply tall_rok_ret; exact I].
apply tall_vis. intros [|b] _; exact I.
Qed.

Definition only_sec (s s' : AState) : Prop :=
(forall c, cls s' c = cls s c) /\ as_next s' = as_next s /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s /\
as_cache_inited s' = as_cache_inited s.

Definition large_alloc_post (s : AState) (n : Z) (r : option Z * AState) : Prop :=
let '(o, s') := r in
match o with
| None => s' = s
| Some mb =>
aok (EvMapAnon (sec_map_size n) (avoid_of L s)) (AOk mb) /\ only_sec s s' /\
as_reg s' = as_reg s ++ [mkSec mb (sec_map_size n) n] /\
(as_nres s' = as_nres s \/ (as_nres s' = as_nres s + kPtrArrBlock /\ as_nres s = zlen (as_reg s))) /\
zlen (as_reg s') <= as_nres s'
end.

Lemma large_alloc_spec s n :
zlen (as_reg s) <= as_nres s -> zlen (as_reg s) < kMaxNumChunks ->
tall aok (rok (large_alloc_post s n)) (large_alloc L s n).
Proof.
intros Hres Hmax. unfold large_alloc. apply tall_vis. intros a Ha.
destruct a as [|mb].
- apply tall_rok_ret. reflexivity.
- unfold zlen in *. destruct (Z.leb_spec kMaxNumChunks (Z.of_nat (length (as_reg s)))); [lia|].
eapply (tall_bind_rok aok (fun s1 => only_sec s s1 /\ as_reg s1 = as_reg s /\
(as_nres s1 = as_nres s \/ (as_nres s1 = as_nres s + kPtrArrBlock /\ as_nres s = zlen (as_reg s))) /\ Z.of_nat (length (as_reg s)) + 1 <= as_nres s1)).
{ destruct (Z.eqb_spec (Z.of_nat (length (as_reg s))) (as_nres s)) as [Heq|Hne].
- apply tall_vis. intros [|b] Hb; [exact (aok_fixed _ _ Hb)|].
apply tall_rok_ret. unfold kPtrArrBlock, zlen. split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [right; split; cbn; lia| cbn; lia].
- apply tall_rok_ret. split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [left; reflexivity| lia]. }
intros s1 (Ho & Hr & Hn & Hle). apply tall_rok_ret. cbn.
destruct Ho as (O1 & O2 & O3 & O4 & O5).
split; [exact Ha|]. split; [repeat split; cbn; auto|]. cbn. rewrite Hr. split; [reflexivity|]. split; [exact Hn|].
unfold zlen. rewrite length_app. cbn. lia.
Qed.

Lemma find_sec_spec a l i0 :
match find_sec a l i0 with
| None => ~ In a (map se_beg l)
| Some (i, e) => (i0 <= i)%nat /\ nth_error l (i - i0) = Some e /\ se_beg e = a
end.
Proof.
revert i0. induction l as [|e l IH]; intros i0; cbn; [tauto|].
destruct (Z.eqb_spec (se_beg e) a) as [E|NE].
- rewrite Nat.sub_diag. cbn. auto.
- specialize (IH (S i0)). destruct (find_sec a l (S i0)) as [[i e']|].
+ destruct IH as (H1 & H2 & H3). split; [lia|]. split; [|exact H3].
replace (i - i0)%nat with (S (i - S i0))%nat by lia. cbn. exact H2.
+ intros [H|H]; [congruence| exact (IH H)].
Qed.

Lemma list_upd_app_l {A} (m r : list A) i v : (i < length m)%nat -> list_upd (m ++ r) i v = list_upd m i v ++ r.
Proof. revert i. induction m as [|x m IH]; intros [|i] H; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.
Lemma list_upd_mid {A} (m1 m2 : list A) e v : list_upd (m1 ++ e :: m2) (length m1) v = m1 ++ v :: m2.
Proof. induction m1 as [|x m1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma swap_remove_perm {A} (l : list A) i e :
nth_error l i = Some e -> Permutation (e :: swap_remove i l) l.
Proof.
intros Hi. unfold swap_remove.
destruct (rev l) as [|lst rl] eqn:Er.
{ exfalso. destruct l as [|y l']; [destruct i; discriminate|]. cbn in Er. destruct (rev l'); discriminate. }
assert (El : l = rev rl ++ [lst]) by (rewrite <- (rev_involutive l), Er; reflexivity).
rewrite El in Hi |- *. set (m := rev rl) in *. clearbody m. clear Er El rl l.
destruct (Nat.ltb_spec i (length m)) as [Hlt|Hge].
- rewrite nth_error_app1 in Hi by exact Hlt.
destruct (nth_error_split m i Hi) as (m1 & m2 & -> & Hlen). subst i.
rewrite list_upd_app_l by (rewrite length_app; cbn; lia).
rewrite list_upd_mid. rewrite (removelast_app (m1 ++ lst :: m2)) by discriminate. cbn [removelast]. rewrite app_nil_r.
rewrite <- app_assoc. cbn [app].
apply (Permutation_trans (l' := e :: m1 ++ m2 ++ [lst])).
+ apply perm_skip. apply Permutation_app_head. apply Permutation_cons_append.
+ apply Permutation_middle.
- rewrite nth_error_app2 in Hi by lia.
assert (i = length m) as ->.
{ destruct (i - length m)%nat as [|k] eqn:E; [lia|]. cbn in Hi. destruct k; discriminate. }
rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as ->.
rewrite list_upd_mid. rewrite (removelast_app m) by discriminate. cbn [removelast]. rewrite app_nil_r.
apply Permutation_cons_append.
Qed.

Definition large_dealloc_post (s : AState) (a : Z) (s' : AState) : Prop :=
only_sec s s' /\ as_nres s' = as_nres s /\
exists e, se_beg e = a /\ Permutation (e :: as_reg s') (as_reg s).

Lemma large_dealloc_spec s a :
In a (map se_beg (as_reg s)) ->
tall aok (rok (large_dealloc_post s a)) (large_dealloc s a).
Proof.
intros Hin. unfold large_dealloc.
pose proof (find_sec_spec a (as_reg s) 0) as F.
destruct (find_sec a (as_reg s) 0) as [[i e]|]; [|exfalso; exact (F Hin)].
destruct F as (_ & Hnth & Hbeg). rewrite Nat.sub_0_r in Hnth.
eapply tall_bind_rok; [apply clear_shadow_spec|]. intros [] _.
apply tall_vis. intros [|b] Hb.
- exact I.
- apply tall_rok_ret. unfold large_dealloc_post. split; [repeat split; reflexivity|]. split; [reflexivity|].
exists e. split; [exact Hbeg|]. cbn. apply swap_remove_perm. exact Hnth.
Qed.

Lemma cntc_cons c p l : cntc c (p :: l) = (if is_cls c p then 1 else 0) + cntc c l.
Proof. unfold cntc. apply zcount_cons. Qed.
Lemma cntc_app c l1 l2 : cntc c (l1 ++ l2) = cntc c l1 + cntc c l2.
Proof. unfold cntc. apply zcount_app. Qed.
Lemma cntc_nonneg c l : 0 <= cntc c l.
Proof. unfold cntc. apply zcount_nonneg. Qed.
Lemma cntc_perm c l l' : Permutation l l' -> cntc c l = cntc c l'.
Proof. unfold cntc. apply zcount_perm. Qed.
Lemma secs_app l1 l2 : secs (l1 ++ l2) = secs l1 ++ secs l2.
Proof. induction l1 as [|[i m|a m] l1 IH]; cbn; rewrite ?IH; reflexivity. Qed.
Lemma secs_perm l l' : Permutation l l' -> Permutation (secs l) (secs l').
Proof.
induction 1 as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
- constructor.
- destruct x; cbn; [exact IH| apply perm_skip; exact IH].
- destruct x, y; cbn; try apply Permutation_refl; try apply perm_swap; apply perm_skip; apply Permutation_refl.
- etransitivity; eassumption.
Qed.
Lemma nbat_nonneg q : 0 <= nbat q.
Proof. unfold nbat. apply zlen_nonneg. Qed.
Lemma tot_nonneg X E B s c : 0 <= B -> 0 <= tot X E B s c.
Proof.
intros HB. unfold tot. pose proof (cntc_nonneg c (allptrs X E s)). pose proof (nbat_nonneg (as_tq s)). pose proof (nbat_nonneg (as_gq s)).
destruct (c =? kBatchClass); lia.
Qed.

Lemma allptrs_only_cls X E c s s' : only_cls c s s' -> allptrs X E s' = allptrs X E s.
Proof. intros (_&_&_&_&T&G). unfold allptrs. rewrite T, G. reflexivity. Qed.
Lemma tot_only_cls X E B c s s' : only_cls c s s' -> forall c', tot X E B s' c' = tot X E B s c'.
Proof. intros Ho c'. unfold tot. rewrite (allptrs_only_cls X E c s s' Ho). destruct Ho as (_&_&_&_&T&G). rewrite T, G. reflexivity. Qed.

Lemma allptrs_set_next X E v s : allptrs X E (set_next v s) = allptrs X E s. Proof. reflexivity. Qed.

Lemma tot_set_next X E B v s c : tot X E B (set_next v s) c = tot X E B s c. Proof. reflexivity. Qed.

Lemma allptrs_cons_X p X E s : allptrs (p :: X) E s = p :: allptrs X E s. Proof. reflexivity. Qed.
Lemma tot_cons_X p X E B s c : tot (p :: X) E B s c = (if is_cls c p then 1 else 0) + tot X E B s c.
Proof. unfold tot. rewrite allptrs_cons_X, cntc_cons. lia. Qed.

Lemma ainvx_frame_cls X E B c s s' :
ainvx X E B s -> only_cls c s s' -> cwf c (cls s' c) -> acc c (cls s' c) = acc c (cls s c) ->
ainvx X E B s'.
Proof.
intros I Ho W Hacc. pose proof Ho as Ho'. destruct Ho as (Hc & Hn & Hr & Hnr & Ht & Hg).
constructor.
- intros c'. destruct (Z.eq_dec c' c) as [->|Hne]; [exact W|]. rewrite (Hc _ Hne). apply (ai_cls _ _ _ _ I).
- intros c' Hc'. rewrite (tot_only_cls X E B c s s' Ho').
destruct (Z.eq_dec c' c) as [->|Hne]; [rewrite Hacc| rewrite (Hc _ Hne)]; apply (ai_cons _ _ _ _ I); exact Hc'.
- rewrite Ht. apply (ai_tq _ _ _ _ I).
- rewrite Hg. apply (ai_gq _ _ _ _ I).
- apply (ai_B _ _ _ _ I).
- rewrite Hn, (allptrs_only_cls X E c s s' Ho'). apply (ai_pwf _ _ _ _ I).
- rewrite Hr, (allptrs_only_cls X E c s s' Ho'). apply (ai_reg _ _ _ _ I).
- rewrite Hr. apply (ai_regw _ _ _ _ I).
- rewrite Hr. apply (ai_regd _ _ _ _ I).
- rewrite Hr, Hnr. apply (ai_nres _ _ _ _ I).
Qed.

Lemma pwf_mono n n' p : (n <= n')%N -> pwf n p -> pwf n' p.
Proof. destruct p; cbn; [|tauto]. intros H (H1 & H2 & H3). repeat split; auto. lia. Qed.

End Ops.

Lemma allptrs_only_sec X E s s' : only_sec s s' -> allptrs X E s' = allptrs X E s.
Proof. intros (_&_&T&G&_). unfold allptrs. rewrite T, G. reflexivity. Qed.
Lemma tot_only_sec X E B s s' : only_sec s s' -> forall c, tot X E B s' c = tot X E B s c.
Proof. intros Ho c. unfold tot. rewrite (allptrs_only_sec X E s s' Ho). destruct Ho as (_&_&T&G&_). rewrite T, G. reflexivity. Qed.

Lemma reg_pairs_app l1 l2 : reg_pairs (l1 ++ l2) = reg_pairs l1 ++ reg_pairs l2.
Proof. unfold reg_pairs. apply map_app. Qed.

Lemma NoDup_app_single {A} (l : list A) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
intros Hl Hx. apply NoDup_app. split; [exact Hl|]. split.
- intros y Hy Hyx. apply list_elem_of_In in Hy. apply list_elem_of_In in Hyx.
destruct Hyx as [<-|[]]. exact (Hx Hy).
- constructor; [intros H; inversion H| constructor].
Qed.

Lemma ainvx_perm_gen X E B s X2 E2 s2 :
ainvx X E B s ->
(forall c, cls s2 c = cls s c) -> as_next s2 = as_next s -> as_reg s2 = as_reg s -> as_nres s2 = as_nres s ->
qwf (as_tq s2) -> qwf (as_gq s2) ->
Permutation (allptrs X E s) (allptrs X2 E2 s2) ->
nbat (as_tq s2) + nbat (as_gq s2) = nbat (as_tq s) + nbat (as_gq s) ->
ainvx X2 E2 B s2.
Proof.
intros I Hc Hn Hr Hnr Qt Qg P Hnb. constructor.
- intros c. rewrite Hc. apply (ai_cls _ _ _ _ I).
- intros c Hc'. rewrite Hc, (ai_cons _ _ _ _ I c Hc'). unfold tot. rewrite (cntc_perm c _ _ P).
destruct (c =? kBatchClass); lia.
- exact Qt.
- exact Qg.
- apply (ai_B _ _ _ _ I).
- rewrite Hn. eapply Permutation_Forall; [exact P| apply (ai_pwf _ _ _ _ I)].
- rewrite Hr. etransitivity; [apply (ai_reg _ _ _ _ I)| apply secs_perm; exact P].
- rewrite Hr. apply (ai_regw _ _ _ _ I).
- rewrite Hr. apply (ai_regd _ _ _ _ I).
- rewrite Hr, Hnr. apply (ai_nres _ _ _ _ I).
Qed.

Lemma ainvx_perm X E X2 E2 B s :
Permutation (X ++ E) (X2 ++ E2) -> ainvx X E B s -> ainvx X2 E2 B s.
Proof.
intros P I. eapply ainvx_perm_gen; try exact I; try reflexivity; [apply (ai_tq _ _ _ _ I)| apply (ai_gq _ _ _ _ I)|].
unfold allptrs. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_tail. exact P.
Qed.

Lemma qchunks_list q : qchunks q = flat_map b_chunks (q_list q). Proof. reflexivity. Qed.

Lemma flat_map_snoc {A B} (f : A -> list B) l x : flat_map f (l ++ [x]) = flat_map f l ++ f x.
Proof. rewrite flat_map_app. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma zsum_snoc l x : zsum (l ++ [x]) = zsum l + x.
Proof. rewrite zsum_app, zsum_cons, zsum_nil. lia. Qed.

Lemma bwf_size_ge lo b : bwf lo b -> kBatchBytes + b_count b <= b_size b.
Proof.
intros (Hc & Hlo & Hs). rewrite Hs, Hc.
assert (forall l, zlen l <= zsum (map aptr_used l)) as G.
{ induction l as [|y l IH]; [unfold zlen; cbn; lia|]. rewrite zlen_cons. cbn [map]. rewrite zsum_cons. assert (1 <= aptr_used y) by apply used_size_pos. lia. }
pose proof (G (b_chunks b)). lia.
Qed.

Lemma qwf_bytes_ge q : qwf q -> kBatchBytes * nbat q <= q_bytes q.
Proof.
destruct q as [l bytes]. intros [F E]. cbn in *. subst bytes. unfold nbat. cbn. revert F.
induction l as [|b l IH]; intros F; [unfold zlen; cbn; lia|].
inversion F; subst. rewrite zlen_cons. cbn [map foldr]. pose proof (bwf_size_ge _ _ H1). pose proof (proj1 (proj2 H1)). specialize (IH H2). unfold kBatchBytes in *. lia.
Qed.

Lemma ainvx_reest X E B s X2 E2 B2 s2 c d R :
ainvx X E B s -> 1 <= c <= 31 ->
(forall c', c' <> c -> cls s2 c' = cls s c') -> cwf c (cls s2 c) ->
acc c (cls s2 c) = acc c (cls s c) + class_size c * d ->
as_next s2 = as_next s -> as_reg s2 = as_reg s -> as_nres s2 = as_nres s ->
qwf (as_tq s2) -> qwf (as_gq s2) -> 0 <= B2 ->
Permutation (allptrs X E s) (R ++ allptrs X2 E2 s2) -> secs R = [] ->
(forall c', 1 <= c' <= 31 -> tot X2 E2 B2 s2 c' = tot X E B s c' + (if c' =? c then d else 0)) ->
ainvx X2 E2 B2 s2.
Proof.
intros I Hc Hcl W Hacc Hn Hr Hnr Qt Qg HB P HR Htot. constructor.
- intros c'. destruct (Z.eq_dec c' c) as [->|Hne]; [exact W|]. rewrite (Hcl _ Hne). apply (ai_cls _ _ _ _ I).
- intros c' Hc'. rewrite (Htot c' Hc'). destruct (Z.eq_dec c' c) as [->|Hne].
+ rewrite Z.eqb_refl, Hacc, (ai_cons _ _ _ _ I c Hc). lia.
+ rewrite (proj2 (Z.eqb_neq c' c) Hne), (Hcl _ Hne), (ai_cons _ _ _ _ I c' Hc'). lia.
- exact Qt.
- exact Qg.
- exact HB.
- rewrite Hn. pose proof (Permutation_Forall P (ai_pwf _ _ _ _ I)) as F. apply Forall_app in F as [_ F]. exact F.
- rewrite Hr. etransitivity; [apply (ai_reg _ _ _ _ I)|]. etransitivity; [apply secs_perm; exact P|]. rewrite secs_app, HR. apply Permutation_refl.
- rewrite Hr. apply (ai_regw _ _ _ _ I).
- rewrite Hr. apply (ai_regd _ _ _ _ I).
- rewrite Hr, Hnr. apply (ai_nres _ _ _ _ I).
Qed.

Lemma split_last_spec {A} (l : list A) :
match split_last l with None => l = [] | Some (f, x) => l = f ++ [x] end.
Proof.
induction l as [|y l IH]; cbn; [reflexivity|].
destruct (split_last l) as [[f x]|]; subst; reflexivity.
Qed.

Lemma qwf_push_back q b : qwf q -> bwf 1 b -> qwf (q_push_back q b).
Proof.
intros [F E] Wb. unfold q_push_back. split; cbn.
- apply Forall_app. split; [exact F| constructor; [exact Wb| constructor]].
- rewrite map_app. cbn [map]. rewrite zsum_snoc. lia.
Qed.

Definition sec24_room (s : AState) : Prop :=
c_count (cls s kBatchClass) = 0 -> c_num_freed (cls s kBatchClass) < 8 ->
c_alloc_user (cls s kBatchClass) + 8 * class_size kBatchClass <= kFreeArrayOffset.

Definition enqueue_post (X : list aptr) (B : Z) (s : AState) (p : aptr) (s' : AState) : Prop :=
ainvx X [] B s' /\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_next s' = as_next s /\
q_bytes (as_tq s') <= q_bytes (as_tq s) + aptr_used p + kBatchBytes /\
(forall c, c <> kBatchClass -> cls s' c = cls s c) /\ c_mapped_user (cls s kBatchClass) <= c_mapped_user (cls s' kBatchClass).

Lemma kBatchClass_range : 1 <= kBatchClass <= 31. Proof. unfold kBatchClass. lia. Qed.

Lemma new_batch_inv L aok X p B s :
ainvx X [p] B s -> sec24_room s ->
tall aok (rok (enqueue_post X B s p)) (new_batch L s p (aptr_used p)).
Proof.
intros AI Hroom. unfold new_batch.
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI _ H24) as Hcons. pose proof (ai_cls _ _ _ _ AI kBatchClass) as W.
pose proof (cw_cnt _ _ W) as Wcnt. pose proof (cw_nf _ _ W) as Wnf. pose proof (ai_B _ _ _ _ AI) as HB.
pose proof (tot_nonneg X [p] B s kBatchClass HB) as Htot.
assert (Hm1 : 0 <= class_size kBatchClass * c_count (cls s kBatchClass)) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hm2 : 0 <= class_size kBatchClass * tot X [p] B s kBatchClass) by (apply Z.mul_nonneg_nonneg; lia).
unfold acc in Hcons.
eapply tall_bind_rok.
{ apply (cache_alloc_spec L aok s kBatchClass); [exact H24| exact W| lia| exact Hroom]. }
intros [ok s1] (Ho & W1 & Hmu & Hnf1 & Hacc). destruct ok; cbn [negb]; [|exact I].
apply tall_rok_ret. pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Hr & Hnr & Ht & Hg).
assert (Wb : bwf 1 (mkB [p] 1 (aptr_used p + kBatchBytes))).
{ unfold bwf. cbn. unfold zlen, kBatchCount. cbn. repeat split; lia. }
unfold enqueue_post. cbn [as_gq as_reg as_nres as_next as_tq set_tq]. rewrite !cls_set_tq.
split.
- eapply (ainvx_reest X [p] B s _ _ _ _ kBatchClass 1 []); [exact AI| exact H24| ..]; cbn [as_next as_reg as_nres as_tq as_gq set_tq app secs].
+ intros c' Hc'. rewrite cls_set_tq. apply Hcl. exact Hc'.
+ rewrite cls_set_tq. exact W1.
+ rewrite cls_set_tq. lia.
+ exact Hnx.
+ exact Hr.
+ exact Hnr.
+ apply qwf_push_back; [rewrite Ht; apply (ai_tq _ _ _ _ AI)| exact Wb].
+ rewrite Hg. apply (ai_gq _ _ _ _ AI).
+ exact HB.
+ unfold allptrs. cbn [as_tq as_gq set_tq app]. rewrite Hg, Ht. unfold q_push_back. rewrite !qchunks_list. cbn [q_list].
rewrite flat_map_snoc. cbn [b_chunks].
apply Permutation_app_head. rewrite <- app_assoc. cbn [app]. apply Permutation_middle.
+ reflexivity.
+ intros c' Hc'. unfold tot, allptrs. cbn [as_tq as_gq set_tq app]. rewrite Hg, Ht. unfold q_push_back, nbat. rewrite !qchunks_list. cbn [q_list].
rewrite flat_map_snoc. cbn [b_chunks].
rewrite zlen_app. repeat rewrite cntc_app. repeat rewrite cntc_cons. repeat rewrite cntc_app. change (zlen [_]) with 1. change (cntc c' []) with 0.
destruct (c' =? kBatchClass); lia.
- rewrite Hg, Hr, Hnr, Hnx, Ht. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [cbn; lia|]. split; [intros c Hc; apply Hcl; exact Hc|]. exact Hmu.
Qed.

Lemma enqueue_inv L aok X p B s :
ainvx X [p] B s -> sec24_room s ->
tall aok (rok (enqueue_post X B s p)) (enqueue L s p).
Proof.
intros AI Hroom. unfold enqueue.
pose proof (split_last_spec (q_list (as_tq s))) as SL.
destruct (split_last (q_list (as_tq s))) as [[front b]|].
2: { apply new_batch_inv; assumption. }
destruct (Z.eqb_spec (b_count b) kBatchCount) as [Hfull|Hnf]; [apply new_batch_inv; assumption|].
apply tall_rok_ret.
pose proof (ai_tq _ _ _ _ AI) as [F E]. rewrite SL in F, E. apply Forall_app in F as [Ff Fb]. inversion Fb as [|b0 l0 Wb _]; subst.
destruct Wb as (Hc & Hlo & Hsz).
set (b' := mkB (b_chunks b ++ [p]) (b_count b + 1) (b_size b + aptr_used p)).
assert (Wb' : bwf 1 b').
{ subst b'. unfold bwf. cbn. rewrite zlen_app, map_app, zsum_app. cbn. unfold zlen at 2. cbn. unfold kBatchCount in *. repeat split; try lia. }
assert (Qwf' : qwf (mkQ (front ++ [b']) (q_bytes (as_tq s) + aptr_used p))).
{ split; cbn.
- apply Forall_app. split; [exact Ff| constructor; [exact Wb'| constructor]].
- rewrite E, !map_app, !zsum_app. cbn. subst b'. cbn. lia. }
pose proof kBatchClass_range as H24.
unfold enqueue_post. cbn [as_gq as_reg as_nres as_next as_tq set_tq q_bytes]. rewrite !cls_set_tq.
split.
- eapply (ainvx_reest X [p] B s _ _ _ _ kBatchClass 0 []); [exact AI| exact H24| ..]; cbn [as_next as_reg as_nres as_tq as_gq set_tq app secs].
+ intros c' _. apply cls_set_tq.
+ rewrite cls_set_tq. apply (ai_cls _ _ _ _ AI).
+ rewrite cls_set_tq. lia.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ exact Qwf'.
+ apply (ai_gq _ _ _ _ AI).
+ apply (ai_B _ _ _ _ AI).
+ unfold allptrs. cbn [as_tq as_gq set_tq app]. rewrite !qchunks_list. cbn [q_list]. rewrite SL.
rewrite !flat_map_snoc. subst b'. cbn [b_chunks].
apply Permutation_app_head. rewrite <- !app_assoc. cbn [app].
rewrite (app_assoc (flat_map b_chunks front) (b_chunks b) (p :: _)).
rewrite (app_assoc (flat_map b_chunks front) (b_chunks b)). apply Permutation_middle.
+ reflexivity.
+ intros c' Hc'. unfold tot, allptrs. cbn [as_tq as_gq set_tq app]. unfold nbat. rewrite !qchunks_list. cbn [q_list]. rewrite SL.
rewrite !flat_map_snoc, !zlen_app. subst b'. cbn [b_chunks].
repeat rewrite cntc_app. repeat rewrite cntc_cons. repeat rewrite cntc_app. change (zlen [_]) with 1. change (cntc c' []) with 0.
destruct (c' =? kBatchClass); lia.
- split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold kBatchBytes; pose proof (used_size_pos (aptr_req p)); unfold aptr_used; lia|]. split; [intros c _; reflexivity|]. lia.
Qed.

Definition transfer (s : AState) : AState :=
set_gq (mkQ (q_list (as_gq s) ++ q_list (as_tq s)) (q_bytes (as_gq s) + q_bytes (as_tq s))) (set_tq q0 s).

Lemma qwf_q0 : qwf q0. Proof. split; [constructor| reflexivity]. Qed.

Lemma transfer_inv X B s : ainvx X [] B s -> ainvx X [] B (transfer s).
Proof.
intros AI. pose proof kBatchClass_range as H24. unfold transfer.
pose proof (ai_tq _ _ _ _ AI) as [Ft Et]. pose proof (ai_gq _ _ _ _ AI) as [Fg Eg].
eapply (ainvx_reest X [] B s _ _ _ _ kBatchClass 0 []); [exact AI| exact H24| ..]; cbn [as_next as_reg as_nres as_tq as_gq set_tq set_gq app secs].
- intros c' _. reflexivity.
- apply (ai_cls _ _ _ _ AI).
- rewrite cls_set_gq, cls_set_tq. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- apply qwf_q0.
- split; cbn; [apply Forall_app; split; assumption| rewrite map_app, zsum_app; lia].
- apply (ai_B _ _ _ _ AI).
- unfold allptrs. cbn [as_tq as_gq set_tq set_gq app]. rewrite !qchunks_list. unfold q0. cbn [q_list flat_map app]. rewrite flat_map_app.
apply Permutation_app_head. apply Permutation_app_comm.
- reflexivity.
- intros c' Hc'. unfold tot, allptrs, nbat. cbn [as_tq as_gq set_tq set_gq app q_list]. rewrite !qchunks_list. unfold q0. cbn [q_list flat_map app].
rewrite flat_map_app, !zlen_app. repeat rewrite cntc_app. change (@zlen batch []) with 0. destruct (c' =? kBatchClass); lia.
Qed.

Definition empty_batch : batch := mkB [] 0 kBatchBytes.

Lemma merge_loop_spec cur rest :
bwf 1 cur -> Forall (bwf 1) rest ->
let '(l, ex) := merge_loop cur rest in
Forall (bwf 1) l /\ flat_map b_chunks l = b_chunks cur ++ flat_map b_chunks rest /\
zsum (map b_size l) + kBatchBytes * zlen ex = b_size cur + zsum (map b_size rest) /\
zlen l + zlen ex = 1 + zlen rest /\ Forall (fun b => b = empty_batch) ex.
Proof.
revert cur. induction rest as [|nx rest IH]; intros cur Wc F; cbn [merge_loop].
- unfold zlen. cbn. rewrite app_nil_r. repeat split; auto; lia.
- inversion F as [|nx0 r0 Wn Fr]; subst.
destruct (Z.leb_spec (b_count cur + b_count nx) kBatchCount) as [Hle|Hgt].
+ set (cur' := mkB (b_chunks cur ++ b_chunks nx) (b_count cur + b_count nx) (b_size cur + (b_size nx - kBatchBytes))).
assert (Wc' : bwf 1 cur').
{ destruct Wc as (C1 & L1 & S1). destruct Wn as (C2 & L2 & S2). subst cur'. unfold bwf. cbn.
rewrite zlen_app, map_app, zsum_app. repeat split; lia. }
specialize (IH cur' Wc' Fr). destruct (merge_loop cur' rest) as [l ex].
destruct IH as (F1 & C1 & S1 & L1 & E1). subst cur'. cbn [b_chunks b_size] in C1, S1.
rewrite zlen_cons. cbn [map flat_map]. rewrite zsum_cons. rewrite <- app_assoc in C1. rewrite zlen_cons.
repeat split; auto; try lia.
+ specialize (IH nx Wn Fr). destruct (merge_loop nx rest) as [l ex].
destruct IH as (F1 & C1 & S1 & L1 & E1). cbn -[zsum zlen]. rewrite !zlen_cons. rewrite !zsum_cons, C1.
repeat split; auto; try lia.
Qed.

Lemma merge_batches_spec g :
qwf g ->
let '(g1, ex) := merge_batches g in
qwf g1 /\ qchunks g1 = qchunks g /\ nbat g1 + zlen ex = nbat g /\
q_bytes g1 + kBatchBytes * zlen ex = q_bytes g /\ Forall (fun b => b = empty_batch) ex.
Proof.
destruct g as [gl gb]. intros [F E]. cbn in F, E. subst gb. unfold merge_batches, nbat, qchunks. cbn [q_list q_bytes].
destruct gl as [|b rest].
- unfold zlen. cbn. repeat split; auto; try lia.
- inversion F as [|b0 r0 Wb Fr]; subst.
pose proof (merge_loop_spec b rest Wb Fr) as M. destruct (merge_loop b rest) as [l ex].
destruct M as (F1 & C1 & S1 & L1 & E1). cbn -[zsum zlen].
rewrite zlen_cons. unfold zsum, zlen in *.
split; [split; [exact F1| cbn; unfold zlen; lia]|]. split; [exact C1|]. split; [lia|]. split; [lia| exact E1].
Qed.

Lemma pop_loop_spec l : forall bytes tmp,
Forall (bwf 1) l -> bytes = zsum (map b_size l) ->
exists popped g2, pop_loop l bytes tmp = Some (g2, tmp ++ popped) /\ l = popped ++ q_list g2 /\
qwf g2 /\ q_bytes g2 <= kQMinSize /\ Forall (bwf 1) popped.
Proof.
induction l as [|b l IH]; intros bytes tmp F E; cbn [pop_loop].
- cbn in E. subst bytes. destruct (Z.ltb_spec kQMinSize 0); [unfold kQMinSize in *; lia|].
exists [], (mkQ [] 0). rewrite app_nil_r. split; [reflexivity|]. split; [reflexivity|].
split; [apply qwf_q0|]. split; [cbn; unfold kQMinSize; lia| constructor].
- apply Forall_cons_iff in F as [Wb Fl]. cbn [map] in E. rewrite zsum_cons in E.
destruct (Z.ltb_spec kQMinSize bytes) as [Hgt|Hle].
+ destruct (IH (bytes - b_size b) (tmp ++ [b]) Fl ltac:(lia)) as (popped & g2 & Hp & Hl & Q2 & Hb & Fp).
exists (b :: popped), g2. rewrite Hp, <- app_assoc. cbn [app]. split; [reflexivity|]. split; [rewrite Hl at 1; reflexivity|].
split; [exact Q2|]. split; [exact Hb| constructor; assumption].
+ exists [], (mkQ (b :: l) bytes). rewrite app_nil_r. cbn [q_list q_bytes]. split; [reflexivity|]. split; [reflexivity|].
split; [split; cbn -[zsum]; [constructor; assumption| rewrite zsum_cons; exact E]|]. split; [cbn; lia| constructor].
Qed.

Lemma nodup_fst_functional {A B} (l : list (A * B)) a x y :
NoDup (map fst l) -> In (a, x) l -> In (a, y) l -> x = y.
Proof.
induction l as [|[a0 b0] l IH]; cbn; intros ND Hx Hy; [destruct Hx|].
inversion ND as [|? ? Hni ND']; subst.
destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
- congruence.
- injection Hx as -> ->. exfalso. apply Hni. apply list_elem_of_In. apply in_map_iff. exists (a, y). auto.
- injection Hy as -> ->. exfalso. apply Hni. apply list_elem_of_In. apply in_map_iff. exists (a, x). auto.
- eauto.
Qed.

Lemma in_secs_allptrs a n l : In (ASec a n) l -> In (a, n) (secs l).
Proof.
induction l as [|[i m|b m] l IH]; cbn; intros H; [destruct H| |].
- destruct H as [H|H]; [discriminate| auto].
- destruct H as [H|H]; [injection H as -> ->; left; reflexivity| right; auto].
Qed.

Lemma map_fst_reg_pairs r : map fst (reg_pairs r) = map se_beg r.
Proof. unfold reg_pairs. rewrite map_map. reflexivity. Qed.

Section Rec.
Variable L : ALay.
Variable aok : evA -> ansA -> Prop.

Definition keeps_q (s s' : AState) : Prop := as_tq s' = as_tq s /\ as_gq s' = as_gq s.

Lemma recycle_chunk_inv X p E B s :
ainvx X (p :: E) B s ->
tall aok (rok (fun s' => ainvx X E B s' /\ keeps_q s s')) (recycle_chunk L s p).
Proof.
intros AI. unfold recycle_chunk.
pose proof (ai_pwf _ _ _ _ AI) as PW. unfold allptrs in PW. rewrite List.Forall_forall in PW.
assert (Hp : In p (X ++ (p :: E) ++ qchunks (as_tq s) ++ qchunks (as_gq s))) by (apply in_or_app; right; left; reflexivity).
specialize (PW _ Hp).
destruct p as [id n|a n]; cbn in PW.
-
destruct PW as (Hid & Hn & Hprim).
pose proof (class_of_facts n Hn Hprim) as (Hc & _ & _). set (c := class_of n) in *.
assert (Hc31 : 1 <= c <= 31) by lia. pose proof (class_facts c Hc31) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI c Hc31) as Hcons. pose proof (ai_cls _ _ _ _ AI c) as W.
assert (Htot1 : 1 <= tot X (APrim id n :: E) B s c).
{ unfold tot, allptrs. repeat rewrite cntc_app. rewrite cntc_cons. cbn [is_cls]. fold c. rewrite Z.eqb_refl.
pose proof (cntc_nonneg c X). pose proof (cntc_nonneg c E). pose proof (cntc_nonneg c (qchunks (as_tq s))). pose proof (cntc_nonneg c (qchunks (as_gq s))).
pose proof (nbat_nonneg (as_tq s)). pose proof (nbat_nonneg (as_gq s)). pose proof (ai_B _ _ _ _ AI).
destruct (c =? kBatchClass); lia. }
assert (Hm : class_size c * 1 <= class_size c * tot X (APrim id n :: E) B s c) by (apply Z.mul_le_mono_nonneg_l; lia).
eapply tall_mono.
{ apply (cache_dealloc_spec L aok s c); [exact Hc31| exact W|]. unfold acc in Hcons. lia. }
intros [s1| |w]; cbn; [|auto|auto]. intros (Ho & W1 & Hacc & Eau & Emu).
pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Hr & Hnr & Ht & Hg).
split; [|split; [exact Ht| exact Hg]].
eapply (ainvx_reest X (APrim id n :: E) B s _ _ _ _ c (-1) [APrim id n]); [exact AI| exact Hc31| exact Hcl| exact W1| lia| exact Hnx| exact Hr| exact Hnr| ..].
+ rewrite Ht. apply (ai_tq _ _ _ _ AI).
+ rewrite Hg. apply (ai_gq _ _ _ _ AI).
+ apply (ai_B _ _ _ _ AI).
+ rewrite (allptrs_only_cls X E c s s1 Ho'). unfold allptrs. cbn [app]. apply Permutation_sym. apply Permutation_middle.
+ reflexivity.
+ intros c' Hc'. rewrite (tot_only_cls X E B c s s1 Ho'). unfold tot, allptrs. repeat rewrite cntc_app. rewrite cntc_cons. cbn [is_cls]. fold c.
rewrite (Z.eqb_sym c c'). destruct (c' =? c); destruct (c' =? kBatchClass); lia.
-
destruct PW as (Hn & Hsec).
assert (Hin : In (a, n) (reg_pairs (as_reg s))).
{ eapply Permutation_in; [apply Permutation_sym; apply (ai_reg _ _ _ _ AI)|]. apply in_secs_allptrs. exact Hp. }
eapply tall_mono.
{ apply (large_dealloc_spec aok s a).
unfold reg_pairs in Hin. apply in_map_iff in Hin as (e & He & Hine). apply in_map_iff. exists e. injection He as H1 H2. auto. }
intros [s1| |w]; cbn; [|auto|auto]. intros (Ho & Hnres & e & Hbeg & Pe).
pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Ht & Hg & _).
split; [|split; [exact Ht| exact Hg]].
assert (Hreq : se_req e = n).
{ apply (nodup_fst_functional (reg_pairs (as_reg s)) a); [rewrite map_fst_reg_pairs; apply (ai_regd _ _ _ _ AI)| |exact Hin].
unfold reg_pairs. apply in_map_iff. exists e. split; [rewrite Hbeg; reflexivity|]. eapply Permutation_in; [exact Pe| left; reflexivity]. }
constructor.
+ intros c'. rewrite Hcl. apply (ai_cls _ _ _ _ AI).
+ intros c' Hc'. rewrite Hcl, (ai_cons _ _ _ _ AI c' Hc'). f_equal. unfold tot. rewrite (allptrs_only_sec X E s s1 Ho'), Ht, Hg.
unfold allptrs. repeat rewrite cntc_app. rewrite cntc_cons. cbn [is_cls]. lia.
+ rewrite Ht. apply (ai_tq _ _ _ _ AI).
+ rewrite Hg. apply (ai_gq _ _ _ _ AI).
+ apply (ai_B _ _ _ _ AI).
+ rewrite Hnx, (allptrs_only_sec X E s s1 Ho'). pose proof (ai_pwf _ _ _ _ AI) as F. unfold allptrs in *.
apply Forall_app in F as [F1 F]. apply Forall_cons_iff in F as [_ F]. apply Forall_app. auto.
+ rewrite (allptrs_only_sec X E s s1 Ho').
apply (Permutation_cons_inv (a := (a, n))).
transitivity (reg_pairs (as_reg s)).
{ change ((a, n) :: reg_pairs (as_reg s1)) with (reg_pairs (mkSec a 0 n :: as_reg s1)).
unfold reg_pairs. cbn [map se_beg se_req]. rewrite <- Hbeg, <- Hreq.
change ((se_beg e, se_req e) :: map (fun e0 => (se_beg e0, se_req e0)) (as_reg s1))
with (map (fun e0 => (se_beg e0, se_req e0)) (e :: as_reg s1)).
apply Permutation_map. exact Pe. }
transitivity (secs (allptrs X (ASec a n :: E) s)); [apply (ai_reg _ _ _ _ AI)|].
change ((a, n) :: secs (allptrs X E s)) with (secs (ASec a n :: allptrs X E s)).
apply secs_perm. unfold allptrs. cbn [app]. apply Permutation_sym. apply Permutation_middle.
+ pose proof (ai_regw _ _ _ _ AI) as F. eapply Permutation_Forall in F; [|apply Permutation_sym; exact Pe]. inversion F; assumption.
+ pose proof (ai_regd _ _ _ _ AI) as ND. apply NoDup_ListNoDup in ND.
eapply (Permutation_NoDup (l' := map se_beg (e :: as_reg s1))) in ND; [|apply Permutation_map; apply Permutation_sym; exact Pe].
cbn in ND. apply NoDup_ListNoDup. inversion ND; assumption.
+ rewrite Hnres. pose proof (ai_nres _ _ _ _ AI) as (N1 & N2 & N3). split; [|split; assumption].
pose proof (Permutation_length Pe) as Hl. cbn in Hl. unfold zlen in *. lia.
Qed.

Lemma recycle_chunks_inv X ps : forall E B s,
ainvx X (ps ++ E) B s ->
tall aok (rok (fun s' => ainvx X E B s' /\ keeps_q s s')) (recycle_chunks L s ps).
Proof.
induction ps as [|p ps IH]; intros E B s AI; cbn [recycle_chunks app] in *.
- apply tall_rok_ret. split; [exact AI| split; reflexivity].
- eapply tall_bind_rok; [apply (recycle_chunk_inv X p (ps ++ E) B s AI)|].
intros s1 [AI1 [T1 G1]]. eapply tall_mono; [apply IH; exact AI1|].
intros [s2| |w]; cbn; auto. intros [AI2 [T2 G2]]. split; [exact AI2|]. split; congruence.
Qed.

Lemma do_recycle_inv X bs : forall s,
ainvx X (flat_map b_chunks bs) (zlen bs) s -> Forall (bwf 0) bs ->
tall aok (rok (fun s' => ainvx X [] 0 s' /\ keeps_q s s')) (do_recycle L s bs).
Proof.
induction bs as [|b bs IH]; intros s AI F; cbn [do_recycle flat_map] in *.
- apply tall_rok_ret. split; [exact AI| split; reflexivity].
- apply Forall_cons_iff in F as [Wb F].
eapply tall_bind_rok; [apply (recycle_chunks_inv X (b_chunks b) (flat_map b_chunks bs) (zlen (b :: bs)) s AI)|].
intros s1 [AI1 [T1 G1]].
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI1 _ H24) as Hcons. pose proof (ai_cls _ _ _ _ AI1 kBatchClass) as W.
assert (Htot1 : 1 <= tot X (flat_map b_chunks bs) (zlen (b :: bs)) s1 kBatchClass).
{ unfold tot. rewrite Z.eqb_refl, zlen_cons. pose proof (cntc_nonneg kBatchClass (allptrs X (flat_map b_chunks bs) s1)).
pose proof (nbat_nonneg (as_tq s1)). pose proof (nbat_nonneg (as_gq s1)). pose proof (zlen_nonneg bs). lia. }
assert (Hm : class_size kBatchClass * 1 <= class_size kBatchClass * tot X (flat_map b_chunks bs) (zlen (b :: bs)) s1 kBatchClass)
by (apply Z.mul_le_mono_nonneg_l; lia).
eapply tall_bind_rok.
{ eapply tall_mono; [apply (cache_dealloc_spec L aok s1 kBatchClass); [exact H24| exact W| unfold acc in Hcons; lia]|].
intros [s2| |w]; cbn; [|auto|auto]. intros (Ho & W2 & Hacc & Eau & Emu).
pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Hr & Hnr & Ht & Hg).
assert (AI2 : ainvx X (flat_map b_chunks bs) (zlen bs) s2).
{ eapply (ainvx_reest X (flat_map b_chunks bs) (zlen (b :: bs)) s1 _ _ _ _ kBatchClass (-1) []);
[exact AI1| exact H24| exact Hcl| exact W2| lia| exact Hnx| exact Hr| exact Hnr| ..].
- rewrite Ht. apply (ai_tq _ _ _ _ AI1).
- rewrite Hg. apply (ai_gq _ _ _ _ AI1).
- apply zlen_nonneg.
- rewrite (allptrs_only_cls _ _ kBatchClass s1 s2 Ho'). apply Permutation_refl.
- reflexivity.
- intros c' Hc'. rewrite (tot_only_cls _ _ (zlen bs) kBatchClass s1 s2 Ho'). unfold tot. rewrite zlen_cons.
destruct (c' =? kBatchClass); lia. }
exact (conj AI2 (conj Ht Hg)). }
intros s2 [AI2 [T2 G2]]. eapply tall_mono; [apply IH; [exact AI2| exact F]|].
intros [s3| |w]; cbn; auto. intros [AI3 [T3 G3]]. split; [exact AI3|]. split; congruence.
Qed.

Lemma recycle_shape X s :
ainvx X [] 0 s ->
exists g2 tmp, recycle L s = do_recycle L (set_gq g2 s) tmp /\
ainvx X (flat_map b_chunks tmp) (zlen tmp) (set_gq g2 s) /\ Forall (bwf 0) tmp /\ q_bytes g2 <= kQMinSize.
Proof.
intros AI. unfold recycle.
pose proof (ai_gq _ _ _ _ AI) as Qg. pose proof (qwf_bytes_ge _ Qg) as Hov. unfold nbat in Hov.
destruct (Z.ltb_spec (q_bytes (as_gq s)) (kBatchBytes * Z.of_nat (length (q_list (as_gq s))))); [unfold zlen in Hov; lia|].
set (mg := if (kBatchBytes * Z.of_nat (length (q_list (as_gq s))) <? q_bytes (as_gq s)) && (q_bytes (as_gq s) * 100 <? kBatchBytes * Z.of_nat (length (q_list (as_gq s))) * 200)
then merge_batches (as_gq s) else (as_gq s, [])).
assert (M : let '(g1, ex) := mg in qwf g1 /\ qchunks g1 = qchunks (as_gq s) /\ nbat g1 + zlen ex = nbat (as_gq s) /\
q_bytes g1 + kBatchBytes * zlen ex = q_bytes (as_gq s) /\ Forall (fun b => b = empty_batch) ex).
{ subst mg. destruct (_ && _); [apply merge_batches_spec; exact Qg|]. cbn -[zsum zlen nbat qchunks]. unfold zlen. cbn [length Z.of_nat].
split; [exact Qg|]. split; [reflexivity|]. split; [lia|]. split; [lia| constructor]. }
destruct mg as [g1 ex]. destruct M as (Q1 & C1 & N1 & B1 & E1).
destruct (pop_loop_spec (q_list g1) (q_bytes g1) ex (proj1 Q1) (proj2 Q1)) as (popped & g2 & Hp & Hl & Q2 & Hb2 & Fp).
rewrite Hp. exists g2, (ex ++ popped). split; [reflexivity|].
assert (AI1 : ainvx X (flat_map b_chunks (ex ++ popped)) (zlen (ex ++ popped)) (set_gq g2 s)).
{ pose proof kBatchClass_range as H24.
assert (Hexc : flat_map b_chunks ex = []).
{ clear -E1. induction ex as [|b ex IH]; [reflexivity|]. apply Forall_cons_iff in E1 as [-> E1]. cbn. apply IH. exact E1. }
eapply (ainvx_reest X [] 0 s _ _ _ _ kBatchClass 0 []); [exact AI| exact H24| ..]; cbn [as_next as_reg as_nres as_tq as_gq set_gq].
- intros c' _. apply cls_set_gq.
- rewrite cls_set_gq. apply (ai_cls _ _ _ _ AI).
- rewrite cls_set_gq. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- apply (ai_tq _ _ _ _ AI).
- exact Q2.
- apply zlen_nonneg.
- unfold allptrs. cbn [as_tq as_gq set_gq app]. rewrite flat_map_app, Hexc. cbn [app].
rewrite <- C1, !qchunks_list, Hl, flat_map_app. cbn [q_list].
apply Permutation_app_head. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
- reflexivity.
- intros c' Hc'. unfold tot, allptrs. cbn [as_tq as_gq set_gq app]. rewrite flat_map_app, Hexc. cbn [app].
rewrite <- C1, !qchunks_list, Hl, flat_map_app. unfold nbat in *. rewrite Hl in N1. rewrite !zlen_app in *.
repeat rewrite cntc_app. destruct (c' =? kBatchClass); lia. }
assert (F0 : Forall (bwf 0) (ex ++ popped)).
{ apply Forall_app. split.
- eapply Forall_impl; [exact E1|]. intros b ->. unfold bwf, empty_batch, zlen, kBatchCount. cbn. lia.
- eapply Forall_impl; [exact Fp|]. intros b (C & Lb & S). unfold bwf. repeat split; auto; lia. }
split; [exact AI1|]. split; [exact F0| exact Hb2].
Qed.

Lemma recycle_inv X s :
ainvx X [] 0 s ->
tall aok (rok (fun s' => ainvx X [] 0 s' /\ as_tq s' = as_tq s /\ q_bytes (as_gq s') <= kQMinSize)) (recycle L s).
Proof.
intros AI. destruct (recycle_shape X s AI) as (g2 & tmp & -> & AI1 & F0 & Hb2).
eapply tall_mono; [apply (do_recycle_inv X tmp (set_gq g2 s) AI1 F0)|].
intros [s'| |w]; cbn; auto. intros [AI' [T' G']]. split; [exact AI'|]. split; [exact T'|]. rewrite G'. exact Hb2.
Qed.

Lemma transfer_eq s : transfer s = set_gq (mkQ (q_list (as_gq s) ++ q_list (as_tq s)) (q_bytes (as_gq s) + q_bytes (as_tq s))) (set_tq q0 s).
Proof. reflexivity. Qed.

Lemma drain_inv X s :
ainvx X [] 0 s -> q_bytes (as_gq s) <= kQMaxSize ->
tall aok (rok (fun s' => ainv X s')) (drain L s).
Proof.
intros AI Hg. unfold drain. cbn [q_bytes].
pose proof (transfer_inv X 0 s AI) as AI1. rewrite transfer_eq in AI1.
set (s1 := set_gq _ (set_tq q0 s)) in *.
destruct (Z.ltb_spec kQMaxSize (q_bytes (as_gq s) + q_bytes (as_tq s))) as [Hgt|Hle].
- eapply tall_mono; [apply (recycle_inv X s1 AI1)|].
intros [s'| |w]; cbn; auto. intros (AI' & T' & G'). split; [exact AI'|]. unfold qbounds. rewrite T'. subst s1. cbn.
unfold kQMaxCache, kQMinSize, kQMaxSize in *. lia.
- apply tall_rok_ret. split; [exact AI1|]. unfold qbounds. subst s1. cbn. unfold kQMaxCache. lia.
Qed.

End Rec.

Section Top.
Variable L : ALay.

Definition pshape (n : Z) (p : aptr) : Prop :=
match p with
| APrim _ m => m = n /\ from_primary n = true
| ASec a m => m = n /\ from_primary n = false /\ a mod kPage = 0 /\ 0 < a
end.

Theorem asan_malloc_inv X s n :
ainv X s -> 0 <= n -> too_big n = false ->
(from_primary n = true -> class_size (class_of n) * (tot X [] 0 s (class_of n) + 17) <= kFreeArrayOffset) ->
(from_primary n = false -> zlen (as_reg s) < kMaxNumChunks) ->
tall (aok s) (rok (fun r => let '(o, s') := r in
match o with
| None => ainv X s'
| Some p => ainv (p :: X) s' /\ ~ In p (allptrs X [] s) /\ pshape n p
end)) (asan_malloc L s n).
Proof.
intros [I QB] Hn Htb Hroom Hreg. unfold asan_malloc. rewrite Htb.
destruct (from_primary n) eqn:Hp.
-
specialize (Hroom eq_refl). set (c := class_of n) in *.
pose proof (class_of_facts n Hn Hp) as (Hc & Hum & Hneed). fold c in Hc, Hum, Hneed.
assert (Hc31 : 1 <= c <= 31) by lia.
pose proof (class_facts c Hc31) as (Hsz & Hmc & Hev).
pose proof (ai_cons _ _ _ _ I c Hc31) as Hcons. pose proof (ai_cls _ _ _ _ I c) as W.
pose proof (cw_cnt _ _ W) as Wcnt. pose proof (cw_nf _ _ W) as Wnf.
pose proof (tot_nonneg X [] 0 s c ltac:(lia)) as Htot.
assert (Hm1 : 0 <= class_size c * c_count (cls s c)) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hm2 : 0 <= class_size c * tot X [] 0 s c) by (apply Z.mul_nonneg_nonneg; lia).
unfold acc in Hcons.
eapply tall_bind_rok.
{ apply (cache_alloc_spec L (aok s)); [exact Hc31| exact W| lia| intros H0 H8; nia]. }
intros [ok s1] (Ho & W1 & Hmu & Hnf1 & Hacc). destruct ok; cbn [negb].
+ apply tall_rok_ret. pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Hr & Hnr & Ht & Hg).
split; [|split].
*
split; [|unfold qbounds in *; cbn; rewrite Ht, Hg; exact QB].
constructor; cbn [as_next as_reg as_nres as_tq as_gq set_next].
-- intros c'. rewrite cls_set_next. destruct (Z.eq_dec c' c) as [->|Hne]; [exact W1|]. rewrite (Hcl _ Hne). apply (ai_cls _ _ _ _ I).
-- intros c' Hc'. rewrite cls_set_next, tot_set_next, tot_cons_X, (tot_only_cls X [] 0 c s s1 Ho'). cbn [is_cls]. fold c.
destruct (Z.eq_dec c' c) as [->|Hne].
++ rewrite Z.eqb_refl, Hacc. unfold acc. rewrite Hcons. lia.
++ rewrite (proj2 (Z.eqb_neq c c') ltac:(congruence)), (Hcl _ Hne). rewrite (ai_cons _ _ _ _ I c' Hc'). lia.
-- rewrite Ht. apply (ai_tq _ _ _ _ I).
-- rewrite Hg. apply (ai_gq _ _ _ _ I).
-- lia.
-- rewrite allptrs_set_next, allptrs_cons_X, (allptrs_only_cls X [] c s s1 Ho'), Hnx. constructor.
++ cbn. repeat split; auto. lia.
++ eapply Forall_impl; [apply (ai_pwf _ _ _ _ I)|]. intros p Hp'. eapply pwf_mono; [|exact Hp']. lia.
-- rewrite allptrs_set_next, allptrs_cons_X, (allptrs_only_cls X [] c s s1 Ho'), Hr. cbn [secs]. apply (ai_reg _ _ _ _ I).
-- rewrite Hr. apply (ai_regw _ _ _ _ I).
-- rewrite Hr. apply (ai_regd _ _ _ _ I).
-- rewrite Hr, Hnr. apply (ai_nres _ _ _ _ I).
*
intros Hin. pose proof (ai_pwf _ _ _ _ I) as PW. rewrite List.Forall_forall in PW. specialize (PW _ Hin). cbn in PW. rewrite Hnx in PW. lia.
* cbn. auto.
+ apply tall_rok_ret. split; [eapply ainvx_frame_cls; [exact I| exact Ho| exact W1| lia]|].
destruct Ho as (_&_&_&_&Ht&Hg). unfold qbounds in *. rewrite Ht, Hg. exact QB.
-
specialize (Hreg eq_refl).
pose proof (ai_nres _ _ _ _ I) as (Hnr1 & Hnr2 & Hnr3).
eapply tall_bind_rok.
{ apply (large_alloc_spec L (aok s) (fun _ _ H => H)); [exact Hnr1| exact Hreg]. }
intros [[mb|] s1] Hpost; cbn in Hpost.
+ destruct Hpost as ((Hal & Hpos & Hav) & Ho & Hr & Hnres & Hle).
assert (Hfresh : ~ In mb (map se_beg (as_reg s))).
{ intros Hin. apply in_map_iff in Hin as (e & He & Hine).
pose proof (ai_regw _ _ _ _ I) as RW. rewrite List.Forall_forall in RW. specialize (RW _ Hine).
unfold zavoids, avoid_of in Hav. rewrite forallb_forall in Hav.
specialize (Hav (sec_iv e) ltac:(apply in_or_app; right; apply in_map; exact Hine)). cbn in Hav.
apply orb_prop in Hav as [Hav|Hav]; apply Z.leb_le in Hav.
- unfold sec_map_size, round_up, kPage in *.
pose proof (Z.div_mod (needed n + rz_size n + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (needed n + rz_size n + 4096 - 1) 4096 ltac:(lia)).
assert (0 <= needed n + rz_size n) by (unfold needed, rz_size, round_up; pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)); repeat (destruct (n <=? _)); lia).
lia.
- rewrite RW in Hav. unfold sec_map_size, round_up, kPage in Hav.
pose proof (Z.div_mod (needed (se_req e) + rz_size (se_req e) + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (needed (se_req e) + rz_size (se_req e) + 4096 - 1) 4096 ltac:(lia)).
assert (0 <= needed (se_req e) + rz_size (se_req e)) by (unfold needed, rz_size, round_up; pose proof (Z.div_mod (Z.max (se_req e) 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max (se_req e) 8 + 8 - 1) 8 ltac:(lia)); repeat (destruct (se_req e <=? _)); lia).
lia. }
eapply tall_bind_rok; [apply clear_shadow_spec|]. intros [] _.
apply tall_rok_ret. pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Ht & Hg & _).
split; [|split].
* split; [|unfold qbounds in *; rewrite Ht, Hg; exact QB].
constructor; cbn [as_next as_reg as_nres as_tq as_gq].
-- intros c'. rewrite Hcl. apply (ai_cls _ _ _ _ I).
-- intros c' Hc'. rewrite Hcl, tot_cons_X, (tot_only_sec X [] 0 s s1 Ho'). cbn [is_cls]. rewrite (ai_cons _ _ _ _ I c' Hc'). lia.
-- rewrite Ht. apply (ai_tq _ _ _ _ I).
-- rewrite Hg. apply (ai_gq _ _ _ _ I).
-- lia.
-- rewrite allptrs_cons_X, (allptrs_only_sec X [] s s1 Ho'), Hnx. constructor; [cbn; split; [lia| exact Hp]| apply (ai_pwf _ _ _ _ I)].
-- rewrite allptrs_cons_X, (allptrs_only_sec X [] s s1 Ho'), Hr, reg_pairs_app. cbn [secs reg_pairs map se_beg se_req].
etransitivity; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. apply (ai_reg _ _ _ _ I).
-- rewrite Hr. apply Forall_app. split; [apply (ai_regw _ _ _ _ I)| constructor; [reflexivity| constructor]].
-- rewrite Hr, map_app. cbn [map se_beg]. apply NoDup_app_single; [apply (ai_regd _ _ _ _ I)| exact Hfresh].
-- split; [exact Hle|]. destruct Hnres as [-> | [-> Heq]]; [split; [lia| exact Hnr3]|].
destruct Hnr3 as [k Hk]. split; [| exists (k + 1); unfold kPtrArrBlock in *; lia].
unfold kPtrArrBlock, kMaxNumChunks in *. rewrite Heq in Hk. unfold zlen in *. nia.
* intros Hin. apply Hfresh.
assert (Hs : In (mb, n) (secs (allptrs X [] s))).
{ clear -Hin. induction (allptrs X [] s) as [|[i m|a m] l IH]; cbn in *; [destruct Hin| |].
- destruct Hin as [H|H]; [discriminate| auto].
- destruct Hin as [H|H]; [injection H as -> ->; left; reflexivity| right; auto]. }
pose proof (Permutation_in _ (Permutation_sym (ai_reg _ _ _ _ I)) Hs) as Hr'.
unfold reg_pairs in Hr'. apply in_map_iff in Hr' as (e & He & Hine). apply in_map_iff. exists e. split; [|exact Hine]. injection He as H1 H2. exact H1.
* cbn. auto.
+ subst s1. apply tall_rok_ret. split; [exact I| exact QB].
Qed.

Theorem asan_free_inv X X' p s :
ainv X s -> Permutation X (p :: X') ->
class_size kBatchClass * (tot X [] 0 s kBatchClass + 17) <= kFreeArrayOffset ->
tall (aok s) (rok (fun s' => ainv X' s')) (asan_free L s p).
Proof.
intros [AI [QT QG]] HP Hroom. unfold asan_free.
assert (AI0 : ainvx X' [p] 0 s).
{ eapply ainvx_perm; [|exact AI]. rewrite app_nil_r. etransitivity; [exact HP|]. apply Permutation_cons_append. }
assert (Hroom' : sec24_room s).
{ unfold sec24_room. intros H0 H8.
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI _ H24) as Hcons. unfold acc in Hcons. rewrite H0 in Hcons.
pose proof (tot_nonneg X [] 0 s kBatchClass ltac:(lia)).
assert (0 <= class_size kBatchClass * tot X [] 0 s kBatchClass) by (apply Z.mul_nonneg_nonneg; lia).
nia. }
eapply (tall_bind_rok (aok s) (fun s1 => ainvx X' [] 0 s1 /\ as_gq s1 = as_gq s)).
{ destruct (Z.ltb_spec kQMaxSize (aptr_used p)).
- eapply tall_mono; [apply (recycle_chunk_inv L (aok s) X' p [] 0 s AI0)|].
intros [s1| |w]; cbn; auto. intros [AI1 [T1 G1]]. auto.
- eapply tall_mono; [apply (enqueue_inv L (aok s) X' p 0 s AI0 Hroom')|].
intros [s1| |w]; cbn; auto. intros (AI1 & G1 & _). auto. }
intros s1 [AI1 G1].
destruct (Z.ltb_spec kQMaxCache (q_bytes (as_tq s1))) as [Hgt|Hle].
- apply (drain_inv L (aok s) X' s1 AI1). rewrite G1. exact QG.
- apply tall_rok_ret. split; [exact AI1|]. split; [exact Hle| rewrite G1; exact QG].
Qed.

Definition kQTotal : Z := kQMaxCache + kQMaxSize.

Lemma batch_class_share c b next :
1 <= c <= 31 -> bwf 1 b -> Forall (pwf next) (b_chunks b) ->
(kBatchBytes + kBatchCount * umin c) * cntc c (b_chunks b) <= kBatchCount * b_size b.
Proof.
intros Hc (C & Lb & S) F.
assert (G : forall l, Forall (pwf next) l -> umin c * cntc c l <= zsum (map aptr_used l) /\ cntc c l <= zlen l).
{ induction l as [|q l IH]; intros Fl.
- unfold cntc, zcount, zlen. cbn. lia.
- apply Forall_cons_iff in Fl as [Wq Fl]. specialize (IH Fl). rewrite cntc_cons, zlen_cons. cbn [map]. rewrite zsum_cons.
pose proof (used_size_pos (aptr_req q)) as U. unfold aptr_used at 1.
destruct q as [i n|a n]; cbn [is_cls aptr_req] in *.
+ destruct Wq as (_ & Hn & Hp). destruct (Z.eqb_spec (class_of n) c) as [E|NE]; [|lia].
pose proof (class_of_facts n Hn Hp) as (_ & Hum & _). rewrite E in Hum. nia.
+ lia. }
destruct (G _ F) as [G1 G2]. rewrite <- C in G2.
pose proof (umin_nonneg c).
pose proof (cntc_nonneg c (b_chunks b)). unfold kBatchBytes, kBatchCount in *. nia.
Qed.

Lemma cache_class_share c q next :
1 <= c <= 31 -> qwf q -> Forall (pwf next) (qchunks q) ->
(kBatchBytes + kBatchCount * umin c) * cntc c (qchunks q) <= kBatchCount * q_bytes q.
Proof.
destruct q as [l bytes]. intros Hc [F E] P. cbn [q_list q_bytes] in F, E, P |- *. subst bytes. unfold qchunks in P |- *. cbn [q_list] in P |- *.
revert F P. induction l as [|b l IH]; intros F P.
- unfold cntc, zcount, zlen. cbn. lia.
- apply Forall_cons_iff in F as [Wb F]. cbn [flat_map] in P. apply Forall_app in P as [Pb P].
specialize (IH F P). cbn [flat_map map]. rewrite cntc_app, zsum_cons.
pose proof (batch_class_share c b next Hc Wb Pb). lia.
Qed.

Lemma not_primary_ge n : 0 <= n -> from_primary n = false -> 64513 <= n.
Proof.
intros Hn Hp. destruct (Z.leb_spec 64513 n) as [|Hlt]; [assumption|]. exfalso.
unfold from_primary, needed, kMaxSize in Hp.
assert (Hr : round_up (Z.max n 8) 8 <= 64512).
{ apply round_up_le_mul; [lia| exists 8064; reflexivity| lia]. }
assert (Hz : rz_size n <= 1024).
{ unfold rz_size. destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); lia. }
apply Z.leb_gt in Hp. lia.
Qed.

Lemma cache_sec_share q next :
qwf q -> Forall (pwf next) (qchunks q) -> 64513 * zlen (secs (qchunks q)) <= q_bytes q.
Proof.
destruct q as [l bytes]. intros [F E] P. cbn [q_list q_bytes] in F, E, P |- *. subst bytes. unfold qchunks in P |- *. cbn [q_list] in P |- *.
assert (G : forall l0, Forall (pwf next) l0 -> 64513 * zlen (secs l0) <= zsum (map aptr_used l0)).
{ induction l0 as [|q l0 IH]; intros Fl.
- unfold zlen. cbn. lia.
- apply Forall_cons_iff in Fl as [Wq Fl]. specialize (IH Fl). cbn [map]. rewrite zsum_cons.
pose proof (used_size_pos (aptr_req q)) as U. unfold aptr_used at 1.
destruct q as [i n|a n]; cbn [secs aptr_req] in *; [lia|].
rewrite zlen_cons. destruct Wq as [Hn Hp].
pose proof (not_primary_ge n Hn Hp).
unfold used_size. lia. }
revert F P. induction l as [|b l IH]; intros F P.
- unfold zlen. cbn. lia.
- apply Forall_cons_iff in F as [Wb F]. cbn [flat_map] in P. apply Forall_app in P as [Pb P].
specialize (IH F P). cbn [flat_map map]. rewrite secs_app, zlen_app, zsum_cons.
destruct Wb as (C & Lb & S). pose proof (G _ Pb). unfold kBatchBytes in *. lia.
Qed.

Lemma quarantine_share X s c :
ainv X s -> 1 <= c <= 31 ->
(kBatchBytes + kBatchCount * umin c) * (cntc c (qchunks (as_tq s)) + cntc c (qchunks (as_gq s))) <= kBatchCount * kQTotal.
Proof.
intros [AI [QT QG]] Hc.
pose proof (ai_pwf _ _ _ _ AI) as P. unfold allptrs in P. cbn [app] in P.
apply Forall_app in P as [_ P]. apply Forall_app in P as [Pt Pg].
pose proof (cache_class_share c (as_tq s) (as_next s) Hc (ai_tq _ _ _ _ AI) Pt).
pose proof (cache_class_share c (as_gq s) (as_next s) Hc (ai_gq _ _ _ _ AI) Pg).
pose proof (umin_nonneg c). unfold kQTotal, kQMaxCache, kQMaxSize, kBatchBytes, kBatchCount in *. nia.
Qed.

Definition qcap (c : Z) : Z :=
class_size c * (kBatchCount * kQTotal / (kBatchBytes + kBatchCount * umin c))
+ (if c =? kBatchClass then kQTotal else 0).

Lemma tot_bound X s c :
ainv X s -> 1 <= c <= 31 -> class_size c * (tot X [] 0 s c - cntc c X) <= qcap c.
Proof.
intros AI Hc. pose proof (quarantine_share X s c AI Hc) as Q. destruct AI as [AI [QT QG]].
pose proof (class_facts c Hc) as (Hsz & _ & _). pose proof (umin_nonneg c) as Hu.
unfold tot, allptrs, qcap. cbn [app]. repeat rewrite cntc_app.
set (k := cntc c (qchunks (as_tq s)) + cntc c (qchunks (as_gq s))) in *.
assert (Hk : k <= kBatchCount * kQTotal / (kBatchBytes + kBatchCount * umin c)).
{ apply Z.div_le_lower_bound; [unfold kBatchBytes, kBatchCount; lia| lia]. }
assert (Hm : class_size c * k <= class_size c * (kBatchCount * kQTotal / (kBatchBytes + kBatchCount * umin c))).
{ apply Z.mul_le_mono_nonneg_l; lia. }
destruct (Z.eqb_spec c kBatchClass) as [->|Hne].
- pose proof (qwf_bytes_ge _ (ai_tq _ _ _ _ AI)). pose proof (qwf_bytes_ge _ (ai_gq _ _ _ _ AI)).
replace (class_size kBatchClass) with kBatchBytes in * by reflexivity.
unfold kQTotal in *. lia.
- lia.
Qed.

Lemma reg_bound X s :
ainv X s -> 64513 * (zlen (as_reg s) - zlen (secs X)) <= kQTotal.
Proof.
intros [AI [QT QG]].
pose proof (ai_pwf _ _ _ _ AI) as P. unfold allptrs in P. cbn [app] in P.
apply Forall_app in P as [_ P]. apply Forall_app in P as [Pt Pg].
pose proof (cache_sec_share (as_tq s) (as_next s) (ai_tq _ _ _ _ AI) Pt).
pose proof (cache_sec_share (as_gq s) (as_next s) (ai_gq _ _ _ _ AI) Pg).
pose proof (Permutation_length (ai_reg _ _ _ _ AI)) as Hl. unfold reg_pairs in Hl. rewrite length_map in Hl.
unfold allptrs in Hl. cbn [app] in Hl. rewrite !secs_app, !length_app in Hl.
unfold zlen, kQTotal in *. lia.
Qed.

End Top.

Section Shapes.
Variable L : ALay.

End Shapes.

Section AllOk.
Variable L : ALay.

Fixpoint allok {R} (P : R -> Prop) (t : T R) : Prop :=
match t with
| SRet (ROk r) => P r
| SRet RSpin => False
| SRet (RUnr _) => True
| SVis e k => forall a, allok P (k (AOk a))
end.

Lemma allok_bind {R S} (P : S -> Prop) (t : T R) (f : R -> T S) :
allok (fun x => allok P (f x)) t -> allok P (tbind t f).
Proof. unfold tbind. induction t as [[x| |w]|e k IH]; cbn; auto. Qed.

End AllOk.

Lemma tall_conj {R} (aok : evA -> ansA -> Prop) (P Q : R -> Prop) (t : T R) :
tall aok (rok P) t -> tall aok (rok Q) t -> tall aok (rok (fun x => P x /\ Q x)) t.
Proof.
induction t as [[x| |w]|e k IH]; cbn; intros HP HQ; auto.
Qed.

Section ClsFrame.
Variable L : ALay.
Variable aok : evA -> ansA -> Prop.
Hypothesis aok_fixed : forall a l, aok (EvMapFixed a l) AErr -> False.

Definition cfr (s s' : AState) : Prop :=
forall c, c <> kBatchClass -> cls s c = cst0 -> cls s' c = cst0.

End ClsFrame.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs Qc6I QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf.
Import ListNotations.
Import Qc6I.Exc.

Section Monad.
Context {St : Type}.

Definition M (A : Type) : Type := St -> itree node (exc (A * St)).

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : M St := fun s => Ret (Ok (s, s)).
Definition mput (s : St) : M unit := fun _ => Ret (Ok (tt, s)).
Definition mupd (f : St -> St) : M unit := fun s => Ret (Ok (tt, f s)).
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).
Definition mwhen (b : bool) (m : M unit) : M unit := if b then m else mret tt.
Definition massert (b : bool) : M unit := if b then mret tt else munr.

Fixpoint mloop {X R} (fuel : nat) (body : X -> M (X + R)) (x : X) : M R :=
match fuel with
| O => munr
| S fuel' => mbind (body x) (fun s => match s with
| inl x' => mloop fuel' body x'
| inr r => mret r
end)
end.

Lemma mbind_mret : forall {A B} (a : A) (f : A -> M B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.

Section Machine.
Variable segs : list Segment.

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implM_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implM, mret. apply impl_ret_ok. exact H. Qed.

Lemma implM_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implM munr s Q ms.
Proof. intros. unfold implM, munr. apply impl_ret_unr. Qed.

Lemma implM_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
implM m s Q1 ms ->
(forall a s' ms', Q1 a s' ms' -> implM (f a) s' Q ms') ->
implM (mbind m f) s Q ms.
Proof.
intros A B m f s Q1 Q ms Hm Hf. unfold implM, mbind in *.
eapply impl_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implM_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
implM m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implM m s Q' ms.
Proof.
intros A m s Q Q' ms H HQ. unfold implM in *. eapply impl_epost_mono; [exact H|].
intros [a s'] ms'; cbn; auto.
Qed.

Lemma implM_sys : forall {A} n (dec : resp -> option A) s Q ms,
evt segs (fun ms1 => at_node segs n ms1 /\
forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms ->
implM (msys n dec) s Q ms.
Proof.
intros A n dec s Q ms H. unfold implM, msys. apply impl_enode.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp [a s'] E. cbn. specialize (Hk rsp).
destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. apply Hk. reflexivity.
Qed.

Lemma implM_put : forall s s' Q ms, evt segs (Q tt s') ms -> implM (mput s') s Q ms.
Proof. intros. unfold implM, mput. apply impl_ret_ok. exact H. Qed.
Lemma implM_upd : forall f s Q ms, evt segs (Q tt (f s)) ms -> implM (mupd f) s Q ms.
Proof. intros. unfold implM, mupd. apply impl_ret_ok. exact H. Qed.

Lemma implM_evt : forall {A} (c : M A) s Q P ms,
evt segs P ms -> (forall ms', P ms' -> implM c s Q ms') -> implM c s Q ms.
Proof. intros A c s Q P ms H K. unfold implM in *. eapply impl_evt; eauto. Qed.

Lemma implM_loop_S : forall {X R} fuel (body : X -> M (X + R)) x s Q ms,
implM (body x) s (fun r s' ms' => match r with
| inl x' => implM (mloop fuel body x') s' Q ms'
| inr v => evt segs (Q v s') ms'
end) ms ->
implM (mloop (S fuel) body x) s Q ms.
Proof.
intros X R fuel body x s Q ms H. cbn [mloop]. eapply implM_bind; [exact H|].
intros [x'|v] s' ms' H'; cbn in H'.
- exact H'.
- apply implM_ret. exact H'.
Qed.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
End Mq1.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP.
Local Set Keyed Unification.

Import ListNotations.
Local Open Scope Z_scope.

Definition inT (rid : N) (lo hi : Z) (q : aptr) : Prop := fst q = rid /\ lo <= snd q < hi.

Section WRITE_T.
Variables (X : extras) (st st' : mstate) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Hypothesis ISH : inv_SH st BL.
Variables (m bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Hypothesis NH : s_groups st !! (fst bm, sstart (MR st m) i) = None.
Hypothesis NB : forall k, In k BL -> bslot k <> (fst bm, sstart (MR st m) i).
Let lo := sstart (MR st m) i - 3.
Let hi := sstart (MR st m) (i + 1) - 4.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall q, ~ inT (fst bm) lo hi q ->
cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
(forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

End WRITE_T.

Section REMOVE_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (k : blk).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Let X' := mkX (x_idle X) (x_zomb X) (Some (bslot k)) (x_orph X) (x_fresh X).
Let BL' := bl_remove (bslot k) BL.

Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! (bslot k) = Some (m, i) ->
forall q, ~ inT (fst (bslot k)) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
(forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

End REMOVE_BLOCK.

Definition blk_shadow_ok (st : mstate) (k : blk) (m : aptr) (i : Z) : Prop :=
let rid := fst (bslot k) in
let p := snd (bslot k) + UNIT * boff k in
let e := snd (bslot k) + get_stride (MR st m) - IB in
let res := e - p - bsize k in
let q := (p - snd (gbase (MR st m)) - UNIT) / UNIT in
known st (rid, p - 4) 0
/\ known st (rid, p - 3) (i + 32 * Z.min res 5)
/\ known st (rid, p - 2) (byte_of q 0) /\ known st (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
/\ (5 <= res -> known st (rid, e - 4) (byte_of res 0) /\ known st (rid, e - 3) (byte_of res 1)
/\ known st (rid, e - 2) (byte_of res 2) /\ known st (rid, e - 1) (byte_of res 3)
/\ known st (rid, e - 5) 0 /\ res < 2^32)
/\ (0 < res -> known st (rid, e - res) 0)
/\ (forall a, p <= a < p + bsize k -> unknown st (rid, a)).

Section ADD_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Let k : blk := ((c, off), n).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Let X' := mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X).
Let BL' := k :: BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! c = Some (m, i) ->
forall q, ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
(forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).
Hypothesis BLK : forall m i, s_slots st !! c = Some (m, i) ->
0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB /\ blk_shadow_ok st' k m i.

End ADD_BLOCK.

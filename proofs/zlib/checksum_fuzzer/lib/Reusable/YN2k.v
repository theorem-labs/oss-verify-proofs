(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x
YO0z YO11 YO15 YO0u YO12 YO10 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN2h.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ibind_assoc {S X Y W} : forall (t : itree S X) (f : X -> itree S Y) (g : Y -> itree S W),
ibind (ibind t f) g = ibind t (fun x => ibind (f x) g).
Proof.
induction t as [x | q s k IH | e]; intros f g; cbn; try reflexivity.
f_equal. apply functional_extensionality. intros z. apply IH.
Qed.
Lemma ibind_ret {S X} : forall (t : itree S (X * S)), ibind t (fun '(a, s') => IRet (a, s')) = t.
Proof.
induction t as [[a s] | q s k IH | e]; cbn; try reflexivity.
f_equal. apply functional_extensionality. intros z. apply IH.
Qed.
Lemma ibind_ext {S X Y} : forall (t : itree S X) (f g : X -> itree S Y), (forall x, f x = g x) -> ibind t f = ibind t g.
Proof. intros t f g H. f_equal. apply functional_extensionality. exact H. Qed.
Definition take_st (s : astate) : astate :=
upd_meta (st_avail_meta s) MRaw (set_avail_meta (padd (st_avail_meta s) META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)).
Definition am_area : M bool :=
nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false.
Definition am_after_area (r : bool * astate) : itree astate (option sptr * astate) :=
let '(ok, s1) := r in
(if negb ok then (fun s0 : astate => IRet (None, s0)) else (fun s0 : astate => IRet (Some (st_avail_meta s0), take_st s0))) s1.
Lemma alloc_meta_tree : forall A,
alloc_meta A =
match st_free_meta_head A with
| Some m => ibind (dequeue HFreeMeta m (set_init_done true A)) (fun r => IRet (Some m, snd r))
| None => if 0 <? st_avail_meta_count A then IRet (Some (st_avail_meta A), take_st (set_init_done true A))
else ibind (am_area (set_init_done true A)) am_after_area
end.
Proof.
intros A. unfold alloc_meta, dequeue_head, get_head, bind, modify, get, ret. cbn [ibind st_free_meta_head set_init_done st_avail_meta_count st_avail_meta].
destruct (st_free_meta_head A) as [m|].
- rewrite ibind_assoc. apply ibind_ext. intros [[] s']. reflexivity.
- cbn [ibind]. change (st_avail_meta_count (set_init_done true A)) with (st_avail_meta_count A).
destruct (0 <? st_avail_meta_count A); [reflexivity|].
unfold am_area, bind. rewrite !ibind_assoc. apply ibind_ext. intros [nu s1].
rewrite !ibind_assoc. apply ibind_ext. intros [rs s2]. destruct rs; [|reflexivity].
apply ibind_ext. intros [ok s3]. reflexivity.
Qed.
Definition openR_st (s : astate) : astate :=
let p := st_avail_meta_areas s in
open_st p (set_regions (lupd (st_regions s) (prid p)
(let rg := nth (prid p) (st_regions s) (mkRegion RkMap 0 [] false) in
mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff p]) (rg_live rg))) s).
Definition resv_st (s : astate) : astate :=
let n := Z.shiftl 2 (st_meta_alloc_shift s) in
set_meta_alloc_shift (st_meta_alloc_shift s + 1)
(set_avail_meta_area_count (n - 1)
(set_avail_meta_areas (SP (length (st_regions s)) PGSZ)
(set_regions (st_regions s ++ [mkRegion RkMetaRes (n * PGSZ) [] true]) s))).
Definition brk2_st (s : astate) : astate :=
set_avail_meta_area_count 1
(set_avail_meta_areas (SP (length (st_regions s)) PGSZ)
(set_brk (BrkCur (length (st_regions s)) 2)
(set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s))).
Definition brk1_st (r : nat) (pages : Z) (s : astate) : astate :=
set_avail_meta_area_count 1
(set_avail_meta_areas (SP r (PGSZ * pages))
(set_brk (BrkCur r (pages + 1))
(set_regions (lupd (st_regions s) r
(mkRegion RkBrk (rg_len (nth r (st_regions s) (mkRegion RkMap 0 [] false)) + PGSZ) [] true)) s))).
Lemma am_area_R : forall s, st_avail_meta_area_count s <> 0 ->
exists k, am_area s = IAsk (KMprotect (st_avail_meta_areas s)) s k /\
forall z, k z = if z =? 0 then IRet (false, s) else IRet (true, openR_st s).
Proof.
intros s Hc. assert (Heq : (st_avail_meta_area_count s =? 0) = false) by (apply Z.eqb_neq; exact Hc).
unfold am_area, area_from_brk, area_from_mmap, open_area, bind, get, ret, ask, modify, upd_region. cbn [ibind].
rewrite !Heq. cbn [andb ibind negb]. rewrite !Heq. cbn [ibind].
eexists. split; [reflexivity|]. intros z. cbn [ibind]. destruct (z =? 0); reflexivity.
Qed.
Lemma am_resv_tree : forall s, st_avail_meta_area_count s = 0 ->
exists k, (rs <- area_from_mmap ;; if rs then open_area true else ret false) s
= IAsk (KMmapNone (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ)) s k /\
k 0 = IRet (false, s) /\
forall z, z <> 0 -> exists k2, k z = IAsk (KMprotect (SP (length (st_regions s)) PGSZ)) (resv_st s) k2 /\
forall z2, k2 z2 = if z2 =? 0 then IRet (false, resv_st s) else IRet (true, openR_st (resv_st s)).
Proof.
intros s Hc. unfold area_from_mmap, open_area, new_region, bind, get, put, ret, ask, modify, upd_region. cbn [ibind].
rewrite Hc. cbn [Z.eqb ibind].
eexists. split; [reflexivity|]. split; [reflexivity|].
intros z Hz. rewrite (proj2 (Z.eqb_neq _ _) Hz). cbn [negb ibind].
eexists. split; [reflexivity|]. intros z2. cbn beta. destruct (z2 =? 0); reflexivity.
Qed.
Lemma am_area_BD : forall s, st_avail_meta_area_count s = 0 -> st_brk s = BrkDead ->
am_area s = (rs <- area_from_mmap ;; if rs then open_area true else ret false) s.
Proof.
intros s Hc Hb. unfold am_area. unfold bind at 1. unfold area_from_brk. unfold bind at 1. unfold get, ret. cbn [ibind]. rewrite Hc, Hb. reflexivity.
Qed.
Lemma am_area_BN : forall s, st_avail_meta_area_count s = 0 -> st_brk s = BrkNever ->
exists k0, am_area s = IAsk KBrkQuery s k0 /\ forall z0, exists k1, k0 z0 = IAsk (KBrkGrow 2) s k1 /\
k1 0 = (rs <- area_from_mmap ;; if rs then open_area true else ret false) (set_brk BrkDead s) /\
forall z1, z1 <> 0 -> exists k3, k1 z1 = IAsk KGuard (brk2_st s) k3 /\
forall z3, k3 z3 = IRet (true, open_st (SP (length (st_regions s)) PGSZ) (brk2_st s)).
Proof.
intros s Hc Hb. unfold am_area. unfold bind at 1. unfold area_from_brk, new_region, bind, get, put, ret, ask, modify. cbn [ibind].
rewrite Hc, Hb. cbn [andb ibind].
eexists. split; [reflexivity|]. intros z0. cbn beta. eexists. split; [reflexivity|]. split.
- cbn [Z.eqb negb ibind]. reflexivity.
- intros z1 Hz1. cbn beta. rewrite (proj2 (Z.eqb_neq _ _) Hz1). cbn [negb ibind].
eexists. split; [reflexivity|]. intros z3. cbn beta.
unfold area_from_mmap, open_area, bind, get, ret, modify. cbn. reflexivity.
Qed.
Lemma am_area_BC : forall s r pages, st_avail_meta_area_count s = 0 -> st_brk s = BrkCur r pages ->
exists k1, am_area s = IAsk (KBrkGrow 1) s k1 /\
k1 0 = (rs <- area_from_mmap ;; if rs then open_area true else ret false) (set_brk BrkDead s) /\
forall z1, z1 <> 0 -> k1 z1 = IRet (true, open_st (SP r (PGSZ * pages)) (brk1_st r pages s)).
Proof.
intros s r pages Hc Hb. unfold am_area. unfold bind at 1. unfold area_from_brk, upd_region, bind, get, put, ret, ask, modify. cbn [ibind].
rewrite Hc, Hb. cbn [andb ibind].
eexists. split; [reflexivity|]. split.
- cbn [Z.eqb negb ibind]. reflexivity.
- intros z1 Hz1. cbn beta. rewrite (proj2 (Z.eqb_neq _ _) Hz1). cbn [negb ibind].
unfold area_from_mmap, open_area, bind, get, ret, modify. cbn. reflexivity.
Qed.
Definition pure {S X} (t : itree S X) : Prop := match t with IAsk _ _ _ => False | _ => True end.
Lemma pure_ibind {S X Y} : forall (t : itree S X) (k : X -> itree S Y), pure t -> (forall x, pure (k x)) -> pure (ibind t k).
Proof. intros [x|q s c|e] k Ht Hk; cbn in *; [apply Hk | destruct Ht | exact I]. Qed.
Lemma itok_pure {X} : forall (t : itree astate X) (Q : X -> Prop), pure t -> itok t Q -> exists r, t = IRet r /\ Q r.
Proof. intros [x|q s c|e] Q Hp Ht; cbn in *; [exists x; auto | destruct Hp | destruct Ht]. Qed.
Lemma pure_get_links : forall p s, pure (get_links p s).
Proof. intros p s. unfold get_links, bind, get, ret, fail. cbn. destruct (mlookup (st_metas s) p); exact I. Qed.
Lemma pure_set_links : forall p a b s, pure (set_links p a b s).
Proof. intros p a b s. unfold set_links, bind, get, ret, fail, setslot, modify. cbn. destruct (mlookup (st_metas s) p); exact I. Qed.
Lemma pure_dequeue : forall h m s, pure (dequeue h m s).
Proof.
intros h m s. unfold dequeue, bind. apply pure_ibind; [apply pure_get_links|]. intros [l s1].
apply pure_ibind; [| intros [u s2]; apply pure_set_links].
destruct (osptr_eqb (snd l) (Some m)).
- unfold set_head, modify. destruct h; exact I.
- destruct (fst l) as [pr|], (snd l) as [nx|]; try exact I.
unfold set_next, set_prev, bind. apply pure_ibind; [apply pure_ibind; [apply pure_get_links | intros [l2 s3]; apply pure_set_links]|].
intros [u s3]. apply pure_ibind; [apply pure_ibind; [apply pure_get_links | intros [l2 s4]; apply pure_set_links]|].
intros [u2 s4]. apply pure_ibind; [unfold get_head, bind, get, ret; cbn; destruct h; exact I|].
intros [hd s5]. destruct (osptr_eqb hd (Some m)); [unfold set_head, modify; destruct h; exact I | exact I].
Qed.
Section i.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (m : sptr).
Hypothesis HI : Inv X R U s.
Hypothesis Hhd : st_free_meta_head s = Some m.
Lemma free_ring : exists rest, ring_ok (flinks X s) (Some m) (m :: rest) /\
(forall g pr nx, MTX X s g = Some (MFree pr nx) -> In g (m :: rest)).
Proof.
destruct (inv_rings HI) as ((ms & Rg & Mem) & _). rewrite Hhd in Rg.
destruct (ring_head_In _ _ _ Rg) as [_ (rest & ->)]. exists rest. auto.
Qed.
Definition deq_post (rest : list sptr) (x : mslot) (r : unit * astate) : Prop :=
let s1 := snd r in
same_but_metas_heads s s1 /\
st_free_meta_head s1 = (match rest with [] => None | y :: _ => Some y end) /\
st_active s1 = st_active s /\
MT s1 m = Some (with_links x None None) /\
(forall q, ~ In q (m :: rest) -> MT s1 q = MT s q) /\
(forall y xy, In y rest -> MT s y = Some xy ->
MT s1 y = Some (with_links xy (if sptr_eqb y (hd m rest) then Some (last rest m) else fst (links_of xy))
(if sptr_eqb y (last rest m) then Some (hd m rest) else snd (links_of xy)))).
Theorem deq_shape : exists rest s1,
let pr := last rest m in let nx := hd m rest in
ring_ok (flinks X s) (Some m) (m :: rest) /\
MT s m = Some (MFree (Some pr) (Some nx)) /\
(forall q, In q (m :: rest) -> exists qp qn, MT s q = Some (MFree qp qn) /\ memb q X = false) /\
dequeue HFreeMeta m s = IRet (tt, s1) /\
deq_post rest (MFree (Some pr) (Some nx)) (tt, s1).
Proof.
destruct free_ring as (rest & Rg & Mem). exists rest.
destruct Rg as [Cyc Hh]. pose proof Cyc as [ND Ch]. cbn [hd_error] in Hh.
assert (MEMS : forall q, In q (m :: rest) -> exists qp qn, MT s q = Some (MFree qp qn) /\ memb q X = false).
{ intros q Hq. destruct (fring_members_free X s (Some m) (m :: rest) q (conj Cyc Hh) Hq) as (qp & qn & Mq & Eq). exists qp, qn. auto. }
assert (LKs : forall q l, In q (m :: rest) -> flinks X s q = Some l -> LK s q = Some l).
{ intros q l Hq Hl. destruct (flinks_free _ _ _ _ Hl) as (qp & qn & _ & Mq & ->). unfold LK. rewrite Mq. reflexivity. }
assert (Lm : flinks X s m = Some (Some (last rest m), Some (hd m rest))).
{ cbn [chain] in Ch. destruct Ch as [Hm _]. rewrite last_cons in Hm. exact Hm. }
destruct (flinks_free _ _ _ _ Lm) as (mp & mn & _ & Mm & Emn). injection Emn as <- <-.
assert (OP : itok (dequeue HFreeMeta m s) (deq_post rest (MFree (Some (last rest m)) (Some (hd m rest))))).
{ apply (dequeue_op HFreeMeta m s _ rest (flinks X s) _ Mm Cyc LKs I).
intros s' S1 S2 S3 S4 S5 S6. unfold deq_post. cbn [snd].
split; [exact S1|]. split.
- unfold head_of in S3. rewrite S3, Hhd. destruct rest; [reflexivity|]. cbn. rewrite sptr_eqb_refl. reflexivity.
- split; [| split; [exact S4 | split; [exact S5 | exact S6]]].
destruct S2 as (A1 & _ & A3). apply (nth_ext _ _ None None A3). intros n _. apply A1. intros sc H; discriminate. }
destruct (itok_pure _ _ (pure_dequeue HFreeMeta m s) OP) as ([[] s1] & Edq & P).
exists s1. cbn zeta. split; [exact (conj Cyc Hh)|]. split; [exact Mm|]. split; [exact MEMS|]. split; [exact Edq | exact P].
Qed.
End i.
End d.

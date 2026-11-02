(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2w.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition KS (r : option sptr * astate) : itree astate (Z * astate) :=
match fst r with None => IRet (-1, snd r) | Some _ => IRet (0, snd r) end.
Definition after_try (fuel : nat) (sc req : Z) (r : Z * astate) : itree astate (Z * astate) :=
if negb (fst r =? 0) then IRet (ctz32 (fst r), snd r) else ibind (alloc_group fuel sc req (snd r)) KS.
Lemma alloc_slot_tree : forall fuel sc req s,
alloc_slot (S fuel) sc req s = ibind (try_avail sc s) (after_try fuel sc req).
Proof.
intros fuel sc req s. cbn [alloc_slot]. unfold bind, ret. apply ibind_ext. intros [first s1]. unfold after_try. cbn [fst snd].
destruct (negb (first =? 0)); [reflexivity|]. apply ibind_ext. intros [[g|] s2]; reflexivity.
Qed.
Definition group_body (fuel : nat) (sc req : Z) (m : sptr) : M (option sptr) :=
fun s =>
let size := class_size sc in
let usage := usage_of s sc in
let cnt0 := initial_cnt sc usage in
if PGSZ / 2 <? size * cnt0 + UNIT then
(account_bounce sc ;;
step_seq ;;
ok <- ask (KMmapRW (snd (mmap_plan s sc req cnt0 usage))) ;;
if negb ok then free_meta m ;; ret None
else
r <- new_region RkMap (page_round (snd (mmap_plan s sc req cnt0 usage))) ;;
s0 <- get ;;
put (set_mmap_counter (Z.land (st_mmap_counter s0 + 1) (2^32 - 1)) s0) ;;
let cnt := fst (mmap_plan s sc req cnt0 usage) in
let a0 := (4096 - UNIT) / size - 1 in
let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
let aidx := if a1 <? 0 then 0 else a1 in
install_group m sc cnt aidx (snd (mmap_plan s sc req cnt0 usage) / 4096) (SP r 0) slot_zero ;;
ret (Some m)) s
else
(let total := UNIT + cnt0 * size - IB in
let j := size_to_class total in
idx <- alloc_slot fuel j total ;;
if idx <? 0 then free_meta m ;; ret None
else
hj <- get_head (HActive j) ;;
match hj with
| None => fail (FModel 8)
| Some g =>
amg <- getm g ;;
mcheck (stride_of amg =? class_size j) 11 ;;
s1 <- get ;;
p <- enframe g idx (class_size j - IB) (st_mmap_counter s1) FGroup ;;
install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
ret (Some m)
end) s.
Definition mm_body (sc req : Z) (m : sptr) (s : astate) : itree astate (option sptr * astate) :=
let size := class_size sc in
let usage := usage_of s sc in
let cnt0 := initial_cnt sc usage in
(account_bounce sc ;;
step_seq ;;
ok <- ask (KMmapRW (snd (mmap_plan s sc req cnt0 usage))) ;;
if negb ok then free_meta m ;; ret None
else
r <- new_region RkMap (page_round (snd (mmap_plan s sc req cnt0 usage))) ;;
s0 <- get ;;
put (set_mmap_counter (Z.land (st_mmap_counter s0 + 1) (2^32 - 1)) s0) ;;
let cnt := fst (mmap_plan s sc req cnt0 usage) in
let a0 := (4096 - UNIT) / size - 1 in
let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
let aidx := if a1 <? 0 then 0 else a1 in
install_group m sc cnt aidx (snd (mmap_plan s sc req cnt0 usage) / 4096) (SP r 0) slot_zero ;;
ret (Some m)) s.
Definition nest_body (fuel : nat) (sc req : Z) (m : sptr) (s : astate) : itree astate (option sptr * astate) :=
let size := class_size sc in
let usage := usage_of s sc in
let cnt0 := initial_cnt sc usage in
(let total := UNIT + cnt0 * size - IB in
let j := size_to_class total in
idx <- alloc_slot fuel j total ;;
if idx <? 0 then free_meta m ;; ret None
else
hj <- get_head (HActive j) ;;
match hj with
| None => fail (FModel 8)
| Some g =>
amg <- getm g ;;
mcheck (stride_of amg =? class_size j) 11 ;;
s1 <- get ;;
p <- enframe g idx (class_size j - IB) (st_mmap_counter s1) FGroup ;;
install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
ret (Some m)
end) s.
Lemma group_body_arms : forall fuel sc req m s,
group_body fuel sc req m s =
if PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s sc) + UNIT then mm_body sc req m s else nest_body fuel sc req m s.
Proof. reflexivity. Qed.
Definition KG (fuel : nat) (sc req : Z) (r : option sptr * astate) : itree astate (option sptr * astate) :=
match fst r with None => IRet (None, snd r) | Some m => group_body fuel sc req m (snd r) end.
Lemma alloc_group_tree : forall fuel sc req s,
alloc_group (S fuel) sc req s = ibind (alloc_meta s) (KG fuel sc req).
Proof.
intros fuel sc req s. cbn [alloc_group]. unfold bind at 1. apply ibind_ext. intros [[m|] s1]; [| reflexivity].
unfold KG, group_body. cbn [fst snd]. unfold bind at 1. unfold get. cbn [ibind].
destruct (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT); reflexivity.
Qed.
Lemma try_avail_none : forall sc s, active_hd s sc = None -> try_avail sc s = IRet (0, s).
Proof.
intros sc s H. unfold try_avail. unfold bind at 1. unfold get_head, bind, get, ret. cbn [ibind].
unfold active_hd in H. rewrite H. reflexivity.
Qed.
Lemma try_avail_fast : forall sc s m am, active_hd s sc = Some m -> MT s m = Some (MUsed am) -> am_avail am <> 0 ->
try_avail sc s = IRet (lowbit (am_avail am), set_metas (mupdate (st_metas s) m (MUsed (am_set_avail (am_avail am - lowbit (am_avail am)) am))) s).
Proof.
intros sc s m am Hhd Hm Hav. unfold try_avail. unfold bind at 1. unfold get_head, bind, get, ret. cbn [ibind].
unfold active_hd in Hhd. rewrite Hhd. cbn [ibind]. unfold getm. unfold bind at 1. unfold get. cbn [ibind]. unfold MT in Hm. rewrite Hm.
unfold ret. cbn [ibind]. rewrite (proj2 (Z.eqb_neq _ _) Hav). cbn [negb]. unfold bind, setm, modify. cbn [ibind]. reflexivity.
Qed.
Fixpoint iall {A : Type} (t : itree astate A) (P : A -> Prop) : Prop :=
match t with
| IRet a => P a
| IFail _ => True
| IAsk _ _ k => forall z, iall (k z) P
end.
Lemma itok_iall {A} : forall (t : itree astate A) (Q : A -> Prop) (P : A -> Prop),
itok t Q -> iall t P -> itok t (fun a => Q a /\ P a).
Proof.
induction t as [a | q s k IH | e]; intros Q P HQ HP; cbn in *; [auto | | exact HQ].
destruct HQ as [R K]. split; [exact R|]. intros z Hz. apply IH; [apply K; exact Hz | apply HP].
Qed.
Lemma iall_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) (P : A -> Prop) (Q : R -> Prop),
iall t P -> (forall a, P a -> iall (f a) Q) -> iall (ibind t f) Q.
Proof.
induction t as [a | q s k IH | e]; intros f P Q HP Hf; cbn in *; [apply Hf; exact HP | | exact I].
intros z. apply (IH z f P Q (HP z) Hf).
Qed.
Lemma iall_mono {A} : forall (t : itree astate A) (P P' : A -> Prop), (forall a, P a -> P' a) -> iall t P -> iall t P'.
Proof. induction t as [a | q s k IH | e]; intros P P' H HP; cbn in *; auto. intros z. apply (IH z P P' H (HP z)). Qed.
Lemma iall_conj {A} : forall (t : itree astate A) (P P' : A -> Prop), iall t P -> iall t P' -> iall t (fun a => P a /\ P' a).
Proof. induction t as [a | q s k IH | e]; intros P P' H H'; cbn in *; [exact (conj H H') | | exact I]. intros z. apply (IH z P P' (H z) (H' z)). Qed.
Lemma metas_openR : forall s, st_metas (openR_st s) = st_metas s. Proof. reflexivity. Qed.
Lemma metas_resv : forall s, st_metas (resv_st s) = st_metas s. Proof. reflexivity. Qed.
Lemma metas_brk2 : forall s, st_metas (brk2_st s) = st_metas s. Proof. reflexivity. Qed.
Lemma metas_brk1 : forall r p s, st_metas (brk1_st r p s) = st_metas s. Proof. reflexivity. Qed.
Lemma metas_open : forall p s, st_metas (open_st p s) = st_metas s. Proof. reflexivity. Qed.
Lemma metas_dead : forall s, st_metas (set_brk BrkDead s) = st_metas s. Proof. reflexivity. Qed.
Lemma MT_take : forall s q, MT (take_st s) q = if sptr_eqb q (st_avail_meta s) then Some MRaw else MT s q.
Proof. intros s q. unfold take_st. rewrite MT_upd. reflexivity. Qed.
Definition raw_stable (P : astate -> Prop) : Prop :=
(forall s s', st_metas s' = st_metas s -> P s -> P s') /\ (forall s, P s -> P (take_st s)).
Lemma am_area_iall : forall s P, raw_stable P -> P s -> iall (ibind (am_area s) am_after_area) (fun r => P (snd r)).
Proof.
intros s P [PM PT] Ps.
assert (AFTER : forall ok s1, P s1 -> iall (am_after_area (ok, s1)) (fun r => P (snd r))).
{ intros ok s1 P1. unfold am_after_area. destruct ok; cbn; [apply PT; exact P1 | exact P1]. }
assert (RESV : forall s0, P s0 -> iall (ibind ((rs <- area_from_mmap ;; if rs then open_area true else ret false) s0) am_after_area) (fun r => P (snd r)) \/ st_avail_meta_area_count s0 <> 0).
{ intros s0 P0. destruct (Z.eq_dec (st_avail_meta_area_count s0) 0) as [E0|NE]; [left | right; exact NE].
destruct (am_resv_tree s0 E0) as (k & Ek & Hk0 & Hk1). rewrite Ek. cbn. intros z.
destruct (Z.eq_dec z 0) as [->|Hz]; [rewrite Hk0; cbn; exact P0|].
destruct (Hk1 z Hz) as (k2 & Ek2 & Hk2). rewrite Ek2. cbn. intros z2. rewrite Hk2.
destruct (z2 =? 0); cbn; [apply (PM s0); [apply metas_resv | exact P0] | apply PT; apply (PM s0); [reflexivity | exact P0]]. }
destruct (Z.eq_dec (st_avail_meta_area_count s) 0) as [E0|NE].
- destruct (st_brk s) as [| |r pg] eqn:Eb.
+ destruct (am_area_BN s E0 Eb) as (k0 & Ek0 & Hk0). rewrite Ek0. cbn. intros z0.
destruct (Hk0 z0) as (k1 & Ek1 & Hk10 & Hk11). rewrite Ek1. cbn. intros z1.
destruct (Z.eq_dec z1 0) as [->|Hz1].
* rewrite Hk10. destruct (RESV (set_brk BrkDead s) ltac:(apply (PM s); [reflexivity | exact Ps])) as [H|H]; [exact H | exfalso; apply H; exact E0].
* destruct (Hk11 z1 Hz1) as (k3 & Ek3 & Hk3). rewrite Ek3. cbn. intros z3. rewrite Hk3. cbn. apply PT. apply (PM s); [reflexivity | exact Ps].
+ rewrite (am_area_BD s E0 Eb). destruct (RESV s Ps) as [H|H]; [exact H | exfalso; apply H; exact E0].
+ destruct (am_area_BC s r pg E0 Eb) as (k1 & Ek1 & Hk10 & Hk11). rewrite Ek1. cbn. intros z1.
destruct (Z.eq_dec z1 0) as [->|Hz1].
* rewrite Hk10. destruct (RESV (set_brk BrkDead s) ltac:(apply (PM s); [reflexivity | exact Ps])) as [H|H]; [exact H | exfalso; apply H; exact E0].
* rewrite (Hk11 z1 Hz1). cbn. apply PT. apply (PM s); [reflexivity | exact Ps].
- destruct (am_area_R s NE) as (k & Ek & Hk). rewrite Ek. cbn. intros z. rewrite Hk. destruct (z =? 0); cbn; [exact Ps | apply PT; apply (PM s); [reflexivity | exact Ps]].
Qed.
Definition as_budget (sc : Z) : Z := 384 + 144 * (24 - Z.min sc 24).
Lemma as_budget_range : forall sc, 0 <= sc -> 384 <= as_budget sc <= 3840.
Proof. intros sc Hsc. unfold as_budget. pose proof (Z.le_min_l sc 24). pose proof (Z.le_min_r sc 24). destruct (Z.min_spec sc 24) as [[_ E]|[_ E]]; rewrite E in *; lia. Qed.
Lemma as_budget_step : forall sc j, sc <= 23 -> sc < j -> as_budget j + 144 <= as_budget sc.
Proof.
intros sc j H1 H2. unfold as_budget. rewrite (Z.min_l sc 24) by lia.
destruct (Z.min_spec j 24) as [[_ E]|[_ E]]; rewrite E; lia.
Qed.
Definition rawX (X : list sptr) (s : astate) : Prop := forall x, In x X -> MT s x = Some MRaw \/ MT s x = Some (MFree None None).
Lemma rawX_stable : forall X, raw_stable (rawX X).
Proof.
intros X. split.
- intros s s' Em H x Hx. unfold MT. rewrite Em. apply H. exact Hx.
- intros s H x Hx. rewrite MT_take. destruct (sptr_eqb x (st_avail_meta s)); [left; reflexivity | apply H; exact Hx].
Qed.
Definition rawm (s : astate) (x : sptr) : Prop := MT s x = Some MRaw \/ MT s x = Some (MFree None None).
Definition as_keep (X : list sptr) (s s' : astate) : Prop :=
(forall x, In x X -> rawm s x -> rawm s' x) /\
(forall a, In a (st_areas s) -> In a (st_areas s')) /\
(forall k rg, region_of s k = Some rg -> rg_live rg = true ->
exists rg', region_of s' k = Some rg' /\ rg_live rg' = true /\ (rg_kind rg' = RkMap <-> rg_kind rg = RkMap) /\ rg_len rg <= rg_len rg').
Lemma as_keep_refl : forall X s, as_keep X s s.
Proof.
intros X s. split; [intros x _ H; exact H|]. split; [intros a H; exact H|].
intros k rg Hk Hl. exists rg. split; [exact Hk|]. split; [exact Hl|]. split; [tauto | lia].
Qed.
Lemma as_keep_trans : forall X s1 s2 s3, as_keep X s1 s2 -> as_keep X s2 s3 -> as_keep X s1 s3.
Proof.
intros X s1 s2 s3 (A1 & A2 & A3) (B1 & B2 & B3). split; [| split].
- intros x Hx H. apply (B1 x Hx). apply (A1 x Hx). exact H.
- intros a Ha. apply B2. apply A2. exact Ha.
- intros k rg Hk Hl. destruct (A3 k rg Hk Hl) as (rg2 & Hk2 & Hl2 & Hkd2 & Hlen2).
destruct (B3 k rg2 Hk2 Hl2) as (rg3 & Hk3 & Hl3 & Hkd3 & Hlen3).
exists rg3. split; [exact Hk3|]. split; [exact Hl3|]. split; [tauto | lia].
Qed.
Lemma as_keep_cons : forall m X s s', as_keep (m :: X) s s' -> as_keep X s s'.
Proof.
intros m X s s' (A1 & A2 & A3). split; [| split; [exact A2 | exact A3]].
intros x Hx. apply A1. right. exact Hx.
Qed.
Lemma rawX_keep : forall X s s', rawX X s -> as_keep X s s' -> rawX X s'.
Proof. intros X s s' RX (A1 & _ & _) x Hx. apply (A1 x Hx). apply RX. exact Hx. Qed.
Lemma as_keep_same : forall X s s',
(forall x, In x X -> rawm s x -> rawm s' x) -> st_areas s' = st_areas s -> st_regions s' = st_regions s -> as_keep X s s'.
Proof.
intros X s s' H1 Ea Er. split; [exact H1|]. split; [intros a; rewrite Ea; exact (fun H => H)|].
intros k rg Hk Hl. exists rg. unfold region_of in *. rewrite Er. split; [exact Hk|]. split; [exact Hl|]. split; [tauto | lia].
Qed.
Lemma as_keep_metas : forall X s s', st_metas s' = st_metas s -> st_areas s' = st_areas s -> st_regions s' = st_regions s -> as_keep X s s'.
Proof. intros X s s' Em Ea Er. apply as_keep_same; [| exact Ea | exact Er]. intros x _ H. unfold rawm, MT in *. rewrite Em. exact H. Qed.
Lemma as_keep_upd_meta : forall X s g v, MT s g <> Some MRaw -> MT s g <> Some (MFree None None) -> as_keep X s (upd_meta g v s).
Proof.
intros X s g v N1 N2. apply as_keep_same; [| reflexivity | reflexivity].
intros x _ Hr. unfold rawm in *. rewrite MT_upd. destruct (sptr_eqb x g) eqn:E; [| exact Hr].
apply sptr_eqb_eq in E. subst x. exfalso. destruct Hr as [Hr|Hr]; [exact (N1 Hr) | exact (N2 Hr)].
Qed.
Lemma as_keep_take : forall X s, as_keep X s (take_st s).
Proof.
intros X s. apply as_keep_same; [| reflexivity | reflexivity].
intros x _ Hr. unfold rawm. rewrite MT_take. destruct (sptr_eqb x (st_avail_meta s)); [left; reflexivity | exact Hr].
Qed.
Lemma as_keep_app_region : forall X s x, as_keep X s (set_regions (st_regions s ++ [x]) s).
Proof.
intros X s x. split; [intros y _ H; exact H|]. split; [intros a H; exact H|].
intros k rg Hk Hl. exists rg. split; [apply region_of_app; exact Hk|]. split; [exact Hl|]. split; [tauto | lia].
Qed.
Lemma as_keep_open : forall X p s, as_keep X s (open_st p s).
Proof.
intros X p s. split; [intros y _ H; exact H|]. split; [| intros k rg Hk Hl; exists rg; split; [exact Hk|]; split; [exact Hl|]; split; [tauto | lia]].
intros a Ha. unfold open_st. cbn. apply in_app_iff. left. exact Ha.
Qed.
Lemma as_keep_resv : forall X s, as_keep X s (resv_st s).
Proof.
intros X s. unfold resv_st.
apply (as_keep_trans X s (set_regions (st_regions s ++ [mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true]) s)); [apply as_keep_app_region|].
apply as_keep_metas; reflexivity.
Qed.
Lemma as_keep_brk2 : forall X s, as_keep X s (brk2_st s).
Proof.
intros X s. unfold brk2_st.
apply (as_keep_trans X s (set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s)); [apply as_keep_app_region|].
apply as_keep_metas; reflexivity.
Qed.
Lemma as_keep_dead : forall X s, as_keep X s (set_brk BrkDead s).
Proof. intros X s. apply as_keep_metas; reflexivity. Qed.
Lemma as_keep_openR : forall X s, as_keep X s (openR_st s).
Proof.
intros X s. unfold openR_st.
set (p := st_avail_meta_areas s).
set (x := let rg := nth (prid p) (st_regions s) (mkRegion RkMap 0 [] false) in mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff p]) (rg_live rg)).
apply (as_keep_trans X s (set_regions (lupd (st_regions s) (prid p) x) s)); [| apply as_keep_open].
split; [intros y _ H; exact H|]. split; [intros a H; exact H|].
intros k rg Hk Hl. rewrite region_of_upd.
destruct (Nat.eqb k (prid p) && Nat.ltb (prid p) (length (st_regions s)))%bool eqn:E.
- apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1. subst k.
unfold region_of in Hk. rewrite (nth_error_nth' (st_regions s) (mkRegion RkMap 0 [] false)) in Hk by (apply Nat.ltb_lt; exact E2).
injection Hk as E0. exists x. split; [reflexivity|]. subst x. cbn. rewrite E0. split; [exact Hl|]. split; [tauto | lia].
- exists rg. split; [exact Hk|]. split; [exact Hl|]. split; [tauto | lia].
Qed.
Lemma as_keep_brk1 : forall X s r pages,
(exists rg, region_of s r = Some rg /\ rg_kind rg = RkBrk) -> as_keep X s (brk1_st r pages s).
Proof.
intros X s r pages (rg0 & Hr0 & Hk0). unfold brk1_st.
set (x := mkRegion RkBrk (rg_len (nth r (st_regions s) (mkRegion RkMap 0 [] false)) + PGSZ) [] true).
apply (as_keep_trans X s (set_regions (lupd (st_regions s) r x) s)); [| apply as_keep_metas; reflexivity].
split; [intros y _ H; exact H|]. split; [intros a H; exact H|].
intros k rg Hk Hl. rewrite region_of_upd.
destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E.
- apply andb_prop in E as [E1 E2]. apply Nat.eqb_eq in E1. subst k. rewrite Hr0 in Hk. injection Hk as <-.
unfold region_of in Hr0. rewrite (nth_error_nth' (st_regions s) (mkRegion RkMap 0 [] false)) in Hr0 by (apply Nat.ltb_lt; exact E2).
injection Hr0 as E0. exists x. split; [reflexivity|]. subst x. cbn. rewrite E0, Hk0. split; [reflexivity|]. split; [split; intros HH; discriminate HH | unfold PGSZ; lia].
- exists rg. split; [exact Hk|]. split; [exact Hl|]. split; [tauto | lia].
Qed.
Lemma am_area_keep : forall X s,
(forall r pages, st_brk s = BrkCur r pages -> exists rg, region_of s r = Some rg /\ rg_kind rg = RkBrk) ->
iall (ibind (am_area s) am_after_area) (fun r => as_keep X s (snd r)).
Proof.
intros X s HBRK.
assert (AFTER : forall ok s1, as_keep X s s1 -> iall (am_after_area (ok, s1)) (fun r => as_keep X s (snd r))).
{ intros ok s1 P1. unfold am_after_area. destruct ok; cbn; [eapply as_keep_trans; [exact P1 | apply as_keep_take] | exact P1]. }
assert (RESV : forall s0, as_keep X s s0 -> iall (ibind ((rs <- area_from_mmap ;; if rs then open_area true else ret false) s0) am_after_area) (fun r => as_keep X s (snd r)) \/ st_avail_meta_area_count s0 <> 0).
{ intros s0 P0. destruct (Z.eq_dec (st_avail_meta_area_count s0) 0) as [E0|NE]; [left | right; exact NE].
destruct (am_resv_tree s0 E0) as (k & Ek & Hk0 & Hk1). rewrite Ek. cbn. intros z.
destruct (Z.eq_dec z 0) as [->|Hz]; [rewrite Hk0; cbn; exact P0|].
destruct (Hk1 z Hz) as (k2 & Ek2 & Hk2). rewrite Ek2. cbn. intros z2. rewrite Hk2.
assert (P1 : as_keep X s (resv_st s0)) by (eapply as_keep_trans; [exact P0 | apply as_keep_resv]).
destruct (z2 =? 0); cbn; [exact P1|].
eapply as_keep_trans; [| apply as_keep_take]. eapply as_keep_trans; [exact P1 | apply as_keep_openR]. }
pose proof (as_keep_refl X s) as Ps.
destruct (Z.eq_dec (st_avail_meta_area_count s) 0) as [E0|NE].
- destruct (st_brk s) as [| |r pg] eqn:Eb.
+ destruct (am_area_BN s E0 Eb) as (k0 & Ek0 & Hk0). rewrite Ek0. cbn. intros z0.
destruct (Hk0 z0) as (k1 & Ek1 & Hk10 & Hk11). rewrite Ek1. cbn. intros z1.
destruct (Z.eq_dec z1 0) as [->|Hz1].
* rewrite Hk10. destruct (RESV (set_brk BrkDead s) (as_keep_dead X s)) as [H|H]; [exact H | exfalso; apply H; exact E0].
* destruct (Hk11 z1 Hz1) as (k3 & Ek3 & Hk3). rewrite Ek3. cbn. intros z3. rewrite Hk3. cbn.
eapply as_keep_trans; [| apply as_keep_take]. eapply as_keep_trans; [apply as_keep_brk2 | apply as_keep_open].
+ rewrite (am_area_BD s E0 Eb). destruct (RESV s Ps) as [H|H]; [exact H | exfalso; apply H; exact E0].
+ destruct (am_area_BC s r pg E0 Eb) as (k1 & Ek1 & Hk10 & Hk11). rewrite Ek1. cbn. intros z1.
destruct (Z.eq_dec z1 0) as [->|Hz1].
* rewrite Hk10. destruct (RESV (set_brk BrkDead s) (as_keep_dead X s)) as [H|H]; [exact H | exfalso; apply H; exact E0].
* rewrite (Hk11 z1 Hz1). cbn. eapply as_keep_trans; [| apply as_keep_take]. eapply as_keep_trans; [apply (as_keep_brk1 X s r pg (HBRK r pg eq_refl)) | apply as_keep_open].
- destruct (am_area_R s NE) as (k & Ek & Hk). rewrite Ek. cbn. intros z. rewrite Hk. destruct (z =? 0); cbn; [exact Ps|].
eapply as_keep_trans; [apply as_keep_openR | apply as_keep_take].
Qed.
Lemma alloc_meta_keep : forall X R U s, Inv X R U s -> iall (alloc_meta s) (fun r => as_keep X s (snd r)).
Proof.
intros X R U s HI. rewrite alloc_meta_tree.
assert (K0 : as_keep X s (set_init_done true s)) by (apply as_keep_metas; reflexivity).
destruct (st_free_meta_head s) as [m|] eqn:Efh.
- destruct (deq_shape X R U (set_init_done true s) m (Inv_set_init_done X R U s HI) Efh) as (rest & s1 & RING & MTm & MEMS & Edq & DP).
rewrite Edq. cbn. destruct DP as (SB & _ & _ & _ & OTHER & _). cbn [snd] in OTHER, SB.
eapply as_keep_trans; [exact K0|]. apply as_keep_same.
+ intros x Hx Hr. unfold rawm. rewrite (OTHER x); [exact Hr|].
intros Hin. destruct (MEMS x Hin) as (qp & qn & Mq & Mx). apply (proj2 (memb_In x X)) in Hx. rewrite Hx in Mx. discriminate.
+ destruct SB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Sar & _). exact Sar.
+ destruct SB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Srg & _ & _). exact Srg.
- destruct (0 <? st_avail_meta_count s); [cbn; eapply as_keep_trans; [exact K0 | apply as_keep_take]|].
eapply iall_mono; [| apply am_area_keep].
+ intros a Ha. eapply as_keep_trans; [exact K0 | exact Ha].
+ intros r pages Hb. cbn in Hb. pose proof (inv_areas (Inv_set_init_done X R U s HI)) as (_ & _ & _ & _ & _ & _ & HB & _).
cbn [st_brk set_init_done] in HB. rewrite Hb in HB. destruct HB as [Hbr _].
assert (Hin : In r (brk_regions (set_init_done true s))) by (rewrite Hbr; left; reflexivity).
unfold brk_regions in Hin. apply in_flat_map in Hin as [k [_ Hk]].
destruct (region_of (set_init_done true s) k) as [rg|] eqn:Er; [| destruct Hk].
destruct (rg_kind rg) eqn:Ekd; try (destruct Hk; fail).
destruct Hk as [->|[]]. exists rg. split; [exact Er | exact Ekd].
Qed.
Lemma alloc_meta_rawX : forall X R U s, Inv X R U s -> rawX X s -> iall (alloc_meta s) (fun r => rawX X (snd r)).
Proof.
intros X R U s HI RX. rewrite alloc_meta_tree.
assert (RX0 : rawX X (set_init_done true s)) by (apply (proj1 (rawX_stable X) s); [reflexivity | exact RX]).
destruct (st_free_meta_head s) as [m|] eqn:Efh.
- destruct (deq_shape X R U (set_init_done true s) m (Inv_set_init_done X R U s HI) Efh) as (rest & s1 & RING & MTm & MEMS & Edq & DP).
rewrite Edq. cbn. intros x Hx. destruct DP as (_ & _ & _ & _ & OTHER & _). cbn [snd] in OTHER.
rewrite (OTHER x); [apply RX0; exact Hx|].
intros Hin. destruct (MEMS x Hin) as (qp & qn & Mq & Mx). apply (proj2 (memb_In x X)) in Hx. rewrite Hx in Mx. discriminate.
- destruct (0 <? st_avail_meta_count s); [cbn; apply (proj2 (rawX_stable X)); exact RX0|].
apply am_area_iall; [apply rawX_stable | exact RX0].
Qed.
End b.

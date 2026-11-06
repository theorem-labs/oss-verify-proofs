(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YK15 YK0k YK18 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition realloc_tree (p : sptr) (n : Z) (tr : list Z) : M sptr :=
YG00.bind (free PNull tr) (fun _ =>
YG00.bind (malloc n tr) (fun q =>
match q with
| PNull => YG00.ret PNull
| _ => YG00.bind (free p tr) (fun _ => YG00.ret q)
end)).
Definition realloc_s1 (s : astate) : astate := set_internal_inited true (set_nev (st_nev s + 1) s).
Lemma free_null_eq : forall tr s, free PNull tr s = IRet (tt, realloc_s1 s).
Proof.
intros tr s. unfold free, realloc_s1. cbn [YG00.bind YG00.ret tick modify ibind get put].
destruct (st_internal_inited (set_nev (st_nev s + 1) s)) eqn:E; cbn [YG00.ret modify ibind]; [|reflexivity].
f_equal. f_equal. destruct s; cbn in E |- *. subst. reflexivity.
Qed.
Fixpoint ileaves {A : Type} (t : itree astate A) (P : A -> Prop) : Prop :=
match t with
| IRet a => P a
| IAsk _ _ k => forall z, ileaves (k z) P
| ISpin _ => True
| IFail _ => True
end.
Lemma ileaves_mono {A} (t : itree astate A) : forall (P Q : A -> Prop), (forall a, P a -> Q a) -> ileaves t P -> ileaves t Q.
Proof. induction t as [a | q snap k IH | pc | f]; cbn; intros P Q HPQ H; [exact (HPQ a H) | intros z; exact (IH z P Q HPQ (H z)) | exact I | exact I]. Qed.
Lemma ileaves_ibind {A B} (t : itree astate A) : forall (k : A -> itree astate B) (P : B -> Prop),
ileaves t (fun a => ileaves (k a) P) -> ileaves (ibind t k) P.
Proof. induction t as [a | q snap c IH | pc | f]; cbn; intros k P H; [exact H | intros z; apply IH; exact (H z) | exact I | exact I]. Qed.
Lemma atok_leaves {A} (t : itree astate A) : forall ns (Q : bool -> A -> Prop) (P : A -> Prop),
atok ns t Q -> ileaves t P -> atok ns t (fun b a => Q b a /\ P a).
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q P HQ HP; [exact (conj HQ HP) | | exact HQ | exact HQ].
destruct HQ as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH; [apply Hk, Hz | apply HP].
Qed.
Definition keeps {A} (m : M A) : Prop := forall s, ileaves (m s) (fun r => st_internal_inited (snd r) = st_internal_inited s).
Lemma keeps_ret {A} (a : A) : keeps (YG00.ret a). Proof. intros s. reflexivity. Qed.
Lemma keeps_bind {A B} (m : M A) (k : A -> M B) : keeps m -> (forall a, keeps (k a)) -> keeps (YG00.bind m k).
Proof.
intros Hm Hk s. unfold YG00.bind. apply ileaves_ibind. eapply ileaves_mono; [|exact (Hm s)].
intros [a s'] E. cbn [snd] in E. eapply ileaves_mono; [|exact (Hk a s')]. intros r E'. rewrite E'. exact E.
Qed.
Lemma keeps_modify (f : astate -> astate) : (forall s, st_internal_inited (f s) = st_internal_inited s) -> keeps (modify f).
Proof. intros Hf s. exact (Hf s). Qed.
Lemma keeps_askz (q : kreq) : keeps (askz q). Proof. intros s z. reflexivity. Qed.
Lemma keeps_mcheck (b : bool) (pc : Z) : keeps (mcheck b pc). Proof. intros s. unfold mcheck. destruct b; exact eq_refl || exact I. Qed.
Lemma keeps_spin {A} (pc : Z) : keeps (@spin A pc). Proof. intros s. exact I. Qed.

Lemma from_primary_big : forall n, 64513 <= n -> from_primary n = false.
Proof.
intros n Hn. unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize.
repeat match goal with |- context [n <=? ?c] => replace (n <=? c) with false by (symmetry; apply Z.leb_gt; lia) end.
change (Z.shiftl 16 7) with 2048. rewrite Z.max_l by lia. apply Z.leb_gt.
pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)) as M. lia.
Qed.
Lemma keeps_depot_put : forall tr, keeps (depot_put tr).
Proof.
intros tr. unfold depot_put. apply keeps_bind; [apply keeps_askz|]. intros z. destruct (z =? 0); [apply keeps_ret|].
intros s. unfold YG00.bind, get. cbn [ibind]. unfold mcheck.
destruct (depot_ids s + 1 <? kDepotIdsPerBlock); cbn [YG00.ret YG00.fail ibind]; [|exact I].
destruct (kStartFramesMax + depot_frames s + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock); cbn [YG00.ret YG00.fail ibind put]; [|exact I].
reflexivity.
Qed.
Lemma keeps_sec_alloc : forall n, keeps (sec_alloc n).
Proof.
intros n. unfold sec_alloc. apply keeps_bind; [apply keeps_askz|]. intros z. destruct (z =? 0); [apply keeps_ret|].
intros s. unfold YG00.bind at 1, get. cbn [ibind]. unfold YG00.bind at 1. unfold mcheck.
destruct (Z.of_nat (length (st_sec_arr s)) <? kMaxNumChunks); cbn [YG00.ret YG00.fail ibind]; [|exact I].
unfold YG00.bind at 1, put. cbn [ibind].
set (s' := set_secs (st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]) s).
assert (E' : st_internal_inited s' = st_internal_inited s) by reflexivity.
assert (K : keeps (YG00.bind (if Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s
then YG00.bind (askz (KMapPtrArray (8 * Z.of_nat (length (st_sec_arr s))) kPtrArrayCommit))
(fun z2 => if aGranted z2 then modify (fun s0 => set_sec_reserved (st_sec_reserved s0 + kPtrArrayEntriesPerCommit) s0) else spin 391172)
else YG00.ret tt)
(fun _ => YG00.bind (modify (fun s0 => set_sec_arr (st_sec_arr s0 ++ [length (st_secs s)]) s0))
(fun _ => YG00.ret (Some (PSec (length (st_secs s)) kPage)))))).
{ apply keeps_bind.
- destruct (Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s); [|apply keeps_ret].
apply keeps_bind; [apply keeps_askz|]. intros z2. destruct (aGranted z2); [apply keeps_modify; intros; reflexivity | apply keeps_spin].
- intros _. apply keeps_bind; [apply keeps_modify; intros; reflexivity | intros _; apply keeps_ret]. }
eapply ileaves_mono; [|exact (K s')]. intros r E. rewrite E. exact E'.
Qed.
Lemma keeps_malloc_sec : forall n tr, from_primary n = false -> keeps (malloc n tr).
Proof.
intros n tr FP. unfold malloc. rewrite FP.
apply keeps_bind; [apply keeps_modify; intros; reflexivity|]. intros _.
apply keeps_bind; [apply keeps_mcheck|]. intros _.
apply keeps_bind; [apply keeps_sec_alloc|]. intros [beg|]; [|apply keeps_ret].
apply keeps_bind; [apply keeps_depot_put|]. intros _.
apply keeps_bind.
- destruct (needs_remap (ck_n {| ck_beg := beg; ck_req := n; ck_state := CAllocated |})); [|apply keeps_ret].
apply keeps_bind; [apply keeps_askz|]. intros z. destruct (aGranted z); [apply keeps_ret | apply keeps_spin].
- intros _. apply keeps_bind; [apply keeps_modify; intros; reflexivity | intros _; apply keeps_ret].
Qed.
Definition realloc_mpost (U : list (list Z)) (s : astate) (n : Z) (ns : bool) (r : sptr * astate) : Prop :=
malloc_post U (realloc_s1 s) n ns r /\ st_internal_inited (snd r) = true /\
(BigInv s -> BigInv (snd r) /\ mgrow (realloc_s1 s) n (snd r)).
Definition aregime3 (s : astate) (n : Z) : Prop :=
st_nev s + 2 < EV_MAX \/ (BigInv s /\ qtight s /\ bud_ok s 3 1 (wcost n) (hcost n)).

Lemma aregime3_s0 : forall U s n, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> aregime s.
Proof.
intros U s n W Hn [H|(BI & QT & B)]; [left; lia|]. apply (aregime_intro U s W BI QT).
pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn). eapply bud_ok_mono; [exact B | lia | lia | lia | lia].
Qed.
Lemma realloc_s1_wf : forall U s n, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> Wf U (realloc_s1 s).
Proof.
intros U s n W Hn R. unfold realloc_s1. apply (YG06.WfP_weaken U 1 1 1); try lia. apply YG03.WfP_set_internal_inited.
apply YG02.WfP_tick; [exact W | exact (aregime3_s0 U s n W Hn R)].
Qed.
Lemma aregime3_s1 : forall U s n, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> aregime (realloc_s1 s).
Proof.
intros U s n W Hn R. pose proof (realloc_s1_wf U s n W Hn R) as W1. destruct R as [H|(BI & QT & (B1 & B2 & B3 & B4))].
- left. unfold realloc_s1. cbn [st_nev set_nev set_internal_inited]. lia.
- apply (aregime_intro U _ W1); [exact BI | exact (qtight_ext s _ eq_refl eq_refl eq_refl QT) |].
pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn).
unfold bud_ok, nrec, wpot, sec_hulls, realloc_s1 in *. cbn [st_nev st_chunks st_secs set_nev set_internal_inited]. lia.
Qed.
Lemma aregime3_s2 : forall U s n ns q s2, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> qtight s ->
realloc_mpost U s n ns (q, s2) -> aregime s2.
Proof.
intros U s n ns q s2 W Hn R QT ((W2 & NE & _ & _ & _ & QT2) & _ & BG). cbn [snd] in *.
destruct R as [H|(BI & _ & (B1 & B2 & B3 & B4))].
- left. rewrite NE. unfold realloc_s1. cbn [st_nev set_nev set_internal_inited]. lia.
- destruct (BG BI) as (BI2 & G). apply (aregime_intro U s2 W2 BI2 (QT2 (qtight_ext s _ eq_refl eq_refl eq_refl QT))).
pose proof (bud_malloc _ n s2 ltac:(lia) G NE) as (C1 & C2 & C3 & C4).
unfold bud_ok, nrec, wpot, sec_hulls, realloc_s1 in *. cbn [st_nev st_chunks st_secs set_nev set_internal_inited] in *. lia.
Qed.
Definition realloc_fpost (U : list (list Z)) (s2 : astate) (p : sptr) (n_old : Z) (ns : bool) (r : unit * astate) : Prop :=
free_post U s2 p n_old ns r /\ (BigInv s2 -> BigInv (snd r) /\ fgrow s2 (snd r)).
Lemma realloc_free_ok : forall U s2 p n_old tr,
universe_ok U -> Wf U s2 -> aregime s2 -> In (p, n_old) (blocks s2) -> In tr U ->
atok true (free p tr s2) (realloc_fpost U s2 p n_old).
Proof.
intros U s2 p n_old tr HU W R Hin Htr.
eapply atok_mono; [|exact (YG03.free_gen U s2 p n_old tr HU W (aregime_ok _ R) (or_intror Hin) Htr)].
cbv beta. intros b r (P & BG & G). split; [exact P|]. intros BI. split; [exact (BG BI) | exact G].
Qed.
Lemma aregime3_vev : forall s n, 0 <= n < MALLOC_MAX -> qtightB s -> vev s + 2 < VEV_MAX -> aregime3 s n.
Proof.
intros s n Hn (QT & BI) H. right. split; [exact BI|]. split; [exact QT|].
pose proof (vev_bud s 3 ltac:(lia)) as B. pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn).
eapply bud_ok_mono; [exact B | lia | lia | lia | unfold HULL_UNIT in *; lia].
Qed.
Lemma realloc_s1_bud : forall s, bud_le s (realloc_s1 s) 1 0 0 0.
Proof. intros s. unfold bud_le, nrec, wpot, sec_hulls, realloc_s1. cbn [st_nev st_chunks st_secs set_nev set_internal_inited]. lia. Qed.
Lemma realloc_s1_big : forall U s, Wf U s -> qtightB s -> vev s + 2 < VEV_MAX -> Wf U (realloc_s1 s) /\ regime_big (realloc_s1 s).
Proof.
intros U s W QB H. pose proof (realloc_s1_wf U s 64513 W ltac:(unfold MALLOC_MAX; lia) (aregime3_vev s 64513 ltac:(unfold MALLOC_MAX; lia) QB H)) as W1.
split; [exact W1|]. apply (regime_big_vev U _ W1).
- destruct QB as (QT & BI). split; [exact (qtight_ext s _ eq_refl eq_refl eq_refl QT) | exact BI].
- pose proof (vev_le s (realloc_s1 s) 1 ltac:(lia) ltac:(eapply bud_le_mono; [exact (realloc_s1_bud s) | lia | lia | lia | unfold HULL_UNIT; lia])). lia.
Qed.
Lemma realloc_mpost_big : forall U s n ns q s2, 0 <= n < MALLOC_MAX -> qtightB s -> realloc_mpost U s n ns (q, s2) ->
qtightB s2 /\ jbud s s2 2 /\ bud_le s s2 2 1 (wcost n) (hcost n).
Proof.
intros U s n ns q s2 Hn (QT & BI) ((W2 & NE & _ & _ & _ & QT2) & _ & BG). cbn [snd] in *. destruct (BG BI) as (BI2 & G).
pose proof (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ (realloc_s1_bud s) (bud_malloc _ n s2 ltac:(lia) G NE)) as D. cbn in D.
pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn).
split; [split; [exact (QT2 (qtight_ext s _ eq_refl eq_refl eq_refl QT)) | exact BI2]|]. split; [|exact D].
apply (jbud_of_bud s s2 _ _ _ _ 2 ltac:(lia) D); lia.
Qed.

Lemma realloc_fpost_big : forall U s2 p nold ns s3, qtightB s2 -> realloc_fpost U s2 p nold ns (tt, s3) ->
(qtight s3 -> qtightB s3) /\ jbud s2 s3 1 /\ bud_le s2 s3 1 0 0 0.
Proof.
intros U s2 p nold ns s3 (QT & BI) (P & BG). destruct (BG BI) as (BI3 & G). cbn [snd] in *.
split; [intros Q3; exact (conj Q3 BI3)|]. split; [exact (jbud_free1 U s2 p nold ns (tt, s3) G P) | exact (bud_free U s2 p nold ns (tt, s3) G P)].
Qed.
Lemma realloc_malloc_ok : forall U s n tr,
universe_ok U -> Wf U s -> aregime3 s n   -> 64513 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr (realloc_s1 s)) (realloc_mpost U s n).
Proof.
intros U s n tr HU W Hev Hn Hlive Htr.
pose proof (realloc_s1_wf U s n W ltac:(lia) Hev) as W1. pose proof (aregime3_s1 U s n W ltac:(lia) Hev) as R1.
unfold realloc_mpost.
eapply atok_mono; [|apply atok_leaves; [exact (YG07.malloc_gen U (realloc_s1 s) n tr HU W1 (aregime_ok _ R1) ltac:(lia) Hlive Htr)
| exact (keeps_malloc_sec n tr (from_primary_big n ltac:(lia)) (realloc_s1 s))]].
cbv beta. intros b r ((P & BG & G) & K). split; [exact P|]. split; [exact K|]. intros BI. split; [exact (BG BI) | exact G].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Definition astage (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) : Prop :=
AR segs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).
Definition realloc_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\ qtight (snd r) /\
match fst r with
| PNull => astage ASTACK ly S W regs mem md (fun _ => False) ly' (snd r) W' mem' md' /\
(exists ns, realloc_mpost (as_universe B) S n ns r)
| q => exists ly2 S2 W2 mem2 md2,
astage ASTACK ly S W regs mem md (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 mem2 md2 /\
(exists ns, realloc_mpost (as_universe B) S n ns (q, S2)) /\ qtight S2 /\
(forall i, 0 <= i < Z.min n_old n ->
aview segs (w_H W2) mem2 (sptr_addr B ly2 q + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
astage ASTACK ly2 S2 W2 regs mem2 md2 (fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) ly' (snd r) W' mem' md' /\
(exists ns, realloc_fpost (as_universe B) S2 p n_old ns (tt, snd r))
end.
Definition arealloc_realizes (pc pc0 : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre segs B ly S W regs mem md ch -> aregime3 S n   ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) -> getr regs 11 = w64 n ->
64513 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In (call_trace ly pc0 regs ch) (as_universe B) ->
amreal segs (realloc_tree p n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(realloc_leaf ly S W regs mem md p n_old n).
End e.
End d.

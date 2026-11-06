(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), REQUEST ADMISSIBILITY.
   cgif's areq_ok (YG01.v:14-36) is the only thing in the atok layer this instance has to change, and it has to
   change for two reasons, both of them forced by a unit's measured numbers:
     1. KMmapSec's arm demands `len = sec_map_size n` for a secondary request n < MALLOC_MAX. The instance also
        maps the 64 KiB error-message buffer on the first class-full report, and 65,536 is NOT a sec_map_size
        value (the smallest is 73,728), so cgif's areq_ok refuses it and the first report is unprovable.
     2. MALLOC_MAX = 2 ^ 28 is below fuzz_reply's largest request, 2 ^ 29.
   areq_ok_cf therefore widens that ONE arm: a secondary of a cf-admissible size, or any page-aligned map up to
   cf_nob, which is what the placement lemma bounds anyway. Every other arm is cgif's, verbatim.
   atok_cf is cgif's atok (YG01.v:49-55) over areq_ok_cf, with its lemma family copied. atok_cf_of_atok shows
   the cf layer is WEAKER, so nothing cgif admits is lost.
   cgif's YG01.v is NOT edited. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section TOK.
Context {cp : CfParams}.

Definition areq_ok_cf (s : astate) (q : kreq) : Prop :=
match q with
| KMapUser c off len =>
1 <= c <= 31 /\ off = rg_mapped_user (reg s c) /\ len = kUserMapSize /\
0 <= off /\ off mod kUserMapSize = 0 /\ off + len <= kFreeArrayOffset /\
Forall (fun h => fst h = off /\ snd h = len \/ fst h + snd h <= off \/ off + len <= fst h) (rg_holes (reg s c))
| KMapFreeArray c off len =>
1 <= c <= 31 /\ off = rg_mapped_fa (reg s c) /\ len = kFreeArrayMapSize /\
0 <= off /\ off mod kFreeArrayMapSize = 0 /\ off + len <= kFreeArrayMax /\
Forall (fun h => fst h = kFreeArrayOffset + off /\ snd h = len \/
fst h + snd h <= kFreeArrayOffset + off \/ kFreeArrayOffset + off + len <= fst h) (rg_holes (reg s c))
| KMapPtrArray off len =>
off = 8 * st_sec_reserved s /\ len = kPtrArrayCommit /\ 0 <= off /\ off mod kPtrArrayCommit = 0 /\
off + len <= 8 * kMaxNumChunks
(* THE ONE WIDENED ARM. Left: a secondary of a cf-admissible request, cgif's condition with
   cf_malloc_max for MALLOC_MAX. Right: the error-message buffer, any page-aligned map up to
   cf_nob, which is the bound the LPS placement lemma works to in any case. *)
| KMmapSec len =>
(exists n, 0 <= n < cf_malloc_max /\ from_primary n = false /\ len = sec_map_size n)
\/ (0 < len /\ len mod kPage = 0 /\ len <= cf_nob)
| KMunmapSec r len =>
In r (st_sec_arr s) /\ exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\ len = sm_len sm
| KShadowRemap p len =>
kClearShadowMmapThreshold <= len / 8 /\
exists r off sm, p = PSec r off /\ nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\
0 <= off /\ off + len <= sm_len sm /\ off mod 8 = 0
| KDepot tr => (length tr <= kUnwindMax)%nat
end.

(* cgif's areq_ok implies ours: the only arm that differs is weaker on both sides,
   since MALLOC_MAX <= cf_malloc_max (CfParams' cf_malloc_max_ge). *)
Lemma areq_ok_cf_of_areq_ok : forall s q, areq_ok s q -> areq_ok_cf s q.
Proof.
intros s q H. destruct q; try exact H.
destruct H as (n & H1 & H2 & H3). left. exists n. pose proof cf_malloc_max_ge.
unfold MALLOC_MAX in *. split; [lia | split; assumption].
Qed.

(* The errbuf map is admissible, which is what the class-full report needs. *)
Lemma areq_ok_cf_errb : forall s w, 0 < w -> round_up w kPage <= cf_nob ->
areq_ok_cf s (KMmapSec (round_up w kPage)).
Proof.
intros s w Hw Hle. cbn. right. unfold round_up, kPage in *.
split; [|split; [apply Z_mod_mult | exact Hle]].
assert (0 < (w + 4096 - 1) / 4096) by (apply Z.div_str_pos; lia). lia.
Qed.

Fixpoint atok_cf {A : Type} (ns : bool) (t : itree astate A) (Q : bool -> A -> Prop) : Prop :=
match t with
| IRet a => Q ns a
| ISpin _ => ns = false
| IFail _ => False
| IAsk q snap k => areq_ok_cf snap q /\ forall z, aok snap q z -> atok_cf (progz q z) (k z) Q
end.

Lemma atok_cf_mono {A} (t : itree astate A) : forall ns (Q Q' : bool -> A -> Prop),
(forall b a, Q b a -> Q' b a) -> atok_cf ns t Q -> atok_cf ns t Q'.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q Q' HQ H; auto.
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH with (Q := Q); [exact HQ | apply Hk, Hz].
Qed.

Lemma atok_cf_ibind {A B} (t : itree astate A) : forall ns (k : A -> itree astate B) (Q : bool -> B -> Prop),
atok_cf ns t (fun ns' a => atok_cf ns' (k a) Q) -> atok_cf ns (ibind t k) Q.
Proof.
induction t as [a | q snap c IH | pc | f]; cbn; intros ns k Q H; auto.
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH. apply Hk, Hz.
Qed.

Lemma atok_cf_asafe {A} (t : itree astate A) : forall ns Q, atok_cf ns t Q -> asafe t.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [_ Hk]. intros z Hz. apply (IH z (progz q z) Q). apply Hk, Hz.
Qed.

Lemma atok_cf_nospin {A} (t : itree astate A) : forall Q, atok_cf true t Q -> is_spin t = false.
Proof. destruct t; cbn; intros Q H; try reflexivity. discriminate. Qed.

Lemma atok_cf_agprog {A} (t : itree astate A) : forall ns Q, atok_cf ns t Q -> agprog t.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [_ Hk]. split.
- pose proof (aok_one snap q) as H1. destruct q; try (apply (atok_cf_nospin _ Q); specialize (Hk 1 H1); cbn in Hk; exact Hk).
intros z Hz. apply (atok_cf_nospin _ Q). exact (Hk z Hz).
- intros z Hz. apply (IH z (progz q z) Q). apply Hk, Hz.
Qed.

Lemma atok_cf_apath {A} (t : itree astate A) : forall ns Q tr a, atok_cf ns t Q -> apath t tr a -> exists ns', Q ns' a.
Proof.
induction t as [a' | q snap k IH | pc | f]; cbn; intros ns Q tr a H Hy.
- destruct tr; [subst; eauto | destruct Hy].
- destruct tr as [|[q' z] tr']; [destruct Hy|].
destruct Hy as (-> & Hz & Hy). destruct H as [_ Hk]. eapply IH; [apply Hk, Hz | exact Hy].
- destruct tr; destruct Hy.
- destruct tr; destruct Hy.
Qed.

Fixpoint areqs_ok_cf {A : Type} (t : itree astate A) : Prop :=
match t with
| IAsk q snap k => areq_ok_cf snap q /\ forall z, aok snap q z -> areqs_ok_cf (k z)
| _ => True
end.

Lemma atok_cf_areqs_ok {A} (t : itree astate A) : forall ns Q, atok_cf ns t Q -> areqs_ok_cf t.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply (IH z (progz q z) Q). apply Hk, Hz.
Qed.

(* cgif's atok implies the cf one, so every released model lemma transfers. *)
Lemma atok_cf_of_atok {A} (t : itree astate A) : forall ns Q, atok ns t Q -> atok_cf ns t Q.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [Hr Hk]. split; [exact (areq_ok_cf_of_areq_ok _ _ Hr)|].
intros z Hz. apply IH. apply Hk, Hz.
Qed.

Section D.
Context {A Bt : Type}.
Implicit Types (Q : bool -> A * astate -> Prop) (s : astate) (ns : bool).
Lemma atok_cf_ret ns (a : A) s Q : Q ns (a, s) -> atok_cf ns (ret a s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_cf_bind ns (m : M Bt) (k : Bt -> M A) s Q :
atok_cf ns (m s) (fun ns' r => atok_cf ns' (k (fst r) (snd r)) Q) -> atok_cf ns (bind m k s) Q.
Proof.
intros H. unfold bind. apply atok_cf_ibind.
eapply atok_cf_mono; [|exact H]. intros b [x s'] Hb. exact Hb.
Qed.
Lemma atok_cf_fail ns f s Q : False -> atok_cf ns (@fail A f s) Q.
Proof. intros []. Qed.
Lemma atok_cf_spin pc s Q : atok_cf false (@spin A pc s) Q.
Proof. reflexivity. Qed.
Lemma atok_cf_get ns s (Q : bool -> astate * astate -> Prop) : Q ns (s, s) -> atok_cf ns (get s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_cf_put ns s s' (Q : bool -> unit * astate -> Prop) : Q ns (tt, s') -> atok_cf ns (put s' s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_cf_modify ns f s (Q : bool -> unit * astate -> Prop) : Q ns (tt, f s) -> atok_cf ns (modify f s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_cf_askz ns q s (Q : bool -> Z * astate -> Prop) :
areq_ok_cf s q -> (forall z, aok s q z -> Q (progz q z) (z, s)) -> atok_cf ns (askz q s) Q.
Proof. intros Hr H. cbn. split; [exact Hr|]. intros z Hz. apply H, Hz. Qed.
Lemma atok_cf_mcheck ns (b : bool) tag s (Q : bool -> unit * astate -> Prop) :
b = true -> Q ns (tt, s) -> atok_cf ns (mcheck b tag s) Q.
Proof. intros -> H. exact H. Qed.
Lemma atok_cf_if ns (b : bool) (m1 m2 : M A) s Q :
(b = true -> atok_cf ns (m1 s) Q) -> (b = false -> atok_cf ns (m2 s) Q) -> atok_cf ns ((if b then m1 else m2) s) Q.
Proof. intros H1 H2. destruct b; auto. Qed.
End D.

Lemma atok_cf_tick ns s (Q : bool -> unit * astate -> Prop) :
Q ns (tt, set_nev (st_nev s + 1) s) -> atok_cf ns (tick s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_cf_get_region ns c s (Q : bool -> region * astate -> Prop) :
Q ns (reg s c, s) -> atok_cf ns (get_region c s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_cf_get_pc ns c s (Q : bool -> pclass * astate -> Prop) :
Q ns (cache s c, s) -> atok_cf ns (get_pc c s) Q.
Proof. intros H. exact H. Qed.

End TOK.

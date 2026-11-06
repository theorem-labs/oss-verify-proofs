(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1r3 X1q8 X1po X1ph X1pv X1pm X1px X1pj
X1q0 X1qg X1ql X1q6 X1qn X1qj X1q5 X1pi.
Import ListNotations.
Local Open Scope Z_scope.

Definition RBIG : Z := 1024.

Lemma invl_big_block_top X st L BL LS c off n :
INVL X st L BL LS -> In ((c, off), n) BL -> RBIG <= n ->
exists g i, s_slots st !! c = Some (g, i) /\ m_maplen (get_meta_rec st g) <> 0.
Proof.
intros INV Hk Hbig.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (is_blocks _ _ _ IS _ Hk) as (g & i & Hs & Hoff & Hn & Hfit). cbn [bslot boff bsize fst snd] in Hs, Hoff, Hn, Hfit.
exists g, i. split; [exact Hs|]. intros Hml.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hg] & Hi & Ec).
destruct (hosts_ok X st LS IG _ _ Hg) as (ai & Hb & GO).
pose proof (g_nsc _ _ _ _ _ _ GO Hml) as NSC.
destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(_ & _ & ML & _)]; [| exact (ML Hml)].
destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (GS & _ & _).
assert (SCL : size_class (m_sizeclass (MR st g)) <= size_class 19) by (apply size_class_le; lia).
change (size_class 19) with 63 in SCL. unfold MR in *. unfold RBIG, UNIT, IB in *.
destruct GS as [GS|GS]; [nia| lia].
Qed.

Lemma slot_top_strip st c : slot_top (strip st) c = slot_top st c.
Proof. reflexivity. Qed.

Lemma cmalloc_sim cs L n L' cs' c :
creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', Some c) ->
exists st' BL off LS', strip st' = cs' /\ INVL x0 st' L' (((c, off), n) :: BL) LS'.
Proof.
intros CR Hn CP. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in RES.
destruct rf as [pf|]; [| exfalso; rewrite <- H1 in RES; exact RES].
rewrite <- H1 in RES. destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
exists st', BL, off, LS'. split; [reflexivity| exact INV'].
Qed.

Theorem cmalloc_big_top cs L n L' cs' c :
creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', Some c) -> RBIG <= n ->
slot_top cs' c = true /\
exists g i, s_slots cs' !! c = Some (g, i) /\ 0 <= get_stride (get_meta_rec cs' g) - IB - n.
Proof.
intros CR Hn CP Hbig. destruct (cmalloc_sim cs L n L' cs' c CR Hn CP) as (st' & BL & off & LS' & <- & INV').
rewrite slot_top_strip. destruct (invl_big_block_top _ _ _ _ _ c off n INV' (or_introl eq_refl) Hbig) as (g & i & Hs & Hml).
pose proof INV' as (_ & _ & _ & _ & _ & IS & _).
destruct (is_blocks _ _ _ IS _ (or_introl eq_refl)) as (g' & i' & Hs' & Hoff & _ & Hfit). cbn [bslot boff bsize fst snd] in Hs', Hoff, Hfit.
rewrite Hs in Hs'. injection Hs' as <- <-.
split.
- unfold slot_top. rewrite Hs. destruct (Z.eqb_spec (m_maplen (get_meta_rec st' g)) 0); [contradiction| reflexivity].
- exists g, i. split; [exact Hs|]. change (get_meta_rec (strip st') g) with (get_meta_rec st' g). unfold MR, UNIT in *. lia.
Qed.

Lemma creach_live_slot cs L c : creach cs L -> In c (ld_live L) -> exists g i, s_slots cs !! c = Some (g, i).
Proof.
intros CR Hc. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
pose proof INV as (_ & _ & _ & _ & _ & IS & _).
destruct (is_blocks _ _ _ IS _ Hk) as (g & i & Hs & _). cbn [bslot fst snd] in Hs. exists g, i. exact Hs.
Qed.

Lemma lor_nonneg a b : 0 <= a -> 0 <= b -> 0 <= Z.lor a b.
Proof. intros. apply Z.lor_nonneg. auto. Qed.

Lemma fold_off_nonneg off slack : 0 <= off -> 0 <= slack -> 0 <= fold_off off slack.
Proof.
intros Ho Hs. unfold fold_off.
destruct (Z.ltb_spec slack off); [|exact Ho].
set (m1 := Z.lor slack (Z.shiftr slack 1)).
assert (M1 : 0 <= m1) by (subst m1; apply lor_nonneg; [lia| apply Z.shiftr_nonneg; lia]).
set (m2 := Z.lor m1 (Z.shiftr m1 2)).
assert (M2 : 0 <= m2) by (subst m2; apply lor_nonneg; [lia| apply Z.shiftr_nonneg; lia]).
set (m3 := Z.lor m2 (Z.shiftr m2 4)).
assert (M3 : 0 <= m3) by (subst m3; apply lor_nonneg; [lia| apply Z.shiftr_nonneg; lia]).
pose proof (Z.land_nonneg off m3) as LN.
destruct (Z.ltb_spec slack (Z.land off m3)); lia.
Qed.

Lemma real_off_nonneg hdr cs c n g i :
s_slots cs !! c = Some (g, i) -> 0 <= get_stride (get_meta_rec cs g) - IB - n -> 0 <= real_off hdr cs c n.
Proof.
intros Hs Hsl. unfold real_off. rewrite Hs. apply fold_off_nonneg.
- unfold enf_raw. destruct (hdr !! c); apply Z.land_nonneg; right; lia.
- apply Z.div_pos; [exact Hsl| unfold UNIT; lia].
Qed.

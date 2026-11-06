(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhfJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhfJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition isC (r : mstate * option (aptr * Z)) : bool := match snd r with Some _ => true | None => false end.
Definition isM (r : mstate * optr) : bool := match snd r with Some _ => true | None => false end.
Definition isCC (r : mstate * option cptr) : bool := match snd r with Some _ => true | None => false end.

Definition PSH (SH : Z) {X : Type} (r : mstate * X) : Prop := c_meta_alloc_shift (s_ctx (fst r)) <= SH + 1.

#[using="Type"] Lemma s_ctx_enframe_at st g idx n off : s_ctx (fst (enframe_at st g idx n off)) = s_ctx st.
Proof.
unfold enframe_at. destruct (m_mem _); cbn -[wr8 wr16 set_size aadd];
destruct (negb (off =? 0)); cbn [fst]; rewrite s_ctx_set_size, ?s_ctx_wr8, ?s_ctx_wr16, ?s_ctx_wr8; reflexivity.
Qed.

Definition BIGW (SH n : Z) : Z := AMW SH + round_up_pg (n + IB + UNIT).
Definition BIGD : nat := 6%nat.

#[using="Type"] Lemma round_up_pg_le_al x y : x <= y -> y mod 4096 = 0 -> round_up_pg x <= y.
Proof. intros H1 H2. pose proof (round_up_pg_spec x) as [A B]. pose proof (Z_div_mod_eq_full y 4096). pose proof (Z_div_mod_eq_full (round_up_pg x) 4096). nia. Qed.

Section BIG.
Variables (SH : Z) (W : Z) (D : nat).
Hypothesis HSH : 0 <= SH <= 16.

Notation SHF st := (c_meta_alloc_shift (s_ctx st)).

#[using="HSH"] Theorem malloc_core_big_ks st L BL LS n :
INVL x0 st L BL LS -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 -> SHF st <= SH ->
KSUM isC (PSH SH) W D L (malloc_core full_lay st n) KS (W + BIGW SH n) (D + BIGD)%nat.
Proof.
intros INV Hbig Hn30 SHC. unfold BIGW, BIGD. pose proof (pow_SH SH HSH) as PS.
assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; unfold IB, UNIT in *; lia).
unfold malloc_core. rewrite Hov. rewrite (proj2 (Z.leb_le _ _) Hbig).
set (needed := n + IB + UNIT).
assert (HN : 131072 <= needed <= 2 ^ 30) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (round_up_pg_ge needed) as RU.
replace (D + 6)%nat with (S (D + 5))%nat by lia.
eapply (ks_ev' isC (PSH SH) W D L _ _ KN (am_kind KN KS st) _ (W + AMW SH) (D + 5)%nat);
[reflexivity| | unfold AMW; unfold PGSZ; nia| | | | intros E; discriminate E| unfold am_kind; destruct (am_quick st); reflexivity].
- cbn [esz_ok]. intros _. split; [lia|]. apply round_up_pg_le_al; [lia| reflexivity].
- cbn [ecost]. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false. cbv iota. lia.
-
intros a Ha Ca. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb]. cbn [eclass] in Ca. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false in Ca. cbv iota in Ca.
apply negb_false_iff in Ca. rewrite Ca. constructor; [unfold PSH; cbn [fst]; lia| unfold AMW, PGSZ; nia| lia].
-
intros a Ha Ca. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb]. cbn [eclass] in Ca. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false in Ca. cbv iota in Ca.
apply negb_true_iff in Ca. rewrite Ca.
change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then Qfya.set_metas ((a, needed, 0) :: ld_metas L) L else Qfya.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. rewrite Ca. cbn iota.
destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha Ca ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
rewrite <- Est1, <- Erid in INV1.
set (L1 := Qfya.set_groups ((a, needed) :: ld_groups L) L) in *.
pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
assert (AQ : am_kind KN KS st = am_kind KN KS (step_seq st1)) by reflexivity.
rewrite AQ. replace (D + 5)%nat with (S D + 4)%nat by lia.
eapply (alloc_meta_ks isC (PSH SH) W D BL _ _ (xorph x0 (Some rid)) (step_seq st1) L1 KN KS W (S D) SH ltac:(lia) HSH);
[ | | exact INV2| apply amf_refl| apply lf_refl| | split; reflexivity].
+
intros st3 L3 LS3 INV3 AF LF SH3. cbn beta iota.
eapply (ks_ev' isC (PSH SH) W D L3 _ _ KN KN _ W D); [reflexivity| exact I| lia| cbn; lia| | intros ru Hru C; cbn in C; discriminate C| intros _; reflexivity| reflexivity].
intros ru Hru _. cbn [answer_ok] in Hru. rewrite Hru. constructor; [| lia| lia]. unfold PSH. cbn [fst]. rewrite s_ctx_drop_region. exact SH3.
+
intros st3 L3 LS3 g INV3 NIg AF LF SH3 _. cbn beta iota zeta. constructor; [| lia| lia]. unfold PSH. cbn -[Z.le Z.add]. exact SH3.
+ unfold step_seq. destruct (c_seq (ctx st1) =? 255); rewrite Est1; cbn; exact SHC.
Qed.

#[using="Type"] Lemma enframe_full_ks L st g idx n ctr W' D' : W <= W' -> (D <= D')%nat -> PSH SH (st, tt) ->
KSUM isM (PSH SH) W D L (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) KS W' D'.
Proof.
intros HW' HD' HP. unfold PSH in HP. cbn [fst] in HP. unfold enframe_full, enframe_read_off. apply rd8_ks; [exact HW'|]. intros b3.
assert (LEAF : forall off, KSUM isM (PSH SH) W D L (let '(st1, p) := enframe_at st g idx n off in ret (havoc p n st1, Some p)) KS W' D').
{ intros off. pose proof (s_ctx_enframe_at st g idx n off) as E. destruct (enframe_at _ _ _ _ _) as [st1 p]. cbn [fst] in E.
constructor; [| exact HW'| exact HD']. unfold PSH. cbn [fst]. rewrite s_ctx_havoc, E. exact HP. }
destruct (negb (b3 =? 0)).
- apply rd16_ks; [exact HW'|]. intros o16. apply LEAF.
- apply LEAF.
Qed.

#[using="HSH"] Theorem malloc_big_ks st L BL LS n :
INVL x0 st L BL LS -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 -> SHF st <= SH ->
KSUM isM (PSH SH) W D L (malloc st n) KS (W + BIGW SH n) (D + BIGD)%nat.
Proof.
intros INV Hbig Hn30 SHC. unfold malloc.
apply (KSUM_sbind_same isC isM (PSH SH) (PSH SH) W D).
- intros L' [st1 [[g idx]|]] W' D' HP HW' HD'; cbn [snd isC ksingle].
+ apply enframe_full_ks; [exact HW'| exact HD'| exact HP].
+ constructor; [exact HP| exact HW'| exact HD'].
- apply (malloc_core_big_ks _ L BL LS); [| exact Hbig| exact Hn30| exact SHC].
apply INVL_set_tick; [| exact INV]. lia.
Qed.

#[using="HSH"] Theorem cmalloc_big_ks st L BL LS n :
INVL x0 st L BL LS -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 -> SHF st <= SH ->
KSUM isCC (PSH SH) W D L (cmalloc (strip st) n) KS (W + BIGW SH n) (D + BIGD)%nat.
Proof.
intros INV Hbig Hn30 SHC.
eapply (KSUM_strel (fun x => isM (snd x)) isCC (fun x => PSH SH (snd x)) (PSH SH) W D MREL); [apply (malloc_control pans0 pupd0 pans0_range st n tt)| | |].
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold isM, isCC; cbn [snd]. destruct r1, r2; try reflexivity; destruct HM.
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold PSH. cbn [fst]. rewrite <- E. exact (fun H => H).
- apply (KSUM_prun pans0 pupd0 pans0_range isM (PSH SH) W D). apply (malloc_big_ks st L BL LS n INV Hbig Hn30 SHC).
Qed.

End BIG.

End RC__1.

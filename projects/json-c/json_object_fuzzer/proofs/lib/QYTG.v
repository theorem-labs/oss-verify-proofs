(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QUZl Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import Q5Rg.Mq0.
Import QUZl.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
#[using="Type"] Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

#[using="Type"] Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

#[using="Type"] Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

#[using="Type"] Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
nia.
Qed.

#[using="Type"] Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. rewrite PGSZ_eq. change (4096-1) with 4095. rewrite land_4095. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)). lia. Qed.

#[using="Type"] Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

#[using="Type"] Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

#[using="Type"] Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. exact Q6q3.alloc_ceiling_lt. Qed.

#[using="Type"] Lemma alloc_ceiling_State : alloc_ceiling = rc_ceil.
Proof. reflexivity. Qed.

End RC__1.
End Mq0.
From Stdlib Require NArith List Bool Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi Q7S0 Qfya Qatc QSfG QdBa QpFQ QPiB Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya Qatc QSfG.Mq2 Q7S0 QdBa.Mq1 QdBa.Mq0 QpFQ QPiB Ql2m.Mq2.
Import ListNotations.
Local Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

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

Local Notation R := (MR st).

#[using="RD"] Lemma known_out q v : ~ inT (fst bm) lo hi q -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite RD by exact Hq. exact K. Qed.
#[using="RD"] Lemma unknown_out q : ~ inT (fst bm) lo hi q -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite RD by exact Hq. exact K. Qed.

#[using="st' TK"] Lemma not_inT_lo q : snd q < lo -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [H1 _]]. lia. Qed.
#[using="st' TK"] Lemma not_inT_hi q : hi <= snd q -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [_ H2]]. lia. Qed.
#[using="Type"] Lemma not_inT_rid q : fst q <> fst bm -> ~ inT (fst bm) lo hi q.
Proof. intros H [H1 _]. exact (H H1). Qed.

#[using="X st LS IM IG IS ISH m bm i Hm Hi NH NB lo hi CE TK RD DOM TKS"] Theorem inv_SH_write_T : inv_SH st' BL.
Proof.
pose proof (ce_metas _ _ CE) as HMe. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
pose proof (MR_ext st st' HMe) as ME. pose proof (hosts_ext st st' HG) as HE.
destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
- intros rid sh H. rewrite HR. eapply DOM. exact H.
- intros rid sh H. rewrite TK. eapply TKS. exact H.
-
intros b2 m2 i2 Hb2 Hi2. apply HE in Hb2. rewrite ME in Hi2 |- *.
apply known_out; [| exact (D3 b2 m2 i2 Hb2 Hi2)].
destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
unfold cnt_of in Hi2.
destruct (aptr_eq_dec m2 m) as [Em|NEm]; [destruct (Z.eq_dec i2 i) as [Ei|NEi]|].
+ subst m2 i2. apply not_inT_lo. subst lo hi. cbn. unfold IB. lia.
+ destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_intror NEi)) as [A|A];
[apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
+ destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_introl NEm)) as [A|A];
[apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
-
intros b2 m2 o Hb2 Ho. apply HE in Hb2. apply unknown_out; [| exact (D4 b2 m2 o Hb2 Ho)].
destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 Hb2 Ef) as [A|A];
[apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
-
intros b2 m2 p2 i2 Hb2 Hml Hs. apply HE in Hb2. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
destruct (D5 b2 m2 p2 i2 Hb2 Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp2 Hp2] & Hi2 & Eb2).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp2) in Eb2.
assert (OUT : forall d, 1 <= d <= 3 -> ~ inT (fst bm) lo hi (fst b2, snd b2 - d)).
{ intros d Hd. subst b2. cbn [fst snd].
destruct (N.eq_dec (fst bp2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
assert (NE : p2 <> m \/ i2 <> i).
{ destruct (aptr_eq_dec p2 m) as [->|]; [right| left; assumption]. intros ->.
pose proof (hosts_inj _ _ _ IM _ _ _ Hp2 Hm). subst bp2. destruct Hb2 as [ai2 Hb2]. rewrite Hb2 in NH. discriminate. }
destruct (sep_h3 _ _ _ _ IM IG IS m bm i Hm Hi NH p2 bp2 i2 Hp2 Ef Hi2 NE) as [A|A];
[apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
split; [exists v3; split; [apply known_out; [apply (OUT 3); lia| exact K3]| auto]|].
split; [apply known_out; [apply (OUT 2); lia| exact K2]|].
split; [apply known_out; [apply (OUT 1); lia| exact K1]| exact Q].
-
intros k m2 i2 Hk Hs. rewrite HS in Hs. rewrite !ME.
destruct (D6 k m2 i2 Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b2 Hb2] & Hi2 & Ek).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb2) in Ek.
destruct (is_blocks _ _ _ IS k Hk) as (m2' & i2' & Hs' & Hoff & Hsz & Hfit). rewrite Hs in Hs'. inversion Hs'. subst m2' i2'. clear Hs'.
pose proof (stride_ge _ _ _ IG _ _ Hb2) as [SG _].
assert (NH2 : s_groups st !! (fst b2, sstart (R m2) i2) = None).
{ destruct Hb2 as [ai2 Hb2']. pose proof (is_part _ _ _ IS _ _ _ _ Hb2' Hi2) as P. cbn zeta in P.
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai2 Hb2')) in P.
unfold one5 in P. destruct (s_groups st !! (fst b2, sstart (R m2) i2)) eqn:E; [| reflexivity]. exfalso.
assert (U : In (fst b2, sstart (R m2) i2) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
assert (H : s_groups st !! (fst b2, sstart (R m2) i2) <> None) by congruence. tauto. }
assert (NE : m2 <> m \/ i2 <> i).
{ destruct (aptr_eq_dec m2 m) as [->|]; [right| left; assumption]. intros ->.
pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2. exact (NB k Hk Ek). }
assert (OUT : forall o, sstart (R m2) i2 - 4 <= o < sstart (R m2) (i2 + 1) - 4 -> ~ inT (fst bm) lo hi (fst (bslot k), o)).
{ intros o Ho. rewrite Ek. cbn [fst].
destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 NE NH2) as [A|A];
[apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
assert (Esnd : snd (bslot k) = sstart (R m2) i2) by (rewrite Ek; reflexivity).
rewrite sstart_succ in OUT. unfold UNIT, IB in *.
split; [apply known_out; [apply OUT; lia| exact A1]|].
split; [apply known_out; [apply OUT; lia| exact A2]|].
split; [apply known_out; [apply OUT; lia| exact A3]|].
split; [apply known_out; [apply OUT; lia| exact A4]|].
split; [exact A5|]. split.
+ intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6).
repeat split; try (apply known_out; [apply OUT; lia| assumption]). exact B6.
+ split; [intros Hr; apply known_out; [apply OUT; lia| apply A7; exact Hr]|].
intros a Ha. apply unknown_out; [apply OUT; lia| apply A8; exact Ha].
Qed.
End WRITE_T.

#[using="Type"] Lemma inv_R_X X X' st L : x_orph X' = x_orph X -> inv_R X st L -> inv_R X' st L.
Proof. intros E I. destruct I; constructor; try assumption. rewrite E. assumption. Qed.
#[using="Type"] Lemma inv_M_X X X' st LS : x_idle X' = x_idle X -> x_zomb X' = x_zomb X -> inv_M X st LS -> inv_M X' st LS.
Proof. intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; assumption. Qed.
#[using="Type"] Lemma group_ok_X X X' st LS m b ai : x_fresh X' = x_fresh X -> group_ok X st LS m b ai -> group_ok X' st LS m b ai.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
#[using="Type"] Lemma inv_G_X X X' st LS : x_fresh X' = x_fresh X -> x_orph X' = x_orph X -> inv_G X st LS -> inv_G X' st LS.
Proof.
intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; try assumption.
intros. eapply group_ok_X; [exact E1|]. eauto.
Qed.

#[using="Type"] Lemma inv_SH_incl st BL BL' : (forall k, In k BL' -> In k BL) -> inv_SH st BL -> inv_SH st BL'.
Proof. intros Hsub I. destruct I; constructor; try assumption. intros k m i Hk Hs. apply ish_blk; [apply Hsub; exact Hk| exact Hs]. Qed.

#[using="Type"] Lemma bl_remove_split BL k : NoDup (map bslot BL) -> In k BL ->
exists l1 l2, BL = l1 ++ k :: l2 /\ bl_remove (bslot k) BL = l1 ++ l2 /\ ~ In (bslot k) (map bslot l1) /\ ~ In (bslot k) (map bslot l2).
Proof.
induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
cbn in ND. apply NoDup_cons in ND as [N1 N2].
destruct Hin as [<-|Hin].
- exists [], BL. cbn. rewrite aptr_eqb_refl. repeat split; auto. intros H. apply N1. apply list_elem_of_In. exact H.
- destruct (IH N2 Hin) as (l1 & l2 & E1 & E2 & M1 & M2).
assert (NE : bslot b <> bslot k).
{ intros E. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin. }
exists (b :: l1), l2. cbn. rewrite (aptr_eqb_neq (bslot b) (bslot k)) by exact NE. rewrite E1, E2 at 1. rewrite <- E1.
repeat split; auto. cbn. intros [H|H]; [exact (NE H)| exact (M1 H)].
Qed.

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

#[using="st INV Hk NP CE TK RD DOM TKS"] Theorem INVL_remove_block : INVL X' st' L BL' LS.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Hoff & Hsz & Hfit).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
assert (SUB : forall k', In k' BL' -> In k' BL /\ bslot k' <> bslot k).
{ intros k' H. subst BL'. rewrite EBL' in H. rewrite EBL. apply in_app_iff in H. split.
- apply in_app_iff. cbn. tauto.
- intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H. }

assert (IS' : inv_S X' st BL').
{ destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
- exact S1.
- exact S2.
- intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
rewrite NP in P.
assert (MEMk : In (slot_start' (MR st m2) i2) (map bslot BL) <->
In (slot_start' (MR st m2) i2) (map bslot BL') \/ slot_start' (MR st m2) i2 = bslot k).
{ subst BL'. rewrite EBL' , EBL. rewrite !map_app. cbn. rewrite !in_app_iff. cbn. intuition congruence. }
assert (NOTk : In (slot_start' (MR st m2) i2) (map bslot BL') -> slot_start' (MR st m2) i2 <> bslot k).
{ intros H E. subst BL'. rewrite EBL' in H. rewrite map_app, in_app_iff in H. rewrite E in H. tauto. }
unfold one5 in P |- *.
assert (D : @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2)) <-> slot_start' (MR st m2) i2 = bslot k) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
set (U' := In (slot_start' (MR st m2) i2) (map bslot BL')) in *.
set (E := slot_start' (MR st m2) i2 = bslot k) in *.
set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
set (P5 := @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2))) in *.
set (Q5 := None = Some (slot_start' (MR st m2) i2)) in *.
fold P5. fold Q5 in P. clearbody U U' E A F Hh P5 Q5. tauto.
- intros s Hs'. cbn in Hs'. inversion Hs'. subst s. rewrite Hs. discriminate.
- subst BL'. rewrite EBL'. pose proof S5 as ND. rewrite EBL in ND. rewrite !map_app in ND |- *. cbn in ND.
apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2.
- intros k' Hk'. apply S6. apply SUB. exact Hk'. }
assert (ISH' : inv_SH st' BL').
{ eapply (inv_SH_write_T X' st st' BL' LS (inv_M_X X X' st LS eq_refl eq_refl IM) (inv_G_X X X' st LS eq_refl eq_refl IG) IS'); try eassumption.
- apply (inv_SH_incl st BL). { intros k' H. apply SUB. exact H. } exact ISH.
-
destruct Hm as [ai Hm']. pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P.
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')) in P. unfold one5 in P.
destruct (s_groups st !! (fst bm, sstart (MR st m) i)) eqn:E; [| reflexivity]. exfalso.
assert (U : In (fst bm, sstart (MR st m) i) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
assert (H : s_groups st !! (fst bm, sstart (MR st m) i) <> None) by congruence. tauto.
- intros k' Hk' E. destruct (SUB k' Hk') as [_ NE]. apply NE. rewrite E, Ek. reflexivity.
- intros q Hq. apply (RD m i Hs). rewrite Ek. exact Hq. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
- apply (inv_A_ctrl st st' CE). exact IA.
- apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ctrl st st' LS CE). exact IL.
- apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
- apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
- exact ISH'.
Qed.

#[using="RC__ X st L LS INV Hk"] Lemma remove_block_members k' : In k' BL' <-> In k' BL /\ bslot k' <> bslot k.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
subst BL'. rewrite EBL', EBL. rewrite !in_app_iff. cbn. split.
- intros H. split; [tauto|]. intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H.
- intros [[H|[<-|H]] NE]; [tauto| congruence| tauto].
Qed.
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

#[using="Type"] Lemma inv_SH_cons st BL k m i :
inv_SH st BL -> s_slots st !! (bslot k) = Some (m, i) -> blk_shadow_ok st k m i -> inv_SH st (k :: BL).
Proof.
intros I Hs Hk. destruct I; constructor; try assumption.
intros k' m' i' [<-|Hk'] Hs'.
- rewrite Hs in Hs'. inversion Hs'. subst. exact Hk.
- apply ish_blk; assumption.
Qed.

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

#[using="st INV HP CE TK RD DOM TKS BLK"] Theorem INVL_add_block : INVL X' st' L BL' LS.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (s_slots st !! c) as [[m i]|] eqn:Hs. 2:{ exfalso. exact (is_pend _ _ _ IS c HP Hs). }
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
destruct (BLK m i eq_refl) as (Hoff & Hn & Hfit & SHK).

destruct Hm as [ai Hm'].
pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P0. cbn zeta in P0.
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')), <- Ek, HP in P0.
assert (NU : ~ In c (map bslot BL)) by (unfold one5 in P0; tauto).
assert (NH : s_groups st !! c = None).
{ destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. unfold one5 in P0. tauto. }
assert (IS' : inv_S X' st BL').
{ destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
- exact S1.
- exact S2.
- intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
rewrite HP in P. subst BL'.
assert (EQm : In (slot_start' (MR st m2) i2) (map bslot (k :: BL)) <-> c = slot_start' (MR st m2) i2 \/ In (slot_start' (MR st m2) i2) (map bslot BL)) by (cbn; tauto).
unfold one5 in P |- *. rewrite EQm.
assert (D : @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2)) <-> c = slot_start' (MR st m2) i2) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
assert (NU' : c = slot_start' (MR st m2) i2 -> ~ In (slot_start' (MR st m2) i2) (map bslot BL)) by (intros <-; exact NU).
set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
set (E := c = slot_start' (MR st m2) i2) in *.
set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
set (P5 := @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2))) in *.
set (Q5 := @eq (option aptr) None (Some (slot_start' (MR st m2) i2))) in *.
clearbody U E A F Hh P5 Q5. tauto.
- intros s Hs'. cbn in Hs'. discriminate.
- subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros H. apply NU. apply list_elem_of_In. exact H.
- intros k' [<-|Hk']; [| apply S6; exact Hk'].
exists m, i. cbn. auto. }
assert (ISH' : inv_SH st' BL').
{ apply (inv_SH_cons st' BL k m i).
- eapply (inv_SH_write_T X st st' BL LS IM IG IS); try eassumption.
+ exists ai. exact Hm'.
+ rewrite <- Ek. exact NH.
+ intros k' Hk' E. apply NU. rewrite Ek, <- E. apply in_map. exact Hk'.
+ intros q Hq. apply (RD m i eq_refl). rewrite Ek. exact Hq.
- rewrite (ce_slots _ _ CE). exact Hs.
- exact SHK. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
- apply (inv_A_ctrl st st' CE). exact IA.
- apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ctrl st st' LS CE). exact IL.
- apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
- apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
- exact ISH'.
Qed.
End ADD_BLOCK.

End RC__1.
End Mq1.
From Stdlib Require String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW QlEo_c1 QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QZAi.Mq1 Ql2m.Mq3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TIOCGWINSZ : Z := 21523.
Definition STDOUT_BUFSIZ : Z := 1024.
Definition INTERNAL_BUFSIZ : Z := 80.

Record stdout_st := mkStdout {
so_active : bool;
so_buf : list Z;
so_lbf_nl : bool;
so_first : bool
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Let M := @M St.
Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
_ <- msys (NWritev fd (match buf with [] => [to_bytes s] | _ => [to_bytes buf; to_bytes s] end))
(dec_writev (zlength buf + zlength s)) ;;
mret tt.

Definition stdout_stdio_write (s : list Z) : M unit :=
so <- rd_so ;;
stdio_writev 1 (so_buf so) s ;;;
upd_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_writefn (s : list Z) : M unit :=
so <- rd_so ;;
(if so_first so then
upd_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
match r with
| SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
| SVal _ => munr
end
else mret tt) ;;;
stdout_stdio_write s.

Definition after_last_nl (s : list Z) : Z :=
fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
(combine (map Z.of_nat (seq 0 (length s))) s) 0.

Definition stdout_towrite : M unit :=
upd_so (fun so => if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_fwritex (s : list Z) : M unit :=
stdout_towrite ;;;
so <- rd_so ;;
if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s
then stdout_writefn s
else if so_lbf_nl so then
let i := after_last_nl s in
(if 0 <? i then stdout_writefn (firstn (Z.to_nat i) s) else mret tt) ;;;
upd_so (fun so => mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
else
upd_so (fun so => mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

Fixpoint out_pieces (ps : list (list Z)) : M unit :=
match ps with
| [] => mret tt
| p :: ps' => stdout_fwritex p ;;; out_pieces ps'
end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
stdout_towrite ;;; out_pieces pieces.

Definition stdout_exit_flush : M unit :=
so <- rd_so ;;
if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

Fixpoint stderr_pieces (buf : list Z) (ps : list (list Z)) : M (list Z) :=
match ps with
| [] => mret buf
| p :: ps' =>
if INTERNAL_BUFSIZ - zlength buf <? zlength p
then (stdio_writev 2 buf p ;;; stderr_pieces [] ps')
else stderr_pieces (buf ++ p) ps'
end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
buf <- stderr_pieces [] pieces ;;
stdio_writev 2 buf [].

Definition stderr_fwrite (s : list Z) : M unit :=
if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

End Stdio.

Definition str (s : string) : list Z :=
map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Definition pieces_emit (s : list Z) : list (list Z) := [ []; []; s; [10] ].

Definition pieces_usage (argv0 : list Z) : list (list Z) :=
[ str "usage: "; []; []; argv0; str " INPUT" ++ [10] ].

Definition pieces_cannot_open (path : list Z) : list (list Z) :=
[ str "cli: cannot open "; []; []; path; [10] ].

Definition pieces_read_error (path : list Z) : list (list Z) :=
[ str "cli: read error on "; []; []; path; [10] ].

Definition pieces_oom : list (list Z) := [ str "cli: out of memory" ++ [10] ].

Definition pieces_too_big : list (list Z) :=
[ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ].

Definition pieces_short_hdr : list (list Z) := [ str "cli: input shorter than header" ++ [10] ].

Definition pieces_cfg_overrun : list (list Z) := [ str "cli: config_len overruns input" ++ [10] ].

Example pieces_usage_concat :
concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof. vm_compute. reflexivity. Qed.
End Mq2.

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Lemma hx_dig_loop_eq : forall fuel s, hx_dig_loop fuel s = wbloop hx_dig_cond hx_dig_body fuel s.
Proof. induction fuel as [|fu IH]; intros s; [reflexivity|]. cbn [hx_dig_loop wbloop]. destruct (hx_dig_cond s); [|reflexivity]. destruct (hx_dig_body s); [apply IH|reflexivity]. Qed.

Definition HXI (f0 : shfile) (s : st_hex) : Prop :=
sh_wf (hx_f s) /\ sh_same f0 (hx_f s) /\ sh_rpos f0 <= sh_rpos (hx_f s)
/\ (contc (hx_c s) -> sh_rpos (hx_f s) <= sh_N (hx_f s)) /\ bchar (hx_c s) /\ 0 <= hx_x s < 2^32.

Lemma ishexc_cont : forall c, bchar c -> ishexc c = true -> contc c.
Proof.
intros c Hc H. unfold ishexc in H. apply orb_prop in H. unfold contc. destruct H as [H|H].
- apply Z.ltb_lt in H. unfold u32 in H. split; intros ->; cbv in H; discriminate.
- apply Z.ltb_lt in H. unfold u32 in H. split; intros ->; cbv in H; discriminate.
Qed.
Lemma hx_cond_cont : forall s, bchar (hx_c s) -> hx_dig_cond s = true -> contc (hx_c s).
Proof.
intros s B H. unfold hx_dig_cond in H. apply orb_prop in H. destruct H as [H|H].
- apply ishexc_cont; assumption.
- apply Z.eqb_eq in H. rewrite H. unfold contc. lia.
Qed.

Lemma hx_dig_total : forall fuel f0 s,
BB f0 -> HXI f0 s -> cm (hx_c s) (hx_f s) < Z.of_nat fuel ->
exists s', hx_dig_loop fuel s = Some s' /\ HXI f0 s'.
Proof.
intros fuel f0 s HB HI HM. rewrite hx_dig_loop_eq.
apply (wbloop_total hx_dig_cond hx_dig_body (HXI f0) (HXI f0) (fun s => cm (hx_c s) (hx_f s))).
- intros [c f x y sc gt gr gd rp dc] HIs CND. pose proof HIs as HIcopy.
destruct HIs as (W & SM & R0 & CI & BC & RX). cbn [hx_c hx_f hx_x] in *.
pose proof (hx_cond_cont (mkHX c f x y sc gt gr gd rp dc) BC CND) as CC. cbn [hx_c] in CC. specialize (CI CC).
assert (HBf : BB f). { intros i. destruct SM as (Bf & _). rewrite Bf. apply HB. }
unfold hx_dig_body.
assert (STEP : forall x' y' sc' gt' gr' gd' rp' dc', 0 <= x' < 2^32 ->
let '(c', f') := sh_getc f in
HXI f0 (mkHX c' f' x' y' sc' gt' gr' gd' rp' dc') /\ 0 <= cm c' f' < cm c f).
{ intros * RX'. destruct (sh_getc f) as [c' f'] eqn:G.
destruct (sh_getc_facts f c' f' G W) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
destruct (cm_read f c' f' W G CI) as [M' CI'].
split. 2:{ rewrite (cm_cont c f CC). split; [apply cm_nonneg| exact M']. }
unfold HXI; cbn [hx_c hx_f hx_x]. split; [exact W'|]. split; [eapply sh_same_trans; [exact SM| eapply sh_same_getc; eauto]|].
split; [lia|]. split; [exact CI'|]. split; [eapply getc_bchar; eauto| exact RX']. }
destruct (Z.eqb_spec c 46) as [E46|N46].
+ destruct (nz gr); [exact HIcopy|].
specialize (STEP x y sc gt 1 gd dc dc RX). destruct (sh_getc f) as [c' f']. cbn [hx_c hx_f]. exact STEP.
+ match goal with |- context [match ?U with pair _ _ => _ end] =>
lazymatch U with sh_getc f => fail | _ => destruct U as [[[x2 y2] sc2] gt2] eqn:EU end end.
assert (RX2 : 0 <= x2 < 2^32).
{ destruct (dc <=? 7); [injection EU as <- _ _ _; apply u32_range|].
destruct (dc <=? 29); [injection EU as <- _ _ _; exact RX|].
destruct (nz _ && negb (nz gt)); injection EU as <- _ _ _; exact RX. }
specialize (STEP x2 y2 sc2 gt2 gr 1 rp (dc + 1) RX2). destruct (sh_getc f) as [c' f']. cbn [hx_c hx_f]. exact STEP.
- intros s' HI' _. exact HI'.
- exact HI.
- split; [apply cm_nonneg| exact HM].
Qed.

Lemma hx_norm_total : forall n x y e, 0 < x < 2^32 -> 2^31 <= x * 2^(Z.of_nat n) ->
exists x' y' e', hx_norm_loop (S n) (x, y, e) = Some (x', y', e').
Proof.
induction n as [|n IH]; intros x y e RX HX.
- rewrite hx_norm_loop_S. change (2 ^ Z.of_nat 0) with 1 in HX. replace (2^31 <=? x) with true by (symmetry; apply Z.leb_le; lia).
eexists _, _, _; reflexivity.
- rewrite hx_norm_loop_S. destruct (Z.leb_spec (2^31) x) as [GE|LT]; [eexists _, _, _; reflexivity|].
unfold hx_norm_body.
assert (U2 : u32 (2 * x) = 2 * x) by (unfold u32; apply Z.mod_small; lia).
rewrite U2.
assert (P2 : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
destruct (0 <=? f128_ge y (f128_of_d (bv_unsigned D_05))).
+ assert (L : Z.lor (2 * x) 1 = 2 * x + 1).
{ rewrite <- Z.lxor_lor by (rewrite Z.land_comm; change 1 with (Z.ones 1); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mul_comm, Z.mod_mul; lia).
rewrite Z.add_nocarry_lxor; [reflexivity|]. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Z.mul_comm, Z.mod_mul; lia. }
rewrite L. apply IH; [lia|]. nia.
+ apply IH; [lia|]. nia.
Qed.

Lemma lor32_112_cont : forall c, (Z.lor c 32 =? 112) = true -> contc c.
Proof. intros c H. apply (lor32_eq_cont c 112); [lia| exact H]. Qed.

Lemma hexfloat_m_total : forall fuelc f bits emin sign pok,
sh_wf f -> BB f -> 0 <= sh_rpos f <= sh_N f -> zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
(sh_stdio f = false -> sh_cnt0 f + 2 <= sh_rpos f) ->
exists f' y, hexfloat_m fuelc f bits emin sign pok = Some (f', y)
/\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
/\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f').
Proof.
intros fuelc f bits emin sign pok W HB R FU NS.
pose proof (sh_N_le f W) as NL.
rewrite (hexfloat_m_eq fuelc bits emin sign pok f).
destruct (sh_getc f) as [c1 f1] eqn:G1.
destruct (sh_getc_facts f c1 f1 G1 W) as (W1 & B1 & S1 & C01 & N1 & n1 & RP1 & CT1 & SH1).
destruct (cm_read f c1 f1 W G1 ltac:(lia)) as [M1 CI1].
assert (BB1 : BB f1) by (intros i; rewrite B1; apply HB).
assert (NS1 : sh_stdio f = false -> sh_rpos f1 = sh_rpos f + 1) by (intros ST; exact (nonstdio_read f c1 f1 W ST G1)).
assert (LZ1 : LZI f1 c1 f1).
{ unfold LZI. split; [exact W1|]. split; [apply sh_same_refl|]. split; [lia|]. split; [exact CI1|]. exact (getc_bchar f c1 f1 HB W G1). }

assert (FIN : forall g (y d : Z), sh_wf g -> sh_same f1 g -> (sh_stdio f = false -> sh_rpos f1 - d <= sh_rpos g) -> d <= 3 ->
exists (f' : shfile) (y' : Z), Some (g, y) = Some (f', y') /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
/\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f')).
{ intros g y d Wg (Bg & Sg & Cg & _) Rg Hd. eexists _, _. split; [reflexivity|]. split; [exact Wg|].
split; [congruence|]. split; [congruence|]. intros ST. rewrite Cg, C01. specialize (NS ST). specialize (NS1 ST). specialize (Rg ST). lia. }
assert (UNG1 : forall g, sh_wf g -> sh_same f1 g -> forall d, (sh_stdio f = false -> sh_rpos f1 - d <= sh_rpos g) ->
sh_wf (sh_unget g) /\ sh_same f1 (sh_unget g) /\ (sh_stdio f = false -> sh_rpos f1 - (d + 1) <= sh_rpos (sh_unget g))).
{ intros g Wg Sg d Rg. destruct (sh_unget_facts g Wg) as (Wu & Su & Ru). split; [exact Wu|].
split; [eapply sh_same_trans; [exact Sg | exact Su]|]. intros ST. specialize (Rg ST). lia. }
unfold HX_lz.
destruct (df_lz_total fuelc f1 0 c1 f1 BB1 LZ1) as [gd2 [c2 [f2 (E2 & LZ2 & N48 & M2)]]].
{ unfold cm. rewrite N1. destruct (contb c1); lia. }
rewrite E2.

assert (DIG : forall s, HXI f1 s -> cm (hx_c s) (hx_f s) < Z.of_nat fuelc ->
exists f' y', HX_dig fuelc bits emin sign pok s = Some (f', y') /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
/\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f')).
{ intros s HIs HMs. unfold HX_dig.
destruct (hx_dig_total fuelc f1 s BB1 HIs HMs) as [[c5 f5 x5 y5 sc5 gt5 gr5 gd5 rp5 dc5] [E5 HI5]]. rewrite E5.
destruct HI5 as (W5 & SM5 & R5 & CI5 & BC5 & RX5). cbn [hx_c hx_f hx_x] in *.
unfold HX_tail.
destruct (negb (nz gd5)).
{
destruct (UNG1 f5 W5 SM5 0 ltac:(intros; lia)) as (W6 & S6 & R6).
destruct (nz pok).
- destruct (UNG1 _ W6 S6 _ R6) as (W7 & S7 & R7).
destruct (nz gr5); [| eapply (FIN _ _ (0 + 1 + 1)); [exact W7 | exact S7 | exact R7 | lia]].
destruct (UNG1 _ W7 S7 _ R7) as (W8 & S8 & R8). eapply (FIN _ _ (0 + 1 + 1 + 1)); [exact W8 | exact S8 | exact R8 | lia].
- eexists _, _. split; [reflexivity|]. split; [apply sh_lim0_wf; exact W6|].
destruct S6 as (B6 & St6 & _). unfold sh_lim0; cbn. split; [congruence|]. split; [congruence|]. intros; lia. }

set (rp6 := if nz gr5 then rp5 else dc5). set (x6 := if dc5 <=? 7 then u32 (x5 * 16 ^ (8 - dc5)) else x5).
assert (RX6 : 0 <= x6 < 2^32) by (subst x6; destruct (dc5 <=? 7); [apply u32_range | exact RX5]).
assert (E2OK : forall g e2, sh_wf g -> sh_same f1 g -> (sh_stdio f = false -> sh_rpos f1 - 1 <= sh_rpos g) ->
exists f' y', HX_e2 bits emin sign g x6 y5 (4 * rp6 + e2 - 32) = Some (f', y') /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
/\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f')).
{ intros g e2 Wg Sg Rg. unfold HX_e2.
destruct (Z.eqb_spec x6 0) as [X0|X0]; [eapply (FIN _ _ 1); [exact Wg | exact Sg | exact Rg | lia]|].
destruct (- emin <? _); [eapply (FIN _ _ 1); [exact Wg | exact Sg | exact Rg | lia]|].
destruct (_ <? emin - _); [eapply (FIN _ _ 1); [exact Wg | exact Sg | exact Rg | lia]|].
destruct (hx_norm_total 32 x6 y5 (4 * rp6 + e2 - 32) ltac:(lia) ltac:(change (2 ^ Z.of_nat 32) with (2^32); lia)) as [x7 [y7 [e7 E7]]].
change 33%nat with (S 32). rewrite E7. unfold HX_fin.
match goal with |- context [match ?X with pair _ _ => _ end] => destruct X as [[bias x8] y8] end.
eapply (FIN _ _ 1); [exact Wg | exact Sg | exact Rg | lia]. }
destruct (Z.lor c5 32 =? 112) eqn:EP.
- pose proof (lor32_112_cont c5 EP) as CC5. specialize (CI5 CC5).
assert (R5' : 0 <= sh_rpos f5) by lia.
destruct (scanexp_total fuelc f5 pok W5 ltac:(lia)) as [f6 [e6 (E6 & W6 & S6 & R6)]].
{ destruct SM5 as (B5 & _). rewrite B5, B1. exact FU. }
rewrite E6.
assert (S16 : sh_same f1 f6) by (eapply sh_same_trans; [exact SM5 | exact S6]).
assert (R6' : sh_stdio f = false -> sh_rpos f1 - 0 <= sh_rpos f6).
{ intros ST. destruct SM5 as (_ & St5 & _). specialize (R6 ltac:(congruence)). lia. }
destruct (e6 =? LLONG_MIN_).
+ destruct (nz pok).
* destruct (UNG1 _ W6 S16 _ R6') as (W7 & S7 & R7). apply (E2OK _ _ W7 S7). intros ST. specialize (R7 ST). lia.
* eexists _, _. split; [reflexivity|]. split; [apply sh_lim0_wf; exact W6|].
destruct S16 as (B6 & St6 & _). unfold sh_lim0; cbn. split; [congruence|]. split; [congruence|]. intros; lia.
+ apply (E2OK _ _ W6 S16). intros ST. specialize (R6' ST). lia.
- destruct (UNG1 f5 W5 SM5 0 ltac:(intros; lia)) as (W6 & S6 & R6). apply (E2OK _ _ W6 S6). intros ST. specialize (R6 ST). lia. }

assert (CMB : forall c g, sh_same f1 g -> sh_rpos f1 <= sh_rpos g -> cm c g < Z.of_nat fuelc).
{ intros c g (Bg & Sg & Cg & Ng & ng) Rg. unfold cm. rewrite Ng, N1. destruct (contb c); lia. }
unfold HX_alz. destruct LZ2 as (W2 & SM2 & R2 & CI2 & BC2).
destruct (Z.eqb_spec c2 46) as [E46|N46].
- destruct (sh_getc f2) as [c3 f3] eqn:G3.
assert (CC2 : contc c2) by (rewrite E46; unfold contc; lia). specialize (CI2 CC2).
destruct (LZI_read f1 c2 f2 c3 f3 BB1 ltac:(unfold LZI; auto) CC2 G3) as [LZ3 M3].
unfold HX_rz.
destruct (df_rz_total fuelc f1 gd2 0 c3 f3 BB1 LZ3) as [gd4 [rp4 [c4 [f4 (E4 & LZ4 & N48' & M4)]]]].
{ destruct LZ3 as (W3 & SM3 & R3 & _). apply CMB; [exact SM3 | exact R3]. }
rewrite E4. destruct LZ4 as (W4 & SM4 & R4 & CI4 & BC4).
apply DIG.
+ unfold HXI; cbn [hx_c hx_f hx_x]. split; [exact W4|]. split; [exact SM4|]. split; [exact R4|]. split; [exact CI4|]. split; [exact BC4|]. lia.
+ cbn [hx_c hx_f]. apply CMB; [exact SM4 | exact R4].
- apply DIG.
+ unfold HXI; cbn [hx_c hx_f hx_x]. split; [exact W2|]. split; [exact SM2|]. split; [exact R2|]. split; [exact CI2|]. split; [exact BC2|]. lia.
+ cbn [hx_c hx_f]. apply CMB; [exact SM2 | exact R2].
Qed.
Lemma floatscan_h_total : forall fuelc f pok,
sh_wf f -> BB f -> 0 <= sh_rpos f -> zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
(sh_stdio f = false -> sh_cnt0 f <= sh_rpos f) ->
exists f' y, floatscan_h fuelc f 1 pok = Some (f', y)
/\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
/\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f').
Proof.
intros fuelc f pok W HB R FU NS.
pose proof (sh_N_le f W) as NL.
rewrite floatscan_h_1.
destruct (fs_ws_total fuelc f W HB R FU) as [c1 [f1 (E1 & W1 & S1 & B1 & SP1 & R1 & CI1 & NS1 & CR1 & _)]]. rewrite E1. unfold FS_sign.
destruct S1 as (Bf1 & St1 & C01 & N1 & n1).
assert (BB1 : BB f1) by (intros i; rewrite Bf1; apply HB).

set (sg := if (c1 =? 43) || (c1 =? 45) then _ else _).
assert (SG : exists sign c2 f2, sg = (sign, c2, f2) /\ sh_wf f2 /\ sh_same f f2 /\ bchar c2 /\ (contc c2 -> sh_rpos f2 <= sh_N f2)
/\ 0 <= sh_rpos f2 /\ (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f2) /\ (contc c2 -> 1 <= sh_rpos f2)).
{ subst sg. destruct ((c1 =? 43) || (c1 =? 45)) eqn:SGN.
- assert (CC1 : contc c1). { unfold contc. destruct (Z.eqb_spec c1 43); [subst; lia|]. destruct (Z.eqb_spec c1 45); [subst; lia| discriminate SGN]. }
specialize (CI1 CC1). cbv zeta.
destruct (sh_getc f1) as [c2 f2] eqn:G2.
destruct (sh_getc_facts f1 c2 f2 G2 W1) as (W2 & B2 & S2 & C02 & N2 & n2 & RP2 & CT2 & SH2).
eexists _, _, _. split; [reflexivity|]. split; [exact W2|]. split.
{ eapply sh_same_trans; [| eapply sh_same_getc; eauto]. unfold sh_same; auto. }
split; [eapply getc_bchar; eauto|]. split; [intros CC; destruct (CT2 CC); rewrite N2; lia|]. split; [lia|].
split. { intros ST. specialize (NS ST). specialize (NS1 ST). lia. } intros CC. destruct (CT2 CC). lia.
- eexists _, _, _. split; [reflexivity|]. split; [exact W1|]. split; [unfold sh_same; auto|]. split; [exact B1|]. split; [exact CI1|]. split; [lia|].
split. { intros ST. specialize (NS ST). specialize (NS1 ST). lia. } intros CC. specialize (CR1 CC). lia. }
destruct SG as [sign [c2 [f2 (-> & W2 & S2 & B2 & CI2 & R2 & NS2 & CR2)]]].
destruct S2 as (Bf2 & St2 & C02 & N2 & n2).
assert (BB2 : BB f2) by (intros i; rewrite Bf2; apply HB).
unfold FS_infk. change (Z.to_nat (9 - 0)) with 9%nat.
pose proof (sh_N_le f2 W2) as NL2.

destruct (fs_inf_total f2 c2 W2 BB2 B2 CI2) as [[[i3 c3] f3] (E3 & (Hi3 & W3 & S3 & B3 & CI3 & R3 & NS3) & C3)]. rewrite E3. unfold FS_inf.
destruct S3 as (Bf3 & St3 & C03 & N3 & n3).
assert (UNG : forall g n, sh_wf g -> sh_stdio g = sh_stdio f -> (sh_stdio f = false -> sh_rpos (fs_unget_loop n g) = sh_rpos g - Z.of_nat n)).
{ intros g n Wg Sg ST. destruct (fs_unget_loop_facts n g) as (_ & _ & _ & _ & _ & _ & _ & E). apply E.
unfold sh_wf in Wg. rewrite Sg, ST in Wg. tauto. }
destruct ((i3 =? 3) || (i3 =? 8) || ((3 <? i3) && nz pok)) eqn:INF.
{
match goal with |- exists f' y, Some (?g, _) = Some (f', y) /\ _ => set (g' := g) end.
assert (HG : sh_wf g' /\ sh_buf g' = sh_buf f /\ sh_stdio g' = sh_stdio f /\ (sh_stdio f = false -> sh_cnt0 g' <= sh_rpos g')).
{ subst g'. destruct (negb (i3 =? 8)) eqn:N8.
- destruct (sh_unget_facts f3 W3) as (W4 & S4 & R4). destruct S4 as (Bf4 & St4 & C04 & N4 & n4).
assert (U4 : sh_stdio f = false -> sh_rpos (sh_unget f3) = sh_rpos f3 - 1).
{ intros ST. apply sh_unget_rpos_nonstdio. unfold sh_wf in W3. rewrite St3, St2, ST in W3. tauto. }
destruct (nz pok).
+ destruct (fs_unget_loop_facts (Z.to_nat (i3 - 3)) (sh_unget f3)) as (N5 & C05 & St5 & Bf5 & G5 & n5 & R5 & E5).
split; [apply fs_unget_loop_wf; exact W4|]. split; [congruence|]. split; [congruence|].
intros ST. rewrite C05, C04, C03. rewrite (UNG (sh_unget f3) _ W4 ltac:(congruence) ST), (U4 ST), (NS3 ltac:(congruence)).
rewrite Z2Nat.id by lia. specialize (NS2 ST).
assert (i3 <> 8). { intros ->. discriminate N8. } lia.
+ split; [exact W4|]. split; [congruence|]. split; [congruence|].
intros ST. rewrite C04, C03, (U4 ST), (NS3 ltac:(congruence)). specialize (NS2 ST). lia.
- split; [exact W3|]. split; [congruence|]. split; [congruence|]. intros ST. rewrite C03, (NS3 ltac:(congruence)). specialize (NS2 ST). lia. }
destruct HG as (HG1 & HG2 & HG3 & HG4). eexists _, _. split; [reflexivity|]. auto. }

set (nn := if i3 =? 0 then fs_nan_loop 4 (0, c3, f3) else Some (i3, c3, f3)).
assert (NN : exists i4 c4 f4, nn = Some (i4, c4, f4) /\ 0 <= i4 <= 8 /\ sh_wf f4 /\ sh_same f2 f4 /\ bchar c4 /\ (contc c4 -> sh_rpos f4 <= sh_N f4)
/\ sh_rpos f2 <= sh_rpos f4 /\ (sh_stdio f = false -> sh_rpos f4 <= sh_rpos f2 + i4) /\ (i4 = 0 -> contc c4 -> 1 <= sh_rpos f4)).
{ subst nn. destruct (Z.eqb_spec i3 0) as [I0|I0].
- subst i3. destruct (fs_inf_loop_i0 _ _ _ _ _ E3) as [-> ->].
destruct (fs_nan_total f2 c2 W2 BB2 B2 CI2) as [[[i4 c4] f4] (E4 & (Hi4 & W4 & S4 & B4 & CI4 & R4 & NS4) & C4)].
rewrite E4. eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact W4|]. split; [exact S4|]. split; [exact B4|]. split; [exact CI4|].
split; [lia|]. split; [intros ST; rewrite (NS4 ltac:(congruence)); lia|]. intros ->.
destruct (fs_nan_loop_i0 _ _ _ _ _ E4) as [-> ->]. exact CR2.
- eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact W3|]. split; [unfold sh_same; auto|]. split; [exact B3|]. split; [exact CI3|].
split; [lia|]. split; [intros ST; rewrite (NS3 ltac:(congruence)); lia|]. intros; lia. }
destruct NN as [i4 [c4 [f4 (-> & Hi4 & W4 & S4 & B4 & CI4 & R4 & NS4 & I40)]]].
destruct S4 as (Bf4 & St4 & C04 & N4 & n4).
assert (BB4 : BB f4) by (intros i; rewrite Bf4, Bf2; apply HB).
unfold FS_nan.
pose proof (sh_N_le f4 W4) as NL4.
destruct (Z.eqb_spec i4 3) as [I3|I3].
{
destruct (sh_getc f4) as [c5 f5] eqn:G5.
destruct (sh_getc_facts f4 c5 f5 G5 W4) as (W5 & B5 & S5 & C05 & N5 & n5 & RP5 & CT5 & SH5).
destruct (negb (c5 =? 40)).
{ destruct (sh_unget_facts f5 W5) as (W6 & S6 & R6). destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
eexists _, _. split; [reflexivity|]. split; [exact W6|]. split; [congruence|]. split; [congruence|].
intros ST. rewrite C06, C05, C04. specialize (NS2 ST). lia. }
destruct (fs_par_total fuelc f5 W5) as [i6 [c6 [f6 (E6 & W6 & S6 & B6 & Hi6 & R6 & NS6)]]].
{ intros i; rewrite B5, Bf4, Bf2; apply HB. } { lia. } { rewrite B5, Bf4, Bf2. lia. }
rewrite E6. destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
destruct (c6 =? 41).
{ eexists _, _. split; [reflexivity|]. split; [exact W6|]. split; [congruence|]. split; [congruence|]. intros ST. rewrite C06, C05, C04. specialize (NS2 ST). lia. }
destruct (sh_unget_facts f6 W6) as (W7 & S7 & R7). destruct S7 as (Bf7 & St7 & C07 & N7 & n7).
destruct (negb (nz pok)).
{ eexists _, _. split; [reflexivity|]. split; [now apply sh_lim0_wf|]. unfold sh_lim0; cbn. split; [congruence|]. split; [congruence|]. intros; lia. }
eexists _, _. split; [reflexivity|]. split; [apply fs_unget_loop_wf; exact W7|].
destruct (fs_unget_loop_facts (Z.to_nat i6) (sh_unget f6)) as (N8 & C08 & St8 & Bf8 & G8 & n8 & R8 & E8).
split; [congruence|]. split; [congruence|].
intros ST. rewrite C08, C07, C06, C05, C04. rewrite (UNG (sh_unget f6) _ W7 ltac:(congruence) ST).
rewrite sh_unget_rpos_nonstdio. 2:{ unfold sh_wf in W6. rewrite St6, S5, St4, St2, ST in W6. tauto. }
rewrite (NS6 ltac:(congruence)). rewrite Z2Nat.id by lia.
rewrite (nonstdio_read f4 c5 f5 W4 ltac:(congruence) G5). specialize (NS2 ST). lia. }
destruct (nz i4) eqn:NZ4.
{ eexists _, _. split; [reflexivity|]. split; [apply sh_lim0_wf; now apply sh_unget_wf|].
unfold sh_lim0; cbn. rewrite sh_unget_buf, sh_unget_stdio. split; [congruence|]. split; [congruence|]. intros; lia. }
assert (I40' : i4 = 0). { unfold nz in NZ4. destruct (Z.eqb_spec i4 0); [assumption| discriminate NZ4]. }
specialize (I40 I40').
unfold FS_tail_h. destruct (Z.eqb_spec c4 48) as [C48|C48].
- destruct (sh_getc f4) as [c5 f5] eqn:G5.
destruct (sh_getc_facts f4 c5 f5 G5 W4) as (W5 & B5 & S5 & C05 & N5 & n5 & RP5 & CT5 & SH5).
unfold FS_zero. destruct (Z.lor c5 32 =? 120) eqn:HX5.
{
pose proof (lor32_eq_cont c5 120 ltac:(lia) HX5) as CC5. destruct (CT5 CC5) as [E5 L5].
assert (CC4 : contc c4) by (subst; unfold contc; lia). specialize (CI4 CC4). specialize (I40 CC4).
destruct (hexfloat_m_total fuelc f5 53 (-1074) sign pok W5) as [f' [y (E & W' & B' & S' & NS')]].
+ intros i. rewrite B5, Bf4, Bf2. apply HB.
+ pose proof (cm_read f4 c5 f5 W4 G5 CI4) as [_ CI5]. specialize (CI5 CC5). lia.
+ rewrite B5, Bf4, Bf2. exact FU.
+ intros ST. rewrite C05, C04, C02, E5. specialize (NS2 ltac:(congruence)). lia.
+ rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
intros ST. apply NS'. congruence. }
destruct (sh_unget_facts f5 W5) as (W6 & S6 & R6). destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
assert (CC4 : contc c4) by (subst; unfold contc; lia). specialize (CI4 CC4). specialize (I40 CC4).
destruct (decfloat_total_all fuelc (sh_unget f5) 48 sign pok W6) as [f' [y (E & W' & B' & S' & NS')]].
+ intros i. rewrite Bf6, B5, Bf4, Bf2. apply HB.
+ unfold bchar. lia.
+ intros _. destruct (sh_unget_shape f5) as [(L & EU)|(L & EU & _)].
* rewrite EU. clear - W5 L. unfold sh_wf in W5. unfold sh_N. destruct (sh_stdio f5) eqn:ST5; [lia|]. destruct W5 as [_ W5b]. congruence.
* rewrite EU, sh_unget_N, N5. lia.
+ lia.
+ rewrite Bf6, B5, Bf4, Bf2. exact FU.
+ intros ST. rewrite St6 in ST. rewrite C06, C05, C04, C02. rewrite sh_unget_rpos_nonstdio. 2:{ unfold sh_wf in W5. rewrite ST in W5. tauto. }
rewrite (nonstdio_read f4 c5 f5 W4 ltac:(congruence) G5). specialize (NS2 ltac:(congruence)). lia.
+ rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
intros ST. apply NS'. congruence.
- destruct (decfloat_total_all fuelc f4 c4 sign pok W4 BB4 B4 CI4 ltac:(lia)) as [f' [y (E & W' & B' & S' & NS')]].
+ rewrite Bf4, Bf2. exact FU.
+ intros ST. rewrite C04, C02. specialize (NS2 ltac:(congruence)). lia.
+ rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
intros ST. apply NS'. congruence.
Qed.

Theorem scan_strtod_h_total : forall l,
Forall (fun c => 0 <= c < 256) l ->
exists bits used, scan_strtod_h (l ++ [0]) = Some (bits, used) /\ 0 <= used.
Proof.
intros l HB. unfold scan_strtod_h.
set (f0 := mkSh (l ++ [0]) 0 0 0 false false).
assert (W0 : sh_wf f0). { unfold sh_wf; cbn. split; [exists l; reflexivity| reflexivity]. }
destruct (floatscan_h_total (fuel_of (l ++ [0])) f0 1 W0) as [f' [y (E & W' & B' & S' & NS')]].
- eapply BB_of_bytes; [reflexivity| exact HB].
- cbn. lia.
- rewrite fuel_of_val. cbn [sh_buf f0]. lia.
- cbn. intros; lia.
- rewrite E. eexists _, _. split; [reflexivity|]. unfold sh_cnt. specialize (NS' eq_refl). lia.
Qed.

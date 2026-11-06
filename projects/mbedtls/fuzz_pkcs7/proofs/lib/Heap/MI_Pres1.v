(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_Pres1 () : Init.string Init.list := ["OSSVerify.KrLib.Heap.MI_Inv.hosts"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.slot_start'"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.MI_Inv.tbit"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.False"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.MI_Inv.one5"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.Heap.MI_Inv.blk"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "OSSVerify.KrLib.Heap.MI_Inv.bslot"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.MI_Inv.x_pend"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.MI_Inv.x_fresh"; "OSSVerify.KrLib.Heap.Malloc.LActive"; "OSSVerify.KrLib.Heap.MI_Inv.head_of"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.size_class"].


(* [comment removed for export] *)
Lemma slot_key_inj X st BL (IS : inv_S X st BL) b1 m1 b2 m2 i1 i2 : ltac2:(CDefT.buildp (gd_tbl_MI_Pres1 ()) "P,(0.O9.O6.O5.)P,(0.O9.O4.O3.)P,(1.(2.=O2.)(2.O2.(3.(4.O9.O5.))))P,(1.(2.=O1.)(2.O1.(3.(4.O9.O3.))))P,(5.$6.(7.(4.O9.O5.)O2.)(7.(4.O9.O3.)O1.))(1.(5.$6.O5.O3.)(5.$8.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros H1 H2 R1 R2 E.
  pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
  rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

(* [comment removed for export] *)
Lemma one5_E_irrel (A B C D E E' : Prop) : one5 A B C D E -> ~ E -> ~ E' -> one5 A B C D E'.
Proof.
  unfold one5. (intros dd_H; ddestruct dd_H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); intros NE NE').
  split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
  repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : ltac2:(CDefT.buildp (gd_tbl_MI_Pres1 ()) "(1.(2.=VA',)(1.(2.=VF',)(1.Pi,$8.P,(2.=R1.)P,(5.$9.(:.VA',R2.)$;.)(2.R3.Vai,)(1.Pi,$8.P,(2.=R1.)P,(5.$9.(:.VF',R2.)$;.)(2.R3.(3.(4.Vst,Vg,)))(1.Pi,$8.P,(2.=R1.)P,(5.$9.(:.VA',R2.)$;.)P,(5.$9.(:.VF',R3.)$;.)$<.Pi,$8.P,(1.(=.Vai,R1.)(2.R1.(3.(4.Vst,Vg,))))(5.$9.(:.VF',R2.)$;.))))))")
(* [comment removed for export] *).
Hypothesis C_part : ltac2:(CDefT.buildp (gd_tbl_MI_Pres1 ()) "Pi,$8.P,(1.(2.=R1.)(2.R1.(3.(4.Vst,Vg,))))Zs,$6.(7.(4.Vst,Vg,)R2.)(>.(5.$9.(:.VA',R3.)$;.)(5.$9.(:.VF',R3.)$;.)(?.$6.R1.(10.$11.$12.$13.VBL,))(14.(5.(15.$16.)(17.$6.$16.(18.$6.(19.$1:.$1;.$8.$1<.)(1=.$1:.$1;.$1>.$8.$1<.$1?.)$16.)(20.$6.(19.$1:.$1;.$8.$1<.)(1=.$1:.$1;.$1>.$8.$1<.$1?.)$16.)R1.(21.Vst,))(22.$16.)))(5.(15.$6.)Vpend',(23.$6.R1.)))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Hypothesis C_pend : ltac2:(CDefT.buildp (gd_tbl_MI_Pres1 ()) "(24.(5.(15.$6.)Vpend',(25.VX,))(1.Ps,$6.P,(5.(15.$6.)(25.VX,)(23.$6.R1.))(26.$8.Li,$8.(1.(1.(2.=R1.)(2.R1.(3.(4.Vst,Vg,))))(5.$6.R3.(7.(4.Vst,Vg,)R1.))))Ps,$6.P,(5.(15.$6.)Vpend',(23.$6.R1.))(26.$8.Li,$8.(1.(1.(2.=R1.)(2.R1.(3.(4.Vst,Vg,))))(5.$6.R3.(7.(4.Vst,Vg,)R1.))))))")
(* [comment removed for export] *).
Hypothesis C_rest : ltac2:(CDefT.buildp (gd_tbl_MI_Pres1 ()) "P,(14.(5.(15.$6.)(27.VX,)(23.$6.Vg,)))Psc,$8.P,(?.$6.Vg,A1.VLS,(28.R1.))P,(14.(5.(15.$6.)(23.$6.Vg,)(29.A1.VLS,(28.R2.))))(1.(5.$8.VA',=)(14.(5.$8.VF',=)))")
(* [comment removed for export] *).
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : ltac2:(CDefT.buildp (gd_tbl_MI_Pres1 ()) "P,(14.(5.(15.$6.)(27.VX,)(23.$6.Vg,)))P,(=.(2:.(4.Vst,Vg,))+30.)P,(=.(2;.(4.Vst,Vg,))(2<.$2=.(2>.(2:.(4.Vst,Vg,)))))(1.(5.$8.VA',=)(5.$8.VF',=))")
(* [comment removed for export] *).

#[using="Type"] Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
#[using="Type"] Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fR_mem : m_mem (f (R g)) = m_mem (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_prev : m_prev (f (R g)) = m_prev (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_next : m_next (f (R g)) = m_next (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_avail : m_avail (f (R g)) = A'. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_freed : m_freed (f (R g)) = F'. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_stride : get_stride (f (R g)) = get_stride (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_gbase : gbase (f (R g)) = gbase (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_sstart i : sstart (f (R g)) i = sstart (R g) i. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_slot_start' i : slot_start' (f (R g)) i = slot_start' (R g) i. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_gend : gend (f (R g)) = gend (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_cnt : cnt_of (f (R g)) = cnt_of (R g). Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_maplen x : m_maplen (R' x) = m_maplen (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_stride x : get_stride (R' x) = get_stride (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sstart x i : sstart (R' x) i = sstart (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_slot_start' x i : slot_start' (R' x) i = slot_start' (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_gend x : gend (R' x) = gend (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_avail_other x : x <> g -> m_avail (R' x) = m_avail (R x). Proof. intros; rewrite R'_other; auto. Qed.
#[using="Type"] Lemma R'_freed_other x : x <> g -> m_freed (R' x) = m_freed (R x). Proof. intros; rewrite R'_other; auto. Qed.

#[using="Type"] Lemma st'_groups : s_groups st' = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_slots : s_slots st' = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_shadow : s_shadow st' = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m. Proof. apply hosts_ext. reflexivity. Qed.
#[using="Type"] Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
#[using="X ai pend' C_masks C_pend"] Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [auto| intros _; discriminate].
Qed.

#[using="ai Hg"] Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.

#[using="b ai INV Hg C_masks C_part C_pend C_rest C_unlisted C_under"] Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
  ddestruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
  assert (Gpres : s_metas st !! g <> None).
  { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
  assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
      destruct K as [K| ->].
      * destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
      * destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. ddestruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
      * apply K. apply Hk. exact Hk2.
      * apply Gpres. rewrite <- K. apply Hk. exact Hk2.
    + intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
      unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
      rewrite R'_sc, R'_cnt. reflexivity.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
      * apply M1. exact Hm.
    + intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
    + intros bb h Hb. rewrite st'_groups in Hb. ddestruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
    + intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
      exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
    + intros z Hz. ddestruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
    + exact L3.
    + exact L4.
    + intros m. rewrite R'_next, R'_prev. apply L5.
    + intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
      exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
    + intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
    + exact L9.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
      destruct (aptr_eqb_spec m g) as [->|NE].
      * (* [comment removed for export] *)
        pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
        rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
        destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; exact g_present).
        all: try exact C_masks.
        all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
        all: try (intros NF Hsc NI; apply C_unlisted; assumption).
        all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
        all: try (intros NF Hsc Hs; apply C_under; assumption).
        all: try (intros Hml; ddestruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); dexists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-G" g end.
      * destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; assumption).
        all: try (intros Hml; ddestruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); dexists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-O" g end.
    + intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. ddestruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
    + intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i H. rewrite st'_slots in H. ddestruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
    + intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
    + intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
      rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite fR_avail, fR_freed. apply C_part. exact Hi.
      * (* [comment removed for export] *)
        pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
        destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
        assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
        assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
        exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
    + intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
      * apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
      * destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
    + exact S5.
    + intros k Hk. ddestruct (S6 k Hk) as (m & i & ? & ?). dexists m, i. rewrite st'_slots, R'_stride. auto.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); try reflexivity; try assumption.
    + apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.

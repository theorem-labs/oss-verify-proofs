(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocRep MallocKit_AB MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A3.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_W0 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.c_secret"; "OSSVerify.KrLib.Heap.Malloc.c_init_done"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_count"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_area_count"; "OSSVerify.KrLib.Heap.Malloc.c_meta_alloc_shift"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_head"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "stdpp.gmap.gmap"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.c_usage"; "OSSVerify.KrLib.Heap.Malloc.c_unmap_seq"; "OSSVerify.KrLib.Heap.Malloc.c_seq"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "geom_same"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.testbit"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "ta_rel"; "OSSVerify.KrLib.Heap.Malloc.put_meta"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.g_meta"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.Malloc.set_group_active_idx"].


(* [comment removed for export] *)
Definition ctx_ta_same (c c1 : mctx) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_W0 ()) "(0.(1.$2.(3.O1.)(3.O2.))(0.(1.$2.(4.O1.)(4.O2.))(0.(1.$2.(5.O1.)(5.O2.))(0.(1.$6.(7.O1.)(7.O2.))(0.(1.$6.(8.O1.)(8.O2.))(0.(1.$2.(9.O1.)(9.O2.))(0.(1.$2.(:.O1.)(:.O2.))(0.(1.$2.(;.O1.)(;.O2.))(0.(1.$6.(<.O1.)(<.O2.))(0.(1.$6.(=.O1.)(=.O2.))(0.(1.$6.(>.O1.)(>.O2.))(0.(1.(?.$2.$10.$11.$2.)(12.O1.)(12.O2.))(0.(1.(?.$2.$10.$11.$2.)(13.O1.)(13.O2.))(0.(1.$2.(14.O1.)(14.O2.))(1.$15.(16.O1.)(16.O2.))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition geom_same (r r1 : meta) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_W0 ()) "(0.(1.$6.(17.O1.)(17.O2.))(0.(1.$2.(18.O1.)(18.O2.))(0.(1.$2.(19.O1.)(19.O2.))(0.(1.$2.(1:.O1.)(1:.O2.))(1.$2.(1;.O1.)(1;.O2.))))))")
(* [comment removed for export] *).

Record ta_rel (sc : Z) (st st1 : mstate) : Prop := mkTR {
  tr_regions : s_regions st1 = s_regions st;
  tr_shadow : s_shadow st1 = s_shadow st;
  tr_next : s_next_rid st1 = s_next_rid st;
  tr_areas : s_areas st1 = s_areas st;
  tr_slots : s_slots st1 = s_slots st;
  tr_tick : s_tick st1 = s_tick st;
  tr_secret : s_secret st1 = s_secret st;
  tr_reserved : s_reserved st1 = s_reserved st;
  tr_ctx : ctx_ta_same (ctx st) (ctx st1);
  tr_active : forall c, c <> sc -> active st1 c = active st c;
  tr_bounces : forall i, 0 <= bounces st i -> 0 <= bounces st1 i <= bounces st i;
  tr_geom : forall q, geom_same (get_meta_rec st q) (get_meta_rec st1 q);
  (* [comment removed for export] *)
  tr_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st1 q)) i || Z.testbit (m_freed (get_meta_rec st1 q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true;
  tr_mrange : forall q, 0 <= m_avail (get_meta_rec st q) < 2^32 -> 0 <= m_freed (get_meta_rec st q) < 2^32 ->
      0 <= m_avail (get_meta_rec st1 q) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 q) < 2^32;
  (* [comment removed for export] *)
  tr_groups : forall b, (exists gh1, (s_groups st1) !! b = Some gh1) <-> (exists gh, (s_groups st) !! b = Some gh);
  tr_gmeta : forall b gh1, (s_groups st1) !! b = Some gh1 ->
      exists gh, (s_groups st) !! b = Some gh /\ g_meta gh1 = g_meta gh
                 /\ (g_active_idx gh1 = g_active_idx gh
                     \/ (0 <= g_active_idx gh1 <= 31 /\ forall g, g_meta gh = Some g -> m_sizeclass (get_meta_rec st g) <> 0))
}.

Lemma ctx_ta_same_refl c : ctx_ta_same c c.
Proof. repeat split; reflexivity. Qed.
Lemma geom_same_refl r : geom_same r r.
Proof. repeat split; reflexivity. Qed.

Ltac ta_auto :=
  first [ reflexivity
        | apply ctx_ta_same_refl
        | (cbn; repeat split; reflexivity)
        | (intros; apply geom_same_refl)
        | (intros ? ? ? Hb__; exact Hb__)
        | (intros ? Ha__ Hf__; split; [exact Ha__| exact Hf__])
        | (intros ? ? Hq__; eexists; split; [exact Hq__|]; split; [reflexivity| left; reflexivity])
        | (intros; unfold bounces, ctx in *; cbn in *; lia)
        | idtac ].

Lemma ta_rel_refl sc st : ta_rel sc st st.
Proof. constructor; ta_auto. Qed.

Lemma ta_rel_trans sc st st1 st2 : ta_rel sc st st1 -> ta_rel sc st1 st2 -> ta_rel sc st st2.
Proof.
  intros A B. destruct A as [R1 S1 N1 A1 L1 T1 E1 V1 C1 AC1 B1 G1 BI1 MR1 GR1 GM1].
  destruct B as [R2 S2 N2 A2 L2 T2 E2 V2 C2 AC2 B2 G2 BI2 MR2 GR2 GM2].
  constructor; try congruence.
  - unfold ctx_ta_same in *. ddestruct C1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). ddestruct C2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    repeat split; congruence.
  - intros c Hc. rewrite AC2 by exact Hc. apply AC1. exact Hc.
  - intros i Hi. pose proof (B1 i Hi). pose proof (B2 i ltac:(lia)). lia.
  - intros q. ddestruct (G1 q) as (?&?&?&?&?). ddestruct (G2 q) as (?&?&?&?&?). repeat split; congruence.
  - intros q i Hi Hb. apply (BI1 q i Hi). apply (BI2 q i Hi). exact Hb.
  - intros q Ha Hf. destruct (MR1 q Ha Hf) as [Ha1 Hf1]. exact (MR2 q Ha1 Hf1).
  - intros b. rewrite GR2. apply GR1.
  - intros b gh2 H2. ddestruct (GM2 b gh2 H2) as (gh1 & H1 & M1 & AI1). ddestruct (GM1 b gh1 H1) as (gh & H & M & AI).
    exists gh. split; [exact H|]. split; [congruence|].
    destruct AI1 as [Q1|[RR1 P1]]; destruct AI as [Q0|[R0 P0]]; [left; congruence| right; split; [lia| exact P0] | right | right; split; [lia| exact P0]].
    split; [lia|]. intros g Hg E0. apply (P1 g); [congruence|]. ddestruct (G1 g) as (_ & _ & _ & SC1 & _). rewrite SC1. exact E0.
Qed.

(* [comment removed for export] *)
Lemma ta_rel_set_active sc st v : ta_rel sc st (set_active sc v st).
Proof.
  constructor; ta_auto.
  intros c Hc. rewrite active_set_active. destruct (Z.eqb_spec c sc); [lia| reflexivity].
Qed.

Lemma ta_rel_put_meta sc st g r : ltac2:(CDefT.buildp (gd_tbl_ASlot_W0 ()) "P,(1<.(1=.O3.O2.)O1.)P,Pi,$2.P,(1>.=R1.)P,(1.$1?.(20.(21.(22.O1.)R2.)(21.(23.O1.)R2.))$24.)(1.$1?.(20.(21.(22.(1=.O3.O2.))R3.)(21.(23.(1=.O3.O2.))R3.))$24.)P,P,(0.(1>.=(22.(1=.O3.O2.)))(25.(22.(1=.O3.O2.))(26.+2.+20.)))P,(0.(1>.=(23.(1=.O3.O2.)))(25.(23.(1=.O3.O2.))(26.+2.+20.)))(0.(0.(1>.=(22.O1.))(25.(22.O1.)(26.+2.+20.)))(0.(1>.=(23.O1.))(25.(23.O1.)(26.+2.+20.))))(27.O4.O3.(28.O2.O1.O3.))")
(* [comment removed for export] *).
Proof.
  intros GS BS RS. constructor; ta_auto.
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact GS| apply geom_same_refl].
  - intros q i Hi. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; apply BS; exact Hi| auto].
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact RS| auto].
Qed.

(* [comment removed for export] *)
Lemma ta_rel_put_links sc st g p n :
  ta_rel sc st (put_meta g (m_set_prev p (m_set_next n (get_meta_rec st g))) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_next sc st g n :
  ta_rel sc st (put_meta g (m_set_next n (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_prev sc st g p :
  ta_rel sc st (put_meta g (m_set_prev p (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.

Lemma ta_rel_set_bounce sc st i v : 0 <= v <= bounces st i -> ta_rel sc st (set_bounce i v st).
Proof.
  intros Hv. constructor; ta_auto.
  intros j Hj. rewrite bounces_set. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.

Lemma ta_rel_decay sc st c : 0 <= bounces st (c - 7) -> ta_rel sc st (decay_bounces c st).
Proof.
  intros Hb. unfold decay_bounces. destruct (_ && _) eqn:E; [|apply ta_rel_refl].
  apply andb_prop in E. destruct E as [_ E]. apply negb_true_iff in E. apply Z.eqb_neq in E.
  apply ta_rel_set_bounce. lia.
Qed.

Lemma ta_rel_set_gai sc st b ai : ltac2:(CDefT.buildp (gd_tbl_ASlot_W0 ()) "P,(0.(1>.=(29.O1.+1?.))(1>.(29.O1.+1?.)+1?.))P,Ph,$2:.Pg,$2;.P,(1.(2<.$2:.)(2=.$2;.$2:.(?.$2;.(2>.$2?.$30.$2.$10.)(31.$2?.$30.$32.$2.$10.$11.)$2:.)(33.$2;.(2>.$2?.$30.$2.$10.)(31.$2?.$30.$32.$2.$10.$11.)$2:.)O2.(34.O3.))(35.$2:.R2.))P,(1.$6.(36.R3.)(35.$2;.R2.))(37.(1.$2.(1:.(1=.O3.R3.))=))(27.O4.O3.(38.O2.O1.O3.))")
(* [comment removed for export] *).
Proof.
  intros Hai HSC. unfold set_group_active_idx. destruct (get_group st b) as [h|] eqn:Hb; [|apply ta_rel_refl].
  unfold get_group in Hb.
  constructor; ta_auto.
  - intros b'. cbn [s_groups set_groups]. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq. split; intros _; eauto.
    + rewrite lookup_insert_ne by congruence. split; intros X; exact X.
  - intros b' gh1 H. cbn [s_groups set_groups] in H. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in H. inversion H; subst. exists h. split; [exact Hb|]. cbn. split; [reflexivity| right; split; [exact Hai| intros g Hg; exact (HSC h g Hb Hg)]].
    + rewrite lookup_insert_ne in H by congruence. exists gh1. auto.
Qed.

Lemma tr_get_shadow sc st st1 rid : ta_rel sc st st1 -> get_shadow st1 rid = get_shadow st rid.
Proof. intros TR. unfold get_shadow. rewrite (tr_shadow _ _ _ TR). reflexivity. Qed.
Lemma tr_conc sc st st1 q : ta_rel sc st st1 -> conc st1 q = conc st q.
Proof. intros TR. unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity. Qed.
Lemma rec_set_gai b ai st q : get_meta_rec (set_group_active_idx b ai st) q = get_meta_rec st q.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
Lemma active_set_gai b ai st i : active (set_group_active_idx b ai st) i = active st i.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.

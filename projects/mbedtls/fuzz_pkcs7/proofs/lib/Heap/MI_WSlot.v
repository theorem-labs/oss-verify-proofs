(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_WSlot () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.s_secret"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.optr"; "geo_of"; "OSSVerify.KrLib.Heap.MI_Inv.sstart"; "OSSVerify.KrLib.Heap.MI_Inv.cnt_of"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "OSSVerify.KrLib.Heap.MI_TF2.geom_kept"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Heap.MI_Inv.x_idle"; "OSSVerify.KrLib.Heap.MI_Inv.INVL"; "OSSVerify.KrLib.Heap.MI_Pres3.xidle"; "X_as"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.usage"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.s_ctx"; "OSSVerify.KrLib.Heap.Malloc.c_bounces"; "OSSVerify.KrLib.Heap.Malloc.c_seq"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.upd_meta"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.m_set_avail"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.mask_upto"; "OSSVerify.KrLib.Heap.Malloc.m_set_freed"; "OSSVerify.KrLib.Heap.Malloc.mkMeta"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.lhead"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Malloc.queue"; "OSSVerify.KrLib.Heap.Malloc.LActive"; "OSSVerify.KrLib.Heap.MI_WFree2.xpend"; "OSSVerify.KrLib.Heap.MI_TF2.TF2"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"].


(* [comment removed for export] *)
Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GP (st st' : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "(0.Prid,$1.Pr,$2.P,(3.(4.$2.)(5.$1.$2.(6.$1.$7.$8.$2.)(9.$1.$7.$8.$2.)R2.(:.O2.))(;.$2.R1.))P,(3.$<.(=.R2.)$>.)(3.(4.$2.)(5.$1.$2.(6.$1.$7.$8.$2.)(9.$1.$7.$8.$2.)R4.(:.O1.))(;.$2.R3.))(3.$?.(10.O1.)(10.O2.)))")
(* [comment removed for export] *).
Lemma GP_refl st : GP st st. Proof. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans a b c : GP a b -> GP b c -> GP a c.
Proof. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> GP st st'.
Proof. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf st st' : AM_frame st st' -> GP st st'.
Proof. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf st st' sc : TA_frame st st' sc -> GP st st'.
Proof. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).

Lemma geo_facts r r' : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "P,(3.(11.(11.(11.$12.$?.)$?.)$?.)(13.O1.)(13.O2.))(0.Pi,$?.(3.$?.(14.O1.R1.)(14.O2.R1.))(0.(3.$?.(15.O1.)(15.O2.))(0.(3.$?.(16.O1.)(16.O2.))(3.$?.(17.O1.)(17.O2.)))))")
(* [comment removed for export] *).
Proof.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma geom_kept_geo st st' : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "P,Pb,$18.Ph,$19.P,(3.(4.$19.)(5.$18.$19.(6.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)$19.)(9.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)$19.)R2.(1>.O2.))(;.$19.R1.))(3.(4.$19.)(5.$18.$19.(6.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)$19.)(9.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)$19.)R3.(1>.O1.))(;.$19.R2.))P,Px,$18.(3.(11.(11.(11.$12.$?.)$?.)$?.)(13.(1?.O1.R1.))(13.(1?.O2.R1.)))(20.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_idle_sub X idle' st L BL LS : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "P,Px,$18.P,(21.$18.R1.O5.)(21.$18.R2.(22.O6.))P,(23.O6.O4.O3.O2.O1.)(23.(24.O6.O5.)O4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  (intros SUB dd_H; ddestruct dd_H as (IR & IA & IM & IL & IG & IS & ISH)).
  split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
  split.
  { destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
  split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
#[using="idle L BL LS INV IM"] Lemma fi_metas : s_metas st !! m = Some meta0.
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
#[using="idle L BL LS INV IM"] Lemma fi_put : put_meta m meta0 st = st.
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

#[using="INV NIm IM"] Lemma free_idle_ok : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "(0.(23.(25.Vidle,)Vst',VL,VBL,VLS',)(0.(3.(6.$1.$7.$8.$26.)(27.Vst',)(27.Vst,))(0.(3.$1.(28.Vst',)(28.Vst,))(0.(3.(6.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)$19.)(1>.Vst',)(1>.Vst,))(0.(3.(6.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)(11.$18.$?.))(29.Vst',)(29.Vst,))(0.(3.(6.$1.$7.$8.$2.)(:.Vst',)(:.Vst,))(0.(3.$1.(2:.Vst',)(2:.Vst,))(0.Psc,$?.(3.$12.(2;.Vst',R1.)(2;.Vst,R1.))(0.Psc,$?.(3.$?.(2<.Vst',R1.)(2<.Vst,R1.))(0.(3.$?.(2=.(2>.Vst',))(2=.(2>.Vst,)))(0.(3.(6.$?.$1;.$1=.$?.)(2?.(2>.Vst',))(2?.(2>.Vst,)))(3.$?.(30.(2>.Vst',))(30.(2>.Vst,))))))))))))))")
(* [comment removed for export] *).
Proof.
  pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
  ddestruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

#[using="ai Hb"] Lemma fin_hosts : hosts st2 b m. Proof. exists ai. exact Hb. Qed.
#[using="idle st2 L BL m X2 INV HA"] Lemma fin_empty : LS (LActive sc) = [].
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

#[using="Type"] Lemma mask_upto_pred a : 0 <= a -> mask_upto a - 1 = Z.ldiff (mask_upto a) 1.
Proof.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

#[using="last Hai"] Lemma testbit_avail' i : 0 <= i -> Z.testbit (mask_upto ai - 1) i = ((1 <=? i) && (i <=? ai)).
Proof.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

#[using="b sc ml Em"] Lemma st3_eq : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "(3.$31.Vst3,(32.Vm,Lr,$33.(34.(35.(36.Vai,)+1.)(37.(35.(36.Vlast,)(36.Vai,))R1.))Vst2,))")
(* [comment removed for export] *).
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

#[using="ai last sc ml X2 INV Hb Em Hai Hl"] Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. ddestruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  dpose INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    ddestruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
Qed.

#[using="Em"] Lemma fin_MR3 : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "(3.$33.(1?.Vst3,Vm,)(38.(39.$18.)(39.$18.)(;.$18.Vb,)(35.(36.Vai,)+1.)(35.(36.Vlast,)(36.Vai,))Vlast,+1.Vsc,Vml,))")
(* [comment removed for export] *).
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
#[using="Type"] Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

#[using="b ai last ml Em"] Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

#[using="HA"] Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

#[using="ai last ml X2 INV Hb Em Hai Hl Hsc"] Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

#[using="idle st2 L BL X2 INV HA"] Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

#[using="Type"] Lemma fin_MR4 : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "(0.(3.(11.(11.(11.$12.$?.)$?.)$?.)(13.(1?.Vst4,Vm,))(13.(1?.Vst3,Vm,)))(0.(3.$?.(3:.(1?.Vst4,Vm,))(3:.(1?.Vst3,Vm,)))(3.$?.(3;.(1?.Vst4,Vm,))(3;.(1?.Vst3,Vm,)))))")
(* [comment removed for export] *).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. ddestruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

#[using="b ai last ml Em"] Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. ddestruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

#[using="LS ai ml X2 INV Hb Em Hai Hl Hsc HA UND TF LS4"] Theorem slot_finish_ok : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot ()) "(3<.P,$3=.(3>.$18.)LLS',P,$3=.(3>.$18.)(0.(3.(3?.VT,)(40.VT,(41.Vsc,)Vm,Vst3,Vk,Vbail,)A1.Vk,Vst4,)(0.(23.(42.(25.Vidle,)(;.$18.Vs0,))Vst4,VL,VBL,R1.)(0.(43.Vst4,)(0.(3.$12.(2;.Vst4,Vsc,)(;.$18.Vm,))(0.Psc',$?.P,(44.(3.$?.R1.Vsc,))(3.$12.(2;.Vst4,R2.)(2;.Vst2,R2.))(0.(3.(6.$18.(1:.$1.$7.$?.$1;.)(1<.$1.$7.$8.$?.$1;.$1=.)$19.)(1>.Vst4,)(1>.Vst2,))(0.(3.$1.(28.Vst4,)(28.Vst2,))(0.(3.(6.$1.$7.$8.$26.)(27.Vst4,)(27.Vst2,))(0.(3.$?.(45.(1?.Vst4,Vm,))Vlast,)(0.(3.$?.(46.(1?.Vst4,Vm,))Vsc,)(0.(3.$?.(17.(1?.Vst4,Vm,))(17.(1?.Vst2,Vm,)))(0.Pi,$?.(3.$?.(14.(1?.Vst4,Vm,)R1.)(14.(1?.Vst2,Vm,)R1.))(0.(3.(6.$1.$7.$8.$2.)(:.Vst4,)(:.Vst2,))(3.$?.(10.Vst4,)(10.Vst2,))))))))))))))))")
(* [comment removed for export] *).
Proof.
  exists LS4. ddestruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
  split; [exact fin_queue_eq|].
  split.
  { (* [comment removed for export] *)
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. ddestruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity| rewrite F8; reflexivity].
Qed.
End FINISH.

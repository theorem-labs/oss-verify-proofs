(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_WTry.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_WTry2 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.mkGhdr"; "GOODH"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.lhead"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.set_active"; "OSSVerify.KrLib.Heap.MI_Inv.INVL"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.Malloc.dequeue"; "OSSVerify.KrLib.Heap.Malloc.LActive"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Heap.MI_Inv.head_of"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.Heap.Malloc.mask_upto"; "TA_frame"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.ctz32"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.MI_WFree2.xpend"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.MI_Inv.sstart"; "OSSVerify.KrLib.Heap.Malloc.m_set_avail"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Malloc.ta_fin"; "TRY.TA_POST"; "OSSVerify.KrLib.Heap.Malloc.try_avail"].


(* [comment removed for export] *)
Record TA_frame (st st1 : mstate) (sc : Z) : Prop := mkTAF {
  taf_regions : s_regions st1 = s_regions st;
  taf_shadow : s_shadow st1 = s_shadow st;
  taf_tick : s_tick st1 = s_tick st;
  taf_slots : s_slots st1 = s_slots st;
  taf_areas : s_areas st1 = s_areas st;
  taf_next_rid : s_next_rid st1 = s_next_rid st;
  taf_heads : forall h, h <> LActive sc -> get_head st1 h = get_head st h;
  taf_usage : forall sc', usage st1 sc' = usage st sc';
  taf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  taf_ssec : s_secret st1 = s_secret st;
  taf_secret : c_secret (s_ctx st1) = c_secret (s_ctx st) /\ c_init_done (s_ctx st1) = c_init_done (s_ctx st)
}.
Lemma taf_refl st sc : TA_frame st st sc. Proof. constructor; auto. Qed.
Lemma taf_trans a b c sc : TA_frame a b sc -> TA_frame b c sc -> TA_frame a c sc.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A12 [A10 A11]] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B12 [B10 B11]]; constructor; try congruence.
  all: try (intros h Hh; rewrite (B7 h Hh); apply A7; exact Hh).
  all: try (intros sc'; rewrite (B8 sc'); apply A8).
  all: split; congruence.
Qed.
Lemma taf_upd_meta st m f sc : TA_frame st (upd_meta m f st) sc.
Proof. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_set_active st sc v : TA_frame st (set_active sc v st) sc.
Proof.
  constructor; auto; try (intros h Hh; change (set_active sc v st) with (set_head (LActive sc) v st); apply get_head_set_head_other; exact Hh).
Qed.
Lemma taf_decay st sc sc0 : TA_frame st (decay_bounces sc0 st) sc.
Proof. unfold decay_bounces. destruct (sc_in_seq_range _ && _); [| apply taf_refl]. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_dequeue st sc m : TA_frame st (dequeue (LActive sc) m st) sc.
Proof.
  ddestruct (dequeue_frame (LActive sc) m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC). destruct FC.
  constructor; auto.
  all: try (intros h Hh; rewrite dequeue_head; destruct (decide (h = LActive sc)); [congruence| reflexivity]).
  all: try (intros sc'; unfold usage, ctx; rewrite cb_usage; reflexivity).
  all: try (split; assumption).
Qed.

(* [comment removed for export] *)
Section HEADFACTS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HA : active st sc = Some m.
#[using="X st L BL INV HA"] Lemma hd_list : exists rest, LS (LActive sc) = m :: rest.
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as H. change (get_head st (LActive sc)) with (active st sc) in H. rewrite HA in H.
  destruct (LS (LActive sc)) as [|a rest]; cbn in H; [discriminate|]. inversion H. exists rest. reflexivity.
Qed.
#[using="X st L BL INV HA"] Lemma hd_in : In m (LS (LActive sc)).
Proof. destruct hd_list as [rest ->]. left. reflexivity. Qed.
#[using="X L BL LS INV HA"] Lemma hd_facts : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "(0.(0.(1.=Vsc,)(2.Vsc,+30.))(0.(3.$4.(5.(6.Vst,Vm,))Vsc,)(7.$8.Lb,$8.(7.$4.Lai,$4.(3.(9.$:.)(;.$8.$:.(<.$8.(=.$>.$?.$4.$10.)(11.$>.$?.$12.$4.$10.$13.)$:.)(14.$8.(=.$>.$?.$4.$10.)(11.$>.$?.$12.$4.$10.$13.)$:.)R2.(15.Vst,))(16.$:.(17.(16.$8.Vm,)R1.)))))))")
(* [comment removed for export] *).
Proof.
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in) as (A & [b [ai Hb]] & C). split; [exact A|]. split; [exact C|]. dexists b, ai. exact Hb.
Qed.
#[using="X st L BL INV HA"] Lemma hd_head : head_of (LS (LActive sc)) = Some m.
Proof. destruct hd_list as [rest ->]. reflexivity. Qed.
#[using="X L BL INV HA"] Lemma hd_next : exists mn, m_next (MR st m) = Some mn /\ In mn (LS (LActive sc)).
Proof.
  destruct (lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in) as (y & Hy & E & _). exists y. auto.
Qed.
End HEADFACTS.

(* [comment removed for export] *)
Definition GOODH (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr) : Prop :=
  INVL X st L BL LS /\ active st sc = Some m /\ m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0.

Section STEPS.
Variables (X : extras) (L : mled) (BL : list blk) (sc : Z).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
#[using="HF"] Lemma rotate_ok st LS m mn : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "P,(18.VX,O4.VL,VBL,O3.Vsc,O2.)P,(3.$19.(1:.(6.O4.O2.))(16.$8.O1.))(7.P,$1;.(1<.$8.)LLS',P,$1;.(1<.$8.)(18.VX,(1=.Vsc,(16.$8.O1.)O4.)VL,VBL,R1.Vsc,O1.))")
(* [comment removed for export] *).
Proof.
  (intros dd_H; ddestruct dd_H as (INV & HA & AV & FR); intros Hn).
  destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  assert (INV' : INVL X (set_head (LActive sc) (Some mn) st) L BL (fupd LS (LActive sc) (rest ++ [m]))).
  { apply (INVL_rotate X st L BL LS sc m mn rest INV HL Hn). intros _ _. auto. }
  exists (fupd LS (LActive sc) (rest ++ [m])). split; [exact INV'|].
  split; [unfold active, set_active, ctx; cbn; rewrite lookup_insert_eq; reflexivity|].
  change (MR (set_active sc (Some mn) st) mn) with (MR st mn).
  pose proof (next_listed X st L BL LS INV (LActive sc) m mn (hd_in X st L BL LS sc m INV HA) Hn) as Hin.
  destruct (aptr_eq_dec mn m) as [->|NE]; [auto|].
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc mn Hin) as (_ & [bb [aa Hbb]] & _).
  apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
  rewrite (hd_head X st L BL LS sc m INV HA). congruence.
Qed.

(* [comment removed for export] *)
#[using="HP HF Hsc"] Lemma dequeue_exhausted_ok st LS m : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "P,(1>.VX,O3.VL,VBL,O2.)P,(3.$19.(1?.O3.Vsc,)(16.$8.O1.))P,(3.$4.(20.(6.O3.O1.))=)P,(3.$4.(21.(6.O3.O1.))=)(7.P,$1;.(1<.$8.)LLS',P,$1;.(1<.$8.)(7.(1<.$8.)Lrest,(1<.$8.)(0.(1>.VX,(22.(23.Vsc,)O1.O3.)VL,VBL,R2.)(0.(3.(1<.$8.)A1.O2.(23.Vsc,)(24.$8.O1.R1.))(0.(3.$19.(1?.(22.(23.Vsc,)O1.O3.)Vsc,)(25.R1.))Pm1,$8.P,(3.$19.(25.R2.)(16.$8.R1.))(0.(3.$4.(20.(6.O3.R2.))=)(26.(3.$4.(21.(6.O3.R2.))=))))))))")
(* [comment removed for export] *).
Proof.
  intros INV HA AV FR. destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  ddestruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & b & ai & Hb).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  pose proof (INVL_dequeue X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)) as INV1.
  assert (INV2 : INVL (xfresh (xfresh X (Some m)) None) (dequeue (LActive sc) m st) L BL (fupd LS (LActive sc) ([] ++ rest))).
  { apply (INVL_clear_fresh _ _ L BL _ m INV1 eq_refl). intros bb aix Hbb.
    ddestruct (dequeue_frame (LActive sc) m st) as (_ & _ & _ & _ & G5 & _). rewrite G5 in Hbb.
    pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ (ex_intro _ aix Hbb) (ex_intro _ ai Hb)) as ->. rewrite Hb in Hbb. inversion Hbb. subst aix.
    pose proof (dequeue_data (LActive sc) m st m) as D. destruct (data_same _ _ 0 D) as (_ & El & Ea & Ef & Es & _).
    rewrite El, Ea, Ef, Es. split; [| split; [intros; auto| split; [| intros; auto]]].
    - intros Hlt. exfalso. pose proof (g_masks _ _ _ _ _ _ GO) as (_ & _ & _ & _ & _ & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
      specialize (M6 (m_last_idx (MR st m)) ltac:(lia)). unfold tbit in M6. rewrite FR, Z.bits_0 in M6. discriminate.
    - intros sc0 Hin. exfalso. cbn in Hin.
      apply (m_out X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)). exists (LActive sc0). exact Hin. }
  replace (xfresh (xfresh X (Some m)) None) with X in INV2 by (destruct X; cbn in HF |- *; subst; reflexivity).
  dexists (fupd LS (LActive sc) ([] ++ rest)), rest. split; [exact INV2|]. split; [exact HL|]. split.
  - change (active (dequeue (LActive sc) m st) sc) with (get_head (dequeue (LActive sc) m st) (LActive sc)). rewrite dequeue_head.
    rewrite decide_True by reflexivity. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. rewrite HL in HH. cbn in HH.
    ddestruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
    destruct (optr_eqb_spec (Some mn) (Some m)) as [E|NE].
    + inversion E. subst mn. pose proof (proj1 (lists_singleton st LS (old_lists _ _ _ _ _ INV) (LActive sc) m rest HL) Hn) as ER. rewrite ER. reflexivity.
    + change (get_head st (LActive sc)) with (active st sc). rewrite HA, optr_eqb_refl. rewrite HL in Hin. destruct Hin as [->|Hin]; [congruence|].
      destruct rest as [|a rest']; [destruct Hin|]. cbn.
      pose proof (il_dll _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as D. rewrite HL in D. cbn [dll app] in D. destruct D as (D1 & _). rewrite Hn in D1. exact D1.
  - intros m1 Hm1. destruct rest as [|a rest']; cbn in Hm1; [discriminate|]. inversion Hm1. subst a.
    assert (Hin : In m1 (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
    destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m1 Hin) as (_ & [bb [aa Hbb]] & _).
    apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
    rewrite HL. cbn. intros E. inversion E. subst m1.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left.
Qed.
End STEPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_upto_all f n : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "P,(1.=O2.)P,(1.=O1.)P,Pi,$4.P,(1.=R1.)P,(3.$27.(28.O2.R2.)$29.)(1.R3.O1.)(3.$4.(2:.O2.(2;.O1.))O2.)")
(* [comment removed for export] *).
Proof.
  intros Hf Hn H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask_upto by lia.
  destruct (Z.testbit f i) eqn:E; [| reflexivity]. cbn. apply Z.leb_le. exact (H i Hi E).
Qed.

Lemma land_mask_upto_zero_above f n : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "P,(1.=O2.)P,(1.=O1.)P,(3.$4.(2:.O2.(2;.O1.))=)Pi,$4.P,(1.=R1.)P,(3.$27.(28.O2.R2.)$29.)(2.O1.R3.)")
(* [comment removed for export] *).
Proof.
  intros Hf Hn H i Hi Hb. destruct (Z.lt_ge_cases n i) as [|LE]; [assumption|]. exfalso.
  assert (T : Z.testbit (Z.land f (mask_upto n)) i = true) by (rewrite Z.land_spec, testbit_mask_upto, Hb by lia; cbn; apply Z.leb_le; lia).
  rewrite H, Z.bits_0 in T. discriminate.
Qed.

Section TRY.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

Definition TA_POST (st st1 : mstate) (first : Z) (LS1 : lhead -> list aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "(0.(2<.O4.O3.Vsc,)(2=.(0.(3.$4.O2.=)(0.(3.$19.(1?.O3.Vsc,)(2>.$8.))(1>.VX,O3.VL,VBL,O1.)))(7.$8.Lg,$8.(7.(2?.$>.$4.)Lbg,(2?.$>.$4.)(7.$4.Lai,$4.(7.$4.Lidx,$4.(0.(26.(3.$4.O2.=))(0.(1.=O2.)(0.(3.$4.(30.O2.)R1.)(0.(3.$19.(1?.O3.Vsc,)(16.$8.R4.))(0.(3.(9.$:.)(;.(2?.$>.$4.)$:.(<.$8.(=.$>.$?.$4.$10.)(11.$>.$?.$12.$4.$10.$13.)$:.)(14.$8.(=.$>.$?.$4.$10.)(11.$>.$?.$12.$4.$10.$13.)$:.)R3.(15.O3.))(16.$:.(17.(16.$8.R4.)R2.)))(0.(0.(1.=R1.)(1.R1.(31.(6.O3.R4.))))(0.(3.$4.(5.(6.O3.R4.))Vsc,)(0.(1.(32.$33.(34.Vsc,))(35.(6.O3.R4.)))(1>.(36.VX,(16.(2?.$>.$4.)(37.$>.$4.(38.$>.$4.R3.)(39.(6.O3.R4.)R1.))))O3.VL,VBL,O1.)))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma set_avail_views v r : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "(0.(3.$4.(31.(3:.O2.O1.))(31.O1.))(0.(3.$4.(5.(3:.O2.O1.))(5.O1.))(0.(3.$4.(35.(3:.O2.O1.))(35.O1.))Pi,$4.(3.$4.(39.(3:.O2.O1.)R1.)(39.O1.R1.)))))")
(* [comment removed for export] *).
Proof. destruct r; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
#[using="HP HF"] Lemma fin_ok st0 st LS m (mask : Z) : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "P,(1>.VX,O4.VL,VBL,O3.)P,(2<.O5.O4.Vsc,)P,(3.$19.(1?.O4.Vsc,)(16.$8.O2.))P,(3.$4.(20.(6.O4.O2.))O1.)P,(26.(3.$4.O1.=))(7.$3;.Lst1,$3;.(7.$4.Lfirst,$4.(7.P,$1;.(1<.$8.)LLS1,P,$1;.(1<.$8.)(0.(3.(3<.VT,)(3=.VT,O4.O2.O1.Vk,)A2.Vk,R3.R2.)(3>.O5.R3.R2.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros INV TF HA AM MNZ. ddestruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  dpose (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|]. split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. dexists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. ddestruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

#[using="HP HF Hsc"] Theorem try_avail_ok st LS : ltac2:(CDefT.buildp (gd_tbl_MI_WTry2 ()) "P,(1>.VX,O2.VL,VBL,O1.)(7.$3;.Lst1,$3;.(7.$4.Lfirst,$4.(7.P,$1;.(1<.$8.)LLS1,P,$1;.(1<.$8.)(0.(3.(3<.VT,)(3?.VT,Vsc,O2.Vk,Vbail,)A2.Vk,R3.R2.)(3>.O2.R3.R2.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [apply taf_refl| left; auto]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_ok st st LS m _ INV (taf_refl st sc) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ TA_frame st st1 sc
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - ddestruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + dexists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + dexists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| apply taf_dequeue].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - ddestruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      dexists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| apply taf_set_active]. }
  ddestruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [apply taf_dequeue| left; auto]. }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ TA_frame st st2 sc).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - dpose G1 as (INV1 & HA1 & _). ddestruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      dexists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| eapply taf_trans; [exact TF1| apply taf_set_active]].
    - dexists st1, m1, LS1. auto. }
  ddestruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & TF2). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
  match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
  cbn iota. fold (MR st2 m2).
  ddestruct G2 as (INV2 & HA2 & AZ2 & FNZ2).
  ddestruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
  pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
  rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
  assert (GAI : group_active_idx st2 b2 = ai2).
  { unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite GAI.
  (* [comment removed for export] *)
  assert (STEP3 : exists st3 m3 LS3 b3 ai3,
    (if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
     then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
          then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
          else (let cnt := ai2 + 2 in
                let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
                let span := UNIT + size * cnt in
                let cnt := span_loop 300 cnt span size in
                let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
                (set_group_active_idx b2 (cnt - 1) st2, m2))
     else (st2, m2)) = (st3, m3)
    /\ GOODH X st3 L BL LS3 sc m3 /\ TA_frame st st3 sc
    /\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
  { destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      ddestruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
        set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
        set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
        pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
        assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
        unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
        replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
        set (st3 := Malloc.set_groups _ st2).
        assert (INV3 : INVL X st3 L BL LS2).
        { apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
          intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
        exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
        split; [split; [exact INV3| split; [exact HA2| auto]]|].
        split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
        split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
        change (MR st3 m2) with (MR st2 m2). intros E0.
        assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
        { rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
        rewrite E0, Z.bits_0 in Tb. discriminate.
      + (* [comment removed for export] *)
        destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
        assert (NEm : mn <> m2) by congruence.
        destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3).
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
        assert (FULL : ai3 = m_last_idx (MR st2 mn)).
        { pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
          apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
        exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
        split; [eapply taf_trans; [exact TF2| apply taf_set_active]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        ddestruct G3 as (_ & _ & _ & F3). exact F3.
    - dexists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  ddestruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & TF3 & Hb3 & ACT).
  match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
  cbn iota. clear E3.
  (* [comment removed for export] *)
  ddestruct G3 as (INV3 & HA3 & AZ3 & FNZ3).
  ddestruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _).
  rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
  pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
  set (st4 := upd_meta m3 _ st3) in INV4 |- *.
  rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
  pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
  set (st5 := decay_bounces _ st4) in INV5 |- *.
  assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
  { transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
  assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
  ddestruct (fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - dexists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRY.

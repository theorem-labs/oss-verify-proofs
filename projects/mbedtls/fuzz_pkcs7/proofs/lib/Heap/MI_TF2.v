(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_Ext MI_Shadow MI_WFree2 MI_WGroup.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_TF2 () : Init.string Init.list := ["Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "Stdlib.NArith.BinNat.N.lt"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.MI_Inv.hosts"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.MI_Inv.cnt_of"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.MI_Inv.sstart"; "OSSVerify.KrLib.Heap.Malloc.IB"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.countable.prod_countable"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.meta"; "geom_kept"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.MI_WGroup.wrs"; "TF2"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.modulo"].


Definition TW (st : mstate) (P : aptr -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "Prid,$0.Psh,$1.Po,$2.Pv,$2.Pt,$0.P,(3.(4.$1.)(5.$0.$1.(6.$0.$7.$8.$1.)(9.$0.$7.$8.$1.)R5.(:.O2.))(;.$1.R4.))P,(3.(4.(<.$2.$0.))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R4.(?.R5.))(;.(<.$2.$0.)(10.$2.$0.R3.R2.)))P,(3.$0.R3.(11.O2.))A1.O1.(10.$0.$2.R8.R6.)")
(* [comment removed for export] *).

Definition TF0 (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "Prid,$0.Psh,$1.Po,$2.Pv,$2.Pt,$0.P,(3.(4.$1.)(5.$0.$1.(6.$0.$7.$8.$1.)(9.$0.$7.$8.$1.)R5.(:.O1.))(;.$1.R4.))P,(3.(4.(<.$2.$0.))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R4.(?.R5.))(;.(<.$2.$0.)(10.$2.$0.R3.R2.)))(12.R3.(11.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition PS (st : mstate) (q : aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "(13.$14.Lb,$14.(13.$14.Lm,$14.(15.(16.O2.R2.R1.)(15.(3.$0.(17.$0.$2.R2.)(17.$0.$2.O1.))(18.(13.$2.Li,$2.(15.(15.(19.=R1.)(19.R1.(1:.(1;.O2.R2.))))(3.$2.(1<.$0.$2.O1.)(1=.(1>.(1;.O2.R2.)R1.)$1?.))))(15.(3.$2.(20.(1;.O2.R1.))=)(15.(19.(1=.(1<.$0.$2.R2.)+3.)(1<.$0.$2.O1.))(19.(1<.$0.$2.O1.)(1=.(1<.$0.$2.R2.)+1.)))))))))")
(* [comment removed for export] *).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

Lemma TF0_TW st P : TF0 st -> TW st P.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 st : TF0 st -> TF2 st. Proof. apply TF0_TW. Qed.
Lemma TF0_TF st : TF0 st -> TF st.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.

Lemma TW_mono st (P P' : aptr -> Prop) : (forall q, P q -> P' q) -> TW st P -> TW st P'.
Proof. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

Lemma TW_ctrl st st' P : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TW st P -> TW st' P.
Proof. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

Lemma TF0_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF0 st -> TF0 st'.
Proof. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Lemma TF0_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF0 (set_tick t st).
Proof.
  intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. ddestruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

Lemma TF0_hdr_havoc st b : TF0 st -> TF0 (hdr_havoc b st).
Proof.
  intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st).
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; eassumption.
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

Lemma TW_hdr_havoc st b P : TW st P -> TW (hdr_havoc b st) P.
Proof.
  intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wr8' st q v P : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
  intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  unfold wr8, upd_shadow in Hs. cbn in Hs.
  destruct (N.eq_dec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
      destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
      eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wrs l : forall st P, TW st P -> (forall q, In q (map fst l) -> P q) -> TW (wrs l st) P.
Proof.
  induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
  apply IH.
  - apply TW_wr8'; [exact H| apply HP; left; reflexivity].
  - intros q' Hq'. apply HP. right. exact Hq'.
Qed.

(* [comment removed for export] *)
Definition geom_kept (st st' : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "Pb,$14.Pm,$14.P,(16.O2.R2.R1.)(15.(16.O1.R3.R2.)(15.Pi,$2.(3.$2.(1>.(1;.O1.R3.)R1.)(1>.(1;.O2.R3.)R1.))(15.(3.$2.(1:.(1;.O1.R2.))(1:.(1;.O2.R2.)))(3.$2.(20.(1;.O1.R2.))(20.(1;.O2.R2.))))))")
(* [comment removed for export] *).

Lemma geom_kept_refl st : geom_kept st st.
Proof. intros b m H. auto. Qed.
Lemma geom_kept_trans a b c : geom_kept a b -> geom_kept b c -> geom_kept a c.
Proof.
  intros H1 H2 bb m H. destruct (H1 _ _ H) as (Hb & S1 & C1 & M1). destruct (H2 _ _ Hb) as (Hc & S2 & C2 & M2).
  split; [exact Hc|]. split; [intros i; rewrite S2; apply S1|]. split; congruence.
Qed.

Lemma PS_mono st st' q : geom_kept st st' -> PS st q -> PS st' q.
Proof.
  (intros GK dd_H; ddestruct dd_H as (b & m & Hm & Hf & ALT)). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
  dexists b, m. split; [exact Hm'|]. split; [exact Hf|].
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - left. exists i. rewrite C, S. auto.
  - right. rewrite ML. auto.
Qed.

Lemma TF2_kept st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> geom_kept st st' -> TF2 st -> TF2 st'.
Proof.
  intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

(* [comment removed for export] *)
Lemma geom_kept_of st st' : ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "P,Pb,$14.Ph,$21.P,(3.(4.$21.)(5.$14.$21.(6.$14.(22.$0.$7.$2.$=.)(23.$0.$7.$8.$2.$=.$>.)$21.)(9.$14.(22.$0.$7.$2.$=.)(23.$0.$7.$8.$2.$=.$>.)$21.)R2.(24.O2.))(;.$21.R1.))(3.(4.$21.)(5.$14.$21.(6.$14.(22.$0.$7.$2.$=.)(23.$0.$7.$8.$2.$=.$>.)$21.)(9.$14.(22.$0.$7.$2.$=.)(23.$0.$7.$8.$2.$=.$>.)$21.)R3.(24.O1.))(;.$21.R2.))P,Pb,$14.Pm,$14.P,(16.O2.R2.R1.)(3.$25.(1;.O1.R2.)(1;.O2.R2.))(26.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  rewrite (HM _ _ Hm). auto.
Qed.

(* [comment removed for export] *)
Lemma wr8_cells_other st q v rid o : (rid, o) <> q ->
  r_cells (get_shadow (wr8 q v st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
  destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
  rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

Lemma wrs_cells_other l : ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "Pst,$27.Prid,$0.Po,$2.P,(28.(29.(<.$0.$2.)(10.$0.$2.R2.R1.)(2:.(<.(<.$0.$2.)$2.)(<.$0.$2.)(17.(<.$0.$2.)$2.)O1.)))(3.(4.(<.$2.$0.))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R2.(?.(2;.(2<.O1.R4.)R3.)))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R2.(?.(2;.R4.R3.))))")
(* [comment removed for export] *).
Proof.
  induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

#[using="X L BL LS INV"] Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. dpose INV as (_ & _ & IM0 & _ & IG0 & _).
  pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="X L BL LS INV Hg Hidx NH IM IG IS"] Lemma PS_not_interior q :
  PS st q -> fst q = fst bg -> ~ (sstart (MR st g) idx <= snd q < sstart (MR st g) (idx + 1) - IB).
Proof.
  (intros dd_H; ddestruct dd_H as (b & m & Hm & Hf & ALT); intros Hq HI). rewrite Hq in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
    + (* [comment removed for export] *)
      assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
    + assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
        destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
  - (* [comment removed for export] *)
    destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
    destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
    destruct LVp as [bp Hp].
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
    assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
    assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
    assert (NE : p <> g \/ ip <> idx).
    { destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
    destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

(* [comment removed for export] *)
#[using="X L BL LS INV Hg Hidx NH IM IG IS"] Lemma TF2_interior_old : ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "P,(2=.Vst,)Po,$2.Pv,$2.Pt,$0.P,(3.(4.(<.$2.$0.))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R3.(?.(2;.Vst,(17.$0.$2.Vbg,))))(;.(<.$2.$0.)(10.$2.$0.R2.R1.)))P,(15.(19.(1>.(1;.Vst,Vg,)Vidx,)R4.)(2>.R4.(1=.(1>.(1;.Vst,Vg,)(2?.Vidx,+1.))$1?.)))(12.R3.(11.Vst,))")
(* [comment removed for export] *).
Proof.
  intros TF o v t Hc Ho. ddestruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

(* [comment removed for export] *)
#[using="X L BL LS INV IG"] Lemma TF2_ghdr_old (p : aptr) : ltac2:(CDefT.buildp (gd_tbl_MI_TF2 ()) "P,(2=.Vst,)P,(3.$2.(30.(1<.$0.$2.O1.)+10.)=)Po,$2.Pv,$2.Pt,$0.P,(15.(19.(1<.$0.$2.O1.)R3.)(2>.R3.(2?.(1<.$0.$2.O1.)+<.)))P,(3.(4.(<.$2.$0.))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R4.(?.(2;.Vst,(17.$0.$2.O1.))))(;.(<.$2.$0.)(10.$2.$0.R3.R2.)))(12.R3.(11.Vst,))")
(* [comment removed for export] *).
Proof.
  intros TF Al o v t Ho Hc. ddestruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="X L BL LS INV IG"] Lemma TF2_TF : TF2 st -> TF st.
Proof.
  intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.

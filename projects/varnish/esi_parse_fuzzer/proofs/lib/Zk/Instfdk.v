(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Geom Mallkgx Mall1es Mall79j KNodes KLink KLinkC MSafe KFrame.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_rejt8 InstDefs InstFree Instjhg Instqy7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Lemma stride_small_proof : forall s LB m st b off g bm i r ar q res,
  heap_wit s LB m st -> In b LB ->
  blk_addr b = r_base r + snd (blk_slot b) + UNIT * off ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res ->
  m_sizeclass (get_meta_rec st g) < 48 -> get_stride (get_meta_rec st g) < 2^31.
Proof.
  intros until res. intros HW Hb HA RB SC.
  pose proof (rb_stride20 _ _ _ _ _ _ _ _ _ _ _ _ RB SC) as S20.
  pose proof (rb_li _ _ _ _ _ _ _ _ _ _ _ _ RB) as LI.
  pose proof (rb_stride _ _ _ _ _ _ _ _ _ _ _ _ RB) as [S16 _].
  unfold UNIT in S16. nia.
Qed.

(* [comment removed for export] *)
Lemma slot_private_proof : forall s LB m st b off g bm i r ar q res y,
  heap_wit s LB m st -> In b LB ->
  blk_addr b = r_base r + snd (blk_slot b) + UNIT * off ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res ->
  In y LB -> y <> b ->
  blk_addr y + blk_size y <= r_base r + snd (blk_slot b) - IB
  \/ r_base r + snd (blk_slot b) + get_stride (get_meta_rec st g) - IB < blk_addr y.
Proof.
  intros until y. intros HW Hb HA RB Hy NE.
  (first [ pose proof (HW) as dR_1; dand5 dR_1 as LB0 PERM Hst MR [BLK AR] | pose proof HW as (LB0 & PERM & Hst & MR & [BLK AR]) ]).
  pose proof (heap_wit_HEAP _ _ _ _ HW) as HP.
  assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  assert (INy : In y LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hy]).
  (first [ pose proof ((OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls6g.Mallttr.areach_inv _ st LB0 AR)) as dR_2; dand8 dR_2 as L LS BL INV LIVE RESV SEC CR | destruct (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls6g.Mallttr.areach_inv _ st LB0 AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]).
  (first [ pose proof (INV) as dR_3; dand7 dR_3 as IR IA IM IL IG IS ISH | pose proof INV as (IR & IA & IM & IL & IG & IS & ISH) ]).
  (first [ pose proof ((Malls6g.LB_geo _ st L BL LS INV LB0 CR b INb)) as dR_4; dex7 dR_4 as cb ob nb mb bmb ib rb; dand13 dR_4 as Kb Cb Sb Hmb Hib Ecb NHb Hrb Krb Ab Ob Nb Fb | pose proof ((Malls6g.LB_geo _ st L BL LS INV LB0 CR b INb)) as dR_4; dand20 dR_4 as cb ob nb mb bmb ib rb Kb Cb Sb Hmb Hib Ecb NHb Hrb Krb Ab Ob Nb Fb | destruct (Malls6g.LB_geo _ st L BL LS INV LB0 CR b INb) as (cb & ob & nb & mb & bmb & ib & rb & Kb & Cb & Sb & Hmb & Hib & Ecb & NHb & Hrb & Krb & Ab & Ob & Nb & Fb) ]).
  (first [ pose proof ((Malls6g.LB_geo _ st L BL LS INV LB0 CR y INy)) as dR_5; dex7 dR_5 as cy oy ny my bmy iy ry; dand13 dR_5 as Ky Cy Sy Hmy Hiy Ecy NHy Hry Kry Ay Oy Ny Fy | pose proof ((Malls6g.LB_geo _ st L BL LS INV LB0 CR y INy)) as dR_5; dand20 dR_5 as cy oy ny my bmy iy ry Ky Cy Sy Hmy Hiy Ecy NHy Hry Kry Ay Oy Ny Fy | destruct (Malls6g.LB_geo _ st L BL LS INV LB0 CR y INy) as (cy & oy & ny & my & bmy & iy & ry & Ky & Cy & Sy & Hmy & Hiy & Ecy & NHy & Hry & Kry & Ay & Oy & Ny & Fy) ]).
  (* [comment removed for export] *)
  pose proof (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hr. rewrite Cb, Ecb in Hr. cbn [fst] in Hr. rewrite Hrb in Hr. inversion Hr; subst rb. clear Hr.
  pose proof (rb_slot _ _ _ _ _ _ _ _ _ _ _ _ RB) as SL. rewrite Cb in SL.
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ SL)) as dR_6; dand3 dR_6 as _ _ ESL | destruct (is_valid _ _ _ IS _ _ _ SL) as (_ & _ & ESL) ]).
  pose proof (is_total _ _ _ IS _ _ _ Hmb Hib) as TOT. rewrite (MI_Geom.slot_start'_eq _ _ _ IM _ _ _ Hmb), <- Ecb in TOT.
  rewrite SL in TOT. inversion TOT; subst mb ib. clear TOT.
  change (MI_Inv.MR st g) with (get_meta_rec st g) in *.
  rewrite Cb, Ecb. cbn [snd]. rewrite Sy, Ay.
  pose proof (sstart_succ st g i) as SSb. pose proof (sstart_succ st my iy) as SSy.
  change (MI_Inv.MR st g) with (get_meta_rec st g) in SSb. change (MI_Inv.MR st my) with (get_meta_rec st my) in SSy, Fy, Hiy, Ecy, Ay |- *.
  destruct (N.eq_dec (fst bmy) (fst bmb)) as [EF|NF].
  - (* [comment removed for export] *)
    rewrite EF, Hrb in Hry. inversion Hry; subst ry. clear Hry.
    assert (NE' : my <> g \/ iy <> i).
    { destruct (aptr_eq_dec my g) as [->|]; [right| now left]. intros ->. apply NE.
      apply (heap_slot_inj s LB m y b HP Hy Hb). rewrite Cb, Cy, Ecb, Ecy, EF. reflexivity. }
    rewrite Ecb in NHb. rewrite Ecy in NHy.
    destruct (sep_ext _ _ _ _ IM IG IS g bmb i Hmb Hib NHb my bmy iy Hmy EF Hiy NE' NHy) as [A|A];
      change (MI_Inv.MR st g) with (get_meta_rec st g) in A; change (MI_Inv.MR st my) with (get_meta_rec st my) in A;
      unfold UNIT, IB in *; [left| right]; lia.
  - (* [comment removed for export] *)
    pose proof MR as (WF & _). (first [ pose proof (WF) as dR_7; dand4 dR_7 as _ WR DJ _ | pose proof WF as (_ & WR & DJ & _) ]).
    destruct (DJ _ _ _ _ Hry Hrb NF) as [A|A]; rewrite ?(lr_lo_group _ Krb), ?(lr_lo_group _ Kry) in A.
    + left. pose proof (rb_c _ _ _ _ _ _ _ _ _ _ _ _ RB) as EC. rewrite Cb, Ecb in EC. cbn [snd] in EC.
      pose proof (rb_b0 _ _ _ _ _ _ _ _ _ _ _ _ RB) as B0. pose proof (rb_si0 _ _ _ _ _ _ _ _ _ _ _ _ RB) as SI0.
      (first [ pose proof ((Mallzvh.rblock_inside_strict st LB0 m y (Malls6g.areach_facts_proof _ _ AR) MR INy)) as dR_8; dex1 dR_8 as r2; dand5 dR_8 as Hr2 _ LO2 HI2 _ | pose proof ((Mallzvh.rblock_inside_strict st LB0 m y (Malls6g.areach_facts_proof _ _ AR) MR INy)) as dR_8; dand6 dR_8 as r2 Hr2 _ LO2 HI2 _ | destruct (Mallzvh.rblock_inside_strict st LB0 m y (Malls6g.areach_facts_proof _ _ AR) MR INy) as (r2 & Hr2 & _ & LO2 & HI2 & _) ]).
      rewrite Cy, Ecy in Hr2. cbn [fst] in Hr2. rewrite Hry in Hr2. inversion Hr2; subst r2.
      rewrite Ay, Sy in HI2. unfold UNIT, IB in *. lia.
    + right. pose proof (rb_span _ _ _ _ _ _ _ _ _ _ _ _ RB) as SPAN. pose proof (rb_c _ _ _ _ _ _ _ _ _ _ _ _ RB) as EC.
      pose proof (rb_i _ _ _ _ _ _ _ _ _ _ _ _ RB) as HI. pose proof (rb_stride _ _ _ _ _ _ _ _ _ _ _ _ RB) as [S16 _].
      rewrite Cb, Ecb in EC. cbn [snd] in EC.
      (first [ pose proof ((Mallzvh.rblock_inside_strict st LB0 m y (Malls6g.areach_facts_proof _ _ AR) MR INy)) as dR_9; dex1 dR_9 as r2; dand5 dR_9 as Hr2 _ LO2 HI2 _ | pose proof ((Mallzvh.rblock_inside_strict st LB0 m y (Malls6g.areach_facts_proof _ _ AR) MR INy)) as dR_9; dand6 dR_9 as r2 Hr2 _ LO2 HI2 _ | destruct (Mallzvh.rblock_inside_strict st LB0 m y (Malls6g.areach_facts_proof _ _ AR) MR INy) as (r2 & Hr2 & _ & LO2 & HI2 & _) ]).
      rewrite Cy, Ecy in Hr2. cbn [fst] in Hr2. rewrite Hry in Hr2. inversion Hr2; subst r2.
      rewrite Ay in LO2.
      assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
      { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
      rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
Qed.

End CEIL.

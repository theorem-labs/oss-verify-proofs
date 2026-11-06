(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5DivInnerSpecsA L5ParseSpecsA L5OpmodSpecsA L5ADivH L5ADivT L5ADivD L5ADivP2 L5ADivE L5ADivEA L5ADivHC L5ADivHD L5ADivHA
     L5ADivHO L5ADivHL L5ADivHP L5ADivGE.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVO1.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA.
Import L5ADVHO. Import L5ADVHL. Import L5ADVHP. Import L5ADVGE.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

(* [comment removed for export] *)
Lemma land2_0 fb : Z.testbit fb 1 = false -> Z.land fb 2 = 0.
Proof.
  intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec n 1) as [->|Ne]. rewrite H. reflexivity.
  change 2 with (2 ^ 1). rewrite Z.pow2_bits_false by (clear - Ne; lia). apply andb_false_r.
Qed.
Lemma adebits_0 L cr : L5OMA.adebits L cr 0 0 = cr.
Proof. destruct cr as [a b]. unfold L5OMA.adebits. cbn [fst snd]. f_equal; ring. Qed.
Lemma inl_limbs (Mk : word -> option byte) o fb n v0 v1 : L5.big_at RSEGS Mk o (L5.BO fb n (L5.BInl v0 v1)) -> L5C.obj_limbs RSEGS Mk (L5.BO fb n (L5.BInl v0 v1)) (firstn n [v0; v1]).
Proof.
  intros (_ & _ & _ & (_ & _ & _ & N2 & V0R & V1R)). cbn [L5.bo_len L5.bo_st] in *. split. cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. clear - N2; lia.
  split. destruct n as [|[|[|n']]]; cbn [firstn]; [constructor | constructor; [exact V0R | constructor] | constructor; [exact V0R | constructor; [exact V1R | constructor]] | exfalso; clear - N2; lia]. reflexivity.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hcpa : copya_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hrsz : resize_spec L ar HI.

(* [comment removed for export] *)
Lemma arg_kept (M Mf : word -> option byte) (model : Model) LB FF LK cr A E SCR W o b ws :
  ri_inv HI LB FF LK cr A M (vml_of model) -> ahpres L ar LB FF E SCR W M Mf -> aobj FF o 32 -> L5ADVEA.tob LB M o b ws -> (forall a, L5ADVEA.oreg o b a -> L5.outside W a) ->
  L5.big_at RSEGS Mf o b /\ L5C.obj_limbs RSEGS Mf b ws.
Proof.
  intros HH0 (EK & _) AOB (OB & OL & SZ & INB) NW.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 E SCR HH0 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (AGO : forall i, o <= i < o + 32 -> Mf (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply EK. split. clear - Hi OR; lia. split. replace i with (o + (i - o)) by (clear; lia). apply OCL. clear - Hi; lia. apply NW. left. exact Hi. }
  split. { eapply L5C.big_at_agree. 4: exact OB. exact AGO. clear - OR; lia. clear - OR; lia. }
  destruct OL as (OL1 & OL2 & OL3). split. exact OL1. split. exact OL2.
  destruct b as [fb len sto]. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q]. exact OL3.
  destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CR & Q8 & Q4096 & Q47 & _)). cbn [L5.bo_len] in LC.
  eapply L5C.limbs_at_agree. 4: exact OL3. 2: clear - Q4096; lia. 2: rewrite OL1; clear - Q47 LC CR; lia.
  intros i Hi. rewrite OL1 in Hi. apply EK. split. clear - Hi Q4096 Q47 LC CR; lia. split.
  apply (block_client L ar LB FF E SCR q (8 * cap) i (INB cap q eq_refl)). clear - Hi LC; lia.
  apply NW. right; right. exists cap, q. split. reflexivity. clear - Hi LC; lia.
Qed.

(* [comment removed for export] *)
Definition gen_O1 : Prop :=
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (xo bo qo E r fbx : Z) (bb : L5.bigobj) (wb : list Z)
         (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx1 : FPState) g1 g2 R1 M1 model1 cr1 LK1 A1 c qn bits bn bd,
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E L5DIA.DIVO_SCR ->
    L5OMA.stksh ar M (E - L5DIA.DIVO_SCR) -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 -> ffrs FF E ->
    L5OMA.x_is_a M xo fbx -> aobj FF xo 32 -> shadow_zero M xo 4 ->
    L5OMA.b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 ->
    L5DIA.zero_obj M qo -> aobj FF qo 32 -> shadow_zero M qo 4 ->
    (xo + 32 <= bo \/ bo + 32 <= xo) -> (xo + 32 <= qo \/ qo + 32 <= xo) -> (bo + 32 <= qo \/ qo + 32 <= bo) ->
    L5.bo_dyn bb = false -> (L5.bo_len bb = 2%nat \/ (L5.bo_len bb = 1%nat /\ exists d0 d1, L5.bo_st bb = L5.BInl d0 d1 /\ 4294967296 <= d0)) ->
    L5OMA.acredit_for L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) ->
    L5AFK.gctx L ar HI LB FF LK A E L5DIA.DIVO_SCR (E - 352) (E - 352) E (docell E) (down E F xo R) F fl 3 LK2 M2 model2 cr ->
    140735332487680 <= E <= 140737488355328 -> U R 1 = r ->
    atG L ar HI R M model LB FF LK A E L5DIA.DIVO_SCR F xo g1 g2 R1 M1 model1 cr1 LK1 A1 xo qo qn bits 1 bn bd [L5PSA.A0; L5PSA.A1] wb ->
    g1 = Same -> g2 = Same -> cr1 = cr -> incl A A1 -> incl LK1 LK ->
    (0 <= c <= 1) -> (L5.bo_len bb = 2%nat -> c = L5CMP.cmp_val [L5PSA.A0; L5PSA.A1] wb) ->
    L5.bo_len bn = 2%nat -> L5.bo_len bd = L5.bo_len bb -> L5.bo_st bn = L5.BInl L5PSA.A0 L5PSA.A1 -> L5.bo_st bd = L5.bo_st bb -> bits = 0 ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        L5DIA.divO1_postA L ar LB FF LK' cr M M' R R' xo bo qo E bb wb LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z),
        L5DIA.divO1_e3A L ar LB FF cr M M' R R' xo qo E F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (L5DIA.ff_o FF E F3a F1b F3b F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K.

(* [comment removed for export] *)
Lemma o1_fin (R Rf : bvmap 5 word) (M Mf : word -> option byte) (model : Model) LB FF LK LK' cr cr9 A xo bo qo E bb wb (Wf : list L5.range) :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  L5OMA.b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 -> aobj FF xo 32 -> aobj FF qo 32 ->
  (xo + 32 <= bo \/ bo + 32 <= xo) -> (bo + 32 <= qo \/ qo + 32 <= bo) -> (1 <= L5.bo_len bb)%nat ->
  regs_preserved R Rf -> ahpres L ar LB FF E L5DIA.DIVO_SCR Wf M Mf -> (forall a, L5.outside [(xo, 32); (qo, 32)] a -> L5.outside Wf a) ->
  (exists fq nq q0 q1, L5.big_at RSEGS Mf qo (L5.BO fq nq (L5.BInl q0 q1))) ->
  (exists fr nr r0 r1, L5.big_at RSEGS Mf xo (L5.BO fr nr (L5.BInl r0 r1)) /\ Z.testbit fr 1 = false) ->
  credit_le (L5OMA.adebits L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb))) cr9 ->
  L5DIA.divO1_postA L ar LB FF LK' cr M Mf R Rf xo bo qo E bb wb LB cr9.
Proof.
  intros HH (OBB & OLB & _ & INB) AOB SZB AOX AOQ APXB APBQ LB1 RP AH WSUB (fq & nq & q0 & q1 & OBQ) (fr & nr & r0 & r1 & OBR & SGR) CRL.
  assert (AHW : ahpres L ar LB FF E L5DIA.DIVO_SCR [(xo, 32); (qo, 32)] M Mf).
  { destruct AH as (EK & DF & DK). split. eapply ek_W. exact EK. exact WSUB. split. exact DF. exact DK. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 E L5DIA.DIVO_SCR HH AOX ltac:(clear; lia) ltac:(reflexivity)) as ((XLO & XCE & XHI & X8 & _) & XBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model qo 32 E L5DIA.DIVO_SCR HH AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model bo 32 E L5DIA.DIVO_SCR HH AOB ltac:(clear; lia) ltac:(reflexivity)) as ((BLO & BCE & BHI & B8 & _) & BBIG & _).
  assert (TB : L5ADVEA.tob LB M bo bb wb). { split. exact OBB. split. exact OLB. split. exact SZB. intros cap q Eq. rewrite Eq in INB. exact INB. }
  destruct (arg_kept M Mf model LB FF LK cr A E L5DIA.DIVO_SCR [(xo, 32); (qo, 32)] bo bb wb HH AHW AOB TB) as (OBBf & OLBf).
  { intros a OR rr Hr IR. unfold L5.in_rng in IR.
    assert (OO : forall o2, aobj FF o2 32 -> (o2 + 32 <= bo \/ bo + 32 <= o2) -> 0x633000 <= o2 -> (0x7fff7000 + 17592186048512 <= o2 \/ o2 + 32 <= 0x7fff7000) -> ~ (o2 <= a < o2 + 32)).
    { intros o2 AO2 AP2 LO2 BIG2 X. destruct OR as [OR|[OR|(cap & q & Eq & OR)]]. clear - OR X AP2; lia.
      unfold SB in OR. clear - OR X BLO BHI LO2 BIG2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). rewrite Eq in INB.
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ INB))))))) as FA. cbn [fst snd] in FA. destruct AO2 as (f & Hf & O1 & O2 & _).
      specialize (FA f (in_or_app _ _ _ (or_introl Hf))). clear - FA O1 O2 OR X. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in IR. exact (OO xo AOX ltac:(clear - APXB; lia) XLO XBIG IR). exact (OO qo AOQ ltac:(clear - APBQ; lia) QLO QBIG IR). }
  split. exact RP.
  split. { exists [], []. split. reflexivity.
    split. { exists (L5.BO fr nr (L5.BInl r0 r1)), (firstn nr [r0; r1]). split. exact OBR. split. apply (inl_limbs Mf xo). exact OBR. split. unfold L5.bo_neg. cbn [L5.bo_fb]. exact SGR. cbn [L5.bo_st]. reflexivity. }
    exists (L5.BO fq nq (L5.BInl q0 q1)), (firstn nq [q0; q1]). split. exact OBQ. split. apply (inl_limbs Mf qo). exact OBQ. cbn [L5.bo_st]. reflexivity. }
  split. exact OBBf. split. exact OLBf. split. exact LB1. split. exact CRL. exact AHW.
Qed.

(* [comment removed for export] *)
Theorem divO1_ok : gen_O1 -> L5DIA.divO1_specA L ar HI.
Proof.
  intros HGEN fx R M model K LB FF LK cr A xo bo qo E r fbx bb wb HH AM HK G10 G11 G12 G13 G14 G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS XA AOX SZX BOK AOB SZB ZQ AOQ SZQ APXB APXQ APBQ CAPB DYN3 CRF KN KE2 KE3.
  pose proof (as0_layout2_of L C LY) as LY2.
  destruct XA as (OBX & SGX). pose proof BOK as (OBB & OLB & REDB & INB).
  pose proof OBX as (_ & _ & _ & (XBT & _ & _ & _ & A0R & A1R)). cbn [L5.bo_fb L5.bo_st] in XBT, A0R, A1R.
  set (bx := L5.BO fbx 2 (L5.BInl L5PSA.A0 L5PSA.A1)) in *.
  assert (TX : L5ADVEA.tob LB M xo bx [L5PSA.A0; L5PSA.A1]).
  { split. exact OBX. split. { split. reflexivity. split. constructor; [exact A0R | constructor; [exact A1R | constructor]]. reflexivity. } split. exact SZX. intros cap q Eq. discriminate Eq. }
  assert (TB : L5ADVEA.tob LB M bo bb wb). { split. exact OBB. split. exact OLB. split. exact SZB. intros cap q Eq. rewrite Eq in INB. exact INB. }
  assert (TQ : L5ADVEA.tob LB M qo (L5.BO 0 0 (L5.BInl 0 0)) []). { split. exact ZQ. split. { split. reflexivity. split. constructor. reflexivity. } split. exact SZQ. intros cap q Eq. discriminate Eq. }
  assert (LBB : Z.of_nat (L5.bo_len bb) <= L5.bo_cap bb). { pose proof OBB as (_ & _ & _ & ST). unfold L5.bo_cap. destruct (L5.bo_st bb) as [v0 v1|cap q]. destruct ST as (_ & _ & _ & L2 & _). clear - L2; lia. destruct ST as (_ & _ & _ & LC & _). exact LC. }
  assert (CAPP : 0 <= L5.bo_cap bb). { clear - LBB. lia. }
  assert (DXF : L5.bo_dyn bx = false) by (unfold L5.bo_dyn, bx; cbn [L5.bo_fb]; exact XBT).
  apply (divO_head L ar C HI LY HIok Hcpa fx R M model K LB FF LK cr A xo bo qo E r bx bb [L5PSA.A0; L5PSA.A1] wb HH AM HK G10 G11 G12 G13 G14 G1 RA G2 A32 G4 STK (ffrk_le 3 FF LK 3 2 FFR3 ltac:(clear; lia)) (ffrk_le 1 FF LK 5 4 FFR1 ltac:(clear; lia)) FFRS TX AOX TB AOB AOQ).
  - cbn [L5.bo_len bx]. clear; lia.
  - clear - LBB CAPB. lia.
  - intros L0. destruct (L5.bo_dyn bb) eqn:DY. specialize (DYN3 eq_refl). exfalso. clear - DYN3 L0. lia. reflexivity.
  - intros DY. split. clear - CAPB; lia. apply (L5OMA.acredit_for_take L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) (8 * L5.bo_cap bb) LY2 CRF). vm_compute; discriminate. unfold L5DIA.divO1_bytes. clear - CAPP; lia.
  - intros cr4 _ DY. exfalso. rewrite DXF in DY. discriminate DY.
  - (* [comment removed for export] *) intros fx' R' M' model' LK' A' F fl L0 E2A RT IA AM' ILK HH'. exact (KE2 fx' R' M' model' LK' A' F fl L0 E2A RT IA AM' ILK HH').
  - intros F fl LK2 M2 model2 fx9 g1 g2 R9 M9 model9 cr9 LK9 A9 c qn bits bn bd G ER UR1 A20 cRS cVAL LNE LDE EBITS LB1 STD STN ECR.
    assert (EA : L5ADIVP2.aligned E 32) by exact A32.
    pose proof (ffrk_le 1 FF LK 5 4 FFR1 ltac:(clear; lia)) as FFR1'.
    assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- G2; reflexivity).
    assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- G4; reflexivity).
    assert (BZ : bits = 0) by (rewrite EBITS; cbn [L5.bo_fb bx]; apply land2_0; exact SGX).
    assert (G2S : g2 = Same). { destruct g2 as [|q2 c2]. reflexivity. exfalso. destruct STN as (_ & _ & DY). rewrite DXF in DY. discriminate DY. }
    subst g2. destruct STN as (STN & _). cbn [L5.bo_st bx] in STN.
    pose proof A20 as (BI9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & TN9 & _).
    pose proof BI9 as (_ & _ & _ & IA9 & ILK9 & _).
    (* [comment removed for export] *)
    assert (CRL : credit_le (L5OMA.adebits L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb))) cr9).
    { rewrite ECR. destruct g1 as [|q1 c1].
      - rewrite <- (adebits_0 L cr) at 2. apply L5OMA.adebits_le. exact LY2. vm_compute; discriminate. unfold L5DIA.divO1_bytes. clear - CAPP; lia.
      - destruct STD as (_ & EC & _). subst c1. rewrite <- L5OMA.adebits_1. apply L5OMA.adebits_le. exact LY2. vm_compute; discriminate. unfold L5DIA.divO1_bytes. clear - CAPP; lia. }
    destruct cRS as ([C0|[C1|CM]] & CLT & CGT).
    3:{ (* [comment removed for export] *) subst c.
      eapply L5ADVHO.early_arm with (qn := qn) (bits := bits) (bn := bn) (bd := bd) (qo := qo) (bt := bx) (wt := [L5PSA.A0; L5PSA.A1]) (bq := L5.BO 0 0 (L5.BInl 0 0)) (wq := []);
        try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact L5ADVHO.divO_scr | exact HH | exact Hdel | exact Hasg | exact RA | exact UR1 | exact G2' | exact FFR1' | exact FFRS];
        [exact A20 | exact TX | exact AOX | exact LNE | cbn [L5.bo_len bx]; clear; lia | exact TQ | exact AOQ | clear - APXQ; lia | intros c0 q0 c' q' Eq; discriminate Eq | ].
      intros fxf Rf Mf modelf Af LKf RPf IAf ILf AHf (stq & TQf & SSQ) (str & TRf & SSR) RTf AMf HHf.
      unfold L5ADVEA.same_store in SSQ, SSR. cbn [L5.bo_st bx] in SSQ, SSR.
      destruct stq as [q0 q1|? ?]. 2: destruct SSQ. destruct str as [r0 r1|? ?]. 2: destruct SSR.
      apply (KN fxf Rf Mf modelf LB cr9 LKf Af).
      + eapply (o1_fin R Rf M Mf model LB FF LK LKf cr cr9 A xo bo qo E bb wb _ HH BOK AOB SZB AOX AOQ APXB APBQ LB1 RPf AHf).
        * intros a O rr [<-|[<-|[<-|[<-|[]]]]] IR; unfold L5.in_rng in IR; cbn [fst snd L5.bo_data L5.bo_st bx] in IR.
          apply (O (xo, 32)). left; reflexivity. exact IR.
          apply (O (xo, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. rewrite LNE in IR. cbn [L5.bo_len bx] in IR. clear - IR; lia.
          apply (O (qo, 32)). right; left; reflexivity. exact IR.
          exfalso. clear - IR; lia.
        * eexists _, _, _, _. exact (proj1 TQf).
        * eexists _, _, _, _. split. exact (proj1 TRf). rewrite BZ. rewrite Z.lor_0_r. rewrite Z.land_spec. change (Z.testbit 253 1) with false. apply andb_false_r.
        * exact CRL.
      + exact RTf.
      + intros x Hx. apply IAf. apply IA9. exact Hx.
      + exact AMf.
      + intros x Hx. apply ILK9. apply ILf. exact Hx.
      + exact HHf. }
    all: assert (CR : 0 <= c <= 1) by (clear - C0 || clear - C1; lia).
    all: assert (LB2 : (L5.bo_len bb <= 2)%nat) by (destruct (Nat.le_gt_cases (L5.bo_len bb) 2) as [X|X]; [exact X | exfalso; cbn [L5.bo_len bx] in CLT; specialize (CLT X); unfold L5CMP.MAXW in CLT; clear - CLT CR; lia]).
    all: assert (DYB : L5.bo_dyn bb = false) by (destruct (L5.bo_dyn bb) eqn:DY; [specialize (DYN3 eq_refl); exfalso; clear - DYN3 LB2; lia | reflexivity]).
    all: assert (G1S : g1 = Same) by (destruct g1 as [|q1 c1]; [reflexivity | exfalso; destruct STD as (_ & _ & DY); rewrite DYB in DY; discriminate DY]).
    all: subst g1; destruct STD as (STD & _); cbn iota in ECR.
    all: pose proof OBB as (_ & _ & _ & STB); destruct (L5.bo_st bb) as [d0 d1|capb qb] eqn:ESB; [|exfalso; destruct STB as (BT & _); unfold L5.bo_dyn in DYB; rewrite BT in DYB; discriminate DYB].
    all: pose proof (proj1 TN9) as OBN9; pose proof OBN9 as (_ & _ & _ & STN9); rewrite STN in STN9; destruct STN9 as (NBT & _).
    all: assert (DYE : L5.bo_dyn bn = L5.bo_dyn bx) by (unfold L5.bo_dyn at 1; rewrite NBT; symmetry; exact DXF).
    all: assert (HALFQ : {L5.bo_len bb = 1%nat /\ d0 <= 4294967295} + {L5.bo_len bb = 2%nat \/ (L5.bo_len bb = 1%nat /\ 4294967296 <= d0)}) by
           (destruct (Nat.eq_dec (L5.bo_len bb) 1) as [L1|L1]; [destruct (Z_le_gt_dec d0 4294967295) as [D|D]; [left; split; assumption | right; right; split; [exact L1 | clear - D; lia]] | right; left; clear - L1 LB1 LB2; lia]).
    all: destruct HALFQ as [(L1 & D0H)|GENC].
    1,3: (* [comment removed for export] *)
      (eapply L5ADVHP.half_path with (c := c) (qn := qn) (bits := bits) (bn := bn) (bd := bd) (qo := qo) (fbx := fbx) (x0 := L5PSA.A0) (x1 := L5PSA.A1) (d0 := d0) (d1 := d1);
        try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact L5ADVHO.divO_scr | exact HH | exact Hdel | exact Hasg | exact Hrsz | exact RA | exact UR1 | exact G2' | exact FFR1' | exact FFRS];
        [exact A20 | exact CR | exact BZ | exact OBX | exact AOX | exact SZX | exact LNE | unfold L5.bo_dyn; exact NBT | rewrite LDE; exact L1 | exact STD
         | split; [destruct STB as (_ & _ & _ & _ & D0R & _); clear - D0R; lia | exact D0H] | exact ZQ | exact AOQ | exact SZQ | clear - APXQ; lia | ];
       intros fxf Rf Mf modelf Af LKf RPf IAf ILf AHf QF RF RTf AMf HHf;
       apply (KN fxf Rf Mf modelf LB cr9 LKf Af);
        [ eapply (o1_fin R Rf M Mf model LB FF LK LKf cr cr9 A xo bo qo E bb wb _ HH BOK AOB SZB AOX AOQ APXB APBQ LB1 RPf AHf); [intros a O; exact O | exact QF | exact RF | exact CRL]
        | exact RTf | intros x Hx; apply IAf; apply IA9; exact Hx | exact AMf | intros x Hx; apply ILK9; apply ILf; exact Hx | exact HHf ]).
    (* [comment removed for export] *)
    all: assert (GENK : forall (fx1 : FPState) R1 M1 model1, atG L ar HI R M model LB FF LK A E L5DIA.DIVO_SCR F xo Same Same R1 M1 model1 cr9 LK9 A9 xo qo qn bits 1 bn bd [L5PSA.A0; L5PSA.A1] wb ->
                       srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K) by
      (intros fx1 R1 M1 model1 AG;
       apply (HGEN R M model K LB FF LK cr A xo bo qo E r fbx bb wb F fl LK2 M2 model2 fx1 Same Same R1 M1 model1 cr9 LK9 A9 c qn bits bn bd HH AM HK G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS (conj OBX SGX) AOX SZX BOK AOB SZB ZQ AOQ SZQ APXB APXQ APBQ DYB);
       [ destruct GENC as [L2|(L1 & D0G)]; [left; exact L2 | right; split; [exact L1 | exists d0, d1; split; [exact ESB | exact D0G]]] | exact CRF | exact G | exact ER | exact UR1 | exact AG | reflexivity | reflexivity | exact ECR | exact IA9 | exact ILK9 | exact CR
       | intros L2; apply cVAL; cbn [L5.bo_len bx]; symmetry; exact L2 | exact LNE | exact LDE | exact STN | rewrite STD, ESB; reflexivity | exact BZ | exact KN | exact KE3 ]).
    all: destruct GENC as [L2|(L1 & D0G)].
    1,3: (eapply L5ADVGE.gen_entry_p4 with (c := c) (qn := qn) (bits := bits) (bn := bn) (bd := bd) (to := xo) (qo := qo) (bt := bx) (wt := [L5PSA.A0; L5PSA.A1]);
           try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact L5ADVHO.divO_scr | exact HH | exact RA | exact UR1 | exact G2' | exact FFR1' | exact FFRS];
           [exact A20 | exact CR | exact TX | exact AOX | exact AOQ | exact DYE | rewrite LDE, L2; clear; lia | exact GENK]).
    all: (eapply L5ADVGE.gen_entry_ht with (c := c) (qn := qn) (bits := bits) (bn := bn) (bd := bd) (to := xo) (qo := qo) (bt := bx) (wt := [L5PSA.A0; L5PSA.A1]) (d0 := d0) (d1 := d1);
           try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact L5ADVHO.divO_scr | exact HH | exact RA | exact UR1 | exact G2' | exact FFR1' | exact FFRS];
           [exact A20 | exact CR | exact TX | exact AOX | exact AOQ | exact DYE | rewrite LDE; exact L1 | rewrite LNE; cbn [L5.bo_len bx]; clear; lia | exact STD | exact D0G | exact GENK]).
Qed.
End WithIface.
End SCFG_1.
End L5ADVO1.

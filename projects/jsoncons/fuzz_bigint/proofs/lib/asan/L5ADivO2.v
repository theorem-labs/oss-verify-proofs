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
     L5ADivHO L5ADivHL L5ADivHP L5ADivGE L5ADivO1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVO2.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA.
Import L5ADVHO. Import L5ADVHL. Import L5ADVHP. Import L5ADVGE. Import L5ADVO1.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.


Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hcpa : copya_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.

(* [comment removed for export] *)
Definition gen_O2 : Prop :=
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (yo ao qo E r fba : Z) (by_ : L5.bigobj) (wy : list Z)
         (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx1 : FPState) g2 R1 M1 model1 cr1 LK1 A1 c qn bits bn bd,
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E L5DIA.DIVO_SCR ->
    L5OMA.stksh ar M (E - L5DIA.DIVO_SCR) -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 -> ffrs FF E ->
    L5OMA.y_ok LB M yo by_ wy -> aobj FF yo 32 -> shadow_zero M yo 4 -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
    L5OMA.a_ok M ao fba -> aobj FF ao 32 -> shadow_zero M ao 4 ->
    L5DIA.zero_obj M qo -> aobj FF qo 32 -> shadow_zero M qo 4 ->
    (yo + 32 <= ao \/ ao + 32 <= yo) -> (yo + 32 <= qo \/ qo + 32 <= yo) -> (ao + 32 <= qo \/ qo + 32 <= ao) ->
    L5OMA.acredit_for L cr L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_)) ->
    L5AFK.gctx L ar HI LB FF LK A E L5DIA.DIVO_SCR (E - 352) (E - 352) E (docell E) (down E F yo R) F fl 3 LK2 M2 model2 cr ->
    140735332487680 <= E <= 140737488355328 -> U R 1 = r ->
    atG L ar HI R M model LB FF LK A E L5DIA.DIVO_SCR F yo Same g2 R1 M1 model1 cr1 LK1 A1 yo qo qn bits 1 bn bd wy [L5PSA.A0; L5PSA.A1] ->
    match g2 with Same => L5.bo_st bn = L5.bo_st by_ /\ L5.bo_dyn by_ = false | Grown q cap => L5.bo_st bn = L5.BDyn cap q /\ cap = L5.bo_cap by_ /\ L5.bo_dyn by_ = true end ->
    cr1 = (match g2 with Same => cr | Grown q2 cap2 => adebit L cr (8 * cap2) end) -> incl A A1 -> incl LK1 LK ->
    (0 <= c <= 1) -> (L5.bo_len by_ = 2%nat -> c = L5CMP.cmp_val wy [L5PSA.A0; L5PSA.A1]) -> (2 <= L5.bo_len by_)%nat ->
    L5.bo_len bn = L5.bo_len by_ -> L5.bo_len bd = 2%nat -> L5.bo_st bd = L5.BInl L5PSA.A0 L5PSA.A1 -> bits = Z.land (L5.bo_fb by_) 2 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        L5DIA.divO2_postA L ar LB FF LK' cr M M' R R' yo ao qo E fba by_ LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K.

(* [comment removed for export] *)
Theorem divO2_ok : gen_O2 -> L5DIA.divO2_specA L ar HI.
Proof.
  intros HGEN fx R M model K LB FF LK cr A yo ao qo E r fba by_ wy HH AM HK G10 G11 G12 G13 G14 G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS YOK AOY SZY LY1 CAPY AOK AOA SZA ZQ AOQ SZQ APYA APYQ APAQ CRF KN.
  pose proof (as0_layout2_of L C LY) as LY2.
  destruct AOK as (OBA & SGA). pose proof YOK as (OBY & OLY & REDY & INY).
  pose proof OBA as (_ & _ & _ & (ABT & _ & _ & _ & A0R & A1R)). cbn [L5.bo_fb L5.bo_st] in ABT, A0R, A1R.
  set (ba := L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) in *.
  assert (TA : L5ADVEA.tob LB M ao ba [L5PSA.A0; L5PSA.A1]).
  { split. exact OBA. split. { split. reflexivity. split. constructor; [exact A0R | constructor; [exact A1R | constructor]]. reflexivity. } split. exact SZA. intros cap q Eq. discriminate Eq. }
  assert (TY : L5ADVEA.tob LB M yo by_ wy). { split. exact OBY. split. exact OLY. split. exact SZY. intros cap q Eq. rewrite Eq in INY. exact (proj1 INY). }
  assert (TQ : L5ADVEA.tob LB M qo (L5.BO 0 0 (L5.BInl 0 0)) []). { split. exact ZQ. split. { split. reflexivity. split. constructor. reflexivity. } split. exact SZQ. intros cap q Eq. discriminate Eq. }
  assert (LYC : Z.of_nat (L5.bo_len by_) <= L5.bo_cap by_). { pose proof OBY as (_ & _ & _ & ST). unfold L5.bo_cap. destruct (L5.bo_st by_) as [v0 v1|cap q]. destruct ST as (_ & _ & _ & L2 & _). clear - L2; lia. destruct ST as (_ & _ & _ & LC & _). exact LC. }
  assert (CAPP : 0 <= L5.bo_cap by_) by (clear - LYC; lia).
  assert (DAF : L5.bo_dyn ba = false) by (unfold L5.bo_dyn, ba; cbn [L5.bo_fb]; exact ABT).
  apply (divO_head L ar C HI LY HIok Hcpa fx R M model K LB FF LK cr A yo ao qo E r by_ ba wy [L5PSA.A0; L5PSA.A1] HH AM HK G10 G11 G12 G13 G14 G1 RA G2 A32 G4 STK (ffrk_le 3 FF LK 3 2 FFR3 ltac:(clear; lia)) (ffrk_le 1 FF LK 5 4 FFR1 ltac:(clear; lia)) FFRS TY AOY TA AOA AOQ).
  - clear - LY1 LYC CAPY. lia.
  - cbn [L5.bo_len ba]. clear; lia.
  - intros L0. exfalso. cbn [L5.bo_len ba] in L0. discriminate L0.
  - intros DY. exfalso. rewrite DAF in DY. discriminate DY.
  - intros cr4 [-> | ->] DY.
    + split. clear - CAPY; lia. apply (L5OMA.acredit_for_take L cr L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_)) (8 * L5.bo_cap by_) LY2 CRF). vm_compute; discriminate. unfold L5DIA.divO2_bytes. clear - CAPP; lia.
    + split. clear - CAPY; lia.
      destruct (L5OMA.acredit_for_take L cr L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_)) (8 * L5.bo_cap ba) LY2 CRF ltac:(vm_compute; discriminate) ltac:(change (L5.bo_cap ba) with 2; unfold L5DIA.divO2_bytes; clear - CAPP; lia)) as (_ & CRF2).
      apply (L5OMA.acredit_for_take L _ _ _ (8 * L5.bo_cap by_) LY2 CRF2). vm_compute; discriminate. change (L5.bo_cap ba) with 2. unfold L5DIA.divO2_bytes. clear - CAPP; lia.
  - (* [comment removed for export] *) intros fx' R' M' model' LK' A' F fl L0. exfalso. cbn [L5.bo_len ba] in L0. discriminate L0.
  - intros F fl LK2 M2 model2 fx9 g1 g2 R9 M9 model9 cr9 LK9 A9 c qn bits bn bd G ER UR1 A20 cRS cVAL LNE LDE EBITS _ STD STN ECR.
    assert (EA : L5ADIVP2.aligned E 32) by exact A32.
    pose proof (ffrk_le 1 FF LK 5 4 FFR1 ltac:(clear; lia)) as FFR1'.
    assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- G2; reflexivity).
    assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- G4; reflexivity).
    assert (G1S : g1 = Same). { destruct g1 as [|q1 c1]. reflexivity. exfalso. destruct STD as (_ & _ & DY). rewrite DAF in DY. discriminate DY. }
    subst g1. destruct STD as (STD & _). cbn [L5.bo_st ba] in STD. cbn iota in ECR.
    pose proof A20 as (BI9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & TN9 & _).
    pose proof BI9 as (_ & _ & _ & IA9 & ILK9 & _).
    assert (CRL : credit_le (L5OMA.adebits L cr L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_))) cr9).
    { rewrite ECR. destruct g2 as [|q2 c2].
      - rewrite <- (adebits_0 L cr) at 2. apply L5OMA.adebits_le. exact LY2. vm_compute; discriminate. unfold L5DIA.divO2_bytes. clear - CAPP; lia.
      - destruct STN as (_ & EC & _). subst c2. rewrite <- L5OMA.adebits_1. apply L5OMA.adebits_le. exact LY2. vm_compute; discriminate. unfold L5DIA.divO2_bytes. clear - CAPP; lia. }
    destruct cRS as (CC & CLT & CGT).
    destruct (Z.eq_dec c 18446744073709551615) as [CM|CNM].
    + (* [comment removed for export] *) subst c.
      eapply L5ADVHO.early_arm with (qn := qn) (bits := bits) (bn := bn) (bd := bd) (qo := qo) (bt := by_) (wt := wy) (bq := L5.BO 0 0 (L5.BInl 0 0)) (wq := []);
        try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact L5ADVHO.divO_scr | exact HH | exact Hdel | exact Hasg | exact RA | exact UR1 | exact G2' | exact FFR1' | exact FFRS];
        [exact A20 | exact TY | exact AOY | exact LNE | clear - LYC CAPY; lia | exact TQ | exact AOQ | clear - APYQ; lia | intros c0 q0 c' q' Eq; discriminate Eq | ].
      intros fxf Rf Mf modelf Af LKf RPf IAf ILf AHf (stq & TQf & SSQ) (str & TRf & SSR) RTf AMf HHf.
      unfold L5ADVEA.same_store in SSQ. cbn [L5.bo_st] in SSQ. destruct stq as [q0 q1|? ?]. 2: destruct SSQ.
      assert (AHW : ahpres L ar LB FF E L5DIA.DIVO_SCR [(yo, 32); (L5.bo_data yo by_, 8 * L5.bo_cap by_); (qo, 32)] M Mf).
      { destruct AHf as (EK & DF & DK). split. 2: split; [exact DF | exact DK]. eapply ek_W. exact EK.
        intros a O rr [<-|[<-|[<-|[<-|[]]]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR.
        apply (O (yo, 32)). left; reflexivity. exact IR.
        apply (O (L5.bo_data yo by_, 8 * L5.bo_cap by_)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. rewrite LNE in IR. clear - IR LYC; lia.
        apply (O (qo, 32)). right; right; left; reflexivity. exact IR.
        exfalso. clear - IR; lia. }
      pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model yo 32 E L5DIA.DIVO_SCR HH AOY ltac:(clear; lia) ltac:(reflexivity)) as ((YLO & YCE & YHI & Y8 & _) & YBIG & _).
      pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model qo 32 E L5DIA.DIVO_SCR HH AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
      pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model ao 32 E L5DIA.DIVO_SCR HH AOA ltac:(clear; lia) ltac:(reflexivity)) as ((ALO & ACE & AHI & A8 & _) & ABIG & _).
      destruct (arg_kept L ar C HI LY HIok M Mf model LB FF LK cr A E L5DIA.DIVO_SCR _ ao ba [L5PSA.A0; L5PSA.A1] HH AHW AOA TA) as (OBAf & _).
      { intros a OR rr Hr IR. unfold L5.in_rng in IR.
        assert (ORA : ao <= a < ao + 32 \/ ao / 8 + SB <= a < ao / 8 + SB + 4). { destruct OR as [OR|[OR|(cap & q & Eq & _)]]. left; exact OR. right; exact OR. discriminate Eq. }
        assert (OO : forall o2, (o2 + 32 <= ao \/ ao + 32 <= o2) -> 0x633000 <= o2 -> (0x7fff7000 + 17592186048512 <= o2 \/ o2 + 32 <= 0x7fff7000) -> ~ (o2 <= a < o2 + 32)).
        { intros o2 AP2 LO2 BIG2 X. unfold SB in ORA. clear - ORA X AP2 ALO AHI LO2 BIG2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in IR. exact (OO yo ltac:(clear - APYA; lia) YLO YBIG IR). 2: exact (OO qo ltac:(clear - APAQ; lia) QLO QBIG IR).
        unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st by_) as [v0 v1|capy qy] eqn:ESY. exact (OO yo ltac:(clear - APYA; lia) YLO YBIG ltac:(clear - IR; lia)).
        pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB _ (proj1 INY)) as ((_ & _ & _ & _ & _ & (_ & APPM & _)) & _ & _ & _ & _ & FA & _). cbn [fst snd] in APPM, FA.
        destruct AOA as (f & Hf & O1 & O2 & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). unfold BIGSHADOW_LO, BIGSHADOW_HI in APPM. unfold SB in ORA.
        clear - ORA IR FA O1 O2 APPM ALO AHI. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      apply (KN fxf Rf Mf modelf LB cr9 LKf Af).
      * split. exact RPf.
        split. { exists [], []. split. reflexivity.
          split. { eexists _, _. split. exact (proj1 TRf). split. exact (proj1 (proj2 TRf)). cbn [L5.bo_st]. unfold L5ADVEA.same_store in SSR.
                   destruct (L5.bo_st by_) as [v0 v1|capy qy]; destruct str as [v0' v1'|cap' q']; [reflexivity | destruct SSR | exact SSR | destruct SSR as (-> & ->); split; [reflexivity | split; reflexivity]]. }
          eexists _, _. split. exact (proj1 TQf). split. exact (proj1 (proj2 TQf)). cbn [L5.bo_st]. reflexivity. }
        split. split. exact OBAf. exact SGA. split. exact CRL. exact AHW.
      * exact RTf.
      * intros x Hx. apply IAf. apply IA9. exact Hx.
      * exact AMf.
      * intros x Hx. apply ILK9. apply ILf. exact Hx.
      * exact HHf.
    + (* [comment removed for export] *)
      assert (CR : 0 <= c <= 1) by (unfold L5CMP.MAXW in CC; clear - CC CNM; lia).
      assert (LY2' : (2 <= L5.bo_len by_)%nat). { destruct (Nat.le_gt_cases 2 (L5.bo_len by_)) as [X|X]. exact X. exfalso. cbn [L5.bo_len ba] in CLT. specialize (CLT X). unfold L5CMP.MAXW in CLT. clear - CLT CNM. lia. }
      assert (DYE : L5.bo_dyn bn = L5.bo_dyn by_).
      { pose proof (proj1 TN9) as (_ & _ & _ & STN9). unfold L5.bo_dyn at 1. destruct g2 as [|q2 c2].
        - destruct STN as (STN & DYF). rewrite DYF. rewrite STN in STN9. destruct (L5.bo_st by_) as [v0 v1|capy qy] eqn:ESY. exact (proj1 STN9).
          exfalso. destruct OBY as (_ & _ & _ & ST). rewrite ESY in ST. unfold L5.bo_dyn in DYF. rewrite (proj1 ST) in DYF. discriminate DYF.
        - destruct STN as (STN & _ & DYT). rewrite DYT. rewrite STN in STN9. exact (proj1 STN9). }
      eapply L5ADVGE.gen_entry_p4 with (c := c) (qn := qn) (bits := bits) (bn := bn) (bd := bd) (to := yo) (qo := qo) (bt := by_) (wt := wy);
        try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact L5ADVHO.divO_scr | exact HH | exact RA | exact UR1 | exact G2' | exact FFR1' | exact FFRS];
        [exact A20 | exact CR | exact TY | exact AOY | exact AOQ | exact DYE | rewrite LDE; cbn [L5.bo_len ba]; clear; lia | ].
      intros fx1 R1 M1 model1 AG.
      apply (HGEN R M model K LB FF LK cr A yo ao qo E r fba by_ wy F fl LK2 M2 model2 fx1 g2 R1 M1 model1 cr9 LK9 A9 c qn bits bn bd HH AM HK G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS YOK AOY SZY LY1 CAPY (conj OBA SGA) AOA SZA ZQ AOQ SZQ APYA APYQ APAQ CRF G ER UR1 AG STN ECR IA9 ILK9 CR).
      * intros L2. apply cVAL. rewrite L2. reflexivity.
      * exact LY2'.
      * exact LNE.
      * rewrite LDE. reflexivity.
      * exact STD.
      * exact EBITS.
      * exact KN.
Qed.
End WithIface.
End SCFG_1.
End L5ADVO2.

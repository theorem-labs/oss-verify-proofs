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
     L5ADivHO L5ADivHL L5ADivHP L5ADivGE L5ADivO1 L5ACopyAS L5ADivHS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVN.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA.
Import L5ADVHO. Import L5ADVHL. Import L5ADVHP. Import L5ADVGE. Import L5ADVO1. Import L5ADVHS.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.



Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hcpa : copya_spec L ar HI.

Lemma divN_scr : 352 + 4656 <= L5DIA.DIVN_SCR. Proof. vm_compute. intros H; discriminate H. Qed.

(* [comment removed for export] *)
Definition gen_N : Prop :=
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (X qX rr dv fdv E r : Z) (bX : L5.bigobj) (wX : list Z)
         (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx1 : FPState) q2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd,
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E L5DIA.DIVN_SCR ->
    L5OMA.stksh ar M (E - L5DIA.DIVN_SCR) -> ffrk 1 FF LK 4 -> ffrk 3 FF LK 2 -> ffrs FF E ->
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
    Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> aobj FF X 32 -> shadow_zero M X 4 ->
    L5DIA.mword_obj M dv fdv -> L5DIA.stkobj ar E dv 32 -> L5.defined M dv 32 ->
    L5DIA.zero_obj M rr -> aobj FF rr 32 -> shadow_zero M rr 4 -> (X + 32 <= rr \/ rr + 32 <= X) ->
    L5OMA.acredit_for L cr L5DIA.DIVN_K L5DIA.DIVN_BYTES ->
    L5AFK.gctx L ar HI LB FF LK A E L5DIA.DIVN_SCR (E - 352) (E - 352) E (docell E) (down E F rr R) F fl 3 LK2 M2 model2 cr ->
    140735332487680 <= E <= 140737488355328 -> U R 1 = r ->
    atG L ar HI R M model LB FF LK A E L5DIA.DIVN_SCR F rr Same (Grown q2 8) R1 M1 model1 cr1 LK1 A1 X X qn bits 0 bn bd wX [L5DSA.MWORD] ->
    cr1 = adebit L cr 64 -> incl A A1 -> incl LK1 LK ->
    L5.bo_len bn = L5.bo_len bX -> L5.bo_st bn = L5.BDyn 8 q2 -> L5.bo_len bd = 1%nat -> L5.bo_st bd = L5.BInl L5DSA.MWORD 0 -> bits = 0 -> qn = 0 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        L5DIA.divN_postA L ar LB FF LK' cr M M' R R' X qX rr dv fdv E LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F3 fl3 F1c fl1c F1d fl1d : Z),
        L5DIA.divN_e3A L ar LB FF cr M M' R R' X qX (L5.bo_len bX) rr dv E F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (L5DIA.ff_n FF E F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K.

(* [comment removed for export] *)
Theorem divN_ok : L5ACPAS.copya_ssrc_spec L ar HI -> gen_N -> L5DIA.divN_specA L ar HI.
Proof.
  intros Hcpss HGEN fx R M model K LB FF LK cr A X qX rr dv fdv E r bX wX HH AM HK G10 G11 G12 G13 G14 G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS OBX OLX STX LX SGX INX AOX SZX MW SO DFD ZR AOR SZR APXR CRF KN KE3.
  pose proof (as0_layout2_of L C LY) as LY2.
  destruct MW as (OBD & SGD0).
  pose proof OBD as (_ & _ & _ & (DBT & _ & _ & _ & MWR & _)). cbn [L5.bo_fb L5.bo_st] in DBT, MWR.
  set (bdn := L5.BO fdv 1 (L5.BInl L5DSA.MWORD 0)) in *.
  assert (TX : L5ADVEA.tob LB M X bX wX). { split. exact OBX. split. exact OLX. split. exact SZX. intros cap q Eq. rewrite STX in Eq. injection Eq as <- <-. exact INX. }
  assert (DXT : L5.bo_dyn bX = true). { pose proof OBX as (_ & _ & _ & ST). rewrite STX in ST. unfold L5.bo_dyn. exact (proj1 ST). }
  assert (CAPX : L5.bo_cap bX = 8) by (unfold L5.bo_cap; rewrite STX; reflexivity).
  assert (DDF : L5.bo_dyn bdn = false) by (unfold L5.bo_dyn, bdn; cbn [L5.bo_fb]; exact DBT).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model X 32 E L5DIA.DIVN_SCR HH AOX ltac:(clear; lia) ltac:(reflexivity)) as ((XLO & XCE & XHI & X8 & _) & XBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model rr 32 E L5DIA.DIVN_SCR HH AOR ltac:(clear; lia) ltac:(reflexivity)) as ((RLO & RCE & RHI & R8 & _) & RBIG & _).
  pose proof STK as (A16 & SLO & SHI & SPT & _).
  destruct SO as (SO1 & SO2 & SO3).
  assert (ER0 : 140735332487680 <= E <= 140737488355328) by (pose proof divN_scr as HS0; clear - SLO SHI SPT HS0; lia).
  assert (SZDV : shadow_zero M dv 4).
  { intros j Hj. unfold L5OMA.stksh in STKSH. unfold byte_at, S.
    assert (Q : dv / 8 + SB + j = S (E - L5DIA.DIVN_SCR) + ((dv - (E - L5DIA.DIVN_SCR)) / 8 + j) /\ 0 <= (dv - (E - L5DIA.DIVN_SCR)) / 8 + j < (Z.max (ar_sptop ar) (ar_stack_top ar) - (E - L5DIA.DIVN_SCR)) / 8).
    { unfold S. change L5DIA.DIVN_SCR with 5008. clear - Hj SO1 SO2 SO3 A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    destruct Q as (Q1 & Q2). rewrite Q1. apply (STKSH _ Q2). }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (head1_ss L ar C HI LY HIok Hcpss L5DIA.DIVN_SCR fx R M model K LB FF LK cr A X dv X rr 0 E r bdn [L5DSA.MWORD] divN_scr HH AM HK G10 G11 G12 G13 G14);
    [clear - XLO XHI; lia | clear - SO1 SO2 ER0 SPT; lia | clear - XLO XHI; lia | clear - RLO RHI; lia | clear; lia | exact G1 | exact RA | exact G2 | exact A32 | exact G4 | exact STK | exact FFR3 | exact FFR1 | exact FFRS
     | exact OBD | exact DDF | split; [exact SO1 | split; [exact SO2 | exact SO3]] | exact DFD | exact SZDV | ].
  intros F fl LK2 M2 model2 fx4 R3 R4 M3 model3 M4 model4 g1 LBn cr4 LK4 A4 fbo G ER UR1 BI3 BI4 RI3 RP4 XS POST FBR DSH3 SZD3 HDR3 (OBD3 & DFD3 & SZDV3).
  assert (EA : L5ADIVP2.aligned E 32) by exact A32.
  assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- G2; reflexivity).
  assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- G4; reflexivity).
  pose proof (NUM L ar HI R LB FF LK A E L5DIA.DIVN_SCR F fl rr LK2 M2 model2 cr G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : (F + 32) / 8 = F / 8 + 4 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (TD3 : L5ADVEA.tob ([] ++ LB) M3 dv bdn [L5DSA.MWORD]).
  { split. exact OBD3. split. { split. reflexivity. split. constructor; [exact MWR | constructor]. reflexivity. } split. exact SZDV3. intros cap q Eq. discriminate Eq. }
  destruct (copied L ar C HI LY HIok R M model LB FF LK A E L5DIA.DIVN_SCR F fl rr LK2 M2 model2 cr G ER [] [] M3 model3 LK2 cr A M4 R3 R4 32 dv fbo bdn [L5DSA.MWORD] g1 LBn cr4 LK4 BI3 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) TD3 SZD3 POST)
    as (bd & TD4 & LNE & FNE & STD & OFF4).
  assert (G1S : g1 = Same). { destruct g1 as [|q1 c1]. reflexivity. exfalso. destruct STD as (_ & _ & DY). rewrite DDF in DY. discriminate DY. }
  subst g1. destruct STD as (STD & _). cbn [L5.bo_st bdn] in STD.
  assert (CR4 : cr4 = cr). { destruct POST as (_ & (_ & _ & X0 & _)). exact X0. }
  assert (DSH4 : dsh M4 F 248 248 248 248 248).
  { eapply dsh_keep; [exact G | exact ER | exact DSH3 | exact OFF4 | ]. intros j Hj (rr0 & [Er|[]] & IR). subst rr0. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hj IR SHQ FBIG. lia. }
  assert (HDR4 : L5.u64_at RSEGS M4 F 1102416563).
  { eapply hdr_keep; [exact G | exact HDR3 | exact OFF4 | ]. intros i Hi (rr0 & [Er|[]] & IR). subst rr0. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hi IR. lia. }
  destruct XS as (X18 & X19 & X20 & X21 & X22 & X23 & X24 & X27 & X25 & X26).
  assert (RIH4 : L5ADVHC.rinvH R E F R4).
  { split. apply (rinvD_pres R E R3 R4 RI3 RP4). split. rewrite (cs_of_preserved R3 R4 18 RP4) by inl. exact X18. split. rewrite (cs_of_preserved R3 R4 23 RP4) by inl. exact X23.
    split. rewrite (cs_of_preserved R3 R4 27 RP4) by inl. exact X27. rewrite (cs_of_preserved R3 R4 25 RP4) by inl. exact X25. }
  eapply (head2 L ar C HI LY HIok Hcpa R M model K LB FF LK A cr E L5DIA.DIVN_SCR F fl rr LK2 M2 model2 cr G ER EA HK G4' divN_scr FFR1 FFRS HH fx4 R4 M4 model4 LK4 cr4 A4 _ X X 0 bd [L5DSA.MWORD] bX wX);
    [exact BI4 | exact RIH4 | rewrite (cs_of_preserved R3 R4 19 RP4) by inl; exact X19 | rewrite (cs_of_preserved R3 R4 20 RP4) by inl; exact X20 | rewrite (cs_of_preserved R3 R4 22 RP4) by inl; exact X22
     | rewrite (cs_of_preserved R3 R4 24 RP4) by inl; exact X24 | exact TD4 | rewrite LNE; cbn [L5.bo_len bdn]; clear; lia | exact DSH4 | exact HDR4 | exact TX | exact AOX | clear - LX; lia | clear - XLO XHI; lia | clear; lia | | ].
  { intros _. rewrite CR4, CAPX. split. clear; lia. apply (L5OMA.acredit_for_take L cr L5DIA.DIVN_K L5DIA.DIVN_BYTES 64 LY2 CRF). vm_compute; discriminate. vm_compute. split; discriminate. }
  intros fx9 R9 M9 model9 c g2 cr9 LK9 A9 bn fbo2 BI9 RIH9 c10 cRS cVAL c22 c24 TN9 LNEn FNEn STN TD9 (S88 & S48 & S104 & S144 & S64) CR9 IA9 ILK9 c19 c20 c26 DSH9 HDR9.
  destruct g2 as [|q2 cap2]. { exfalso. destruct STN as (_ & DY). rewrite DXT in DY. discriminate DY. }
  destruct STN as (STN & ECAP & _). rewrite CAPX in ECAP. subst cap2.
  change (match Same with Same => [] | Grown q cap => [(q, 8 * cap)] end) with (@nil (Z * Z)) in BI9, TN9, TD9.
  pose proof (bx_eq Same (Grown q2 8)) as BXE. cbn iota in BXE. rewrite BXE in BI9, TN9, TD9.
  pose proof (L5ADVHC.qn_rng (L5.bo_fb bd) (L5.bo_fb bX) (proj1 (proj2 (proj1 TD4))) (proj1 (proj2 OBX))) as (QNR & BITS).
  pose proof (L5ADVHC.fb_clr (L5.bo_fb bd) (proj1 (proj2 (proj1 TD4)))) as (_ & _ & SGD).
  set (bn9 := L5.BO (Z.land (L5.bo_fb bn) 253) (L5.bo_len bn) (L5.bo_st bn)) in *. set (bd9 := L5.BO (Z.land (L5.bo_fb bd) 253) (L5.bo_len bd) (L5.bo_st bd)) in *.
  assert (A20 : at20 L ar HI R M model LB FF LK A E L5DIA.DIVN_SCR F rr Same (Grown q2 8) R9 M9 model9 cr9 LK9 A9 c X X
                     (Z.lxor (Z.land (L5.bo_fb bd) 2) (Z.land (L5.bo_fb bX) 2) / 2) (Z.land (L5.bo_fb bX) 2) 0 bn9 bd9 wX [L5DSA.MWORD]).
  { split. exact BI9. split. exact RIH9. split. exact c10. split. exact c19. split. cbn [L5.bo_len bd9]. exact c20. split. exact c22. split. exact c24. split. exact c26.
    split. exact QNR. split. exact BITS. split. exact TN9. split. exact TD9.
    split. { eapply obj_at_copy. exact (proj1 TN9). exact OBX. cbn [L5.bo_st bn9]. exact STN. }
    split. { eapply obj_at_copy. exact (proj1 TD9). exact OBD. cbn [L5.bo_st bd9]. split. exact STD. exact DDF. }
    split. { cbn [L5.bo_fb bn9]. rewrite Z.land_spec. change (Z.testbit 253 1) with false. apply andb_false_r. }
    split. exact SGD. split. exact S88. split. exact S48. split. exact S104. split. exact S144. split. exact S64. split. exact DSH9. exact HDR9. }
  assert (C1 : c = 1). { destruct cRS as (_ & _ & CGT). apply CGT. rewrite LNE. cbn [L5.bo_len bdn]. clear - LX. lia. }
  assert (DYE : L5.bo_dyn bn9 = L5.bo_dyn bX). { rewrite DXT. pose proof (proj1 TN9) as (_ & _ & _ & ST9). cbn [L5.bo_st bn9] in ST9. rewrite STN in ST9. unfold L5.bo_dyn. exact (proj1 ST9). }
  eapply L5ADVGE.gen_entry_ht with (c := c) (bn := bn9) (bd := bd9) (to := X) (qo := X) (bt := bX) (wt := wX) (d0 := L5DSA.MWORD) (d1 := 0)
      (qn := Z.lxor (Z.land (L5.bo_fb bd) 2) (Z.land (L5.bo_fb bX) 2) / 2) (bits := Z.land (L5.bo_fb bX) 2);
    try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4' | exact divN_scr | exact HH | exact RA | exact UR1 | exact G2' | exact FFR1 | exact FFRS];
    [exact A20 | rewrite C1; clear; lia | exact TX | exact AOX | exact AOX | exact DYE | cbn [L5.bo_len bd9]; rewrite LNE; reflexivity | cbn [L5.bo_len bn9]; rewrite LNEn; clear - LX; lia
     | cbn [L5.bo_st bd9]; exact STD | vm_compute; discriminate | ].
  intros fx1 R1 M1 model1 AG.
  pose proof BI9 as (_ & _ & _ & IAA & ILL & _).
  apply (HGEN R M model K LB FF LK cr A X qX rr dv fdv E r bX wX F fl LK2 M2 model2 fx1 q2 R1 M1 model1 cr9 LK9 A9 _ _ bn9 bd9 HH AM HK G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS OBX OLX STX LX SGX INX AOX SZX
           (conj OBD SGD0) (conj SO1 (conj SO2 SO3)) DFD ZR AOR SZR APXR CRF G ER UR1 AG).
  - rewrite CR9, CR4. reflexivity.
  - exact IAA.
  - exact ILL.
  - cbn [L5.bo_len bn9]. exact LNEn.
  - cbn [L5.bo_st bn9]. exact STN.
  - cbn [L5.bo_len bd9]. rewrite LNE. reflexivity.
  - cbn [L5.bo_st bd9]. exact STD.
  - apply land2_0. exact SGX.
  - rewrite (land2_0 _ SGX). rewrite FNE, DDF. rewrite (land2_0 (copy_fb fbo (L5.bo_fb bdn) false)). reflexivity.
    unfold copy_fb. cbn [L5.bo_fb bdn]. rewrite !Z.lor_spec, !Z.land_spec, SGD0. change (Z.testbit 252 1) with false. rewrite andb_false_r. reflexivity.
  - exact KN.
  - exact KE3.
Qed.
End WithIface.
End SCFG_1.
End L5ADVN.

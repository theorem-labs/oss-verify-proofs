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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivHL L5ADivHM L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB L5ADivGC L5ADivGD L5ADivGU L5ARed L5ADivHH L5ADivHS L5ADivGE L5ADivN L5ADivO1 L5ANorm L5ADivGN L5ADivGK L5ARzHuge L5ADivGK2 L5ADivGK3 L5ADivO2 L5ADivGO2 L5ADivGO2b L5ADivGO2c BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO2D.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGO2. Import L5ADVGO2B. Import L5ADVGO2C. Import L5ADVGK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 352).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 352 + 4656 <= SCRD.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis Hcps : L5ACPAS.copya_stk_spec L ar HI.
Hypothesis Hnorm : L5DLA.norm_specA L ar HI.
Hypothesis Hrsz : resize_spec L ar HI.
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).
Local Notation offx := (L5ADVEA.offx L ar FF E F).
Local Notation tob := (L5ADVEA.tob).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation G1 := (L5ADVGA.g1 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G2s := (L5ADVGA.g2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G3 := (L5ADVGA.g3 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hnorm).
Local Notation G4s := (L5ADVGA.g4 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G5 := (L5ADVGA.g5 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR).
Local Notation G6 := (L5ADVGB.g6 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G7 := (L5ADVGC.g7 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation G7b := (L5ADVGC.g7b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8 := (L5ADVGC.g8 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8b := (L5ADVGC.g8b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G9 := (L5ADVGC.g9 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation RSZ := (L5ADVHH.resize_stage L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation ARG_AFTER := (L5ADVGN.arg_after L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation OREG_DISJ := (L5ADVGN.oreg_disj L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation GN_FRONT := (L5ADVGN.gn_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps Hnorm).
Local Notation G12C := (L5ADVGN.g12_copies L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation NORM_TOBS := (L5ADVGN.norm_tobs L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation STK_DEST := (L5ADVGN.stk_dest L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation ARSZ2 := (L5ADVGK3.arg_resize2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation G6A2 := (L5ADVGK3.g6_arg2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G5A := (L5ADVGK2.g5_arg L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR).
Local Notation G9A := (L5ADVGK2.g9_arg L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation ARG_AT := (L5ADVHA.arg_at L ar C HI LY HIok R M model LB FF LK A).
Local Notation trk := (L5ADVGO2.trk LB E F).
Local Notation TRK_KEEP := (L5ADVGO2.trk_keep L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation TRK_KEEP_ARG := (L5ADVGO2.trk_keep_arg L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation INV_HEAD := (L5ADVGO2.inv_head_fresh L ar C HI HIok).
Local Notation INV_APART := (L5ADVGO2.inv_blk_apart L ar C HI HIok).
Local Notation OFFX_WEAKEN := (L5ADVGO2.offx_weaken L ar FF E F).
Local Notation G11N := (L5ADVGD.g11 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation G12N := (L5ADVGD.g12 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G13N := (L5ADVGD.g13 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G14N := (L5ADVGD.g14 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR Hdel).
Local Notation G9T := (L5ADVGO2B.g9_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation GBT := (L5ADVGO2B.gB_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation G7T := (L5ADVGO2B.g7_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation MID1 := (L5ADVGO2.go2_mid1 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg Hrsz).
Local Notation FRONT := (L5ADVGO2.go2_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps Hnorm).
Local Notation GEN_BACK := (L5ADVGO2C.gen_back L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hdel RA UR1 G2).
Local Notation cinv := (L5ADVGO2C.cinv L).
Local Notation cinv_for := (L5ADVGO2C.cinv_for L C LY).
Local Notation cinv_debit := (L5ADVGO2C.cinv_debit L).
Local Notation cinv_weak := (L5ADVGO2C.cinv_weak L).
Local Notation cinv_fin := (L5ADVGO2C.cinv_fin L C LY).
Local Notation SH_OBJ := (L5ADVGO2C.sh_off_obj L ar C HI LY HIok R M model LB FF LK A E SCRD F ro).
Local Notation SH_BLK := (L5ADVGO2C.sh_off_blk L ar C HI LY HIok R M model LB FF LK A E SCRD F ro).
Local Notation DIST5 := (L5ADVGO2C.dist5 L ar C HI HIok R M model LB FF LK A E SCRD F ro).

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incell := solve [cbn [In]; repeat (first [left; reflexivity | right])].
Lemma go2_all (ao qo fba : Z) (by_ : L5.bigobj) (wy : list Z) (fx1 : FPState) g2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd (Hunn : L5DIA.unnorm_specA L ar HI) :
  ri_inv HI LB FF LK cr2 A M (vml_of model) -> SCRD = L5DIA.DIVO_SCR ->
  L5OMA.stksh ar M (E - SCRD) -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 ->
  L5OMA.y_ok LB M ro by_ wy -> aobj FF ro 32 -> shadow_zero M ro 4 -> L5.bo_cap by_ <= 268 ->
  L5OMA.a_ok M ao fba -> aobj FF ao 32 -> shadow_zero M ao 4 ->
  L5DIA.zero_obj M qo -> aobj FF qo 32 -> shadow_zero M qo 4 ->
  (ro + 32 <= ao \/ ao + 32 <= ro) -> (ro + 32 <= qo \/ qo + 32 <= ro) -> (ao + 32 <= qo \/ qo + 32 <= ao) ->
  L5OMA.acredit_for L cr2 L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_)) ->
  atG L ar HI R M model LB FF LK A E SCRD F ro Same g2 R1 M1 model1 cr1 LK1 A1 ro qo qn bits 1 bn bd wy WA ->
  match g2 with Same => L5.bo_st bn = L5.bo_st by_ /\ L5.bo_dyn by_ = false | Grown q cap => L5.bo_st bn = L5.BDyn cap q /\ cap = L5.bo_cap by_ /\ L5.bo_dyn by_ = true end ->
  cr1 = (match g2 with Same => cr2 | Grown q2 cap2 => adebit L cr2 (8 * cap2) end) -> incl A A1 -> incl LK1 LK ->
  (2 <= L5.bo_len by_)%nat -> L5.bo_len bn = L5.bo_len by_ -> L5.bo_len bd = 2%nat -> L5.bo_st bd = L5.BInl L5PSA.A0 L5PSA.A1 -> bits = Z.land (L5.bo_fb by_) 2 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
      L5DIA.divO2_postA L ar LB FF LK' cr2 M M' R R' ro ao qo E fba by_ LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K.
Proof.
  intros HH0 ESCR SSH FFR5 FFR3 YOK AOR SZR CAPY AOK AOA SZA ZQ AOQ SZQ APYA APYQ APAQ CRF ATG G2F ECR1 IA1 ILK1 LY2 LNE LDE STD EBITS KF.
  pose proof YOK as (OBY & OLY & REDY & INY0). pose proof OLY as (LWY & WYOK & _).
  pose proof ATG as (BI0 & RI0 & X18 & X22 & X24 & X25 & X26 & QNR & BITSR & TN & TD & ON & OD & SGN_N & SGN_D & SPL & DSH & HDR).
  assert (TY : tob LB M ro by_ wy). { split. exact OBY. split. exact OLY. split. exact SZR. intros cap q Eq. rewrite Eq in INY0. exact (proj1 INY0). }
  assert (TQ0 : tob LB M qo (L5.BO 0 0 (L5.BInl 0 0)) []). { split. exact ZQ. split. { split. reflexivity. split. constructor. reflexivity. } split. exact SZQ. intros cap q Eq. discriminate Eq. }
  assert (INY : forall cap q, L5.bo_st by_ = L5.BDyn cap q -> In (q, 8 * cap) LB). { intros cap q Eq. rewrite Eq in INY0. exact (proj1 INY0). }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model ro 32 E SCRD HH0 AOR ltac:(clear; lia) ltac:(reflexivity)) as ((RLO & RCE & RHI & R8 & _) & RBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model qo 32 E SCRD HH0 AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  pose proof (dyn_kind M ro by_ OBY) as DKY.
  pose proof (len_le_cap M ro by_ OBY) as LCY. fold (L5.bo_cap by_) in LCY.
  set (rn := shl_words wy 2) in *. set (nn := rlen rn) in *.
  assert (TOPY : nth_w wy (L5.bo_len by_ - 1) <> 0). { destruct REDY as [->|X0]. cbn [length] in LWY. exfalso. clear - LWY LY2. lia. rewrite LWY in X0. exact X0. }
  destruct (go2_vals wy WYOK ltac:(rewrite LWY; exact LY2) ltac:(rewrite LWY; exact TOPY)) as (NNB & BARM). fold rn in NNB, BARM. fold nn in NNB, BARM. rewrite LWY in NNB, BARM.
  (* [comment removed for export] *)
  assert (YALT : (L5.bo_dyn by_ = true /\ exists q2, g2 = Grown q2 (L5.bo_cap by_) /\ L5.bo_st bn = L5.BDyn (L5.bo_cap by_) q2 /\ Z.of_nat (L5.bo_len by_) + 1 <= L5.bo_cap by_ /\ exists qy, L5.bo_st by_ = L5.BDyn (L5.bo_cap by_) qy)
               \/ (L5.bo_dyn by_ = false /\ g2 = Same /\ L5.bo_cap by_ = 2 /\ L5.bo_len by_ = 2%nat /\ (nn <= 3)%nat /\ skind (L5.bo_st by_) = None /\ skind (L5.bo_st bn) = None)).
  { destruct g2 as [|q2 cap2].
    - right. destruct G2F as (EST & DYF). split. exact DYF. split. reflexivity. rewrite DYF in DKY. unfold L5.bo_cap in *. destruct (L5.bo_st by_) as [v0 v1|c0 q0] eqn:EY. 2: discriminate DKY.
      split. reflexivity. assert (L5.bo_len by_ = 2%nat) by (clear - LCY LY2; lia). split. assumption. split. clear - NNB H; lia. split. reflexivity. rewrite EST. reflexivity.
    - left. destruct G2F as (EST & -> & DYT). split. exact DYT. exists q2. split. reflexivity. split. exact EST. rewrite DYT in DKY. unfold L5.bo_cap in *. destruct (L5.bo_st by_) as [v0 v1|c0 q0] eqn:EY. discriminate DKY.
      split. exact (proj2 INY0). exists q0. reflexivity. }
  set (BB := L5DIA.divO2_bytes (L5.bo_cap by_)) in *.
  set (EQ := 8 * (Z.of_nat nn + 7)). set (ER0 := if L5.bo_dyn by_ then 0 else 8 * (Z.of_nat nn + 9)). set (DR0 := if L5.bo_dyn by_ then 0 else 1).
  assert (CAPBN : L5.bo_cap bn = L5.bo_cap by_).
  { destruct YALT as [(_ & q2 & _ & EST & _)|(_ & _ & C2 & _ & _ & _ & KN)]. unfold L5.bo_cap at 1. rewrite EST. reflexivity. rewrite C2. unfold L5.bo_cap. unfold skind in KN. destruct (L5.bo_st bn). reflexivity. discriminate KN. }
  assert (CINV1 : cinv cr2 cr1 L5DIA.DIVO2_K BB (3 + (1 + DR0)) ((8 * L5.bo_cap bn + 144) + (EQ + ER0))).
  { rewrite CAPBN. unfold L5ADVGO2C.cinv. unfold L5DIA.DIVO2_K, BB, L5DIA.divO2_bytes, L5DIA.DIVN_K, L5DIA.DIVN_BYTES. subst DR0 ER0 EQ.
    destruct YALT as [(DYT & q2 & -> & _ & SLK & _)|(DYF & -> & C2 & _ & N3 & _)].
    - rewrite DYT. cbv iota. exists 1, (8 * L5.bo_cap by_). rewrite L5OMA.adebits_1. split. exact ECR1. clear - SLK NNB LCY. Lia.lia.
    - rewrite DYF. cbv iota. exists 0, 0. rewrite L5ADVO1.adebits_0. split. exact ECR1. rewrite C2. clear - N3. Lia.lia. }
  apply (FRONT cr2 qo wy fx1 g2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd HH0 SSH ltac:(clear - RLO RHI; lia) ltac:(clear - QLO QHI; lia) ltac:(rewrite LNE; exact LY2) ltac:(rewrite CAPBN; exact CAPY) ltac:(rewrite LNE; exact TOPY)).
  { intros cap q Eq. rewrite LNE. destruct YALT as [(_ & q2 & -> & EST & SLK & _)|(_ & _ & _ & _ & _ & _ & KN)]. rewrite EST in Eq. injection Eq as <- <-. split. reflexivity. exact SLK.
    rewrite Eq in KN. discriminate KN. }
  { apply (cinv_for cr2 cr1 _ _ _ _ 3 (8 * L5.bo_cap bn + 144) CINV1 CRF). subst DR0. destruct (L5.bo_dyn by_); clear; lia.
    subst EQ ER0. pose proof (one_le_cap M1 _ bn (proj1 TN)) as X0. fold (L5.bo_cap bn) in X0. destruct (L5.bo_dyn by_); clear - X0; lia. }
  { exact ATG. } { exact LDE. } { exact STD. }
  intros fx4 R4 M4 model4 gn0 gn qd bn0 bd0 fbd' fbn' stn cr4 LK4 A4 rn' BX4 BI4 RI4 KR4 p19 p20 p23 p1 p10 p11 p21 p27 TD4 TN4 GST CAPN GN0F ON0 OD0 SPL4 S336 S224 S216 HDR4 DSH4 U172 SGN4 ECR4 IA4 ILK4.
  subst rn'. fold rn in BX4, p11, p27, TN4, CAPN |- *. fold nn in p11, p27, TN4 |- *.
  set (bn4 := L5.BO fbn' nn stn) in *. set (bd4 := L5.BO fbd' 2 (L5.BDyn 8 qd)) in *.
  set (cells := [(E - 264, F + 32); (E - 304, 1); (E - 248, qo); (E - 208, ro); (E - 288, bits); (E - 272, F + 96); (E - 312, qn); (E - 296, F); (E - 336, 0); (E - 224, qd); (E - 216, 2)]).
  assert (TRK4 : trk BX4 M4 bn4 bd4 bn0 bd0 (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells 2).
  { split. exact TN4. split. exact TD4. split. exact ON0. split. exact OD0. split. 2: split; [exact U172 | split; [exact HDR4 | exact DSH4]].
    intros a v Hin. unfold cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [try (apply SPL4; rewrite <- Hin; incell)|]). 4: destruct Hin.
    all: injection Hin as <- <-; split; [assumption | clear; lia]. }
  pose proof BI4 as (B4 & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B4) as WF4.
  assert (ND4 : NoDup (map fst (BX4 ++ LB))). { clear - WF4. decompose [and] WF4. assumption. }
  pose proof (dyn_kind M1 (F + 96) bn (proj1 TN)) as DKN.
  assert (FACTS4 : cinv cr2 cr4 L5DIA.DIVO2_K BB (1 + DR0) (EQ + ER0) /\ (forall cap q, stn = L5.BDyn cap q -> In (q, 8 * cap) BX4) /\
            exists B2 B3, match L5ADVHO.on_of gn0 with None => B2 = BX4 | Some (q, k) => In (q, k) BX4 /\ lb_remove q (BX4 ++ LB) = B2 ++ LB end /\
                          match blk_of bn4 with None => B3 = B2 | Some (q, k) => In (q, k) B2 /\ lb_remove q (B2 ++ LB) = B3 ++ LB end /\
                          match blk_of bd4 with None => [] = B3 | Some (q, k) => In (q, k) B3 /\ lb_remove q (B3 ++ LB) = [] ++ LB end).
  { unfold blk_of. cbn [bn4 bd4 L5.bo_st]. subst cr4. subst BX4.
    destruct YALT as [(DYT & q2 & -> & EST & SLK & _)|(DYF & -> & C2 & _ & N3 & _ & KN)].
    - (* [comment removed for export] *)
      rewrite EST in DKN. cbn [skind] in DKN. destruct gn0 as [|q0 cap0]. rewrite DKN in GN0F. discriminate GN0F. destruct GN0F as (-> & _).
      destruct gn as [|qA capA]. 2: { destruct GST as (X0 & _). rewrite DKN in X0. discriminate X0. }
      cbn [gro_st] in GST. unfold L5ADVEA.same_store in GST. rewrite EST in GST. destruct stn as [v0 v1|capn qn']. destruct GST. destruct GST as (-> & ->).
      cbn [L5DLA.blocks_of L5ADVHO.bx12 L5ADVHO.on_of L5ADVD.ostr app L5DLA.adebl] in *.
      split. { apply (cinv_weak cr2 _ _ _ (0 + (1 + DR0)) (80 + (EQ + ER0))). 2: clear; lia. 2: clear; lia.
               apply (cinv_debit cr2 _ _ _ (1 + (1 + DR0)) (144 + (EQ + ER0))). 2: clear; lia. 2: clear; lia. 2: clear; lia.
               apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV1). pose proof (one_le_cap M1 _ bn (proj1 TN)) as X0. fold (L5.bo_cap bn) in X0. clear - X0; lia. clear; lia. clear; lia. }
      split. { intros cap q Eq. injection Eq as <- <-. right; right; left. reflexivity. }
      assert (D1 : qd <> q0) by exact (L5ADVHO.nodup_app_fst [(qd, 8 * 8)] _ (qd, 8 * 8) (q0, 8 * L5.bo_cap bn) ND4 (or_introl eq_refl) (or_introl eq_refl)).
      assert (D2 : qd <> q2) by exact (L5ADVHO.nodup_app_fst [(qd, 8 * 8)] _ (qd, 8 * 8) (q2, 8 * L5.bo_cap by_) ND4 (or_introl eq_refl) (or_intror (or_introl eq_refl))).
      exists [(qd, 8 * 8); (q2, 8 * L5.bo_cap by_)], [(qd, 8 * 8)].
      split. { split. right; left; reflexivity. cbn [app]. rewrite lb_remove_skip by exact D1. rewrite lb_remove_head. reflexivity. }
      split. { split. right; left; reflexivity. cbn [app]. rewrite lb_remove_skip by exact D2. rewrite lb_remove_head. reflexivity. }
      split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity.
    - (* [comment removed for export] *)
      rewrite KN in DKN. destruct gn0 as [|q0 cap0]. 2: { destruct GN0F as (_ & X0). rewrite DKN in X0. discriminate X0. }
      destruct gn as [|qA capA].
      + cbn [gro_st] in GST. unfold L5ADVEA.same_store in GST. unfold skind in KN. destruct (L5.bo_st bn) as [u0 u1|? ?]. 2: discriminate KN. destruct stn as [v0 v1|capn qn']. 2: destruct GST.
        cbn [L5DLA.blocks_of L5ADVHO.bx12 L5ADVHO.on_of L5ADVD.ostr app L5DLA.adebl] in *.
        split. { apply (cinv_weak cr2 _ _ _ (2 + (1 + DR0)) (8 * L5.bo_cap bn + 80 + (EQ + ER0))). 2: clear; lia. 2: { pose proof (one_le_cap M1 _ bn (proj1 TN)) as X0. fold (L5.bo_cap bn) in X0. clear - X0; lia. }
                 apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV1). clear; lia. clear; lia. clear; lia. }
        split. { intros cap q Eq. discriminate Eq. }
        exists [(qd, 8 * 8)], [(qd, 8 * 8)]. split. reflexivity. split. reflexivity. split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity.
      + destruct GST as (_ & -> & ->).
        cbn [L5DLA.blocks_of L5ADVHO.bx12 L5ADVHO.on_of L5ADVD.ostr app L5DLA.adebl] in *.
        split. { apply (cinv_weak cr2 _ _ _ (1 + (1 + DR0)) (8 * L5.bo_cap bn + 16 + (EQ + ER0))). 2: clear; lia. 2: { pose proof (one_le_cap M1 _ bn (proj1 TN)) as X0. fold (L5.bo_cap bn) in X0. clear - X0; lia. }
                 apply (cinv_debit cr2 _ _ _ (2 + (1 + DR0)) (8 * L5.bo_cap bn + 80 + (EQ + ER0))). 2: clear; lia. 2: clear; lia. 2: clear; lia.
                 apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV1). clear; lia. clear; lia. clear; lia. }
        split. { intros cap q Eq. injection Eq as <- <-. left. reflexivity. }
        exists [(qA, 8 * 8); (qd, 8 * 8)], [(qd, 8 * 8)]. split. reflexivity.
        split. { split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity. }
        split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity. }
  destruct FACTS4 as (CINV4 & INN4 & B2 & B3 & L2 & L3 & Lf).
  assert (IND4 : forall cap q, L5.bo_st bd4 = L5.BDyn cap q -> In (q, 8 * cap) BX4).
  { intros cap q Eq. cbn [bd4 L5.bo_st] in Eq. injection Eq as <- <-. subst BX4. apply in_or_app. right. left. reflexivity. }
  assert (NQY : forall (b : L5.bigobj), (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st by_ = L5.BDyn c' q' -> q <> q').
  { intros b INB c q c' q' E1 E2. exact (L5ADVHO.nodup_app_fst BX4 LB (q, 8 * c) (q', 8 * c') ND4 (INB _ _ E1) (INY _ _ E2)). }
  assert (NNR : (2 <= nn <= 269)%nat). { clear - NNB LY2 LCY CAPY. Lia.lia. }
  pose proof (ru_bounds (Z.of_nat nn - 2) ltac:(clear - NNR; Lia.lia)) as RU1. pose proof (ru_bounds (Z.of_nat nn) ltac:(clear; Lia.lia)) as RU2.
  apply (MID1 cr2 qo by_ wy fx4 R4 M4 model4 BX4 LK4 cr4 A4 bn4 bd4 bn0 bd0 (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells 2 nn (nn - 2)%nat HH0 TQ0 AOQ TY AOR APYQ BI4 RI4 p1 p10 ltac:(rewrite p11; f_equal; clear - NNR; lia) p20 p21
           ltac:(rewrite (KR4 22%nat) by inl; exact X22) p23 TRK4 eq_refl NNR ltac:(clear; lia)).
  { intros DY. destruct YALT as [(_ & _ & _ & _ & SLK & _)|(DYF & _)]. clear - SLK NNB; Lia.lia. rewrite DYF in DY; discriminate DY. }
  { exact (NQY bn4 INN4). } { exact (NQY bd4 IND4). }
  { replace (Z.of_nat (nn - 2)) with (Z.of_nat nn - 2) by (clear - NNR; lia). apply (cinv_for cr2 cr4 _ _ _ _ _ _ CINV4 CRF). subst DR0. destruct (L5.bo_dyn by_); clear; lia. subst EQ ER0. destruct (L5.bo_dyn by_); clear - RU1 RU2; lia. }
  intros fx7 R7 M7 model7 gq gr bq br W7 cr7 LK7 A7 wq BX5 BX7 BI7 RI7 EW7 q18 q21 q22 q23 q24 q27 q25 TQ7 LENQ7 FBQ7 GQF TR7 LENR7 GRF TRK7 ECR7 IA7 ILK7.
  replace (Z.of_nat (nn - 2)) with (Z.of_nat nn - 2) in q25, GQF by (clear - NNR; lia).
  set (LBy7 := L5DLA.blocks_of gr). set (LBq7 := L5DLA.blocks_of gq).
  assert (EBX7 : BX7 = (LBy7 ++ LBq7) ++ BX4). { subst BX7 BX5 LBy7 LBq7. destruct gr, gq; reflexivity. }
  clearbody BX7. clear BX5. subst BX7.
  pose proof (dyn_kind M7 qo bq (proj1 TQ7)) as DKQ. pose proof (dyn_kind M7 ro br (proj1 TR7)) as DKR.
  assert (RU8 : forall i, 0 <= i < 8 -> round_up i = 8). { intros i Hi. unfold round_up. rewrite Z.div_small by exact Hi. reflexivity. }
  assert (RSC7 : match skind (L5.bo_st by_), skind (L5.bo_st br) with
                 | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LBy7 = []
                 | None, None => LBy7 = []
                 | None, Some (cap', q') => cap' = 8 /\ LBy7 = [(q', 64)]
                 | Some _, None => False end).
  { subst LBy7. destruct gr as [|qr capr].
    - destruct GRF as (_ & SS). rewrite (skind_same _ _ SS). destruct (skind (L5.bo_st by_)) as [[c0 q0]|]. split. reflexivity. split; reflexivity. reflexivity.
    - destruct GRF as (_ & ST & EC & DYF). rewrite ST. cbn [skind L5DLA.blocks_of]. destruct YALT as [(DYT & _)|(_ & _ & _ & _ & N3 & KY & _)]. rewrite DYT in DYF; discriminate DYF.
      rewrite KY. rewrite (RU8 (Z.of_nat nn)) in EC by (clear - N3; Lia.lia). subst capr. split; reflexivity. }
  assert (QSC7 : match skind (L5.bo_st bq) with None => LBq7 = [] | Some (cap, q) => LBq7 = [(q, 8 * cap)] end).
  { subst LBq7. destruct gq as [|qq capq]. rewrite GQF in DKQ. destruct (skind (L5.bo_st bq)) as [[c0 q0]|]. discriminate DKQ. reflexivity. rewrite (proj1 GQF). reflexivity. }
  assert (DYQ : L5.bo_dyn bq = match gq with Same => false | Grown _ _ => true end). { destruct gq as [|qq capq]. exact GQF. rewrite DKQ, (proj1 GQF). reflexivity. }
  assert (DYR : L5.bo_dyn br = match gr with Same => L5.bo_dyn by_ | Grown _ _ => true end).
  { destruct gr as [|qr capr]. rewrite DKR, DKY. rewrite (skind_same _ _ (proj2 GRF)). reflexivity. rewrite DKR. destruct GRF as (_ & -> & _). reflexivity. }
  set (ERR := 8 * (Z.of_nat nn + 9)).
  assert (CINV7 : cinv cr2 cr7 L5DIA.DIVO2_K BB ((if L5.bo_dyn br then 0 else 1) + (if L5.bo_dyn bq then 0 else 1)) ((if L5.bo_dyn br then 0 else ERR) + (if L5.bo_dyn bq then 0 else EQ))).
  { rewrite DYQ, DYR. subst cr7. subst DR0 ER0. fold ERR in CINV4. destruct gq as [|qq capq]; destruct gr as [|qr capr]; cbn [L5DLA.blocks_of L5DLA.adebl].
    - apply (cinv_weak cr2 _ _ _ _ _ _ _ CINV4). destruct (L5.bo_dyn by_); clear; lia. destruct (L5.bo_dyn by_); clear; lia.
    - destruct GRF as (_ & _ & -> & DYF). rewrite DYF in CINV4. apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV4). clear - RU2; lia. clear; lia. subst ERR. clear - RU2; lia.
    - destruct GQF as (_ & -> & _). apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV4). clear - RU1; lia. destruct (L5.bo_dyn by_); clear; lia. subst EQ. destruct (L5.bo_dyn by_); clear - RU1; lia.
    - destruct GQF as (_ & -> & _). destruct GRF as (_ & _ & -> & DYF). rewrite DYF in CINV4.
      apply (cinv_debit cr2 _ _ _ (1 + 0) (ERR + 0)). 2: clear - RU2; lia. 2: clear; lia. 2: subst ERR; clear - RU2; lia.
      apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV4). clear - RU1; lia. clear; lia. subst EQ. clear - RU1; lia. }
  assert (NCL7 : forall q k a, In (q, k) ((LBy7 ++ LBq7) ++ BX4) -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a).
  { intros q k a Hin Ha. exact (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W7 _ M7 model7 LK7 cr7 A7 q k a BI7 Hin Ha). }
  pose proof (len_le_cap M7 qo bq (proj1 TQ7)) as LCQ7. fold (L5.bo_cap bq) in LCQ7.
  destruct AOK as (OBA & SGA). set (ba := L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) in *.
  assert (TA : tob LB M ao ba [L5PSA.A0; L5PSA.A1]).
  { pose proof OBA as (_ & _ & _ & (_ & _ & _ & _ & A0R & A1R)). split. exact OBA. split. { split. reflexivity. split. constructor; [exact A0R | constructor; [exact A1R | constructor]]. reflexivity. } split. exact SZA. intros cap q Eq. discriminate Eq. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model ao 32 E SCRD HH0 AOA ltac:(clear; lia) ltac:(reflexivity)) as ((ALO & ACE & AHI & A8 & _) & ABIG & _).
  assert (FIN : forall LByx LBqx (bqx brx : L5.bigobj) crx dk db,
     match skind (L5.bo_st by_), skind (L5.bo_st brx) with
     | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LByx = []
     | None, None => LByx = []
     | None, Some (cap', q') => cap' = 8 /\ LByx = [(q', 64)]
     | Some _, None => False end ->
     match skind (L5.bo_st bqx) with None => LBqx = [] | Some (cap, q) => LBqx = [(q, 8 * cap)] end ->
     (LByx = [] \/ LBqx = []) ->
     (forall q k a, In (q, k) LByx -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a) ->
     cinv cr2 crx L5DIA.DIVO2_K BB dk db -> 0 <= dk -> 0 <= db ->
     forall (fxf : FPState) Rf Mf modelf Af crf LKf bqf wqf brf wrf fb',
      regs_preserved R Rf -> incl A Af -> incl LKf LK -> ahpres L ar LB FF E SCRD (W7 ++ [(L5.bo_data ro brx, 8 * L5.bo_cap brx)]) M Mf ->
      L5.big_at RSEGS Mf qo bqf -> L5C.obj_limbs RSEGS Mf bqf wqf -> skind (L5.bo_st bqf) = skind (L5.bo_st bqx) ->
      L5.big_at RSEGS Mf ro brf -> L5C.obj_limbs RSEGS Mf brf wrf -> skind (L5.bo_st brf) = skind (L5.bo_st brx) ->
      L5.bo_fb brf = Z.lor (Z.land fb' 253) bits -> Z.testbit fb' 1 = false ->
      L5OMA.acredit_after L crx L5DIA.DIVN_K L5DIA.DIVN_BYTES crf -> model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI ((LByx ++ LBqx) ++ LB) FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K).
  { intros LByx LBqx bqx brx crx dk db RSCx QSCx ONE NCLx CINVx DK0 DB0 fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf IAf ILKf AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf.
    rewrite <- app_assoc in HHf.
    apply (KF fxf Rf Mf modelf (LByx ++ LBqx ++ LB) crf LKf Af). 2: exact RTf. 2: exact IAf. 2: exact AMf. 2: exact ILKf. 2: exact HHf.
    assert (AHW : ahpres L ar LB FF E L5DIA.DIVO_SCR [(ro, 32); (L5.bo_data ro by_, 8 * L5.bo_cap by_); (qo, 32)] M Mf).
    { rewrite ESCR in AHf. destruct AHf as (EK & DFK). split. 2: exact DFK. intros a (Ha & Hc & Ho). rewrite <- ESCR in Hc. apply EK. split. exact Ha. split. rewrite <- ESCR. exact Hc.
      rewrite EW7. intros rr Hr IR. unfold L5.in_rng in IR. cbn [In app] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in IR.
      - apply (Ho (qo, 32)). right; right; left; reflexivity. exact IR.
      - unfold L5.bo_data, L5.bo_cap in IR, LCQ7. destruct (L5.bo_st bq) as [v0 v1|capq qq] eqn:EQ7. apply (Ho (qo, 32)). right; right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - IR LCQ7; lia.
        cbn [skind] in QSC7. apply (NCL7 qq (8 * capq) a). apply in_or_app. left. apply in_or_app. right. rewrite QSC7. left; reflexivity. clear - IR LCQ7; lia. exact Hc.
      - apply (Ho (ro, 32)). left; reflexivity. exact IR.
      - apply (Ho (L5.bo_data ro by_, 8 * L5.bo_cap by_)). right; left; reflexivity. exact IR.
      - unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st brx) as [v0 v1|capx qx] eqn:EBX. apply (Ho (ro, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - IR; lia.
        cbn [skind] in RSCx. destruct (skind (L5.bo_st by_)) as [[c0 q0]|] eqn:EKY.
        + destruct RSCx as (-> & -> & _). apply skind_dyn in EKY. apply (Ho (L5.bo_data ro by_, 8 * L5.bo_cap by_)). right; left; reflexivity. unfold L5.in_rng, L5.bo_data, L5.bo_cap. rewrite EKY. cbn [fst snd]. exact IR.
        + destruct RSCx as (-> & ->). apply (NCLx qx 64 a). left; reflexivity. clear - IR; lia. exact Hc. }
    split. exact RPf.
    split. { exists LByx, LBqx. split. reflexivity.
      split. { exists brf, wrf. split. exact OBRf. split. exact OLRf. rewrite <- KRf in RSCx. unfold skind in RSCx.
               destruct (L5.bo_st by_) as [v0 v1|capy qy]; destruct (L5.bo_st brf) as [u0 u1|capf qf].
               - exact RSCx.
               - destruct RSCx as (-> & ->). split. reflexivity. split. reflexivity. cbn [app] in HHf. exact (L5ADH.afresh_of_inv L ar C HI HIok qf 64 _ FF LKf crf Af Mf (vml_of modelf) HHf).
               - exact RSCx.
               - exact RSCx. }
      exists bqf, wqf. split. exact OBQf. split. exact OLQf. rewrite <- KQf in QSCx. unfold skind in QSCx. destruct (L5.bo_st bqf) as [u0 u1|capf qf]. exact QSCx.
      split. exact QSCx. destruct ONE as [->| ->]. 2: discriminate QSCx. subst LBqx. cbn [app] in HHf. exact (L5ADH.afresh_of_inv L ar C HI HIok qf (8 * capf) _ FF LKf crf Af Mf (vml_of modelf) HHf). }
    split. { split. 2: exact SGA.
      refine (proj1 (L5ADVO1.arg_kept L ar C HI LY HIok M Mf model LB FF LK cr2 A E L5DIA.DIVO_SCR _ ao ba [L5PSA.A0; L5PSA.A1] HH0 AHW AOA TA _)).
      intros a OR rr Hr IR. unfold L5.in_rng in IR. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB0 & _).
      destruct OR as [OR|[OR|(cap & q & Eq & _)]]. 3: discriminate Eq.
      - destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in IR.
        + clear - OR IR APYA; lia.
        + unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st by_) as [v0 v1|capy qy] eqn:EY. clear - OR IR APYA; lia.
          pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB0 _ (INY _ _ eq_refl)))))))) as FA. cbn [fst snd] in FA. destruct AOA as (f & Hf & O1 & O2 & _).
          specialize (FA f (in_or_app _ _ _ (or_introl Hf))). clear - FA O1 O2 OR IR. lia.
        + clear - OR IR APAQ; lia.
      - unfold SB in OR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in IR.
        + clear - OR IR ALO AHI RLO RBIG. lia.
        + unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st by_) as [v0 v1|capy qy] eqn:EY. clear - OR IR ALO AHI RLO RBIG. lia.
          pose proof (proj1 (WB0 _ (INY _ _ eq_refl))) as (_ & _ & _ & _ & _ & (_ & AM & _)). cbn [fst snd] in AM. unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. clear - OR IR ALO AHI AM. lia.
        + clear - OR IR ALO AHI QLO QBIG. lia. }
    split. { exact (cinv_fin cr2 crx _ _ dk db crf CINVx DK0 DB0 CRAf). }
    exact AHW. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (WQH7 : forall a, qo <= a < qo + 32 -> ~ L5.outside W7 a). { intros a Ha OUT. rewrite EW7 in OUT. apply (OUT (qo, 32)). left; reflexivity. exact Ha. }
  assert (WRH7 : forall a, ro <= a < ro + 32 -> ~ L5.outside W7 a). { intros a Ha OUT. rewrite EW7 in OUT. apply (OUT (ro, 32)). right; right; left; reflexivity. exact Ha. }
  assert (WY7 : forall cap q a, L5.bo_st by_ = L5.BDyn cap q -> q <= a < q + 8 * cap -> ~ L5.outside W7 a).
  { intros cap q a Eq Ha OUT. rewrite EW7 in OUT. apply (OUT (L5.bo_data ro by_, 8 * L5.bo_cap by_)). right; right; right; left; reflexivity. unfold L5.in_rng, L5.bo_data, L5.bo_cap. rewrite Eq. exact Ha. }
  assert (WSH7 : forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W7 a).
  { intros a Hs. rewrite EW7. intros rr Hr IR. unfold L5.in_rng in IR. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in IR.
    - exact (SH_OBJ W7 _ M7 model7 LK7 cr7 A7 qo a BI7 AOQ' Hs IR).
    - unfold L5.bo_data, L5.bo_cap in IR, LCQ7. destruct (L5.bo_st bq) as [v0 v1|capq qq] eqn:EQ7. apply (SH_OBJ W7 _ M7 model7 LK7 cr7 A7 qo a BI7 AOQ' Hs). clear - IR LCQ7; lia.
      apply (SH_BLK W7 _ M7 model7 LK7 cr7 A7 qq (8 * capq) a BI7 AOR' (proj2 (proj2 (proj2 TQ7)) capq qq EQ7) Hs). clear - IR LCQ7; lia.
    - exact (SH_OBJ W7 _ M7 model7 LK7 cr7 A7 ro a BI7 AOR' Hs IR).
    - unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st by_) as [v0 v1|capy qy] eqn:EY. apply (SH_OBJ W7 _ M7 model7 LK7 cr7 A7 ro a BI7 AOR' Hs). clear - IR; lia.
      apply (SH_BLK W7 _ M7 model7 LK7 cr7 A7 qy (8 * capy) a BI7 AOR' ltac:(apply in_or_app; right; exact (INY _ _ eq_refl)) Hs). exact IR. }
  assert (SGR7 : Z.testbit (L5.bo_fb br) 1 = false).
  { assert (X0 : forall g, Z.testbit (assign_fb (L5.bo_fb by_) (L5.bo_fb bn4) nn g) 1 = false).
    { intros g. unfold assign_fb. destruct (Nat.eqb_spec nn 0) as [E0|_]. exfalso. clear - E0 NNR. Lia.lia. rewrite Z.lor_spec, !Z.land_spec. cbn [bn4 L5.bo_fb]. rewrite SGN4.
      change (Z.testbit 253 1) with false. rewrite !andb_false_r. reflexivity. }
    destruct gr as [|qr capr]. rewrite (proj1 GRF). apply X0. rewrite (proj1 GRF). apply X0. }
  assert (RUL : forall i, 0 <= i -> i < round_up i). { intros i Hi. unfold round_up. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hi. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (GQS : skind (L5.bo_st by_) = None -> gq = Same). { intros KY. destruct gq as [|qq capq]. reflexivity. exfalso. destruct GQF as (_ & _ & N3). destruct YALT as [(DYT & _)|(_ & _ & _ & _ & N3' & _)]. rewrite DKY, KY in DYT. discriminate DYT. clear - N3 N3'. Lia.lia. }
  assert (GRS : skind (L5.bo_st by_) <> None -> gr = Same). { intros KY. destruct gr as [|qr capr]. reflexivity. exfalso. destruct GRF as (_ & _ & _ & DYF). rewrite DKY in DYF. destruct (skind (L5.bo_st by_)). discriminate DYF. apply KY; reflexivity. }
  assert (ONE7 : LBy7 = [] \/ LBq7 = []). { subst LBy7 LBq7. destruct (skind (L5.bo_st by_)) as [[c0 q0]|] eqn:KY. left. rewrite GRS. reflexivity. intros X0; discriminate X0. right. rewrite GQS; reflexivity. }
  set (n := Z.of_nat nn - 1).
  assert (CELLS7 : forall c v, In (c, v) cells -> (c + 8 <= E - 232 \/ E - 224 <= c) /\ (c + 8 <= E - 328 \/ E - 312 <= c) /\ (c + 8 <= E - 184 \/ E - 176 <= c)).
  { intros c v Hin. unfold cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; clear; lia|]). destruct Hin. }
  assert (USCR : 352 + L5DIA.UNNORM_SCR <= SCRD) by (rewrite ESCR; unfold L5DIA.DIVO_SCR; clear; lia).
  assert (SCR8 : SCRD mod 8 = 0) by (rewrite ESCR; reflexivity).
  apply (G7T qo fx7 R7 M7 model7 W7 _ LK7 cr7 A7 bq br bn4 bd4 bn0 bd0 wq (firstn nn rn) (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells 2 n 1 BI7 RI7 AOQ AOR q21 q23 q24
           ltac:(rewrite q27, p27; f_equal; subst n; clear; lia) TQ7 TR7 TRK7 ltac:(rewrite LENR7; subst n; clear; lia) ltac:(reflexivity) ltac:(subst n; clear - NNR; lia) ltac:(clear; lia)
           ltac:(unfold cells; incell) ltac:(unfold cells; incell) ltac:(intros c v Hin; exact (proj1 (CELLS7 c v Hin)))).
  intros fx8 Rg Mg modelg BI8 RI8 KR8 r19 r20 r21 r22 r24 r26 TQ8 TR8 TRK8 S232.
  assert (IA7' : incl A A7) by (intros z Hz; apply IA7, IA4, IA1; exact Hz). assert (ILK7' : incl LK7 LK) by (intros z Hz; apply ILK1, ILK4, ILK7; exact Hz).
  assert (KE3v : forall (brx bqx : L5.bigobj) (BXx : list (Z * Z)) crx LKx Ax cellsx (fx2 : FPState) R2 M2' model2' (bq2 br2 : L5.bigobj) (wq2 wr2 : list Z),
      binv W7 BXx M2' model2' LKx crx Ax -> rinvD R E R2 ->
      (getr R2 (reg 1) = Z_to_bv 64 0x92a54 /\ getr R2 (reg 18) = Z_to_bv 64 SH /\ getr R2 (reg 19) = Z_to_bv 64 ro /\ getr R2 (reg 20) = Z_to_bv 64 (F + 32) /\ getr R2 (reg 21) = Z_to_bv 64 (F + 96) /\ getr R2 (reg 22) = Z_to_bv 64 qo /\ getr R2 (reg 23) = Z_to_bv 64 (ro / 8 + 2147450880) /\ getr R2 (reg 24) = Z_to_bv 64 F /\ getr R2 (reg 27) = Z_to_bv 64 F) ->
      skind (L5.bo_st bq2) = skind (L5.bo_st bqx) ->
      tob (BXx ++ LB) M2' qo bq2 wq2 -> tob (BXx ++ LB) M2' ro br2 wr2 -> skind (L5.bo_st br2) = skind (L5.bo_st brx) -> L5.bo_len br2 = L5.bo_len brx ->
      trk BXx M2' bn4 bd4 bn0 bd0 (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cellsx 2 ->
      forall (fx' : FPState) R' M' model' qX LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
      0 = 1 -> L5.bo_st br2 = L5.BDyn 8 qX ->
      L5DIA.unnorm_e3A L ar (BXx ++ LB) FF' crx M2' M' R2 R' ro qX (L5.bo_len br2) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model2' model' -> incl Ax A' -> amodel_ok A' model' -> incl LK' LKx ->
      ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K).
  { intros. discriminate. }
  destruct (Z.ltb_spec (nth_w (firstn nn rn) (Z.to_nat n)) (nth_w (firstn 2 DA) (Z.to_nat 1))) as [LT|GE].
  - (* [comment removed for export] *)
    apply (GEN_BACK fx8 Rg Mg modelg W7 BX4 B2 B3 LBy7 LBq7 LK7 cr7 A7 qo qn bits 0 1 n by_ bq br bn4 bd4 bn0 bd0 wq (firstn nn rn) (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells 2 Hunn BI8 RI8 r19 r20 r21 r22 r24
             ltac:(rewrite (KR8 18%nat) by inl; exact q18) r26 AOR AOQ ltac:(clear - APYQ; lia) TR8 TQ8 TRK8
             ltac:(rewrite LENR7; subst n; clear; lia) ltac:(rewrite LENQ7; subst n; clear - NNR; lia) ltac:(reflexivity) ltac:(subst n; clear - NNR; lia) ltac:(clear; lia)
             (proj1 go2_d) SGR7 S232).
    all: try (unfold cells; incell).
    { exact QNR. } { exact BITSR. } { clear; lia. }
    { intros c v Hin. exact (proj2 (CELLS7 c v Hin)). }
    { exact SSH. } { exact USCR. } { exact SCR8. } { exact FFR5. } { exact FFR3. } { exact WQH7. } { exact WRH7. } { exact WY7. } { exact WSH7. } { exact INY. } { exact INN4. } { exact IND4. }
    { exact RSC7. } { exact QSC7. } { intros X0; discriminate X0. } { intros X0; discriminate X0. } { exact L2. } { exact L3. } { exact Lf. }
    2: { exact (KE3v br bq _ cr7 LK7 A7 _). }
    intros fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf IAf ILKf AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf.
    refine (FIN LBy7 LBq7 bq br cr7 _ _ RSC7 QSC7 _ _ CINV7 _ _ fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf _ _ AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf).
    + exact ONE7.
    + intros q k a Hin Ha. apply (NCL7 q k a). apply in_or_app. left. apply in_or_app. left. exact Hin. exact Ha.
    + destruct (L5.bo_dyn br); destruct (L5.bo_dyn bq); clear; lia.
    + destruct (L5.bo_dyn br); destruct (L5.bo_dyn bq); subst ERR EQ; clear; lia.
    + intros z Hz. apply IAf, IA7'. exact Hz.
    + intros z Hz. apply ILK7', ILKf. exact Hz.
  - (* [comment removed for export] *)
    assert (ENN : nn = L5.bo_len by_). { apply BARM. replace (nn - 1)%nat with (Z.to_nat n) by (subst n; clear - NNR; Lia.lia). clear - GE. lia. }
    set (cells8 := (E - 232, 1) :: cells).
    assert (TRK8' : trk ((LBy7 ++ LBq7) ++ BX4) Mg bn4 bd4 bn0 bd0 (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells8 2).
    { destruct TRK8 as (T1 & T2 & T3 & T4 & SPL8 & T6). split. exact T1. split. exact T2. split. exact T3. split. exact T4. split. 2: exact T6.
      intros a v [Eq|Hin]. injection Eq as <- <-. split. exact S232. clear; lia. exact (SPL8 a v Hin). }
    assert (INC8 : forall c v, In (c, v) cells -> In (c, v) cells8) by (intros c v Hin; right; exact Hin).
    destruct (DIST5 W7 BX4 LBy7 LBq7 Mg modelg LK7 cr7 A7 by_ bq br bn4 bd4 BI8 INY INN4 IND4 RSC7 QSC7) as (NQB & NQNR & NQNQ & NQDR & NQDQ & RB7 & QB7).
    pose proof (len_le_cap M7 ro br (proj1 TR7)) as LCR7. fold (L5.bo_cap br) in LCR7.
    assert (SLKB : L5.bo_dyn br = true -> Z.of_nat nn + 1 <= L5.bo_cap br /\ (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * L5.bo_cap br -> aclient L ar LB FF E SCRD a -> ~ L5.outside W7 a)).
    { intros DY. rewrite DKR in DY. unfold L5.bo_cap, L5.bo_data. destruct (L5.bo_st br) as [v0 v1|capr qr] eqn:EBR. discriminate DY. destruct (RB7 capr qr eq_refl) as [(EY & _)|Hin].
      - split. 2: { intros a Ha _. exact (WY7 capr qr a EY Ha). } pose proof INY0 as X1. rewrite EY in X1. rewrite ENN. exact (proj2 X1).
      - split. 2: { intros a Ha Hc. exfalso. exact (NCL7 qr (8 * capr) a ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) Ha Hc). }
        destruct gr as [|qg capg]. { exfalso. subst LBy7. destruct Hin. } destruct GRF as (_ & ST & EC & _). injection ST as -> ->. rewrite EC. pose proof (RUL (Z.of_nat nn) ltac:(clear; lia)) as X0. clear - X0; lia. }
    assert (SLKQ : L5.bo_dyn bq = true -> Z.of_nat nn - 1 <= L5.bo_cap bq).
    { intros DY. destruct gq as [|qg capg]. rewrite GQF in DY. discriminate DY. destruct GQF as (ST & EC & _). unfold L5.bo_cap. rewrite ST, EC. pose proof (RUL (Z.of_nat nn - 2) ltac:(clear - NNR; lia)) as X0. clear - X0; lia. }
    pose proof (ru_bounds (Z.of_nat nn + 1) ltac:(clear; lia)) as RU3. pose proof (ru_bounds (Z.of_nat nn - 1) ltac:(clear - NNR; lia)) as RU4.
    apply (GBT fx8 Rg Mg modelg W7 _ LK7 cr7 A7 qo br bq bn4 bd4 bn0 bd0 (firstn nn rn) wq (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells8 2 (nn - 1)%nat (nn - 2)%nat BI8 RI8 AOR AOQ
             ltac:(clear - APYQ; lia) ltac:(clear - QLO QHI; lia) ltac:(rewrite (KR8 18%nat) by inl; exact q18) ltac:(rewrite (KR8 23%nat) by inl; exact q23)
             ltac:(rewrite (KR8 25%nat) by inl; rewrite q25; f_equal; clear - NNR; lia) r26 ltac:(rewrite (KR8 27%nat) by inl; rewrite q27, p27; f_equal; clear - NNR; lia)
             TR8 ltac:(rewrite LENR7; clear - NNR; lia) TQ8 LENQ7 TRK8' ltac:(apply INC8; unfold cells; incell) ltac:(clear - NNR; lia) ltac:(clear - NNR; lia)).
    { intros DY. destruct (SLKB DY) as (X0 & _). clear - X0 NNR. lia. }
    { intros DY. pose proof (SLKQ DY) as X0. clear - X0 NNR. lia. }
    { apply (cinv_for cr2 cr7 _ _ _ _ _ _ CINV7 CRF). destruct (L5.bo_dyn br); destruct (L5.bo_dyn bq); clear; lia.
      replace (Z.of_nat (nn - 1) + 2) with (Z.of_nat nn + 1) by (clear - NNR; lia). replace (Z.of_nat (nn - 2) + 1) with (Z.of_nat nn - 1) by (clear - NNR; lia).
      subst ERR EQ. destruct (L5.bo_dyn br); destruct (L5.bo_dyn bq); clear - RU3 RU4; lia. }
    { intros a OUT. rewrite EW7 in OUT. split; intros rr [<-|[]]; apply OUT. right; right; left; reflexivity. left; reflexivity. }
    { intros [DY|X0] a Hc OUT IR. 2: { exfalso. clear - X0 NNR. Lia.lia. } destruct (SLKB DY) as (X0 & COV). apply (COV a). 2: exact Hc. 2: exact OUT.
      unfold L5.in_rng in IR. cbn [fst snd] in IR. clear - IR X0 NNR. lia. }
    { intros ALT a Hc OUT IR. unfold L5.in_rng in IR. cbn [fst snd] in IR. rewrite DKQ in ALT. unfold L5.bo_data in IR. destruct (L5.bo_st bq) as [v0 v1|capq qq] eqn:EBQ.
      - destruct ALT as [X0|X0]. discriminate X0. apply (WQH7 a). clear - IR X0 NNR. lia. exact OUT.
      - assert (DY : L5.bo_dyn bq = true) by (rewrite DKQ; reflexivity). pose proof (SLKQ DY) as X0. unfold L5.bo_cap in X0. rewrite EBQ in X0.
        apply (NCL7 qq (8 * capq) a). apply in_or_app. left. apply in_or_app. right. exact (QB7 capq qq eq_refl). clear - IR X0 NNR. lia. exact Hc. }
    { exact NQB. } { exact NQNR. } { exact NQNQ. } { exact NQDR. } { exact NQDQ. }
    intros fx9 R9 M9 model9 gr9 gq9 br9 bq9 cr9 LK9 A9 BXr BX9 BI9 RI9 KR9 s19 s20 s22 TR9 LENR9 GRF9 TQ9 LENQ9 GQF9 TRK9 ECR9 IA9 ILK9.
    set (LBy9 := L5DLA.blocks_of gr9 ++ LBy7). set (LBq9 := L5DLA.blocks_of gq9 ++ LBq7).
    pose proof (dyn_kind M9 qo bq9 (proj1 TQ9)) as DKQ9. pose proof (dyn_kind M9 ro br9 (proj1 TR9)) as DKR9.
    assert (KYI : skind (L5.bo_st by_) = None -> (nn <= 3)%nat). { intros KY. destruct YALT as [(DYT & _)|(_ & _ & _ & _ & N3 & _)]. rewrite DKY, KY in DYT. discriminate DYT. exact N3. }
    (* [comment removed for export] *)
    assert (GQ9 : forall q c, gq9 = Grown q c -> LBy9 = [] /\ LBq7 = []).
    { intros q c ->. destruct GQF9 as (_ & _ & _ & DQF & N3). assert (gq = Same). { destruct gq. reflexivity. rewrite DYQ in DQF. discriminate DQF. }
      assert (KY : skind (L5.bo_st by_) <> None). { intros KY. pose proof (KYI KY) as X0. clear - X0 N3. Lia.lia. }
      pose proof (GRS KY) as GR. subst LBy9 LBy7 LBq7. rewrite GR, H. split. 2: reflexivity. destruct gr9 as [|q9 c9]. reflexivity. exfalso. destruct GRF9 as (_ & _ & _ & DRF & _). rewrite DYR, GR, DKY in DRF.
      destruct (skind (L5.bo_st by_)). discriminate DRF. apply KY; reflexivity. }
    assert (EBX9 : BX9 = (LBy9 ++ LBq9) ++ BX4).
    { subst BX9 BXr. destruct gq9 as [|q9 c9]. unfold LBy9, LBq9. destruct gr9; cbn [L5DLA.blocks_of app]; reflexivity.
      destruct (GQ9 q9 c9 eq_refl) as (E1 & E2). unfold LBy9, LBq9 in E1 |- *. destruct gr9 as [|qr9 cr9']. 2: discriminate E1. cbn [L5DLA.blocks_of app] in E1 |- *. rewrite E1, E2. reflexivity. }
    clearbody BX9. clear BXr. subst BX9.
    assert (RSC9 : match skind (L5.bo_st by_), skind (L5.bo_st br9) with
                   | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LBy9 = []
                   | None, None => LBy9 = []
                   | None, Some (cap', q') => cap' = 8 /\ LBy9 = [(q', 64)]
                   | Some _, None => False end).
    { subst LBy9. destruct gr9 as [|q9 c9]. destruct GRF9 as (_ & SS). rewrite (skind_same _ _ SS). exact RSC7.
      destruct GRF9 as (_ & ST & EC & DRF & _). rewrite ST. cbn [skind L5DLA.blocks_of app]. rewrite DKR in DRF. destruct (skind (L5.bo_st br)) as [[c0 q0]|]. discriminate DRF.
      destruct (skind (L5.bo_st by_)) as [[c0 q0]|] eqn:KY. destruct RSC7. rewrite RSC7. pose proof (KYI eq_refl) as N3.
      rewrite (RU8 (Z.of_nat (Datatypes.S (Datatypes.S (nn - 1))))) in EC by (clear - N3 NNR; Lia.lia). subst c9. split; reflexivity. }
    assert (QSC9 : match skind (L5.bo_st bq9) with None => LBq9 = [] | Some (cap, q) => LBq9 = [(q, 8 * cap)] end).
    { subst LBq9. destruct gq9 as [|q9 c9]. destruct GQF9 as (_ & SS). rewrite (skind_same _ _ SS). exact QSC7.
      destruct (GQ9 q9 c9 eq_refl) as (_ & E2). rewrite E2. destruct GQF9 as (_ & ST & _). rewrite ST. reflexivity. }
    assert (ONE9 : LBy9 = [] \/ LBq9 = []).
    { destruct gq9 as [|q9 c9]. 2: { left. exact (proj1 (GQ9 q9 c9 eq_refl)). } subst LBq9. cbn [L5DLA.blocks_of app]. destruct ONE7 as [E1|E2]. 2: { right; exact E2. }
      destruct (skind (L5.bo_st by_)) as [[c0 q0]|] eqn:KY. 2: { right. subst LBq7. rewrite GQS; reflexivity. }
      left. subst LBy9. rewrite E1. destruct gr9 as [|qr9 cr9']. reflexivity. exfalso. destruct GRF9 as (_ & _ & _ & DRF & _). rewrite DYR, (GRS ltac:(intros X0; discriminate X0)), DKY in DRF. discriminate DRF. }
    assert (CINV9 : cinv cr2 cr9 L5DIA.DIVO2_K BB 0 0).
    { subst cr9. replace (Z.of_nat (nn - 1) + 2) with (Z.of_nat nn + 1) in * by (clear - NNR; lia).
      assert (X1 : cinv cr2 (L5DLA.adebl L cr7 (L5DLA.blocks_of gr9)) L5DIA.DIVO2_K BB (0 + (if L5.bo_dyn bq then 0 else 1)) (0 + (if L5.bo_dyn bq then 0 else EQ))).
      { destruct gr9 as [|q9 c9]; cbn [L5DLA.blocks_of L5DLA.adebl]. apply (cinv_weak cr2 _ _ _ _ _ _ _ CINV7). destruct (L5.bo_dyn br); clear; lia. subst ERR. destruct (L5.bo_dyn br); clear; lia.
        destruct GRF9 as (_ & _ & -> & DRF & _). rewrite DRF in CINV7. replace (Z.of_nat (Datatypes.S (Datatypes.S (nn - 1)))) with (Z.of_nat nn + 1) by (clear - NNR; lia).
        apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV7). clear - RU3; lia. clear; lia. subst ERR. clear - RU3; lia. }
      destruct gq9 as [|q9 c9]; cbn [L5DLA.blocks_of L5DLA.adebl]. apply (cinv_weak cr2 _ _ _ _ _ _ _ X1). destruct (L5.bo_dyn bq); clear; lia. subst EQ. destruct (L5.bo_dyn bq); clear; lia.
      destruct GQF9 as (_ & _ & -> & DQF & _). rewrite DQF in X1. replace (Z.of_nat (Datatypes.S (nn - 2))) with (Z.of_nat nn - 1) by (clear - NNR; lia).
      apply (cinv_debit cr2 _ _ _ _ _ _ _ _ X1). clear - RU4; lia. clear; lia. subst EQ. clear - RU4; lia. }
    assert (SGR9 : Z.testbit (L5.bo_fb br9) 1 = false).
    { destruct gr9 as [|q9 c9]. rewrite (proj1 GRF9). exact SGR7. rewrite (proj1 GRF9). rewrite Z.lor_spec, SGR7. reflexivity. }
    pose proof TRK9 as (_ & _ & _ & _ & SPL9 & _).
    assert (NCL9 : forall q k a, In (q, k) ((LBy9 ++ LBq9) ++ BX4) -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a).
    { intros q k a Hin Ha. exact (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W7 _ M9 model9 LK9 cr9 A9 q k a BI9 Hin Ha). }
    apply (GEN_BACK fx9 R9 M9 model9 W7 BX4 B2 B3 LBy9 LBq9 LK9 cr9 A9 qo qn bits 0 1 (Z.of_nat nn) by_ bq9 br9 bn4 bd4 bn0 bd0 _ _ (firstn nn rn) (firstn 2 DA) (L5ADVHO.on_of gn0) cells8 2 Hunn BI9 RI9 s19 s20
             ltac:(rewrite (KR9 21%nat) by inl; exact r21) ltac:(rewrite s22; f_equal; clear - NNR; lia) ltac:(rewrite (KR9 24%nat) by inl; exact r24)
             ltac:(rewrite (KR9 18%nat) by inl; rewrite (KR8 18%nat) by inl; exact q18) ltac:(rewrite (KR9 26%nat) by inl; exact r26) AOR AOQ ltac:(clear - APYQ; lia) TR9 TQ9 TRK9
             ltac:(rewrite LENR9; clear - NNR; lia) ltac:(rewrite LENQ9; clear - NNR; lia) ltac:(reflexivity) ltac:(clear - NNR; lia) ltac:(clear; lia)
             (proj1 go2_d) SGR9 (proj1 (SPL9 _ _ (or_introl eq_refl)))).
    all: try (apply INC8; unfold cells; incell).
    { exact QNR. } { exact BITSR. } { left; reflexivity. } { clear; lia. }
    { intros c v [Eq|Hin]. injection Eq as <- <-. clear; lia. exact (proj2 (CELLS7 c v Hin)). }
    { exact SSH. } { exact USCR. } { exact SCR8. } { exact FFR5. } { exact FFR3. } { exact WQH7. } { exact WRH7. } { exact WY7. } { exact WSH7. } { exact INY. } { exact INN4. } { exact IND4. }
    { exact RSC9. } { exact QSC9. } { intros X0; discriminate X0. } { intros X0; discriminate X0. } { exact L2. } { exact L3. } { exact Lf. }
    2: { exact (KE3v br9 bq9 _ cr9 LK9 A9 _). }
    intros fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf IAf ILKf AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf.
    refine (FIN LBy9 LBq9 bq9 br9 cr9 _ _ RSC9 QSC9 ONE9 _ CINV9 _ _ fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf _ _ AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf).
    + intros q k a Hin Ha. apply (NCL9 q k a). apply in_or_app. left. apply in_or_app. left. exact Hin. exact Ha.
    + clear; lia.
    + clear; lia.
    + intros z Hz. apply IAf, IA9, IA7'. exact Hz.
    + intros z Hz. apply ILK7', ILK9, ILKf. exact Hz.
Qed.
End DIV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem gen_O2_ok : L5ACPAS.copya_stk_spec L ar HI -> L5DLA.norm_specA L ar HI -> resize_spec L ar HI -> assign_spec L ar HI -> opdel_sized_spec L ar HI -> L5DIA.unnorm_specA L ar HI ->
  L5ADVO2.gen_O2 L ar HI.
Proof.
  intros Hcps Hnorm Hrsz Hasg Hdel Hunn. unfold L5ADVO2.gen_O2.
  intros R M model K LB FF LK cr A yo ao qo E r fba by_ wy F fl LK2 M2 model2 fx1 g2 R1 M1 model1 cr1 LK1 A1 c qn bits bn bd HH AM HK G1 RA G2 A32 G4 STK SSH FFR5 FFR3 FFRS YOK AOY SZY LY1 CAPY AOK AOA SZA ZQ AOQ SZQ APYA APYQ APAQ CRF G ER UR1
         ATG G2F ECR1 IA1 ILK1 CR CV LY2 LNE LDE STD EBITS KF.
  assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- G2; reflexivity).
  assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- G4; reflexivity).
  exact (go2_all R M model K LB FF LK A E L5DIA.DIVO_SCR F fl yo r LK2 M2 model2 cr G ER A32 HK G4' ltac:(vm_compute; discriminate) (ffrk_le 1 FF LK 5 4 FFR5 ltac:(clear; lia)) FFRS Hdel Hasg Hcps Hnorm Hrsz RA UR1 G2'
           ao qo fba by_ wy fx1 g2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd Hunn HH eq_refl SSH FFR5 FFR3 YOK AOY SZY CAPY AOK AOA SZA ZQ AOQ SZQ APYA APYQ APAQ CRF ATG G2F ECR1 IA1 ILK1 LY2 LNE LDE STD EBITS KF).
Qed.
End WithIface.
End SCFG_1.
End L5ADVGO2D.

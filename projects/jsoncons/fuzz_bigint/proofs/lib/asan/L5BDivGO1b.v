(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BDivGU L5BRed L5BDivHH L5BDivHS L5BDivGE L5BDivN L5BDivO1 L5BDivGN L5BDivGK L5BRzHuge L5BDivGK2 L5BDivGK3 L5BDivO2 L5BDivGO2 L5BDivGO2b L5BDivGO2c L5BDivGO1a L5BDivGO1e BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsAB0 L5OpMod1V L5Cmp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO1B.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGO2. Import L5ADVGO2B. Import L5ADVGO2C. Import L5ADVGO1A. Import L5ADVGK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac algn := lazymatch goal with |- ?h _ (Zpos _) => is_const h; lazymatch h with Z.le => fail | Z.lt => fail | Z.ge => fail | Z.gt => fail | _ => assumption end end.
Local Ltac sc := first [ asm | rk | gmem | algn | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis HSSH : L5OMA.stksh ar M (E - SCRD).
Hypothesis HSC8 : SCRD mod 8 = 0.
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
Local Notation HSCR0 := (L5ADVGA.HSCR0 SCRD HSCR).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation G1 := (L5ADVGA.g1 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G2s := (L5ADVGA.g2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G3 := (L5ADVGA.g3 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hnorm).
Local Notation G4s := (L5ADVGA.g4 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G5 := (L5ADVGA.g5 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation G6 := (L5ADVGB.g6 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G7 := (L5ADVGC.g7 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation G7b := (L5ADVGC.g7b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8 := (L5ADVGC.g8 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8b := (L5ADVGC.g8b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G9 := (L5ADVGC.g9 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation RSZ := (L5ADVHH.resize_stage L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR0 FFR1 FFRS Hrsz).
Local Notation ARG_AFTER := (L5ADVGN.arg_after L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation OREG_DISJ := (L5ADVGN.oreg_disj L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation GN_FRONT := (L5ADVGN.gn_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hcps Hnorm).
Local Notation G12C := (L5ADVGN.g12_copies L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation NORM_TOBS := (L5ADVGN.norm_tobs L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation STK_DEST := (L5ADVGN.stk_dest L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation ARSZ2 := (L5ADVGK3.arg_resize2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation G6A2 := (L5ADVGK3.g6_arg2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G5A := (L5ADVGK2.g5_arg L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation G9A := (L5ADVGK2.g9_arg L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
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
Local Notation G9T := (L5ADVGO2B.g9_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation GBT := (L5ADVGO2B.gB_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation G7T := (L5ADVGO2B.g7_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation MID1 := (L5ADVGO2.go2_mid1 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hasg Hrsz).
Local Notation FRONT := (L5ADVGO2.go2_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hcps Hnorm).
Local Notation FRONT1 := (L5ADVGO1A.go1_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hcps Hnorm).
Local Notation GEN_BACK := (L5ADVGO2C.gen_back L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hdel RA UR1 G2).
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
Lemma binv_swap W b1 b2 BXt Mc modelc LKc crc Ac : binv W (b1 :: b2 :: BXt) Mc modelc LKc crc Ac -> binv W (b2 :: b1 :: BXt) Mc modelc LKc crc Ac.
Proof.
  intros (B1 & REST). split. 2: exact REST. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (ND : NoDup (map fst ((b1 :: b2 :: BXt) ++ LB))) by (clear - WF0; decompose [and] WF0; assumption).
  assert (NDF : NoDup (map ff_addr FF')). { assert (X0 : NoDup (map ff_addr (FF' ++ LKc))) by (clear - WF0; decompose [and] WF0; assumption). rewrite map_app in X0. apply list_relations.list.NoDup_app in X0. exact (proj1 X0). }
  apply (aio_perm _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ B1). intros b. cbn [app In]. tauto.
  cbn [app map] in ND |- *. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. revert ND. apply Permutation_NoDup. apply perm_swap.
  intros f. reflexivity. exact NDF.
Qed.
Lemma afresh_in LBf LBt FFx LKx crx Ax Mx Vx q n : ri_inv HI LBf FFx LKx crx Ax Mx Vx -> In (q, n) LBf -> (forall b, In b LBt -> In b (lb_remove q LBf)) -> afresh L ar LBt (FFx ++ LKx) Mx q n.
Proof.
  intros HH Hin SUB. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (q, n) Hin) as (BR & BD & BS & _ & BA & BF & _). cbn [fst snd] in *.
  split. exact BR. split. intros b Hb. apply BA. apply SUB. exact Hb. split. exact BF. split. exact BD. exact BS.
Qed.
Lemma tob_sub LBx LBy Mk o b ws : tob LBx Mk o b ws -> (forall z, In z LBx -> In z LBy) -> tob LBy Mk o b ws.
Proof. intros (T1 & T2 & T3 & T4) SUB. split. exact T1. split. exact T2. split. exact T3. intros cap q Eq. exact (SUB _ (T4 cap q Eq)). Qed.
Lemma trk_sub BXx BXy Mk bn bd bn0 bd0 wn wd on0 cells x : trk BXx Mk bn bd bn0 bd0 wn wd on0 cells x -> (forall z, In z (BXx ++ LB) -> In z (BXy ++ LB)) -> trk BXy Mk bn bd bn0 bd0 wn wd on0 cells x.
Proof. intros (T1 & T2 & T3) SUB. split. exact (tob_sub _ _ _ _ _ _ T1 SUB). split. exact (tob_sub _ _ _ _ _ _ T2 SUB). exact T3. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incell := solve [cbn [In]; repeat (first [left; reflexivity | right])].
Lemma go1_all (bo qo fbx : Z) (bb : L5.bigobj) (wb : list Z) (fx1 : FPState) R1 M1 model1 LK1 A1 cc qn bits bn bd (Hunn : L5DIA.unnorm_specA L ar HI) :
  o1_e3_goal L ar HI R M model K LB FF LK A E SCRD F ro cr2 qo ->
  ri_inv HI LB FF LK cr2 A M (vml_of model) -> SCRD = L5DIA.DIVO_SCR ->
  L5OMA.stksh ar M (E - SCRD) -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 ->
  L5OMA.x_is_a M ro fbx -> aobj FF ro 32 -> shadow_zero M ro 4 ->
  L5OMA.b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 ->
  L5DIA.zero_obj M qo -> aobj FF qo 32 -> shadow_zero M qo 4 ->
  (ro + 32 <= bo \/ bo + 32 <= ro) -> (ro + 32 <= qo \/ qo + 32 <= ro) -> (bo + 32 <= qo \/ qo + 32 <= bo) ->
  L5.bo_dyn bb = false -> (L5.bo_len bb = 2%nat \/ (L5.bo_len bb = 1%nat /\ exists d0 d1, L5.bo_st bb = L5.BInl d0 d1 /\ 4294967296 <= d0)) ->
  L5OMA.acredit_for L cr2 L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) ->
  atG L ar HI R M model LB FF LK A E SCRD F ro Same Same R1 M1 model1 cr2 LK1 A1 ro qo qn bits 1 bn bd [L5PSA.A0; L5PSA.A1] wb ->
  incl A A1 -> incl LK1 LK ->
  (0 <= cc <= 1) -> (L5.bo_len bb = 2%nat -> cc = L5CMP.cmp_val [L5PSA.A0; L5PSA.A1] wb) ->
  L5.bo_len bn = 2%nat -> L5.bo_len bd = L5.bo_len bb -> L5.bo_st bn = L5.BInl L5PSA.A0 L5PSA.A1 -> L5.bo_st bd = L5.bo_st bb -> bits = 0 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
      L5DIA.divO1_postA L ar LB FF LK' cr2 M M' R R' ro bo qo E bb wb LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
          (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z),
      L5DIA.divO1_e3A L ar LB FF cr2 M M' R R' ro qo E F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' (L5DIA.ff_o FF E F3a F1b F3b F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x930a8 M1 model1) K.
Proof.
  intros HE3 HH0 ESCR SSH FFR5 FFR3 XOK AOR SZR BOK AOB SZB ZQ AOQ SZQ APXB APXQ APBQ DYBF NB12 CRF ATG IA1 ILK1 CCR CCV LNE LDE STN STD EBITS KF KE3.
  pose proof XOK as (OBX & SGX). set (bx := L5.BO fbx 2 (L5.BInl L5PSA.A0 L5PSA.A1)) in *.
  pose proof BOK as (OBB & OLB & REDB & INB0). pose proof OLB as (LWB & WBOK & WBST).
  pose proof ATG as (BI0 & RI0 & X18 & X21 & X22 & X25 & X26 & X27 & QNR & BITSR & TN & TD & ON & OD & SGN_N & SGN_D & SPL & DSH & HDR).
  assert (TX : tob LB M ro bx [L5PSA.A0; L5PSA.A1]).
  { pose proof OBX as (_ & _ & _ & (_ & _ & _ & _ & A0R & A1R)). split. exact OBX. split. { split. reflexivity. split. constructor; [exact A0R | constructor; [exact A1R | constructor]]. reflexivity. } split. exact SZR. intros cap q Eq. discriminate Eq. }
  assert (TQ0 : tob LB M qo (L5.BO 0 0 (L5.BInl 0 0)) []). { split. exact ZQ. split. { split. reflexivity. split. constructor. reflexivity. } split. exact SZQ. intros cap q Eq. discriminate Eq. }
  assert (INX : forall cap q, L5.bo_st bx = L5.BDyn cap q -> In (q, 8 * cap) LB). { intros cap q Eq. discriminate Eq. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model ro 32 E SCRD HH0 AOR ltac:(clear; lia) ltac:(reflexivity)) as ((RLO & RCE & RHI & R8 & _) & RBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model qo 32 E SCRD HH0 AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  (* [comment removed for export] *)
  set (nb := L5.bo_len bb) in *.
  assert (STB : exists b0 b1, L5.bo_st bb = L5.BInl b0 b1 /\ 0 <= b0 < 2 ^ 64 /\ 0 <= b1 < 2 ^ 64).
  { pose proof OBB as (_ & _ & _ & OST). destruct (L5.bo_st bb) as [b0 b1|cap q]. exists b0, b1. split. reflexivity. destruct OST as (_ & _ & _ & _ & R0' & R1'). split; assumption.
    exfalso. unfold L5.bo_dyn in DYBF. rewrite (proj1 OST) in DYBF. discriminate DYBF. }
  destruct STB as (b0 & b1 & STB & Rb0 & Rb1). rewrite STB in WBST. fold nb in WBST, LWB.
  assert (NB : nb = 1%nat \/ nb = 2%nat) by (destruct NB12 as [X0|(X0 & _)]; [right | left]; exact X0).
  assert (TOPB : nth_w wb (nb - 1) <> 0). { destruct REDB as [->|X0]. cbn [length] in LWB. exfalso. clear - LWB NB. lia. rewrite LWB in X0. exact X0. }
  assert (V1 : nb = 1%nat -> 2 ^ 32 <= b0). { intros N1. destruct NB12 as [X0|(_ & d0 & d1 & Eq & X0)]. exfalso. clear - X0 N1. subst nb. lia. rewrite STB in Eq. injection Eq as -> _. exact X0. }
  assert (V2 : nb = 2%nat -> BigFactsBase.val wb <= BigFactsBase.val [L5PSA.A0; L5PSA.A1]).
  { intros N2. pose proof (CCV N2) as EC0. destruct (Z.eq_dec cc 0) as [E0|N0].
    - rewrite E0 in EC0. symmetry in EC0. apply L5CMP.cmp_val_eq in EC0. clear - EC0. lia.
    - assert (E1 : cc = 1) by (clear - CCR N0; lia). rewrite E1 in EC0. symmetry in EC0. apply L5CMP.cmp_val_gt in EC0. clear - EC0. lia. }
  destruct (o1_vals nb b0 b1 wb NB WBST Rb0 Rb1 TOPB V1 V2) as (CR63 & L13 & N24 & LLE & NL2 & LRDL & LRD3 & NRNL & LRN4 & D63 & SECT & SECF & RD3 & RN3 & NB2C).
  set (c := L5DLA.clz_of (nth_w wb (nb - 1))) in *. set (sec := L5DLA.second nb (L5DLA.shl_result wb c)) in *.
  set (rd := L5DLA.norm_words wb c sec) in *. set (rn := L5DLA.norm_words [L5PSA.A0; L5PSA.A1] c sec) in *. set (l1 := rlen rd) in *. set (n1 := rlen rn) in *.
  set (BB := L5DIA.divO1_bytes (L5.bo_cap bb)) in *.
  assert (CAPB2 : L5.bo_cap bb = 2) by (unfold L5.bo_cap; rewrite STB; reflexivity).
  assert (RU8 : forall i, 0 <= i < 8 -> round_up i = 8). { intros i Hi. unfold round_up. rewrite Z.div_small by exact Hi. reflexivity. }
  assert (CINV1 : cinv cr2 cr2 L5DIA.DIVO1_K BB (2 + (1 + 1)) (128 + (64 + 64))).
  { unfold L5ADVGO2C.cinv. unfold L5DIA.DIVO1_K, BB, L5DIA.divO1_bytes, L5DIA.DIVN_K, L5DIA.DIVN_BYTES. exists 0, 0. rewrite L5ADVO1.adebits_0. split. reflexivity. rewrite CAPB2. clear. lia. }
  pose proof (dyn_kind M1 (F + 96) bn (proj1 TN)) as DKN. rewrite STN in DKN. cbn [skind] in DKN.
  pose proof (dyn_kind M1 (F + 32) bd (proj1 TD)) as DKD. rewrite STD, STB in DKD. cbn [skind] in DKD.
  pose proof (proj1 (proj2 TD)) as (LWD & _). 
  apply (FRONT1 cr2 qo [L5PSA.A0; L5PSA.A1] wb fx1 R1 M1 model1 cr2 LK1 A1 qn bits bn bd HH0 SSH ltac:(clear - RLO RHI; lia) ltac:(clear - QLO QHI; lia) DKN DKD).
  { rewrite LDE. fold nb. clear - NB; lia. }
  { rewrite LDE. exact TOPB. }
  { rewrite LDE. fold nb. intros N2. assert (E2 : nb = 2%nat) by (clear - N2 NB; lia). pose proof (NB2C E2) as C1. pose proof (L5OM1V.c_spec nb b0 b1 wb NB WBST Rb0 Rb1 TOPB V1 V2) as (_ & X0).
    change (L5OM1V.c nb wb) with c in X0. change (L5OM1V.top nb wb) with (nth_w wb (nb - 1)) in X0. assert (2 <= 2 ^ c) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; clear - C1; lia). clear - X0 H. nia. }
  { rewrite LNE. clear; lia. }
  { intros _. rewrite LNE. split. clear; lia. exists 1%nat. split. clear; lia. cbn. unfold L5PSA.A1. clear; lia. }
  { apply (cinv_for cr2 cr2 _ _ _ _ 2 128 CINV1 CRF). clear; lia. clear; lia. }
  { exact ATG. }
  intros fx4 R4 M4 model4 c' gd gn bn0 bd0 fbd' fbn' std stn cr4 LK4 A4. cbv zeta. rewrite LDE. fold nb. intros EC. subst c'. fold c. fold sec. fold rd. fold rn. fold l1. fold n1.
  intros BI4 RI4 KR4 p19 p25 p1 p10 p11 p20 p24 TD4 TN4 GRD GRN CPD CPN ON0 OD0 SPL4 S360 S120 S112 S272 HDR4 DSH4 U172 SGN4 ECR4 IA4 ILK4.
  set (BX4 := L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ []) in *.
  set (bn4 := L5.BO fbn' n1 stn) in *. set (bd4 := L5.BO fbd' l1 std) in *.
  set (l := Z.of_nat l1 - 1). set (n := Z.of_nat n1 - 1). set (sdv := if sec then 1 else 0) in *.
  replace (Z.of_nat l1) with (l + 1) in S112, S272 by (subst l; clear; lia).
  set (cells := [(E - 304, F + 32); (E - 344, 1); (E - 296, qo); (E - 264, ro); (E - 288, ro); (E - 328, bits); (E - 280, F + 96); (E - 312, qn); (E - 336, F); (E - 320, qo / 8 + 2147450880); (E - 352, (qo + 8) / 8 + 2147450880);
                 (E - 360, F); (E - 120, L5.bo_data (F + 32) bd4); (E - 112, l + 1); (E - 272, l + 1)]).
  assert (TRK4 : trk BX4 M4 bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cells c).
  { split. exact TN4. split. exact TD4. split. exact ON0. split. exact OD0. split. 2: split; [exact U172 | split; [exact HDR4 | exact DSH4]].
    intros a v Hin. unfold cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [try (apply SPL4; rewrite <- Hin; incell)|]). 5: destruct Hin.
    all: injection Hin as <- <-; split; [assumption | clear; lia]. }
  pose proof BI4 as (B4 & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B4) as WF4.
  assert (ND4 : NoDup (map fst (BX4 ++ LB))). { clear - WF4. decompose [and] WF4. assumption. }
  (* [comment removed for export] *)
  assert (GNS : match gn with Same => skind stn = None | Grown qA capA => capA = 8 /\ stn = L5.BDyn 8 qA end).
  { destruct gn as [|qA capA]. cbn [gro_st] in GRN. unfold L5ADVEA.same_store in GRN. rewrite STN in GRN. destruct stn. reflexivity. destruct GRN. destruct GRN as (_ & -> & ->). split; reflexivity. }
  assert (GDS : match gd with Same => skind std = None | Grown qA capA => capA = 8 /\ std = L5.BDyn 8 qA end).
  { destruct gd as [|qA capA]. cbn [gro_st] in GRD. unfold L5ADVEA.same_store in GRD. rewrite STD, STB in GRD. destruct std. reflexivity. destruct GRD. destruct GRD as (_ & -> & ->). split; reflexivity. }
  assert (FACTS4 : cinv cr2 cr4 L5DIA.DIVO1_K BB (1 + 1) (64 + 64) /\ (forall cap q, stn = L5.BDyn cap q -> In (q, 8 * cap) BX4) /\ (forall cap q, std = L5.BDyn cap q -> In (q, 8 * cap) BX4) /\
            exists B3, match blk_of bn4 with None => B3 = BX4 | Some (q, k) => In (q, k) BX4 /\ lb_remove q (BX4 ++ LB) = B3 ++ LB end /\
                       match blk_of bd4 with None => [] = B3 | Some (q, k) => In (q, k) B3 /\ lb_remove q (B3 ++ LB) = [] ++ LB end).
  { unfold blk_of. cbn [bn4 bd4 L5.bo_st]. subst cr4 BX4. destruct gn as [|qA capA]; destruct gd as [|qB capB]; cbn [L5DLA.blocks_of app L5DLA.adebl] in *.
    - unfold skind in GNS, GDS. destruct stn; [|discriminate GNS]. destruct std; [|discriminate GDS].
      split. apply (cinv_weak cr2 _ _ _ _ _ _ _ CINV1). clear; lia. clear; lia. split. intros ? ? X0; discriminate X0. split. intros ? ? X0; discriminate X0. exists []. split; reflexivity.
    - unfold skind in GNS. destruct stn; [|discriminate GNS]. destruct GDS as (-> & ->).
      split. apply (cinv_weak cr2 _ _ _ (1 + (1 + 1)) (64 + (64 + 64))). 2: clear; lia. 2: clear; lia. apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV1). clear; lia. clear; lia. clear; lia.
      split. intros ? ? X0; discriminate X0. split. intros cap q Eq. injection Eq as <- <-. left; reflexivity.
      exists [(qB, 8 * 8)]. split. reflexivity. split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity.
    - unfold skind in GDS. destruct std; [|discriminate GDS]. destruct GNS as (-> & ->).
      split. apply (cinv_weak cr2 _ _ _ (1 + (1 + 1)) (64 + (64 + 64))). 2: clear; lia. 2: clear; lia. apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV1). clear; lia. clear; lia. clear; lia.
      split. intros cap q Eq. injection Eq as <- <-. left; reflexivity. split. intros ? ? X0; discriminate X0.
      exists []. split. split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity. reflexivity.
    - destruct GNS as (-> & ->). destruct GDS as (-> & ->).
      split. apply (cinv_debit cr2 _ _ _ (1 + (1 + 1)) (64 + (64 + 64))). 2: clear; lia. 2: clear; lia. 2: clear; lia. apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV1). clear; lia. clear; lia. clear; lia.
      split. intros cap q Eq. injection Eq as <- <-. left; reflexivity. split. intros cap q Eq. injection Eq as <- <-. right; left; reflexivity.
      exists [(qB, 8 * 8)]. split. split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity. split. left; reflexivity. cbn [app]. rewrite lb_remove_head. reflexivity. }
  destruct FACTS4 as (CINV4 & INN4 & IND4 & B3 & L3 & Lf).
  assert (NNR : (2 <= n1 <= 269)%nat) by (clear - N24; lia).
  pose proof (dyn_kind M ro bx OBX) as DKX. cbn [bx L5.bo_st skind] in DKX.
  apply (MID1 cr2 qo bx [L5PSA.A0; L5PSA.A1] fx4 R4 M4 model4 BX4 LK4 cr4 A4 bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cells c n1 (n1 - l1)%nat HH0 TQ0 AOQ TX AOR APXQ BI4 RI4 p1 p10
           ltac:(rewrite p11; f_equal; clear - LLE; lia) p25 ltac:(rewrite (KR4 26%nat) by inl; exact X26) TRK4
           ltac:(unfold cells; incell) ltac:(unfold cells; incell) ltac:(unfold cells; incell) ltac:(unfold cells; incell)
           ltac:(intros c0 v Hin; unfold cells in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; clear; lia|]); destruct Hin) eq_refl NNR ltac:(clear; lia)).
  { intros DY. rewrite DKX in DY. discriminate DY. }
  { intros ? ? ? ? _ Eq. discriminate Eq. } { intros ? ? ? ? _ Eq. discriminate Eq. }
  { rewrite DKX. apply (cinv_for cr2 cr4 _ _ _ _ _ _ CINV4 CRF). clear; lia. rewrite (RU8 (Z.of_nat (n1 - l1))) by (clear - NL2; lia). rewrite (RU8 (Z.of_nat n1)) by (clear - N24; lia). clear; lia. }
  intros fx7 R7 M7 model7 gq gr bq br W7 cr7 LK7 A7 wq BX5 BX7 BI7 RI7 EW7 KR7 q22 S136_7 S128_7 TQ7 LENQ7 FBQ7 GQF TR7 LENR7 GRF TRK7 ECR7 IA7 ILK7.
  assert (GQS : gq = Same). { destruct gq as [|qq capq]. reflexivity. exfalso. destruct GQF as (_ & _ & N3). clear - N3 NL2. lia. }
  subst gq. cbn iota in GQF.
  set (LBy7 := L5DLA.blocks_of gr).
  assert (EBX7 : BX7 = (LBy7 ++ []) ++ BX4). { subst BX7 BX5 LBy7. destruct gr; reflexivity. }
  clearbody BX7. clear BX5. subst BX7.
  pose proof (dyn_kind M7 qo bq (proj1 TQ7)) as DKQ. pose proof (dyn_kind M7 ro br (proj1 TR7)) as DKR.
  assert (KQ7 : skind (L5.bo_st bq) = None). { rewrite GQF in DKQ. destruct (skind (L5.bo_st bq)). discriminate DKQ. reflexivity. }
  assert (RSC7 : match skind (L5.bo_st bx), skind (L5.bo_st br) with
                 | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LBy7 = []
                 | None, None => LBy7 = []
                 | None, Some (cap', q') => cap' = 8 /\ LBy7 = [(q', 64)]
                 | Some _, None => False end).
  { subst LBy7. cbn [bx L5.bo_st skind]. destruct gr as [|qr capr].
    - destruct GRF as (_ & SS). rewrite (skind_same _ _ SS). reflexivity.
    - destruct GRF as (_ & ST & EC & _). rewrite ST. cbn [skind L5DLA.blocks_of]. rewrite (RU8 (Z.of_nat n1)) in EC by (clear - N24; lia). subst capr. split; reflexivity. }
  assert (QSC7 : match skind (L5.bo_st bq) with None => @nil (Z * Z) = [] | Some (cap, q) => [] = [(q, 8 * cap)] end). { rewrite KQ7. reflexivity. }
  assert (DYR : L5.bo_dyn br = match gr with Same => false | Grown _ _ => true end).
  { destruct gr as [|qr capr]. rewrite DKR. rewrite (skind_same _ _ (proj2 GRF)). reflexivity. rewrite DKR. destruct GRF as (_ & -> & _). reflexivity. }
  assert (CINV7 : cinv cr2 cr7 L5DIA.DIVO1_K BB ((if L5.bo_dyn br then 0 else 1) + 1) ((if L5.bo_dyn br then 0 else 64) + 64)).
  { rewrite DYR. subst cr7. destruct gr as [|qr capr]; cbn [L5DLA.blocks_of L5DLA.adebl]. exact CINV4.
    destruct GRF as (_ & _ & -> & _). rewrite (RU8 (Z.of_nat n1)) by (clear - N24; lia). apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV4). clear; lia. clear; lia. clear; lia. }
  assert (NCL7 : forall q k a, In (q, k) ((LBy7 ++ []) ++ BX4) -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a).
  { intros q k a Hin Ha. exact (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W7 _ M7 model7 LK7 cr7 A7 q k a BI7 Hin Ha). }
  pose proof (len_le_cap M7 qo bq (proj1 TQ7)) as LCQ7. fold (L5.bo_cap bq) in LCQ7.
  assert (WSUB7 : forall a, L5.outside [(ro, 32); (qo, 32)] a -> L5.outside W7 a).
  { intros a Ho. rewrite EW7. intros rr Hr IR. unfold L5.in_rng in IR. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in IR.
    - apply (Ho (qo, 32)). right; left; reflexivity. exact IR.
    - unfold L5.bo_data, L5.bo_cap in IR, LCQ7. unfold skind in KQ7. destruct (L5.bo_st bq) as [v0 v1|? ?]. 2: discriminate KQ7. apply (Ho (qo, 32)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - IR LCQ7; lia.
    - apply (Ho (ro, 32)). left; reflexivity. exact IR.
    - cbn [bx L5.bo_data L5.bo_cap L5.bo_st] in IR. apply (Ho (ro, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - IR; lia. }
  assert (TB : tob LB M bo bb wb). { split. exact OBB. split. exact OLB. split. exact SZB. intros cap q Eq. rewrite STB in Eq. discriminate Eq. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model bo 32 E SCRD HH0 AOB ltac:(clear; lia) ltac:(reflexivity)) as ((BLO & BCE & BHI & B8 & _) & BBIG & _).
  assert (FIN : forall LByx LBqx (bqx brx : L5.bigobj) crx dk db,
     match skind (L5.bo_st bx), skind (L5.bo_st brx) with
     | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LByx = []
     | None, None => LByx = []
     | None, Some (cap', q') => cap' = 8 /\ LByx = [(q', 64)]
     | Some _, None => False end ->
     match skind (L5.bo_st bqx) with None => LBqx = [] | Some (cap, q) => LBqx = [(q, 8 * cap)] end ->
     (forall q k a, In (q, k) LByx -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a) ->
     cinv cr2 crx L5DIA.DIVO1_K BB dk db -> 0 <= dk -> 0 <= db ->
     forall (fxf : FPState) Rf Mf modelf Af crf LKf bqf wqf brf wrf fb',
      regs_preserved R Rf -> incl A Af -> incl LKf LK -> ahpres L ar LB FF E SCRD (W7 ++ [(L5.bo_data ro brx, 8 * L5.bo_cap brx)]) M Mf ->
      L5.big_at RSEGS Mf qo bqf -> L5C.obj_limbs RSEGS Mf bqf wqf -> skind (L5.bo_st bqf) = skind (L5.bo_st bqx) ->
      L5.big_at RSEGS Mf ro brf -> L5C.obj_limbs RSEGS Mf brf wrf -> skind (L5.bo_st brf) = skind (L5.bo_st brx) ->
      L5.bo_fb brf = Z.lor (Z.land fb' 253) bits -> Z.testbit fb' 1 = false ->
      L5OMA.acredit_after L crx L5DIA.DIVN_K L5DIA.DIVN_BYTES crf -> model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI ((LByx ++ LBqx) ++ LB) FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K).
  { intros LByx LBqx bqx brx crx dk db RSCx QSCx NCLx CINVx DK0 DB0 fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf IAf ILKf AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as WFf. assert (NDf : NoDup (map fst ((LByx ++ LBqx) ++ LB))) by (clear - WFf; decompose [and] WFf; assumption).
    cbn [bx L5.bo_st skind] in RSCx.
    apply (KF fxf Rf Mf modelf (LByx ++ LBqx ++ LB) crf LKf Af). 2: exact RTf. 2: exact IAf. 2: exact AMf. 2: exact ILKf. 2: { rewrite app_assoc. exact HHf. }
    assert (AHW : ahpres L ar LB FF E L5DIA.DIVO_SCR [(ro, 32); (qo, 32)] M Mf).
    { rewrite ESCR in AHf. destruct AHf as (EK & DFK). split. 2: exact DFK. intros a (Ha & Hc & Ho). rewrite <- ESCR in Hc. apply EK. split. exact Ha. split. rewrite <- ESCR. exact Hc.
      apply L5.outside_app. split. exact (WSUB7 a Ho). intros rr [<-|[]] IR. unfold L5.in_rng in IR. cbn [fst snd] in IR. unfold L5.bo_data, L5.bo_cap in IR.
      destruct (L5.bo_st brx) as [v0 v1|capx qx] eqn:EBX. apply (Ho (ro, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - IR; lia.
      cbn [skind] in RSCx. destruct RSCx as (-> & ->). apply (NCLx qx 64 a). left; reflexivity. clear - IR; lia. exact Hc. }
    split. exact RPf.
    split. { exists LByx, LBqx. split. reflexivity.
      split. { exists brf, wrf. split. exact OBRf. split. exact OLRf. split. { unfold L5.bo_neg. rewrite FBRf, EBITS, Z.lor_0_r, Z.land_spec. change (Z.testbit 253 1) with false. apply andb_false_r. }
               rewrite <- KRf in RSCx. unfold skind in RSCx. destruct (L5.bo_st brf) as [u0 u1|capf qf]. exact RSCx.
               destruct RSCx as (-> & ->). split. reflexivity. split. reflexivity. cbn [app] in HHf. exact (L5ADH.afresh_of_inv L ar C HI HIok qf 64 _ FF LKf crf Af Mf (vml_of modelf) HHf). }
      exists bqf, wqf. split. exact OBQf. split. exact OLQf. rewrite <- KQf in QSCx. unfold skind in QSCx. destruct (L5.bo_st bqf) as [u0 u1|capf qf]. exact QSCx.
      split. exact QSCx. apply (afresh_in _ LB FF LKf crf Af Mf (vml_of modelf) qf (8 * capf) HHf). rewrite QSCx. apply in_or_app. left. apply in_or_app. right. left; reflexivity.
      intros b Hb. apply L5ADVHO.in_lb_remove. apply in_or_app. right. exact Hb. intros X0.
      exact (L5ADVHO.nodup_app_fst (LByx ++ LBqx) LB (qf, 8 * capf) b NDf ltac:(rewrite QSCx; apply in_or_app; right; left; reflexivity) Hb (eq_sym X0)). }
    destruct (L5ADVO1.arg_kept L ar C HI LY HIok M Mf model LB FF LK cr2 A E L5DIA.DIVO_SCR _ bo bb wb HH0 AHW AOB TB) as (OBBf & OLBf).
    { intros a OR rr Hr IR. unfold L5.in_rng in IR. destruct OR as [OR|[OR|(cap & q & Eq & _)]]. 3: { rewrite STB in Eq. discriminate Eq. }
      - destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in IR. clear - OR IR APXB; lia. clear - OR IR APBQ; lia.
      - unfold SB in OR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in IR. clear - OR IR BLO BHI RLO RBIG. lia. clear - OR IR BLO BHI QLO QBIG. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. exact OBBf. split. exact OLBf. split. fold nb. clear - NB; lia.
    split. { exact (cinv_fin cr2 crx _ _ dk db crf CINVx DK0 DB0 CRAf). }
    exact AHW. }
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (WQH7 : forall a, qo <= a < qo + 32 -> ~ L5.outside W7 a). { intros a Ha OUT. rewrite EW7 in OUT. apply (OUT (qo, 32)). left; reflexivity. exact Ha. }
  assert (WRH7 : forall a, ro <= a < ro + 32 -> ~ L5.outside W7 a). { intros a Ha OUT. rewrite EW7 in OUT. apply (OUT (ro, 32)). right; right; left; reflexivity. exact Ha. }
  assert (WY7 : forall cap q a, L5.bo_st bx = L5.BDyn cap q -> q <= a < q + 8 * cap -> ~ L5.outside W7 a). { intros cap q a Eq. discriminate Eq. }
  assert (WSH7 : forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W7 a).
  { intros a Hs. apply WSUB7. intros rr [<-|[<-|[]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    exact (SH_OBJ W7 _ M7 model7 LK7 cr7 A7 ro a BI7 AOR' Hs IR). exact (SH_OBJ W7 _ M7 model7 LK7 cr7 A7 qo a BI7 AOQ' Hs IR). }
  assert (SGR7 : Z.testbit (L5.bo_fb br) 1 = false).
  { assert (X0 : forall g, Z.testbit (assign_fb (L5.bo_fb bx) (L5.bo_fb bn4) n1 g) 1 = false).
    { intros g. unfold assign_fb. destruct (Nat.eqb_spec n1 0) as [E0|_]. exfalso. clear - E0 NNR. Lia.lia. rewrite Z.lor_spec, !Z.land_spec. cbn [bn4 L5.bo_fb]. rewrite SGN4.
      change (Z.testbit 253 1) with false. rewrite !andb_false_r. reflexivity. }
    destruct gr as [|qr capr]. rewrite (proj1 GRF). apply X0. rewrite (proj1 GRF). apply X0. }
  assert (CINV3 : forall crx dk db, cinv cr2 crx L5DIA.DIVO1_K BB dk db -> 0 <= dk -> 0 <= db -> L5OMA.acredit_for L crx L5DIA.DIVN_K L5DIA.DIVN_BYTES).
  { intros crx dk db CI DK DB. unfold L5ADVGO2C.cinv in CI. destruct CI as (k & b & -> & K0 & B0 & K1 & B1). destruct CRF as (C1 & C2). destruct (aly_cost L C LY) as (P1 & P2 & P3).
    unfold L5DIA.DIVN_K, L5DIA.DIVN_BYTES in *. unfold L5OMA.acredit_for, L5OMA.adebits. cbn [fst snd]. split. clear - C1 K0 K1 DK P1. nia. clear - C2 K0 K1 B0 B1 DK DB P2 P3. nia. }
  assert (SDV : sdv = 0 \/ sdv = 1) by (subst sdv; destruct sec; [right | left]; reflexivity).
  assert (SEC1 : sdv = 1 -> sec = true) by (subst sdv; destruct sec; intros X0; [reflexivity | discriminate X0]).
  (* [comment removed for export] *)
  assert (BRDYN : sec = true -> exists qx, L5.bo_st br = L5.BDyn 8 qx /\ LBy7 = [(qx, 64)]).
  { intros ST. destruct (SECT ST) as (_ & _ & N3 & _). cbn [bx L5.bo_st skind] in RSC7. destruct (L5.bo_st br) as [v0 v1|capr qr] eqn:EBR.
    - exfalso. pose proof (proj1 TR7) as (_ & _ & _ & OST). rewrite EBR in OST. destruct OST as (_ & _ & _ & L2 & _). rewrite LENR7 in L2. clear - L2 N3. lia.
    - cbn [skind] in RSC7. destruct RSC7 as (-> & EL). exists qr. split. reflexivity. exact EL. }
  assert (GNG : sec = true -> exists d3 d4, gn = Grown d3 8 /\ gd = Grown d4 8).
  { intros ST. destruct (SECT ST) as (_ & _ & _ & LR3 & LN3).
    destruct gn as [|d3 c3]. { exfalso. unfold skind in GNS. destruct stn. cbn in CPN. clear - CPN LN3. lia. discriminate GNS. }
    destruct gd as [|d4 c4]. { exfalso. unfold skind in GDS. destruct std. cbn in CPD. clear - CPD LR3. lia. discriminate GDS. }
    exists d3, d4. rewrite (proj1 GNS), (proj1 GDS). split; reflexivity. }
  (* [comment removed for export] *)
  assert (KE3g : forall LByx LBqx (brx bqx : L5.bigobj) crx LKx Ax cellsx,
      (sec = true -> exists qx, L5.bo_st brx = L5.BDyn 8 qx /\ LByx = [(qx, 64)] /\ LBqx = []) -> (sec = true -> skind (L5.bo_st bqx) = None) ->
      (sec = true -> credit_le (L5OMA.adebits L cr2 3 192) crx /\ credit_le crx (L5OMA.adebits L cr2 3 192)) ->
      (forall c0 v, In (c0, v) cells -> In (c0, v) cellsx) -> In (E - 376, sdv) cellsx -> incl A Ax -> incl LKx LK ->
      forall (fx2 : FPState) R2 M2' model2' (bq2 br2 : L5.bigobj) (wq2 wr2 : list Z),
      binv W7 ((LByx ++ LBqx) ++ BX4) M2' model2' LKx crx Ax -> rinvD R E R2 ->
      (getr R2 (reg 1) = Z_to_bv 64 0x934bc /\ getr R2 (reg 18) = Z_to_bv 64 SH /\ getr R2 (reg 19) = Z_to_bv 64 ro /\ getr R2 (reg 20) = Z_to_bv 64 qo /\ getr R2 (reg 22) = Z_to_bv 64 F /\ getr R2 (reg 24) = Z_to_bv 64 (F + 32) /\ getr R2 (reg 25) = Z_to_bv 64 (F + 96) /\ getr R2 (reg 27) = Z_to_bv 64 F) ->
      skind (L5.bo_st bq2) = skind (L5.bo_st bqx) ->
      tob (((LByx ++ LBqx) ++ BX4) ++ LB) M2' qo bq2 wq2 -> tob (((LByx ++ LBqx) ++ BX4) ++ LB) M2' ro br2 wr2 -> skind (L5.bo_st br2) = skind (L5.bo_st brx) -> L5.bo_len br2 = L5.bo_len brx ->
      trk ((LByx ++ LBqx) ++ BX4) M2' bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cellsx c ->
      forall (fx' : FPState) R' M' model' qX LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
      sdv = 1 -> L5.bo_st br2 = L5.BDyn 8 qX ->
      L5DIA.unnorm_e3A L ar (((LByx ++ LBqx) ++ BX4) ++ LB) FF' crx M2' M' R2 R' ro qX (L5.bo_len br2) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model2' model' -> incl Ax A' -> amodel_ok A' model' -> incl LK' LKx ->
      ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K).
  { intros LByx LBqx brx bqx crx LKx Ax cellsx SHAPE KQx CRX INCX IN376x IAx ILKx fx2 R2 M2' model2' bq2 br2 wq2 wr2 BI2 RI2 REGS2 KQ2 TQ2 TR2 KR2 LENR2 TRK2
           fx' R' M' model' qX LB' cr' LK' A' F1 fl1 F3 fl3 F1c fl1c F1d fl1d S1 EBR2 E3A RT' IA' AM' ILK' HH'.
    pose proof (SEC1 S1) as ST. destruct (SHAPE ST) as (qx & EBRX & -> & ->). destruct (GNG ST) as (d3 & d4 & EGN & EGD). destruct (CRX ST) as (CL1 & CL2).
    assert (EQX : qX = qx). { rewrite EBRX in KR2. cbn [skind] in KR2. apply skind_dyn in KR2. rewrite KR2 in EBR2. injection EBR2 as <-. reflexivity. }
    subst qX. rewrite EGN in GNS. rewrite EGD in GDS. destruct GNS as (_ & ESTN). destruct GDS as (_ & ESTD).
    assert (EBX : (([(qx, 64)] ++ []) ++ BX4) = [(qx, 64); (d3, 8 * 8); (d4, 8 * 8)]). { subst BX4. rewrite EGN, EGD. reflexivity. }
    rewrite EBX in BI2, TQ2, TR2, TRK2, E3A.
    pose proof (dyn_kind M2' qo bq2 (proj1 TQ2)) as DK2. rewrite KQ2, (KQx ST) in DK2.
    refine (HE3 KE3 qx d3 d4 W7 bq2 br2 bn4 bd4 bn0 bd0 wq2 wr2 _ _ _ c R2 M2' model2' LKx crx Ax HH0 ESCR SSH AOR AOQ ltac:(clear - APXQ; lia) WSUB7 BI2 RI2 REGS2 TQ2 DK2 TR2 EBR2 TRK2 ESTN ESTD _ _ _ _ _ _ _ _ CL1 CL2
              fx' R' M' model' LB' cr' LK' A' F1 fl1 F3 fl3 F1c fl1c F1d fl1d E3A RT' IA' AM' ILK' HH').
    1: { subst sdv. rewrite ST in IN376x. exact IN376x. }
    all: apply INCX; unfold cells; incell. }
  (* [comment removed for export] *)
  set (cells7 := (E - 136, L5.bo_data qo bq) :: (E - 128, Z.of_nat (n1 - l1)) :: cells).
  assert (TRK7' : trk ((LBy7 ++ []) ++ BX4) M7 bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cells7 c).
  { apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ cells cells7 _ TRK7). intros a v [Eq|[Eq|Hin]]. injection Eq as <- <-. right. split. exact S136_7. clear; lia.
    injection Eq as <- <-. right. split. exact S128_7. clear; lia. left. exact Hin. }
  assert (CELLS7 : forall c0 v, In (c0, v) cells7 -> (c0 + 8 <= E - 376 \/ E - 360 <= c0) /\ (c0 + 8 <= E - 240 \/ E - 224 <= c0)).
  { intros c0 v Hin. unfold cells7, cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; clear; lia|]). destruct Hin. }
  assert (USCR : 384 + L5DIA.UNNORM_SCR <= SCRD) by (rewrite ESCR; unfold L5DIA.DIVO_SCR; clear; lia).
  assert (SCR8 : SCRD mod 8 = 0) by (rewrite ESCR; reflexivity).
  assert (D63' : 2 ^ 63 <= nth_w (firstn l1 rd) (Z.to_nat l)). { replace (Z.to_nat l) with (l1 - 1)%nat by (subst l; clear - L13; lia). rewrite nth_w_firstn by (clear - L13; lia). exact (proj1 D63). }
  apply (G7T qo fx7 R7 M7 model7 W7 _ LK7 cr7 A7 bq br bn4 bd4 bn0 bd0 wq (firstn n1 rn) (firstn n1 rn) (firstn l1 rd) None cells7 c n l sdv BI7 RI7 AOQ AOR
           ltac:(rewrite (KR7 20%nat) by inl; rewrite p20; f_equal; subst n; clear; lia) q22 ltac:(rewrite (KR7 24%nat) by inl; exact p24) ltac:(clear - SDV; lia)
           TQ7 TR7 TRK7' ltac:(rewrite LENR7; subst n; clear; lia) ltac:(cbn [bd4 L5.bo_len]; subst l; clear; lia) ltac:(subst n; clear - NNR; lia) ltac:(subst l; clear - L13; lia)
           ltac:(unfold cells7, cells; incell) ltac:(unfold cells7, cells; incell) CELLS7 WSH7).
  intros fx8 Rg Mg modelg BI8 RI8 KR8 r19 r21 r22 r27 TQ8 TR8 TRK8 S232 S240 S376 S368.
  assert (X18g : getr Rg (reg 18) = Z_to_bv 64 SH). { rewrite (KR8 18%nat) by inl. rewrite (KR7 18%nat) by inl. rewrite (KR4 18%nat) by inl. exact X18. }
  assert (IA7' : incl A A7) by (intros z Hz; apply IA7, IA4, IA1; exact Hz). assert (ILK7' : incl LK7 LK) by (intros z Hz; apply ILK1, ILK4, ILK7; exact Hz).
  assert (CRX7 : sec = true -> credit_le (L5OMA.adebits L cr2 3 192) cr7 /\ credit_le cr7 (L5OMA.adebits L cr2 3 192)).
  { intros ST. destruct (GNG ST) as (d3 & d4 & EGN & EGD). destruct (BRDYN ST) as (qx & EBR & ELY). subst cr7 cr4. rewrite EGN, EGD. destruct gr as [|qr capr]. { exfalso. subst LBy7. discriminate ELY. }
    destruct GRF as (_ & _ & -> & _). rewrite (RU8 (Z.of_nat n1)) by (clear - N24; lia). cbn [L5DLA.blocks_of L5DLA.adebl app]. unfold credit_le, L5OMA.adebits, adebit. cbn [fst snd]. clear. split; split; lia. }
  destruct (Z.ltb_spec (nth_w (firstn n1 rn) (Z.to_nat n)) (nth_w (firstn l1 rd) (Z.to_nat l))) as [LT|GE].
  - (* [comment removed for export] *)
    set (cellsA := (E - 240, L5.bo_data ro br) :: (E - 376, sdv) :: (E - 368, ro / 8 + 2147450880) :: cells7).
    assert (TRKA : trk ((LBy7 ++ []) ++ BX4) Mg bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cellsA c).
    { apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ cells7 cellsA _ TRK8). intros a v [Eq|[Eq|[Eq|Hin]]]. injection Eq as <- <-. right. split. exact S240. clear; lia.
      injection Eq as <- <-. right. split. exact S376. clear; lia. injection Eq as <- <-. right. split. exact S368. clear; lia. left. exact Hin. }
    apply (GEN_BACK fx8 Rg Mg modelg W7 BX4 BX4 B3 LBy7 [] LK7 cr7 A7 qo qn bits sdv l n bx bq br bn4 bd4 bn0 bd0 wq (firstn n1 rn) (firstn n1 rn) (firstn l1 rd) None cellsA c Hunn BI8 RI8 r19 r27
             X18g AOR AOQ ltac:(clear - APXQ; lia) TR8 TQ8 TRKA
             ltac:(rewrite LENR7; subst n; clear; lia) ltac:(rewrite LENQ7; subst n l; clear - LLE; lia) ltac:(cbn [bd4 L5.bo_len]; subst l; clear; lia) ltac:(subst n l; clear - LLE N24; lia) ltac:(subst l; clear - L13; lia)
             D63' SGR7).
    all: try (unfold cellsA, cells7, cells; incell).
    { exact QNR. } { exact BITSR. } { exact SDV. } { exact CR63. }
    { intros c0 v Hin. unfold cellsA, cells7, cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; clear; lia|]). destruct Hin. }
    { exact SSH. } { exact USCR. } { exact SCR8. } { exact FFR5. } { exact FFR3. } { exact WQH7. } { exact WRH7. } { exact WY7. } { exact WSH7. } { exact INX. } { exact INN4. } { exact IND4. }
    { exact RSC7. } { exact QSC7. }
    { intros S1. destruct (BRDYN (SEC1 S1)) as (qx & EBR & _). exists qx. split. exact EBR. rewrite LENR7. destruct (SECT (SEC1 S1)) as (_ & _ & N3 & _). clear - N3 N24. lia. }
    { intros _. apply (CINV3 cr7 _ _ CINV7). destruct (L5.bo_dyn br); clear; lia. destruct (L5.bo_dyn br); clear; lia. }
    { reflexivity. } { exact L3. } { exact Lf. }
    2: { apply (KE3g LBy7 [] br bq cr7 LK7 A7 cellsA). intros ST. destruct (BRDYN ST) as (qx & EBR & ELY). exists qx. split. exact EBR. split. exact ELY. reflexivity. intros _; exact KQ7. exact CRX7. intros c0 v Hin; unfold cellsA, cells7; do 5 right; exact Hin. unfold cellsA; right; left; reflexivity. exact IA7'. exact ILK7'. }
    intros fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf IAf ILKf AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf.
    refine (FIN LBy7 [] bq br cr7 _ _ RSC7 QSC7 _ CINV7 _ _ fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf _ _ AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf).
    + intros q k a Hin Ha. apply (NCL7 q k a). apply in_or_app. left. apply in_or_app. left. exact Hin. exact Ha.
    + destruct (L5.bo_dyn br); clear; lia.
    + destruct (L5.bo_dyn br); clear; lia.
    + intros z Hz. apply IAf, IA7'. exact Hz.
    + intros z Hz. apply ILK7', ILKf. exact Hz.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (cells8 := (E - 376, sdv) :: (E - 368, ro / 8 + 2147450880) :: cells).
    assert (TRK8' : trk ((LBy7 ++ []) ++ BX4) Mg bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cells8 c).
    { apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ cells7 cells8 _ TRK8). intros a v [Eq|[Eq|Hin]]. injection Eq as <- <-. right. split. exact S376. clear; lia.
      injection Eq as <- <-. right. split. exact S368. clear; lia. left. right; right. exact Hin. }
    assert (INC8 : forall c0 v, In (c0, v) cells -> In (c0, v) cells8) by (intros c0 v Hin; right; right; exact Hin).
    assert (S232' : L5.u64_at RSEGS Mg (E - 232) (Z.of_nat (Datatypes.S (n1 - 1)))). { replace (Datatypes.S (n1 - 1)) with (L5.bo_len br) by (rewrite LENR7; clear - NNR; lia). exact S232. }
    assert (S128g : L5.u64_at RSEGS Mg (E - 128) (Z.of_nat (n1 - l1))). { exact (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK8 ltac:(right; left; reflexivity)). }
    destruct (DIST5 W7 BX4 LBy7 [] Mg modelg LK7 cr7 A7 bx bq br bn4 bd4 BI8 INX INN4 IND4 RSC7 QSC7) as (NQB & NQNR & NQNQ & NQDR & NQDQ & RB7 & QB7).
    assert (SLKB : L5.bo_dyn br = true -> Z.of_nat n1 + 1 <= L5.bo_cap br /\ (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * L5.bo_cap br -> aclient L ar LB FF E SCRD a -> ~ L5.outside W7 a)).
    { intros DY. rewrite DKR in DY. unfold L5.bo_cap, L5.bo_data. destruct (L5.bo_st br) as [v0 v1|capr qr] eqn:EBR. discriminate DY. destruct (RB7 capr qr eq_refl) as [(EY & _)|Hin]. discriminate EY.
      split. 2: { intros a Ha Hc. exfalso. exact (NCL7 qr (8 * capr) a ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) Ha Hc). }
      destruct gr as [|qg capg]. { exfalso. subst LBy7. destruct Hin. } destruct GRF as (_ & ST & EC & _). injection ST as -> ->. rewrite EC, (RU8 (Z.of_nat n1)) by (clear - N24; lia). clear - N24; lia. }
    assert (RU9 : round_up (Z.of_nat n1 + 1) = 8 /\ round_up (Z.of_nat (n1 - l1) + 1) = 8). { split; apply RU8. clear - N24; lia. clear - NL2; lia. }
    apply (GBT fx8 Rg Mg modelg W7 _ LK7 cr7 A7 qo br bq bn4 bd4 bn0 bd0 (firstn n1 rn) wq (firstn n1 rn) (firstn l1 rd) None cells8 c (n1 - 1)%nat (n1 - l1)%nat BI8 RI8 AOR AOQ
             ltac:(clear - APXQ; lia) ltac:(clear - QLO QHI; lia)
             ltac:(rewrite (KR8 20%nat) by inl; rewrite (KR7 20%nat) by inl; rewrite p20; f_equal; clear - NNR; lia) r21 r22
             ltac:(rewrite (KR8 26%nat) by inl; rewrite (KR7 26%nat) by inl; rewrite (KR4 26%nat) by inl; exact X26)
             TR8 ltac:(rewrite LENR7; clear - NNR; lia) TQ8 LENQ7 TRK8' ltac:(apply INC8; unfold cells; incell) ltac:(apply INC8; unfold cells; incell) ltac:(apply INC8; unfold cells; incell) ltac:(apply INC8; unfold cells; incell)
             ltac:(right; left; reflexivity) S232' S128g
             ltac:(intros c0 v Hin; unfold cells8, cells in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; clear; lia|]); destruct Hin)
             ltac:(clear - N24; lia) ltac:(clear - N24; lia)).
    { intros DY. destruct (SLKB DY) as (X0 & _). clear - X0 NNR. lia. }
    { intros DY. rewrite GQF in DY. discriminate DY. }
    { rewrite GQF. replace (Z.of_nat (n1 - 1) + 2) with (Z.of_nat n1 + 1) by (clear - NNR; lia). rewrite (proj1 RU9), (proj2 RU9).
      apply (cinv_for cr2 cr7 _ _ _ _ _ _ CINV7 CRF). destruct (L5.bo_dyn br); clear; lia. destruct (L5.bo_dyn br); clear; lia. }
    { intros a OUT. rewrite EW7 in OUT. split; intros rr [<-|[]]; apply OUT. right; right; left; reflexivity. left; reflexivity. }
    { intros [DY|X0] a Hc OUT IR. 2: { exfalso. clear - X0 NNR. Lia.lia. } destruct (SLKB DY) as (X0 & COV). apply (COV a). 2: exact Hc. 2: exact OUT.
      unfold L5.in_rng in IR. cbn [fst snd] in IR. clear - IR X0 NNR. lia. }
    { intros [DY|X0] a Hc OUT IR. rewrite GQF in DY. discriminate DY. unfold L5.in_rng in IR. cbn [fst snd] in IR. unfold L5.bo_data in IR. unfold skind in KQ7. destruct (L5.bo_st bq) as [v0 v1|? ?]. 2: discriminate KQ7.
      apply (WQH7 a). clear - IR X0. lia. exact OUT. }
    { exact NQB. } { exact NQNR. } { exact NQNQ. } { exact NQDR. } { exact NQDQ. }
    intros fx9 R9 M9 model9 gr9 gq9 br9 bq9 cr9 LK9 A9 BXr BX9 BI9 RI9 KR9 s19 TR9 LENR9 GRF9 TQ9 LENQ9 GQF9 TRK9 S240_9 S136_9 ECR9 IA9 ILK9.
    set (LBy9 := L5DLA.blocks_of gr9 ++ LBy7). set (LBq9 := L5DLA.blocks_of gq9).
    pose proof (dyn_kind M9 qo bq9 (proj1 TQ9)) as DKQ9. pose proof (dyn_kind M9 ro br9 (proj1 TR9)) as DKR9.
    assert (GR9S : forall q9 c9, gr9 = Grown q9 c9 -> gr = Same). { intros q9 c9 ->. destruct GRF9 as (_ & _ & _ & DRF & _). rewrite DYR in DRF. destruct gr. reflexivity. discriminate DRF. }
    (* [comment removed for export] *)
    assert (PERM9 : binv W7 ((LBy9 ++ LBq9) ++ BX4) M9 model9 LK9 cr9 A9 /\ (forall z, In z (BX9 ++ LB) -> In z (((LBy9 ++ LBq9) ++ BX4) ++ LB))).
    { subst BX9 BXr LBy9 LBq9 LBy7. destruct gq9 as [|qq9 cq9].
      - split. destruct gr9; destruct gr; exact BI9. intros z Hz. destruct gr9; destruct gr; exact Hz.
      - destruct gr9 as [|qr9 cr9'].
        + destruct gr as [|qr capr]. split. exact BI9. intros z Hz; exact Hz.
          cbn [L5DLA.blocks_of app] in *. split. exact (binv_swap _ _ _ _ _ _ _ _ _ BI9). intros z [Hz|[Hz|Hz]]; [right; left | left | right; right]; exact Hz.
        + rewrite (GR9S qr9 cr9' eq_refl) in *. cbn [L5DLA.blocks_of app] in *. split. exact (binv_swap _ _ _ _ _ _ _ _ _ BI9). intros z [Hz|[Hz|Hz]]; [right; left | left | right; right]; exact Hz. }
    destruct PERM9 as (BI9' & SUB9).
    pose proof (tob_sub _ _ _ _ _ _ TR9 SUB9) as TR9'. pose proof (tob_sub _ _ _ _ _ _ TQ9 SUB9) as TQ9'. pose proof (trk_sub _ _ _ _ _ _ _ _ _ _ _ _ TRK9 SUB9) as TRK9'.
    set (cells9 := (E - 240, L5.bo_data ro br9) :: (E - 136, L5.bo_data qo bq9) :: cells8).
    assert (TRK9c : trk ((LBy9 ++ LBq9) ++ BX4) M9 bn4 bd4 bn0 bd0 (firstn n1 rn) (firstn l1 rd) None cells9 c).
    { apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ cells8 cells9 _ TRK9'). intros a v [Eq|[Eq|Hin]]. injection Eq as <- <-. right. split. exact S240_9. clear; lia.
      injection Eq as <- <-. right. split. exact S136_9. clear; lia. left. exact Hin. }
    assert (RSC9 : match skind (L5.bo_st bx), skind (L5.bo_st br9) with
                   | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LBy9 = []
                   | None, None => LBy9 = []
                   | None, Some (cap', q') => cap' = 8 /\ LBy9 = [(q', 64)]
                   | Some _, None => False end).
    { subst LBy9 LBy7. destruct gr9 as [|q9 c9]. destruct GRF9 as (_ & SS). rewrite (skind_same _ _ SS). exact RSC7.
      rewrite (GR9S q9 c9 eq_refl) in *. destruct GRF9 as (_ & ST & EC & _). rewrite ST. cbn [bx L5.bo_st skind L5DLA.blocks_of app].
      replace (Z.of_nat (Datatypes.S (Datatypes.S (n1 - 1)))) with (Z.of_nat n1 + 1) in EC by (clear - NNR; lia). rewrite (proj1 RU9) in EC. subst c9. split; reflexivity. }
    assert (QSC9 : match skind (L5.bo_st bq9) with None => LBq9 = [] | Some (cap, q) => LBq9 = [(q, 8 * cap)] end).
    { subst LBq9. destruct gq9 as [|q9 c9]. destruct GQF9 as (_ & SS). rewrite (skind_same _ _ SS), KQ7. reflexivity. destruct GQF9 as (_ & ST & _). rewrite ST. reflexivity. }
    assert (CINV9 : cinv cr2 cr9 L5DIA.DIVO1_K BB 0 0).
    { subst cr9. assert (X1 : cinv cr2 (L5DLA.adebl L cr7 (L5DLA.blocks_of gr9)) L5DIA.DIVO1_K BB (0 + 1) (0 + 64)).
      { destruct gr9 as [|q9 c9]; cbn [L5DLA.blocks_of L5DLA.adebl]. apply (cinv_weak cr2 _ _ _ _ _ _ _ CINV7). destruct (L5.bo_dyn br); clear; lia. destruct (L5.bo_dyn br); clear; lia.
        destruct GRF9 as (_ & _ & -> & DRF & _). rewrite DRF in CINV7. replace (Z.of_nat (Datatypes.S (Datatypes.S (n1 - 1)))) with (Z.of_nat n1 + 1) by (clear - NNR; lia). rewrite (proj1 RU9).
        apply (cinv_debit cr2 _ _ _ _ _ _ _ _ CINV7). clear; lia. clear; lia. clear; lia. }
      destruct gq9 as [|q9 c9]; cbn [L5DLA.blocks_of L5DLA.adebl]. apply (cinv_weak cr2 _ _ _ _ _ _ _ X1). clear; lia. clear; lia.
      destruct GQF9 as (_ & _ & -> & _). replace (Z.of_nat (Datatypes.S (n1 - l1))) with (Z.of_nat (n1 - l1) + 1) by (clear; lia). rewrite (proj2 RU9).
      apply (cinv_debit cr2 _ _ _ _ _ _ _ _ X1). clear; lia. clear; lia. clear; lia. }
    assert (SGR9 : Z.testbit (L5.bo_fb br9) 1 = false).
    { destruct gr9 as [|q9 c9]. rewrite (proj1 GRF9). exact SGR7. rewrite (proj1 GRF9). rewrite Z.lor_spec, SGR7. reflexivity. }
    pose proof TRK9 as (_ & _ & _ & _ & SPL9 & _).
    assert (NCL9 : forall q k a, In (q, k) ((LBy9 ++ LBq9) ++ BX4) -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a).
    { intros q k a Hin Ha. exact (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W7 _ M9 model9 LK9 cr9 A9 q k a BI9' Hin Ha). }
    (* [comment removed for export] *)
    assert (SHAPE9 : sec = true -> gr9 = Same /\ gq9 = Same).
    { intros ST. destruct (BRDYN ST) as (qx & EBR & _). destruct (SECT ST) as (_ & EL3 & _). split.
      destruct gr9 as [|q9 c9]. reflexivity. exfalso. destruct GRF9 as (_ & _ & _ & DRF & _). rewrite DKR, EBR in DRF. discriminate DRF.
      destruct gq9 as [|q9 c9]. reflexivity. exfalso. destruct GQF9 as (_ & _ & _ & _ & N3). clear - N3 EL3 N24. lia. }
    apply (GEN_BACK fx9 R9 M9 model9 W7 BX4 BX4 B3 LBy9 LBq9 LK9 cr9 A9 qo qn bits sdv l (Z.of_nat n1) bx bq9 br9 bn4 bd4 bn0 bd0 _ _ (firstn n1 rn) (firstn l1 rd) None cells9 c Hunn BI9' RI9
             ltac:(rewrite s19; f_equal; clear - NNR; lia) ltac:(rewrite (KR9 27%nat) by inl; exact r27) ltac:(rewrite (KR9 18%nat) by inl; exact X18g) AOR AOQ ltac:(clear - APXQ; lia) TR9' TQ9' TRK9c
             ltac:(rewrite LENR9; clear - NNR; lia) ltac:(rewrite LENQ9; subst l; clear - LLE; lia) ltac:(cbn [bd4 L5.bo_len]; subst l; clear; lia) ltac:(subst l; clear - LLE N24; lia) ltac:(subst l; clear - L13; lia)
             D63' SGR9).
    all: try (unfold cells9, cells8, cells; incell).
    { exact QNR. } { exact BITSR. } { exact SDV. } { exact CR63. }
    { intros c0 v Hin. unfold cells9, cells8, cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; clear; lia|]). destruct Hin. }
    { exact SSH. } { exact USCR. } { exact SCR8. } { exact FFR5. } { exact FFR3. } { exact WQH7. } { exact WRH7. } { exact WY7. } { exact WSH7. } { exact INX. } { exact INN4. } { exact IND4. }
    { exact RSC9. } { exact QSC9. }
    { intros S1. destruct (BRDYN (SEC1 S1)) as (qx & EBR & _). destruct (SHAPE9 (SEC1 S1)) as (EG & _). subst gr9. destruct GRF9 as (_ & SS). exists qx. split.
      apply skind_dyn. rewrite (skind_same _ _ SS), EBR. reflexivity. rewrite LENR9. destruct (SECT (SEC1 S1)) as (_ & _ & N3 & _). clear - N3 N24. lia. }
    { intros _. apply (CINV3 cr9 _ _ CINV9). clear; lia. clear; lia. }
    { reflexivity. } { exact L3. } { exact Lf. }
    2: { apply (KE3g LBy9 LBq9 br9 bq9 cr9 LK9 A9 cells9).
         - intros ST. destruct (BRDYN ST) as (qx & EBR & ELY). destruct (SHAPE9 ST) as (EG & EQ9). exists qx. subst LBy9 LBq9. rewrite EG, EQ9 in *. destruct GRF9 as (_ & SS). split.
           apply skind_dyn. rewrite (skind_same _ _ SS), EBR. reflexivity. split. exact ELY. reflexivity.
         - intros ST. destruct (SHAPE9 ST) as (_ & EQ9). rewrite EQ9 in GQF9. rewrite (skind_same _ _ (proj2 GQF9)). exact KQ7.
         - intros ST. destruct (SHAPE9 ST) as (EG & EQ9). subst cr9. rewrite EG, EQ9. cbn [L5DLA.blocks_of L5DLA.adebl]. exact (CRX7 ST).
         - intros c0 v Hin. unfold cells9, cells8. do 4 right. exact Hin.
         - unfold cells9, cells8. do 2 right. left. reflexivity.
         - intros z Hz. apply IA9, IA7'. exact Hz.
         - intros z Hz. apply ILK7', ILK9. exact Hz. }
    intros fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf IAf ILKf AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf.
    refine (FIN LBy9 LBq9 bq9 br9 cr9 _ _ RSC9 QSC9 _ CINV9 _ _ fxf Rf Mf modelf Af crf LKf bqf wqf brf wrf fb' RPf _ _ AHf OBQf OLQf KQf OBRf OLRf KRf FBRf SGf CRAf RTf AMf HHf).
    + intros q k a Hin Ha. apply (NCL9 q k a). apply in_or_app. left. apply in_or_app. left. exact Hin. exact Ha.
    + clear; lia.
    + clear; lia.
    + intros z Hz. apply IAf, IA9, IA7'. exact Hz.
    + intros z Hz. apply ILK7', ILK9, ILKf. exact Hz.
Qed.
End DIV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem gen_O1_ok : L5ACPAS.copya_stk_spec L ar HI -> L5DLA.norm_specA L ar HI -> resize_spec L ar HI -> assign_spec L ar HI -> opdel_sized_spec L ar HI -> L5DIA.unnorm_specA L ar HI ->
  L5ADVO1.gen_O1 L ar HI.
Proof.
  intros Hcps Hnorm Hrsz Hasg Hdel Hunn. unfold L5ADVO1.gen_O1.
  intros R M model K LB FF LK cr A xo bo qo E r fbx bb wb F fl LK2 M2 model2 fx1 g1 g2 R1 M1 model1 cr1 LK1 A1 c qn bits bn bd HH AM HK G1 RA G2 A32 G4 STK SSH FFR5 FFR3 FFRS XOK AOX SZX BOK AOB SZB ZQ AOQ SZQ APXB APXQ APBQ DYB NB12 CRF G ER UR1
         ATG EG1 EG2 ECR1 IA1 ILK1 CR CV LNE LDE STN STD EBITS KF KE3.
  subst g1 g2 cr1.
  assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- G2; reflexivity).
  assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- G4; reflexivity).
  assert (HSCR' : 384 + 4784 <= L5DIA.DIVO_SCR) by exact L5ADVHO.divO_scr.
  exact (go1_all R M model K LB FF LK A E L5DIA.DIVO_SCR F fl xo r LK2 M2 model2 cr G ER A32 HK G4' HSCR' SSH L5ADVHO.divO_scr8 (ffrk_le 1 FF LK 5 4 FFR5 ltac:(clear; lia)) FFRS Hdel Hasg Hcps Hnorm Hrsz RA UR1 G2'
           bo qo fbx bb wb fx1 R1 M1 model1 LK1 A1 c qn bits bn bd Hunn
           (L5ADVGO1E.o1_e3_ok L ar C HI LY HIok R M model K LB FF LK A E L5DIA.DIVO_SCR F fl xo LK2 M2 model2 cr G ER HSCR' cr qo)
           HH eq_refl SSH FFR5 FFR3 XOK AOX SZX BOK AOB SZB ZQ AOQ SZQ APXB APXQ APBQ DYB NB12 CRF ATG IA1 ILK1 CR CV LNE LDE STN STD EBITS KF KE3).
Qed.
End WithIface.
End SCFG_1.
End L5ADVGO1B.

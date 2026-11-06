(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BDivGU L5BRed L5BDivHH L5BDivHS L5BDivGE L5BDivN L5BDivO1 L5BDivGN L5BDivGK L5BRzHuge L5BDivGK2 L5BDivGK3 L5BDivO2 L5BDivGO2 L5BDivGO2b L5BDivGO2c BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsAB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGNB.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGO2. Import L5ADVGO2B. Import L5ADVGO2C. Import L5ADVGK.
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
(* [comment removed for export] *)
Local Notation G11T := (L5ADVGO2C.g11_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation G12T := (L5ADVGO2C.g12_trk L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation G14F := (L5ADVGO2C.g14_fin L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK G4 HSCR Hdel RA UR1 G2).
Local Notation DIST5 := (L5ADVGO2C.dist5 L ar C HI HIok R M model LB FF LK A E SCRD F ro).
Local Notation SH_OFF_OBJ := (L5ADVGO2C.sh_off_obj L ar C HI LY HIok R M model LB FF LK A E SCRD F ro).
Local Notation SH_OFF_BLK := (L5ADVGO2C.sh_off_blk L ar C HI LY HIok R M model LB FF LK A E SCRD F ro).
Local Notation SKIND_SAME := (L5ADVGO2C.skind_same).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dsaves_agree (R0 : bvmap 5 word) (Ma Mb : word -> option byte) E0 : L5DIA.dsaves R0 Ma E0 -> 104 <= E0 -> E0 <= 2 ^ 64 ->
  (forall a, E0 - 104 <= a < E0 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5DIA.dsaves R0 Mb E0.
Proof.
  intros D H0 H1 AG. unfold L5DIA.dsaves in *. decompose [and] D.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros i Hi; apply AG; clear - Hi H0; lia | clear - H0; lia | clear - H1; lia]).
Qed.

Lemma gn_e3 (cre : credit) (X qX dv : Z) (bX : L5.bigobj) (wX : list Z) (fx4 : FPState) R4 M4 model4 q0 q2 bn0 bd0 fbd' fbn' d1 cr4 LK4 A4 :
  let BX4 := [(q0, 8 * 8); (q2, 8 * 8)] in
  SCRD = L5DIA.DIVN_SCR ->
  ri_inv HI LB FF LK cre A M (vml_of model) -> tob LB M X bX wX -> aobj FF X 32 -> L5.bo_st bX = L5.BDyn 8 qX -> 0 <= ro < 2 ^ 64 ->
  binv [] BX4 M4 model4 LK4 cr4 A4 -> rinvD R E R4 ->
  getr R4 (reg 18) = Z_to_bv 64 SH -> getr R4 (reg 21) = Z_to_bv 64 X -> getr R4 (reg 22) = Z_to_bv 64 F -> getr R4 (reg 26) = Z_to_bv 64 (X + 8) -> getr R4 (reg 27) = Z_to_bv 64 F ->
  getr R4 (reg 19) = Z_to_bv 64 (F + 32) -> getr R4 (reg 25) = Z_to_bv 64 (F + 96) ->
  getr R4 (reg 1) = Z_to_bv 64 0x9313c -> getr R4 (reg 10) = Z_to_bv 64 X -> getr R4 (reg 11) = Z_to_bv 64 (0 - 1) ->
  getr R4 (reg 20) = Z_to_bv 64 0 -> getr R4 (reg 24) = Z_to_bv 64 0 ->
  tob (BX4 ++ LB) M4 (F + 32) (L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1)) [L5DSA.MWORD] ->
  tob (BX4 ++ LB) M4 (F + 96) (L5.BO fbn' 0 (L5.BDyn 8 q2)) [] ->
  L5ADVD.obj_at M4 (SPA + 200) bn0 (Some (q0, 8 * 8)) -> L5ADVD.obj_at M4 (SPA + 168) bd0 None ->
  L5.bo_len bn0 = L5.bo_len bX -> L5.bo_st bn0 = L5.BDyn 8 q0 -> L5.bo_len bd0 = 1%nat -> L5.bo_st bd0 = L5.BInl L5DSA.MWORD 0 ->
  Z.testbit fbd' 1 = false -> Z.testbit fbn' 1 = false -> dsh M4 F 0 248 248 248 248 ->
  L5.u64_at RSEGS M4 (E - 304) (F + 32) -> L5.u64_at RSEGS M4 (E - 296) X -> L5.u64_at RSEGS M4 (E - 264) X -> L5.u64_at RSEGS M4 (E - 280) (F + 96) -> L5.u64_at RSEGS M4 (E - 336) F ->
  L5.u64_at RSEGS M4 (E - 288) ro -> L5.u64_at RSEGS M4 (E - 360) F -> L5.u64_at RSEGS M4 (E - 120) (F + 48) -> L5.u64_at RSEGS M4 (E - 112) 1 -> L5.u64_at RSEGS M4 (E - 272) 1 -> L5.u64_at RSEGS M4 F 1102416563 ->
  L5.u32_at RSEGS M4 (E - 220) 0 ->
  cr4 = adebit L (adebit L cre 64) 64 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
          (F3 fl3 F1c fl1c F1d fl1d : Z),
      L5DIA.divN_e3A L ar LB FF cre M M' R R' X qX (L5.bo_len bX) ro dv E F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' (L5DIA.ff_n FF E F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 RESIZE M4 model4) K.
Proof.
  intros BX4 ESCR HH0 TX0 AOX STX ROR BI4 RI4 X18 X21 X22 X26 X27 X19 X25 p1 p10 p11 p20 p24 TD4 TN4 ON4 OD4 LNN0 STN0 LND0 STD0 SGD SGN DSH4
         S264 S248 S208 S272 S296 S288 S360 S224 S216 S112 HDR4 PX4 ECR KE3.
  assert (TX4 : tob (BX4 ++ LB) M4 X bX wX). { eapply L5ADVHA.arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOX | exact TX0 | ]. intros a _ rr []. }
  assert (DYX : L5.bo_dyn bX = true). { destruct TX0 as ((_ & _ & _ & OST) & _). rewrite STX in OST. exact (proj1 OST). }
  pose proof BI4 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  edestruct L5ADVEA.callee_pre with (SCRc := RESIZE_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI4 | vm_compute; discriminate | clear - HSCR; change RESIZE_SCR with 4496; lia | ].
  pose proof RI4 as (Z2 & Z8 & Z9 & Z3 & Z4 & ZSB).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct (L5ADVHO.frame_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX4 M4 model4 LK4 cr4 A4 BI4 HDR4) as (DSV4 & S192 & _ & AHP4).
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX).
  edestruct L5ADVEA.obj_rng with (o := X) as ((XR1 & XR2 & _) & _); try first [exact LY | exact HIok | exact BI4 | exact AOX'].
  apply (L5ARZH.resize_huge_ok L ar C HI LY HIok fx4 R4 M4 model4 K (BX4 ++ LB) FF' LK4 cr4 A4 X SPA 0x9313c (2 ^ 64 - 1) bX B1 B2 HK).
  - rewrite r10. exact p10.
  - rewrite r11. rewrite p11. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity.
  - unfold L5DIA.MAX_SIZE. clear; lia.
  - rewrite r1. exact p1.
  - split; [clear; lia | reflexivity].
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - exact ROOMc.
  - exact RSc.
  - exact (proj1 TX4).
  - exact DYX.
  - exact AOX'.
  - exact (proj1 (proj2 (proj2 TX4))).
  - intros fx' R' M' model' LK' A' F1c fl1c F1d fl1d E3A RT3 IA3 AM3 ILK3 HH3.
    assert (AHP3 : ahpres L ar (BX4 ++ LB) FF' SPA RESIZE_SCR [] M4 M'). { clear - E3A. unfold L5DIA.resize_huge_atA in E3A. decompose [and] E3A. assumption. }
    pose proof (L5ADVEA.offx_of_ahpres L ar FF E F (BX4 ++ LB) RESIZE_SCR [] M4 M' AHP3) as OFF3.
    assert (NW : forall a, ~ L5ADVEA.inW [] a) by (intros a (rr & [] & _)).
    pose proof G as G0. destruct G0 as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in Hk, FS2, FCEIL, FLC, FR, F8, FBIG', FLA', NCF.
    assert (KST : forall a, SPA <= a < E -> M' (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
    { intros a Ha. apply OFF3. clear - Ha ER; lia. apply stack_client. clear - Ha SLO SPC SPT HSCR; lia. change RESIZE_SCR with 4496. clear - Ha; lia. apply NW. }
    assert (KF0 : forall a, F <= a < F + 504 -> ~ (F + 24 <= a < F + 32) -> M' (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
    { intros a Ha Hn. apply OFF3. clear - Ha FRP; lia. apply (fframe_client L ar _ FF' SPA RESIZE_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. split. clear - Ha; lia. exact Hn. apply NW. }
    assert (SPL3 : forall a v, L5.u64_at RSEGS M4 a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M' a v).
    { intros a v Hc H1 H2. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia. intros i Hi. apply KST. cbn in Hi. clear - Hi H1 H2; lia. }
    assert (STK3 : forall o b, L5.big_at RSEGS M4 o b -> SPA <= o -> o + 32 <= E -> L5.big_at RSEGS M' o b).
    { intros o b OB H1 H2. eapply L5C.big_at_agree. 4: exact OB. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia. intros i Hi. apply KST. cbn in Hi. clear - Hi H1 H2; lia. }
    assert (LOC3 : forall k b, L5.big_at RSEGS M4 (F + k) b -> 32 <= k -> k + 32 <= 504 -> L5.big_at RSEGS M' (F + k) b).
    { intros k b OB H1 H2. eapply L5C.big_at_agree. 4: exact OB. 2: clear - H1 FRP; lia. 2: clear - H2 FRP; lia. intros i Hi. apply KF0. cbn in Hi. clear - Hi H1 H2; lia. cbn in Hi. clear - Hi H1; lia. }
    apply (KE3 fx' R' M' model' (BX4 ++ LB) cr4 LK' A' F fl F1c fl1c F1d fl1d).
    2:{ eapply L5LZ.model_rt_trans. exact B3. exact RT3. }
    2:{ intros x Hx. apply IA3. apply B4. exact Hx. }
    2: exact AM3.
    2:{ intros x Hx. apply B5. apply ILK3. exact Hx. }
    2:{ unfold L5DIA.ff_n. replace (E - 352) with (SPA + 32) by (clear; lia). exact HH3. }
    exists R4, M4, q0, q2, (L5.bo_fb bd0), (L5.bo_fb bn0), fbn', fbd', d1.
    assert (UL : forall k v, getr R4 (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> L5DSA.U R4 (Z.of_nat k) = v).
    { intros k0 v Hk0 Hv. exact (U_of R4 k0 v Hk0 Hv). }
    split. { apply (UL 1%nat _ p1). clear; lia. }
    split. { apply (UL 8%nat _ Z8). exact ERG. }
    split. { apply (UL 9%nat _ Z9). clear - ER; lia. }
    split. { unfold S. apply (UL 18%nat _ X18). unfold SB. clear - FRP. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { apply (UL 19%nat _ X19). clear - FRP; lia. }
    split. { exact p20. }
    split. { apply (UL 21%nat _ X21). clear - XR1 XR2; lia. }
    split. { apply (UL 22%nat _ X22). clear - FRP; lia. }
    split. { apply (UL 23%nat _ ZSB). unfold SB. clear; lia. }
    split. { exact p24. }
    split. { apply (UL 25%nat _ X25). clear - FRP; lia. }
    split. { apply (UL 26%nat _ X26). clear - XR1 XR2; lia. }
    split. { apply (UL 27%nat _ X27). clear - FRP; lia. }
    split. { exact Z3. }
    split. { exact Z4. }
    split. { replace (E - 352) with (SPA + 32) by (clear; lia). exact E3A. }
    split. { apply (dsaves_agree R M4 M' E DSV4). clear - ER; lia. clear - ER; lia. intros a Ha. apply KST. clear - Ha; lia. }
    split. { apply (SPL3 _ _ S360); clear; lia. }
    split. { apply (SPL3 _ _ S296); clear; lia. }
    split. { apply (SPL3 _ _ S272); clear; lia. }
    split. { apply (SPL3 _ _ S264); clear; lia. }
    split. { apply (SPL3 _ _ S288); clear; lia. }
    split. { apply (SPL3 _ _ S248); clear; lia. }
    split. { apply (SPL3 _ _ S224); clear; lia. }
    split. { apply (SPL3 _ _ S216); clear; lia. }
    split. { apply (SPL3 _ _ S112); clear; lia. }
    split. { apply (SPL3 _ _ S208); clear; lia. }
    split. { apply (SPL3 _ _ S192); clear; lia. }
    split. { eapply L5ARED.u32_at_agree1. 4: exact PX4. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply KST. clear - Hi; lia. }
    split. { replace (E - 216) with (SPA + 168) by (clear; lia). destruct OD4 as (OBD0 & _). destruct bd0 as [fd0 ld0 sd0]. cbn [L5.bo_len L5.bo_st L5.bo_fb] in *. subst ld0 sd0. apply (STK3 _ _ OBD0); clear; lia. }
    split. { replace (E - 184) with (SPA + 200) by (clear; lia). destruct ON4 as (OBN0 & _). destruct bn0 as [fn0 ln0 sn0]. cbn [L5.bo_len L5.bo_st L5.bo_fb] in *. subst ln0 sn0. apply (STK3 _ _ OBN0); clear; lia. }
    split. { apply (LOC3 96 _ (proj1 TN4)); clear; lia. }
    split. { exact SGN. }
    split. { apply (LOC3 32 _ (proj1 TD4)); clear; lia. }
    split. { exact SGD. }
    assert (SHQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416).
    { hnf in ALF. clear - FRP ALF. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { apply (L5ADVHO.sh_div_of_dsh M' F 0 248 248 248 248 (proj1 SHQ) (proj2 SHQ)).
             eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH4 | exact OFF3 | ].
             intros j _. apply NW. }
    split. { apply L5DSA.FRL.
             - refine (proj1 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model' F 3 _ _ fl HH2 HH3 (or_introl eq_refl) _ Hk FLC)).
               unfold L5DIA.ff_rz. right; right; left; reflexivity.
             - exact FLP.
             - replace (E - 352) with (SPA + 32) by (clear; lia).
               apply (not_client_bx L ar ((F, 3, SPA + 32) :: FF) fl BX4 LB).
               apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX4 LB HH3 eq_refl). exact FLP. exact FLBIG. exact FLNC.
             - exact FLA.
             - eapply L5C.u64_at_agree. 4: exact HDR4. 2: clear - FRP; lia. 2: clear - FRP; lia. intros j Hj. apply KF0. cbn in Hj. clear - Hj; lia. cbn in Hj. clear - Hj; lia. }
    split. { reflexivity. }
    split. { exact ECR. }
    rewrite <- ESCR. apply ahpres_of.
    + eapply ek_trans. exact B7. apply (ek_callee L ar LB BX4 FF [(F, 3, SPA + 32)] E SCRD SPA RESIZE_SCR [] [] M4 M' AHP3).
      change RESIZE_SCR with 4496; clear - HSCR; lia. clear; lia. intros a _ Ho. exact Ho.
    + assert (STK3' : astk ar M' E SCRD).
      { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ (BX4 ++ LB) FF' M4 M4 M' E SCRD SPA RESIZE_SCR [] B1 B6 (mem_grows_refl M4) AHP3).
        change RESIZE_SCR with 4496; clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
      eapply astk_defined. exact STK3'. clear; lia. clear; lia.
    + eapply dk_trans. exact B8. apply (dk_callee L ar LB BX4 FF [(F, 3, SPA + 32)] E SCRD SPA RESIZE_SCR [] M4 M' AHP3).
      change RESIZE_SCR with 4496; clear - HSCR; lia. clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gn_mid1 (cr0 : credit) (X qX : Z) (bX : L5.bigobj) (wX : list Z) (fx4 : FPState) R4 M4 model4 BX4 LK4 cr4 A4 bn bd bn0 bd0 wn wd on0 cells x (nn : nat) :
  ri_inv HI LB FF LK cr0 A M (vml_of model) ->
  tob LB M X bX wX -> aobj FF X 32 -> L5.bo_st bX = L5.BDyn 8 qX ->
  tob LB M ro (L5.BO 0 0 (L5.BInl 0 0)) [] -> aobj FF ro 32 -> (X + 32 <= ro \/ ro + 32 <= X) ->
  binv [] BX4 M4 model4 LK4 cr4 A4 -> rinvD R E R4 ->
  getr R4 (reg 1) = Z_to_bv 64 0x9313c -> getr R4 (reg 10) = Z_to_bv 64 X -> getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat nn - 1) ->
  getr R4 (reg 25) = Z_to_bv 64 (F + 96) -> getr R4 (reg 26) = Z_to_bv 64 (X + 8) ->
  trk BX4 M4 bn bd bn0 bd0 wn wd on0 cells x ->
  In (E - 296, X) cells -> In (E - 320, X / 8 + 2147450880) cells -> In (E - 352, (X + 8) / 8 + 2147450880) cells -> In (E - 288, ro) cells ->
  (forall c v, In (c, v) cells -> c + 8 <= E - 136 \/ E - 120 <= c) ->
  L5.bo_len bn = nn -> (1 <= nn <= 6)%nat -> (nn <= L5.bo_len bX)%nat ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bX = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bX = L5.BDyn c' q' -> q <> q') ->
  L5OMA.acredit_for L cr4 1 64 ->
  (forall (fx7 : FPState) R7 M7 model7 (gr : growth) bq br cr7 LK7 A7 wq,
      let BX7 := match gr with Same => BX4 | Grown q cap => (q, 8 * cap) :: BX4 end in
      binv [(X, 32); (qX, 64); (ro, 32)] BX7 M7 model7 LK7 cr7 A7 -> rinvD R E R7 ->
      (forall k, In k [18; 20; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R4 (reg k)) -> getr R7 (reg 22) = Z_to_bv 64 ro ->
      L5.u64_at RSEGS M7 (E - 136) qX -> L5.u64_at RSEGS M7 (E - 128) (Z.of_nat nn - 1) ->
      tob (BX7 ++ LB) M7 X bq wq -> L5.bo_len bq = (nn - 1)%nat -> L5.bo_fb bq = L5.bo_fb bX -> L5.bo_st bq = L5.BDyn 8 qX ->
      tob (BX7 ++ LB) M7 ro br wn -> L5.bo_len br = nn ->
      (match gr with
       | Same => L5.bo_fb br = assign_fb 0 (L5.bo_fb bn) nn false /\ L5ADVEA.same_store (L5.BO 0 0 (L5.BInl 0 0)) (L5.bo_st br) /\ cr7 = cr4
       | Grown q cap => L5.bo_fb br = assign_fb 0 (L5.bo_fb bn) nn true /\ L5.bo_st br = L5.BDyn cap q /\ cap = 8 /\ cr7 = adebit L cr4 64 end) ->
      trk BX7 M7 bn bd bn0 bd0 wn wd on0 cells x -> incl A4 A7 -> incl LK7 LK4 ->
      srealizes RSEGS SCFG (cfg (fx:=fx7) R7 0x931d4 M7 model7) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 RESIZE M4 model4) K.
Proof.
  intros HH0 TX0 AOX STX TR0 AOR APXR BI4 RI4 p1 p10 p11 p25 p26 TRK4 IN296 IN320 IN352 IN288 CELLQ LNN NNR NLE NQNX NQDX CRD KF.
  set (n := (nn - 1)%nat). set (zo := L5.BO 0 0 (L5.BInl 0 0)) in *.
  assert (TX4 : tob (BX4 ++ LB) M4 X bX wX). { eapply L5ADVHA.arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOX | exact TX0 | ]. intros a _ rr []. }
  assert (TR4 : tob (BX4 ++ LB) M4 ro zo []). { eapply L5ADVHA.arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOR | exact TR0 | ]. intros a _ rr []. }
  assert (DYX : L5.bo_dyn bX = true). { destruct TX0 as ((_ & _ & _ & OST) & _). rewrite STX in OST. exact (proj1 OST). }
  assert (CAPX : L5.bo_cap bX = 8) by (unfold L5.bo_cap; rewrite STX; reflexivity).
  assert (DATX : L5.bo_data X bX = qX) by (unfold L5.bo_data; rewrite STX; reflexivity).
  assert (P11 : getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat n)). { rewrite p11. f_equal. subst n. clear - NNR. lia. }
  assert (RUN : round_up (Z.of_nat nn) = 8). { unfold round_up. clear - NNR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  set (W1 := [(X, 32); (qX, 64)]).
  apply (ARSZ2 fx4 R4 M4 model4 [] W1 BX4 LK4 cr4 A4 X 0x9313c n bX wX BI4 RI4 p10 P11 p1 ltac:(split; [clear; lia | reflexivity]) AOX TX4).
  { subst n. clear - NNR. lia. }
  { intros _. rewrite CAPX. subst n. clear - NNR. lia. }
  { intros _ X0. rewrite DYX in X0. discriminate X0. }
  { intros a OUT. split. intros rr []. intros rr [<-|[]]. apply OUT. left; reflexivity. }
  { intros _ a _ _ IR. unfold L5.in_rng in IR. cbn [fst snd] in IR. subst n. clear - IR NLE NNR. lia. }
  intros fx5 R5 M5 model5 gq bq1 cr5 LK5 A5 RP5 BI5 TQ5 LENQ GQF OFF5 IA5 ILK5.
  destruct gq as [|qg capg]. 2:{ exfalso. destruct GQF as (_ & _ & _ & _ & X0 & _). rewrite DYX in X0. discriminate X0. }
  destruct GQF as (FBQ1 & SSQ1 & ECR5). subst cr5.
  assert (STQ1 : L5.bo_st bq1 = L5.BDyn 8 qX). { unfold L5ADVEA.same_store in SSQ1. rewrite STX in SSQ1. destruct (L5.bo_st bq1) as [? ?|c1 q1]. destruct SSQ1. destruct SSQ1 as (-> & ->). reflexivity. }
  assert (TRK5 : trk BX4 M5 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP_ARG [] BX4 BX4 M4 M5 model4 LK4 cr4 A4 RESIZE_SCR X bX wX bn bd bn0 bd0 wn wd on0 cells x BI4 AOX TX4 OFF5 ltac:(intros b0 Hb; exact Hb) TRK4 NQNX NQDX). }
  assert (NQRX4 : forall a, L5ADVEA.oreg ro zo a -> L5ADVEA.oreg X bX a -> False).
  { intros a O1 O2. apply (OREG_DISJ [] BX4 M4 model4 LK4 cr4 A4 ro zo [] X bX wX a BI4 AOR' TR4 AOX' TX4 ltac:(clear - APXR; lia)). intros c q c' q' Eq _. discriminate Eq. exact O1. exact O2. }
  assert (TR5 : tob (BX4 ++ LB) M5 ro zo []).
  { pose proof BI4 as (B4 & _).
    apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX4 ++ LB) (BX4 ++ LB) (BX4 ++ LB) LK4 cr4 A4 model4 RESIZE_SCR _ M4 M5 ro zo [] B4 AOR' TR4 OFF5).
    intros cap q Eq. discriminate Eq. intros a O1 O2. exact (NQRX4 a O1 O2). }
  assert (RI5 : rinvD R E R5) by (apply (rinvD_pres R E R4 R5 RI4 RP5)).
  assert (X26 : getr R5 (reg 26) = Z_to_bv 64 (X + 8)) by (rewrite (cs_of_preserved R4 R5 26 RP5) by inl; exact p26).
  assert (DATQ1 : L5.bo_data X bq1 = qX) by (unfold L5.bo_data; rewrite STQ1; reflexivity).
  (* [comment removed for export] *)
  apply (G5A fx5 R5 M5 model5 W1 W1 BX4 LK5 cr4 A5 X bq1 (resize_limbs wX n) BI5 RI5 X26 (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK5 IN320) (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK5 IN352) (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK5 IN296) AOX TQ5).
  { rewrite LENQ. subst n. clear - NNR. lia. }
  { intros a Hs rr [<-|[<-|[]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    - exact (L5ADVGO2.sh_off_obj L ar C HI LY HIok R M model LB FF LK A E SCRD F ro W1 BX4 M5 model5 LK5 cr4 A5 X a BI5 AOX' Hs IR).
    - exact (L5ADVGO2.sh_off_blk L ar C HI LY HIok R M model LB FF LK A E SCRD F ro W1 BX4 M5 model5 LK5 cr4 A5 X qX (8 * 8) a BI5 AOX' (proj2 (proj2 (proj2 TQ5)) 8 qX STQ1) Hs IR). }
  { intros a OUT. split. exact OUT. intros rr [<-|[]] IR. unfold L5.in_rng in IR. cbn [fst snd] in IR. rewrite DATQ1, LENQ in IR.
    apply (OUT (qX, 64)). right; left; reflexivity. unfold L5.in_rng. cbn [fst snd]. subst n. clear - IR NNR. lia. }
  intros fx6 R6 M6 model6 bq wq BI6 RI6 KS6 TQ6 FB6 LN6 SS6 DT6 OFF6 S136_6 S128_6.
  assert (STQ : L5.bo_st bq = L5.BDyn 8 qX). { unfold L5ADVEA.same_store in SS6. rewrite STQ1 in SS6. destruct (L5.bo_st bq) as [? ?|c1 q1]. destruct SS6. destruct SS6 as (-> & ->). reflexivity. }
  assert (DSUB : forall a, L5.bo_data X bq1 <= a < L5.bo_data X bq1 + 8 * Z.of_nat (L5.bo_len bq1) -> L5ADVEA.oreg X bq1 a).
  { intros a Ha. right; right. exists 8, qX. split. exact STQ1. rewrite DATQ1, LENQ in Ha. subst n. clear - Ha NNR. lia. }
  assert (NQN1 : forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq1 = L5.BDyn c' q' -> q <> q'). { intros c q c' q' E1 E2. rewrite STQ1 in E2. rewrite <- STX in E2. exact (NQNX c q c' q' E1 E2). }
  assert (NQD1 : forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq1 = L5.BDyn c' q' -> q <> q'). { intros c q c' q' E1 E2. rewrite STQ1 in E2. rewrite <- STX in E2. exact (NQDX c q c' q' E1 E2). }
  set (XS6 := fun a => E - 136 <= a < E - 120 \/ E - 392 <= a < E - 384).
  assert (OFF6' : offx (BX4 ++ LB) 0 (fun a => XS6 a \/ L5ADVEA.oreg X bq1 a) M5 M6).
  { apply (OFFX_WEAKEN _ _ _ _ _ _ OFF6). intros a [Y|[Y|Y]]. left; left; exact Y. left; right; exact Y. right. exact (DSUB a Y). }
  assert (TRK6 : trk BX4 M6 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (L5ADVGO2.trk_keep_argX L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR W1 BX4 BX4 M5 M6 model5 LK5 cr4 A5 0 XS6 X bq1 _ bn bd bn0 bd0 wn wd on0 cells x BI5 AOX TQ5 OFF6' ltac:(intros b0 Hb; exact Hb) TRK5 NQN1 NQD1).
    - intros i [Y|Y]; split; clear - Y; lia.
    - intros c v Hin i Hi [Y|Y]. destruct (CELLQ c v Hin) as [Z0|Z0]; clear - Hi Y Z0; lia.
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 TRK5)))) c v Hin) as (_ & H1 & _). clear - Hi Y H1; lia. }
  assert (NQRX5 : forall a, L5ADVEA.oreg ro zo a -> L5ADVEA.oreg X bq1 a -> False).
  { intros a O1 O2. apply (OREG_DISJ W1 BX4 M5 model5 LK5 cr4 A5 ro zo [] X bq1 _ a BI5 AOR' TR5 AOX' TQ5 ltac:(clear - APXR; lia)). intros c q c' q' Eq _. discriminate Eq. exact O1. exact O2. }
  assert (TR6 : tob (BX4 ++ LB) M6 ro zo []).
  { pose proof BI5 as (B5 & _).
    apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX4 ++ LB) (BX4 ++ LB) (BX4 ++ LB) LK5 cr4 A5 model5 0 _ M5 M6 ro zo [] B5 AOR' TR5 OFF6').
    intros cap q Eq. discriminate Eq. intros a O1 [Y|O2]. 2: exact (NQRX5 a O1 O2).
    apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W1 BX4 M5 model5 LK5 cr4 A5 ro zo [] a BI5 AOR' TR5 O1). clear - Y HSCR. destruct Y; lia. }
  (* [comment removed for export] *)
  assert (X25 : getr R6 (reg 25) = Z_to_bv 64 (F + 96)) by (rewrite (KS6 25%nat) by inl; rewrite (cs_of_preserved R4 R5 25 RP5) by inl; exact p25).
  pose proof (proj1 TRK6) as TN6. pose proof BI6 as (B6 & _).
  set (W3 := [(X, 32); (qX, 64); (ro, 32)]).
  apply (G6A2 fx6 R6 M6 model6 W1 W3 BX4 LK5 cr4 A5 zo bn [] wn BI6 RI6 X25 (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK6 IN288) AOR TR6 TN6).
  { rewrite LNN. clear - NNR. lia. }
  { intros DY. discriminate DY. }
  { rewrite LNN. intros _ _. rewrite RUN. apply (cred_ok1 L C LY cr4 1 64 _ CRD). clear; lia. clear; lia. }
  { intros c q c' q' Eq. discriminate Eq. }
  { intros a OUT. split. intros rr [<-|[<-|[]]]; apply OUT. left; reflexivity. right; left; reflexivity. intros rr [<-|[]]. apply OUT. right; right; left; reflexivity. }
  { intros DL a _ OUT IR. rewrite LNN in DL, IR. unfold L5.in_rng in IR. cbn [fst snd L5.bo_data L5.bo_st zo] in IR. destruct DL as [X0|LE2]. discriminate X0.
    apply (OUT (ro, 32)). right; right; left; reflexivity. unfold L5.in_rng. cbn [fst snd]. clear - IR LE2. lia. }
  intros fx7 R7a R7 M7 model7 gr br cr7 LK7 A7 KS7 p22 RP7 BI7 TR7 LENR GRF OFF7 IA7 ILK7.
  set (BX7 := match gr with Same => BX4 | Grown q cap => (q, 8 * cap) :: BX4 end) in *.
  assert (SUB7 : forall b0, In b0 (BX4 ++ LB) -> In b0 (BX7 ++ LB)). { intros b0 Hb. subst BX7. destruct gr. exact Hb. right. exact Hb. }
  assert (TRK7 : trk BX7 M7 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP_ARG W1 BX4 BX7 M6 M7 model6 LK5 cr4 A5 ASSIGN_SCR ro zo [] bn bd bn0 bd0 wn wd on0 cells x BI6 AOR TR6 OFF7 SUB7 TRK6).
    intros c q c' q' _ Eq. discriminate Eq. intros c q c' q' _ Eq. discriminate Eq. }
  assert (AOX'' := AOX').
  assert (TQ7 : tob (BX7 ++ LB) M7 X bq wq).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX4 ++ LB) (BX4 ++ LB) (BX7 ++ LB) LK5 cr4 A5 model6 ASSIGN_SCR _ M6 M7 X bq wq B6 AOX' TQ6 OFF7).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TQ6)) cap q Eq) as X0. split. exact X0. apply SUB7. exact X0.
    intros a O1 O2. apply (OREG_DISJ W1 BX4 M6 model6 LK5 cr4 A5 ro zo [] X bq wq a BI6 AOR' TR6 AOX' TQ6 ltac:(clear - APXR; lia)). 2: exact O2. 2: exact O1.
    intros c q c' q' Eq _. discriminate Eq. }
  (* [comment removed for export] *)
  assert (KR7 : forall k, In k [18; 20; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R4 (reg k)).
  { intros k Hk. rewrite (cs_of_preserved R7a R7 k RP7) by (revert Hk; apply (L5K.incl_b [18; 20; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (KS7 k) by (revert Hk; apply (L5K.incl_b [18; 20; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (KS6 k) by (revert Hk; apply (L5K.incl_b [18; 20; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    apply (cs_of_preserved R4 R5 k RP5). revert Hk. apply (L5K.incl_b [18; 20; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
  assert (OFFR7 : forall a, L5ADVEA.oreg ro zo a -> ~ (SPA <= a < E)).
  { intros a OR. edestruct L5ADVEA.arg_off with (o := ro) (a := a) as (_ & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI6 | exact AOR | exact TR6 | exact OR | ]. exact Y3. }
  assert (S136_7 : L5.u64_at RSEGS M7 (E - 136) qX).
  { rewrite <- DATQ1. apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX4 ++ LB) ASSIGN_SCR _ M6 M7 _ _ S136_6 ltac:(clear; lia) ltac:(clear; lia) OFF7).
    intros i Hi OR. apply (OFFR7 i OR). clear - Hi; lia. }
  assert (S128_7 : L5.u64_at RSEGS M7 (E - 128) (Z.of_nat nn - 1)).
  { replace (Z.of_nat nn - 1) with (Z.of_nat (L5.bo_len bq1)) by (rewrite LENQ; subst n; clear - NNR; lia).
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX4 ++ LB) ASSIGN_SCR _ M6 M7 _ _ S128_6 ltac:(clear; lia) ltac:(clear; lia) OFF7).
    intros i Hi OR. apply (OFFR7 i OR). clear - Hi; lia. }
  assert (RI7 : rinvD R E R7). { apply (rinvD_pres R E R7a R7). apply (rinvD_ks R E R6 R7a KS_v5G6 RI6 KS7). vm_compute; reflexivity. exact RP7. }
  apply (KF fx7 R7 M7 model7 gr bq br cr7 LK7 A7 wq BI7 RI7).
  - exact KR7.
  - rewrite (cs_of_preserved R7a R7 22 RP7) by inl. exact p22.
  - exact S136_7.
  - exact S128_7.
  - exact TQ7.
  - rewrite LN6. exact LENQ.
  - rewrite FB6. exact FBQ1.
  - exact STQ.
  - exact TR7.
  - rewrite LENR. exact LNN.
  - rewrite LNN in GRF. destruct gr as [|qr capr]. exact GRF.
    destruct GRF as (G1' & G2' & G3' & G4' & _). split. exact G1'. split. exact G2'. rewrite RUN in G3'. split. exact G3'. rewrite G4', G3'. reflexivity.
  - exact TRK7.
  - intros a0 Ha0. apply IA7. apply IA5. exact Ha0.
  - intros f0 Hf0. apply ILK5. apply ILK7. exact Hf0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gn_back (fx : FPState) Rc Mc modelc W BX BX2 BX3 BXf LKc crc Ac to qo qn (l n : Z) (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 n -> getr Rc (reg 27) = Z_to_bv 64 l -> getr Rc (reg 18) = Z_to_bv 64 SH ->
  aobj FF ro 32 -> aobj FF qo 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc qo bq wq -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n - l -> Z.of_nat (L5.bo_len bd) = l + 1 -> l <= n <= 298 -> 0 <= l <= 298 ->
  2 ^ 63 <= nth_w wd (Z.to_nat l) ->
  In (E - 272, l + 1) cells -> In (E - 264, to) cells -> 0 <= to < 2 ^ 64 -> In (E - 240, L5.bo_data ro br) cells -> In (E - 136, L5.bo_data qo bq) cells -> In (E - 120, L5.bo_data (F + 32) bd) cells ->
  In (E - 360, F) cells -> In (E - 288, ro) cells -> In (E - 320, qo / 8 + 2147450880) cells ->
  In (E - 296, qo) cells -> In (E - 336, F) cells -> In (E - 304, F + 32) cells -> In (E - 280, F + 96) cells ->
  In (E - 312, qn) cells -> 0 <= qn <= 1 -> In (E - 344, 0) cells ->
  (forall c v, In (c, v) cells -> c + 8 <= E - 248 \/ E - 240 <= c) ->
  L5OMA.stksh ar M (E - SCRD) ->
  (forall a, qo <= a < qo + 32 -> ~ L5.outside W a) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * (n + 1) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall a, L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * (n - l) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  match on0 with None => BX2 = BX | Some (q, k) => In (q, k) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BX2 ++ LB end ->
  match blk_of bn with None => BX3 = BX2 | Some (q, k) => In (q, k) (BX2 ++ LB) /\ lb_remove q (BX2 ++ LB) = BX3 ++ LB end ->
  match blk_of bd with None => BXf = BX3 | Some (q, k) => In (q, k) (BX3 ++ LB) /\ lb_remove q (BX3 ++ LB) = BXf ++ LB end ->
  (forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) -> (forall cap q, L5.bo_st br = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) ->
  (forall (fxf : FPState) Rf Mf modelf Af fbq' bqf wqf brf wrf,
      regs_preserved R Rf -> incl Ac Af -> ahpres L ar LB FF E SCRD W M Mf ->
      L5.big_at RSEGS Mf qo bqf -> L5C.obj_limbs RSEGS Mf bqf wqf -> L5.bo_fb bqf = Z.lor (Z.land fbq' 253) (2 * qn) -> L5ADVEA.same_store bq (L5.bo_st bqf) ->
      (Z.of_nat (L5.bo_len bqf) <= n - l) ->
      L5.big_at RSEGS Mf ro brf -> L5C.obj_limbs RSEGS Mf brf wrf -> L5ADVEA.same_store br (L5.bo_st brf) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI (BXf ++ LB) FF LKc crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93350 Mc modelc) K.
Proof.
  intros BI RI X19 X27 X18 AOR AOQ APO TR TQ TRK LENR LENQ LEND NR LR D63 IN272c IN208 TOR IN240 IN136 IN120 IN360 IN288 IN320 IN248 IN296 IN264 IN272 IN312 QNR IN304 CELLS
         SSH WQH WSH COVR COVQ NQB NQNR NQNQ NQDR NQDQ L2 L3 Lf INQf INRf KF.
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  edestruct L5ADVEA.obj_rng with (o := ro) as ((RR1 & RR2 & RR8) & _); try first [exact LY | exact HIok | exact BI | exact AOR'].
  edestruct L5ADVEA.obj_rng with (o := qo) as ((QR1 & QR2 & QR8) & _); try first [exact LY | exact HIok | exact BI | exact AOQ'].
  apply (G9T fx Rc Mc modelc W BX LKc crc Ac to qo br bq bn bd bn0 bd0 wr wq wn wd on0 cells x n l BI RI X19 X27 AOR AOQ TR TQ TRK LENR LENQ LEND ltac:(clear - NR; lia) LR D63 IN272c IN208
           TOR IN240 IN136 IN120 CELLS WSH COVR COVQ APO NQB NQNR NQNQ NQDR NQDQ).
  intros fx1 R1 M1 model1 br1 wr1 bq1 wq1 BI1 RI1 K18 TR1 FBR1 LENR1 SSR1 DATR1 TQ1 FBQ1 LENQ1 SSQ1 DATQ1 TRK1.
  pose proof (SKIND_SAME _ _ SSR1) as KR1. pose proof (SKIND_SAME _ _ SSQ1) as KQ1.
  assert (STR : forall c q, L5.bo_st br1 = L5.BDyn c q -> L5.bo_st br = L5.BDyn c q). { intros c q Eq. apply skind_dyn. rewrite <- KR1. apply skind_dyn. exact Eq. }
  assert (STQ : forall c q, L5.bo_st bq1 = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c q). { intros c q Eq. apply skind_dyn. rewrite <- KQ1. apply skind_dyn. exact Eq. }
  assert (NQB1 : forall c q c' q', L5.bo_st br1 = L5.BDyn c q -> L5.bo_st bq1 = L5.BDyn c' q' -> q <> q'). { intros c q c' q' E1 E2. exact (NQB c q c' q' (STR _ _ E1) (STQ _ _ E2)). }
  assert (NQNQ1 : forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq1 = L5.BDyn c' q' -> q <> q'). { intros c q c' q' E1 E2. exact (NQNQ c q c' q' E1 (STQ _ _ E2)). }
  assert (NQDQ1 : forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq1 = L5.BDyn c' q' -> q <> q'). { intros c q c' q' E1 E2. exact (NQDQ c q c' q' E1 (STQ _ _ E2)). }
  (* [comment removed for export] *)
  apply (G11T fx1 R1 M1 model1 W BX LKc crc Ac qo bq1 br1 bn bd bn0 bd0 wq1 wr1 wn wd on0 cells x BI1 RI1 AOQ AOR APO TQ1 TR1 TRK1
           ltac:(intros a Ha; apply WQH; clear - Ha; lia) ltac:(rewrite K18; exact X18) WSH IN248 IN360 IN296 IN264 IN272 NQB1 NQNQ1 NQDQ1).
  intros fx2 R2 M2' model2' fb2 BI2 RI2 p18 p24 p25 p20 p22 p27 EFB TQ2 TR2 TRK2.
  set (bq2 := L5.BO fb2 (L5W.rlen wq1) (L5.bo_st bq1)) in *.
  pose proof TRK2 as (_ & _ & _ & _ & SPL2 & _).
  (* [comment removed for export] *)
  apply (G12T fx2 R2 M2' model2' W BX LKc crc Ac to qo qn 0 0 bq2 br1 bn bd bn0 bd0 _ wr1 wn wd on0 cells x BI2 RI2 p20 AOQ AOR APO TQ2 TR2 TRK2
           ltac:(apply WQH; clear; lia) IN288 IN320
           IN208 TOR IN312 QNR IN304 ltac:(left; reflexivity) ltac:(intros X0; exfalso; clear - X0; lia) NQB1 NQNQ1 NQDQ1).
  intros fx3 R3 M3 model3 BI3 RI3 KS3 q19 TQ3 TR3 TRK3 _. change (0 =? 1) with false. cbn iota.
  set (bq3 := L5.BO (Z.lor (Z.land (L5.bo_fb bq2) 253) (2 * qn)) (L5.bo_len bq2) (L5.bo_st bq2)) in *.
  assert (RT3 : L5ADVD.rinvTL R E F R3).
  { split. exact RI3. rewrite !KS3 by inl. split. exact p18. split. exact p24. split. exact p25. split. exact p22. exact p27. }
  (* [comment removed for export] *)
  apply (G14F fx3 R3 M3 model3 W BX BX2 BX3 BXf LKc crc Ac qo bq3 br1 bn bd bn0 bd0 _ wr1 wn wd on0 cells x BI3 RT3 AOQ AOR TQ3 TR3 TRK3 L2 L3 Lf).
  { intros cap q Eq. exact (INQf cap q (STQ _ _ Eq)). }
  { intros cap q Eq. exact (INRf cap q (STR _ _ Eq)). }
  intros fxf Rf Mf modelf Af RPf IAf AHf OBQf OLQf OBRf OLRf RTf AMf HHf.
  apply (KF fxf Rf Mf modelf Af (L5.bo_fb bq2) bq3 _ br1 wr1 RPf IAf AHf OBQf OLQf).
  - reflexivity.
  - cbn [bq3 bq2 L5.bo_st]. exact SSQ1.
  - cbn [bq3 bq2 L5.bo_len]. pose proof (rlen_le wq1) as RLE. pose proof (proj1 (proj1 (proj2 TQ1))) as LWQ. rewrite LWQ, LENQ1 in RLE. clear - RLE LENQ. lia.
  - exact OBRf.
  - exact OLRf.
  - exact SSR1.
  - exact RTf.
  - exact AMf.
  - exact HHf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gn_dist W LBr q0 q2 qX Mc modelc LKc crc Ac (bq br : L5.bigobj) fbn' (nn : nat) fbd' d1 :
  let BX := LBr ++ [(q0, 8 * 8); (q2, 8 * 8)] in
  let bn := L5.BO fbn' nn (L5.BDyn 8 q2) in let bd := L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1) in
  binv W BX Mc modelc LKc crc Ac -> In (qX, 64) LB -> L5.bo_st bq = L5.BDyn 8 qX ->
  match skind (L5.bo_st br) with None => LBr = [] | Some (cap, q) => cap = 8 /\ LBr = [(q, 64)] end ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') /\
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') /\
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') /\
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') /\
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q').
Proof.
  intros BX bn bd BI INX STQ RSK. pose proof BI as (B1 & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (ND : NoDup (map fst (BX ++ LB))). { clear - WF0. decompose [and] WF0. assumption. }
  set (BX4 := [(q0, 8 * 8); (q2, 8 * 8)]) in *.
  assert (INBX_r : forall b, In b LBr -> In b BX) by (intros b Hb; subst BX; apply in_or_app; left; exact Hb).
  assert (INBX_4 : forall b, In b BX4 -> In b BX) by (intros b Hb; subst BX; apply in_or_app; right; exact Hb).
  assert (RB : forall cap q, L5.bo_st br = L5.BDyn cap q -> cap = 8 /\ LBr = [(q, 64)]). { intros cap q Eq. rewrite Eq in RSK. cbn [skind] in RSK. exact RSK. }
  split.
  { intros c q c' q' E1 E2. rewrite STQ in E2. injection E2 as <- <-. destruct (RB _ _ E1) as (-> & ELB).
    exact (L5ADVHO.nodup_app_fst BX LB (q, 64) (qX, 64) ND (INBX_r _ ltac:(rewrite ELB; left; reflexivity)) INX). }
  split.
  { intros c q c' q' E1 E2. cbn [bn L5.bo_st] in E1. injection E1 as <- <-. destruct (RB _ _ E2) as (-> & ELB). intros X0.
    subst BX. rewrite ELB in ND. rewrite <- app_assoc in ND.
    exact (L5ADVHO.nodup_app_fst [(q', 64)] (BX4 ++ LB) (q', 64) (q2, 8 * 8) ND ltac:(left; reflexivity) ltac:(right; left; reflexivity) (eq_sym X0)). }
  split.
  { intros c q c' q' E1 E2. cbn [bn L5.bo_st] in E1. injection E1 as <- <-. rewrite STQ in E2. injection E2 as <- <-.
    exact (L5ADVHO.nodup_app_fst BX LB (q2, 8 * 8) (qX, 64) ND (INBX_4 _ ltac:(right; left; reflexivity)) INX). }
  split; intros c q c' q' E1; discriminate E1.
Qed.

Lemma gn_fin (cre : credit) (X qX dv fdv : Z) (fx : FPState) Rc Mc modelc LBr LKc crc Ac q0 q2 (n : Z) (bq br bn0 bd0 : L5.bigobj) fbn' fbd' d1 (nn : nat) wq wr wn :
  let BX4 := [(q0, 8 * 8); (q2, 8 * 8)] in let BX := LBr ++ BX4 in
  let bn := L5.BO fbn' nn (L5.BDyn 8 q2) in let bd := L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1) in
  let W := [(X, 32); (qX, 64); (ro, 32)] in
  let cells := [(E - 304, F + 32); (E - 344, 0); (E - 296, X); (E - 264, X); (E - 288, ro); (E - 328, 0); (E - 280, F + 96); (E - 312, 0); (E - 336, F); (E - 320, X / 8 + 2147450880); (E - 352, (X + 8) / 8 + 2147450880);
                (E - 360, F); (E - 120, F + 48); (E - 112, 1); (E - 272, 1); (E - 376, 0); (E - 368, ro / 8 + 2147450880); (E - 240, L5.bo_data ro br); (E - 136, qX)] in
  SCRD = L5DIA.DIVN_SCR -> ri_inv HI LB FF LK cre A M (vml_of model) -> L5OMA.stksh ar M (E - SCRD) ->
  In (qX, 64) LB -> aobj FF X 32 -> aobj FF ro 32 -> (X + 32 <= ro \/ ro + 32 <= X) ->
  L5DIA.mword_obj M dv fdv -> L5DIA.stkobj ar E dv 32 ->
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 n -> getr Rc (reg 27) = Z_to_bv 64 0 -> getr Rc (reg 18) = Z_to_bv 64 SH ->
  tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc X bq wq -> trk BX Mc bn bd bn0 bd0 wn [L5DSA.MWORD] (Some (q0, 8 * 8)) cells 0 ->
  L5.bo_st bq = L5.BDyn 8 qX ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n -> 0 <= n <= 6 ->
  match skind (L5.bo_st br) with None => LBr = [] | Some (cap, q) => cap = 8 /\ LBr = [(q, 64)] end ->
  L5OMA.acredit_after L cre L5DIA.DIVN_K L5DIA.DIVN_BYTES crc ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
      L5DIA.divN_postA L ar LB FF LK' cre M M' R R' X qX ro dv fdv E LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93350 Mc modelc) K.
Proof.
  intros BX4 BX bn bd W cells ESCR HH0 SSH INX AOX AOR APXR MWD SKD BI RI X19 X27 X18 TR TQ TRK STQ LENR LENQ NR RSK CRA KN.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (ND : NoDup (map fst (BX ++ LB))). { clear - WF0. decompose [and] WF0. assumption. }
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  edestruct L5ADVEA.obj_rng with (o := X) as ((XR1 & XR2 & _) & _); try first [exact LY | exact HIok | exact BI | exact AOX'].
  pose proof TR as (OBR & OLR & SZR & INR). pose proof TQ as (OBQ & OLQ & SZQ & INQ).
  pose proof (len_le_cap Mc ro br OBR) as LCR. fold (L5.bo_cap br) in LCR.
  assert (INBX_r : forall b, In b LBr -> In b BX) by (intros b Hb; subst BX; apply in_or_app; left; exact Hb).
  assert (INBX_4 : forall b, In b BX4 -> In b BX) by (intros b Hb; subst BX; apply in_or_app; right; exact Hb).
  assert (RB : forall cap q, L5.bo_st br = L5.BDyn cap q -> cap = 8 /\ LBr = [(q, 64)]). { intros cap q Eq. rewrite Eq in RSK. cbn [skind] in RSK. exact RSK. }
  assert (NCL : forall q k a, In (q, k) BX -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a).
  { intros q k a Hin Ha. exact (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac q k a BI Hin Ha). }
  (* [comment removed for export] *)
  destruct (gn_dist W LBr q0 q2 qX Mc modelc LKc crc Ac bq br fbn' nn fbd' d1 BI INX STQ RSK) as (NQB & NQNR & NQNQ & NQDR & NQDQ).
  (* [comment removed for export] *)
  assert (COVR : forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * (n + 1) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a).
  { intros a Ha Hc OUT. unfold L5.bo_data, L5.bo_cap in Ha, LCR. destruct (L5.bo_st br) as [v0 v1|cap q] eqn:Eq.
    - apply (OUT (ro, 32)). right; right; left; reflexivity. unfold L5.in_rng. cbn [fst snd]. clear - Ha LCR LENR. lia.
    - destruct (RB cap q eq_refl) as (-> & ELB). apply (NCL q 64 a (INBX_r _ ltac:(rewrite ELB; left; reflexivity))). clear - Ha LCR LENR; lia. exact Hc. }
  assert (COVQ : forall a, L5.bo_data X bq <= a < L5.bo_data X bq + 8 * (n - 0) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a).
  { intros a Ha _ OUT. unfold L5.bo_data in Ha. rewrite STQ in Ha. apply (OUT (qX, 64)). right; left; reflexivity. unfold L5.in_rng. cbn [fst snd]. clear - Ha NR. lia. }
  assert (WSH : forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a).
  { intros a SHA rr [<-|[<-|[<-|[]]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    - exact (SH_OFF_OBJ W BX Mc modelc LKc crc Ac X a BI AOX' SHA IR).
    - exact (SH_OFF_BLK W BX Mc modelc LKc crc Ac qX 64 a BI AOR' ltac:(apply in_or_app; right; exact INX) SHA IR).
    - exact (SH_OFF_OBJ W BX Mc modelc LKc crc Ac ro a BI AOR' SHA IR). }
  (* [comment removed for export] *)
  assert (NI4 : forall b, In b (BX4 ++ LB) -> ~ In (fst b) (map fst LBr)).
  { intros b Hb X0. apply in_map_iff in X0. destruct X0 as (b1 & E1 & H1). subst BX. rewrite <- app_assoc in ND. exact (L5ADVHO.nodup_app_fst LBr _ b1 b ND H1 Hb E1). }
  assert (L2 : In (q0, 8 * 8) (BX ++ LB) /\ lb_remove q0 (BX ++ LB) = (LBr ++ [(q2, 8 * 8)]) ++ LB).
  { apply (lift_rm LB LBr BX4 [(q2, 8 * 8)] (Some (q0, 8 * 8)) NI4). split. left; reflexivity. subst BX4. cbn [app]. apply lb_remove_head. }
  assert (L3 : In (q2, 8 * 8) ((LBr ++ [(q2, 8 * 8)]) ++ LB) /\ lb_remove q2 ((LBr ++ [(q2, 8 * 8)]) ++ LB) = (LBr ++ []) ++ LB).
  { apply (lift_rm LB LBr [(q2, 8 * 8)] [] (Some (q2, 8 * 8))). intros b Hb. apply NI4. right. exact Hb. split. left; reflexivity. cbn [app]. apply lb_remove_head. }
  apply (gn_back fx Rc Mc modelc W BX (LBr ++ [(q2, 8 * 8)]) (LBr ++ []) (LBr ++ []) LKc crc Ac X X 0 0 n bq br bn bd bn0 bd0 wq wr wn [L5DSA.MWORD] (Some (q0, 8 * 8)) cells 0
           BI RI X19 X27 X18 AOR AOX ltac:(clear - APXR; lia) TR TQ TRK LENR ltac:(rewrite LENQ; clear; lia) ltac:(reflexivity) ltac:(clear - NR; lia) ltac:(clear; lia)).
  { vm_compute. intros X0; discriminate X0. }
  { subst cells. cbn [In]. do 14 right. left. reflexivity. }
  { subst cells. cbn [In]. do 3 right. left. reflexivity. }
  { clear - XR1 XR2; lia. }
  { subst cells. cbn [In]. do 17 right. left. reflexivity. }
  { replace (L5.bo_data X bq) with qX by (unfold L5.bo_data; rewrite STQ; reflexivity). subst cells. cbn [In]. do 18 right. left. reflexivity. }
  { replace (L5.bo_data (F + 32) bd) with (F + 48) by (unfold L5.bo_data; cbn [bd L5.bo_st]; clear; lia). subst cells. cbn [In]. do 12 right. left. reflexivity. }
  { subst cells. cbn [In]. do 11 right. left. reflexivity. }
  { subst cells. cbn [In]. do 4 right. left. reflexivity. }
  { subst cells. cbn [In]. do 9 right. left. reflexivity. }
  { subst cells. cbn [In]. do 2 right. left. reflexivity. }
  { subst cells. cbn [In]. do 8 right. left. reflexivity. }
  { subst cells. cbn [In]. left. reflexivity. }
  { subst cells. cbn [In]. do 6 right. left. reflexivity. }
  { subst cells. cbn [In]. do 7 right. left. reflexivity. }
  { clear; lia. }
  { subst cells. cbn [In]. right. left. reflexivity. }
  { intros c v Hin. subst cells. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear; lia|]). destruct Hin. }
  { exact SSH. }
  { intros a Ha OUT. apply (OUT (X, 32)). left; reflexivity. exact Ha. }
  { exact WSH. }
  { exact COVR. }
  { exact COVQ. }
  { exact NQB. } { exact NQNR. } { exact NQNQ. } { exact NQDR. } { exact NQDQ. }
  { exact L2. }
  { exact L3. }
  { reflexivity. }
  { intros cap q Eq. rewrite STQ in Eq. injection Eq as <- <-. apply in_or_app. right. exact INX. }
  { intros cap q Eq. destruct (RB cap q Eq) as (-> & ELB). apply in_or_app. left. apply in_or_app. left. rewrite ELB. left; reflexivity. }
  intros fxf Rf Mf modelf Af fbq' bqf wqf brf wrf RPf IAf AHf OBQf OLQf FBQf SSQf LENQf OBRf OLRf SSRf RTf AMf HHf.
  apply (KN fxf Rf Mf modelf ((LBr ++ []) ++ LB) crc LKc Af).
  2: exact RTf. 2:{ intros x Hx. apply IAf. apply B4. exact Hx. } 2: exact AMf. 2: exact B5. 2: exact HHf.
  split. exact RPf.
  split.
  { destruct bqf as [fbq lq stq]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. unfold L5ADVEA.same_store in SSQf. rewrite STQ in SSQf. destruct stq as [? ?|c1 q1]. destruct SSQf. destruct SSQf as (-> & ->).
    exists fbq, lq, wqf. split. exact OBQf. split. exact OLQf. split.
    - rewrite FBQf. rewrite Z.lor_spec, Z.land_spec. change (Z.testbit 253 1) with false. change (Z.testbit (2 * 0) 1) with false. rewrite andb_false_r. reflexivity.
    - clear - LENQf NR. lia. }
  split.
  { destruct brf as [fbr lr str]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. exists fbr, lr, str, wrf. split. exact OBRf. split. exact OLRf.
    unfold L5ADVEA.same_store in SSRf. destruct (L5.bo_st br) as [v0 v1|c0 q0'] eqn:Eq; destruct str as [w0 w1|c1 q1]; try (destruct SSRf; fail).
    - cbn [skind] in RSK. rewrite RSK. reflexivity.
    - destruct SSRf as (-> & ->). destruct (RB c0 q0' eq_refl) as (-> & ELB). split. reflexivity. rewrite ELB in HHf |- *. split. reflexivity.
      exact (afresh_of_inv L ar C HI HIok q0' 64 LB FF LKc crc Af Mf _ HHf). }
  split.
  { destruct MWD as (OBD & SGD0). split. 2: exact SGD0. destruct SKD as (SK1 & SK2 & SK3).
    pose proof G as G0. destruct G0 as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    pose proof (aobj_facts L ar C HI LY HIok LB FF LK cre A M model X 32 E SCRD HH0 AOX ltac:(clear; lia) ltac:(reflexivity)) as ((_ & XCE & _) & _).
    pose proof (aobj_facts L ar C HI LY HIok LB FF LK cre A M model ro 32 E SCRD HH0 AOR ltac:(clear; lia) ltac:(reflexivity)) as ((_ & RCE & _) & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB & _). destruct (proj1 (WB (qX, 64) INX)) as (_ & _ & _ & _ & QCE & _). cbn [fst snd] in QCE.
    destruct AHf as (EKf & _).
    eapply L5C.big_at_agree. 4: exact OBD. 2: clear - SK1 ER; lia. 2: clear - SK2 SPT; lia.
    intros i Hi. cbn in Hi. apply EKf. split. clear - Hi SK1 SK2 SPT ER; lia. split.
    - apply stack_client. clear - Hi SK1 SK2 SPT SLO SPC; lia. clear - Hi SK1; lia.
    - intros rr [<-|[<-|[<-|[]]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - IR Hi SK1 XCE SLO SPC; lia. clear - IR Hi SK1 QCE SLO SPC; lia. clear - IR Hi SK1 RCE SLO SPC; lia. }
  split. exact CRA.
  rewrite <- ESCR. exact AHf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cred_after3 cre : L5OMA.acredit_after L cre L5DIA.DIVN_K L5DIA.DIVN_BYTES (adebit L (adebit L (adebit L cre 64) 64) 64).
Proof. unfold L5OMA.acredit_after, L5OMA.adebits, adebit, credit_le, L5DIA.DIVN_K, L5DIA.DIVN_BYTES. cbn [fst snd]. split; clear; lia. Qed.
Lemma cred_after2 cre : L5OMA.acredit_after L cre L5DIA.DIVN_K L5DIA.DIVN_BYTES (adebit L (adebit L cre 64) 64).
Proof.
  destruct (aly_cost L C LY) as (P1 & P2 & P3).
  unfold L5OMA.acredit_after, L5OMA.adebits, adebit, credit_le, L5DIA.DIVN_K, L5DIA.DIVN_BYTES. cbn [fst snd]. split. clear - P1; lia. clear - P2 P3; nia.
Qed.

Lemma gn_all (cre : credit) (X qX dv fdv : Z) (bX : L5.bigobj) (wX : list Z) (fx1 : FPState) q2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd :
  SCRD = L5DIA.DIVN_SCR ->
  ri_inv HI LB FF LK cre A M (vml_of model) -> L5OMA.stksh ar M (E - SCRD) ->
  L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
  In (qX, 64) LB -> aobj FF X 32 -> shadow_zero M X 4 ->
  L5DIA.mword_obj M dv fdv -> L5DIA.stkobj ar E dv 32 ->
  L5DIA.zero_obj M ro -> aobj FF ro 32 -> shadow_zero M ro 4 -> (X + 32 <= ro \/ ro + 32 <= X) ->
  L5OMA.acredit_for L cre L5DIA.DIVN_K L5DIA.DIVN_BYTES ->
  atG L ar HI R M model LB FF LK A E SCRD F ro Same (Grown q2 8) R1 M1 model1 cr1 LK1 A1 X X qn bits 0 bn bd wX [L5DSA.MWORD] ->
  cr1 = adebit L cre 64 ->
  L5.bo_len bn = L5.bo_len bX -> L5.bo_st bn = L5.BDyn 8 q2 -> L5.bo_len bd = 1%nat -> L5.bo_st bd = L5.BInl L5DSA.MWORD 0 -> bits = 0 -> qn = 0 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
      L5DIA.divN_postA L ar LB FF LK' cre M M' R R' X qX ro dv fdv E LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
          (F3 fl3 F1c fl1c F1d fl1d : Z),
      L5DIA.divN_e3A L ar LB FF cre M M' R R' X qX (L5.bo_len bX) ro dv E F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' (L5DIA.ff_n FF E F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x930a8 M1 model1) K.
Proof.
  intros ESCR HH0 SSH OBX OLX STX LENX INX AOX SZX MWD SKD ZR AOR SZR APXR CRF ATG ECR1 LNB STN LND STD EBITS EQN KN KE3. subst bits qn.
  assert (TX : tob LB M X bX wX). { split. exact OBX. split. exact OLX. split. exact SZX. intros cap q Eq. rewrite STX in Eq. injection Eq as <- <-. exact INX. }
  set (zo := L5.BO 0 0 (L5.BInl 0 0)).
  assert (TR0 : tob LB M ro zo []). { split. exact ZR. split. { split. reflexivity. split. constructor. reflexivity. } split. exact SZR. intros cap q Eq. discriminate Eq. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cre A M model ro 32 E SCRD HH0 AOR ltac:(clear; lia) ltac:(reflexivity)) as ((RLO & RCE & RHI & _) & _).
  assert (ROR : 0 <= ro < 2 ^ 64) by (clear - RLO RHI; lia).
  assert (CRD1 : L5OMA.acredit_for L cr1 2 128).
  { rewrite ECR1. exact (cred_step L cre 3 192 64 CRF ltac:(clear; lia) ltac:(clear; lia)). }
  pose proof ATG as (_ & _ & X18 & X21 & X22 & X25 & X26 & X27 & _).
  apply (GN_FRONT cre X bX wX fx1 q2 R1 M1 model1 cr1 LK1 A1 0 0 bn bd HH0 SSH TX AOX LENX ROR CRD1 ATG LNB STN LND STD).
  intros fx4 R4 M4 model4 q0 bn0 bd0 fbd' fbn' d1 cr4 LK4 A4 BX4 BI4 RI4 KS4 p19 p25 p1 p10 p11 p20 p24 TD4 TN4 ON4 OD4 LNN0 STN0 LND0 STD0 SGD SGN DSH4 SPL4 S360 S120 S112 S272 HDR4 PX4 ECR4 IA4 ILK4.
  assert (P18 : getr R4 (reg 18) = Z_to_bv 64 SH) by (rewrite (KS4 18%nat) by inl; exact X18).
  assert (P21 : getr R4 (reg 21) = Z_to_bv 64 X) by (rewrite (KS4 21%nat) by inl; exact X21).
  assert (P22 : getr R4 (reg 22) = Z_to_bv 64 F) by (rewrite (KS4 22%nat) by inl; exact X22).
  assert (P26 : getr R4 (reg 26) = Z_to_bv 64 (X + 8)) by (rewrite (KS4 26%nat) by inl; exact X26).
  assert (P27 : getr R4 (reg 27) = Z_to_bv 64 F) by (rewrite (KS4 27%nat) by inl; exact X27).
  assert (ECR4' : cr4 = adebit L (adebit L cre 64) 64) by (rewrite ECR4, ECR1; reflexivity).
  pose proof (rlen_le wX) as RLE. pose proof (proj1 OLX) as LWX. rewrite LWX in RLE.
  destruct (Nat.eq_dec (rlen wX) 0) as [RZ|RNZ].
  - (* [comment removed for export] *)
    rewrite RZ in p11, p20, TN4. cbn [firstn] in TN4. change (Z.of_nat 0) with 0 in p11, p20.
    apply (gn_e3 cre X qX dv bX wX fx4 R4 M4 model4 q0 q2 bn0 bd0 fbd' fbn' d1 cr4 LK4 A4 ESCR HH0 TX AOX STX ROR BI4 RI4 P18 P21 P22 P26 P27 p19 p25 p1 p10 p11 p20 p24 TD4 TN4 ON4 OD4
             LNN0 STN0 LND0 STD0 SGD SGN DSH4).
    + exact (proj1 (SPL4 _ _ ltac:(left; reflexivity))).
    + exact (proj1 (SPL4 _ _ ltac:(do 2 right; left; reflexivity))).
    + exact (proj1 (SPL4 _ _ ltac:(do 3 right; left; reflexivity))).
    + exact (proj1 (SPL4 _ _ ltac:(do 6 right; left; reflexivity))).
    + exact (proj1 (SPL4 _ _ ltac:(do 8 right; left; reflexivity))).
    + exact (proj1 (SPL4 _ _ ltac:(do 4 right; left; reflexivity))).
    + exact S360. + exact S120. + exact S112. + exact S272. + exact HDR4. + exact PX4. + exact ECR4'. + exact KE3.
  - (* [comment removed for export] *)
    set (nn := rlen wX) in *. assert (NNR : (1 <= nn <= 6)%nat) by (clear - RNZ RLE LENX; lia).
    set (bn' := L5.BO fbn' nn (L5.BDyn 8 q2)) in *. set (bd' := L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1)) in *.
    set (cells := [(E - 304, F + 32); (E - 344, 0); (E - 296, X); (E - 264, X); (E - 288, ro); (E - 328, 0); (E - 280, F + 96); (E - 312, 0); (E - 336, F); (E - 320, X / 8 + 2147450880); (E - 352, (X + 8) / 8 + 2147450880);
                   (E - 360, F); (E - 120, F + 48); (E - 112, 1); (E - 272, 1)]).
    assert (TRK4 : trk BX4 M4 bn' bd' bn0 bd0 (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) cells 0).
    { split. exact TN4. split. exact TD4. split. exact ON4. split. exact OD4. split. 2: split; [exact PX4 | split; [exact HDR4 | exact DSH4]].
      intros a v Hin. subst cells. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [try (apply SPL4; rewrite <- Hin; solve [cbn [In]; repeat (first [left; reflexivity | right])])|]). 5: destruct Hin.
      all: injection Hin as <- <-; split; [assumption | clear; lia]. }
    pose proof BI4 as (B14 & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B14) as WF4.
    assert (ND4 : NoDup (map fst (BX4 ++ LB))). { clear - WF4. decompose [and] WF4. assumption. }
    assert (NQ2X : q2 <> qX). { exact (L5ADVHO.nodup_app_fst BX4 LB (q2, 8 * 8) (qX, 64) ND4 ltac:(right; left; reflexivity) INX). }
    assert (CRD4 : L5OMA.acredit_for L cr4 1 64).
    { rewrite ECR4. exact (cred_step L cr1 2 128 64 CRD1 ltac:(clear; lia) ltac:(clear; lia)). }
    apply (gn_mid1 cre X qX bX wX fx4 R4 M4 model4 BX4 LK4 cr4 A4 bn' bd' bn0 bd0 (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) cells 0 nn HH0 TX AOX STX TR0 AOR APXR BI4 RI4 p1 p10 p11 p25 P26 TRK4
             ltac:(subst cells; cbn [In]; do 2 right; left; reflexivity) ltac:(subst cells; cbn [In]; do 9 right; left; reflexivity) ltac:(subst cells; cbn [In]; do 10 right; left; reflexivity) ltac:(subst cells; cbn [In]; do 4 right; left; reflexivity)
             ltac:(intros c v Hin; subst cells; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear; lia|]); destruct Hin)
             ltac:(reflexivity) NNR ltac:(clear - RLE; lia)).
    { intros c q c' q' E1 E2. cbn [bn' L5.bo_st] in E1. injection E1 as <- <-. rewrite STX in E2. injection E2 as <- <-. exact NQ2X. }
    { intros c q c' q' E1. discriminate E1. }
    { exact CRD4. }
    intros fx7 R7 M7 model7 gr bq br cr7 LK7 A7 wq BX7 BI7 RI7 KR7 r22 S136_7 S128_7 TQ7 LENQ FBQ STQ TR7 LENR GRF TRK7 IA7 ILK7.
    (* [comment removed for export] *)
    set (LBr := match gr with Same => [] | Grown q cap => [(q, 64)] end).
    assert (GR7 : BX7 = LBr ++ BX4 /\ match skind (L5.bo_st br) with None => LBr = [] | Some (cap, q) => cap = 8 /\ LBr = [(q, 64)] end
                  /\ L5OMA.acredit_for L cr7 (if L5.bo_dyn br then 0 else 1) (if L5.bo_dyn br then 0 else 64)
                  /\ L5OMA.acredit_after L cre L5DIA.DIVN_K L5DIA.DIVN_BYTES cr7
                  /\ (gr = Same -> cr7 = cr4)).
    { pose proof (dyn_kind M7 ro br (proj1 TR7)) as DK. subst BX7 LBr. destruct gr as [|qr capr].
      - destruct GRF as (_ & SS & ->). unfold L5ADVEA.same_store in SS. cbn [L5.bo_st] in SS. destruct (L5.bo_st br) as [v0 v1|c0 q0'] eqn:Eq. 2: destruct SS.
        cbn [skind] in DK |- *. rewrite DK. split. reflexivity. split. reflexivity. split. exact CRD4. split. rewrite ECR4'. apply cred_after2. reflexivity.
      - destruct GRF as (_ & ST & -> & ->). rewrite ST in DK |- *. cbn [skind] in DK |- *. rewrite DK. split. reflexivity. split. split; reflexivity.
        split. exact (cred_step L cr4 1 64 64 CRD4 ltac:(clear; lia) ltac:(clear; lia)). split. rewrite ECR4'. apply cred_after3. intros X0; discriminate X0. }
    destruct GR7 as (EBX7 & RSK7 & CRD7 & CRA7 & CRS7).
    edestruct L5ADVEA.obj_rng with (o := X) as ((XR1 & XR2 & _) & _); try first [exact LY | exact HIok | exact BI7 | apply aobj_cons; exact AOX].
    assert (DATQ : L5.bo_data X bq = qX) by (unfold L5.bo_data; rewrite STQ; reflexivity).
    assert (DATD : L5.bo_data (F + 32) bd' = F + 48) by (unfold L5.bo_data; cbn [bd' L5.bo_st]; clear; lia).
    set (n := Z.of_nat nn - 1).
    assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
    assert (WSH7 : forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside [(X, 32); (qX, 64); (ro, 32)] a).
    { intros a SHA rr [<-|[<-|[<-|[]]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR.
      - exact (SH_OFF_OBJ _ BX7 M7 model7 LK7 cr7 A7 X a BI7 AOX' SHA IR).
      - exact (SH_OFF_BLK _ BX7 M7 model7 LK7 cr7 A7 qX 64 a BI7 AOR' ltac:(apply in_or_app; right; exact INX) SHA IR).
      - exact (SH_OFF_OBJ _ BX7 M7 model7 LK7 cr7 A7 ro a BI7 AOR' SHA IR). }
    (* [comment removed for export] *)
    set (cells7 := (E - 136, qX) :: (E - 128, Z.of_nat nn - 1) :: cells).
    assert (TRK7' : trk BX7 M7 bn' bd' bn0 bd0 (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) cells7 0).
    { apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ cells cells7 _ TRK7). intros a v [Eq|[Eq|Hin]]. injection Eq as <- <-. right. split. exact S136_7. clear; lia.
      injection Eq as <- <-. right. split. exact S128_7. clear; lia. left. exact Hin. }
    apply (G7T X fx7 R7 M7 model7 _ BX7 LK7 cr7 A7 bq br bn' bd' bn0 bd0 wq (firstn nn wX) (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) cells7 0 n 0 0 BI7 RI7 AOX AOR
             ltac:(rewrite (KR7 20%nat) by inl; rewrite p20; f_equal; subst n; clear; lia) r22 ltac:(rewrite (KR7 24%nat) by inl; exact p24) ltac:(clear; lia)
             TQ7 TR7 TRK7' ltac:(rewrite LENR; subst n; clear; lia) ltac:(reflexivity)
             ltac:(subst n; clear - NNR; lia) ltac:(clear; lia)).
    { subst cells7 cells. cbn [In]. do 16 right. left. reflexivity. }
    { rewrite DATD. subst cells7 cells. cbn [In]. do 14 right. left. reflexivity. }
    { intros c v Hin. subst cells7 cells. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear; lia|]). destruct Hin. }
    { exact WSH7. }
    intros fx8 R8 M8 model8 BI8 RI8 KS8 q19 q21 q22 q27 TQ8 TR8 TRK8 S232 S240 S376 S368.
    assert (X18_8 : getr R8 (reg 18) = Z_to_bv 64 SH). { rewrite (KS8 18%nat) by inl. rewrite (KR7 18%nat) by inl. exact P18. }
    assert (FINCELLS : forall Mx BXx (brx : L5.bigobj), trk BXx Mx bn' bd' bn0 bd0 (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) ((E - 376, 0) :: (E - 368, ro / 8 + 2147450880) :: cells) 0 ->
              L5.u64_at RSEGS Mx (E - 240) (L5.bo_data ro brx) -> L5.u64_at RSEGS Mx (E - 136) qX ->
              trk BXx Mx bn' bd' bn0 bd0 (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8))
                [(E - 304, F + 32); (E - 344, 0); (E - 296, X); (E - 264, X); (E - 288, ro); (E - 328, 0); (E - 280, F + 96); (E - 312, 0); (E - 336, F); (E - 320, X / 8 + 2147450880); (E - 352, (X + 8) / 8 + 2147450880);
                 (E - 360, F); (E - 120, F + 48); (E - 112, 1); (E - 272, 1); (E - 376, 0); (E - 368, ro / 8 + 2147450880); (E - 240, L5.bo_data ro brx); (E - 136, qX)] 0).
    { intros Mx BXx brx TRKx S240x S136x. apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ _ _ _ TRKx). intros a v Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; first [left; subst cells; solve [cbn [In]; repeat (first [left; reflexivity | right])] | right; split; [assumption | clear; lia]] |]). destruct Hin. }
    set (cells8 := (E - 376, 0) :: (E - 368, ro / 8 + 2147450880) :: cells).
    assert (TRK8' : trk BX7 M8 bn' bd' bn0 bd0 (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) cells8 0).
    { apply (L5ADVGO2.trk_recell LB E F _ _ _ _ _ _ _ _ _ cells7 cells8 _ TRK8). intros a v [Eq|[Eq|Hin]]. injection Eq as <- <-. right. split. exact S376. clear; lia.
      injection Eq as <- <-. right. split. exact S368. clear; lia. left. right; right. exact Hin. }
    assert (S136_8 : L5.u64_at RSEGS M8 (E - 136) qX). { exact (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK8 ltac:(left; reflexivity)). }
    assert (S128_8 : L5.u64_at RSEGS M8 (E - 128) (Z.of_nat nn - 1)). { exact (L5ADVGO2.trk_cell LB E F _ _ _ _ _ _ _ _ _ _ _ _ _ TRK8 ltac:(right; left; reflexivity)). }
    destruct (nth_w (firstn nn wX) (Z.to_nat n) <? nth_w [L5DSA.MWORD] (Z.to_nat 0)) eqn:TEST.
    + (* [comment removed for export] *)
      pose proof (FINCELLS M8 BX7 br TRK8' S240 S136_8) as TRKA.
      rewrite EBX7 in BI8, TQ8, TR8, TRKA.
      apply (gn_fin cre X qX dv fdv fx8 R8 M8 model8 LBr LK7 cr7 A7 q0 q2 n bq br bn0 bd0 fbn' fbd' d1 nn wq (firstn nn wX) (firstn nn wX) ESCR HH0 SSH INX AOX AOR APXR MWD SKD BI8 RI8 q19 q27
               X18_8 TR8 TQ8 TRKA STQ ltac:(rewrite LENR; subst n; clear; lia) ltac:(rewrite LENQ; subst n; clear - NNR; lia) ltac:(subst n; clear - NNR; lia) RSK7 CRA7 KN).
    + (* [comment removed for export] *)
      clear TEST. rewrite EBX7 in BI8, TQ8, TR8, TRK8'.
      set (W := [(X, 32); (qX, 64); (ro, 32)]) in *.
      set (nb := (nn - 1)%nat).
      pose proof (dyn_kind M8 ro br (proj1 TR8)) as DKR. pose proof (dyn_kind M8 X bq (proj1 TQ8)) as DKQ. rewrite STQ in DKQ. cbn [skind] in DKQ.
      assert (CAPQ : L5.bo_cap bq = 8) by (unfold L5.bo_cap; rewrite STQ; reflexivity).
      assert (RU8 : round_up (Z.of_nat nb + 2) = 8). { unfold round_up. subst nb. clear - NNR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct (gn_dist W LBr q0 q2 qX M8 model8 LK7 cr7 A7 bq br fbn' nn fbd' d1 BI8 INX STQ RSK7) as (NQB & NQNR & NQNQ & NQDR & NQDQ).
      assert (S232' : L5.u64_at RSEGS M8 (E - 232) (Z.of_nat (Datatypes.S nb))). { replace (Datatypes.S nb) with (L5.bo_len br) by (rewrite LENR; subst nb; clear - NNR; lia). exact S232. }
      assert (S128' : L5.u64_at RSEGS M8 (E - 128) (Z.of_nat nb)). { replace (Z.of_nat nb) with (Z.of_nat nn - 1) by (subst nb; clear - NNR; lia). exact S128_8. }
      apply (GBT fx8 R8 M8 model8 W (LBr ++ BX4) LK7 cr7 A7 X br bq bn' bd' bn0 bd0 (firstn nn wX) wq (firstn nn wX) [L5DSA.MWORD] (Some (q0, 8 * 8)) cells8 0 nb nb BI8 RI8 AOR AOX
               ltac:(clear - APXR; lia) ltac:(clear - XR1 XR2; lia)
               ltac:(rewrite (KS8 20%nat) by inl; rewrite (KR7 20%nat) by inl; rewrite p20; f_equal; subst nb; clear - NNR; lia) q21 q22
               ltac:(rewrite (KS8 26%nat) by inl; rewrite (KR7 26%nat) by inl; exact P26)
               TR8 ltac:(rewrite LENR; subst nb; clear - NNR; lia) TQ8 LENQ TRK8'
               ltac:(subst cells8 cells; cbn [In]; do 4 right; left; reflexivity) ltac:(subst cells8 cells; cbn [In]; do 6 right; left; reflexivity) ltac:(subst cells8 cells; cbn [In]; do 11 right; left; reflexivity)
               ltac:(subst cells8 cells; cbn [In]; do 12 right; left; reflexivity) ltac:(subst cells8 cells; cbn [In]; right; left; reflexivity) S232' S128'
               ltac:(intros c v Hin; subst cells8 cells; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear; lia|]); destruct Hin)).
      { subst nb. clear - NNR; lia. } { subst nb. clear - NNR; lia. }
      { intros DY. rewrite DY in DKR. unfold L5.bo_cap. destruct (L5.bo_st br) as [v0 v1|c0 q0'] eqn:Eq. discriminate DKR. cbn [skind] in RSK7. destruct RSK7 as (-> & _). subst nb. clear - NNR. lia. }
      { intros _. rewrite CAPQ. subst nb. clear - NNR. lia. }
      { rewrite DKQ. rewrite RU8. destruct (L5.bo_dyn br); exact CRD7. }
      { intros a OUT. split; intros rr [<-|[]]; apply OUT. right; right; left; reflexivity. left; reflexivity. }
      { intros DL a Hc OUT IR. unfold L5.in_rng in IR. cbn [fst snd] in IR. unfold L5.bo_data in IR. destruct (L5.bo_st br) as [v0 v1|c0 q0'] eqn:Eq.
        - cbn [skind] in DKR. destruct DL as [DY|LE2]. rewrite DY in DKR. discriminate DKR.
          apply (OUT (ro, 32)). right; right; left; reflexivity. unfold L5.in_rng. cbn [fst snd]. clear - IR LE2. lia.
        - cbn [skind] in RSK7. destruct RSK7 as (-> & ELB).
          apply (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W (LBr ++ BX4) M8 model8 LK7 cr7 A7 q0' 64 a BI8).
          apply in_or_app. left. rewrite ELB. left; reflexivity. subst nb. clear - IR NNR. lia. exact Hc. }
      { intros _ a _ OUT IR. unfold L5.in_rng in IR. cbn [fst snd] in IR. unfold L5.bo_data in IR. rewrite STQ in IR.
        apply (OUT (qX, 64)). right; left; reflexivity. unfold L5.in_rng. cbn [fst snd]. subst nb. clear - IR NNR. lia. }
      { exact NQB. } { exact NQNR. } { exact NQNQ. } { exact NQDR. } { exact NQDQ. }
      intros fx9 R9 M9 model9 gr9 gq9 br9 bq9 cr9 LK9 A9 BXr BX9 BI9 RI9 KS9 s19 TR9 LENR9 GRF9 TQ9 LENQ9 GQF9 TRK9 S240_9 S136_9 ECR9 IA9 ILK9.
      destruct gq9 as [|qq capq]. 2:{ exfalso. destruct GQF9 as (_ & _ & _ & DYF & _). rewrite DKQ in DYF. discriminate DYF. }
      destruct GQF9 as (FBQ9 & SSQ9).
      assert (STQ9 : L5.bo_st bq9 = L5.BDyn 8 qX). { unfold L5ADVEA.same_store in SSQ9. rewrite STQ in SSQ9. destruct (L5.bo_st bq9) as [? ?|c1 q1]. destruct SSQ9. destruct SSQ9 as (-> & ->). reflexivity. }
      set (LBr9 := match gr9 with Same => LBr | Grown q cap => [(q, 64)] end).
      assert (RU9 : round_up (Z.of_nat (Datatypes.S (Datatypes.S nb))) = 8). { unfold round_up. subst nb. clear - NNR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (GR9 : BX9 = LBr9 ++ BX4 /\ match skind (L5.bo_st br9) with None => LBr9 = [] | Some (cap, q) => cap = 8 /\ LBr9 = [(q, 64)] end
                    /\ L5OMA.acredit_after L cre L5DIA.DIVN_K L5DIA.DIVN_BYTES cr9).
      { subst BX9 BXr LBr9. cbn [L5DLA.blocks_of L5DLA.adebl] in ECR9. destruct gr9 as [|q9 cap9].
        - destruct GRF9 as (_ & SS9). rewrite (SKIND_SAME _ _ SS9). cbn [L5DLA.adebl] in ECR9. subst cr9. split. reflexivity. split. exact RSK7. exact CRA7.
        - destruct GRF9 as (_ & ST9 & EC9 & DYF & _). rewrite RU9 in EC9. subst cap9. rewrite DYF in DKR.
          destruct (L5.bo_st br) as [v0 v1|c0 q0'] eqn:Eq. 2:{ cbn [skind] in DKR. discriminate DKR. } cbn [skind] in RSK7.
          assert (GS : gr = Same). { destruct gr as [|qr capr]. reflexivity. exfalso. destruct GRF as (_ & ST & _). discriminate ST. }
          rewrite RSK7. rewrite ST9. cbn [skind]. split. reflexivity. split. split; reflexivity.
          cbn [L5DLA.adebl] in ECR9. rewrite ECR9, (CRS7 GS), ECR4'. apply cred_after3. }
      destruct GR9 as (EBX9 & RSK9 & CRA9).
      assert (S136_9' : L5.u64_at RSEGS M9 (E - 136) qX). { unfold L5.bo_data in S136_9. rewrite STQ9 in S136_9. exact S136_9. }
      pose proof (FINCELLS M9 BX9 br9 TRK9 S240_9 S136_9') as TRK9'.
      rewrite EBX9 in BI9, TR9, TQ9, TRK9'.
      apply (gn_fin cre X qX dv fdv fx9 R9 M9 model9 LBr9 LK9 cr9 A9 q0 q2 (Z.of_nat nn) bq9 br9 bn0 bd0 fbn' fbd' d1 nn _ _ (firstn nn wX) ESCR HH0 SSH INX AOX AOR APXR MWD SKD BI9 RI9
               ltac:(rewrite s19; f_equal; subst nb; clear - NNR; lia) ltac:(rewrite (KS9 27%nat) by inl; exact q27) ltac:(rewrite (KS9 18%nat) by inl; exact X18_8)
               TR9 TQ9 TRK9' STQ9 ltac:(rewrite LENR9; subst nb; clear - NNR; lia) ltac:(rewrite LENQ9; subst nb; clear - NNR; lia) ltac:(clear - NNR; lia) RSK9 CRA9 KN).
Qed.
End DIV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem gen_N_ok : opdel_sized_spec L ar HI -> assign_spec L ar HI -> L5ACPAS.copya_stk_spec L ar HI -> L5DLA.norm_specA L ar HI -> resize_spec L ar HI ->
  L5ADVN.gen_N L ar HI.
Proof.
  intros Hdel Hasg Hcps Hnorm Hrsz. unfold L5ADVN.gen_N.
  intros R M model K LB FF LK cr A X qX rr dv fdv E r bX wX F fl LK2 M2 model2 fx1 q2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd HH AM HK G1 RA G2 A32 G4 STK STKSH FFR1 FFR3 FFRS OBX OLX STX LX SGX INX AOX SZX MW SO DFD
         ZR AOR SZR APXR CRF G ER UR1 AG ECR IA ILK LNB STN LND STD EBITS EQN KN KE3.
  assert (EA : aligned E 32) by exact A32.
  assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- G2; reflexivity).
  assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- G4; reflexivity).
  exact (gn_all R M model K LB FF LK A E L5DIA.DIVN_SCR F fl rr r LK2 M2 model2 cr G ER EA HK G4' L5ADVN.divN_scr STKSH L5ADVN.divN_scr8 FFR1 FFRS Hdel Hasg Hcps Hnorm Hrsz RA UR1 G2'
           cr X qX dv fdv bX wX fx1 q2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd eq_refl HH STKSH OBX OLX STX LX INX AOX SZX MW SO ZR AOR SZR APXR CRF AG ECR LNB STN LND STD EBITS EQN KN KE3).
Qed.
End WithIface.
End SCFG_1.
End L5ADVGNB.

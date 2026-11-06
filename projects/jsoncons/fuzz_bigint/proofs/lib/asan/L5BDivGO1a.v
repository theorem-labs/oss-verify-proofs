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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BDivGU L5BRed L5BDivHH L5BDivHS L5BDivGE L5BDivN L5BDivO1 L5BDivGN L5BDivGK L5BRzHuge L5BDivGK2 L5BDivGK3 L5BDivO2 L5BDivGO2 L5BDivGO2b L5BDivGO2c BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsAB0 L5OpMod1V L5Cmp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO1A.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGO2. Import L5ADVGO2B. Import L5ADVGO2C. Import L5ADVGK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac algn := lazymatch goal with |- ?h _ (Zpos _) => is_const h; lazymatch h with Z.le => fail | Z.lt => fail | Z.ge => fail | Z.gt => fail | _ => assumption end end.
Local Ltac sc := first [ asm | rk | gmem | algn | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma o1_vals (nb : nat) (b0 b1 : Z) (wb : list Z) :
  nb = 1%nat \/ nb = 2%nat -> wb = firstn nb [b0; b1] -> 0 <= b0 < 2 ^ 64 -> 0 <= b1 < 2 ^ 64 -> nth_w wb (nb - 1) <> 0 ->
  (nb = 1%nat -> 2 ^ 32 <= b0) -> (nb = 2%nat -> BigFactsBase.val wb <= BigFactsBase.val [L5PSA.A0; L5PSA.A1]) ->
  let c := L5DLA.clz_of (nth_w wb (nb - 1)) in let sec := L5DLA.second nb (L5DLA.shl_result wb c) in
  let rd := L5DLA.norm_words wb c sec in let rn := L5DLA.norm_words [L5PSA.A0; L5PSA.A1] c sec in
  let l1 := rlen rd in let n1 := rlen rn in
  0 <= c <= 63 /\
  (1 <= l1 <= 3)%nat /\ (2 <= n1 <= 4)%nat /\ (l1 <= n1)%nat /\ (n1 - l1 <= 2)%nat
  /\ (l1 <= length rd)%nat /\ (length rd <= 3)%nat /\ (n1 <= length rn)%nat /\ (length rn <= 4)%nat
  /\ 2 ^ 63 <= nth_w rd (l1 - 1) < 2 ^ 64
  /\ (sec = true -> nb = 2%nat /\ l1 = 3%nat /\ (3 <= n1)%nat /\ length rd = 3%nat /\ (3 <= length rn)%nat)
  /\ (sec = false -> l1 = nb /\ (n1 <= 3)%nat)
  /\ ((3 <= length rd)%nat <-> nb = 2%nat)
  /\ ((3 <= length rn)%nat <-> 1 <= c)
  /\ (nb = 2%nat -> 1 <= c).
Proof.
  intros NB WB R0 R1 TOP V1 V2. cbv zeta. split. exact (proj1 (L5OM1V.c_spec nb b0 b1 wb NB WB R0 R1 TOP V1 V2)).
  exact (L5OM1V.norm_facts nb b0 b1 wb NB WB R0 R1 TOP V1 V2).
Qed.

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
Lemma go1_front (cr0 : credit) (qo : Z) (wn wd : list Z) (fx1 : FPState) R1 M1 model1 cr1 LK1 A1 qn bits bn bd :
  ri_inv HI LB FF LK cr0 A M (vml_of model) -> L5OMA.stksh ar M (E - SCRD) ->
  0 <= ro < 2 ^ 64 -> 0 <= qo < 2 ^ 64 ->
  L5.bo_dyn bn = false -> L5.bo_dyn bd = false ->
  (1 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) <> 0 -> ((2 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) < 2 ^ 63) ->
  (1 <= L5.bo_len bn)%nat -> ((2 <= L5.bo_len bd)%nat -> (2 <= L5.bo_len bn)%nat /\ exists i, (i < L5.bo_len bn)%nat /\ nth_w wn i <> 0) ->
  L5OMA.acredit_for L cr1 2 128 ->
  atG L ar HI R M model LB FF LK A E SCRD F ro Same Same R1 M1 model1 cr1 LK1 A1 ro qo qn bits 1 bn bd wn wd ->
  (forall (fx4 : FPState) R4 M4 model4 (c : Z) (gd gn : growth) bn0 bd0 fbd' fbn' std stn cr4 LK4 A4,
      let sec := L5DLA.second (L5.bo_len bd) (L5DLA.shl_result wd c) in
      let rd := L5DLA.norm_words wd c sec in let rn := L5DLA.norm_words wn c sec in
      let BX4 := L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ [] in
      c = L5DLA.clz_of (nth_w wd (L5.bo_len bd - 1)) ->
      binv [] BX4 M4 model4 LK4 cr4 A4 -> rinvD R E R4 ->
      (forall x, In x [18; 21; 22; 26; 27]%nat -> getr R4 (reg x) = getr R1 (reg x)) ->
      getr R4 (reg 19) = Z_to_bv 64 (F + 32) -> getr R4 (reg 25) = Z_to_bv 64 (F + 96) ->
      getr R4 (reg 1) = Z_to_bv 64 0x9313c -> getr R4 (reg 10) = Z_to_bv 64 qo -> getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat (rlen rn) - Z.of_nat (rlen rd)) ->
      getr R4 (reg 20) = Z_to_bv 64 (Z.of_nat (rlen rn)) -> getr R4 (reg 24) = Z_to_bv 64 (if sec then 1 else 0) ->
      tob (BX4 ++ LB) M4 (F + 32) (L5.BO fbd' (rlen rd) std) (firstn (rlen rd) rd) ->
      tob (BX4 ++ LB) M4 (F + 96) (L5.BO fbn' (rlen rn) stn) (firstn (rlen rn) rn) ->
      gro_st gd bd std -> gro_st gn bn stn ->
      (match std with L5.BDyn cap _ => Z.of_nat (length rd) <= cap | L5.BInl _ _ => (length rd <= 2)%nat end) ->
      (match stn with L5.BDyn cap _ => Z.of_nat (length rn) <= cap | L5.BInl _ _ => (length rn <= 2)%nat end) ->
      L5ADVD.obj_at M4 (SPA + 200) bn0 None -> L5ADVD.obj_at M4 (SPA + 168) bd0 None ->
      spl E M4 [(E - 304, F + 32); (E - 344, 1); (E - 296, qo); (E - 264, ro); (E - 288, ro); (E - 328, bits); (E - 280, F + 96); (E - 312, qn); (E - 336, F); (E - 320, qo / 8 + 2147450880); (E - 352, (qo + 8) / 8 + 2147450880)] ->
      L5.u64_at RSEGS M4 (E - 360) F -> L5.u64_at RSEGS M4 (E - 120) (L5.bo_data (F + 32) (L5.BO fbd' (rlen rd) std)) -> L5.u64_at RSEGS M4 (E - 112) (Z.of_nat (rlen rd)) -> L5.u64_at RSEGS M4 (E - 272) (Z.of_nat (rlen rd)) ->
      L5.u64_at RSEGS M4 F 1102416563 -> dsh M4 F 0 248 248 248 248 -> L5.u32_at RSEGS M4 (E - 220) c ->
      Z.testbit fbn' 1 = false ->
      cr4 = L5DLA.adebl L cr1 (L5DLA.blocks_of gn ++ L5DLA.blocks_of gd) -> incl A1 A4 -> incl LK4 LK1 ->
      srealizes RSEGS SCFG (cfg (fx:=fx4) R4 RESIZE M4 model4) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x930a8 M1 model1) K.
Proof.
  intros HH0 SSH ROR QOR DYNF DYD LD1 TOPD TOPD63 LN1 NZN CRD (BI0 & RI0 & X18 & X21 & X22 & X25 & X26 & X27 & QNR & BITSR & TN & TD & ON & OD & SGN_N & SGN_D & SPL & DSH & HDR) KF.
  set (BX0 := L5ADVHO.bx12 Same Same) in *.
  set (cells := [(E - 304, F + 32); (E - 344, 1); (E - 296, qo); (E - 264, ro); (E - 288, ro); (E - 328, bits); (E - 280, F + 96); (E - 312, qn); (E - 336, F); (E - 320, qo / 8 + 2147450880); (E - 352, (qo + 8) / 8 + 2147450880)]) in *.
  assert (NDB : forall cap q, L5.bo_st bd <> L5.BDyn cap q). { intros cap q Eq. destruct TD as ((_ & _ & _ & OST) & _). rewrite Eq in OST. unfold L5.bo_dyn in DYD. rewrite (proj1 OST) in DYD. discriminate DYD. }
  assert (NDN : forall cap q, L5.bo_st bn <> L5.BDyn cap q). { intros cap q Eq. destruct TN as ((_ & _ & _ & OST) & _). rewrite Eq in OST. unfold L5.bo_dyn in DYNF. rewrite (proj1 OST) in DYNF. discriminate DYNF. }
  assert (CAPD : L5.bo_cap bd = 2). { unfold L5.bo_cap. destruct (L5.bo_st bd) as [? ?|cap q] eqn:Eq. reflexivity. exfalso. exact (NDB cap q eq_refl). }
  assert (CAPN : L5.bo_cap bn = 2). { unfold L5.bo_cap. destruct (L5.bo_st bn) as [? ?|cap q] eqn:Eq. reflexivity. exfalso. exact (NDN cap q eq_refl). }
  pose proof (len_le_cap M1 (F + 32) bd (proj1 TD)) as LLD. fold (L5.bo_cap bd) in LLD.
  pose proof (len_le_cap M1 (F + 96) bn (proj1 TN)) as LLC. fold (L5.bo_cap bn) in LLC.
  pose proof (one_le_cap M1 (F + 96) bn (proj1 TN)) as OLC. fold (L5.bo_cap bn) in OLC.
  pose proof (proj1 (proj2 TN)) as (LWY & WYOK & _).
  apply (G12C fx1 R1 M1 model1 BX0 LK1 cr1 A1 bn bd wn wd _ _ cells BI0 RI0 SSH TN TD ON OD SPL X25 X27).
  { subst cells. left. reflexivity. }
  { intros X0. rewrite DYNF in X0. discriminate X0. } { intros X0. rewrite DYD in X0. discriminate X0. }
  { rewrite CAPD, CAPN. apply (cred_weak L C LY cr1 2 128 _ _ CRD). clear; lia. clear; lia. }
  intros fx2 R2 M2' model2' gn0 gd0 bn0 bd0 cr2' LK2' A2 BX2 BI2 RI2 p19 p25 KS2 OFF2 S360_2 ON0 OD0 GNF GDF ECR2 IA2 ILK2.
  destruct gd0 as [|qd0 capd0]. 2:{ destruct GDF as (_ & X0). rewrite DYD in X0. discriminate X0. }
  destruct gn0 as [|qn0 capn0]. 2:{ destruct GNF as (_ & X0). rewrite DYNF in X0. discriminate X0. }
  cbn [L5DLA.blocks_of app L5ADVHO.on_of] in *.
  pose proof BI0 as (B1 & _).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX0 ++ LB) M1 o b ws -> L5ADVEA.oreg o b a -> ~ (SPA + 168 <= a < SPA + 232 \/ E - 360 <= a < E - 352)).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX0 M1 model1 LK1 cr1 A1 o b ws a BI0 AO TO OR). clear - X0 HSCR; lia. }
  assert (SUB2 : forall b0, In b0 (BX0 ++ LB) -> In b0 (BX2 ++ LB)). { intros b0 Hb. exact Hb. }
  assert (TN2 : tob (BX2 ++ LB) M2' (F + 96) bn wn).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX0 ++ LB) (BX0 ++ LB) (BX2 ++ LB) LK1 cr1 A1 model1 COPY_SCR _ M1 M2' (F + 96) bn wn B1 AON' TN OFF2).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN)) cap q Eq) as X0. split. exact X0. apply SUB2. exact X0. intros a OR. exact (NOFR _ _ _ a AON' TN OR). }
  assert (TD2 : tob (BX2 ++ LB) M2' (F + 32) bd wd).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX0 ++ LB) (BX0 ++ LB) (BX2 ++ LB) LK1 cr1 A1 model1 COPY_SCR _ M1 M2' (F + 32) bd _ B1 AOD' TD OFF2).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TD)) cap q Eq) as X0. split. exact X0. apply SUB2. exact X0. intros a OR. exact (NOFR _ _ _ a AOD' TD OR). }
  assert (SPL2 : spl E M2' cells).
  { intros a v Hin. destruct (SPL a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX0 ++ LB) COPY_SCR _ M1 M2' a v Hc H1 H2 OFF2).
    intros i Hi X0. subst cells. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear - Hi X0; lia|]). destruct Hin. }
  assert (HDR2 : L5.u64_at RSEGS M2' F 1102416563).
  { eapply L5C.u64_at_agree. 4: exact HDR. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFF2. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA COPY_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia.
    clear - Hi SFB. lia. }
  assert (DSH2 : dsh M2' F 0 248 248 248 248).
  { eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH | exact OFF2 | ]. intros j Hj X0. pose proof (L5ADVGO2.sh_rng L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER j Hj) as Y. clear - Y X0 ER. lia. }
  (* [comment removed for export] *)
  assert (E8 : (E - 224) mod 8 = 0 /\ (E - 220) / 8 = (E - 224) / 8). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SZP : shadow_zero M2' (E - 220) 1).
  { destruct (STK_DEST [] BX2 M2' model2' LK2' cr2' A2 (E - 224) BI2 SSH ltac:(clear; lia) ltac:(clear; lia) (proj1 E8) ltac:(intros a _ rr [])) as (_ & SZ176).
    intros j Hj. assert (j = 0) by (clear - Hj; lia). subst j. specialize (SZ176 0 ltac:(clear; lia)). unfold byte_at, S in *. rewrite (proj2 E8). exact SZ176. }
  assert (CR2 : L5DLA.acredits L cr2' (L5DLA.cnt bd + L5DLA.cnt bn)).
  { unfold L5DLA.cnt. rewrite DYD, DYNF. cbn [L5DLA.blocks_of L5DLA.adebl app] in ECR2. subst cr2'. destruct CRD as (C1 & C2). unfold L5DLA.acredits. split. exact C1. clear - C2. lia. }
  apply (G3 fx2 R2 M2' model2' [] BX2 LK2' cr2' A2 ro bd wd bn wn BI2 RI2 p19 p25 ltac:(rewrite (KS2 21%nat) by inl; exact X21) ROR ROR SZP ltac:(intros a _ rr []) TD2 TN2).
  { intros cap q Eq. exfalso. exact (NDB cap q Eq). }
  { intros cap q Eq. exfalso. exact (NDN cap q Eq). }
  { clear - LD1 LLD CAPD. lia. }
  { exact TOPD. }
  { exact TOPD63. }
  { clear - LN1 LLC CAPN. lia. }
  { exact NZN. }
  { intros cap q Eq. exfalso. exact (NDB cap q Eq). }
  { intros cap q Eq. exfalso. exact (NDN cap q Eq). }
  { intros _. split; intros X0; [rewrite DYD in X0 | rewrite DYNF in X0]; discriminate X0. }
  { intros cd qd cn qn0 Eq. exfalso. exact (NDB cd qd Eq). }
  { exact CR2. }
  intros fx3 R3 R3' M3 M3' model3 c gd gn LBn cr3 LK3 A3 KS3 AG3 POST3 BI3 IA3 ILK3.
  pose proof POST3 as (RP3 & EC & _ & _ & E10 & PX3 & _ & _ & ECR3 & _). cbv zeta in EC, E10, ECR3.
  destruct (NORM_TOBS [] BX2 M2' M3 M3' model2' LK2' cr2' A2 R3 R3' bd bn wd wn c gd gn LBn cr3 LK3 BI2 AG3 TD2 TN2 POST3)
    as (fbd' & fbn' & std & stn & TD3 & TN3 & GRD & GRN & CPD & CPN & OFF3).
  (* [comment removed for export] *)
  cbv zeta in TD3, TN3, CPD, CPN.
  set (sec := L5DLA.second (L5.bo_len bd) (L5DLA.shl_result wd c)) in *.
  set (rd := L5DLA.norm_words wd c sec) in *. set (rn := L5DLA.norm_words wn c sec) in *.
  set (BXc := L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ BX2) in *.
  assert (R19 : getr R3' (reg 19) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R3 R3' 19 RP3) by inl; rewrite (KS3 19%nat) by inl; exact p19).
  assert (R25 : getr R3' (reg 25) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R3 R3' 25 RP3) by inl; rewrite (KS3 25%nat) by inl; exact p25).
  assert (R10 : getr R3' (reg 10) = Z_to_bv 64 (if sec then 1 else 0)). { rewrite <- r10. exact E10. }
  assert (RI3 : rinvD R E R3'). { apply (rinvD_pres R E R3 R3'). apply (rinvD_ks R E R2 R3 KS_v5G3 RI2 KS3). vm_compute; reflexivity. exact RP3. }
  pose proof (proj1 TN3) as OBN3. pose proof OBN3 as (_ & _ & NL8 & OSTN). cbn [L5.bo_len L5.bo_st] in NL8, OSTN. replace (F + 96 + 8) with (F + 104) in NL8 by (clear; lia).
  assert (LNR : 0 <= Z.of_nat (rlen rn) < 2 ^ 64). { destruct stn as [v0 v1|cap q]. destruct OSTN as (_ & _ & _ & L2 & _). clear - L2; lia. destruct OSTN as (_ & _ & _ & LC & CRR & _). clear - LC CRR; lia. }
  assert (OFF23 : offx (BX2 ++ LB) L5DLA.NORM_SCR (fun a => E - 220 <= a < E - 216) M2' M3).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG3. exact Ha. exact NX. }
  assert (INWN : forall a, L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn) a -> F + 32 <= a < F + 128 \/ E - 220 <= a < E - 216).
  { intros a (rr & Hr & IR). unfold L5DLA.norm_W, L5DLA.dyn_area in Hr. unfold L5.in_rng in IR.
    destruct (L5.bo_st bd) as [? ?|cd qd] eqn:ED. 2: { exfalso. exact (NDB cd qd eq_refl). } destruct (L5.bo_st bn) as [? ?|cn qn'] eqn:EN. 2: { exfalso. exact (NDN cn qn' eq_refl). }
    cbn [app In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in IR. left; clear - IR; lia. left; clear - IR; lia. right; clear - IR; lia. }
  pose proof (offx_trans L ar FF E F _ _ _ _ _ _ _ OFF23 OFF3) as OFFN. cbv beta in OFFN.
  assert (S88_3 : L5.u64_at RSEGS M3' (E - 296) qo).
  { destruct (SPL2 (E - 296) qo ltac:(subst cells; do 2 right; left; reflexivity)) as (Hc & H1 & H2).
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX2 ++ LB) L5DLA.NORM_SCR _ M2' M3' _ _ Hc H1 H2 OFFN).
    intros i Hi [Y|Y]. clear - Y Hi; lia. destruct (INWN i Y) as [Z0|Z0]. clear - Z0 Hi SFB; lia. clear - Z0 Hi; lia. }
  apply (G4s fx3 R3' M3' model3 [] BXc LK3 cr3 A3 (if sec then 1 else 0) qo (L5.BO fbd' (rlen rd) std) (Z.of_nat (rlen rn)) BI3 RI3 R10 R19 R25 ltac:(destruct sec; clear; lia) QOR S88_3 (proj1 (proj2 (proj2 TD3))) (proj1 TD3) NL8 LNR).
  intros fx4 R4 M4 model4 BI4 RI4 KS4 p1 p10 p11 p20 p24 AG4 S264 S272 S112.
  cbn [L5.bo_len] in p11, S272, S112.
  (* [comment removed for export] *)
  set (X4 := fun a => E - 120 <= a < E - 104 \/ E - 272 <= a < E - 264).
  assert (OFF4 : offx (BXc ++ LB) L5DLA.NORM_SCR X4 M3' M4).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG4. exact Ha. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  pose proof BI3 as (B3 & _). pose proof BI2 as (B2 & _).
  assert (NOFR4 : forall o b ws a, aobj FF' o 32 -> tob (BXc ++ LB) M3' o b ws -> L5ADVEA.oreg o b a -> ~ X4 a).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BXc M3' model3 LK3 cr3 A3 o b ws a BI3 AO TO OR). subst X4; cbn beta in X0. clear - X0 HSCR; lia. }
  assert (TD4 : tob (BXc ++ LB) M4 (F + 32) (L5.BO fbd' (rlen rd) std) (firstn (rlen rd) rd)).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXc ++ LB) (BXc ++ LB) (BXc ++ LB) LK3 cr3 A3 model3 L5DLA.NORM_SCR _ M3' M4 (F + 32) _ _ B3 AOD' TD3 OFF4).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TD3)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR4 _ _ _ a AOD' TD3 OR). }
  assert (TN4 : tob (BXc ++ LB) M4 (F + 96) (L5.BO fbn' (rlen rn) stn) (firstn (rlen rn) rn)).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXc ++ LB) (BXc ++ LB) (BXc ++ LB) LK3 cr3 A3 model3 L5DLA.NORM_SCR _ M3' M4 (F + 96) _ _ B3 AON' TN3 OFF4).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN3)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR4 _ _ _ a AON' TN3 OR). }
  (* [comment removed for export] *)
  assert (XST : forall a, SPA <= a < E -> ~ (E - 220 <= a < E - 216) -> ~ X4 a -> ~ (((E - 220 <= a < E - 216) \/ L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn) a) \/ X4 a)).
  { intros a Ha N1 N4 [[Y|Y]|Y]. exact (N1 Y). 2: exact (N4 Y). destruct (INWN a Y) as [Z0|Z0]. clear - Z0 Ha SFB; lia. exact (N1 Z0). }
  assert (OFF4b : offx (BX2 ++ LB) L5DLA.NORM_SCR X4 M3' M4).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG4. exact Ha. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  pose proof (offx_trans L ar FF E F _ _ _ _ _ _ _ (offx_trans L ar FF E F _ _ _ _ _ _ _ OFF23 OFF3) OFF4b) as OFFA. cbv beta in OFFA.
  assert (SPL4 : spl E M4 cells).
  { intros a v Hin. destruct (SPL2 a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX2 ++ LB) L5DLA.NORM_SCR _ M2' M4 a v Hc H1 H2 OFFA).
    intros i Hi. apply XST. clear - Hi H1 H2; lia.
    all: subst cells X4; cbn beta; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear - Hi; lia|]); destruct Hin. }
  assert (HDR4 : L5.u64_at RSEGS M4 F 1102416563).
  { eapply L5C.u64_at_agree. 4: exact HDR2. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFFA. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA L5DLA.NORM_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia.
    intros [[Y|Y]|Y]. clear - Y Hi SFB; lia. 2: subst X4; cbn beta in Y; clear - Y Hi SFB; lia.
    destruct (INWN i Y) as [Z0|Z0]. clear - Z0 Hi; lia. clear - Z0 Hi SFB; lia. }
  assert (DSH4 : dsh M4 F 0 248 248 248 248).
  { eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH2 | exact OFFA | ]. intros j Hj [[Y|Y]|Y]; pose proof (L5ADVGO2.sh_rng L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER j Hj) as YR. clear - YR Y ER; lia. 2: subst X4; cbn beta in Y; clear - YR Y ER; lia.
    destruct (INWN j Y) as [Z0|Z0]. clear - Z0 YR FBIG; lia. clear - Z0 YR ER; lia. }
  assert (STK4 : forall o b blk, L5ADVD.obj_at M2' o b blk -> E - 216 <= o -> o + 32 <= E - 152 -> L5ADVD.obj_at M4 o b blk).
  { intros o b blk OA H1 H2. apply (L5ADVD.obj_at_agree M2' M4 o b blk OA ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia)). intros i Hi. apply OFFA. clear - Hi H1 H2 ER; lia.
    apply stack_client. destruct G as [Hk SPT SLO SHI SPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. clear - Hi H1 H2 SLO SHI SPT HSCR; lia. clear - Hi H1; lia.
    apply XST. clear - Hi H1 H2; lia. clear - Hi H1; lia. subst X4; cbn beta. clear - Hi H1 H2; lia. }
  assert (S360_4 : L5.u64_at RSEGS M4 (E - 360) F).
  { apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX2 ++ LB) L5DLA.NORM_SCR _ M2' M4 _ _ S360_2 ltac:(clear; lia) ltac:(clear; lia) OFFA).
    intros i Hi. apply XST. clear - Hi; lia. clear - Hi; lia. subst X4; cbn beta. clear - Hi; lia. }
  assert (PX4 : L5.u32_at RSEGS M4 (E - 220) c).
  { eapply L5ARED.u32_at_agree1. 4: exact PX3. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply AG4. clear - Hi ER; lia. clear - Hi; lia. clear - Hi; lia. }
  apply (KF fx4 R4 M4 model4 c gd gn bn0 bd0 fbd' fbn' std stn cr3 LK3 A3 EC BI4 RI4).
  - intros x Hx. assert (Hc : In x cs_all) by (revert Hx; apply (L5K.incl_b [18; 21; 22; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (KS4 x) by (revert Hx; apply (L5K.incl_b [18; 21; 22; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (cs_of_preserved R3 R3' x RP3 Hc). rewrite (KS3 x) by (revert Hx; apply (L5K.incl_b [18; 21; 22; 26; 27]%nat); vm_compute; reflexivity).
    apply KS2. revert Hx. apply (L5K.incl_b [18; 21; 22; 26; 27]%nat). vm_compute; reflexivity.
  - rewrite (KS4 19%nat) by inl. exact R19.
  - rewrite (KS4 25%nat) by inl. exact R25.
  - exact p1.
  - exact p10.
  - exact p11.
  - exact p20.
  - exact p24.
  - exact TD4.
  - exact TN4.
  - exact GRD.
  - exact GRN.
  - exact CPD.
  - exact CPN.
  - apply (STK4 _ _ _ ON0). clear; lia. clear; lia.
  - apply (STK4 _ _ _ OD0). clear; lia. clear; lia.
  - exact SPL4.
  - exact S360_4.
  - exact S264.
  - exact S272.
  - exact S112.
  - exact HDR4.
  - exact DSH4.
  - exact PX4.
  - destruct POST3 as (_ & _ & _ & _ & _ & _ & (std0 & stn0 & _ & OAN) & _). exact (L5ADVGO2.after_sgn M3' (F + 96) bn _ gn stn0 fbn' _ _ OAN (proj1 TN3) SGN_N).
  - rewrite ECR3, ECR2. reflexivity.
  - intros x Hx. apply IA3. apply IA2. exact Hx.
  - intros x Hx. apply ILK2. apply ILK3. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition o1_e3_goal (cr0 : credit) (qo : Z) : Prop :=
  forall (KE3 : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
                  (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z),
        L5DIA.divO1_e3A L ar LB FF cr0 M M' R R' ro qo E F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (L5DIA.ff_o FF E F3a F1b F3b F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K)
    (qx d3 d4 : Z) (W : list L5.range) (bq2 br2 bn bd bn0 bd0 : L5.bigobj) (wq2 wr2 wn wd : list Z) (cells : list (Z * Z)) (x : Z)
    (R2 : bvmap 5 word) (M2' : word -> option byte) (model2' : Model) (LKc : list fframe) (crm : credit) (Ac : list (Z * Z)),
  let BX := [(qx, 64); (d3, 8 * 8); (d4, 8 * 8)] in
  ri_inv HI LB FF LK cr0 A M (vml_of model) -> SCRD = L5DIA.DIVO_SCR -> L5OMA.stksh ar M (E - SCRD) ->
  aobj FF ro 32 -> aobj FF qo 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  (forall a, L5.outside [(ro, 32); (qo, 32)] a -> L5.outside W a) ->
  binv W BX M2' model2' LKc crm Ac -> rinvD R E R2 ->
  (getr R2 (reg 1) = Z_to_bv 64 0x934bc /\ getr R2 (reg 18) = Z_to_bv 64 SH /\ getr R2 (reg 19) = Z_to_bv 64 ro /\ getr R2 (reg 20) = Z_to_bv 64 qo /\ getr R2 (reg 22) = Z_to_bv 64 F
   /\ getr R2 (reg 24) = Z_to_bv 64 (F + 32) /\ getr R2 (reg 25) = Z_to_bv 64 (F + 96) /\ getr R2 (reg 27) = Z_to_bv 64 F) ->
  tob (BX ++ LB) M2' qo bq2 wq2 -> L5.bo_dyn bq2 = false -> tob (BX ++ LB) M2' ro br2 wr2 -> L5.bo_st br2 = L5.BDyn 8 qx ->
  trk BX M2' bn bd bn0 bd0 wn wd None cells x -> L5.bo_st bn = L5.BDyn 8 d3 -> L5.bo_st bd = L5.BDyn 8 d4 ->
  In (E - 376, 1) cells -> In (E - 360, F) cells -> In (E - 336, F) cells -> In (E - 280, F + 96) cells -> In (E - 304, F + 32) cells -> In (E - 288, ro) cells -> In (E - 296, qo) cells -> In (E - 264, ro) cells ->
  credit_le (L5OMA.adebits L cr0 3 192) crm -> credit_le crm (L5OMA.adebits L cr0 3 192) ->
  forall (fx' : FPState) R' M' model' LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
    L5DIA.unnorm_e3A L ar (BX ++ LB) FF' crm M2' M' R2 R' ro qx (L5.bo_len br2) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
    model_rt model2' model' -> incl Ac A' -> amodel_ok A' model' -> incl LK' LKc ->
    ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
    srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGO1A.

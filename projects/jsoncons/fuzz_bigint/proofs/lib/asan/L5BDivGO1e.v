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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BDivGU L5BRed L5BDivHH L5BDivHS L5BDivGE L5BDivN L5BDivO1 L5BDivGN L5BDivGK L5BRzHuge L5BDivGK2 L5BDivGK3 L5BDivO2 L5BDivGO2 L5BDivGO2b L5BDivGO2c BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsAB0 L5OpMod1V L5Cmp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5BDivGO1a.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO1E.
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
Lemma dsaves_agree (R0 : bvmap 5 word) (Ma Mb : word -> option byte) E0 : L5DIA.dsaves R0 Ma E0 -> 104 <= E0 -> E0 <= 2 ^ 64 ->
  (forall a, E0 - 104 <= a < E0 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5DIA.dsaves R0 Mb E0.
Proof.
  intros D H0 H1 AG. unfold L5DIA.dsaves in *. decompose [and] D.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros i Hi; apply AG; clear - Hi H0; lia | clear - H0; lia | clear - H1; lia]).
Qed.
Lemma in3 {T : Type} (a b c : T) l x : In x (a :: b :: c :: l) <-> In x (c :: a :: b :: l).
Proof. cbn. clear. intuition. Qed.
Lemma nodup3 (a b c : Z * Z) l : NoDup (map fst (a :: b :: c :: l)) -> NoDup (map fst (c :: a :: b :: l)).
Proof.
  intros ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. revert ND.
  apply Permutation_NoDup. apply Permutation_map. symmetry. apply (Permutation_middle [a; b] l c).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma o1_e3_ok (cr0 : credit) (qo : Z) : L5ADVGO1A.o1_e3_goal L ar HI R M model K LB FF LK A E SCRD F ro cr0 qo.
Proof.
  unfold L5ADVGO1A.o1_e3_goal.
  intros KE3 qx d3 d4 W bq2 br2 bn bd bn0 bd0 wq2 wr2 wn wd cells x R2 M2' model2' LKc crm Ac.
  intros HH0 ESCR SSH AOR AOQ APO WSUB BI RI REGS TQ DYQ TR STR TRK STN STD.
  intros IN376 IN360 IN336 IN280 IN304 IN288 IN296 IN264 CRL1 CRL2.
  intros fx' R' M' model' LB' cr' LK' A' F1 fl1 F3 fl3 F1c fl1c F1d fl1d.
  intros E3A RT3 IA3 AM3 ILK3 HH3.
  set (BX := [(qx, 64); (d3, 8 * 8); (d4, 8 * 8)]) in *.
  destruct REGS as (p1 & p18 & p19 & p20 & p22 & p24 & p25 & p27).
  pose proof TRK as (TN & TD & ON0 & OD0 & SPL & PX & HDR & DSH).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (Z2 & Z8 & Z9 & Z3 & Z4 & ZSB).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct (L5ADVHO.frame_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX M2' model2' LKc crm Ac BI HDR) as (DSV & S256 & _ & AHP2).
  assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR). assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
  edestruct L5ADVEA.obj_rng with (o := ro) as ((RR1 & RR2 & RR8) & _); try first [exact LY | exact HIok | exact BI | exact AOR'].
  edestruct L5ADVEA.obj_rng with (o := qo) as ((QR1 & QR2 & _) & _); try first [exact LY | exact HIok | exact BI | exact AOQ'].
  (* [comment removed for export] *)
  pose proof E3A as (RQ & MQ & E3C).
  assert (AHP3 : ahpres L ar (BX ++ LB) FF' SPA L5DIA.UNNORM_SCR [] M2' M'). { clear - E3C. decompose [and] E3C. assumption. }
  assert (NEST : exists e0 e1, LB' = (e0, 64) :: (e1, 64) :: (BX ++ LB) /\ cr' = adebit L (adebit L crm 64) 64).
  { destruct E3C as (_ & _ & _ & _ & _ & _ & (RN & MN & DQC) & _).
    destruct DQC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (RZ & MZ & e0 & e1 & fd0 & fn0 & fn & fden & w1 & DNC) & _).
    exists e0, e1. clear - DNC. decompose [and] DNC. split; assumption. }
  destruct NEST as (e0 & e1 & ELB' & ECR').
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) L5DIA.UNNORM_SCR [] M2' M' AHP3) as OFF3.
  assert (NW : forall a, ~ L5ADVEA.inW [] a) by (intros a (rr & [] & _)).
  pose proof G as G0. destruct G0 as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in Hk, FS2, FCEIL, FLC, FR, F8, FBIG', FLA', NCF.
  assert (USC : L5DIA.UNNORM_SCR = 5328) by reflexivity.
  assert (HSCRU : 384 + L5DIA.UNNORM_SCR <= SCRD). { rewrite ESCR. unfold L5DIA.DIVO_SCR. clear; lia. }
  assert (KST : forall a, SPA <= a < E -> M' (Z_to_bv 64 a) = M2' (Z_to_bv 64 a)).
  { intros a Ha. apply OFF3. clear - Ha ER; lia. apply stack_client. clear - Ha SLO SPC SPT HSCR; lia. rewrite USC. clear - Ha; lia. apply NW. }
  assert (KF0 : forall a, F <= a < F + 504 -> ~ (F + 24 <= a < F + 32) -> M' (Z_to_bv 64 a) = M2' (Z_to_bv 64 a)).
  { intros a Ha Hn. apply OFF3. clear - Ha FRP; lia. apply (fframe_client L ar _ FF' SPA L5DIA.UNNORM_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. split. clear - Ha; lia. exact Hn. apply NW. }
  assert (SPL3 : forall a v, L5.u64_at RSEGS M2' a v -> SPA <= a -> a + 8 <= E -> L5.u64_at RSEGS M' a v).
  { intros a v Hc H1 H2. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia. intros i Hi. apply KST. cbn in Hi. clear - Hi H1 H2; lia. }
  assert (CEL3 : forall a v, In (a, v) cells -> L5.u64_at RSEGS M' a v).
  { intros a v Hin. destruct (SPL a v Hin) as (Hc & H1 & H2). exact (SPL3 a v Hc H1 H2). }
  assert (STK3 : forall o b, L5.big_at RSEGS M2' o b -> SPA <= o -> o + 32 <= E -> L5.big_at RSEGS M' o b).
  { intros o b OB H1 H2. eapply L5C.big_at_agree. 4: exact OB. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia. intros i Hi. apply KST. cbn in Hi. clear - Hi H1 H2; lia. }
  assert (LOC3 : forall k b, L5.big_at RSEGS M2' (F + k) b -> 32 <= k -> k + 32 <= 504 -> L5.big_at RSEGS M' (F + k) b).
  { intros k b OB H1 H2. eapply L5C.big_at_agree. 4: exact OB. 2: clear - H1 FRP; lia. 2: clear - H2 FRP; lia. intros i Hi. apply KF0. cbn in Hi. clear - Hi H1 H2; lia. cbn in Hi. clear - Hi H1; lia. }
  (* [comment removed for export] *)
  assert (ARG3 : forall o b ws, aobj FF o 32 -> tob (BX ++ LB) M2' o b ws -> L5.big_at RSEGS M' o b).
  { intros o b ws AO TO. assert (AO' : aobj FF' o 32) by (apply aobj_cons; exact AO).
    edestruct L5ADVEA.obj_rng with (o := o) as ((OR1 & OR2 & _) & _); try first [exact LY | exact HIok | exact BI | exact AO'].
    eapply L5C.big_at_agree. 4: exact (proj1 TO). 2: clear - OR1; lia. 2: clear - OR2; lia. intros i Hi. cbn in Hi. apply OFF3. clear - Hi OR1 OR2; lia. 2: apply NW.
    apply (obj_client L ar _ FF' _ _ o 32 i AO'). exact Hi. }
  (* [comment removed for export] *)
  destruct OD0 as (OBD0 & KD0). destruct bd0 as [fd0 nd0 sd0]. destruct sd0 as [v0 v1|cd0 qd0]. 2:{ cbn [L5.bo_st] in KD0. discriminate KD0. }
  destruct ON0 as (OBN0 & KN0). destruct bn0 as [fn0 nn0 sn0]. destruct sn0 as [v2 v3|cn0 qn0]. 2:{ cbn [L5.bo_st] in KN0. discriminate KN0. }
  destruct bn as [fn nn sn]. cbn [L5.bo_st] in STN. subst sn. destruct bd as [fden nd sd]. cbn [L5.bo_st] in STD. subst sd.
  destruct br2 as [fbx lenX sx]. cbn [L5.bo_st L5.bo_len] in *. subst sx.
  apply (KE3 fx' R' M' model' LB' cr' LK' A' F fl F1 fl1 F3 fl3 F1c fl1c F1d fl1d qx).
  2:{ eapply L5LZ.model_rt_trans. exact B3. exact RT3. }
  2:{ intros a0 Ha0. apply IA3. apply B4. exact Ha0. }
  2: exact AM3.
  2:{ intros f0 Hf0. apply B5. apply ILK3. exact Hf0. }
  2:{ unfold L5DIA.ff_o. replace (E - 352) with (SPA + 32) by (clear; lia). exact HH3. }
  exists R2, M2', d3, d4, lenX, (BX ++ LB), crm, fbx, fd0, fn0, fn, fden, v0, v1, v2, v3, nd0, nn0, nn, nd, bq2.
  assert (UL : forall k0 v, getr R2 (reg k0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> L5DSA.U R2 (Z.of_nat k0) = v).
  { intros k0 v Hk0 Hv. exact (U_of R2 k0 v Hk0 Hv). }
  assert (SHQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416).
  { hnf in ALF. clear - FRP ALF. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  assert (SRO : 0 <= ro / 8 + 2147450880 < 2 ^ 64). { clear - RR1 RR2. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  split. { apply (UL 1%nat _ p1). clear; lia. }
  split. { apply (UL 8%nat _ Z8). exact ERG. }
  split. { apply (UL 9%nat _ Z9). clear - ER; lia. }
  split. { unfold S. apply (UL 18%nat _ p18). unfold SB. clear - SHQ; lia. }
  split. { apply (UL 19%nat _ p19). clear - RR1 RR2; lia. }
  split. { apply (UL 20%nat _ p20). clear - QR1 QR2; lia. }
  split. { apply (UL 22%nat _ p22). exact FRG. }
  split. { apply (UL 23%nat _ ZSB). unfold SB. clear; lia. }
  split. { apply (UL 24%nat _ p24). clear - FRP; lia. }
  split. { apply (UL 25%nat _ p25). clear - FRP; lia. }
  split. { apply (UL 27%nat _ p27). exact FRG. }
  split. { exact Z3. }
  split. { exact Z4. }
  split. { reflexivity. }
  split. { replace (E - 352) with (SPA + 32) by (clear; lia). exact E3A. }
  split. { apply (dsaves_agree R M2' M' E DSV). clear - ER; lia. clear - ER; lia. intros a Ha. apply KST. clear - Ha; lia. }
  split. { exact (CEL3 _ _ IN376). }
  split. { exact (CEL3 _ _ IN360). }
  split. { exact (CEL3 _ _ IN336). }
  split. { exact (CEL3 _ _ IN280). }
  split. { exact (CEL3 _ _ IN304). }
  split. { exact (CEL3 _ _ IN288). }
  split. { exact (CEL3 _ _ IN296). }
  split. { exact (CEL3 _ _ IN264). }
  split. { apply (SPL3 _ _ S256); clear; lia. }
  split. { replace (E - 216) with (SPA + 168) by (clear; lia). apply (STK3 _ _ OBD0); clear; lia. }
  split. { replace (E - 184) with (SPA + 200) by (clear; lia). apply (STK3 _ _ OBN0); clear; lia. }
  split. { apply (LOC3 96 _ (proj1 TN)); clear; lia. }
  split. { apply (LOC3 32 _ (proj1 TD)); clear; lia. }
  split. { apply (L5ADVHO.sh_div_of_dsh M' F 0 248 248 248 248 (proj1 SHQ) (proj2 SHQ)).
           eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH | exact OFF3 | ]. intros j _. apply NW. }
  split. { apply L5DSA.FRL.
           - refine (proj1 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model' F 3 _ _ fl HH2 HH3 (or_introl eq_refl) _ Hk FLC)).
             unfold L5DIA.ff_u, L5DIA.ff_q, L5DIA.ff_n, L5DIA.ff_rz. do 4 right. left. reflexivity.
           - exact FLP.
           - replace (E - 352) with (SPA + 32) by (clear; lia). rewrite ELB'.
             apply (not_client_bx L ar ((F, 3, SPA + 32) :: FF) fl ((e0, 64) :: (e1, 64) :: BX) LB).
             apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ ((e0, 64) :: (e1, 64) :: BX) LB HH3). rewrite ELB'. reflexivity. exact FLP. exact FLBIG. exact FLNC.
           - exact FLA.
           - eapply L5C.u64_at_agree. 4: exact HDR. 2: clear - FRP; lia. 2: clear - FRP; lia. intros j Hj. apply KF0. cbn in Hj. clear - Hj; lia. cbn in Hj. clear - Hj; lia. }
  split. { exact (ARG3 ro _ _ AOR TR). }
  split. { exact (ARG3 qo _ _ AOQ TQ). }
  split. { exact DYQ. }
  split.
  { (* [comment removed for export] *)
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as WF3.
    set (FFt := L5DIA.ff_u FF' SPA F1 F3 F1c F1d) in *.
    assert (ND3 : NoDup (map fst LB')). { clear - WF3. decompose [and] WF3. assumption. }
    assert (NDF3 : NoDup (map ff_addr FFt)).
    { assert (X0 : NoDup (map ff_addr (FFt ++ LK'))) by (clear - WF3; decompose [and] WF3; assumption).
      rewrite map_app in X0. apply list_relations.list.NoDup_app in X0. exact (proj1 X0). }
    rewrite ELB' in HH3, ND3. subst BX. cbn [app] in HH3, ND3.
    assert (HHq : ri_inv HI ((qx, 64) :: (e0, 64) :: (e1, 64) :: (d3, 8 * 8) :: (d4, 8 * 8) :: LB) FFt LK' cr' A' M' (vml_of model')).
    { apply (aio_perm _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ HH3). intros b. apply in3. apply nodup3. exact ND3. intros f. reflexivity. exact NDF3. }
    pose proof (L5ADH.afresh_of_inv L ar C HI HIok qx 64 _ FFt LK' cr' A' M' _ HHq) as (AF1 & AF2 & AF3 & AF4 & AF5).
    split. exact AF1. split. intros b Hb. apply AF2. do 4 right. exact Hb. split. 2: split; [exact AF4 | exact AF5].
    intros f Hf. apply AF3. apply in_or_app. left. subst FFt. unfold L5DIA.ff_u, L5DIA.ff_q, L5DIA.ff_n, L5DIA.ff_rz. do 5 right. exact Hf. }
  split.
  { rewrite ECR'. clear - CRL1. unfold credit_le, L5OMA.adebits, adebit in *. cbn [fst snd] in *. lia. }
  rewrite <- ESCR. apply ahpres_of.
  - apply (ek_W L ar LB FF E SCRD [(ro, 32); (qo, 32)] W). 2: exact WSUB.
    eapply ek_trans. exact B7. apply (ek_callee L ar LB BX FF [(F, 3, SPA + 32)] E SCRD SPA L5DIA.UNNORM_SCR W [] M2' M' AHP3).
    clear - HSCRU; lia. clear; lia. intros a _ _ rr [].
  - assert (STK3' : astk ar M' E SCRD).
    { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ (BX ++ LB) FF' M2' M2' M' E SCRD SPA L5DIA.UNNORM_SCR [] B1 B6 (mem_grows_refl M2') AHP3).
      clear - HSCRU; lia. clear; lia. clear - HSCR; lia. }
    eapply astk_defined. exact STK3'. clear; lia. clear; lia.
  - eapply dk_trans. exact B8. apply (dk_callee L ar LB BX FF [(F, 3, SPA + 32)] E SCRD SPA L5DIA.UNNORM_SCR [] M2' M' AHP3).
    clear - HSCRU; lia. clear; lia.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGO1E.

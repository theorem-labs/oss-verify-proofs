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
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivHL L5ADivHM L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB L5ADivGC L5ADivGD L5ADivGU L5ARed L5ADivHH L5ADivHS L5ADivGE L5ADivN L5ADivO1 L5ANorm L5ADivGN L5ADivGK L5ARzHuge L5ADivGK2 L5ADivGK3 L5ADivO2 L5ADivGO2 L5ADivGO2b BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO2C.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGO2. Import L5ADVGO2B. Import L5ADVGK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nth_w_firstn ws k j : (j < k)%nat -> nth_w (firstn k ws) j = nth_w ws j.
Proof. unfold nth_w. revert k j. induction ws as [|w ws IH]; intros k j Hj. rewrite firstn_nil. destruct j; reflexivity. destruct k. Lia.lia. destruct j. reflexivity. cbn. apply IH. Lia.lia. Qed.
Lemma go2_d : 2 ^ 63 <= nth_w (firstn 2 DA) (Z.to_nat 1) /\ 4 <= nth_w (firstn 2 DA) (Z.to_nat 1). Proof. vm_compute. split; intros X0; discriminate X0. Qed.
Lemma go2_vals wy : words_ok wy -> (2 <= length wy)%nat -> nth_w wy (length wy - 1) <> 0 ->
  let rn := shl_words wy 2 in let nn := rlen rn in
  (length wy <= nn <= Datatypes.S (length wy))%nat /\
  (~ (nth_w (firstn nn rn) (nn - 1) < nth_w (firstn 2 DA) (Z.to_nat 1)) -> nn = length wy).
Proof.
  intros W L2 T rn nn. pose proof (rlen_shl_bounds wy 2 W ltac:(Lia.lia) T ltac:(Lia.lia)) as B. fold rn in B. fold nn in B. split. exact B.
  intros NLT. destruct (Nat.eq_dec nn (length wy)) as [Eq|Ne]. exact Eq. exfalso. assert (EG : nn = Datatypes.S (length wy)) by Lia.lia.
  pose proof (shl_grown_top wy 2 W ltac:(Lia.lia) ltac:(Lia.lia) EG) as TOP. fold rn in TOP. fold nn in TOP.
  rewrite nth_w_firstn in NLT by Lia.lia. pose proof (proj2 go2_d) as D4. change (2 ^ 2) with 4 in TOP. Lia.lia.
Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g11_trk (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> aobj FF qo 32 -> aobj FF ro 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc ro br wr -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  (forall a, qo <= a < qo + 16 -> ~ L5.outside W a) ->
  In (E - 248, qo) cells -> In (E - 296, F) cells -> In (E - 264, F + 32) cells -> In (E - 272, F + 96) cells ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall (fx1 : FPState) R1 M1 model1 fb',
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      getr R1 (reg 18) = Z_to_bv 64 SH -> getr R1 (reg 20) = Z_to_bv 64 (F + 32) -> getr R1 (reg 21) = Z_to_bv 64 (F + 96) -> getr R1 (reg 22) = Z_to_bv 64 qo ->
      getr R1 (reg 24) = Z_to_bv 64 F -> getr R1 (reg 27) = Z_to_bv 64 F ->
      fb' = (if Nat.eqb (L5W.rlen wq) 0 then Z.land (L5.bo_fb bq) 253 else L5.bo_fb bq) ->
      tob (BX ++ LB) M1 qo (L5.BO fb' (L5W.rlen wq) (L5.bo_st bq)) (firstn (L5W.rlen wq) wq) ->
      tob (BX ++ LB) M1 ro br wr -> trk BX M1 bn bd bn0 bd0 wn wd on0 cells x ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x92a08 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x929e8 Mc modelc) K.
Proof.
  intros BI RI AOQ AOR APO TQ TR TRK WQ IN248 IN296 IN264 IN272 NQB NQNQ NQDQ KF.
  pose proof TRK as (TN & TD & _ & _ & SPL & _). pose proof BI as (B1 & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  apply (G11N fx Rc Mc modelc W BX LKc crc Ac qo bq wq BI RI AOQ TQ WQ (proj1 (SPL _ _ IN248)) (proj1 (SPL _ _ IN296)) (proj1 (SPL _ _ IN264)) (proj1 (SPL _ _ IN272))).
  intros fx1 R1 M1 model1 BI1 RI1 p18 p20 p21 p22 p24 p27 AG1 OBQ1.
  set (X := fun a => qo <= a < qo + 16 \/ SPA - 16 <= a < SPA).
  assert (OFF1 : offx (BX ++ LB) 0 X Mc M1). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  assert (AOFF : forall a, L5ADVEA.oreg qo bq a -> ~ (F <= a < F + 512) /\ ~ (SPA <= a < E)).
  { intros a OR. edestruct L5ADVEA.arg_off with (o := qo) (a := a) as (Y1 & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOQ | exact TQ | exact OR | ]. split; assumption. }
  assert (APF : forall k, 0 <= k <= 480 -> F + k + 32 <= qo \/ qo + 32 <= F + k).
  { intros k Hk. destruct (AOFF qo ltac:(left; clear; lia)) as (Y1 & _). destruct (AOFF (qo + 31) ltac:(left; clear; lia)) as (Y2 & _). clear - Hk Y1 Y2. lia. }
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ (E - SCRD <= a < E)).
  { intros o b ws a AO TO OR. exact (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o b ws a BI AO TO OR). }
  assert (FSTK : F + 512 <= E - SCRD). { destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _]. change (ff_bytes 3) with 512 in FCEIL. clear - SLO FCEIL. lia. }
  (* [comment removed for export] *)
  assert (OTHER : forall o b ws, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> (o + 32 <= qo \/ qo + 32 <= o) ->
            (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') -> forall a, L5ADVEA.oreg o b a -> ~ X a).
  { intros o b ws AO TO AP NQ a OR [X0|X0].
    - exact (OREG_DISJ W BX Mc modelc LKc crc Ac o b ws qo bq wq a BI AO TO AOQ' TQ AP NQ OR ltac:(left; clear - X0; lia)).
    - apply (NOFR o b ws a AO TO OR). clear - X0 HSCR. lia. }
  assert (TR1 : tob (BX ++ LB) M1 ro br wr).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 _ Mc M1 ro br wr B1 AOR' TR OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TR)) cap q Eq) as X0. split; exact X0. exact (OTHER ro br wr AOR' TR ltac:(clear - APO; lia) NQB). }
  assert (TRK1 : trk BX M1 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP W BX BX Mc M1 modelc LKc crc Ac 0 _ bn bd bn0 bd0 wn wd on0 cells x BI OFF1 ltac:(intros b0 Hb; exact Hb) TRK).
    - exact (OTHER (F + 96) bn wn AON' TN (APF 96 ltac:(clear; lia)) NQNQ).
    - exact (OTHER (F + 32) bd wd AOD' TD (APF 32 ltac:(clear; lia)) NQDQ).
    - intros i Hi [X0|X0]. apply (proj2 (AOFF i ltac:(left; clear - X0; lia))). clear - Hi; lia. clear - Hi X0; lia.
    - intros c v Hin i Hi [X0|X0]; destruct (SPL c v Hin) as (_ & H1 & H2). apply (proj2 (AOFF i ltac:(left; clear - X0; lia))). clear - Hi H1 H2; lia. clear - Hi X0 H1; lia.
    - intros i Hi [X0|X0]. apply (proj1 (AOFF i ltac:(left; clear - X0; lia))). clear - Hi; lia. clear - Hi X0 FSTK HSCR; lia.
    - intros j Hj [X0|X0]. 2:{ pose proof (L5ADVGO2.sh_rng L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER j Hj) as Y. clear - Y X0 ER. lia. }
      edestruct L5ADVEA.arg_off with (o := qo) (a := j) as (_ & Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOQ | exact TQ | left; clear - X0; lia | ]. exact (Y2 Hj). }
  (* [comment removed for export] *)
  pose proof TQ as (OBQ & (LQ1 & LQ2 & LQ3) & SZQ & INQ). destruct bq as [fbq lenq stq]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  pose proof (L5W.rlen_le wq) as RLE. rewrite LQ1 in RLE.
  assert (OL1 : L5C.obj_limbs RSEGS M1 (L5.BO fbq lenq stq) wq).
  { split. exact LQ1. split. exact LQ2. cbn [L5.bo_st L5.bo_len]. destruct stq as [v0 v1|cap q]. exact LQ3.
    pose proof OBQ as (_ & _ & _ & (_ & _ & _ & LC & CR0 & _ & Q1 & Q2 & _)). cbn [L5.bo_len] in LC.
    eapply (L5C.limbs_at_agree RSEGS Mc M1). 4: exact LQ3. 2: clear - Q1; lia. 2: rewrite LQ1; clear - Q2 LC CR0; lia.
    intros j Hj. rewrite LQ1 in Hj. apply OFF1. clear - Hj Q1 Q2 LC CR0; lia.
    apply (block_client L ar (BX ++ LB) FF' SPA 0 q (8 * cap) j (INQ cap q eq_refl)). clear - Hj LC; lia.
    intros [X0|X0].
    - edestruct L5ADVEA.blk_frame with (q := q) (n := 8 * cap) (o := qo) as (_ & Y & _); try first [exact LY | exact HIok | exact G | exact HSCR | exact BI]. exact (INQ cap q eq_refl).
      specialize (Y AOQ'). clear - Y X0 Hj LC. lia.
    - apply (NOFR qo (L5.BO fbq lenq (L5.BDyn cap q)) wq j AOQ' TQ). right; right. exists cap, q. split. reflexivity. clear - Hj LC; lia. clear - X0 HSCR; lia. }
  assert (SZ1 : shadow_zero M1 qo 4).
  { intros j Hj. unfold byte_at, S. rewrite (OFF1 (qo / 8 + SB + j)). exact (SZQ j Hj).
    - edestruct L5ADVEA.obj_rng with (o := qo) as ((Y1 & Y2 & _) & _); try first [exact LY | exact HIok | exact BI | exact AOQ']. unfold SB. clear - Hj Y1 Y2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      apply (aclient_narrow L ar (BX ++ LB) FF' 0 0). 2: intros X0; apply (NOFR qo _ wq (qo / 8 + SB + j) AOQ' TQ ltac:(right; left; unfold SB in *; clear - Hj; lia)); clear - X0 HSCR; lia.
      destruct (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc qo 32 0 0 B1 AOQ' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & _ & OCLSH). change (32 / 8) with 4 in OCLSH. exact (OCLSH j Hj).
    - intros [X0|X0]. destruct (shz_off_self L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo _ wq j BI AOQ' TQ Hj) as (Y & _). apply Y. clear - X0; lia.
      apply (NOFR qo _ wq (qo / 8 + SB + j) AOQ' TQ ltac:(right; left; unfold SB in *; clear - Hj; lia)). clear - X0 HSCR; lia. }
  assert (TQ1 : tob (BX ++ LB) M1 qo (L5.BO (if Nat.eqb (L5W.rlen wq) 0 then Z.land fbq 253 else fbq) (L5W.rlen wq) stq) (firstn (L5W.rlen wq) wq)).
  { split. exact OBQ1. split. 2: split; [exact SZ1 | exact INQ].
    apply (L5ANORM.obj_limbs_prefix M1 _ lenq stq wq (L5W.rlen wq)). 2: exact RLE.
    - destruct OL1 as (A1 & A2 & A3). split. exact A1. split. exact A2. exact A3.
    - destruct stq as [v0 v1|? ?]. 2: exact I. pose proof OBQ as (_ & _ & _ & (_ & _ & _ & L2 & _)). exact L2. }
  apply (KF fx1 R1 M1 model1 _ BI1 RI1 p18 p20 p21 p22 p24 p27 eq_refl TQ1 TR1 TRK1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g12_trk (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo qn rd sr sd (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 22) = Z_to_bv 64 qo -> aobj FF qo 32 -> aobj FF ro 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc ro br wr -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  ~ L5.outside W qo ->
  L5.u64_at RSEGS Mc (E - 320) sr -> 0 <= sr < 2 ^ 64 -> L5.u64_at RSEGS Mc (E - 328) (qo / 8 + 2147450880) ->
  In (E - 208, to) cells -> 0 <= to < 2 ^ 64 -> In (E - 312, qn) cells -> 0 <= qn <= 1 -> In (E - 304, rd) cells -> (rd = 0 \/ rd = 1) ->
  (rd = 1 -> 0 <= x <= 63 /\ L5.u64_at RSEGS Mc (E - 336) sd /\ 0 <= sd < 2 ^ 64) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall k, In k [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr Rc (reg k)) ->
      getr R1 (reg 19) = Z_to_bv 64 ro -> getr R1 (reg 23) = Z_to_bv 64 sr ->
      tob (BX ++ LB) M1 qo (L5.BO (Z.lor (Z.land (L5.bo_fb bq) 253) (2 * qn)) (L5.bo_len bq) (L5.bo_st bq)) wq ->
      tob (BX ++ LB) M1 ro br wr -> trk BX M1 bn bd bn0 bd0 wn wd on0 cells x ->
      (rd = 1 -> getr R1 (reg 1) = Z_to_bv 64 0x92a54 /\ getr R1 (reg 10) = Z_to_bv 64 to /\ getr R1 (reg 11) = Z_to_bv 64 ro /\ getr R1 (reg 12) = Z_to_bv 64 x /\ getr R1 (reg 13) = Z_to_bv 64 sd) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if rd =? 1 then L5DSA.UNNORM else 0x92a70) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92a08 Mc modelc) K.
Proof.
  intros BI RI X22 AOQ AOR APO TQ TR TRK WQ S320 SRR S328 IN208 TOR IN312 QNR IN304 RD RD1 NQB NQNQ NQDQ KF.
  pose proof TRK as (TN & TD & _ & _ & SPL & U172 & _). pose proof BI as (B1 & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof TQ as (OBQ & OLQ & SZQ & INQ). pose proof OBQ as (Q0 & FQR & _).
  edestruct L5ADVEA.obj_rng with (o := ro) as ((RR1 & RR2 & _) & _); try first [exact LY | exact HIok | exact BI | exact AOR'].
  apply (G12N fx Rc Mc modelc W BX LKc crc Ac to qo qn rd sr sd x (L5.bo_fb bq) BI RI X22 AOQ SZQ Q0 FQR WQ ltac:(clear - RR1 RR2; lia) S320 SRR S328
           (proj1 (SPL _ _ IN208)) TOR (proj1 (SPL _ _ IN312)) QNR (proj1 (SPL _ _ IN304)) RD).
  { intros E1. destruct (RD1 E1) as (XR & S336 & SDR). split. exact U172. split. exact XR. split. exact S336. exact SDR. }
  intros fx1 R1 M1 model1 BI1 RI1 KS1 p19 p23 AG1 U8Q REGS.
  set (X := fun a => a = qo).
  assert (OFF1 : offx (BX ++ LB) 0 X Mc M1). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. exact NX. }
  assert (AOFF : forall a, L5ADVEA.oreg qo bq a -> ~ (F <= a < F + 512) /\ ~ (SPA <= a < E)).
  { intros a OR. edestruct L5ADVEA.arg_off with (o := qo) (a := a) as (Y1 & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOQ | exact TQ | exact OR | ]. split; assumption. }
  assert (APF : forall k, 0 <= k <= 480 -> F + k + 32 <= qo \/ qo + 32 <= F + k).
  { intros k Hk. destruct (AOFF qo ltac:(left; clear; lia)) as (Y1 & _). destruct (AOFF (qo + 31) ltac:(left; clear; lia)) as (Y2 & _). clear - Hk Y1 Y2. lia. }
  assert (OTHER : forall o b ws, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> (o + 32 <= qo \/ qo + 32 <= o) ->
            (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') -> forall a, L5ADVEA.oreg o b a -> ~ X a).
  { intros o b ws AO TO AP NQ a OR X0. hnf in X0. subst a.
    exact (OREG_DISJ W BX Mc modelc LKc crc Ac o b ws qo bq wq qo BI AO TO AOQ' TQ AP NQ OR ltac:(left; clear; lia)). }
  assert (TR1 : tob (BX ++ LB) M1 ro br wr).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 _ Mc M1 ro br wr B1 AOR' TR OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TR)) cap q Eq) as X0. split; exact X0. exact (OTHER ro br wr AOR' TR ltac:(clear - APO; lia) NQB). }
  assert (TRK1 : trk BX M1 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP W BX BX Mc M1 modelc LKc crc Ac 0 _ bn bd bn0 bd0 wn wd on0 cells x BI OFF1 ltac:(intros b0 Hb; exact Hb) TRK).
    - exact (OTHER (F + 96) bn wn AON' TN (APF 96 ltac:(clear; lia)) NQNQ).
    - exact (OTHER (F + 32) bd wd AOD' TD (APF 32 ltac:(clear; lia)) NQDQ).
    - intros i Hi X0. hnf in X0. subst i. apply (proj2 (AOFF qo ltac:(left; clear; lia))). clear - Hi; lia.
    - intros c v Hin i Hi X0; destruct (SPL c v Hin) as (_ & H1 & H2). hnf in X0. subst i. apply (proj2 (AOFF qo ltac:(left; clear; lia))). clear - Hi H1 H2; lia.
    - intros i Hi X0. hnf in X0. subst i. apply (proj1 (AOFF qo ltac:(left; clear; lia))). clear - Hi; lia.
    - intros j Hj X0. hnf in X0. subst j. edestruct L5ADVEA.arg_off with (o := qo) (a := qo) as (_ & Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOQ | exact TQ | left; clear; lia | ]. exact (Y2 Hj). }
  pose proof (L5ADVEA.fb_sgn (L5.bo_fb bq) (2 * qn) FQR ltac:(clear - QNR; lia)) as (FQR' & FQT).
  assert (TQ1 : tob (BX ++ LB) M1 qo (L5.BO (Z.lor (Z.land (L5.bo_fb bq) 253) (2 * qn)) (L5.bo_len bq) (L5.bo_st bq)) wq).
  { apply (L5ADVEA.tob_keep_fb L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 X Mc M1 qo bq wq _ B1 AOQ' TQ OFF1).
    - intros cap q Eq. pose proof (INQ cap q Eq) as X0. split; exact X0.
    - intros a Ha X0. hnf in X0. clear - Ha X0. lia.
    - intros j Hj X0. hnf in X0. destruct (shz_off_self L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo _ wq j BI AOQ' TQ Hj) as (Y & _). apply Y. rewrite X0. clear; lia.
    - intros cap q a Eq Ha X0. hnf in X0. subst a.
      edestruct L5ADVEA.blk_frame with (q := q) (n := 8 * cap) (o := qo) as (_ & Y & _); try first [exact LY | exact HIok | exact G | exact HSCR | exact BI]. exact (INQ cap q Eq).
      specialize (Y AOQ'). pose proof OBQ as (_ & _ & _ & OST). rewrite Eq in OST. destruct OST as (_ & _ & _ & LC & _). clear - Y Ha LC. lia.
    - exact U8Q.
    - exact FQR'.
    - exact FQT. }
  apply (KF fx1 R1 M1 model1 BI1 RI1 KS1 p19 p23 TQ1 TR1 TRK1 REGS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unn_trk (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac qo sd (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x (Hunn : L5DIA.unnorm_specA L ar HI) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 11) = Z_to_bv 64 ro -> getr Rc (reg 12) = Z_to_bv 64 x -> 0 <= x <= 63 -> getr Rc (reg 13) = Z_to_bv 64 sd -> (sd = 0 \/ sd = 1) ->
  getr Rc (reg 1) = Z_to_bv 64 0x92a54 ->
  352 + L5DIA.UNNORM_SCR <= SCRD -> SCRD mod 8 = 0 -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 ->
  L5OMA.stksh ar M (E - SCRD) -> (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  aobj FF qo 32 -> aobj FF ro 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc ro br wr -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  (1 <= L5.bo_len br <= 299)%nat -> Z.testbit (L5.bo_fb br) 1 = false ->
  (sd = 1 -> exists qX, L5.bo_st br = L5.BDyn 8 qX /\ (2 <= L5.bo_len br <= 6)%nat) ->
  (sd = 1 -> L5OMA.acredit_for L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32); (L5.bo_data ro br, 8 * L5.bo_cap br)] a) ->
  (forall c q c' q', L5.bo_st bq = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall (fx' : FPState) R' M' model' cr' LK' A' fb' n' st' w',
      regs_preserved Rc R' -> binv W1 BX M' model' LK' cr' A' -> incl Ac A' -> incl LK' LKc ->
      tob (BX ++ LB) M' ro (L5.BO fb' n' st') w' -> Z.testbit fb' 1 = false -> L5ADVEA.same_store br st' ->
      L5OMA.acredit_after L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES cr' ->
      tob (BX ++ LB) M' qo bq wq -> trk BX M' bn bd bn0 bd0 wn wd on0 cells x ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x92a54 M' model') K) ->
  (forall (fx' : FPState) R' M' model' qX LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
      sd = 1 -> L5.bo_st br = L5.BDyn 8 qX ->
      L5DIA.unnorm_e3A L ar (BX ++ LB) FF' crc Mc M' Rc R' ro qX (L5.bo_len br) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt modelc model' -> incl Ac A' -> amodel_ok A' model' -> incl LK' LKc ->
      ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc L5DSA.UNNORM Mc modelc) K.
Proof.
  intros BI RI X11 X12 XR X13 SD X1 USCR SCR8 FFR5 FFR3 SSH WSH AOQ AOR APO TQ TR TRK LENR SGR SD1 CRD1 WSUB NQB NQNR NQDR KF KE3.
  pose proof BI as (B1 & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  pose proof TR as (OBR & OLR & SZR & INR).
  apply (L5ADVGU.unnorm_stage L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR FFR1 FFRS fx Rc Mc modelc W W1 BX LKc crc Ac x sd br wr Hunn
           BI RI X11 X12 XR X13 SD X1 USCR SCR8 FFR5 FFR3 SSH WSH OBR OLR LENR SGR AOR SZR INR SD1 CRD1 WSUB).
  2: exact KE3.
  intros fx' R' M' model' cr' LK' A' (RP & (fb' & n' & st' & w' & OB' & OL' & SG' & ST') & CRA & AH) BI' IA' ILK'.
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F _ _ _ _ _ AH) as OFF0.
  assert (OFF1 : offx (BX ++ LB) L5DIA.UNNORM_SCR (L5ADVEA.oreg ro br) Mc M').
  { apply (OFFX_WEAKEN _ _ _ _ _ _ OFF0). intros a (rr & [E1|[E1|[]]] & IR); subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    - left. exact IR.
    - unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st br) as [v0 v1|cap q] eqn:Eq. left. clear - IR; lia. right; right. exists cap, q. split. exact Eq. exact IR. }
  assert (TQ1 : tob (BX ++ LB) M' qo bq wq).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc _ _ Mc M' qo bq wq B1 AOQ' TQ OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TQ)) cap q Eq) as X0. split; exact X0.
    intros a OQ OR. exact (OREG_DISJ W BX Mc modelc LKc crc Ac qo bq wq ro br wr a BI AOQ' TQ AOR' TR APO NQB OQ OR). }
  assert (TRK1 : trk BX M' bn bd bn0 bd0 wn wd on0 cells x).
  { exact (TRK_KEEP_ARG W BX BX Mc M' modelc LKc crc Ac _ ro br wr bn bd bn0 bd0 wn wd on0 cells x BI AOR TR OFF1 ltac:(intros b0 Hb; exact Hb) TRK NQNR NQDR). }
  assert (SST : L5ADVEA.same_store br st'). { unfold L5ADVEA.same_store. destruct (L5.bo_st br) as [v0 v1|cap q]; destruct st' as [u0 u1|cap' q']; exact ST'. }
  assert (SZ1 : shadow_zero M' ro 4).
  { apply (L5ADVEA.shz_keep L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) LKc crc Ac modelc _ _ Mc M' ro B1 AOR' SZR OFF0).
    intros j Hj (rr & [E1|[E1|[]]] & IR); subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR;
      destruct (shz_off_self L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro _ wr j BI AOR' TR Hj) as (Y1 & Y2).
    - apply Y1. exact IR.
    - unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st br) as [v0 v1|cap q] eqn:Eq. apply Y1. clear - IR; lia. exact (Y2 cap q eq_refl IR). }
  assert (TR1 : tob (BX ++ LB) M' ro (L5.BO fb' n' st') w').
  { split. exact OB'. split. exact OL'. split. exact SZ1. cbn [L5.bo_st]. intros cap q Eq. subst st'. unfold L5ADVEA.same_store in SST. destruct (L5.bo_st br) as [v0 v1|cap0 q0] eqn:Eq0. destruct SST.
    destruct SST as (-> & ->). exact (INR cap0 q0 eq_refl). }
  exact (KF fx' R' M' model' cr' LK' A' fb' n' st' w' RP BI' IA' ILK' TR1 SG' SST CRA TQ1 TRK1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g13_trk (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo bits (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 19) = Z_to_bv 64 ro -> getr Rc (reg 23) = Z_to_bv 64 (ro / 8 + 2147450880) ->
  aobj FF qo 32 -> aobj FF ro 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc ro br wr -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  ~ L5.outside W ro -> In (E - 288, bits) cells -> (bits = 0 \/ bits = 2) ->
  (forall c q c' q', L5.bo_st bq = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      (forall k, In k [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr Rc (reg k)) ->
      tob (BX ++ LB) M1 ro (L5.BO (Z.lor (Z.land (L5.bo_fb br) 253) bits) (L5.bo_len br) (L5.bo_st br)) wr ->
      tob (BX ++ LB) M1 qo bq wq -> trk BX M1 bn bd bn0 bd0 wn wd on0 cells x ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x92a70 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92a54 Mc modelc) K.
Proof.
  intros BI RI X19 X23 AOQ AOR APO TQ TR TRK WR IN288 BITS NQB NQNR NQDR KF.
  pose proof TRK as (TN & TD & _ & _ & SPL & _). pose proof BI as (B1 & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof TR as (OBR & OLR & SZR & INR). pose proof OBR as (R0 & FRR & _).
  apply (G13N fx Rc Mc modelc W BX LKc crc Ac bits (L5.bo_fb br) BI RI X19 X23 AOR SZR R0 FRR WR (proj1 (SPL _ _ IN288)) ltac:(clear - BITS; lia)).
  intros fx1 R1 M1 model1 BI1 RI1 KS1 AG1 U8R.
  set (X := fun a => a = ro).
  assert (OFF1 : offx (BX ++ LB) 0 X Mc M1). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. exact NX. }
  assert (AOFF : forall a, L5ADVEA.oreg ro br a -> ~ (F <= a < F + 512) /\ ~ (SPA <= a < E)).
  { intros a OR. edestruct L5ADVEA.arg_off with (o := ro) (a := a) as (Y1 & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOR | exact TR | exact OR | ]. split; assumption. }
  assert (APF : forall k, 0 <= k <= 480 -> F + k + 32 <= ro \/ ro + 32 <= F + k).
  { intros k Hk. destruct (AOFF ro ltac:(left; clear; lia)) as (Y1 & _). destruct (AOFF (ro + 31) ltac:(left; clear; lia)) as (Y2 & _). clear - Hk Y1 Y2. lia. }
  assert (OTHER : forall o b ws, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> (o + 32 <= ro \/ ro + 32 <= o) ->
            (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> forall a, L5ADVEA.oreg o b a -> ~ X a).
  { intros o b ws AO TO AP NQ a OR X0. hnf in X0. subst a.
    exact (OREG_DISJ W BX Mc modelc LKc crc Ac o b ws ro br wr ro BI AO TO AOR' TR AP NQ OR ltac:(left; clear; lia)). }
  assert (TQ1 : tob (BX ++ LB) M1 qo bq wq).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 _ Mc M1 qo bq wq B1 AOQ' TQ OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TQ)) cap q Eq) as X0. split; exact X0. exact (OTHER qo bq wq AOQ' TQ APO NQB). }
  assert (TRK1 : trk BX M1 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP W BX BX Mc M1 modelc LKc crc Ac 0 _ bn bd bn0 bd0 wn wd on0 cells x BI OFF1 ltac:(intros b0 Hb; exact Hb) TRK).
    - exact (OTHER (F + 96) bn wn AON' TN (APF 96 ltac:(clear; lia)) NQNR).
    - exact (OTHER (F + 32) bd wd AOD' TD (APF 32 ltac:(clear; lia)) NQDR).
    - intros i Hi X0. hnf in X0. subst i. apply (proj2 (AOFF ro ltac:(left; clear; lia))). clear - Hi; lia.
    - intros c v Hin i Hi X0; destruct (SPL c v Hin) as (_ & H1 & H2). hnf in X0. subst i. apply (proj2 (AOFF ro ltac:(left; clear; lia))). clear - Hi H1 H2; lia.
    - intros i Hi X0. hnf in X0. subst i. apply (proj1 (AOFF ro ltac:(left; clear; lia))). clear - Hi; lia.
    - intros j Hj X0. hnf in X0. subst j. edestruct L5ADVEA.arg_off with (o := ro) (a := ro) as (_ & Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOR | exact TR | left; clear; lia | ]. exact (Y2 Hj). }
  pose proof (L5ADVEA.fb_sgn (L5.bo_fb br) bits FRR BITS) as (FRR' & FRT).
  assert (TR1 : tob (BX ++ LB) M1 ro (L5.BO (Z.lor (Z.land (L5.bo_fb br) 253) bits) (L5.bo_len br) (L5.bo_st br)) wr).
  { apply (L5ADVEA.tob_keep_fb L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 X Mc M1 ro br wr _ B1 AOR' TR OFF1).
    - intros cap q Eq. pose proof (INR cap q Eq) as X0. split; exact X0.
    - intros a Ha X0. hnf in X0. clear - Ha X0. lia.
    - intros j Hj X0. hnf in X0. destruct (shz_off_self L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro _ wr j BI AOR' TR Hj) as (Y & _). apply Y. rewrite X0. clear; lia.
    - intros cap q a Eq Ha X0. hnf in X0. subst a.
      edestruct L5ADVEA.blk_frame with (q := q) (n := 8 * cap) (o := ro) as (_ & Y & _); try first [exact LY | exact HIok | exact G | exact HSCR | exact BI]. exact (INR cap q Eq).
      specialize (Y AOR'). pose proof OBR as (_ & _ & _ & OST). rewrite Eq in OST. destruct OST as (_ & _ & _ & LC & _). clear - Y Ha LC. lia.
    - exact U8R.
    - exact FRR'.
    - exact FRT. }
  apply (KF fx1 R1 M1 model1 BI1 RI1 KS1 TR1 TQ1 TRK1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blk_of (b : L5.bigobj) : option (Z * Z) := match L5.bo_st b with L5.BInl _ _ => None | L5.BDyn cap q => Some (q, 8 * cap) end.
Lemma obj_at_blk Mk o b : L5.big_at RSEGS Mk o b -> L5ADVD.obj_at Mk o b (blk_of b).
Proof. intros OB. split. exact OB. unfold blk_of. destruct (L5.bo_st b); reflexivity. Qed.
Lemma in_lb_remove_inv q (b : Z * Z) l : In b (lb_remove q l) -> In b l.
Proof. induction l as [|c l IH]; cbn [lb_remove]. intros []. destruct (Z.eqb (fst c) q). intros H; right; exact H. intros [->|H]. left; reflexivity. right; exact (IH H). Qed.
Lemma lb_remove_app q (l1 l2 : list (Z * Z)) : ~ In q (map fst l1) -> lb_remove q (l1 ++ l2) = l1 ++ lb_remove q l2.
Proof.
  induction l1 as [|c l1 IH]; intros NI. reflexivity. cbn [app lb_remove]. destruct (Z.eqb_spec (fst c) q) as [Eq|Ne]. exfalso. apply NI. left. exact Eq.
  f_equal. apply IH. intros X0. apply NI. right. exact X0.
Qed.
Lemma aclient_sub LBa LBb FFx sp scr a : (forall b, In b LBa -> In b LBb) -> aclient L ar LBa FFx sp scr a -> aclient L ar LBb FFx sp scr a.
Proof.
  intros SUB X0. unfold aclient, aclient_g in *. destruct X0 as [X0|[X0|[X0|[X0|[X0|[X0|X0]]]]]].
  - left. destruct X0 as (b & Hb & Y). exists b. split. exact (SUB b Hb). exact Y.
  - right; left; exact X0.
  - right; right; left; exact X0.
  - right; right; right; left; exact X0.
  - right; right; right; right; left; exact X0.
  - right; right; right; right; right; left; exact X0.
  - right; right; right; right; right; right. destruct X0 as (b & Hb & Y). exists b. split. exact (SUB b Hb). exact Y.
Qed.

Lemma g14_fin (fx : FPState) Rc Mc modelc W BX BX2 BX3 BXf LKc crc Ac qo (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x :
  binv W BX Mc modelc LKc crc Ac -> L5ADVD.rinvTL R E F Rc -> aobj FF qo 32 -> aobj FF ro 32 ->
  tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc ro br wr -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  match on0 with None => BX2 = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BX2 ++ LB end ->
  match blk_of bn with None => BX3 = BX2 | Some (q, n) => In (q, n) (BX2 ++ LB) /\ lb_remove q (BX2 ++ LB) = BX3 ++ LB end ->
  match blk_of bd with None => BXf = BX3 | Some (q, n) => In (q, n) (BX3 ++ LB) /\ lb_remove q (BX3 ++ LB) = BXf ++ LB end ->
  (forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) -> (forall cap q, L5.bo_st br = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) ->
  (forall (fxf : FPState) Rf Mf modelf Af,
      regs_preserved R Rf -> incl Ac Af -> ahpres L ar LB FF E SCRD W M Mf ->
      L5.big_at RSEGS Mf qo bq -> L5C.obj_limbs RSEGS Mf bq wq -> L5.big_at RSEGS Mf ro br -> L5C.obj_limbs RSEGS Mf br wr ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI (BXf ++ LB) FF LKc crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92a70 Mc modelc) K.
Proof.
  intros BI RI AOQ AOR TQ TR TRK L2 L3 Lf INQf INRf KF.
  pose proof TRK as (TN & TD & ON0 & OD0 & _). pose proof BI as (B1 & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (SUB2 : forall b, In b (BX2 ++ LB) -> In b (BX ++ LB)). { destruct on0 as [[q n]|]. destruct L2 as (_ & <-). intros b. apply in_lb_remove_inv. subst BX2. intros b Hb; exact Hb. }
  assert (SUB3 : forall b, In b (BX3 ++ LB) -> In b (BX2 ++ LB)). { destruct (blk_of bn) as [[q n]|]. destruct L3 as (_ & <-). intros b. apply in_lb_remove_inv. subst BX3. intros b Hb; exact Hb. }
  assert (SUBf : forall b, In b (BXf ++ LB) -> In b (BX3 ++ LB)). { destruct (blk_of bd) as [[q n]|]. destruct Lf as (_ & <-). intros b. apply in_lb_remove_inv. subst BXf. intros b Hb; exact Hb. }
  apply (G14N fx Rc Mc modelc W BX BX BX2 LKc crc Ac bd0 None bn0 on0 BI RI OD0 ON0 eq_refl L2).
  { intros a. apply aclient_sub. exact SUB2. }
  intros fx' R' M' model' A' BI' RI' IA' AG'. pose proof BI' as (B1' & _).
  assert (OFF1 : offx (BX2 ++ LB) OPDEL_SCR (fun _ => False) Mc M'). { intros a Ha Hc _. apply AG'; assumption. }
  assert (KP1 : forall o b ws, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX2 ++ LB)) -> tob (BX2 ++ LB) M' o b ws).
  { intros o b ws AO TO INO. apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX2 ++ LB) (BX ++ LB) (BX2 ++ LB) LKc crc Ac modelc _ _ Mc M' o b ws B1 AO TO OFF1).
    intros cap q Eq. split; exact (INO cap q Eq). intros a _ []. }
  pose proof (KP1 qo bq wq AOQ' TQ ltac:(intros cap q Eq; exact (SUB3 _ (SUBf _ (INQf cap q Eq))))) as TQ'.
  pose proof (KP1 ro br wr AOR' TR ltac:(intros cap q Eq; exact (SUB3 _ (SUBf _ (INRf cap q Eq))))) as TR'.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (LOC : forall k b blk, 32 <= k -> k + 32 <= 504 -> k mod 8 = 0 -> L5ADVD.obj_at Mc (F + k) b blk -> L5ADVD.obj_at M' (F + k) b blk).
  { intros k b blk K1 K2 K8 OA. apply (L5ADVD.obj_at_agree Mc M' _ _ _ OA ltac:(clear - FRP K1; lia) ltac:(clear - FRP K2; lia)). intros i Hi. apply AG'. clear - Hi FRP K1 K2; lia.
    apply (obj_client L ar (BX2 ++ LB) FF' SPA OPDEL_SCR (F + k) 32 i). eapply L5ADVEA.loc_aobj; [exact G | exact K1 | exact K2 | exact K8]. exact Hi. }
  pose proof (LOC 96 bn _ ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) (obj_at_blk Mc _ _ (proj1 TN))) as ON'.
  pose proof (LOC 32 bd _ ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) (obj_at_blk Mc _ _ (proj1 TD))) as OD'.
  apply (L5ADVD.div_dtors L ar C HI LY HIok Hdel R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK RA UR1 G2 G4 ltac:(clear - HSCR; lia) fx' R' M' model' W BX2 BX3 BXf LKc crc A' bn (blk_of bn) bd (blk_of bd) BI' RI' ON' OD' L3 Lf).
  { intros a. apply aclient_sub. exact SUBf. }
  intros fxf Rf Mf modelf Af RPf IAf AHf AGf RTf AMf HHf.
  set (X := fun a => L5AFK.Wret F fl 3 a \/ (F / 8 + SB + 12 <= a < F / 8 + SB + 16)).
  assert (OFF2 : offx (BXf ++ LB) OPDEL_SCR X M' Mf). { intros a Ha Hc NX. apply AGf. exact Ha. exact Hc. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  assert (KP2 : forall o b ws, aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> tob (BX2 ++ LB) M' o b ws -> (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) -> tob (BXf ++ LB) Mf o b ws).
  { intros o b ws AO TO TO' INO. apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXf ++ LB) (BX2 ++ LB) (BXf ++ LB) LKc crc A' model' _ _ M' Mf o b ws B1' (aobj_cons _ _ _ _ AO) TO' OFF2).
    intros cap q Eq. split; exact (INO cap q Eq).
    intros a OR. edestruct L5ADVEA.arg_off with (o := o) (a := a) as (Y1 & Y2 & _ & Y4); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AO | exact TO | exact OR | ].
    subst X. cbn beta. unfold L5AFK.Wret. change (ff_bytes 3 / 8) with 64. unfold SB in *. clear - Y1 Y2 Y4. lia. }
  pose proof (KP2 qo bq wq AOQ TQ TQ' INQf) as (OBQf & OLQf & _). pose proof (KP2 ro br wr AOR TR TR' INRf) as (OBRf & OLRf & _).
  exact (KF fxf Rf Mf modelf Af RPf (incl_tran IA' IAf) AHf OBQf OLQf OBRf OLRf RTf AMf HHf).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gT_u (fx : FPState) Rc Mc modelc W W1 BX BX2 BX3 BXf LKc crc Ac qo qn bits sd (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x (Hunn : L5DIA.unnorm_specA L ar HI) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> aobj FF qo 32 -> aobj FF ro 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc ro br wr -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  (forall a, qo <= a < qo + 16 -> ~ L5.outside W a) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32); (L5.bo_data ro br, 8 * L5.bo_cap br)] a) ->
  In (E - 248, qo) cells -> In (E - 296, F) cells -> In (E - 264, F + 32) cells -> In (E - 272, F + 96) cells ->
  In (E - 208, ro) cells -> In (E - 312, qn) cells -> 0 <= qn <= 1 -> In (E - 304, 1) cells -> In (E - 288, bits) cells -> (bits = 0 \/ bits = 2) ->
  In (E - 320, ro / 8 + 2147450880) cells -> In (E - 328, qo / 8 + 2147450880) cells -> In (E - 336, sd) cells -> (sd = 0 \/ sd = 1) -> 0 <= x <= 63 ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') ->
  352 + L5DIA.UNNORM_SCR <= SCRD -> SCRD mod 8 = 0 -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 ->
  L5OMA.stksh ar M (E - SCRD) -> (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (1 <= L5.bo_len br <= 299)%nat -> Z.testbit (L5.bo_fb br) 1 = false ->
  (sd = 1 -> exists qX, L5.bo_st br = L5.BDyn 8 qX /\ (2 <= L5.bo_len br <= 6)%nat) ->
  (sd = 1 -> L5OMA.acredit_for L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES) ->
  match on0 with None => BX2 = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BX2 ++ LB end ->
  match blk_of bn with None => BX3 = BX2 | Some (q, n) => In (q, n) (BX2 ++ LB) /\ lb_remove q (BX2 ++ LB) = BX3 ++ LB end ->
  match blk_of bd with None => BXf = BX3 | Some (q, n) => In (q, n) (BX3 ++ LB) /\ lb_remove q (BX3 ++ LB) = BXf ++ LB end ->
  (forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) -> (forall cap q, L5.bo_st br = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) ->
  (forall (fxf : FPState) Rf Mf modelf Af crf LKf fbq' fb' n' st' w',
      regs_preserved R Rf -> incl Ac Af -> ahpres L ar LB FF E SCRD W1 M Mf ->
      L5.big_at RSEGS Mf qo (L5.BO fbq' (L5W.rlen wq) (L5.bo_st bq)) -> L5C.obj_limbs RSEGS Mf (L5.BO fbq' (L5W.rlen wq) (L5.bo_st bq)) (firstn (L5W.rlen wq) wq) ->
      L5.big_at RSEGS Mf ro (L5.BO (Z.lor (Z.land fb' 253) bits) n' st') -> L5C.obj_limbs RSEGS Mf (L5.BO (Z.lor (Z.land fb' 253) bits) n' st') w' ->
      Z.testbit fb' 1 = false -> L5ADVEA.same_store br st' ->
      L5OMA.acredit_after L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES crf -> incl LKf LKc ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI (BXf ++ LB) FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  (forall (fx2 : FPState) R2 M2' model2' bq2,
      binv W BX M2' model2' LKc crc Ac -> rinvD R E R2 ->
      (getr R2 (reg 1) = Z_to_bv 64 0x92a54 /\ getr R2 (reg 18) = Z_to_bv 64 SH /\ getr R2 (reg 19) = Z_to_bv 64 ro /\ getr R2 (reg 20) = Z_to_bv 64 (F + 32) /\ getr R2 (reg 21) = Z_to_bv 64 (F + 96) /\ getr R2 (reg 22) = Z_to_bv 64 qo /\ getr R2 (reg 23) = Z_to_bv 64 (ro / 8 + 2147450880) /\ getr R2 (reg 24) = Z_to_bv 64 F /\ getr R2 (reg 27) = Z_to_bv 64 F) ->
      L5.bo_st bq2 = L5.bo_st bq ->
      tob (BX ++ LB) M2' qo bq2 (firstn (L5W.rlen wq) wq) -> tob (BX ++ LB) M2' ro br wr -> trk BX M2' bn bd bn0 bd0 wn wd on0 cells x ->
      forall (fx' : FPState) R' M' model' qX LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
      sd = 1 -> L5.bo_st br = L5.BDyn 8 qX ->
      L5DIA.unnorm_e3A L ar (BX ++ LB) FF' crc M2' M' R2 R' ro qX (L5.bo_len br) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model2' model' -> incl Ac A' -> amodel_ok A' model' -> incl LK' LKc ->
      ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x929e8 Mc modelc) K.
Proof.
  intros BI RI AOQ AOR APO TQ TR TRK WQ WSUB IN248 IN296 IN264 IN272 IN208 IN312 QNR IN304 IN288 BITS S320 S328 S336 SD XR NQB NQNQ NQDQ NQNR NQDR USCR SCR8 FFR5 FFR3 SSH WSH LENR SGR SD1 CRD1 L2 L3 Lf INQf INRf KF KE3.
  edestruct L5ADVEA.obj_rng with (o := ro) as ((RR1 & RR2 & RR8) & _); try first [exact LY | exact HIok | exact BI | apply aobj_cons; exact AOR].
  edestruct L5ADVEA.obj_rng with (o := qo) as ((QR1 & QR2 & QR8) & _); try first [exact LY | exact HIok | exact BI | apply aobj_cons; exact AOQ].
  assert (NBQ : forall c q c' q', L5.bo_st bq = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q'). { intros c q c' q' E1 E2 X0. exact (NQB c' q' c q E2 E1 (eq_sym X0)). }
  apply (g11_trk fx Rc Mc modelc W BX LKc crc Ac qo bq br bn bd bn0 bd0 wq wr wn wd on0 cells x BI RI AOQ AOR APO TQ TR TRK WQ IN248 IN296 IN264 IN272 NQB NQNQ NQDQ).
  intros fx1 R1 M1 model1 fb1 BI1 RI1 p18 p20 p21 p22 p24 p27 EFB TQ1 TR1 TRK1.
  set (bq1 := L5.BO fb1 (L5W.rlen wq) (L5.bo_st bq)) in *.
  pose proof TRK1 as (_ & _ & _ & _ & SPL1 & _).
  apply (g12_trk fx1 R1 M1 model1 W BX LKc crc Ac ro qo qn 1 (ro / 8 + 2147450880) sd bq1 br bn bd bn0 bd0 _ wr wn wd on0 cells x BI1 RI1 p22 AOQ AOR APO TQ1 TR1 TRK1
           ltac:(apply WQ; clear; lia) (proj1 (SPL1 _ _ S320)) ltac:(unfold SB in *; clear - RR1 RR2; lia) (proj1 (SPL1 _ _ S328)) IN208 ltac:(clear - RR1 RR2; lia) IN312 QNR IN304 ltac:(right; reflexivity)
           ltac:(intros _; split; [exact XR | split; [exact (proj1 (SPL1 _ _ S336)) | clear - SD; lia]]) NQB NQNQ NQDQ).
  intros fx2 R2 M2' model2' BI2 RI2 KS2 q19 q23 TQ2 TR2 TRK2 REGS. change (1 =? 1) with true in REGS |- *. cbn iota. destruct (REGS eq_refl) as (q1 & q10 & q11 & q12 & q13).
  set (bq2 := L5.BO (Z.lor (Z.land (L5.bo_fb bq1) 253) (2 * qn)) (L5.bo_len bq1) (L5.bo_st bq1)) in *.
  assert (ST2 : L5.bo_st bq2 = L5.bo_st bq) by reflexivity.
  apply (unn_trk fx2 R2 M2' model2' W W1 BX LKc crc Ac qo sd bq2 br bn bd bn0 bd0 _ wr wn wd on0 cells x Hunn BI2 RI2 q11 q12 XR q13 SD q1 USCR SCR8 FFR5 FFR3 SSH WSH AOQ AOR APO TQ2 TR2 TRK2 LENR SGR SD1 CRD1 WSUB).
  { rewrite ST2. exact NBQ. } { exact NQNR. } { exact NQDR. }
  2: { refine (KE3 fx2 R2 M2' model2' bq2 BI2 RI2 _ ST2 TQ2 TR2 TRK2). rewrite (KS2 18%nat), (KS2 20%nat), (KS2 21%nat), (KS2 22%nat), (KS2 24%nat), (KS2 27%nat) by inl. split. exact q1. split. exact p18. split. exact q19. split. exact p20. split. exact p21. split. exact p22. split. exact q23. split. exact p24. exact p27. }
  intros fx3 R3 M3 model3 cr3 LK3 A3 fb' n' st' w' RP3 BI3 IA3 ILK3 TR3 SG3 SST3 CRA3 TQ3 TRK3.
  set (br3 := L5.BO fb' n' st') in *.
  assert (KR3 : forall k, In k [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k) = getr R2 (reg k)). { intros k Hk. apply (cs_of_preserved R2 R3 k RP3). revert Hk. apply (L5K.incl_b); vm_compute; reflexivity. }
  assert (NX3 : forall (b : L5.bigobj), (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st br3 = L5.BDyn c' q' -> q <> q').
  { intros b NQ c q c' q' E1 E2. cbn [br3 L5.bo_st] in E2. subst st'. unfold L5ADVEA.same_store in SST3. destruct (L5.bo_st br) as [v0 v1|c0 q0] eqn:Eq0. destruct SST3. destruct SST3 as (-> & ->). exact (NQ c q c0 q0 E1 eq_refl). }
  assert (WR : ~ L5.outside W1 ro). { intros OUT. apply (proj2 (WSUB ro OUT) (ro, 32)). left; reflexivity. unfold L5.in_rng. cbn [fst snd]. clear; lia. }
  apply (g13_trk fx3 R3 M3 model3 W1 BX LK3 cr3 A3 qo bits bq2 br3 bn bd bn0 bd0 _ w' wn wd on0 cells x BI3 (rinvD_pres R E R2 R3 RI2 RP3)
           ltac:(rewrite (KR3 19%nat) by inl; exact q19) ltac:(rewrite (KR3 23%nat) by inl; exact q23) AOQ AOR APO TQ3 TR3 TRK3 WR IN288 BITS).
  { apply NX3. rewrite ST2. exact NBQ. } { apply NX3. exact NQNR. } { apply NX3. exact NQDR. }
  intros fx4 R4 M4 model4 BI4 RI4 KS4 TR4 TQ4 TRK4.
  set (br4 := L5.BO (Z.lor (Z.land (L5.bo_fb br3) 253) bits) (L5.bo_len br3) (L5.bo_st br3)) in *.
  assert (RT4 : L5ADVD.rinvTL R E F R4).
  { split. exact RI4. rewrite !KS4 by inl. rewrite !KR3 by inl. rewrite !KS2 by inl. split. exact p18. split. exact p20. split. exact p21. split. exact p24. exact p27. }
  apply (g14_fin fx4 R4 M4 model4 W1 BX BX2 BX3 BXf LK3 cr3 A3 qo bq2 br4 bn bd bn0 bd0 _ w' wn wd on0 cells x BI4 RT4 AOQ AOR TQ4 TR4 TRK4 L2 L3 Lf).
  { rewrite ST2. exact INQf. }
  { intros cap q Eq. cbn [br4 br3 L5.bo_st] in Eq. subst st'. unfold L5ADVEA.same_store in SST3. destruct (L5.bo_st br) as [v0 v1|c0 q0] eqn:Eq0. destruct SST3. destruct SST3 as (-> & ->). exact (INRf c0 q0 eq_refl). }
  intros fxf Rf Mf modelf Af RPf IAf AHf OBQf OLQf OBRf OLRf RTf AMf HHf.
  exact (KF fxf Rf Mf modelf Af cr3 LK3 _ fb' n' st' w' RPf (incl_tran IA3 IAf) AHf OBQf OLQf OBRf OLRf SG3 SST3 CRA3 ILK3 RTf AMf HHf).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition skind (st : L5.bstore) : option (Z * Z) := match st with L5.BInl _ _ => None | L5.BDyn cap q => Some (cap, q) end.
Lemma skind_same b st' : L5ADVEA.same_store b st' -> skind st' = skind (L5.bo_st b).
Proof. unfold L5ADVEA.same_store, skind. destruct (L5.bo_st b) as [v0 v1|cap q]; destruct st' as [u0 u1|cap' q']; intros X0; try (exact (False_ind _ X0)); try reflexivity. destruct X0 as (-> & ->). reflexivity. Qed.
Lemma skind_dyn st cap q : skind st = Some (cap, q) <-> st = L5.BDyn cap q.
Proof. unfold skind. destruct st as [v0 v1|c0 q0]; split; intros X0; try discriminate X0. injection X0 as -> ->. reflexivity. injection X0 as -> ->. reflexivity. Qed.
Lemma blk_of_skind b : blk_of b = match skind (L5.bo_st b) with None => None | Some (cap, q) => Some (q, 8 * cap) end.
Proof. unfold blk_of, skind. destruct (L5.bo_st b); reflexivity. Qed.
Lemma lift_rm (Btop Bx By : list (Z * Z)) (on : option (Z * Z)) :
  (forall b, In b (Bx ++ LB) -> ~ In (fst b) (map fst Btop)) ->
  match on with None => By = Bx | Some (q, n) => In (q, n) Bx /\ lb_remove q (Bx ++ LB) = By ++ LB end ->
  match on with None => Btop ++ By = Btop ++ Bx | Some (q, n) => In (q, n) ((Btop ++ Bx) ++ LB) /\ lb_remove q ((Btop ++ Bx) ++ LB) = (Btop ++ By) ++ LB end.
Proof.
  intros NI. destruct on as [[q n]|]. 2: intros ->; reflexivity. intros (Hin & Eq). split. apply in_or_app. left. apply in_or_app. right. exact Hin.
  rewrite <- !app_assoc. rewrite lb_remove_app. rewrite Eq. reflexivity. exact (NI (q, n) (in_or_app _ _ _ (or_introl Hin))).
Qed.

Lemma gen_back (fx : FPState) Rc Mc modelc W BX4 B2 B3 LBy LBq LKc crc Ac qo qn bits sd (l n : Z) (by_ bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x (Hunn : L5DIA.unnorm_specA L ar HI) :
  let BX := (LBy ++ LBq) ++ BX4 in
  let W1 := W ++ [(L5.bo_data ro br, 8 * L5.bo_cap br)] in
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 (L5.bo_data ro br) -> getr Rc (reg 20) = Z_to_bv 64 (L5.bo_data qo bq) ->
  getr Rc (reg 21) = Z_to_bv 64 ((L5.bo_data (F + 32) bd + 8 * l) / 8 + 2147450880) -> getr Rc (reg 22) = Z_to_bv 64 n ->
  getr Rc (reg 24) = Z_to_bv 64 (L5.bo_data (F + 32) bd + 8 * l) ->
  getr Rc (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr Rc (reg 26) = Z_to_bv 64 (ro / 8 + 2147450880) ->
  aobj FF ro 32 -> aobj FF qo 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc qo bq wq -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n - l -> Z.of_nat (L5.bo_len bd) = l + 1 -> l <= n <= 298 -> 0 <= l <= 298 ->
  2 ^ 63 <= nth_w wd (Z.to_nat l) -> Z.testbit (L5.bo_fb br) 1 = false ->
  L5.u64_at RSEGS Mc (E - 232) l ->
  In (E - 224, L5.bo_data (F + 32) bd) cells -> In (E - 216, l + 1) cells -> In (E - 208, ro) cells ->
  In (E - 248, qo) cells -> In (E - 296, F) cells -> In (E - 264, F + 32) cells -> In (E - 272, F + 96) cells ->
  In (E - 312, qn) cells -> 0 <= qn <= 1 -> In (E - 304, 1) cells -> In (E - 288, bits) cells -> (bits = 0 \/ bits = 2) -> In (E - 336, sd) cells -> (sd = 0 \/ sd = 1) -> 0 <= x <= 63 ->
  (forall c v, In (c, v) cells -> (c + 8 <= E - 328 \/ E - 312 <= c) /\ (c + 8 <= E - 184 \/ E - 176 <= c)) ->
  L5OMA.stksh ar M (E - SCRD) -> 352 + L5DIA.UNNORM_SCR <= SCRD -> SCRD mod 8 = 0 -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 ->
  (forall a, qo <= a < qo + 32 -> ~ L5.outside W a) -> (forall a, ro <= a < ro + 32 -> ~ L5.outside W a) ->
  (forall cap q a, L5.bo_st by_ = L5.BDyn cap q -> q <= a < q + 8 * cap -> ~ L5.outside W a) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (forall cap q, L5.bo_st by_ = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> (forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) BX4) ->
  match skind (L5.bo_st by_), skind (L5.bo_st br) with
  | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LBy = []
  | None, None => LBy = []
  | None, Some (cap', q') => cap' = 8 /\ LBy = [(q', 64)]
  | Some _, None => False end ->
  match skind (L5.bo_st bq) with None => LBq = [] | Some (cap, q) => LBq = [(q, 8 * cap)] end ->
  (sd = 1 -> exists qX, L5.bo_st br = L5.BDyn 8 qX /\ (2 <= L5.bo_len br <= 6)%nat) ->
  (sd = 1 -> L5OMA.acredit_for L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES) ->
  match on0 with None => B2 = BX4 | Some (q, k) => In (q, k) BX4 /\ lb_remove q (BX4 ++ LB) = B2 ++ LB end ->
  match blk_of bn with None => B3 = B2 | Some (q, k) => In (q, k) B2 /\ lb_remove q (B2 ++ LB) = B3 ++ LB end ->
  match blk_of bd with None => [] = B3 | Some (q, k) => In (q, k) B3 /\ lb_remove q (B3 ++ LB) = [] ++ LB end ->
  (forall (fxf : FPState) Rf Mf modelf Af crf LKf bqf wqf brf wrf fb',
      regs_preserved R Rf -> incl Ac Af -> incl LKf LKc -> ahpres L ar LB FF E SCRD W1 M Mf ->
      L5.big_at RSEGS Mf qo bqf -> L5C.obj_limbs RSEGS Mf bqf wqf -> skind (L5.bo_st bqf) = skind (L5.bo_st bq) ->
      L5.big_at RSEGS Mf ro brf -> L5C.obj_limbs RSEGS Mf brf wrf -> skind (L5.bo_st brf) = skind (L5.bo_st br) ->
      L5.bo_fb brf = Z.lor (Z.land fb' 253) bits -> Z.testbit fb' 1 = false ->
      L5OMA.acredit_after L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES crf ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI ((LBy ++ LBq) ++ LB) FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  (forall (fx2 : FPState) R2 M2' model2' bq2 br2 wq2 wr2,
      binv W BX M2' model2' LKc crc Ac -> rinvD R E R2 ->
      (getr R2 (reg 1) = Z_to_bv 64 0x92a54 /\ getr R2 (reg 18) = Z_to_bv 64 SH /\ getr R2 (reg 19) = Z_to_bv 64 ro /\ getr R2 (reg 20) = Z_to_bv 64 (F + 32) /\ getr R2 (reg 21) = Z_to_bv 64 (F + 96) /\ getr R2 (reg 22) = Z_to_bv 64 qo /\ getr R2 (reg 23) = Z_to_bv 64 (ro / 8 + 2147450880) /\ getr R2 (reg 24) = Z_to_bv 64 F /\ getr R2 (reg 27) = Z_to_bv 64 F) ->
      skind (L5.bo_st bq2) = skind (L5.bo_st bq) ->
      tob (BX ++ LB) M2' qo bq2 wq2 -> tob (BX ++ LB) M2' ro br2 wr2 -> skind (L5.bo_st br2) = skind (L5.bo_st br) -> L5.bo_len br2 = L5.bo_len br ->
      trk BX M2' bn bd bn0 bd0 wn wd on0 ((E - 328, qo / 8 + 2147450880) :: (E - 320, ro / 8 + 2147450880) :: cells) x ->
      forall (fx' : FPState) R' M' model' qX LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
      sd = 1 -> L5.bo_st br2 = L5.BDyn 8 qX ->
      L5DIA.unnorm_e3A L ar (BX ++ LB) FF' crc M2' M' R2 R' ro qX (L5.bo_len br2) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model2' model' -> incl Ac A' -> amodel_ok A' model' -> incl LK' LKc ->
      ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9290c Mc modelc) K.
Proof.
  intros BX W1 BI RI X19 X20 X21 X22 X24 X18 X26 AOR AOQ APO TR TQ TRK LENR LENQ LEND NR LR D63 SGR S232 IN224 IN216 IN208 IN248 IN296 IN264 IN272 IN312 QNR IN304 IN288 BITS IN336 SD XR CELLS
         SSH USCR SCR8 FFR5 FFR3 WQH WRH WY WSH INY INN IND RSC QSC SD1 CRD1 L2 L3 Lf KF KE3.
  pose proof BI as (B1 & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (ND : NoDup (map fst (BX ++ LB))). { clear - WF0. decompose [and] WF0. assumption. }
  assert (ND_b : NoDup (map fst ((LBy ++ LBq) ++ (BX4 ++ LB)))). { subst BX. rewrite <- app_assoc in ND. exact ND. }
  assert (ND_a : NoDup (map fst (LBy ++ (LBq ++ BX4 ++ LB)))). { rewrite <- app_assoc in ND_b. exact ND_b. }
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  pose proof TR as (OBR & OLR & SZR & INR). pose proof TQ as (OBQ & OLQ & SZQ & INQ).
  pose proof (len_le_cap Mc ro br OBR) as LCR. fold (L5.bo_cap br) in LCR. pose proof (len_le_cap Mc qo bq OBQ) as LCQ. fold (L5.bo_cap bq) in LCQ.
  (* [comment removed for export] *)
  assert (QB : forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) LBq). { intros cap q Eq. rewrite Eq in QSC. cbn [skind] in QSC. rewrite QSC. left; reflexivity. }
  assert (RB : forall cap q, L5.bo_st br = L5.BDyn cap q -> (L5.bo_st by_ = L5.BDyn cap q /\ In (q, 8 * cap) LB) \/ In (q, 8 * cap) LBy).
  { intros cap q Eq. rewrite Eq in RSC. cbn [skind] in RSC. destruct (skind (L5.bo_st by_)) as [[c0 q0]|] eqn:EK.
    - destruct RSC as (-> & -> & _). apply skind_dyn in EK. left. split. exact EK. exact (INY _ _ EK).
    - destruct RSC as (-> & ->). right. left. reflexivity. }
  assert (NCL : forall q k a, In (q, k) BX -> q <= a < q + k -> ~ aclient L ar LB FF E SCRD a).
  { intros q k a Hin Ha. exact (L5ADVGA.bx_not_client L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac q k a BI Hin Ha). }
  assert (INBX_y : forall b, In b LBy -> In b BX) by (intros b Hb; subst BX; apply in_or_app; left; apply in_or_app; left; exact Hb).
  assert (INBX_q : forall b, In b LBq -> In b BX) by (intros b Hb; subst BX; apply in_or_app; left; apply in_or_app; right; exact Hb).
  assert (INBX_4 : forall b, In b BX4 -> In b BX) by (intros b Hb; subst BX; apply in_or_app; right; exact Hb).
  (* [comment removed for export] *)
  assert (COVR : forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * L5.bo_cap br -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a).
  { intros a Ha Hc. unfold L5.bo_data, L5.bo_cap in Ha. destruct (L5.bo_st br) as [v0 v1|cap q] eqn:Eq. apply WRH. clear - Ha; lia.
    destruct (RB cap q eq_refl) as [(EY & _)|Hin]. exact (WY cap q a EY Ha). exfalso. exact (NCL q (8 * cap) a (INBX_y _ Hin) Ha Hc). }
  assert (COVQ : forall a, L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * L5.bo_cap bq -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a).
  { intros a Ha Hc. unfold L5.bo_data, L5.bo_cap in Ha. destruct (L5.bo_st bq) as [v0 v1|cap q] eqn:Eq. apply WQH. clear - Ha; lia.
    exfalso. exact (NCL q (8 * cap) a (INBX_q _ (QB cap q eq_refl)) Ha Hc). }
  (* [comment removed for export] *)
  assert (NQB : forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q').
  { intros c q c' q' E1 E2. pose proof (QB _ _ E2) as H2. destruct (RB _ _ E1) as [(_ & H1)|H1].
    - intros X0. exact (L5ADVHO.nodup_app_fst BX LB (q', 8 * c') (q, 8 * c) ND (INBX_q _ H2) H1 (eq_sym X0)).
    - exact (L5ADVHO.nodup_app_fst LBy _ (q, 8 * c) (q', 8 * c') ND_a H1 (in_or_app _ _ _ (or_introl H2))). }
  assert (NQ4R : forall (b : L5.bigobj), (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q').
  { intros b INB c q c' q' E1 E2. pose proof (INB _ _ E1) as H1. destruct (RB _ _ E2) as [(_ & H2)|H2].
    - exact (L5ADVHO.nodup_app_fst BX LB (q, 8 * c) (q', 8 * c') ND (INBX_4 _ H1) H2).
    - intros X0. exact (L5ADVHO.nodup_app_fst LBy _ (q', 8 * c') (q, 8 * c) ND_a H2 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl H1)))) (eq_sym X0)). }
  assert (NQ4Q : forall (b : L5.bigobj), (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q').
  { intros b INB c q c' q' E1 E2. pose proof (INB _ _ E1) as H1. pose proof (QB _ _ E2) as H2.
    intros X0. exact (L5ADVHO.nodup_app_fst (LBy ++ LBq) _ (q', 8 * c') (q, 8 * c) ND_b (in_or_app _ _ _ (or_intror H2)) (in_or_app _ _ _ (or_introl H1)) (eq_sym X0)). }
  edestruct L5ADVEA.obj_rng with (o := ro) as ((RR1 & RR2 & RR8) & _); try first [exact LY | exact HIok | exact BI | exact AOR'].
  apply (G9T fx Rc Mc modelc W BX LKc crc Ac ro qo br bq bn bd bn0 bd0 wr wq wn wd on0 cells x n l BI RI X19 X20 X21 X22 X24 AOR AOQ TR TQ TRK LENR LENQ LEND ltac:(clear - NR; lia) LR D63 S232 IN224 IN216 IN208
           ltac:(clear - RR1 RR2; lia) CELLS SSH WSH).
  { intros a Ha. apply COVR. clear - Ha LCR LENR. lia. }
  { intros a Ha. apply COVQ. clear - Ha LCQ LENQ. lia. }
  { exact APO. } { exact NQB. } { exact (NQ4R bn INN). } { exact (NQ4Q bn INN). } { exact (NQ4R bd IND). } { exact (NQ4Q bd IND). }
  intros fx1 R1 M1 model1 br1 wr1 bq1 wq1 BI1 RI1 TR1 FBR1 LENR1 SSR1 DATR1 TQ1 FBQ1 LENQ1 SSQ1 DATQ1 TRK1 S328 S320.
  pose proof (skind_same _ _ SSR1) as KR1. pose proof (skind_same _ _ SSQ1) as KQ1.
  assert (STR : forall c q, L5.bo_st br1 = L5.BDyn c q -> L5.bo_st br = L5.BDyn c q). { intros c q Eq. apply skind_dyn. rewrite <- KR1. apply skind_dyn. exact Eq. }
  assert (STQ : forall c q, L5.bo_st bq1 = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c q). { intros c q Eq. apply skind_dyn. rewrite <- KQ1. apply skind_dyn. exact Eq. }
  assert (CAPR1 : L5.bo_cap br1 = L5.bo_cap br). { unfold L5.bo_cap. unfold skind in KR1. destruct (L5.bo_st br1); destruct (L5.bo_st br); try discriminate KR1; try reflexivity. injection KR1 as -> _. reflexivity. }
  rewrite (U_of Rc 18 _ X18) in S328 by (edestruct L5ADVEA.obj_rng with (o := qo) as ((Q1 & Q2 & _) & _); try first [exact LY | exact HIok | exact BI | exact AOQ']; clear - Q1 Q2; lia).
  rewrite (U_of Rc 26 _ X26) in S320 by (clear - RR1 RR2; lia).
  set (cells' := (E - 328, qo / 8 + 2147450880) :: (E - 320, ro / 8 + 2147450880) :: cells).
  assert (TRK1' : trk BX M1 bn bd bn0 bd0 wn wd on0 cells' x).
  { destruct TRK1 as (T1 & T2 & T3 & T4 & SPL1 & T6). split. exact T1. split. exact T2. split. exact T3. split. exact T4. split. 2: exact T6.
    intros a v [Eq|[Eq|Hin]]. injection Eq as <- <-. split. exact S328. clear; lia. injection Eq as <- <-. split. exact S320. clear; lia. exact (SPL1 a v Hin). }
  assert (INC : forall c v, In (c, v) cells -> In (c, v) cells') by (intros c v Hin; right; right; exact Hin).
  (* [comment removed for export] *)
  assert (NI4 : forall b, In b (BX4 ++ LB) -> ~ In (fst b) (map fst (LBy ++ LBq))).
  { intros b Hb X0. apply in_map_iff in X0. destruct X0 as (b1 & E1 & H1). exact (L5ADVHO.nodup_app_fst (LBy ++ LBq) _ b1 b ND_b H1 Hb E1). }
  assert (SUB2 : forall b, In b (B2 ++ LB) -> In b (BX4 ++ LB)). { destruct on0 as [[q0 k0]|]. destruct L2 as (_ & <-). intros b. apply in_lb_remove_inv. subst B2. intros b Hb; exact Hb. }
  assert (SUB3 : forall b, In b (B3 ++ LB) -> In b (B2 ++ LB)). { destruct (blk_of bn) as [[q0 k0]|]. destruct L3 as (_ & <-). intros b. apply in_lb_remove_inv. subst B3. intros b Hb; exact Hb. }
  pose proof (lift_rm (LBy ++ LBq) BX4 B2 on0 NI4 L2) as L2'.
  pose proof (lift_rm (LBy ++ LBq) B2 B3 (blk_of bn) ltac:(intros b Hb; exact (NI4 b (SUB2 b Hb))) L3) as L3'.
  pose proof (lift_rm (LBy ++ LBq) B3 [] (blk_of bd) ltac:(intros b Hb; exact (NI4 b (SUB2 b (SUB3 b Hb)))) Lf) as Lf'.
  apply (gT_u fx1 R1 M1 model1 W W1 BX ((LBy ++ LBq) ++ B2) ((LBy ++ LBq) ++ B3) ((LBy ++ LBq) ++ []) LKc crc Ac qo qn bits sd bq1 br1 bn bd bn0 bd0 wq1 wr1 wn wd on0 cells' x Hunn BI1 RI1 AOQ AOR APO TQ1 TR1 TRK1').
  { intros a Ha. apply WQH. clear - Ha; lia. }
  { intros a OUT. subst W1. apply L5.outside_app in OUT. destruct OUT as (O1 & O2). split. exact O1.
    intros rr [<-|[<-|[]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR. exact (WRH a IR O1). rewrite DATR1, CAPR1 in IR. apply (O2 _ (or_introl eq_refl)). exact IR. }
  all: try (apply INC; assumption).
  { exact QNR. } { exact BITS. } { right; left; reflexivity. } { left; reflexivity. } { exact SD. } { exact XR. }
  { intros c q c' q' E1 E2. exact (NQB c q c' q' (STR _ _ E1) (STQ _ _ E2)). }
  { intros c q c' q' E1 E2. exact (NQ4Q bn INN c q c' q' E1 (STQ _ _ E2)). }
  { intros c q c' q' E1 E2. exact (NQ4Q bd IND c q c' q' E1 (STQ _ _ E2)). }
  { intros c q c' q' E1 E2. exact (NQ4R bn INN c q c' q' E1 (STR _ _ E2)). }
  { intros c q c' q' E1 E2. exact (NQ4R bd IND c q c' q' E1 (STR _ _ E2)). }
  { exact USCR. } { exact SCR8. } { exact FFR5. } { exact FFR3. } { exact SSH. } { exact WSH. }
  { rewrite LENR1. clear - LENR NR LR. lia. }
  { rewrite FBR1. exact SGR. }
  { intros S1. destruct (SD1 S1) as (qX & EX & LX). exists qX. rewrite LENR1. split. 2: exact LX. apply skind_dyn. rewrite KR1. apply skind_dyn. exact EX. }
  { exact CRD1. } { exact L2'. } { exact L3'. } { exact Lf'. }
  { intros cap q Eq. rewrite app_nil_r. apply in_or_app. left. apply in_or_app. right. exact (QB cap q (STQ _ _ Eq)). }
  { intros cap q Eq. rewrite app_nil_r. destruct (RB cap q (STR _ _ Eq)) as [(_ & Hin)|Hin]. apply in_or_app. right. exact Hin. apply in_or_app. left. apply in_or_app. left. exact Hin. }
  { intros fxf Rf Mf modelf Af crf LKf fbq' fb' n' st' w' RPf IAf AHf OBQf OLQf OBRf OLRf SGf SSf CRAf ILKf RTf AMf HHf. rewrite app_nil_r in HHf.
    apply (KF fxf Rf Mf modelf Af crf LKf _ _ (L5.BO (Z.lor (Z.land fb' 253) bits) n' st') w' fb' RPf IAf ILKf AHf OBQf OLQf). cbn [L5.bo_st]. exact KQ1.
    exact OBRf. exact OLRf. cbn [L5.bo_st]. rewrite (skind_same _ _ SSf). exact KR1. reflexivity. exact SGf. exact CRAf. exact RTf. exact AMf. exact HHf. }
  { intros fx2 R2 M2' model2' bq2 BI2 RI2 REGS2 ST2' TQ2 TR2 TRK2. apply (KE3 fx2 R2 M2' model2' bq2 br1 _ wr1 BI2 RI2 REGS2 ltac:(rewrite ST2'; exact KQ1) TQ2 TR2 KR1 LENR1 TRK2). }
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cinv (cr cri : credit) (KK BB dk db : Z) : Prop :=
  exists k b, cri = L5OMA.adebits L cr k b /\ 0 <= k /\ 0 <= b /\ k + dk + L5DIA.DIVN_K <= KK /\ b + db + L5DIA.DIVN_BYTES <= BB.
Lemma cinv_for cr cri KK BB dk db k' b' : cinv cr cri KK BB dk db -> L5OMA.acredit_for L cr KK BB -> 0 <= k' <= dk -> 0 <= b' <= db -> L5OMA.acredit_for L cri k' b'.
Proof.
  intros (k & b & -> & K0 & B0 & K1 & B1) (C1 & C2) Hk Hb. destruct (aly_cost L C LY) as (P1 & P2 & P3). unfold L5DIA.DIVN_K, L5DIA.DIVN_BYTES in *.
  unfold L5OMA.acredit_for, L5OMA.adebits. cbn [fst snd]. split.
  - clear - C1 K0 K1 Hk P1. nia.
  - clear - C2 K0 K1 B0 B1 Hk Hb P2 P3. nia.
Qed.
Lemma cinv_debit cr cri KK BB dk db n dk' db' : cinv cr cri KK BB dk db -> 0 <= n -> dk' + 1 <= dk -> db' + n <= db -> cinv cr (adebit L cri n) KK BB dk' db'.
Proof.
  intros (k & b & -> & K0 & B0 & K1 & B1) Hn Hk Hb. exists (k + 1), (b + n). split. rewrite <- L5OMA.adebits_1. rewrite L5OMA.adebits_add. reflexivity.
  split. clear - K0; lia. split. clear - B0 Hn; lia. split. clear - K1 Hk; lia. clear - B1 Hb; lia.
Qed.
Lemma cinv_weak cr cri KK BB dk db dk' db' : cinv cr cri KK BB dk db -> dk' <= dk -> db' <= db -> cinv cr cri KK BB dk' db'.
Proof. intros (k & b & -> & K0 & B0 & K1 & B1) Hk Hb. exists k, b. split. reflexivity. split. exact K0. split. exact B0. split. clear - K1 Hk; lia. clear - B1 Hb; lia. Qed.
Lemma cinv_fin cr cri KK BB dk db crf : cinv cr cri KK BB dk db -> 0 <= dk -> 0 <= db -> L5OMA.acredit_after L cri L5DIA.DIVN_K L5DIA.DIVN_BYTES crf -> L5OMA.acredit_after L cr KK BB crf.
Proof.
  intros (k & b & -> & K0 & B0 & K1 & B1) Hk Hb CA. unfold L5OMA.acredit_after in *. rewrite L5OMA.adebits_add in CA.
  eapply credit_le_trans. 2: exact CA. apply L5OMA.adebits_le. exact (as0_layout2_of L C LY). clear - K1 Hk; lia. clear - B1 Hb; lia.
Qed.
Lemma ru_bounds i : 0 <= i -> 8 <= round_up i <= i + 8.
Proof. intros Hi. unfold round_up. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma dyn_kind Mk o b : L5.big_at RSEGS Mk o b -> L5.bo_dyn b = match skind (L5.bo_st b) with None => false | Some _ => true end.
Proof. intros (_ & _ & _ & OST). unfold L5.bo_dyn, skind. destruct (L5.bo_st b); exact (proj1 OST). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sh_off_obj W BX Mc modelc LKc crc Ac o a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> ~ (o <= a < o + 32).
Proof.
  intros (B1 & _) AO Hs. pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AO ltac:(clear; lia) ltac:(reflexivity)) as ((O1 & O2 & _) & OBIG & _).
  unfold in_shadow_of, S, SB in Hs. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in Hs by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in Hs.
  assert (0 <= ahl_ceil ar / 8) by (apply Z.div_pos; [clear - O1 O2; lia | clear; lia]). clear - Hs OBIG H. lia.
Qed.
Lemma sh_off_blk W BX Mc modelc LKc crc Ac q k a : binv W BX Mc modelc LKc crc Ac -> aobj FF' ro 32 -> In (q, k) (BX ++ LB) -> in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> ~ (q <= a < q + k).
Proof.
  intros (B1 & _) AO Hin Hs. pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc ro 32 0 0 B1 AO ltac:(clear; lia) ltac:(reflexivity)) as ((O1 & O2 & _) & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _). destruct (WB _ Hin) as ((_ & _ & _ & _ & _ & (_ & AM & _)) & _). cbn [fst snd] in AM.
  unfold in_shadow_of, S, SB in Hs. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in Hs by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in Hs.
  assert (0 <= ahl_ceil ar / 8) by (apply Z.div_pos; [clear - O1 O2; lia | clear; lia]). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. clear - Hs AM H. lia.
Qed.

Lemma dist5 W BX4 LBy LBq Mc modelc LKc crc Ac (by_ bq br bn bd : L5.bigobj) :
  binv W ((LBy ++ LBq) ++ BX4) Mc modelc LKc crc Ac ->
  (forall cap q, L5.bo_st by_ = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> (forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) BX4) ->
  match skind (L5.bo_st by_), skind (L5.bo_st br) with
  | Some (cap, q), Some (cap', q') => cap' = cap /\ q' = q /\ LBy = []
  | None, None => LBy = []
  | None, Some (cap', q') => cap' = 8 /\ LBy = [(q', 64)]
  | Some _, None => False end ->
  match skind (L5.bo_st bq) with None => LBq = [] | Some (cap, q) => LBq = [(q, 8 * cap)] end ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') /\
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') /\ (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') /\
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') /\ (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') /\
  (forall cap q, L5.bo_st br = L5.BDyn cap q -> (L5.bo_st by_ = L5.BDyn cap q /\ In (q, 8 * cap) LB) \/ In (q, 8 * cap) LBy) /\
  (forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) LBq).
Proof.
  intros BI INY INN IND RSC QSC. set (BX := (LBy ++ LBq) ++ BX4) in *. pose proof BI as (B1 & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (ND : NoDup (map fst (BX ++ LB))). { clear - WF0. decompose [and] WF0. assumption. }
  assert (ND_b : NoDup (map fst ((LBy ++ LBq) ++ (BX4 ++ LB)))). { subst BX. rewrite <- app_assoc in ND. exact ND. }
  assert (ND_a : NoDup (map fst (LBy ++ (LBq ++ BX4 ++ LB)))). { rewrite <- app_assoc in ND_b. exact ND_b. }
  assert (QB : forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) LBq). { intros cap q Eq. rewrite Eq in QSC. cbn [skind] in QSC. rewrite QSC. left; reflexivity. }
  assert (RB : forall cap q, L5.bo_st br = L5.BDyn cap q -> (L5.bo_st by_ = L5.BDyn cap q /\ In (q, 8 * cap) LB) \/ In (q, 8 * cap) LBy).
  { intros cap q Eq. rewrite Eq in RSC. cbn [skind] in RSC. destruct (skind (L5.bo_st by_)) as [[c0 q0]|] eqn:EK.
    - destruct RSC as (-> & -> & _). apply skind_dyn in EK. left. split. exact EK. exact (INY _ _ EK).
    - destruct RSC as (-> & ->). right. left. reflexivity. }
  assert (INBX_q : forall b, In b LBq -> In b BX) by (intros b Hb; subst BX; apply in_or_app; left; apply in_or_app; right; exact Hb).
  assert (INBX_4 : forall b, In b BX4 -> In b BX) by (intros b Hb; subst BX; apply in_or_app; right; exact Hb).
  assert (NQ4R : forall (b : L5.bigobj), (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q').
  { intros b INB c q c' q' E1 E2. pose proof (INB _ _ E1) as H1. destruct (RB _ _ E2) as [(_ & H2)|H2].
    - exact (L5ADVHO.nodup_app_fst BX LB (q, 8 * c) (q', 8 * c') ND (INBX_4 _ H1) H2).
    - intros X0. exact (L5ADVHO.nodup_app_fst LBy _ (q', 8 * c') (q, 8 * c) ND_a H2 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl H1)))) (eq_sym X0)). }
  assert (NQ4Q : forall (b : L5.bigobj), (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) BX4) -> forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q').
  { intros b INB c q c' q' E1 E2. pose proof (INB _ _ E1) as H1. pose proof (QB _ _ E2) as H2.
    intros X0. exact (L5ADVHO.nodup_app_fst (LBy ++ LBq) _ (q', 8 * c') (q, 8 * c) ND_b (in_or_app _ _ _ (or_intror H2)) (in_or_app _ _ _ (or_introl H1)) (eq_sym X0)). }
  split. { intros c q c' q' E1 E2. pose proof (QB _ _ E2) as H2. destruct (RB _ _ E1) as [(_ & H1)|H1].
    - intros X0. exact (L5ADVHO.nodup_app_fst BX LB (q', 8 * c') (q, 8 * c) ND (INBX_q _ H2) H1 (eq_sym X0)).
    - exact (L5ADVHO.nodup_app_fst LBy _ (q, 8 * c) (q', 8 * c') ND_a H1 (in_or_app _ _ _ (or_introl H2))). }
  split. exact (NQ4R bn INN). split. exact (NQ4Q bn INN). split. exact (NQ4R bd IND). split. exact (NQ4Q bd IND). split. exact RB. exact QB.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGO2C.

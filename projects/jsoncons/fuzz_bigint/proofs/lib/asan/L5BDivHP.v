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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPH L5BDivPL L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BRed L5BDivHL L5BDivHL2 L5BDivHM L5BDivHN L5BDivHH L5BDivHO L5BDivGE L5DivSpecsAB0 L5DivInnerSpecsAB0 L5OpmodSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHP.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADIVPL. Import L5ADVHL. Import L5ADVHL2. Import L5ADVHM. Import L5ADVHN. Import L5ADVHH. Import L5ADVHO. Import L5ADVGE.
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
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis Hrsz : resize_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Variable cr0 : credit.
Hypothesis HH0 : ri_inv HI LB FF LK cr0 A M (vml_of model).
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.



(* [comment removed for export] *)
Definition hst (Mk : word -> option byte) (cells : list (Z * Z)) (bn bd : L5.bigobj) (on od : option (Z * Z)) : Prop :=
  spl E Mk cells /\ obj_at Mk (F + 96) bn on /\ obj_at Mk (F + 32) bd od.
Lemma hst_keep LBx scr (X : Z -> Prop) Mc M1 cells bn bd on od :
  hst Mc cells bn bd on od -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall i, SPA <= i < E \/ F + 32 <= i < F + 128 -> ~ X i) -> hst M1 cells bn bd on od.
Proof.
  intros (SP & ON & OD) OFF NX.
  split. { eapply spl_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact SP | exact OFF | ]. intros i Hi. apply NX. left; exact Hi. }
  split. { eapply L5ADVEA.loc_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact ON | clear; lia | clear; lia | exact OFF | ]. intros i Hi. apply NX. right; clear - Hi; lia. }
  eapply L5ADVEA.loc_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact OD | clear; lia | clear; lia | exact OFF | ]. intros i Hi. apply NX. right; clear - Hi; lia.
Qed.
Lemma hst_keepx LBx scr (X : Z -> Prop) Mc M1 cells bn bd on od :
  hst Mc cells bn bd on od -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall a v, In (a, v) cells -> forall i, a <= i < a + 8 -> ~ X i) -> (forall i, F + 32 <= i < F + 128 -> ~ X i) -> hst M1 cells bn bd on od.
Proof.
  intros (SP & ON & OD) OFF NXC NX.
  split. { intros a v Hin. destruct (SP a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
           eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact Hc | exact H1 | exact H2 | exact OFF | ]. intros i Hi. exact (NXC a v Hin i Hi). }
  split. { eapply L5ADVEA.loc_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact ON | clear; lia | clear; lia | exact OFF | ]. intros i Hi. apply NX. clear - Hi; lia. }
  eapply L5ADVEA.loc_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact OD | clear; lia | clear; lia | exact OFF | ]. intros i Hi. apply NX. clear - Hi; lia.
Qed.
Lemma qb_keep LBx scr (X : Z -> Prop) Mc M1 qo bq : aobj FF qo 32 -> 4096 <= qo <= 140737488355296 -> L5.big_at RSEGS Mc qo bq ->
  L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall i, qo <= i < qo + 32 -> ~ X i) -> L5.big_at RSEGS M1 qo bq.
Proof.
  intros AOQ QR OB OFF NX. eapply L5C.big_at_agree. 4: exact OB. 2: clear - QR; lia. 2: clear - QR; lia. intros i Hi. apply OFF. clear - Hi QR; lia.
  apply (obj_client L ar LBx FF' SPA scr qo 32 i). apply aobj_cons. exact AOQ. exact Hi. apply NX. exact Hi.
Qed.
Lemma big_inl_upd (Mc M1 : word -> option byte) o fb n v0 v1 k : L5.big_at RSEGS Mc o (L5.BO fb n (L5.BInl v0 v1)) -> 4096 <= o <= 140737488355296 -> (k = 16 \/ k = 24) ->
  (forall a, o <= a < o + 32 -> ~ (o + k <= a < o + k + 8) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.defined M1 (o + k) 8 ->
  exists v0' v1', L5.big_at RSEGS M1 o (L5.BO fb n (L5.BInl v0' v1')).
Proof.
  intros (B0 & FBR & B8 & (BT & B16 & B24 & N2 & V0R & V1R)) OR KR AG DF. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct (word_of_defined M1 (o + k) DF ltac:(clear - OR KR; lia) ltac:(clear - OR KR; lia)) as (w & WA & WR).
  assert (KP8 : forall a v, (a = o + 8 \/ a = o + 40 - k) -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR KR; lia. 2: clear - Ha OR KR; lia. intros i Hi. apply AG. clear - Hi Ha OR KR; lia. clear - Hi Ha KR; lia. }
  assert (KP0 : L5.u8_at RSEGS M1 o fb). { eapply L5C.u8_at_agree. 4: exact B0. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply AG. clear - Hi OR; lia. clear - Hi KR; lia. }
  destruct KR as [-> | ->].
  - exists w, v1. split. exact KP0. split. exact FBR. split. apply KP8. left; reflexivity. exact B8. cbn [L5.bo_st L5.bo_fb L5.bo_len]. split. exact BT. split. exact WA.
    split. apply KP8. right; clear; lia. exact B24. split. exact N2. split. exact WR. exact V1R.
  - exists v0, w. split. exact KP0. split. exact FBR. split. apply KP8. left; reflexivity. exact B8. cbn [L5.bo_st L5.bo_fb L5.bo_len]. split. exact BT. split. apply KP8. right; clear; lia. exact B16.
    split. exact WA. split. exact N2. split. exact V0R. exact WR.
Qed.

(* [comment removed for export] *)
Lemma half_path (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 c qo qn bits bn bd wn wd fbx x0 x1 d0 d1 :
  at20 L ar HI R M model LB FF LK A E SCRD F ro g1 g2 R9 M9 model9 cr9 LK9 A9 c ro qo qn bits 1 bn bd wn wd -> 0 <= c <= 1 -> bits = 0 ->
  L5OMA.stksh ar M (E - SCRD) -> SCRD mod 8 = 0 ->
  L5.big_at RSEGS M ro (L5.BO fbx 2 (L5.BInl x0 x1)) -> aobj FF ro 32 -> shadow_zero M ro 4 ->
  L5.bo_len bn = 2%nat -> L5.bo_dyn bn = false -> L5.bo_len bd = 1%nat -> L5.bo_st bd = L5.BInl d0 d1 -> 1 <= d0 <= 4294967295 ->
  L5.big_at RSEGS M qo (L5.BO 0 0 (L5.BInl 0 0)) -> aobj FF qo 32 -> shadow_zero M qo 4 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  (forall (fxf : FPState) Rf Mf modelf Af LKf,
      regs_preserved R Rf -> incl A9 Af -> incl LKf LK9 -> ahpres L ar LB FF E SCRD [(ro, 32); (qo, 32)] M Mf ->
      (exists fq nq q0 q1, L5.big_at RSEGS Mf qo (L5.BO fq nq (L5.BInl q0 q1))) ->
      (exists fr nr r0 r1, L5.big_at RSEGS Mf ro (L5.BO fr nr (L5.BInl r0 r1)) /\ Z.testbit fr 1 = false) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI LB FF LKf cr9 Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92c94 M9 model9) K.
Proof.
  intros A20 CR BZ SSH SC8 OBX AOX SZX LN2 DYN LD1 STD D0R OBQ AOQ SZQ APT KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model ro 32 E SCRD HH0 AOX ltac:(clear; lia) ltac:(reflexivity)) as ((XLO & XCE & XHI & X8 & _) & XBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model qo 32 E SCRD HH0 AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  assert (SLO : ahl_ceil ar + 4096 + SCRD <= E) by (destruct G as [_ _ SLO0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact SLO0).
  assert (FCE : F + 512 <= ahl_ceil ar) by (destruct G as [_ _ _ _ _ _ _ _ _ FCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact FCEIL).
  set (bx := L5.BO fbx 2 (L5.BInl x0 x1)). set (bq0 := L5.BO 0 0 (L5.BInl 0 0)).
  assert (TX : L5ADVEA.tob LB M ro bx [x0; x1]).
  { split. exact OBX. split. { destruct OBX as (_ & _ & _ & (_ & _ & _ & _ & V0 & V1)). split. reflexivity. split. constructor; [exact V0 | constructor; [exact V1 | constructor]]. reflexivity. } split. exact SZX. intros cap q Eq. discriminate Eq. }
  assert (TQ : L5ADVEA.tob LB M qo bq0 []).
  { split. exact OBQ. split. { split. reflexivity. split. constructor. reflexivity. } split. exact SZQ. intros cap q Eq. discriminate Eq. }
  (* [comment removed for export] *)
  assert (XOW : forall W0, (forall rr, In rr W0 -> rr = (qo, 32)) -> forall a, L5ADVEA.oreg ro bx a -> L5.outside W0 a).
  { intros W0 HW a OR rr Hr IR. rewrite (HW rr Hr) in IR. unfold L5.in_rng in IR; cbn [fst snd] in IR. destruct OR as [OR|[OR|(cap & q & Eq & _)]]. clear - OR IR APT; lia.
    unfold SB in OR. clear - OR IR QBIG QLO XLO XHI. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. discriminate Eq. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SHW : forall o o2, 0x634000 <= o -> o + 32 <= 2 ^ 47 -> (0x7fff7000 + 17592186048512 <= o2 \/ o2 + 32 <= 0x7fff7000) -> 0x634000 <= o2 -> forall j, 0 <= j < 4 -> ~ (o2 <= o / 8 + SB + j < o2 + 32)).
  { intros o o2 H1 H2 H3 H4 j Hj. unfold SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - H1 H2 H3 H4 Hj. lia. }
  (* [comment removed for export] *)
  assert (NWSH : forall W0, (forall rr, In rr W0 -> rr = (qo, 32) \/ rr = (ro, 32)) -> forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> L5.outside W0 x).
  { intros W0 HW x SX rr Hr IR. unfold in_shadow_of, S, SB in SX. unfold L5.in_rng in IR. destruct (HW rr Hr) as [-> | ->]; cbn [fst snd] in IR. clear - SX IR QBIG QLO QCE. lia. clear - SX IR XBIG XLO XCE. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  eapply (L5ADVGE.atG_of_p4 L ar C HI LY HIok) with (toHT := true) (bt := bx) (wt := [x0; x1]) (bq := bq0) (wq := @nil Z);
    try first [exact G | exact ER | exact EA | exact HSCR | exact HH0 | exact A20 | exact CR | exact TX | exact AOX | exact TQ | exact AOQ].
  { rewrite DYN. unfold L5.bo_dyn, bx. cbn [L5.bo_fb]. destruct OBX as (_ & _ & _ & (BT & _)). cbn [L5.bo_fb] in BT. rewrite BT. reflexivity. }
  { intros DY. exfalso. unfold L5.bo_dyn, bq0 in DY. cbn in DY. discriminate DY. }
  { split. exact LD1. rewrite LN2. clear; lia. }
  intros fx1 R1 M1 model1 (BI1 & RI1 & Y18 & Y21 & Y22 & Y25 & Y26 & Y27 & QNR & BITS & TN1 & TD1 & ON1 & OD1 & SGN & SGD & SP1 & DSH1 & HDR1) p11 TX1 TQ1 VW1. cbn iota.
  set (cells := [(E - 304, F + 32); (E - 344, 1); (E - 296, qo); (E - 264, ro); (E - 288, ro); (E - 328, bits); (E - 280, F + 96); (E - 312, qn); (E - 336, F);
                 (E - 320, qo / 8 + 2147450880); (E - 352, (qo + 8) / 8 + 2147450880); (E - 120, F + 48); (E - 152, ro + 16); (E - 144, 2)]).
  assert (SP1c : spl E M1 cells).
  { intros a v Hin. unfold cells in Hin. cbn [In] in Hin.
    destruct Hin as [Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|Hin]]]]]]]]]]].
    1-11: (apply SP1; rewrite <- Eq; cbn [In]; clear; tauto).
    destruct Hin as [Eq|[Eq|[Eq|[]]]]; injection Eq as <- <-.
    - pose proof (VW1 (E - 120) _ ltac:(left; reflexivity)) as X. unfold L5.bo_data in X. rewrite STD in X. replace (F + 48) with (F + 32 + 16) by (clear; lia). exact X.
    - exact (VW1 (E - 152) _ ltac:(do 4 right; left; reflexivity)).
    - exact (VW1 (E - 144) _ ltac:(do 5 right; left; reflexivity)). }
  assert (HST1 : hst M1 cells bn bd (on_of g2) (on_of g1)) by (split; [exact SP1c | split; [exact ON1 | exact OD1]]).
  assert (SHD1 : shr8 M1 F 4 4 0) by (exact (proj1 (proj2 DSH1))).
  assert (D01 : L5.u64_at RSEGS M1 (F + 48) d0).
  { destruct OD1 as (OBD1 & _). destruct OBD1 as (_ & _ & _ & ST). rewrite STD in ST. destruct ST as (_ & D16 & _). replace (F + 48) with (F + 32 + 16) by (clear; lia). exact D16. }
  change (Z.of_nat (L5.bo_len bx)) with 2 in p11.
  eapply (L5ADVHL2.ht L ar C HI LY HIok) with (toG := false) (qo := qo) (d0 := d0) (lent := 2); try first [exact G | exact ER | exact EA];
    [exact BI1 | exact RI1 | exact Y18 | exact p11 | exact (proj1 (SP1c _ _ ltac:(do 11 right; left; reflexivity))) | exact (proj1 (SP1c _ _ ltac:(do 2 right; left; reflexivity)))
     | exact SHD1 | exact D01 | clear - D0R; lia | clear; lia | clear - QLO QHI; lia | ].
  intros fx2 R2 model2' BI2 KS2 q20 (q1 & q10). cbn iota in KS2 |- *.
  assert (RI2 : rinvD R E R2). { apply (rinvD_ks R E R1 R2 KS_v5HTh RI1 KS2). vm_compute; reflexivity. }
  assert (q11 : getr R2 (reg 11) = Z_to_bv 64 (Z.of_nat 2)). { rewrite (KS2 11%nat) by inl. exact p11. }
  (* [comment removed for export] *)
  eapply L5ADVHH.resize_stage with (W1 := [(qo, 32)]) (o := qo) (n := 2%nat) (b := bq0) (ws := []) (pcn := 0x93084); try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4 | exact HSCR | exact FFR1 | exact FFRS | exact Hrsz];
    [exact BI2 | exact RI2 | exact q10 | exact q11 | exact q1 | split; [clear; lia | reflexivity] | exact (proj1 TQ1) | exact (proj1 (proj2 TQ1)) | exact AOQ | exact (proj1 (proj2 (proj2 TQ1)))
     | clear; lia | intros DY; discriminate DY | intros N3; exfalso; clear - N3; lia | intros cap q Eq; discriminate Eq | | ].
  { intros a O. split. intros rr []. intros rr [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd L5.bo_data L5.bo_st L5.bo_len bq0] in IR; apply (O (qo, 32)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; exact IR | left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - IR; lia]. }
  intros fx3 R3 M3 model3 g3 LBn3 cr3 LK3 A3 POST3 BI3 IA3 ILK3.
  destruct g3 as [|q3 cap3]. 2:{ exfalso. destruct POST3 as (_ & (_ & N3 & _)). clear - N3. lia. }
  destruct POST3 as (RP3 & (_ & _ & ECR3 & (st3 & OBQ3 & _ & SST3) & AH3)). subst cr3. cbn [bq0 L5.bo_fb L5.bo_st] in OBQ3, SST3.
  destruct st3 as [v0 v1|? ?]. 2: destruct SST3.
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F _ RESIZE_SCR _ M1 M3 AH3) as OFF3.
  assert (NX3 : forall i, L5ADVEA.inW [(qo, 32); (L5.bo_data qo bq0 + 8 * Z.of_nat (L5.bo_len bq0), 8 * Z.max 0 (Z.of_nat 2 - Z.of_nat (L5.bo_len bq0)))] i -> qo <= i < qo + 32).
  { intros i (rr & [Er|[Er|[]]] & IR); subst rr; unfold L5.in_rng in IR; cbn [fst snd L5.bo_data L5.bo_st L5.bo_len bq0] in IR; clear - IR; lia. }
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] _ M1 model1 LK9 cr9 A9 qo BI1 AOQ (proj1 (proj2 (proj2 TQ1)))) as (_ & _ & _ & _ & QFR & QF & QSH & _).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] _ M1 model1 LK9 cr9 A9 ro BI1 AOX (proj1 (proj2 (proj2 TX1)))) as (_ & _ & _ & _ & XFR & XF & XSH & _).
  assert (QNF : forall i, qo <= i < qo + 32 -> ~ (SPA <= i < E \/ F + 32 <= i < F + 128)) by (intros i Hi; clear - Hi QFR QF; lia).
  assert (XNF : forall i, ro <= i < ro + 32 -> ~ (SPA <= i < E \/ F + 32 <= i < F + 128)) by (intros i Hi; clear - Hi XFR XF; lia).
  assert (HST3 : hst M3 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. exact HST1. exact OFF3. intros i Hi X. apply (QNF i (NX3 i X)). exact Hi. }
  assert (W3Q : forall rr, In rr [(qo, 32)] -> rr = (qo, 32)) by (intros rr [<-|[]]; reflexivity).
  assert (WROQ : forall a, qo <= a < qo + 32 -> ~ L5.outside [(qo, 32)] a). { intros a Ha O. apply (O (qo, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Ha. }
  assert (SZQW : forall W0 BX0 Mk mk LKk ck Ak, binv W0 BX0 Mk mk LKk ck Ak -> (forall rr, In rr W0 -> rr = (qo, 32) \/ rr = (ro, 32)) -> shadow_zero Mk qo 4 /\ shadow_zero Mk ro 4).
  { intros W0 BX0 Mk mk LKk ck Ak BIk HW. split.
    - eapply L5ADVHL.arg_shz; try first [exact LY | exact HIok]; [exact HH0 | exact BIk | exact AOQ | exact SZQ | ]. intros j Hj rr Hr IR. unfold L5.in_rng in IR. destruct (HW rr Hr) as [-> | ->]; cbn [fst snd] in IR.
      exact (SHW qo qo QLO QHI QBIG QLO j Hj IR). exact (SHW qo ro QLO QHI XBIG XLO j Hj IR).
    - eapply L5ADVHL.arg_shz; try first [exact LY | exact HIok]; [exact HH0 | exact BIk | exact AOX | exact SZX | ]. intros j Hj rr Hr IR. unfold L5.in_rng in IR. destruct (HW rr Hr) as [-> | ->]; cbn [fst snd] in IR.
      exact (SHW ro qo XLO XHI QBIG QLO j Hj IR). exact (SHW ro ro XLO XHI XBIG XLO j Hj IR). }
  assert (W3QR : forall rr, In rr [(qo, 32)] -> rr = (qo, 32) \/ rr = (ro, 32)) by (intros rr [<-|[]]; left; reflexivity).
  assert (RI3 : rinvD R E R3) by (apply (rinvD_pres R E R2 R3 RI2 RP3)).
  assert (Z18 : getr R3 (reg 18) = Z_to_bv 64 SH). { rewrite (cs_of_preserved R2 R3 18 RP3) by inl. rewrite (KS2 18%nat) by inl. exact Y18. }
  assert (Z20 : getr R3 (reg 20) = Z_to_bv 64 d0). { rewrite (cs_of_preserved R2 R3 20 RP3) by inl. exact q20. }
  assert (Z25 : getr R3 (reg 25) = Z_to_bv 64 (F + 96)). { rewrite (cs_of_preserved R2 R3 25 RP3) by inl. rewrite (KS2 25%nat) by inl. exact Y25. }
  assert (Z26 : getr R3 (reg 26) = Z_to_bv 64 (qo + 8)). { rewrite (cs_of_preserved R2 R3 26 RP3) by inl. rewrite (KS2 26%nat) by inl. exact Y26. }
  assert (Z27 : getr R3 (reg 27) = Z_to_bv 64 F). { rewrite (cs_of_preserved R2 R3 27 RP3) by inl. rewrite (KS2 27%nat) by inl. exact Y27. }
  (* [comment removed for export] *)
  destruct (SZQW _ _ _ _ _ _ _ BI3 W3QR) as (SZQ3 & SZX3).
  pose proof OBQ3 as (Q03 & _ & Q83 & _). cbn [L5.bo_fb L5.bo_len] in Q03, Q83. change (Z.of_nat 2) with 2 in Q83.
  pose proof HST3 as (SP3 & _ & _).
  eapply (L5ADVHL2.h1 L ar C HI LY HIok) with (qo := qo) (fq := 0) (lenq := 2); try first [exact G | exact ER | exact EA];
    [exact BI3 | exact RI3 | exact Z18 | exact Z26 | exact (proj1 (SP3 _ _ ltac:(do 9 right; left; reflexivity))) | exact (proj1 (SP3 _ _ ltac:(do 10 right; left; reflexivity)))
     | exact (proj1 (SP3 _ _ ltac:(do 2 right; left; reflexivity))) | exact (proj1 (SP3 _ _ ltac:(do 13 right; left; reflexivity)))
     | exact AOQ | exact SZQ3 | exact Q03 | clear; lia | reflexivity | exact Q83 | clear; lia | ].
  intros fx4 R4 M4 model4 BI4 KS4 h19 h21 h22 h26 AG4 S248_4 S256_4.
  assert (RI4 : rinvD R E R4). { apply (rinvD_ks R E R3 R4 KS_v5H1i RI3 KS4). vm_compute; reflexivity. }
  set (X4 := fun a => E - 136 <= a < E - 120).
  assert (OFF4 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 X4 M3 M4). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG4. exact Ha. exact NX. }
  assert (HST4 : hst M4 cells bn bd (on_of g2) (on_of g1)).
  { eapply hst_keepx. exact HST3. exact OFF4.
    - intros a v Hin i Hi X. unfold X4 in X. unfold cells in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Eq|Hin]; [injection Eq as Ea _; clear - Ea Hi X; lia | ]). destruct Hin.
    - intros i Hi X. unfold X4 in X. clear - Hi X SFB. lia. }
  assert (OBQ4 : L5.big_at RSEGS M4 qo (L5.BO 0 2 (L5.BInl v0 v1))). { eapply qb_keep. exact AOQ. clear - QLO QHI; lia. exact OBQ3. exact OFF4. intros i Hi X. unfold X4 in X. clear - Hi X QFR. lia. }
  assert (SPQ4 : spl E M4 [(E - 136, qo + 16); (E - 128, 2)]).
  { intros a v Hin. cbn [In] in Hin. destruct Hin as [Eq|[Eq|[]]]; injection Eq as <- <-; (split; [|clear; lia]). exact S248_4. exact S256_4. }
  (* [comment removed for export] *)
  assert (TX4 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M4 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOX | exact TX | ]. apply XOW. exact W3Q. }
  pose proof (proj1 TX4) as (_ & _ & _ & (_ & X16_4 & X24_4 & _ & X0R & X1R)). cbn [L5.bo_st bx] in X16_4, X24_4, X0R, X1R.
  destruct (SZQW _ _ _ _ _ _ _ BI4 W3QR) as (SZQ4 & SZX4).
  destruct HST4 as (SP4 & ON4 & OD4).
  eapply (L5ADVHL2.hl L ar C HI LY HIok) with (last := false) (to := ro) (qo := qo) (d0 := d0) (tw := x1) (lenq := 2); try first [exact G | exact ER | exact EA | exact HSCR]; cbn iota;
    [exact BI4 | exact RI4 | rewrite (KS4 18%nat) by inl; exact Z18 | exact h19 | rewrite (KS4 20%nat) by inl; exact Z20 | exact D0R | exact h21 | exact h22 | exact h26
     | exact SSH | exact (NWSH _ W3QR) | exact SC8 | exact AOX | exact SZX4 | exact X24_4 | exact X1R | exact AOQ | exact SZQ4 | clear - APT; lia
     | exact (proj1 (SP4 _ _ ltac:(do 12 right; left; reflexivity))) | exact (proj1 (SP4 _ _ ltac:(do 13 right; left; reflexivity)))
     | exact (proj1 (SPQ4 _ _ ltac:(left; reflexivity))) | exact (proj1 (SPQ4 _ _ ltac:(right; left; reflexivity))) | clear; lia
     | exact (proj1 (SP4 _ _ ltac:(do 6 right; left; reflexivity))) | exact (proj1 (SP4 _ _ ltac:(do 2 right; left; reflexivity)))
     | intros a Ha; apply WROQ; clear - Ha; lia | ].
  intros fx5 R5 M5 model5 BI5 KS5 (i19 & i25) AG5 DF5. cbn iota in KS5.
  set (X5 := fun a => (qo + 24 <= a < qo + 24 + 8) \/ (E - 392 <= a < E - 384)).
  assert (OFF5 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 X5 M4 M5). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG5. exact Ha. all: intros Q; apply NX; unfold X5; clear - Q; lia. }
  assert (NX5 : forall i, SPA <= i < E \/ F + 32 <= i < F + 128 -> ~ X5 i). { intros i Hi [X|X]. apply (QNF i ltac:(clear - X; lia)). exact Hi. clear - Hi X SFB. lia. }
  assert (HST5 : hst M5 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. split; [exact SP4 | split; [exact ON4 | exact OD4]]. exact OFF5. exact NX5. }
  assert (SPQ5 : spl E M5 [(E - 136, qo + 16); (E - 128, 2)]).
  { eapply L5ADVHL.spl_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact SPQ4 | exact OFF5 | ]. intros i Hi. apply NX5. left; exact Hi. }
  destruct (big_inl_upd M4 M5 qo 0 2 v0 v1 24 OBQ4 ltac:(clear - QLO QHI; lia) ltac:(right; reflexivity)) as (v0a & v1a & OBQ5).
  { intros a Ha N1. apply AG5. clear - Ha QLO QHI; lia. exact N1. clear - Ha QCE SLO HSCR; lia. } exact DF5.
  assert (RI5 : rinvD R E R5). { apply (rinvD_ks R E R4 R5 KS_v5HLa RI4 KS5). vm_compute; reflexivity. }
  destruct (SZQW _ _ _ _ _ _ _ BI5 W3QR) as (SZQ5 & SZX5).
  assert (TX5 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M5 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI5 | exact AOX | exact TX | ]. apply XOW. exact W3Q. }
  pose proof (proj1 TX5) as (_ & _ & _ & (_ & X16_5 & _)). cbn [L5.bo_st bx] in X16_5.
  destruct HST5 as (SP5 & ON5 & OD5).
  eapply (L5ADVHL2.hl L ar C HI LY HIok) with (last := true) (to := ro) (qo := qo) (d0 := d0) (tw := x0) (lenq := 2); try first [exact G | exact ER | exact EA | exact HSCR]; cbn iota;
    [exact BI5 | exact RI5 | rewrite (KS5 18%nat) by inl; rewrite (KS4 18%nat) by inl; exact Z18 | exact i19 | rewrite (KS5 20%nat) by inl; rewrite (KS4 20%nat) by inl; exact Z20 | exact D0R | exact I
     | rewrite (KS5 22%nat) by inl; exact h22 | rewrite (KS5 26%nat) by inl; exact h26
     | exact SSH | exact (NWSH _ W3QR) | exact SC8 | exact AOX | exact SZX5 | exact X16_5 | exact X0R | exact AOQ | exact SZQ5 | clear - APT; lia
     | exact (proj1 (SP5 _ _ ltac:(do 12 right; left; reflexivity))) | exact (proj1 (SP5 _ _ ltac:(do 13 right; left; reflexivity)))
     | exact (proj1 (SPQ5 _ _ ltac:(left; reflexivity))) | exact (proj1 (SPQ5 _ _ ltac:(right; left; reflexivity))) | clear; lia
     | exact (proj1 (SP5 _ _ ltac:(do 6 right; left; reflexivity))) | exact (proj1 (SP5 _ _ ltac:(do 2 right; left; reflexivity)))
     | intros a Ha; apply WROQ; clear - Ha; lia | ].
  intros fx6 R6 M6 model6 BI6 KS6 (j1 & j10 & j25) AG6 DF6. cbn iota in KS6.
  set (X6 := fun a => (qo + 16 <= a < qo + 16 + 8) \/ (E - 392 <= a < E - 384)).
  assert (OFF6 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 X6 M5 M6). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG6. exact Ha. all: intros Q; apply NX; unfold X6; clear - Q; lia. }
  assert (HST6 : hst M6 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. split; [exact SP5 | split; [exact ON5 | exact OD5]]. exact OFF6. intros i Hi [X|X]. apply (QNF i ltac:(clear - X; lia)). exact Hi. clear - Hi X SFB. lia. }
  destruct (big_inl_upd M5 M6 qo 0 2 v0a v1a 16 OBQ5 ltac:(clear - QLO QHI; lia) ltac:(left; reflexivity)) as (v0b & v1b & OBQ6).
  { intros a Ha N1. apply AG6. clear - Ha QLO QHI; lia. exact N1. clear - Ha QCE SLO HSCR; lia. } exact DF6.
  assert (RI6 : rinvD R E R6). { apply (rinvD_ks R E R5 R6 KS_v5HLb RI5 KS6). vm_compute; reflexivity. }
  destruct (SZQW _ _ _ _ _ _ _ BI6 W3QR) as (SZQ6 & SZX6).
  assert (V18 : getr R6 (reg 18) = Z_to_bv 64 SH). { rewrite (KS6 18%nat) by inl. rewrite (KS5 18%nat) by inl. rewrite (KS4 18%nat) by inl. exact Z18. }
  assert (V27 : getr R6 (reg 27) = Z_to_bv 64 F). { rewrite (KS6 27%nat) by inl. rewrite (KS5 27%nat) by inl. rewrite (KS4 27%nat) by inl. exact Z27. }
  (* [comment removed for export] *)
  eapply L5ADVHM.red_inl with (o := qo) (pcn := 0x9361c); try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HSCR];
    [exact BI6 | exact RI6 | exact j10 | exact j1 | split; [clear; lia | reflexivity] | exact OBQ6 | exact AOQ | exact SZQ6 | intros a Ha; apply WROQ; clear - Ha; lia | ].
  intros fx7 R7 M7 model7 fq7 nq7 BI7 KS7 k2 k10 AG7 OBQ7 _.
  assert (OFF7 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => (qo <= a < qo + 16) \/ (SPA - 16 <= a < SPA)) M6 M7). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG7. exact Ha. all: intros Q; apply NX; clear - Q; lia. }
  assert (HST7 : hst M7 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. exact HST6. exact OFF7. intros i Hi [X|X]. apply (QNF i ltac:(clear - X; lia)). exact Hi. clear - Hi X SFB. lia. }
  assert (RI7 : rinvD R E R7).
  { destruct RI6 as (Z2 & Z8 & Z9 & Z3 & Z4 & ZSB). split. exact k2. split. rewrite (KS7 8%nat) by inl. exact Z8. split. rewrite (KS7 9%nat) by inl. exact Z9. split. rewrite (KS7 3%nat) by inl. exact Z3.
    split. rewrite (KS7 4%nat) by inl. exact Z4. rewrite (KS7 23%nat) by inl. exact ZSB. }
  (* [comment removed for export] *)
  pose proof HST7 as (SP7 & _ & _).
  eapply L5ADVHM.h3; try first [exact LY | exact HIok | exact G | exact ER | exact EA];
    [exact BI7 | exact RI7 | rewrite (KS7 18%nat) by inl; exact V18 | exact (proj1 (SP7 _ _ ltac:(do 8 right; left; reflexivity))) | exact (proj1 (SP7 _ _ ltac:(do 4 right; left; reflexivity))) | clear - XLO XHI; lia | ].
  intros fx8 R8 M8 model8 nh dh BI8 KS8 l1 l10 l11 l19 l20 l22 AG8 OBT8 NH8 SZT8.
  assert (OFF8 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => (SH + 44 <= a < SH + 48) \/ (F + 352 <= a < F + 384)) M7 M8). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG8. exact Ha. all: intros Q; apply NX; clear - Q; lia. }
  assert (HST8 : hst M8 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. exact HST7. exact OFF8. intros i Hi X. clear - Hi X SFB SHQ FBIG ER FRP. lia. }
  assert (OBQ8 : L5.big_at RSEGS M8 qo (L5.BO fq7 nq7 (L5.BInl v0b v1b))). { eapply qb_keep. exact AOQ. clear - QLO QHI; lia. exact OBQ7. exact OFF8. intros i Hi X. clear - Hi X QF QSH. lia. }
  assert (RI8 : rinvD R E R8). { apply (rinvD_ks R E R7 R8 KS_v5H3 RI7 KS8). vm_compute; reflexivity. }
  destruct (SZQW _ _ _ _ _ _ _ BI8 W3QR) as (SZQ8 & SZX8).
  assert (TX8 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M8 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI8 | exact AOX | exact TX | ]. apply XOW. exact W3Q. }
  pose proof OBX as (_ & _ & _ & (XBT & _)). cbn [L5.bo_fb] in XBT.
  pose proof OBT8 as (_ & _ & _ & (_ & _ & _ & _ & DHR & _)). cbn [L5.bo_st] in DHR.
  (* [comment removed for export] *)
  eapply L5ADVEA.assign_stage with (W1 := [(ro, 32); (qo, 32)]) (o := ro) (k := 352) (pcn := 0x93660) (b := bx) (b' := L5.BO 0 nh (L5.BInl dh 0)) (ws' := firstn nh [dh; 0]);
    try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4 | exact HSCR | exact FFR1 | exact FFRS | exact Hasg];
    [exact BI8 | exact RI8 | exact l10 | exact l11 | exact l1 | split; [clear; lia | reflexivity] | clear; lia | clear; lia | reflexivity | exact (proj1 TX8) | exact AOX | exact SZX8 | exact OBT8 | | exact SZT8
     | cbn [L5.bo_len]; clear - NH8; lia | intros DY; exfalso; unfold L5.bo_dyn, bx in DY; cbn [L5.bo_fb] in DY; rewrite XBT in DY; discriminate DY | intros N3; exfalso; cbn [L5.bo_len] in N3; clear - N3 NH8; lia
     | intros cap q Eq; discriminate Eq | intros cap q Eq; discriminate Eq | intros c0 q c' q' Eq; discriminate Eq | | ].
  { split. cbn [L5.bo_len]. destruct nh as [|[|nh']]; [reflexivity | reflexivity | exfalso; clear - NH8; lia]. split. destruct nh as [|[|nh']]; cbn [firstn]; [constructor | constructor; [exact DHR | constructor] | exfalso; clear - NH8; lia]. reflexivity. }
  { intros a O. split. intros rr [<-|[]] IR. apply (O (qo, 32)). right; left; reflexivity. exact IR.
    intros rr [<-|[<-|[]]] IR; unfold L5.in_rng in IR; cbn [fst snd L5.bo_data L5.bo_st L5.bo_len bx] in IR; apply (O (ro, 32)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; exact IR | left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - IR NH8; lia]. }
  intros fx9' R9' M9' model9' g9 LBn9 cr9' LK9' A9' POST9 BI9' IA9 ILK9.
  destruct g9 as [|q9 cap9]. 2:{ exfalso. destruct POST9 as (_ & _ & (_ & N3 & _)). cbn [L5.bo_len] in N3. clear - N3 NH8. lia. }
  destruct POST9 as (RP9 & _ & (_ & _ & ECR9 & (st9 & OBR9 & _ & SST9) & AH9)). subst cr9'. cbn [bx L5.bo_fb L5.bo_st L5.bo_len] in OBR9, SST9.
  destruct st9 as [r0 r1|? ?]. 2: destruct SST9.
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F _ ASSIGN_SCR _ M8 M9' AH9) as OFF9.
  assert (NX9 : forall i, L5ADVEA.inW [(ro, 32); (L5.bo_data ro bx, 8 * Z.of_nat (L5.bo_len (L5.BO 0 nh (L5.BInl dh 0))))] i -> ro <= i < ro + 32).
  { intros i (rr & [Er|[Er|[]]] & IR); subst rr; unfold L5.in_rng in IR; cbn [fst snd L5.bo_data L5.bo_st L5.bo_len bx] in IR; clear - IR NH8; lia. }
  assert (HST9 : hst M9' cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. exact HST8. exact OFF9. intros i Hi X. apply (XNF i (NX9 i X)). exact Hi. }
  assert (OBQ9 : L5.big_at RSEGS M9' qo (L5.BO fq7 nq7 (L5.BInl v0b v1b))). { eapply qb_keep. exact AOQ. clear - QLO QHI; lia. exact OBQ8. exact OFF9. intros i Hi X. pose proof (NX9 i X) as Y. clear - Hi Y APT. lia. }
  assert (T09 : L5.u8_at RSEGS M9' (F + 352) 0).
  { destruct OBT8 as (T08 & _). cbn [L5.bo_fb] in T08. eapply L5C.u8_at_agree. 4: exact T08. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFF9. clear - Hi FRP; lia.
    apply (fframe_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia. intros X. pose proof (NX9 i X) as Y. clear - Hi Y XF. lia. }
  assert (W9QR : forall rr, In rr [(ro, 32); (qo, 32)] -> rr = (qo, 32) \/ rr = (ro, 32)) by (intros rr [<-|[<-|[]]]; [right | left]; reflexivity).
  destruct (SZQW _ _ _ _ _ _ _ BI9' W9QR) as (SZQ9 & SZX9).
  assert (RI9' : rinvD R E R9') by (apply (rinvD_pres R E R8 R9' RI8 RP9)).
  destruct HST9 as (SP9 & ON9' & OD9'). unfold bx12 in BI9'.
  assert (SP9h : spl E M9' [(E - 296, qo); (E - 304, F + 32); (E - 320, qo / 8 + 2147450880); (E - 312, qn); (E - 288, ro); (E - 328, bits)]).
  { intros a v Hin. apply SP9. unfold cells. cbn [In] in Hin |- *. destruct Hin as [Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[]]]]]]]; rewrite <- Eq; clear; tauto. }
  eapply L5ADVHM.h4_tail with (qo := qo) (qn := qn) (bits := bits) (f0 := 0) (BXf := []);
    try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4 | exact HSCR | exact Hdel | exact RA | exact UR1 | exact G2];
    [exact BI9' | | exact RI9'
     | rewrite (cs_of_preserved R8 R9' 18 RP9) by inl; rewrite (KS8 18%nat) by inl; rewrite (KS7 18%nat) by inl; exact V18
     | rewrite (cs_of_preserved R8 R9' 19 RP9) by inl; exact l19 | rewrite (cs_of_preserved R8 R9' 20 RP9) by inl; exact l20 | rewrite (cs_of_preserved R8 R9' 22 RP9) by inl; exact l22
     | rewrite (cs_of_preserved R8 R9' 25 RP9) by inl; rewrite (KS8 25%nat) by inl; rewrite (KS7 25%nat) by inl; exact j25
     | rewrite (cs_of_preserved R8 R9' 27 RP9) by inl; rewrite (KS8 27%nat) by inl; rewrite (KS7 27%nat) by inl; exact V27
     | exact T09 | clear; lia | reflexivity | exact SP9h | exact QNR | exact BITS | exact ON9' | exact OD9' | exact OBQ9 | exact AOQ | exact SZQ9 | exact OBR9 | exact AOX | exact SZX9 | exact APT | ].
  { intros a [Ha|Ha] O. apply (O (qo, 32)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - Ha; lia. apply (O (ro, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - Ha; lia. }
  intros fxf Rf Mf modelf Af RPf IAf AHf OBQf OBRf RTf AMf HHf.
  apply (KF fxf Rf Mf modelf Af LK9' RPf).
  - intros x Hx. apply IAf. apply IA9. apply IA3. exact Hx.
  - intros x Hx. apply ILK3. apply ILK9. exact Hx.
  - exact AHf.
  - eexists _, _, _, _. exact OBQf.
  - eexists _, _, _, _. split. exact OBRf. subst bits. rewrite Z.lor_0_r. rewrite Z.land_spec. change (Z.testbit 253 1) with false. apply andb_false_r.
  - exact RTf.
  - exact AMf.
  - exact HHf.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVHP.

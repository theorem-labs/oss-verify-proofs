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
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivPH L5ADivPL L5ADivE L5ADivEA L5ADivHC L5ADivHD L5ADivHA L5ARed L5ADivHL L5ADivHM L5ADivHN L5ADivHH L5ADivHO L5DivSpecsA L5DivInnerSpecsA L5OpmodSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHP.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADIVPL. Import L5ADVHL. Import L5ADVHM. Import L5ADVHN. Import L5ADVHH. Import L5ADVHO.
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
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
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
Lemma qb_keep LBx scr (X : Z -> Prop) Mc M1 qo bq : aobj FF qo 32 -> 4096 <= qo <= 140737488355296 -> L5.big_at RSEGS Mc qo bq ->
  L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall i, qo <= i < qo + 32 -> ~ X i) -> L5.big_at RSEGS M1 qo bq.
Proof.
  intros AOQ QR OB OFF NX. eapply L5C.big_at_agree. 4: exact OB. 2: clear - QR; lia. 2: clear - QR; lia. intros i Hi. apply OFF. clear - Hi QR; lia.
  apply (obj_client L ar LBx FF' SPA scr qo 32 i). apply aobj_cons. exact AOQ. exact Hi. apply NX. exact Hi.
Qed.
Lemma big_inl_upd (Mc M1 : word -> option byte) o fb n v0 v1 k : L5.big_at RSEGS Mc o (L5.BO fb n (L5.BInl v0 v1)) -> 4096 <= o <= 140737488355296 -> (k = 16 \/ k = 24) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (o + k <= a < o + k + 8) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5.defined M1 (o + k) 8 ->
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
  L5.big_at RSEGS M ro (L5.BO fbx 2 (L5.BInl x0 x1)) -> aobj FF ro 32 -> shadow_zero M ro 4 ->
  L5.bo_len bn = 2%nat -> L5.bo_dyn bn = false -> L5.bo_len bd = 1%nat -> L5.bo_st bd = L5.BInl d0 d1 -> 0 <= d0 <= 4294967295 ->
  L5.big_at RSEGS M qo (L5.BO 0 0 (L5.BInl 0 0)) -> aobj FF qo 32 -> shadow_zero M qo 4 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  (forall (fxf : FPState) Rf Mf modelf Af LKf,
      regs_preserved R Rf -> incl A9 Af -> incl LKf LK9 -> ahpres L ar LB FF E SCRD [(ro, 32); (qo, 32)] M Mf ->
      (exists fq nq q0 q1, L5.big_at RSEGS Mf qo (L5.BO fq nq (L5.BInl q0 q1))) ->
      (exists fr nr r0 r1, L5.big_at RSEGS Mf ro (L5.BO fr nr (L5.BInl r0 r1)) /\ Z.testbit fr 1 = false) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI LB FF LKf cr9 Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92374 M9 model9) K.
Proof.
  intros (BI9 & RIH9 & c10 & c19 & c20 & c22 & c24 & c26 & QNR & BITS & TN9 & TD9 & ON9 & OD9 & SGN & SGD & S88 & S48 & S104 & S144 & S64 & DSH9 & HDR9) CR BZ OBX AOX SZX LN2 DYN LD1 STD D0R OBQ AOQ SZQ APT KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof RIH9 as (RI9 & X18 & X23 & X27 & X25).
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
  assert (SHW : forall o o2, 0x633000 <= o -> o + 32 <= 2 ^ 47 -> (0x7fff7000 + 17592186048512 <= o2 \/ o2 + 32 <= 0x7fff7000) -> 0x633000 <= o2 -> forall j, 0 <= j < 4 -> ~ (o2 <= o / 8 + SB + j < o2 + 32)).
  { intros o o2 H1 H2 H3 H4 j Hj. unfold SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - H1 H2 H3 H4 Hj. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  pose proof (proj1 TN9) as OBN9. pose proof (proj1 TD9) as OBD9.
  assert (TX9 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M9 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI9 | exact AOX | exact TX | ]. intros a _ rr []. }
  eapply L5ADVHN.p4n with (toHT := true) (bn := bn) (bt := bx) (lend := Z.of_nat (L5.bo_len bd)) (qo := qo) (qn := qn) (c := c) (to := ro); try first [exact LY | exact HIok | exact G | exact ER | exact EA];
    [exact BI9 | exact RI9 | exact X27 | exact c10 | exact CR | exact c19 | exact c20 | exact c22 | exact QNR | exact c24 | exact S104 | exact S144 | clear - QLO QHI; lia
     | exact OBN9 | exact (proj1 TX9) | exact AOX | exact (proj1 (proj2 (proj2 TX9))) | | split; [rewrite LD1; reflexivity | rewrite LN2; clear; lia] | ].
  { rewrite DYN. unfold L5.bo_dyn, bx. cbn [L5.bo_fb]. destruct OBX as (_ & _ & _ & (BT & _)). cbn [L5.bo_fb] in BT. rewrite BT. reflexivity. }
  intros fx1 R1 M1 model1 BI1 KS1 p10 p11 p21 p22 p24 p27 AG1 S80_1 S40_1 S56_1. cbn iota.
  assert (OFF1 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => (E - 272 <= a < E - 264) \/ (E - 312 <= a < E - 304) \/ (E - 296 <= a < E - 288)) M9 M1).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. all: intros Q; apply NX; clear - Q; lia. }
  assert (KPS : forall a v, E - 352 <= a -> a + 8 <= E -> (a + 8 <= E - 312 \/ E - 288 <= a) -> (a + 8 <= E - 272 \/ E - 264 <= a) -> L5.u64_at RSEGS M9 a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 H3 H4 Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia. intros i Hi. apply AG1. clear - Hi H1 H2 ER; lia. all: clear - Hi H3 H4; lia. }
  set (cells := [(E - 272, F + 96); (E - 248, qo); (E - 312, qn); (E - 264, F + 32); (E - 288, bits)]).
  assert (SP1 : spl E M1 cells).
  { intros a v Hin. subst cells. cbn [In] in Hin. destruct Hin as [Eq|[Eq|[Eq|[Eq|[Eq|[]]]]]]; injection Eq as <- <-; (split; [|clear; lia]).
    exact S80_1. apply KPS; [clear; lia | clear; lia | right; clear; lia | right; clear; lia | exact S104]. exact S40_1.
    apply KPS; [clear; lia | clear; lia | right; clear; lia | right; clear; lia | exact S88]. apply KPS; [clear; lia | clear; lia | right; clear; lia | left; clear; lia | exact S64]. }
  assert (KPF : forall i, F <= i < F + 512 \/ SH <= i < SH + 64 -> M1 (Z_to_bv 64 i) = M9 (Z_to_bv 64 i)).
  { intros i Hi. apply AG1. clear - Hi FRP SHQ; lia. all: clear - Hi SFB SHQ ER; lia. }
  assert (ON1 : obj_at M1 (F + 96) bn (on_of g2)). { apply (obj_at_agree M9 M1 _ _ _ ON9 ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KPF. left; clear - Hi; lia. }
  assert (OD1 : obj_at M1 (F + 32) bd (on_of g1)). { apply (obj_at_agree M9 M1 _ _ _ OD9 ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KPF. left; clear - Hi; lia. }
  assert (TQ1 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M1 qo bq0 []). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI1 | exact AOQ | exact TQ | ]. intros a _ rr []. }
  assert (TX1 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M1 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI1 | exact AOX | exact TX | ]. intros a _ rr []. }
  assert (HST1 : hst M1 cells bn bd (on_of g2) (on_of g1)) by (split; [exact SP1 | split; [exact ON1 | exact OD1]]).
  assert (RI1 : rinvD R E R1). { apply (rinvD_ks R E R9 R1 KSP4 RI9 KS1). vm_compute; reflexivity. }
  assert (SHD1 : shr8 M1 F 4 4 0).
  { destruct DSH9 as (_ & D4 & _). intros j Hj. eapply L5C.u8_at_agree. 4: exact (D4 j Hj). 2: unfold SB; clear - Hj SHQ; lia. 2: unfold SB; clear - Hj SHQ; lia.
    intros i Hi. apply KPF. right. unfold SB in Hi. clear - Hi Hj. lia. }
  assert (D01 : L5.u64_at RSEGS M1 (F + 48) d0).
  { destruct OD1 as (OBD1 & _). destruct OBD1 as (_ & _ & _ & ST). rewrite STD in ST. destruct ST as (_ & D16 & _). replace (F + 48) with (F + 32 + 16) by (clear; lia). exact D16. }
  assert (Y26 : getr R1 (reg 26) = Z_to_bv 64 (F + 48)). { rewrite (KS1 26%nat) by inl. rewrite c26. unfold L5.bo_data. rewrite STD. f_equal. clear; lia. }
  pose proof (proj1 TX1) as (_ & _ & XL8 & _). cbn [L5.bo_len] in XL8. change (Z.of_nat 2) with 2 in XL8.
  eapply L5ADVHL.ht with (toG := false) (to := ro) (qo := qo) (d0 := d0) (lent := 2); try first [exact LY | exact HIok | exact G | exact ER | exact EA];
    [exact BI1 | exact RI1 | exact p10 | exact p22 | exact Y26 | exact S56_1 | exact SHD1 | exact D01 | exact D0R | exact AOX | exact (proj1 (proj2 (proj2 TX1))) | exact XL8 | clear; lia | clear - QLO QHI; lia | ].
  intros fx2 R2 model2' BI2 KS2 q23 (q1 & q10 & q11 & q24 & q27). cbn iota in KS2 |- *.
  assert (RI2 : rinvD R E R2). { apply (rinvD_ks R E R1 R2 KS_v5HTh RI1 KS2). vm_compute; reflexivity. }
  (* [comment removed for export] *)
  eapply L5ADVHH.resize_stage with (W1 := [(qo, 32)]) (o := qo) (n := 2%nat) (b := bq0) (ws := []) (pcn := 0x926b0); try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4 | exact HSCR | exact FFR1 | exact FFRS | exact Hrsz];
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
  (* [comment removed for export] *)
  destruct (SZQW _ _ _ _ _ _ _ BI3 W3QR) as (SZQ3 & SZX3).
  pose proof OBQ3 as (Q03 & _). cbn [L5.bo_fb] in Q03.
  eapply L5ADVHL.h1 with (to := ro) (qo := qo) (fq := 0); try first [exact LY | exact HIok | exact G | exact ER | exact EA];
    [exact BI3 | exact RI3 | rk | rk | rk | exact AOQ | exact SZQ3 | exact Q03 | clear; lia | reflexivity | clear - XLO XHI; lia | ].
  intros fx4 R4 model4 BI4 KS4 h10 h11 h12 h20 h21 h22 h26.
  assert (RI4 : rinvD R E R4). { apply (rinvD_ks R E R3 R4 KS_v5H1i RI3 KS4). vm_compute; reflexivity. }
  (* [comment removed for export] *)
  assert (TX4 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M3 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOX | exact TX | ]. apply XOW. exact W3Q. }
  pose proof (proj1 TX4) as (_ & _ & _ & (_ & X16_4 & X24_4 & _ & X0R & X1R)). cbn [L5.bo_st bx] in X16_4, X24_4, X0R, X1R.
  destruct HST3 as (SP3 & ON3 & OD3).
  eapply L5ADVHL.hl with (last := false) (to := ro) (qo := qo) (d0 := d0) (tw := x1); try first [exact LY | exact HIok | exact G | exact ER | exact EA]; cbn iota;
    [exact BI4 | exact RI4 | exact h10 | exact h11 | exact h12 | exact h21 | exact h22 | rk | exact D0R | rk | exact h26 | exact AOX | exact SZX3 | exact X24_4 | exact X1R | exact AOQ | exact SZQ3
     | clear - APT; lia | exact (proj1 (SP3 _ _ ltac:(right; left; reflexivity))) | intros a Ha; apply WROQ; clear - Ha; lia | ].
  intros fx5 R5 M5 model5 BI5 KS5 (i10 & i11 & i12 & i21 & i24) AG5 DF5. cbn iota in KS5.
  assert (OFF5 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => qo + 24 <= a < qo + 24 + 8) M3 M5). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG5. exact Ha. exact NX. }
  assert (HST5 : hst M5 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. split; [exact SP3 | split; [exact ON3 | exact OD3]]. exact OFF5. intros i Hi X. apply (QNF i ltac:(clear - X; lia)). exact Hi. }
  destruct (big_inl_upd M3 M5 qo 0 2 v0 v1 24 OBQ3 ltac:(clear - QLO QHI; lia) ltac:(right; reflexivity) AG5 DF5) as (v0a & v1a & OBQ5).
  assert (RI5 : rinvD R E R5). { apply (rinvD_ks R E R4 R5 KS_v5HLa RI4 KS5). vm_compute; reflexivity. }
  destruct (SZQW _ _ _ _ _ _ _ BI5 W3QR) as (SZQ5 & SZX5).
  assert (TX5 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M5 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI5 | exact AOX | exact TX | ]. apply XOW. exact W3Q. }
  pose proof (proj1 TX5) as (_ & _ & _ & (_ & X16_5 & _)). cbn [L5.bo_st bx] in X16_5.
  destruct HST5 as (SP5 & ON5 & OD5).
  eapply L5ADVHL.hl with (last := true) (to := ro) (qo := qo) (d0 := d0) (tw := x0); try first [exact LY | exact HIok | exact G | exact ER | exact EA]; cbn iota;
    [exact BI5 | exact RI5 | exact i10 | exact i11 | exact i12 | exact i21 | exact I | rk | exact D0R | exact i24 | rk | exact AOX | exact SZX5 | exact X16_5 | exact X0R | exact AOQ | exact SZQ5
     | clear - APT; lia | exact (proj1 (SP5 _ _ ltac:(right; left; reflexivity))) | intros a Ha; apply WROQ; clear - Ha; lia | ].
  intros fx6 R6 M6 model6 BI6 KS6 (j1 & j10) AG6 DF6. cbn iota in KS6.
  assert (OFF6 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => qo + 16 <= a < qo + 16 + 8) M5 M6). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG6. exact Ha. exact NX. }
  assert (HST6 : hst M6 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. split; [exact SP5 | split; [exact ON5 | exact OD5]]. exact OFF6. intros i Hi X. apply (QNF i ltac:(clear - X; lia)). exact Hi. }
  destruct (big_inl_upd M5 M6 qo 0 2 v0a v1a 16 OBQ5 ltac:(clear - QLO QHI; lia) ltac:(left; reflexivity) AG6 DF6) as (v0b & v1b & OBQ6).
  assert (RI6 : rinvD R E R6). { apply (rinvD_ks R E R5 R6 KS_v5HLb RI5 KS6). vm_compute; reflexivity. }
  destruct (SZQW _ _ _ _ _ _ _ BI6 W3QR) as (SZQ6 & SZX6).
  (* [comment removed for export] *)
  eapply L5ADVHM.red_inl with (o := qo) (pcn := 0x92b70); try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HSCR];
    [exact BI6 | exact RI6 | exact j10 | exact j1 | split; [clear; lia | reflexivity] | exact OBQ6 | exact AOQ | exact SZQ6 | intros a Ha; apply WROQ; clear - Ha; lia | ].
  intros fx7 R7 M7 model7 fq7 nq7 BI7 KS7 k2 k10 AG7 OBQ7 _.
  assert (OFF7 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => (qo <= a < qo + 16) \/ (SPA - 16 <= a < SPA)) M6 M7). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG7. exact Ha. all: intros Q; apply NX; clear - Q; lia. }
  assert (HST7 : hst M7 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. exact HST6. exact OFF7. intros i Hi [X|X]. apply (QNF i ltac:(clear - X; lia)). exact Hi. clear - Hi X SFB. lia. }
  assert (RI7 : rinvD R E R7).
  { destruct RI6 as (Z2 & Z8 & Z9 & Z3 & Z4). split. exact k2. split. rewrite (KS7 8%nat) by inl. exact Z8. split. rewrite (KS7 9%nat) by inl. exact Z9. split. rewrite (KS7 3%nat) by inl. exact Z3. rewrite (KS7 4%nat) by inl. exact Z4. }
  (* [comment removed for export] *)
  eapply L5ADVHM.h3; try first [exact LY | exact HIok | exact G | exact ER | exact EA]; [exact BI7 | exact RI7 | rk | clear - XLO XHI; lia | ].
  intros fx8 R8 M8 model8 nh dh BI8 KS8 l1 l10 l11 l23 AG8 OBT8 NH8 SZT8.
  assert (OFF8 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 (fun a => (SH + 44 <= a < SH + 48) \/ (F + 352 <= a < F + 384)) M7 M8). { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG8. exact Ha. all: intros Q; apply NX; clear - Q; lia. }
  assert (HST8 : hst M8 cells bn bd (on_of g2) (on_of g1)). { eapply hst_keep. exact HST7. exact OFF8. intros i Hi X. clear - Hi X SFB SHQ FBIG ER FRP. lia. }
  assert (OBQ8 : L5.big_at RSEGS M8 qo (L5.BO fq7 nq7 (L5.BInl v0b v1b))). { eapply qb_keep. exact AOQ. clear - QLO QHI; lia. exact OBQ7. exact OFF8. intros i Hi X. clear - Hi X QF QSH. lia. }
  assert (RI8 : rinvD R E R8). { apply (rinvD_ks R E R7 R8 KS_v5H3 RI7 KS8). vm_compute; reflexivity. }
  destruct (SZQW _ _ _ _ _ _ _ BI8 W3QR) as (SZQ8 & SZX8).
  assert (TX8 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M8 ro bx [x0; x1]). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI8 | exact AOX | exact TX | ]. apply XOW. exact W3Q. }
  pose proof OBX as (_ & _ & _ & (XBT & _)). cbn [L5.bo_fb] in XBT.
  pose proof OBT8 as (_ & _ & _ & (_ & _ & _ & _ & DHR & _)). cbn [L5.bo_st] in DHR.
  (* [comment removed for export] *)
  eapply L5ADVEA.assign_stage with (W1 := [(ro, 32); (qo, 32)]) (o := ro) (k := 352) (pcn := 0x92ba8) (b := bx) (b' := L5.BO 0 nh (L5.BInl dh 0)) (ws' := firstn nh [dh; 0]);
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
  eapply L5ADVHM.h4_tail with (qo := qo) (qn := qn) (bits := bits) (f0 := 0) (BXf := []);
    try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact G4 | exact HSCR | exact Hdel | exact RA | exact UR1 | exact G2];
    [exact BI9' | | exact RI9' | rk | rk | rk | rk | exact T09 | clear; lia | reflexivity | exact SP9 | exact QNR | exact BITS | exact ON9' | exact OD9' | exact OBQ9 | exact AOQ | exact SZQ9 | exact OBR9 | exact AOX | exact SZX9 | exact APT | ].
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

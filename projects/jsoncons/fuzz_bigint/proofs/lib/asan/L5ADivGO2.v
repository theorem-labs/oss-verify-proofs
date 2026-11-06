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
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivHL L5ADivHM L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB L5ADivGC L5ADivGD L5ADivGU L5ARed L5ADivHH L5ADivHS L5ADivGE L5ADivN L5ADivO1 L5ANorm L5ADivGN L5ADivGK L5ARzHuge L5ADivGK2 L5ADivGK3 L5ADivO2 BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO2.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WA : list Z := [L5PSA.A0; L5PSA.A1].
Definition DA : list Z := [0x5abe7036bc514e54; 0xaa7cd8d89cf2abc8; 0].
Lemma clz_A1 : L5DLA.clz_of (nth_w WA (2 - 1)) = 2. Proof. vm_compute. reflexivity. Qed.
Lemma A1_top : nth_w WA (2 - 1) <> 0 /\ nth_w WA (2 - 1) < 2 ^ 63. Proof. cbn. unfold L5PSA.A1. split; Lia.lia. Qed.
Lemma WA_ok : words_ok WA. Proof. unfold words_ok, WA, L5PSA.A0, L5PSA.A1. repeat constructor; Lia.lia. Qed.
Lemma shl_WA : L5DLA.shl_result WA 2 = DA. Proof. vm_compute. reflexivity. Qed.
Lemma second_WA : L5DLA.second 2 (L5DLA.shl_result WA 2) = false. Proof. vm_compute. reflexivity. Qed.
Lemma norm_WA : L5DLA.norm_words WA 2 false = DA. Proof. unfold L5DLA.norm_words. rewrite shl_WA. reflexivity. Qed.
Lemma rlen_DA : rlen DA = 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma DA_1 : 2 ^ 63 <= nth_w DA 1 < 2 ^ 64. Proof. cbn. split; Lia.lia. Qed.

Lemma shl_top_small ws k : words_ok ws -> (1 <= length ws)%nat -> 0 < k < 64 -> 0 <= nth_w (shl_words ws k) (length ws) < 2 ^ k.
Proof.
  intros W L0 Hk. rewrite shl_words_nth by Lia.lia.
  assert (WO: BigFactsBase.words_ok (ws ++ [0])). { apply (proj1 (words_ok_BF _)). apply words_ok_app. exact W. constructor. Lia.lia. constructor. }
  destruct (BigFactsOps.shlG_val k Hk (ws ++ [0]) (length ws) WO) as [E0 _]. rewrite E0.
  assert (NL: BigModel.nth_w (ws ++ [0]) (length ws) = 0).
  { unfold BigModel.nth_w. rewrite app_nth2 by Lia.lia. rewrite Nat.sub_diag. reflexivity. }
  rewrite NL. unfold BigModel.W.shl, BigModel.W.wrap. rewrite Z.mul_0_l, Z.mod_0_l by (pose proof BigFactsBase.M_pos; Lia.lia).
  destruct (Nat.ltb_spec 0 (length ws)). 2: Lia.lia.
  assert (WL: 0 <= BigModel.nth_w (ws ++ [0]) (length ws - 1) < 2 ^ 64).
  { unfold BigModel.nth_w. rewrite app_nth1 by Lia.lia. apply (words_ok_nth ws). exact W. }
  split. apply Z.add_nonneg_nonneg. Lia.lia. apply Z.div_pos. Lia.lia. apply Z.pow_pos_nonneg; Lia.lia.
  rewrite Z.add_0_l. apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; Lia.lia.
  rewrite <- Z.pow_add_r by Lia.lia. replace (64 - k + k) with 64 by Lia.lia. Lia.lia.
Qed.
Lemma rlen_shl_bounds ws k : words_ok ws -> (1 <= length ws)%nat -> nth_w ws (length ws - 1) <> 0 -> 0 < k < 64 ->
  (length ws <= rlen (shl_words ws k) <= Datatypes.S (length ws))%nat.
Proof.
  intros W L0 T Hk. split.
  - assert (RL: rlen ws = length ws). { apply rlen_charact. Lia.lia. intros i Hi. Lia.lia. right. exact T. }
    rewrite <- RL at 1. apply L5WB.rlen_mono. exact W. apply shl_words_ok. exact Hk. exact W.
    rewrite shl_words_val by assumption. pose proof (BigFactsBase.val_nonneg ws (proj1 (words_ok_BF _) W)).
    assert (1 <= 2 ^ k). { change 1 with (2 ^ 0). apply Z.pow_le_mono_r; Lia.lia. } Lia.nia.
  - rewrite <- (shl_words_length ws k). apply rlen_le.
Qed.
Lemma shl_grown_top ws k : words_ok ws -> (1 <= length ws)%nat -> 0 < k < 64 ->
  rlen (shl_words ws k) = Datatypes.S (length ws) -> nth_w (shl_words ws k) (rlen (shl_words ws k) - 1) < 2 ^ k.
Proof. intros W L0 Hk E0. rewrite E0. replace (Datatypes.S (length ws) - 1)%nat with (length ws) by Lia.lia. apply shl_top_small; assumption. Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sh_rng j : SH <= j < SH + 64 -> 2147450880 <= j < 17594333495296.
Proof.
  intros Hj. pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as (_ & FRP & _ & ALF & _). hnf in ALF.
  clear - Hj FRP ALF. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma u8_inj Mk a b b' : L5.u8_at RSEGS Mk a b -> L5.u8_at RSEGS Mk a b' -> 0 <= b < 256 -> 0 <= b' < 256 -> b = b'.
Proof.
  unfold L5.u8_at. intros H1 H2 B1 B2. rewrite H1 in H2. assert (E2 : Z_to_bv 8 b = Z_to_bv 8 b') by congruence. clear H2. pose proof (f_equal bv_unsigned E2) as H2. rewrite !Z_to_bv_unsigned in H2.
  rewrite !bv_wrap_small in H2. exact H2. all: change (2 ^ Z.of_N 8) with 256; assumption.
Qed.
Lemma after_sgn M' o b rw g st' fb' n' st2 : L5DLA.obj_after M' o b rw g st' -> L5.big_at RSEGS M' o (L5.BO fb' n' st2) -> Z.testbit (L5.bo_fb b) 1 = false -> Z.testbit fb' 1 = false.
Proof.
  intros (_ & _ & OB & _) (U8 & FR & _) SG. cbv zeta in OB. destruct OB as (U8' & FR' & _). cbn [L5.bo_fb] in *.
  rewrite (u8_inj M' o _ _ U8 U8' FR FR').
  assert (X : Z.testbit (match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end) 1 = false). { destruct g. exact SG. rewrite Z.lor_spec, SG. reflexivity. }
  destruct (Nat.eqb _ 0). rewrite Z.land_spec, X. reflexivity. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma go2_front (cr0 : credit) (qo : Z) (wy : list Z) (fx1 : FPState) g2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd :
  ri_inv HI LB FF LK cr0 A M (vml_of model) -> L5OMA.stksh ar M (E - SCRD) ->
  0 <= ro < 2 ^ 64 -> 0 <= qo < 2 ^ 64 ->
  (2 <= L5.bo_len bn)%nat -> L5.bo_cap bn <= 268 -> nth_w wy (L5.bo_len bn - 1) <> 0 ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> g2 = Grown q cap /\ Z.of_nat (L5.bo_len bn) + 1 <= cap) ->
  L5OMA.acredit_for L cr1 3 (8 * L5.bo_cap bn + 144) ->
  atG L ar HI R M model LB FF LK A E SCRD F ro Same g2 R1 M1 model1 cr1 LK1 A1 ro qo qn bits 1 bn bd wy WA ->
  L5.bo_len bd = 2%nat -> L5.bo_st bd = L5.BInl L5PSA.A0 L5PSA.A1 ->
  (forall (fx4 : FPState) R4 M4 model4 (gn0 gn : growth) qd bn0 bd0 fbd' fbn' stn cr4 LK4 A4,
      let rn := shl_words wy 2 in
      let BX4 := L5DLA.blocks_of gn ++ (qd, 8 * 8) :: L5DLA.blocks_of gn0 ++ L5ADVHO.bx12 Same g2 in
      binv [] BX4 M4 model4 LK4 cr4 A4 -> rinvD R E R4 ->
      (forall x, In x [18; 22; 24; 25; 26]%nat -> getr R4 (reg x) = getr R1 (reg x)) ->
      getr R4 (reg 19) = Z_to_bv 64 (F + 32) -> getr R4 (reg 20) = Z_to_bv 64 (F + 96) -> getr R4 (reg 23) = Z_to_bv 64 ro ->
      getr R4 (reg 1) = Z_to_bv 64 0x92758 -> getr R4 (reg 10) = Z_to_bv 64 qo -> getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat (rlen rn) - 2) ->
      getr R4 (reg 21) = Z_to_bv 64 2147450880 -> getr R4 (reg 27) = Z_to_bv 64 (Z.of_nat (rlen rn)) ->
      tob (BX4 ++ LB) M4 (F + 32) (L5.BO fbd' 2 (L5.BDyn 8 qd)) (firstn 2 DA) ->
      tob (BX4 ++ LB) M4 (F + 96) (L5.BO fbn' (rlen rn) stn) (firstn (rlen rn) rn) ->
      gro_st gn bn stn -> (match stn with L5.BDyn cap _ => Z.of_nat (length rn) <= cap | L5.BInl _ _ => (length rn <= 2)%nat end) ->
      (match gn0 with Same => L5.bo_dyn bn = false | Grown _ cap => cap = L5.bo_cap bn /\ L5.bo_dyn bn = true end) ->
      L5ADVD.obj_at M4 (SPA + 216) bn0 (L5ADVHO.on_of gn0) -> L5ADVD.obj_at M4 (SPA + 184) bd0 None ->
      spl E M4 [(E - 264, F + 32); (E - 304, 1); (E - 248, qo); (E - 208, ro); (E - 288, bits); (E - 272, F + 96); (E - 312, qn); (E - 296, F)] ->
      L5.u64_at RSEGS M4 (E - 336) 0 -> L5.u64_at RSEGS M4 (E - 224) qd -> L5.u64_at RSEGS M4 (E - 216) 2 -> L5.u64_at RSEGS M4 F 1102416563 ->
      dsh M4 F 0 248 248 248 248 ->
      L5.u32_at RSEGS M4 (E - 172) 2 ->
      Z.testbit fbn' 1 = false ->
      cr4 = L5DLA.adebl L (L5DLA.adebl L cr1 (L5DLA.blocks_of gn0)) (L5DLA.blocks_of gn ++ [(qd, 8 * 8)]) -> incl A1 A4 -> incl LK4 LK1 ->
      srealizes RSEGS SCFG (cfg (fx:=fx4) R4 RESIZE M4 model4) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K.
Proof.
  intros HH0 SSH ROR QOR LENB CAPB TOPY DYNY CRD (BI0 & RI0 & X18 & X22 & X24 & X25 & X26 & QNR & BITSR & TN & TD & ON & OD & SGN_N & SGN_D & SPL & DSH & HDR) LND STD KF.
  set (BX0 := L5ADVHO.bx12 Same g2) in *.
  set (cells := [(E - 264, F + 32); (E - 304, 1); (E - 248, qo); (E - 208, ro); (E - 288, bits); (E - 272, F + 96); (E - 312, qn); (E - 296, F)]) in *.
  assert (CAPD : L5.bo_cap bd = 2) by (unfold L5.bo_cap; rewrite STD; reflexivity).
  assert (DYD : L5.bo_dyn bd = false). { destruct TD as ((_ & _ & _ & OST) & _). rewrite STD in OST. exact (proj1 OST). }
  pose proof (len_le_cap M1 (F + 96) bn (proj1 TN)) as LLC. fold (L5.bo_cap bn) in LLC.
  pose proof (one_le_cap M1 (F + 96) bn (proj1 TN)) as OLC. fold (L5.bo_cap bn) in OLC.
  pose proof (proj1 (proj2 TN)) as (LWY & WYOK & _).
  apply (G12C fx1 R1 M1 model1 BX0 LK1 cr1 A1 bn bd wy WA _ _ cells BI0 RI0 SSH TN TD ON OD SPL).
  { subst cells. do 5 right. left. reflexivity. } { subst cells. left. reflexivity. }
  { intros _. clear - CAPB; lia. } { intros X0. rewrite DYD in X0. discriminate X0. }
  { rewrite CAPD. apply (cred_weak L C LY cr1 3 (8 * L5.bo_cap bn + 144) _ _ CRD). clear; lia. clear - OLC; lia. }
  intros fx2 R2 M2' model2' gn0 gd0 bn0 bd0 cr2' LK2' A2 BX2 BI2 RI2 p19 p20 KS2 OFF2 ON0 OD0 GNF GDF ECR2 IA2 ILK2.
  destruct gd0 as [|qd0 capd0]. 2:{ destruct GDF as (_ & X0). rewrite DYD in X0. discriminate X0. }
  cbn [L5DLA.blocks_of app L5ADVHO.on_of] in *.
  pose proof BI0 as (B1 & _).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX0 ++ LB) M1 o b ws -> L5ADVEA.oreg o b a -> ~ (SPA + 184 <= a < SPA + 248)).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX0 M1 model1 LK1 cr1 A1 o b ws a BI0 AO TO OR). clear - X0 HSCR; lia. }
  assert (SUB2 : forall b0, In b0 (BX0 ++ LB) -> In b0 (BX2 ++ LB)). { intros b0 Hb. subst BX2. rewrite <- app_assoc. apply in_or_app. right. exact Hb. }
  assert (TN2 : tob (BX2 ++ LB) M2' (F + 96) bn wy).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX0 ++ LB) (BX0 ++ LB) (BX2 ++ LB) LK1 cr1 A1 model1 COPY_SCR _ M1 M2' (F + 96) bn wy B1 AON' TN OFF2).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN)) cap q Eq) as X0. split. exact X0. apply SUB2. exact X0. intros a OR. exact (NOFR _ _ _ a AON' TN OR). }
  assert (TD2 : tob (BX2 ++ LB) M2' (F + 32) bd WA).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX0 ++ LB) (BX0 ++ LB) (BX2 ++ LB) LK1 cr1 A1 model1 COPY_SCR _ M1 M2' (F + 32) bd _ B1 AOD' TD OFF2).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TD)) cap q Eq) as X0. split. exact X0. apply SUB2. exact X0. intros a OR. exact (NOFR _ _ _ a AOD' TD OR). }
  assert (SPL2 : spl E M2' cells).
  { intros a v Hin. destruct (SPL a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR (BX0 ++ LB) COPY_SCR _ M1 M2' a v Hc H1 H2 OFF2).
    intros i Hi X0. subst cells. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear - Hi X0; lia|]). destruct Hin. }
  assert (HDR2 : L5.u64_at RSEGS M2' F 1102416563).
  { eapply L5C.u64_at_agree. 4: exact HDR. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFF2. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA COPY_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia.
    clear - Hi SFB. lia. }
  assert (DSH2 : dsh M2' F 0 248 248 248 248).
  { eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH | exact OFF2 | ]. intros j Hj X0. pose proof (sh_rng j Hj) as Y. clear - Y X0 ER. lia. }
  (* [comment removed for export] *)
  assert (E8 : (E - 176) mod 8 = 0 /\ (E - 172) / 8 = (E - 176) / 8). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SZP : shadow_zero M2' (E - 172) 1).
  { destruct (STK_DEST [] BX2 M2' model2' LK2' cr2' A2 (E - 176) BI2 SSH ltac:(clear; lia) ltac:(clear; lia) (proj1 E8) ltac:(intros a _ rr [])) as (_ & SZ176).
    intros j Hj. assert (j = 0) by (clear - Hj; lia). subst j. specialize (SZ176 0 ltac:(clear; lia)). unfold byte_at, S in *. rewrite (proj2 E8). exact SZ176. }
  assert (CR2 : L5DLA.acredits L cr2' (L5DLA.cnt bd + L5DLA.cnt bn)).
  { unfold L5DLA.cnt. rewrite DYD. destruct gn0 as [|q0 cap0].
    - rewrite GNF. cbn [L5DLA.blocks_of L5DLA.adebl app] in ECR2. subst cr2'.
      destruct (cred_weak L C LY cr1 3 (8 * L5.bo_cap bn + 144) 2 128 CRD ltac:(clear; lia) ltac:(clear - OLC; lia)) as (C1 & C2). unfold L5DLA.acredits. split. exact C1. clear - C2. lia.
    - destruct GNF as (EC0 & DY0). rewrite DY0. cbn [L5DLA.blocks_of L5DLA.adebl app] in ECR2. subst cr2' cap0.
      pose proof (cred_step L cr1 3 (8 * L5.bo_cap bn + 144) (8 * L5.bo_cap bn) CRD ltac:(clear; lia) ltac:(clear - OLC; lia)) as X0.
      destruct (cred_weak L C LY _ _ _ 1 64 X0 ltac:(clear; lia) ltac:(clear; lia)) as (C1 & C2). unfold L5DLA.acredits. split. exact C1. clear - C2. lia. }
  apply (G3 fx2 R2 M2' model2' [] BX2 LK2' cr2' A2 ro bd WA bn wy BI2 RI2 p19 p20 ltac:(rewrite (KS2 24%nat) by inl; exact X24) ROR ROR SZP TD2 TN2).
  { intros cap q Eq. rewrite STD in Eq. discriminate Eq. }
  { intros cap q Eq. destruct (DYNY cap q Eq) as (EG & _). subst BX2 BX0. rewrite EG. apply in_or_app. right. cbn. left. reflexivity. }
  { rewrite LND. clear; lia. }
  { rewrite LND. exact (proj1 A1_top). }
  { rewrite LND. intros _. exact (proj2 A1_top). }
  { clear - LENB LLC CAPB. lia. }
  { intros _. split. exact LENB. exists (L5.bo_len bn - 1)%nat. split. clear - LENB; lia. exact TOPY. }
  { intros cap q Eq. rewrite STD in Eq. discriminate Eq. }
  { intros cap q Eq. exact (proj2 (DYNY cap q Eq)). }
  { rewrite LND, clz_A1, second_WA. intros X0. discriminate X0. }
  { intros cd qd cn qn0 Eq. rewrite STD in Eq. discriminate Eq. }
  { exact CR2. }
  intros fx3 R3 R3' M3 M3' model3 c gd gn LBn cr3 LK3 A3 KS3 p23 AG3 POST3 BI3 IA3 ILK3.
  pose proof POST3 as (RP3 & EC & _ & _ & E10 & PX3 & _ & _ & ECR3 & _ & _ & _ & GD3 & _). cbv zeta in EC, E10, GD3, ECR3.
  rewrite LND in EC, E10, GD3. rewrite clz_A1 in EC. subst c. rewrite second_WA in E10.
  destruct (NORM_TOBS [] BX2 M2' M3 M3' model2' LK2' cr2' A2 R3 R3' bd bn WA wy 2 gd gn LBn cr3 LK3 BI2 AG3 TD2 TN2 POST3)
    as (fbd' & fbn' & std & stn & TD3 & TN3 & GRD & GRN & CPD & CPN & OFF3).
  rewrite LND, second_WA in TD3, TN3, CPD, CPN. rewrite norm_WA in TD3, CPD. rewrite rlen_DA in TD3.
  change (L5DLA.norm_words wy 2 false) with (shl_words wy 2) in *.
  destruct gd as [|qd capd]. { exfalso. unfold gro_st, L5ADVEA.same_store in GRD. rewrite STD in GRD. destruct std as [d0 d1|? ?]. cbn in CPD. clear - CPD; lia. destruct GRD. }
  destruct GRD as (_ & -> & ->).
  (* [comment removed for export] *)
  cbn [L5DLA.blocks_of app] in BI3, TD3, TN3, ECR3.
  set (rn := shl_words wy 2) in *.
  set (BXc := L5DLA.blocks_of gn ++ (qd, 8 * 8) :: BX2) in *.
  assert (R19 : getr R3' (reg 19) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R3 R3' 19 RP3) by inl; rewrite (KS3 19%nat) by inl; exact p19).
  assert (R20 : getr R3' (reg 20) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R3 R3' 20 RP3) by inl; rewrite (KS3 20%nat) by inl; exact p20).
  assert (R22 : getr R3' (reg 22) = Z_to_bv 64 qo) by (rewrite (cs_of_preserved R3 R3' 22 RP3) by inl; rewrite (KS3 22%nat) by inl; rewrite (KS2 22%nat) by inl; exact X22).
  assert (R10 : getr R3' (reg 10) = Z_to_bv 64 0). { rewrite <- r10. exact E10. }
  assert (RI3 : rinvD R E R3'). { apply (rinvD_pres R E R3 R3'). apply (rinvD_ks R E R2 R3 KS_v5G3 RI2 KS3). vm_compute; reflexivity. exact RP3. }
  pose proof (proj1 TN3) as OBN3. pose proof OBN3 as (_ & _ & NL8 & _). cbn [L5.bo_len] in NL8. replace (F + 96 + 8) with (F + 104) in NL8 by (clear; lia).
  pose proof (rlen_le rn) as RLE. assert (LRN : length rn = Datatypes.S (length wy)) by (subst rn; apply shl_words_length). rewrite LRN, LWY in RLE.
  apply (G4s fx3 R3' M3' model3 [] BXc LK3 cr3 A3 0 qo (L5.BO fbd' 2 (L5.BDyn 8 qd)) (Z.of_nat (rlen rn)) BI3 RI3 R10 R19 R20 R22 ltac:(clear; lia) QOR (proj1 TD3) NL8 ltac:(clear - RLE LLC CAPB; lia)).
  intros fx4 R4 M4 model4 BI4 RI4 KS4 p1 p10 p11 p21 p27 AG4 S16 S128 S136.
  cbn [L5.bo_len] in p11. unfold L5.bo_data in S128. cbn [L5.bo_st L5.bo_len] in S128, S136.
  (* [comment removed for export] *)
  set (X4 := fun a => E - 336 <= a < E - 328 \/ E - 224 <= a < E - 208).
  assert (OFF4 : offx (BXc ++ LB) L5DLA.NORM_SCR X4 M3' M4).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG4. exact Ha. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  assert (OFF23 : offx (BX2 ++ LB) L5DLA.NORM_SCR (fun a => E - 172 <= a < E - 168) M2' M3).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG3. exact Ha. exact NX. }
  pose proof BI3 as (B3 & _). pose proof BI2 as (B2 & _).
  assert (NOFR4 : forall o b ws a, aobj FF' o 32 -> tob (BXc ++ LB) M3' o b ws -> L5ADVEA.oreg o b a -> ~ X4 a).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BXc M3' model3 LK3 cr3 A3 o b ws a BI3 AO TO OR). subst X4; cbn beta in X0. clear - X0 HSCR; lia. }
  assert (TD4 : tob (BXc ++ LB) M4 (F + 32) (L5.BO fbd' 2 (L5.BDyn 8 qd)) (firstn 2 DA)).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXc ++ LB) (BXc ++ LB) (BXc ++ LB) LK3 cr3 A3 model3 L5DLA.NORM_SCR _ M3' M4 (F + 32) _ _ B3 AOD' TD3 OFF4).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TD3)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR4 _ _ _ a AOD' TD3 OR). }
  assert (TN4 : tob (BXc ++ LB) M4 (F + 96) (L5.BO fbn' (rlen rn) stn) (firstn (rlen rn) rn)).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXc ++ LB) (BXc ++ LB) (BXc ++ LB) LK3 cr3 A3 model3 L5DLA.NORM_SCR _ M3' M4 (F + 96) _ _ B3 AON' TN3 OFF4).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN3)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR4 _ _ _ a AON' TN3 OR). }
  (* [comment removed for export] *)
  assert (INWN : forall a, L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 172) bd bn) a ->
            F + 32 <= a < F + 128 \/ E - 172 <= a < E - 168 \/ (exists cap q, L5.bo_st bn = L5.BDyn cap q /\ q <= a < q + 8 * cap)).
  { intros a (rr & Hr & IR). unfold L5DLA.norm_W, L5DLA.dyn_area in Hr. rewrite STD in Hr. cbn [app In] in Hr. unfold L5.in_rng in IR.
    destruct Hr as [<-|[<-|[<-|Hr]]]; cbn [fst snd] in IR. left; clear - IR; lia. left; clear - IR; lia. right; left; clear - IR; lia.
    destruct (L5.bo_st bn) as [? ?|cap q]. destruct Hr. destruct Hr as [<-|[]]. cbn [fst snd] in IR. right; right. exists cap, q. split. reflexivity. exact IR. }
  assert (XST : forall a, SPA <= a < E -> ~ (E - 172 <= a < E - 168) -> ~ X4 a -> ~ (((E - 172 <= a < E - 168) \/ L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 172) bd bn) a) \/ X4 a)).
  { intros a Ha N1 N4 [[Y|Y]|Y]. exact (N1 Y). 2: exact (N4 Y). destruct (INWN a Y) as [Z0|[Z0|(cap & q & Eq & Z0)]]. clear - Z0 Ha SFB; lia. exact (N1 Z0).
    pose proof (proj2 (proj2 (proj2 TN2)) cap q Eq) as INQ2.
    destruct (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR [] BX2 M2' model2' LK2' cr2' A2 q (8 * cap) a BI2 INQ2 Z0) as (_ & _ & Y3). exact (Y3 Ha). }
  assert (OFF4b : offx (BX2 ++ LB) L5DLA.NORM_SCR X4 M3' M4).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG4. exact Ha. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  pose proof (offx_trans L ar FF E F _ _ _ _ _ _ _ (offx_trans L ar FF E F _ _ _ _ _ _ _ OFF23 OFF3) OFF4b) as OFFA. cbv beta in OFFA.
  assert (SPL4 : spl E M4 cells).
  { intros a v Hin. destruct (SPL2 a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR (BX2 ++ LB) L5DLA.NORM_SCR _ M2' M4 a v Hc H1 H2 OFFA).
    intros i Hi. apply XST. clear - Hi H1 H2; lia.
    all: subst cells X4; cbn beta; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear - Hi; lia|]); destruct Hin. }
  assert (HDR4 : L5.u64_at RSEGS M4 F 1102416563).
  { eapply L5C.u64_at_agree. 4: exact HDR2. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFFA. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA L5DLA.NORM_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia.
    intros [[Y|Y]|Y]. clear - Y Hi SFB; lia. 2: subst X4; cbn beta in Y; clear - Y Hi SFB; lia.
    destruct (INWN i Y) as [Z0|[Z0|(cap & q & Eq & Z0)]]. clear - Z0 Hi; lia. clear - Z0 Hi SFB; lia.
    pose proof (proj2 (proj2 (proj2 TN2)) cap q Eq) as INQ2.
    destruct (L5ADVEA.blk_frame L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX2 M2' model2' LK2' cr2' A2 q (8 * cap) F BI2 INQ2) as (Y1 & _). clear - Y1 Z0 Hi; lia. }
  assert (DSH4 : dsh M4 F 0 248 248 248 248).
  { eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH2 | exact OFFA | ]. intros j Hj [[Y|Y]|Y]; pose proof (sh_rng j Hj) as YR. clear - YR Y ER; lia. 2: subst X4; cbn beta in Y; clear - YR Y ER; lia.
    destruct (INWN j Y) as [Z0|[Z0|(cap & q & Eq & Z0)]]. clear - Z0 YR FBIG; lia. clear - Z0 YR ER; lia.
    pose proof (proj2 (proj2 (proj2 TN2)) cap q Eq) as INQ2.
    destruct (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR [] BX2 M2' model2' LK2' cr2' A2 q (8 * cap) j BI2 INQ2 Z0) as (_ & Y2 & _). apply Y2. change (ff_bytes 3 / 8) with 64. unfold SB. exact Hj. }
  assert (STK4 : forall o b blk, L5ADVD.obj_at M2' o b blk -> E - 168 <= o -> o + 32 <= E - 104 -> L5ADVD.obj_at M4 o b blk).
  { intros o b blk OA H1 H2. apply (L5ADVD.obj_at_agree M2' M4 o b blk OA ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia)). intros i Hi. apply OFFA. clear - Hi H1 H2 ER; lia.
    apply stack_client. destruct G as [Hk SPT SLO SHI SPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. clear - Hi H1 H2 SLO SHI SPT HSCR; lia. clear - Hi H1; lia.
    apply XST. clear - Hi H1 H2; lia. clear - Hi H1; lia. subst X4; cbn beta. clear - Hi H1; lia. }
  assert (PX4 : L5.u32_at RSEGS M4 (E - 172) 2).
  { eapply L5ACMP.u32_at_agree1. 4: exact PX3. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply AG4. clear - Hi ER; lia. clear - Hi; lia. clear - Hi; lia. }
  apply (KF fx4 R4 M4 model4 gn0 gn qd bn0 bd0 fbd' fbn' stn cr3 LK3 A3 BI4 RI4).
  - intros x Hx. assert (Hc : In x cs_all) by (revert Hx; apply (L5K.incl_b [18; 22; 24; 25; 26]%nat); vm_compute; reflexivity).
    rewrite (KS4 x) by (revert Hx; apply (L5K.incl_b [18; 22; 24; 25; 26]%nat); vm_compute; reflexivity).
    rewrite (cs_of_preserved R3 R3' x RP3 Hc). rewrite (KS3 x) by (revert Hx; apply (L5K.incl_b [18; 22; 24; 25; 26]%nat); vm_compute; reflexivity).
    apply KS2. revert Hx. apply (L5K.incl_b [18; 22; 24; 25; 26]%nat). vm_compute; reflexivity.
  - rewrite (KS4 19%nat) by inl. exact R19.
  - rewrite (KS4 20%nat) by inl. exact R20.
  - rewrite (KS4 23%nat) by inl. rewrite (cs_of_preserved R3 R3' 23 RP3) by inl. exact p23.
  - exact p1.
  - exact p10.
  - exact p11.
  - exact p21.
  - exact p27.
  - exact TD4.
  - exact TN4.
  - exact GRN.
  - exact CPN.
  - exact GNF.
  - apply (STK4 _ _ _ ON0). clear; lia. clear; lia.
  - apply (STK4 _ _ _ OD0). clear; lia. clear; lia.
  - exact SPL4.
  - exact S16.
  - exact S128.
  - exact S136.
  - exact HDR4.
  - exact DSH4.
  - exact PX4.
  - destruct POST3 as (_ & _ & _ & _ & _ & _ & (std0 & stn0 & _ & OAN) & _). exact (after_sgn M3' (F + 96) bn _ gn stn0 fbn' _ _ OAN (proj1 TN3) SGN_N).
  - rewrite ECR3, ECR2. reflexivity.
  - intros x Hx. apply IA3. apply IA2. exact Hx.
  - intros x Hx. apply ILK2. apply ILK3. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition trk (BXx : list (Z * Z)) (Mx : word -> option byte) (bn bd bn0 bd0 : L5.bigobj) (wn wd : list Z) (on0 : option (Z * Z)) (cells : list (Z * Z)) (x : Z) : Prop :=
  tob (BXx ++ LB) Mx (F + 96) bn wn /\ tob (BXx ++ LB) Mx (F + 32) bd wd
  /\ L5ADVD.obj_at Mx (SPA + 216) bn0 on0 /\ L5ADVD.obj_at Mx (SPA + 184) bd0 None
  /\ spl E Mx cells /\ L5.u32_at RSEGS Mx (E - 172) x /\ L5.u64_at RSEGS Mx F 1102416563 /\ dsh Mx F 0 248 248 248 248.

Lemma trk_keep W BXx BXy Mx My modelx LKx crx Ax scr (X : Z -> Prop) bn bd bn0 bd0 wn wd on0 cells x :
  binv W BXx Mx modelx LKx crx Ax -> offx (BXx ++ LB) scr X Mx My -> (forall b0, In b0 (BXx ++ LB) -> In b0 (BXy ++ LB)) ->
  trk BXx Mx bn bd bn0 bd0 wn wd on0 cells x ->
  (forall a, L5ADVEA.oreg (F + 96) bn a -> ~ X a) -> (forall a, L5ADVEA.oreg (F + 32) bd a -> ~ X a) ->
  (forall i, E - 172 <= i < E - 104 -> ~ X i) ->
  (forall c v, In (c, v) cells -> forall i, c <= i < c + 8 -> ~ X i) ->
  (forall i, F <= i < F + 8 -> ~ X i) ->
  (forall j, SH <= j < SH + 64 -> ~ X j) ->
  trk BXy My bn bd bn0 bd0 wn wd on0 cells x.
Proof.
  intros BI OFF SUB (TN & TD & ON0 & OD0 & SPL & PX & HDR & DSH) NXN NXD NXS NXC NXH NXSH.
  pose proof BI as (B1 & _).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (STKC : forall i, E - 172 <= i < E - 104 -> My (Z_to_bv 64 i) = Mx (Z_to_bv 64 i)).
  { intros i Hi. apply OFF. clear - Hi ER; lia.
    apply stack_client. destruct G as [Hk SPT SLO SHI SPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. clear - Hi SLO SHI SPT HSCR; lia. clear - Hi; lia. apply NXS. exact Hi. }
  split. { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXx ++ LB) (BXx ++ LB) (BXy ++ LB) LKx crx Ax modelx scr _ Mx My (F + 96) bn wn B1 AON' TN OFF).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN)) cap q Eq) as X0. split. exact X0. apply SUB. exact X0. exact NXN. }
  split. { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXx ++ LB) (BXx ++ LB) (BXy ++ LB) LKx crx Ax modelx scr _ Mx My (F + 32) bd wd B1 AOD' TD OFF).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TD)) cap q Eq) as X0. split. exact X0. apply SUB. exact X0. exact NXD. }
  split. { apply (L5ADVD.obj_at_agree Mx My _ _ _ ON0 ltac:(clear - ER; lia) ltac:(clear - ER; lia)). intros i Hi. apply STKC. clear - Hi; lia. }
  split. { apply (L5ADVD.obj_at_agree Mx My _ _ _ OD0 ltac:(clear - ER; lia) ltac:(clear - ER; lia)). intros i Hi. apply STKC. clear - Hi; lia. }
  split. { intros a v Hin. destruct (SPL a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR (BXx ++ LB) scr _ Mx My a v Hc H1 H2 OFF). exact (NXC a v Hin). }
  split. { eapply L5ACMP.u32_at_agree1. 4: exact PX. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply STKC. clear - Hi; lia. }
  split. { eapply L5C.u64_at_agree. 4: exact HDR. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFF. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA scr F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia. apply NXH. exact Hi. }
  eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH | exact OFF | exact NXSH].
Qed.

(* [comment removed for export] *)
Lemma trk_keep_arg W BXx BXy Mx My modelx LKx crx Ax scr o b ws bn bd bn0 bd0 wn wd on0 cells x :
  binv W BXx Mx modelx LKx crx Ax -> aobj FF o 32 -> tob (BXx ++ LB) Mx o b ws ->
  offx (BXx ++ LB) scr (L5ADVEA.oreg o b) Mx My -> (forall b0, In b0 (BXx ++ LB) -> In b0 (BXy ++ LB)) ->
  trk BXx Mx bn bd bn0 bd0 wn wd on0 cells x ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st b = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st b = L5.BDyn c' q' -> q <> q') ->
  trk BXy My bn bd bn0 bd0 wn wd on0 cells x.
Proof.
  intros BI AO TO OFF SUB TRK NQN NQD. pose proof TRK as (TN & TD & _ & _ & SPL & _).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AO' : aobj FF' o 32) by (apply aobj_cons; exact AO).
  assert (OFFA : forall a, L5ADVEA.oreg o b a -> ~ (F <= a < F + 512) /\ ~ (SPA <= a < E)).
  { intros a OR. edestruct L5ADVEA.arg_off with (o := o) (a := a) as (Y1 & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AO | exact TO | exact OR | ]. split; assumption. }
  assert (APF : forall k, 0 <= k <= 480 -> F + k + 32 <= o \/ o + 32 <= F + k).
  { intros k Hk. destruct (OFFA o ltac:(left; clear; lia)) as (Y1 & _). destruct (OFFA (o + 31) ltac:(left; clear; lia)) as (Y2 & _). clear - Hk Y1 Y2. lia. }
  apply (trk_keep W BXx BXy Mx My modelx LKx crx Ax scr _ bn bd bn0 bd0 wn wd on0 cells x BI OFF SUB TRK).
  - intros a ORn ORo. exact (OREG_DISJ W BXx Mx modelx LKx crx Ax (F + 96) bn wn o b ws a BI AON' TN AO' TO (APF 96 ltac:(clear; lia)) NQN ORn ORo).
  - intros a ORd ORo. exact (OREG_DISJ W BXx Mx modelx LKx crx Ax (F + 32) bd wd o b ws a BI AOD' TD AO' TO (APF 32 ltac:(clear; lia)) NQD ORd ORo).
  - intros i Hi ORo. apply (proj2 (OFFA i ORo)). clear - Hi; lia.
  - intros c v Hin i Hi ORo. destruct (SPL c v Hin) as (_ & H1 & H2). apply (proj2 (OFFA i ORo)). clear - Hi H1 H2; lia.
  - intros i Hi ORo. apply (proj1 (OFFA i ORo)). clear - Hi; lia.
  - intros j Hj ORo. edestruct L5ADVEA.arg_off with (o := o) (a := j) as (_ & Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AO | exact TO | exact ORo | ]. exact (Y2 Hj).
Qed.

(* [comment removed for export] *)
Lemma inv_head_fresh q n (Lx : list (Z * Z)) FFx LKx crx Ax Mx Vx q' n' : ri_inv HI ((q, n) :: Lx) FFx LKx crx Ax Mx Vx -> In (q', n') Lx -> q <> q'.
Proof.
  intros HH Hin Eq. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF0.
  assert (ND : NoDup (map fst ((q, n) :: Lx))) by (clear - WF0; decompose [and] WF0; assumption).
  apply (L5ADVHO.nodup_app_fst [(q, n)] Lx (q, n) (q', n') ND). left; reflexivity. exact Hin. exact Eq.
Qed.
Lemma inv_blk_apart (Lx : list (Z * Z)) FFx LKx crx Ax Mx Vx q n q' n' : ri_inv HI Lx FFx LKx crx Ax Mx Vx -> In (q, n) Lx -> In (q', n') Lx -> q <> q' -> q + n <= q' \/ q' + n' <= q.
Proof.
  intros HH I1 I2 NE. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ I1) as (_ & _ & _ & _ & BA & _). cbn [fst snd] in BA.
  specialize (BA (q', n') (L5ADVHO.in_lb_remove q (q', n') Lx I2 ltac:(cbn [fst]; intros X0; apply NE; symmetry; exact X0))). cbn [fst snd] in BA. exact BA.
Qed.
Lemma offx_weaken LBx scr (X X' : Z -> Prop) Ma Mb : offx LBx scr X Ma Mb -> (forall a, X a -> X' a) -> offx LBx scr X' Ma Mb.
Proof. intros O HX a Ha Hc NX. apply (O a Ha Hc). intros Y. apply NX. apply HX. exact Y. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma go2_mid1 (cr0 : credit) (qo : Z) (by_ : L5.bigobj) (wy : list Z) (fx4 : FPState) R4 M4 model4 BX4 LK4 cr4 A4 bn bd bn0 bd0 wn wd on0 cells x (nn lq : nat) :
  ri_inv HI LB FF LK cr0 A M (vml_of model) ->
  tob LB M qo (L5.BO 0 0 (L5.BInl 0 0)) [] -> aobj FF qo 32 -> tob LB M ro by_ wy -> aobj FF ro 32 -> (ro + 32 <= qo \/ qo + 32 <= ro) ->
  binv [] BX4 M4 model4 LK4 cr4 A4 -> rinvD R E R4 ->
  getr R4 (reg 1) = Z_to_bv 64 0x92758 -> getr R4 (reg 10) = Z_to_bv 64 qo -> getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat lq) ->
  getr R4 (reg 20) = Z_to_bv 64 (F + 96) -> getr R4 (reg 21) = Z_to_bv 64 2147450880 -> getr R4 (reg 22) = Z_to_bv 64 qo -> getr R4 (reg 23) = Z_to_bv 64 ro ->
  trk BX4 M4 bn bd bn0 bd0 wn wd on0 cells x -> L5.bo_len bn = nn -> (2 <= nn <= 269)%nat -> (lq <= nn)%nat ->
  (L5.bo_dyn by_ = true -> Z.of_nat nn <= L5.bo_cap by_) ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st by_ = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st by_ = L5.BDyn c' q' -> q <> q') ->
  L5OMA.acredit_for L cr4 (if L5.bo_dyn by_ then 1 else 2) (8 * round_up (Z.of_nat lq) + (if L5.bo_dyn by_ then 0 else 8 * round_up (Z.of_nat nn))) ->
  (forall (fx7 : FPState) R7 M7 model7 (gq gr : growth) bq br W7 cr7 LK7 A7 wq,
      let BX5 := match gq with Same => BX4 | Grown q cap => (q, 8 * cap) :: BX4 end in
      let BX7 := match gr with Same => BX5 | Grown q cap => (q, 8 * cap) :: BX5 end in
      binv W7 BX7 M7 model7 LK7 cr7 A7 -> rinvD R E R7 ->
      W7 = [(qo, 32); (L5.bo_data qo bq, 8 * Z.of_nat (L5.bo_len bq)); (ro, 32); (L5.bo_data ro by_, 8 * L5.bo_cap by_)] ->
      getr R7 (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr R7 (reg 21) = Z_to_bv 64 2147450880 -> getr R7 (reg 22) = Z_to_bv 64 qo -> getr R7 (reg 23) = Z_to_bv 64 ro ->
      getr R7 (reg 24) = Z_to_bv 64 (L5.bo_data qo bq) -> getr R7 (reg 27) = getr R4 (reg 27) -> getr R7 (reg 25) = Z_to_bv 64 (Z.of_nat lq) ->
      tob (BX7 ++ LB) M7 qo bq wq -> L5.bo_len bq = lq -> L5.bo_fb bq = (match gq with Same => 0 | Grown _ _ => 1 end) ->
      (match gq with Same => L5.bo_dyn bq = false | Grown q cap => L5.bo_st bq = L5.BDyn cap q /\ cap = round_up (Z.of_nat lq) /\ (3 <= lq)%nat end) ->
      tob (BX7 ++ LB) M7 ro br wn -> L5.bo_len br = nn ->
      (match gr with
       | Same => L5.bo_fb br = assign_fb (L5.bo_fb by_) (L5.bo_fb bn) nn false /\ L5ADVEA.same_store by_ (L5.bo_st br)
       | Grown q cap => L5.bo_fb br = assign_fb (L5.bo_fb by_) (L5.bo_fb bn) nn true /\ L5.bo_st br = L5.BDyn cap q /\ cap = round_up (Z.of_nat nn) /\ L5.bo_dyn by_ = false end) ->
      trk BX7 M7 bn bd bn0 bd0 wn wd on0 cells x ->
      cr7 = L5DLA.adebl L (L5DLA.adebl L cr4 (L5DLA.blocks_of gq)) (L5DLA.blocks_of gr) -> incl A4 A7 -> incl LK7 LK4 ->
      srealizes RSEGS SCFG (cfg (fx:=fx7) R7 0x927cc M7 model7) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 RESIZE M4 model4) K.
Proof.
  intros HH0 TQ0 AOQ TR0 AOR APRQ BI4 RI4 p1 p10 p11 p20 p21 p22 p23 TRK4 LNN NNR LQR CAPY NQNY NQDY CRD KF.
  set (n := lq) in *.
  assert (TQ4 : tob (BX4 ++ LB) M4 qo (L5.BO 0 0 (L5.BInl 0 0)) []). { eapply L5ADVHA.arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOQ | exact TQ0 | ]. intros a _ rr []. }
  assert (P11 : getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat n)) by exact p11.
  assert (RUN : 8 <= round_up (Z.of_nat n) /\ 8 <= round_up (Z.of_nat nn)).
  { unfold round_up. clear. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (ARSZ2 fx4 R4 M4 model4 [] [(qo, 32)] BX4 LK4 cr4 A4 qo 0x92758 n (L5.BO 0 0 (L5.BInl 0 0)) [] BI4 RI4 p10 P11 p1 ltac:(split; [clear; lia | reflexivity]) AOQ TQ4).
  { subst n. clear - NNR LQR. lia. }
  { intros X0. discriminate X0. }
  { intros _ _. apply (cred_ok1 L C LY cr4 _ _ _ CRD). destruct (L5.bo_dyn by_); clear; lia. destruct (L5.bo_dyn by_); clear - RUN; lia. }
  { intros a X0. split. intros rr []. exact X0. }
  { intros [X0|LE2] a _ OUT IR. discriminate X0. apply (OUT (qo, 32)). left; reflexivity. unfold L5.in_rng in *. cbn [fst snd L5.bo_data L5.bo_st L5.bo_len] in *. clear - IR LE2. lia. }
  intros fx5 R5 M5 model5 gq bq1 cr5 LK5 A5 RP5 BI5 TQ5 LENQ GQF OFF5 IA5 ILK5.
  set (BX5 := match gq with Same => BX4 | Grown q cap => (q, 8 * cap) :: BX4 end) in *.
  assert (SUB5 : forall b0, In b0 (BX4 ++ LB) -> In b0 (BX5 ++ LB)). { intros b0 Hb. subst BX5. destruct gq. exact Hb. right. exact Hb. }
  assert (TRK5 : trk BX5 M5 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (trk_keep_arg [] BX4 BX5 M4 M5 model4 LK4 cr4 A4 RESIZE_SCR qo _ _ bn bd bn0 bd0 wn wd on0 cells x BI4 AOQ TQ4 OFF5 SUB5 TRK4).
    intros c q c' q' _ Eq. discriminate Eq. intros c q c' q' _ Eq. discriminate Eq. }
  (* [comment removed for export] *)
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (TR4 : tob (BX4 ++ LB) M4 ro by_ wy). { eapply L5ADVHA.arg_at; [exact LY | exact HIok | exact HH0 | exact BI4 | exact AOR | exact TR0 | ]. intros a _ rr []. }
  assert (NQRQ4 : forall a, L5ADVEA.oreg ro by_ a -> L5ADVEA.oreg qo (L5.BO 0 0 (L5.BInl 0 0)) a -> False).
  { intros a O1 O2. apply (OREG_DISJ [] BX4 M4 model4 LK4 cr4 A4 ro by_ wy qo _ [] a BI4 AOR' TR4 AOQ' TQ4 APRQ). intros c q c' q' _ Eq. discriminate Eq. exact O1. exact O2. }
  assert (TR5 : tob (BX5 ++ LB) M5 ro by_ wy).
  { pose proof BI4 as (B4 & _).
    apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX4 ++ LB) (BX4 ++ LB) (BX5 ++ LB) LK4 cr4 A4 model4 RESIZE_SCR _ M4 M5 ro by_ wy B4 AOR' TR4 OFF5).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TR4)) cap q Eq) as X0. split. exact X0. apply SUB5. exact X0. intros a O1 O2. exact (NQRQ4 a O1 O2). }
  assert (RI5 : rinvD R E R5) by (apply (rinvD_pres R E R4 R5 RI4 RP5)).
  assert (X21 : getr R5 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (cs_of_preserved R4 R5 21 RP5) by inl; exact p21).
  assert (X22 : getr R5 (reg 22) = Z_to_bv 64 qo) by (rewrite (cs_of_preserved R4 R5 22 RP5) by inl; exact p22).
  set (W2 := [(qo, 32); (L5.bo_data qo bq1, 8 * Z.of_nat (L5.bo_len bq1))]).
  apply (G5A fx5 R5 M5 model5 [(qo, 32)] W2 BX5 LK5 cr5 A5 qo bq1 (resize_limbs [] n) BI5 RI5 X21 X22 AOQ TQ5).
  { rewrite LENQ. subst n. clear - NNR LQR. lia. }
  { intros a OUT. split. intros rr [<-|[]]. apply OUT. left; reflexivity. intros rr [<-|[]]. apply OUT. right; left; reflexivity. }
  intros fx6 R6 M6 model6 bq wq BI6 RI6 KS6 p18 p24 p25 TQ6 FB6 LN6 SS6 DT6 OFF6.
  (* [comment removed for export] *)
  assert (DSUB : forall a, L5.bo_data qo bq1 <= a < L5.bo_data qo bq1 + 8 * Z.of_nat (L5.bo_len bq1) -> L5ADVEA.oreg qo bq1 a).
  { intros a Ha. pose proof (len_le_cap M5 qo bq1 (proj1 TQ5)) as LC. unfold L5.bo_data in Ha. destruct (L5.bo_st bq1) as [v0 v1|cap q] eqn:EST.
    left. clear - Ha LC. lia. right; right. exists cap, q. split. exact EST. clear - Ha LC. lia. }
  (* [comment removed for export] *)
  assert (QFRESH : forall c q c' q', L5.bo_st bq1 = L5.BDyn c q -> In (q', 8 * c') (BX4 ++ LB) -> q' <> q).
  { intros c q c' q' Eq Hin X0. subst BX5. destruct gq as [|qg capg].
    - destruct GQF as (_ & SS & _). unfold L5ADVEA.same_store in SS. cbn [L5.bo_st] in SS. rewrite Eq in SS. destruct SS.
    - destruct GQF as (_ & ST & _). rewrite ST in Eq. injection Eq as <- <-. pose proof BI5 as (B5 & _). cbn [app] in B5.
      apply (inv_head_fresh qg (8 * capg) (BX4 ++ LB) _ _ _ _ _ _ q' (8 * c') B5 Hin). symmetry. exact X0. }
  assert (TRK6 : trk BX5 M6 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (trk_keep_arg [(qo, 32)] BX5 BX5 M5 M6 model5 LK5 cr5 A5 MEM_SCR qo bq1 _ bn bd bn0 bd0 wn wd on0 cells x BI5 AOQ TQ5 (offx_weaken _ _ _ _ _ _ OFF6 DSUB) ltac:(intros b0 Hb; exact Hb) TRK5).
    - intros c q c' q' Eq Eq'. apply (QFRESH c' q' c q Eq'). exact (proj2 (proj2 (proj2 (proj1 TRK4))) c q Eq).
    - intros c q c' q' Eq Eq'. apply (QFRESH c' q' c q Eq'). exact (proj2 (proj2 (proj2 (proj1 (proj2 TRK4)))) c q Eq). }
  assert (NQRQ5 : forall a, L5ADVEA.oreg ro by_ a -> L5ADVEA.oreg qo bq1 a -> False).
  { intros a O1 O2. apply (OREG_DISJ [(qo, 32)] BX5 M5 model5 LK5 cr5 A5 ro by_ wy qo bq1 _ a BI5 AOR' TR5 AOQ' TQ5 APRQ). 2: exact O1. 2: exact O2.
    intros c q c' q' Eq Eq'. apply (QFRESH c' q' c q Eq'). exact (proj2 (proj2 (proj2 TR4)) c q Eq). }
  assert (TR6 : tob (BX5 ++ LB) M6 ro by_ wy).
  { pose proof BI5 as (B5 & _).
    apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX5 ++ LB) (BX5 ++ LB) (BX5 ++ LB) LK5 cr5 A5 model5 MEM_SCR _ M5 M6 ro by_ wy B5 AOR' TR5 (offx_weaken _ _ _ _ _ _ OFF6 DSUB)).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TR5)) cap q Eq) as X0. split; exact X0. intros a O1 O2. exact (NQRQ5 a O1 O2). }
  (* [comment removed for export] *)
  assert (X20 : getr R6 (reg 20) = Z_to_bv 64 (F + 96)) by (rewrite (KS6 20%nat) by inl; rewrite (cs_of_preserved R4 R5 20 RP5) by inl; exact p20).
  assert (X23 : getr R6 (reg 23) = Z_to_bv 64 ro) by (rewrite (KS6 23%nat) by inl; rewrite (cs_of_preserved R4 R5 23 RP5) by inl; exact p23).
  pose proof (proj1 TRK6) as TN6. pose proof BI6 as (B6 & _).
  pose proof (proj1 TR6) as OBY6. pose proof (len_le_cap M6 ro by_ OBY6) as LCY. fold (L5.bo_cap by_) in LCY.
  assert (DYY : L5.bo_dyn by_ = false -> exists v0 v1, L5.bo_st by_ = L5.BInl v0 v1).
  { intros DF. destruct (L5.bo_st by_) as [v0 v1|c q] eqn:EST. exists v0, v1. reflexivity. exfalso. destruct OBY6 as (_ & _ & _ & OST). rewrite EST in OST. unfold L5.bo_dyn in DF. rewrite (proj1 OST) in DF. discriminate DF. }
  assert (CR5 : (3 <= nn)%nat -> L5.bo_dyn by_ = false -> acredit_ok L cr5 (8 * round_up (Z.of_nat nn))).
  { intros _ DYF. rewrite DYF in CRD. destruct gq as [|qg capg].
    - destruct GQF as (_ & _ & ->). apply (cred_ok1 L C LY cr4 2 _ _ CRD). clear; lia. clear - RUN; lia.
    - destruct GQF as (_ & _ & -> & -> & _). pose proof (cred_step L cr4 2 _ (8 * round_up (Z.of_nat n)) CRD ltac:(clear; lia) ltac:(clear - RUN; lia)) as X0.
      apply (cred_ok1 L C LY _ (2 - 1) _ (8 * round_up (Z.of_nat nn)) X0). clear; lia. clear - RUN; lia. }
  set (W3 := W2 ++ [(ro, 32); (L5.bo_data ro by_, 8 * L5.bo_cap by_)]).
  apply (G6A2 fx6 R6 M6 model6 W2 W3 BX5 LK5 cr5 A5 by_ bn wy wn BI6 RI6 X20 X23 AOR TR6 TN6).
  { rewrite LNN. clear - NNR. lia. }
  { intros DY. rewrite LNN. exact (CAPY DY). }
  { rewrite LNN. intros H3 DYF. exact (CR5 H3 DYF). }
  { intros c q c' q' Eq Eq'. apply (inv_blk_apart (BX5 ++ LB) _ _ _ _ _ _ q (8 * c) q' (8 * c') B6 (proj2 (proj2 (proj2 TR6)) c q Eq) (proj2 (proj2 (proj2 TN6)) c' q' Eq')).
    intros X0. exact (NQNY c' q' c q Eq' Eq (eq_sym X0)). }
  { intros a OUT. split. intros rr Hr. apply OUT. subst W3. apply in_or_app. left. exact Hr. intros rr [<-|[]]. apply OUT. subst W3. apply in_or_app. right. left. reflexivity. }
  { intros DL a _ OUT IR. rewrite LNN in DL, IR. unfold L5.in_rng in IR. cbn [fst snd] in IR.
    destruct (L5.bo_dyn by_) eqn:DYE.
    - apply (OUT (L5.bo_data ro by_, 8 * L5.bo_cap by_)). subst W3. apply in_or_app. right. right. left. reflexivity. unfold L5.in_rng. cbn [fst snd]. pose proof (CAPY eq_refl) as X0. clear - IR X0. lia.
    - destruct DL as [X0|LE2]. discriminate X0. destruct (DYY eq_refl) as (v0 & v1 & EST). unfold L5.bo_data in IR. rewrite EST in IR.
      apply (OUT (ro, 32)). subst W3. apply in_or_app. right. left. reflexivity. unfold L5.in_rng. cbn [fst snd]. clear - IR LE2. lia. }
  intros fx7 R7a R7 M7 model7 gr br cr7 LK7 A7 KS7 RP7 BI7 TR7 LENR GRF OFF7 IA7 ILK7.
  set (BX7 := match gr with Same => BX5 | Grown q cap => (q, 8 * cap) :: BX5 end) in *.
  assert (SUB7 : forall b0, In b0 (BX5 ++ LB) -> In b0 (BX7 ++ LB)). { intros b0 Hb. subst BX7. destruct gr. exact Hb. right. exact Hb. }
  assert (TRK7 : trk BX7 M7 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (trk_keep_arg W2 BX5 BX7 M6 M7 model6 LK5 cr5 A5 ASSIGN_SCR ro by_ wy bn bd bn0 bd0 wn wd on0 cells x BI6 AOR TR6 OFF7 SUB7 TRK6 NQNY NQDY). }
  assert (TQ7 : tob (BX7 ++ LB) M7 qo bq wq).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX5 ++ LB) (BX5 ++ LB) (BX7 ++ LB) LK5 cr5 A5 model6 ASSIGN_SCR _ M6 M7 qo bq wq B6 AOQ' TQ6 OFF7).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TQ6)) cap q Eq) as X0. split. exact X0. apply SUB7. exact X0.
    intros a O1 O2. apply (OREG_DISJ W2 BX5 M6 model6 LK5 cr5 A5 ro by_ wy qo bq wq a BI6 AOR' TR6 AOQ' TQ6 APRQ). 2: exact O2. 2: exact O1.
    intros c q c' q' Eq Eq'. unfold L5ADVEA.same_store in SS6. rewrite Eq' in SS6. destruct (L5.bo_st bq1) as [? ?|c1 q1] eqn:EST1. destruct SS6. destruct SS6 as (EC1 & EQ1).
    intros X0. apply (QFRESH c1 q1 c q eq_refl (proj2 (proj2 (proj2 TR4)) c q Eq)). clear - X0 EQ1. first [ lia | congruence ]. }
  (* [comment removed for export] *)
  assert (X21_6 : getr R6 (reg 21) = Z_to_bv 64 2147450880). { rewrite (KS6 21%nat) by inl. exact X21. }
  assert (KR7 : forall k, In k [18; 21; 22; 23; 24; 25; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. rewrite (cs_of_preserved R7a R7 k RP7) by (revert Hk; apply (L5K.incl_b [18; 21; 22; 23; 24; 25; 27]%nat); vm_compute; reflexivity).
    apply KS7. revert Hk. apply (L5K.incl_b [18; 21; 22; 23; 24; 25; 27]%nat). vm_compute; reflexivity. }
  assert (RI7 : rinvD R E R7). { apply (rinvD_pres R E R7a R7). apply (rinvD_ks R E R6 R7a KS_v5G6 RI6 KS7). vm_compute; reflexivity. exact RP7. }
  apply (KF fx7 R7 M7 model7 gq gr bq br W3 cr7 LK7 A7 wq BI7 RI7).
  - subst W3 W2. rewrite DT6, LN6. reflexivity.
  - rewrite (KR7 18%nat) by inl. exact p18.
  - rewrite (KR7 21%nat) by inl. exact X21_6.
  - rewrite (KR7 22%nat) by inl. rewrite (KS6 22%nat) by inl. exact X22.
  - rewrite (KR7 23%nat) by inl. exact X23.
  - rewrite (KR7 24%nat) by inl. rewrite DT6. exact p24.
  - rewrite (KR7 27%nat) by inl. rewrite (KS6 27%nat) by inl. apply (cs_of_preserved R4 R5 27 RP5). inl.
  - rewrite (KR7 25%nat) by inl. rewrite p25, LENQ. reflexivity.
  - exact TQ7.
  - rewrite LN6. exact LENQ.
  - rewrite FB6. destruct gq; [exact (proj1 GQF) | rewrite (proj1 GQF); reflexivity].
  - destruct gq as [|qg capg].
    + destruct GQF as (_ & SS & _). unfold L5ADVEA.same_store in SS, SS6. cbn [L5.bo_st] in SS. pose proof (proj1 TQ7) as (_ & _ & _ & OST).
      destruct (L5.bo_st bq1) as [? ?|? ?]. 2: destruct SS. destruct (L5.bo_st bq) as [? ?|? ?]. 2: destruct SS6. unfold L5.bo_dyn. exact (proj1 OST).
    + destruct GQF as (_ & ST & EC & _ & _ & N3). unfold L5ADVEA.same_store in SS6. rewrite ST in SS6. destruct (L5.bo_st bq) as [? ?|c1 q1]. destruct SS6. destruct SS6 as (-> & ->). split. reflexivity.
      split. exact EC. exact N3.
  - exact TR7.
  - rewrite LENR. exact LNN.
  - rewrite LNN in GRF. destruct gr as [|qr capr]. exact (conj (proj1 GRF) (proj1 (proj2 GRF))).
    destruct GRF as (G1 & G2' & G3 & _ & G5'). split. exact G1. split. exact G2'. split. exact G3. exact G5'.
  - exact TRK7.
  - destruct gr as [|qr capr]; destruct gq as [|qg capg]; cbn [L5DLA.blocks_of L5DLA.adebl].
    + rewrite (proj2 (proj2 GRF)). exact (proj2 (proj2 GQF)).
    + rewrite (proj2 (proj2 GRF)). destruct GQF as (_ & _ & EC & -> & _). reflexivity.
    + destruct GRF as (_ & _ & _ & -> & _). rewrite (proj2 (proj2 GQF)). reflexivity.
    + destruct GRF as (_ & _ & _ & -> & _). destruct GQF as (_ & _ & _ & -> & _). reflexivity.
  - intros a0 Ha0. apply IA7. apply IA5. exact Ha0.
  - intros f0 Hf0. apply ILK5. apply ILK7. exact Hf0.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGO2.

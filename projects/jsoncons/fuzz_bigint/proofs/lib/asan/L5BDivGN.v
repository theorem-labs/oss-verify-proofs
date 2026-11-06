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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BDivGU L5BRed L5BDivHH L5BDivHS L5BDivGE L5BDivN L5BDivO1 .
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGN.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cred_ok1 cr k b n : L5OMA.acredit_for L cr k b -> 1 <= k -> 0 <= n <= b -> acredit_ok L cr n.
Proof.
  intros (C1 & C2) Hk Hn. destruct (aly_cost L C LY) as (P1 & P2 & P3). unfold acredit_ok. split.
  - clear - C1 Hk P1. nia.
  - clear - C2 Hk Hn P2 P3. nia.
Qed.
Lemma cred_step cr k b n : L5OMA.acredit_for L cr k b -> 1 <= k -> 0 <= n <= b -> L5OMA.acredit_for L (adebit L cr n) (k - 1) (b - n).
Proof.
  intros (C1 & C2) Hk Hn. unfold L5OMA.acredit_for, adebit. cbn [fst snd]. split.
  - clear - C1. lia.
  - clear - C2. lia.
Qed.
Lemma cred_weak cr k b k' b' : L5OMA.acredit_for L cr k b -> 0 <= k' <= k -> 0 <= b' <= b -> L5OMA.acredit_for L cr k' b'.
Proof.
  intros (C1 & C2) Hk Hb. destruct (aly_cost L C LY) as (P1 & P2 & P3). unfold L5OMA.acredit_for. split.
  - clear - C1 Hk P1. nia.
  - clear - C2 Hk Hb P2 P3. nia.
Qed.

Lemma offx_trans LBx scr (X1 X2 : Z -> Prop) Ma Mb Mc' : offx LBx scr X1 Ma Mb -> offx LBx scr X2 Mb Mc' -> offx LBx scr (fun a => X1 a \/ X2 a) Ma Mc'.
Proof. intros O1 O2 a Ha Hc NX. rewrite (O2 a Ha Hc). apply (O1 a Ha Hc). intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. Qed.
Lemma rlen_mword : rlen [L5DSA.MWORD] = 1%nat. Proof. vm_compute. reflexivity. Qed.
Lemma mword_c : L5DLA.clz_of (nth_w [L5DSA.MWORD] (1 - 1)) = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u8_inj_gn Mk a b b' : L5.u8_at RSEGS Mk a b -> L5.u8_at RSEGS Mk a b' -> 0 <= b < 256 -> 0 <= b' < 256 -> b = b'.
Proof.
  unfold L5.u8_at. intros H1 H2 B1 B2. rewrite H1 in H2. assert (E2 : Z_to_bv 8 b = Z_to_bv 8 b') by congruence. clear H2. pose proof (f_equal bv_unsigned E2) as H2. rewrite !Z_to_bv_unsigned in H2.
  rewrite !bv_wrap_small in H2. exact H2. all: change (2 ^ Z.of_N 8) with 256; assumption.
Qed.

Lemma obj_limbs_prefix Mx fb m st rw n :
  L5C.obj_limbs RSEGS Mx (L5.BO fb m st) rw -> (n <= m)%nat -> (match st with L5.BInl _ _ => (m <= 2)%nat | _ => True end) ->
  L5C.obj_limbs RSEGS Mx (L5.BO fb n st) (firstn n rw).
Proof.
  intros (Lw & Rw & V) Hn Hst. unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st] in *. split. rewrite length_firstn. Lia.lia.
  split. apply (proj2 (L5W.words_ok_BF _)). apply (BigFactsBase.words_ok_firstn n rw). apply (proj1 (L5W.words_ok_BF rw)). exact Rw.
  destruct st as [v0 v1|cap q].
  - subst rw. rewrite L5C.firstn_firstn_le by Lia.lia. reflexivity.
  - apply L5C.limbs_at_firstn. exact V.
Qed.

(* [comment removed for export] *)
Lemma stk_dest W BX Mc modelc LKc crc Ac o : binv W BX Mc modelc LKc crc Ac -> L5OMA.stksh ar M (E - SCRD) -> SPA <= o -> o + 40 <= E -> o mod 8 = 0 ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (exists fbo, L5.u8_at RSEGS Mc o fbo /\ 0 <= fbo < 256) /\ shadow_zero Mc o 4.
Proof.
  intros BI SSH H1 H2 O8 NW. split.
  - pose proof BI as (_ & _ & _ & _ & _ & B6 & _). destruct B6 as (_ & _ & _ & _ & DSCR & _).
    apply L5ADVHA.u8_of_defined. specialize (DSCR (o - (E - SCRD)) ltac:(clear - H1 H2 HSCR; lia)). replace (E - SCRD + (o - (E - SCRD))) with o in DSCR by (clear; lia). exact DSCR.
  - apply (L5ADVGA.stk_shz L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR W BX Mc modelc LKc crc Ac o BI SSH H1 H2 O8).
    intros j Hj. apply NW.
    destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    unfold in_shadow_of, S. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    clear - Hj H1 H2 O8 SLO HSCR ER. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma g12_copies_s (fx : FPState) Rc Mc modelc BX LKc crc Ac bn bd wn wd on od (cells : list (Z * Z)) :
  binv [] BX Mc modelc LKc crc Ac -> rinvD R E Rc -> L5OMA.stksh ar M (E - SCRD) ->
  tob (BX ++ LB) Mc (F + 96) bn wn -> tob (BX ++ LB) Mc (F + 32) bd wd -> L5ADVD.obj_at Mc (F + 96) bn on -> L5ADVD.obj_at Mc (F + 32) bd od ->
  spl E Mc cells -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> getr Rc (reg 27) = Z_to_bv 64 F -> In (E - 304, F + 32) cells ->
  (L5.bo_dyn bn = true -> 8 * L5.bo_cap bn <= 2 ^ 27) -> (L5.bo_dyn bd = true -> 8 * L5.bo_cap bd <= 2 ^ 27) ->
  L5OMA.acredit_for L crc 2 (8 * L5.bo_cap bn + 8 * L5.bo_cap bd) ->
  (forall (fx' : FPState) R' M' model' (gn gd : growth) bn0 bd0 cr' LK' A',
      let BX' := L5DLA.blocks_of gd ++ L5DLA.blocks_of gn ++ BX in
      binv [] BX' M' model' LK' cr' A' -> rinvD R E R' ->
      getr R' (reg 19) = Z_to_bv 64 (F + 32) -> getr R' (reg 25) = Z_to_bv 64 (F + 96) ->
      (forall x, In x [18; 21; 22; 23; 24; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x)) ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) COPY_SCR (fun a => SPA + 168 <= a < SPA + 232 \/ E - 360 <= a < E - 352) Mc M' -> L5.u64_at RSEGS M' (E - 360) F ->
      L5ADVD.obj_at M' (SPA + 200) bn0 (L5ADVHO.on_of gn) -> L5ADVD.obj_at M' (SPA + 168) bd0 (L5ADVHO.on_of gd) ->
      (L5.bo_len bn0 = L5.bo_len bn /\ match gn with Same => L5.bo_st bn0 = L5.bo_st bn | Grown q cap => L5.bo_st bn0 = L5.BDyn cap q end) ->
      (L5.bo_len bd0 = L5.bo_len bd /\ match gd with Same => L5.bo_st bd0 = L5.bo_st bd | Grown q cap => L5.bo_st bd0 = L5.BDyn cap q end) ->
      (match gn with Same => L5.bo_dyn bn = false | Grown _ cap => cap = L5.bo_cap bn /\ L5.bo_dyn bn = true end) ->
      (match gd with Same => L5.bo_dyn bd = false | Grown _ cap => cap = L5.bo_cap bd /\ L5.bo_dyn bd = true end) ->
      cr' = L5DLA.adebl L crc (L5DLA.blocks_of gd ++ L5DLA.blocks_of gn) -> incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x930d0 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x930a8 Mc modelc) K.
Proof.
  intros BI RI SSH TN TD ON OD SPL X25 X27 IN88 CAPN CAPD CRD KF.
  destruct (SPL _ _ IN88) as (S88 & _).
  pose proof (one_le_cap Mc (F + 96) bn (proj1 TN)) as OCN. pose proof (one_le_cap Mc (F + 32) bd (proj1 TD)) as OCD. fold (L5.bo_cap bn) in OCN. fold (L5.bo_cap bd) in OCD.
  assert (E8 : (E - 184) mod 8 = 0 /\ (E - 216) mod 8 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (stk_dest [] BX Mc modelc LKc crc Ac (SPA + 200) BI SSH ltac:(clear; lia) ltac:(clear; lia) ltac:(replace (SPA + 200) with (E - 184) by (clear; lia); exact (proj1 E8)) ltac:(intros a _ rr []))
    as ((fbn & DFN & FBNR) & DSZN).
  apply (G1 fx Rc Mc modelc [] BX LKc crc Ac fbn bn wn BI RI X25 X27 DFN FBNR DSZN TN).
  { intros DY. split. exact (CAPN DY). apply (cred_ok1 crc 2 (8 * L5.bo_cap bn + 8 * L5.bo_cap bd) _ CRD). clear; lia. clear - OCN OCD; lia. }
  intros fx1 R1 R1' M1a M1 model1 gn LBn cr1 LK1 A1 KS1 AGa S360a TNa POST1 BI1 IA1 ILK1.
  set (BX1 := match gn with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) in *.
  (* [comment removed for export] *)
  assert (P1 : regs_preserved R1 R1' /\ ahpres L ar (BX ++ LB) FF' SPA COPY_SCR [(SPA + 200, 32)] M1a M1
               /\ (exists bn0, L5ADVD.obj_at M1 (SPA + 200) bn0 (L5ADVHO.on_of gn) /\ L5.bo_len bn0 = L5.bo_len bn /\ match gn with Same => L5.bo_st bn0 = L5.bo_st bn | Grown q cap => L5.bo_st bn0 = L5.BDyn cap q end)
               /\ (match gn with Same => L5.bo_dyn bn = false | Grown _ cap => cap = L5.bo_cap bn /\ L5.bo_dyn bn = true end)
               /\ cr1 = L5DLA.adebl L crc (L5DLA.blocks_of gn)).
  { destruct POST1 as (RP & PG). split. exact RP. destruct gn as [|q cap].
    - destruct PG as (DY & _ & ECR & OB0 & AH). split. exact AH. split. 2: split; [exact DY | exact ECR].
      eexists. split. apply (L5ADVHO.obj_at_copy M1 M1a (SPA + 200) (F + 96) _ bn Same OB0 (proj1 TNa)). cbn [L5.bo_st]. split. reflexivity. exact DY. split; reflexivity.
    - destruct PG as (DY & ECAP & _ & ECR & _ & OB0 & _ & AH). split. exact AH. split. 2: split; [split; [exact ECAP | exact DY] | exact ECR].
      eexists. split. apply (L5ADVHO.obj_at_copy M1 M1a (SPA + 200) (F + 96) _ bn (Grown q cap) OB0 (proj1 TNa)). cbn [L5.bo_st]. reflexivity. split; reflexivity. }
  destruct P1 as (RP1 & AH1 & (bn0 & ON0 & SHN0) & GN1 & ECR1).
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) COPY_SCR [(SPA + 200, 32)] M1a M1 AH1) as OFF1b.
  assert (OFF1a : offx (BX ++ LB) COPY_SCR (fun a => E - 360 <= a < E - 352) Mc M1a). { apply L5ADVEA.offx_of_frame. exact AGa. }
  pose proof (offx_trans _ _ _ _ _ _ _ OFF1a OFF1b) as OFF1. cbv beta in OFF1.
  pose proof BI as (B1 & _).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ (SPA <= a < E)).
  { intros o b ws a AO TO OR X. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX Mc modelc LKc crc Ac o b ws a BI AO TO OR). clear - X HSCR; lia. }
  assert (INW1 : forall a, L5ADVEA.inW [(SPA + 200, 32)] a -> SPA + 200 <= a < SPA + 232).
  { intros a (rr & [<-|[]] & IR). unfold L5.in_rng in IR. cbn [fst snd] in IR. clear - IR; lia. }
  assert (BXI : forall b0, In b0 (BX ++ LB) -> In b0 (BX1 ++ LB)). { intros b0 Hb. subst BX1. destruct gn. exact Hb. right. exact Hb. }
  assert (TD1 : tob (BX1 ++ LB) M1 (F + 32) bd wd).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX1 ++ LB) LKc crc Ac modelc COPY_SCR _ Mc M1 (F + 32) bd wd B1 AOD' TD OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TD)) cap q Eq) as X. split. exact X. apply BXI. exact X.
    intros a OR [X|X]; [ | apply INW1 in X]; apply (NOFR _ _ _ a AOD' TD OR); clear - X; lia. }
  assert (S88_1 : L5.u64_at RSEGS M1 (E - 304) (F + 32)).
  { apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX ++ LB) COPY_SCR _ Mc M1 _ _ S88 ltac:(clear; lia) ltac:(clear; lia) OFF1).
    intros i Hi [X|X]; [ | apply INW1 in X]; clear - Hi X; lia. }
  assert (S360_1 : L5.u64_at RSEGS M1 (E - 360) F).
  { apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX ++ LB) COPY_SCR _ M1a M1 _ _ S360a ltac:(clear; lia) ltac:(clear; lia) OFF1b).
    intros i Hi X. apply INW1 in X. clear - Hi X; lia. }
  assert (E20 : getr R1' (reg 25) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R1 R1' 25 RP1) by inl; rewrite (KS1 25%nat) by inl; exact X25).
  assert (RI1 : rinvD R E R1'). { apply (rinvD_pres R E R1 R1'). apply (rinvD_ks R E Rc R1 KS_v5G1 RI KS1). vm_compute; reflexivity. exact RP1. }
  assert (W1S : forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside [] a) by (intros a _ rr []).
  destruct (stk_dest [] BX1 M1 model1 LK1 cr1 A1 (SPA + 168) BI1 SSH ltac:(clear; lia) ltac:(clear; lia) ltac:(replace (SPA + 168) with (E - 216) by (clear; lia); exact (proj2 E8)) W1S)
    as ((fbd & DFD & FBDR) & DSZD).
  assert (CRD1 : L5OMA.acredit_for L cr1 1 (8 * L5.bo_cap bd)).
  { rewrite ECR1. destruct gn as [|q cap]; cbn [L5DLA.blocks_of L5DLA.adebl].
    - apply (cred_weak crc 2 (8 * L5.bo_cap bn + 8 * L5.bo_cap bd) _ _ CRD). clear; lia. clear - OCN OCD; lia.
    - destruct GN1 as (-> & _). pose proof (cred_step crc 2 (8 * L5.bo_cap bn + 8 * L5.bo_cap bd) (8 * L5.bo_cap bn) CRD ltac:(clear; lia) ltac:(clear - OCN OCD; lia)) as X.
      replace (2 - 1) with 1 in X by (clear; lia). replace (8 * L5.bo_cap bn + 8 * L5.bo_cap bd - 8 * L5.bo_cap bn) with (8 * L5.bo_cap bd) in X by (clear; lia). exact X. }
  apply (G2s fx1 R1' M1 model1 [] BX1 LK1 cr1 A1 fbd bd wd BI1 RI1 S88_1 DFD FBDR DSZD TD1).
  { intros DY. split. exact (CAPD DY). apply (cred_ok1 cr1 1 (8 * L5.bo_cap bd) _ CRD1). clear; lia. clear - OCD; lia. }
  intros fx2 R2 R2' M2' model2' gd LBd cr2' LK2' A2 KS2 p19 POST2 BI2 IA2 ILK2.
  assert (P2 : regs_preserved R2 R2' /\ ahpres L ar (BX1 ++ LB) FF' SPA COPY_SCR [(SPA + 168, 32)] M1 M2'
               /\ (exists bd0, L5ADVD.obj_at M2' (SPA + 168) bd0 (L5ADVHO.on_of gd) /\ L5.bo_len bd0 = L5.bo_len bd /\ match gd with Same => L5.bo_st bd0 = L5.bo_st bd | Grown q cap => L5.bo_st bd0 = L5.BDyn cap q end)
               /\ (match gd with Same => L5.bo_dyn bd = false | Grown _ cap => cap = L5.bo_cap bd /\ L5.bo_dyn bd = true end)
               /\ cr2' = L5DLA.adebl L cr1 (L5DLA.blocks_of gd)).
  { destruct POST2 as (RP & PG). split. exact RP. destruct gd as [|q cap].
    - destruct PG as (DY & _ & ECR & OB0 & AH). split. exact AH. split. 2: split; [exact DY | exact ECR].
      eexists. split. apply (L5ADVHO.obj_at_copy M2' M1 (SPA + 168) (F + 32) _ bd Same OB0 (proj1 TD1)). cbn [L5.bo_st]. split. reflexivity. exact DY. split; reflexivity.
    - destruct PG as (DY & ECAP & _ & ECR & _ & OB0 & _ & AH). split. exact AH. split. 2: split; [split; [exact ECAP | exact DY] | exact ECR].
      eexists. split. apply (L5ADVHO.obj_at_copy M2' M1 (SPA + 168) (F + 32) _ bd (Grown q cap) OB0 (proj1 TD1)). cbn [L5.bo_st]. reflexivity. split; reflexivity. }
  destruct P2 as (RP2 & AH2 & (bd0 & OD0 & SHD0) & GD2 & ECR2).
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F (BX1 ++ LB) COPY_SCR [(SPA + 168, 32)] M1 M2' AH2) as OFF2.
  assert (INW2 : forall a, L5ADVEA.inW [(SPA + 168, 32)] a -> SPA + 168 <= a < SPA + 200).
  { intros a (rr & [<-|[]] & IR). unfold L5.in_rng in IR. cbn [fst snd] in IR. clear - IR; lia. }
  assert (BX2E : match gd with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end = L5DLA.blocks_of gd ++ L5DLA.blocks_of gn ++ BX).
  { subst BX1. destruct gd, gn; reflexivity. }
  rewrite BX2E in BI2.
  apply (KF fx2 R2' M2' model2' gn gd bn0 bd0 cr2' LK2' A2 BI2).
  - apply (rinvD_pres R E R2 R2'). apply (rinvD_ks R E R1' R2 KS_v5G2 RI1 KS2). vm_compute; reflexivity. exact RP2.
  - rewrite (cs_of_preserved R2 R2' 19 RP2) by inl. exact p19.
  - rewrite (cs_of_preserved R2 R2' 25 RP2) by inl. rewrite (KS2 25%nat) by inl. exact E20.
  - intros x Hx. assert (Hc : In x cs_all) by (revert Hx; apply (L5K.incl_b [18; 21; 22; 23; 24; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (cs_of_preserved R2 R2' x RP2 Hc). rewrite (KS2 x) by (revert Hx; apply (L5K.incl_b [18; 21; 22; 23; 24; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (cs_of_preserved R1 R1' x RP1 Hc). apply KS1. revert Hx. apply (L5K.incl_b [18; 21; 22; 23; 24; 26; 27]%nat). vm_compute; reflexivity.
  - intros a Ha Hc NX. rewrite (OFF2 a Ha). apply (OFF1 a Ha Hc). intros [X|X]; [apply NX; right; exact X | apply INW1 in X; apply NX; left; clear - X; lia].
    + subst BX1. destruct gn. exact Hc. apply aclient_consb. exact Hc.
    + intros X. apply INW2 in X. apply NX. left. clear - X; lia.
  - apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX1 ++ LB) COPY_SCR _ M1 M2' _ _ S360_1 ltac:(clear; lia) ltac:(clear; lia) OFF2).
    intros i Hi X. apply INW2 in X. clear - Hi X; lia.
  - apply (L5ADVD.obj_at_agree M1 M2' (SPA + 200) bn0 _ ON0 ltac:(clear - ER; lia) ltac:(clear - ER; lia)). intros i Hi. apply OFF2. clear - Hi ER; lia.
    + apply stack_client. destruct G as [Hk SPT SLO SHI SPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. clear - Hi SLO SHI SPT HSCR; lia. clear - Hi; lia.
    + intros X. apply INW2 in X. clear - X Hi; lia.
  - exact OD0.
  - exact SHN0.
  - exact SHD0.
  - exact GN1.
  - exact GD2.
  - rewrite ECR2, ECR1. destruct gd, gn; reflexivity.
  - intros x Hx. apply IA2. apply IA1. exact Hx.
  - intros x Hx. apply ILK1. apply ILK2. exact Hx.
Qed.

Lemma g12_copies (fx : FPState) Rc Mc modelc BX LKc crc Ac bn bd wn wd on od (cells : list (Z * Z)) :
  binv [] BX Mc modelc LKc crc Ac -> rinvD R E Rc -> L5OMA.stksh ar M (E - SCRD) ->
  tob (BX ++ LB) Mc (F + 96) bn wn -> tob (BX ++ LB) Mc (F + 32) bd wd -> L5ADVD.obj_at Mc (F + 96) bn on -> L5ADVD.obj_at Mc (F + 32) bd od ->
  spl E Mc cells -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> getr Rc (reg 27) = Z_to_bv 64 F -> In (E - 304, F + 32) cells ->
  (L5.bo_dyn bn = true -> 8 * L5.bo_cap bn <= 2 ^ 27) -> (L5.bo_dyn bd = true -> 8 * L5.bo_cap bd <= 2 ^ 27) ->
  L5OMA.acredit_for L crc 2 (8 * L5.bo_cap bn + 8 * L5.bo_cap bd) ->
  (forall (fx' : FPState) R' M' model' (gn gd : growth) bn0 bd0 cr' LK' A',
      let BX' := L5DLA.blocks_of gd ++ L5DLA.blocks_of gn ++ BX in
      binv [] BX' M' model' LK' cr' A' -> rinvD R E R' ->
      getr R' (reg 19) = Z_to_bv 64 (F + 32) -> getr R' (reg 25) = Z_to_bv 64 (F + 96) ->
      (forall x, In x [18; 21; 22; 23; 24; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x)) ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) COPY_SCR (fun a => SPA + 168 <= a < SPA + 232 \/ E - 360 <= a < E - 352) Mc M' -> L5.u64_at RSEGS M' (E - 360) F ->
      L5ADVD.obj_at M' (SPA + 200) bn0 (L5ADVHO.on_of gn) -> L5ADVD.obj_at M' (SPA + 168) bd0 (L5ADVHO.on_of gd) ->
      (match gn with Same => L5.bo_dyn bn = false | Grown _ cap => cap = L5.bo_cap bn /\ L5.bo_dyn bn = true end) ->
      (match gd with Same => L5.bo_dyn bd = false | Grown _ cap => cap = L5.bo_cap bd /\ L5.bo_dyn bd = true end) ->
      cr' = L5DLA.adebl L crc (L5DLA.blocks_of gd ++ L5DLA.blocks_of gn) -> incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x930d0 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x930a8 Mc modelc) K.
Proof.
  intros BI RI SSH TN TD ON OD SPL X25 X27 IN88 CAPN CAPD CRD KF.
  apply (g12_copies_s fx Rc Mc modelc BX LKc crc Ac bn bd wn wd on od cells BI RI SSH TN TD ON OD SPL X25 X27 IN88 CAPN CAPD CRD).
  intros fx' R' M' model' gn gd bn0 bd0 cr' LK' A' BX' BI' RI' p19 p20 KS OFF S360 ON0 OD0 _ _ GNF GDF ECR IA ILK.
  exact (KF fx' R' M' model' gn gd bn0 bd0 cr' LK' A' BI' RI' p19 p20 KS OFF S360 ON0 OD0 GNF GDF ECR IA ILK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shz_off_self W BX Mc modelc LKc crc Ac o b ws j : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> 0 <= j < 4 ->
  ~ (o <= o / 8 + SB + j < o + 32) /\ (forall cap q, L5.bo_st b = L5.BDyn cap q -> ~ (q <= o / 8 + SB + j < q + 8 * cap)).
Proof.
  intros BI AOB (OB & _ & _ & INB) Hj. pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct G as [Hk SPT SLO SHI SPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  assert (SR : 2147450880 <= o / 8 + SB + j < 2147450880 + 17592186044416) by (unfold SB; clear - OR Hj SLO SHI SPT SPC; lia).
  assert (N1 : ~ (o <= o / 8 + SB + j < o + 32)) by (unfold SB; clear - OR OBIG Hj; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  split. exact N1.
  intros cap q Eq X. pose proof (WB (q, 8 * cap) (INB cap q Eq)) as ((R0 & R1 & R2 & R3 & R4 & R5) & _). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in R5.
  clear - SR X R5 R3. lia.
Qed.

Lemma arg_after W BX Mc modelc LKc crc Ac M' o b ws (fbS fbG : Z) (n : nat) (ws' : list Z) (g : growth) scr (Wc : list L5.range) :
  binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> tob (BX ++ LB) Mc o b ws ->
  match g with
  | Same => exists st', L5.big_at RSEGS M' o (L5.BO fbS n st') /\ L5C.obj_limbs RSEGS M' (L5.BO fbS n st') ws' /\ L5ADVEA.same_store b st'
  | Grown q cap => L5.big_at RSEGS M' o (L5.BO fbG n (L5.BDyn cap q)) /\ L5C.obj_limbs RSEGS M' (L5.BO fbG n (L5.BDyn cap q)) ws'
  end ->
  ahpres L ar (BX ++ LB) FF' SPA scr Wc Mc M' ->
  (forall a, L5ADVEA.inW Wc a -> o <= a < o + 32 \/ (exists cap q, L5.bo_st b = L5.BDyn cap q /\ q <= a < q + 8 * cap)) ->
  exists b1, tob ((match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) ++ LB) M' o b1 ws' /\ L5.bo_len b1 = n
     /\ match g with Same => L5.bo_fb b1 = fbS /\ L5ADVEA.same_store b (L5.bo_st b1) | Grown q cap => L5.bo_fb b1 = fbG /\ L5.bo_st b1 = L5.BDyn cap q end.
Proof.
  intros BI AOB TO PG AH WIN. pose proof BI as (B1 & _). assert (AOB' : aobj FF' o 32) by (apply aobj_cons; exact AOB).
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) scr Wc Mc M' AH) as OFF.
  assert (SZ' : shadow_zero M' o 4).
  { apply (L5ADVEA.shz_keep L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) LKc crc Ac modelc scr _ Mc M' o B1 AOB' (proj1 (proj2 (proj2 TO))) OFF).
    intros j Hj X. destruct (shz_off_self W BX Mc modelc LKc crc Ac o b ws j BI AOB' TO Hj) as (N1 & N2).
    destruct (WIN _ X) as [Y|(cap & q & Eq & Y)]. exact (N1 Y). exact (N2 cap q Eq Y). }
  destruct g as [|q cap].
  - destruct PG as (st' & OB' & OL' & SS). exists (L5.BO fbS n st'). split. 2: split; [reflexivity | split; [reflexivity | exact SS]].
    split. exact OB'. split. exact OL'. split. exact SZ'. cbn [L5.bo_st]. intros cap q Eq. subst st'. unfold L5ADVEA.same_store in SS.
    destruct (L5.bo_st b) as [v0 v1|cap0 q0] eqn:EB. destruct SS. destruct SS as (-> & ->). apply (proj2 (proj2 (proj2 TO)) cap0 q0). exact EB.
  - destruct PG as (OB' & OL'). exists (L5.BO fbG n (L5.BDyn cap q)). split. 2: split; [reflexivity | split; reflexivity].
    split. exact OB'. split. exact OL'. split. exact SZ'. cbn [L5.bo_st]. intros cap1 q1 Eq. injection Eq as <- <-. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma oreg_disj W BX Mc modelc LKc crc Ac o1 b1 ws1 o2 b2 ws2 a : binv W BX Mc modelc LKc crc Ac ->
  aobj FF' o1 32 -> tob (BX ++ LB) Mc o1 b1 ws1 -> aobj FF' o2 32 -> tob (BX ++ LB) Mc o2 b2 ws2 -> (o1 + 32 <= o2 \/ o2 + 32 <= o1) ->
  (forall c q c' q', L5.bo_st b1 = L5.BDyn c q -> L5.bo_st b2 = L5.BDyn c' q' -> q <> q') ->
  L5ADVEA.oreg o1 b1 a -> L5ADVEA.oreg o2 b2 a -> False.
Proof.
  intros BI AO1 T1 AO2 T2 AP NQ OR1 OR2. pose proof BI as (B1 & _).
  destruct OR2 as [X|[X|(c2 & q2 & E2 & X)]].
  - eapply L5ADVEA.oreg_hdr with (o := o1) (o2 := o2) (a := a); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR | exact BI | exact AO1 | exact T1 | exact AO2 | exact AP | exact OR1 | exact X].
  - eapply L5ADVEA.oreg_shd with (o := o1) (o2 := o2) (a := a); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR | exact BI | exact AO1 | exact T1 | exact AO2 | exact AP | exact OR1 | exact X].
  - pose proof (proj2 (proj2 (proj2 T2)) c2 q2 E2) as IN2.
    eapply L5ADVEA.oreg_blk with (o := o1) (q2 := q2) (n2 := 8 * c2) (a := a); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR | exact BI | exact AO1 | exact T1 | exact IN2 | exact OR1 | exact X].
    intros c1 q1 E1. pose proof (proj2 (proj2 (proj2 T1)) c1 q1 E1) as IN1.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WB _ IN1)))))) as BA. cbn [fst snd] in BA.
    specialize (BA (q2, 8 * c2) (L5ADVHO.in_lb_remove q1 (q2, 8 * c2) _ IN2 ltac:(cbn [fst]; intros X0; exact (NQ c1 q1 c2 q2 E1 E2 (eq_sym X0))))). cbn [fst snd] in BA. clear - BA. lia.
Qed.

(* [comment removed for export] *)
Lemma tob_data_upd LBx (Mc M' : word -> option byte) o b ws : tob LBx Mc o b ws -> 4096 <= o -> o + 32 <= 2 ^ 47 ->
  (forall a, o <= a < o + 32 -> ~ (L5.bo_data o b <= a < L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b)) -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall j, 0 <= j < 4 -> M' (Z_to_bv 64 (o / 8 + SB + j)) = Mc (Z_to_bv 64 (o / 8 + SB + j))) ->
  L5.defined M' (L5.bo_data o b) (8 * Z.of_nat (L5.bo_len b)) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> q + 8 * cap <= o \/ o + 32 <= q) ->
  exists b' ws', tob LBx M' o b' ws' /\ L5.bo_fb b' = L5.bo_fb b /\ L5.bo_len b' = L5.bo_len b /\ L5ADVEA.same_store b (L5.bo_st b') /\ L5.bo_data o b' = L5.bo_data o b.
Proof.
  intros (OB & OL & SZ & INB) O1 O2 AGH AGS DEF APB.
  assert (SZ' : shadow_zero M' o 4). { intros j Hj. unfold byte_at, S. rewrite (AGS j Hj). exact (SZ j Hj). }
  destruct b as [fb len sto]. unfold L5.bo_data, L5ADVEA.same_store in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct OB as (B0 & FBR & B8 & OST).
  destruct sto as [v0 v1|cap q].
  - destruct OST as (BT & B16 & B24 & N2 & V0R & V1R). cbn [L5.bo_len L5.bo_fb L5.bo_st] in *.
    assert (KP : forall a n, o <= a -> a + n <= o + 16 -> forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
    { intros a n H1 H2 i Hi. apply AGH. clear - Hi H1 H2; lia. clear - Hi H1 H2; lia. }
    assert (CELL : forall k v, (k = 16 \/ k = 24) -> L5.u64_at RSEGS Mc (o + k) v -> 0 <= v < 2 ^ 64 -> exists v', L5.u64_at RSEGS M' (o + k) v' /\ 0 <= v' < 2 ^ 64).
    { intros k v Hk Hc Hv. destruct (Z_lt_le_dec (o + k) (o + 16 + 8 * Z.of_nat len)) as [IN|OUT].
      - apply (L5ADVHL.word_of_defined M' (o + k)). 2: clear - O1 Hk; lia. 2: clear - O2 Hk; lia.
        intros i Hi. replace (o + k + i) with (o + 16 + (k - 16 + i)) by (clear; lia). apply DEF. clear - Hi Hk IN N2. lia.
      - exists v. split. 2: exact Hv. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - O1 Hk; lia. 2: clear - O2 Hk; lia.
        intros i Hi. apply AGH. clear - Hi Hk; lia. clear - Hi Hk OUT; lia. }
    destruct (CELL 16 v0 ltac:(left; reflexivity) B16 V0R) as (v0' & C16 & V0R'). destruct (CELL 24 v1 ltac:(right; reflexivity) B24 V1R) as (v1' & C24 & V1R').
    exists (L5.BO fb len (L5.BInl v0' v1')), (firstn len [v0'; v1']). cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. 2: repeat split.
    split. { split. eapply L5C.u8_at_agree. 4: exact B0. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP o 1 ltac:(clear; lia) ltac:(clear; lia)).
             split. exact FBR. split. eapply L5C.u64_at_agree. 4: exact B8. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP (o + 8) 8 ltac:(clear; lia) ltac:(clear; lia)).
             cbn [L5.bo_st L5.bo_fb L5.bo_len]. split. exact BT. split. exact C16. split. exact C24. split. exact N2. split. exact V0R'. exact V1R'. }
    split. { apply (L5ADVO1.inl_limbs M' o fb len v0' v1').
             split. eapply L5C.u8_at_agree. 4: exact B0. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP o 1 ltac:(clear; lia) ltac:(clear; lia)).
             split. exact FBR. split. eapply L5C.u64_at_agree. 4: exact B8. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP (o + 8) 8 ltac:(clear; lia) ltac:(clear; lia)).
             cbn [L5.bo_st L5.bo_fb L5.bo_len]. split. exact BT. split. exact C16. split. exact C24. split. exact N2. split. exact V0R'. exact V1R'. }
    split. exact SZ'. intros cap q Eq. discriminate Eq.
  - destruct OST as (BT & B16 & B24 & LC & CR & Q8 & Q4096 & Q47 & HA). cbn [L5.bo_len L5.bo_fb L5.bo_st] in *.
    specialize (APB cap q eq_refl).
    assert (KP : forall a n, o <= a -> a + n <= o + 32 -> forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
    { intros a n H1 H2 i Hi. apply AGH. clear - Hi H1 H2; lia. clear - Hi H1 H2 APB LC. lia. }
    destruct (limbs_of_defined M' q len DEF ltac:(clear - Q4096; lia) ltac:(clear - Q47 LC CR; lia)) as (ws' & LW & RW & LA).
    exists (L5.BO fb len (L5.BDyn cap q)), ws'. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. 2: repeat split.
    split. { split. eapply L5C.u8_at_agree. 4: exact B0. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP o 1 ltac:(clear; lia) ltac:(clear; lia)).
             split. exact FBR. split. eapply L5C.u64_at_agree. 4: exact B8. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP (o + 8) 8 ltac:(clear; lia) ltac:(clear; lia)).
             cbn [L5.bo_st L5.bo_fb L5.bo_len]. split. exact BT.
             split. eapply L5C.u64_at_agree. 4: exact B16. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP (o + 16) 8 ltac:(clear; lia) ltac:(clear; lia)).
             split. eapply L5C.u64_at_agree. 4: exact B24. 2: clear - O1; lia. 2: clear - O2; lia. exact (KP (o + 24) 8 ltac:(clear; lia) ltac:(clear; lia)).
             split. exact LC. split. exact CR. split. exact Q8. split. exact Q4096. split. exact Q47. exact HA. }
    split. { split. exact LW. split. exact RW. exact LA. }
    split. exact SZ'. exact INB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shz_loc_norm W BX Mc M1 M' modelc LKc crc Ac (Wn : list L5.range) k bd bn :
  binv W BX Mc modelc LKc crc Ac -> (k = 32 \/ k = 96) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 220 <= a < E - 216) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  L5ADVEA.offx L ar FF E F (BX ++ LB) L5DLA.NORM_SCR (L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn)) M1 M' ->
  (forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) -> (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  shadow_zero Mc (F + k) 4 -> shadow_zero M' (F + k) 4.
Proof.
  intros BI Hk AG1 OFF INBD INBN SZ j Hj. unfold byte_at, S.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SQ : (F + k) / 8 = F / 8 + k / 8 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416 /\ (k / 8 = 4 \/ k / 8 = 12)) by (hnf in ALF; clear - FRP ALF Hk; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SQ as (SQ1 & SQ2 & SQ3 & SQ4). set (s := (F + k) / 8 + SB + j) in *.
  assert (SR : F / 8 + SB <= s < F / 8 + SB + 64 /\ 2147450880 <= s < 17594333495296) by (subst s; unfold SB; clear - SQ1 SQ2 SQ3 SQ4 Hj; lia). destruct SR as (SR1 & SR2).
  rewrite OFF.
  - rewrite AG1. exact (SZ j Hj). clear - SR2; lia. clear - SR2 ER; lia.
  - clear - SR2; lia.
  - apply (fframe_shadow_client L ar (BX ++ LB) FF' SPA L5DLA.NORM_SCR F 3 (SPA + 32)). left; reflexivity. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    hnf in ALF. clear - SR1 ALF FRP. unfold SB in *. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    intros (rr & Hr & IR). unfold L5.in_rng in IR. unfold L5DLA.norm_W in Hr. cbn [app In] in Hr.
    destruct Hr as [<-|[<-|[<-|Hr]]]; cbn [fst snd] in IR.
    + clear - IR SR2 FBIG; lia.
    + clear - IR SR2 FBIG; lia.
    + clear - IR SR2 ER; lia.
    + assert (BLK : exists cap q, In (q, 8 * cap) (BX ++ LB) /\ rr = (q, 8 * cap)).
      { apply in_app_or in Hr. unfold L5DLA.dyn_area in Hr. destruct Hr as [Hr|Hr].
        - destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:EB. destruct Hr. destruct Hr as [<-|[]]. exists cap, q. split. apply (INBD cap q eq_refl). reflexivity.
        - destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:EB. destruct Hr. destruct Hr as [<-|[]]. exists cap, q. split. apply (INBN cap q eq_refl). reflexivity. }
      destruct BLK as (cap & q & INQ & ->). cbn [fst snd] in IR.
      destruct (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR W BX Mc modelc LKc crc Ac q (8 * cap) s BI INQ IR) as (_ & Y & _).
      apply Y. change (ff_bytes 3 / 8) with 64. exact SR1.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition gro_st (g : growth) (b : L5.bigobj) (st' : L5.bstore) : Prop :=
  match g with Same => L5ADVEA.same_store b st' | Grown A cap => L5.bo_dyn b = false /\ cap = 8 /\ st' = L5.BDyn cap A end.

Lemma norm_tobs W BX Mc M1 M' modelc LKc crc Ac R1 R' bd bn wd wn c gd gn LBn cr' LK' :
  binv W BX Mc modelc LKc crc Ac ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 220 <= a < E - 216) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  tob (BX ++ LB) Mc (F + 32) bd wd -> tob (BX ++ LB) Mc (F + 96) bn wn ->
  L5DLA.norm_postA L ar (BX ++ LB) FF' LK' crc M1 M' R1 R' (F + 32) (F + 96) (E - 220) SPA bd bn wd wn c gd gn LBn cr' ->
  let sec := L5DLA.second (L5.bo_len bd) (L5DLA.shl_result wd c) in
  let rd := L5DLA.norm_words wd c sec in let rn := L5DLA.norm_words wn c sec in
  let BX' := L5DLA.blocks_of gn ++ L5DLA.blocks_of gd ++ BX in
  exists fbd' fbn' std stn,
       tob (BX' ++ LB) M' (F + 32) (L5.BO fbd' (rlen rd) std) (firstn (rlen rd) rd) /\ tob (BX' ++ LB) M' (F + 96) (L5.BO fbn' (rlen rn) stn) (firstn (rlen rn) rn)
    /\ gro_st gd bd std /\ gro_st gn bn stn
    /\ (match std with L5.BDyn cap _ => Z.of_nat (length rd) <= cap | L5.BInl _ _ => (length rd <= 2)%nat end)
    /\ (match stn with L5.BDyn cap _ => Z.of_nat (length rn) <= cap | L5.BInl _ _ => (length rn <= 2)%nat end)
    /\ L5ADVEA.offx L ar FF E F (BX ++ LB) L5DLA.NORM_SCR (L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn)) M1 M'.
Proof.
  intros BI AG1 TD TN POST sec rd rn BX'.
  destruct POST as (RP & EC & CR & TOP & E10 & PX & (std & stn & OAD & OAN) & ELB & ECR & FRD & FRN & AH & GD & GN). cbv zeta in *.
  fold sec in OAD, OAN. fold rd in OAD. fold rn in OAN.
  pose proof (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) L5DLA.NORM_SCR _ M1 M' AH) as OFF.
  destruct OAD as (WOD & LED & OBD' & OLD' & CAPD & GRD). destruct OAN as (WON & LEN & OBN' & OLN' & CAPN & GRN).
  pose proof (proj2 (proj2 (proj2 TD))) as INBD. pose proof (proj2 (proj2 (proj2 TN))) as INBN.
  assert (SUB : forall b0, In b0 (BX ++ LB) -> In b0 (BX' ++ LB)).
  { intros b0 Hb. subst BX'. rewrite <- !app_assoc. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  eexists _, _, std, stn.
  split; [|split; [|split; [|split; [|split; [exact CAPD | split; [exact CAPN | exact OFF]]]]]].
  - split. exact OBD'. split. { apply obj_limbs_prefix with (m := length rd). exact OLD'. exact LED. destruct std. exact CAPD. exact I. }
    split. { apply (shz_loc_norm W BX Mc M1 M' modelc LKc crc Ac [] 32 bd bn BI ltac:(left; reflexivity) AG1 OFF INBD INBN (proj1 (proj2 (proj2 TD)))). }
    cbn [L5.bo_st]. intros cap q Eq. subst std. destruct gd as [|Ag capg].
    + unfold L5ADVEA.same_store in GRD. destruct (L5.bo_st bd) as [v0 v1|cap0 q0] eqn:EB. destruct GRD. destruct GRD as (-> & ->). apply SUB. apply (INBD cap0 q0 eq_refl).
    + destruct GRD as (_ & _ & Eq'). injection Eq' as E1 E2. rewrite E1, E2. subst BX'. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
  - split. exact OBN'. split. { apply obj_limbs_prefix with (m := length rn). exact OLN'. exact LEN. destruct stn. exact CAPN. exact I. }
    split. { apply (shz_loc_norm W BX Mc M1 M' modelc LKc crc Ac [] 96 bd bn BI ltac:(right; reflexivity) AG1 OFF INBD INBN (proj1 (proj2 (proj2 TN)))). }
    cbn [L5.bo_st]. intros cap q Eq. subst stn. destruct gn as [|Ag capg].
    + unfold L5ADVEA.same_store in GRN. destruct (L5.bo_st bn) as [v0 v1|cap0 q0] eqn:EB. destruct GRN. destruct GRN as (-> & ->). apply SUB. apply (INBN cap0 q0 eq_refl).
    + destruct GRN as (_ & _ & Eq'). injection Eq' as E1 E2. rewrite E1, E2. subst BX'. apply in_or_app. left. apply in_or_app. left. left. reflexivity.
  - unfold gro_st. destruct gd; exact GRD.
  - unfold gro_st. destruct gn; exact GRN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_sgn_gn M' o b rw g st' fb' n' st2 : L5DLA.obj_after M' o b rw g st' -> L5.big_at RSEGS M' o (L5.BO fb' n' st2) -> Z.testbit (L5.bo_fb b) 1 = false -> Z.testbit fb' 1 = false.
Proof.
  intros (_ & _ & OB & _) (U8 & FR & _) SG. cbv zeta in OB. destruct OB as (U8' & FR' & _). cbn [L5.bo_fb] in *.
  rewrite (u8_inj_gn M' o _ _ U8 U8' FR FR').
  assert (X : Z.testbit (match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end) 1 = false). { destruct g. exact SG. rewrite Z.lor_spec, SG. reflexivity. }
  destruct (Nat.eqb _ 0). rewrite Z.land_spec, X. reflexivity. exact X.
Qed.

Lemma gn_front (cr0 : credit) (X : Z) (bX : L5.bigobj) (wX : list Z) (fx1 : FPState) q2 R1 M1 model1 cr1 LK1 A1 qn bits bn bd :
  ri_inv HI LB FF LK cr0 A M (vml_of model) -> L5OMA.stksh ar M (E - SCRD) ->
  tob LB M X bX wX -> aobj FF X 32 -> (2 <= L5.bo_len bX <= 6)%nat -> 0 <= ro < 2 ^ 64 ->
  L5OMA.acredit_for L cr1 2 128 ->
  atG L ar HI R M model LB FF LK A E SCRD F ro Same (Grown q2 8) R1 M1 model1 cr1 LK1 A1 X X qn bits 0 bn bd wX [L5DSA.MWORD] ->
  L5.bo_len bn = L5.bo_len bX -> L5.bo_st bn = L5.BDyn 8 q2 -> L5.bo_len bd = 1%nat -> L5.bo_st bd = L5.BInl L5DSA.MWORD 0 ->
  (forall (fx4 : FPState) R4 M4 model4 q0 bn0 bd0 fbd' fbn' d1 cr4 LK4 A4,
      let BX4 := (q0, 8 * 8) :: L5ADVHO.bx12 Same (Grown q2 8) in
      binv [] BX4 M4 model4 LK4 cr4 A4 -> rinvD R E R4 ->
      (forall x, In x [18; 21; 22; 26; 27]%nat -> getr R4 (reg x) = getr R1 (reg x)) ->
      getr R4 (reg 19) = Z_to_bv 64 (F + 32) -> getr R4 (reg 25) = Z_to_bv 64 (F + 96) ->
      getr R4 (reg 1) = Z_to_bv 64 0x9313c -> getr R4 (reg 10) = Z_to_bv 64 X -> getr R4 (reg 11) = Z_to_bv 64 (Z.of_nat (rlen wX) - 1) ->
      getr R4 (reg 20) = Z_to_bv 64 (Z.of_nat (rlen wX)) -> getr R4 (reg 24) = Z_to_bv 64 0 ->
      tob (BX4 ++ LB) M4 (F + 32) (L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1)) [L5DSA.MWORD] ->
      tob (BX4 ++ LB) M4 (F + 96) (L5.BO fbn' (rlen wX) (L5.BDyn 8 q2)) (firstn (rlen wX) wX) ->
      L5ADVD.obj_at M4 (SPA + 200) bn0 (Some (q0, 8 * 8)) -> L5ADVD.obj_at M4 (SPA + 168) bd0 None ->
      L5.bo_len bn0 = L5.bo_len bX -> L5.bo_st bn0 = L5.BDyn 8 q0 -> L5.bo_len bd0 = 1%nat -> L5.bo_st bd0 = L5.BInl L5DSA.MWORD 0 ->
      Z.testbit fbd' 1 = false -> Z.testbit fbn' 1 = false -> dsh M4 F 0 248 248 248 248 ->
      spl E M4 [(E - 304, F + 32); (E - 344, 0); (E - 296, X); (E - 264, X); (E - 288, ro); (E - 328, bits); (E - 280, F + 96); (E - 312, qn); (E - 336, F); (E - 320, X / 8 + 2147450880); (E - 352, (X + 8) / 8 + 2147450880)] ->
      L5.u64_at RSEGS M4 (E - 360) F -> L5.u64_at RSEGS M4 (E - 120) (F + 48) -> L5.u64_at RSEGS M4 (E - 112) 1 -> L5.u64_at RSEGS M4 (E - 272) 1 -> L5.u64_at RSEGS M4 F 1102416563 ->
      L5.u32_at RSEGS M4 (E - 220) 0 ->
      cr4 = adebit L cr1 64 -> incl A1 A4 -> incl LK4 LK1 ->
      srealizes RSEGS SCFG (cfg (fx:=fx4) R4 RESIZE M4 model4) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x930a8 M1 model1) K.
Proof.
  intros HH0 SSH TX AOX LENX ROR CRD (BI0 & RI0 & X18 & X21 & X22 & X25 & X26 & X27 & QNR & BITSR & TN & TD & ON & OD & SGN_N & SGN_D & SPL & DSH & HDR) LNB STN LND STD KF.
  set (BX0 := L5ADVHO.bx12 Same (Grown q2 8)) in *.
  set (cells := [(E - 304, F + 32); (E - 344, 0); (E - 296, X); (E - 264, X); (E - 288, ro); (E - 328, bits); (E - 280, F + 96); (E - 312, qn); (E - 336, F); (E - 320, X / 8 + 2147450880); (E - 352, (X + 8) / 8 + 2147450880)]) in *.
  assert (CAPN : L5.bo_cap bn = 8) by (unfold L5.bo_cap; rewrite STN; reflexivity). assert (CAPD : L5.bo_cap bd = 2) by (unfold L5.bo_cap; rewrite STD; reflexivity).
  assert (DYN : L5.bo_dyn bn = true). { destruct TN as ((_ & _ & _ & OST) & _). rewrite STN in OST. exact (proj1 OST). }
  assert (DYD : L5.bo_dyn bd = false). { destruct TD as ((_ & _ & _ & OST) & _). rewrite STD in OST. exact (proj1 OST). }
  apply (g12_copies_s fx1 R1 M1 model1 BX0 LK1 cr1 A1 bn bd wX [L5DSA.MWORD] _ _ cells BI0 RI0 SSH TN TD ON OD SPL X25 X27).
  { subst cells. left. reflexivity. }
  { intros _. rewrite CAPN. clear; lia. } { intros _. rewrite CAPD. clear; lia. }
  { rewrite CAPN, CAPD. apply (cred_weak cr1 2 128 _ _ CRD). clear; lia. clear; lia. }
  intros fx2 R2 M2' model2' gn gd bn0 bd0 cr2' LK2' A2 BX2 BI2 RI2 p19 p25 KS2 OFF2 S360_2 ON0 OD0 (LNN0 & STN0) (LND0 & STD0) GNF GDF ECR2 IA2 ILK2.
  destruct gn as [|q0 cap0]. { rewrite DYN in GNF. discriminate GNF. } destruct GNF as (EC0 & _). rewrite CAPN in EC0. subst cap0.
  destruct gd as [|qd capd]. 2:{ destruct GDF as (_ & X0). rewrite DYD in X0. discriminate X0. }
  cbn [L5DLA.blocks_of app L5ADVHO.on_of L5DLA.adebl] in *.
  subst BX2. cbn [L5DLA.blocks_of app L5ADVHO.on_of L5DLA.adebl] in *. set (BX2 := (q0, 8 * 8) :: BX0) in *.
  pose proof BI0 as (B1 & _).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX0 ++ LB) M1 o b ws -> L5ADVEA.oreg o b a -> ~ (SPA + 168 <= a < SPA + 232 \/ E - 360 <= a < E - 352)).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX0 M1 model1 LK1 cr1 A1 o b ws a BI0 AO TO OR). clear - X0 HSCR; lia. }
  assert (SUB2 : forall b0, In b0 (BX0 ++ LB) -> In b0 (BX2 ++ LB)) by (intros b0 Hb; right; exact Hb).
  assert (TN2 : tob (BX2 ++ LB) M2' (F + 96) bn wX).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX0 ++ LB) (BX0 ++ LB) (BX2 ++ LB) LK1 cr1 A1 model1 COPY_SCR _ M1 M2' (F + 96) bn wX B1 AON' TN OFF2).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN)) cap q Eq) as X0. split. exact X0. apply SUB2. exact X0. intros a OR. exact (NOFR _ _ _ a AON' TN OR). }
  assert (TD2 : tob (BX2 ++ LB) M2' (F + 32) bd [L5DSA.MWORD]).
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
  assert (SHQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416).
  { hnf in ALF. clear - FRP ALF. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (DSH2 : dsh M2' F 0 248 248 248 248).
  { eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH | exact OFF2 | ]. intros j Hj X0. clear - Hj X0 SHQ ER. lia. }
  (* [comment removed for export] *)
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX).
  assert (XRG : 0 <= X < 2 ^ 64). { edestruct L5ADVEA.obj_rng with (o := X) as ((Y1 & Y2 & _) & _); try first [exact LY | exact HIok | exact BI2 | exact AOX']. clear - Y1 Y2; lia. }
  assert (E8 : (E - 224) mod 8 = 0 /\ (E - 220) / 8 = (E - 224) / 8). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SZP : shadow_zero M2' (E - 220) 1).
  { destruct (stk_dest [] BX2 M2' model2' LK2' cr2' A2 (E - 224) BI2 SSH ltac:(clear; lia) ltac:(clear; lia) (proj1 E8) ltac:(intros a _ rr [])) as (_ & SZ176).
    intros j Hj. assert (j = 0) by (clear - Hj; lia). subst j. specialize (SZ176 0 ltac:(clear; lia)). unfold byte_at, S in *. rewrite (proj2 E8). exact SZ176. }
  apply (G3 fx2 R2 M2' model2' [] BX2 LK2' cr2' A2 X bd [L5DSA.MWORD] bn wX BI2 RI2 p19 p25 ltac:(rewrite (KS2 21%nat) by inl; exact X21) XRG ROR SZP ltac:(intros a _ rr []) TD2 TN2).
  { intros cap q Eq. rewrite STD in Eq. discriminate Eq. }
  { intros cap q Eq. rewrite STN in Eq. injection Eq as <- <-. right. subst BX0. simpl. left. reflexivity. }
  { rewrite LND. clear; lia. }
  { rewrite LND. vm_compute. intros X0; discriminate X0. }
  { rewrite LND. intros X0. exfalso. clear - X0; lia. }
  { rewrite LNB. clear - LENX; lia. }
  { rewrite LND. intros X0. exfalso. clear - X0; lia. }
  { intros cap q Eq. rewrite STD in Eq. discriminate Eq. }
  { intros cap q Eq. rewrite STN in Eq. injection Eq as <- _. rewrite LNB. clear - LENX; lia. }
  { rewrite LND. intros X0. exfalso. unfold L5DLA.second in X0. cbn [Nat.leb andb] in X0. discriminate X0. }
  { intros cd qd cn qn0 Eq. rewrite STD in Eq. discriminate Eq. }
  { unfold L5DLA.acredits, L5DLA.cnt. rewrite DYD, DYN, ECR2. unfold adebit. cbn [fst snd]. destruct CRD as (C1 & C2). change (8 * 8) with 64. split. clear - C1; lia. clear - C2; lia. }
  intros fx3 R3 R3' M3 M3' model3 c gd gn LBn cr3 LK3 A3 KS3 AG3 POST3 BI3 IA3 ILK3.
  pose proof POST3 as (RP3 & EC & _ & _ & E10 & PX3 & _ & _ & ECR3 & _ & _ & _ & GD3 & _). cbv zeta in EC, E10, GD3, ECR3.
  rewrite LND in EC, E10, GD3. rewrite mword_c in EC. subst c.
  assert (SEC0 : L5DLA.second 1 (L5DLA.shl_result [L5DSA.MWORD] 0) = false) by reflexivity.
  destruct (norm_tobs [] BX2 M2' M3 M3' model2' LK2' cr2' A2 R3 R3' bd bn [L5DSA.MWORD] wX 0 gd gn LBn cr3 LK3 BI2 AG3 TD2 TN2 POST3)
    as (fbd' & fbn' & std & stn & TD3 & TN3 & GRD & GRN & CPD & CPN & OFF3).
  rewrite LND, SEC0 in TD3, TN3, CPD, CPN. change (L5DLA.norm_words [L5DSA.MWORD] 0 false) with [L5DSA.MWORD] in *. change (L5DLA.norm_words wX 0 false) with wX in *.
  rewrite rlen_mword in TD3. cbn [firstn] in TD3.
  destruct gn as [|qg capg]. 2:{ destruct GRN as (X0 & _). rewrite DYN in X0. discriminate X0. }
  destruct gd as [|qg capg]. 2:{ exfalso. rewrite SEC0 in GD3. destruct GD3 as [X0|X0]. cbn in X0. clear - X0; lia. discriminate X0. }
  cbn [L5DLA.blocks_of app L5DLA.adebl] in *. unfold gro_st, L5ADVEA.same_store in GRD, GRN. rewrite STD in GRD. rewrite STN in GRN.
  destruct std as [d0 d1|? ?]. 2: destruct GRD. destruct stn as [? ?|capn qn0]. destruct GRN. destruct GRN as (-> & ->).
  assert (D0E : d0 = L5DSA.MWORD). { destruct TD3 as (_ & (_ & _ & OL3) & _). cbn [L5.bo_st L5.bo_len firstn] in OL3. injection OL3 as X0. symmetry. exact X0. }
  subst d0.
  (* [comment removed for export] *)
  set (BXc := (q0, 8 * 8) :: BX0) in *.
  assert (R19 : getr R3' (reg 19) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R3 R3' 19 RP3) by inl; rewrite (KS3 19%nat) by inl; exact p19).
  assert (R25 : getr R3' (reg 25) = Z_to_bv 64 (F + 96)) by (rewrite (cs_of_preserved R3 R3' 25 RP3) by inl; rewrite (KS3 25%nat) by inl; exact p25).
  assert (R10 : getr R3' (reg 10) = Z_to_bv 64 0). { rewrite <- r10. rewrite E10. rewrite SEC0. reflexivity. }
  assert (RI3 : rinvD R E R3'). { apply (rinvD_pres R E R3 R3'). apply (rinvD_ks R E R2 R3 KS_v5G3 RI2 KS3). vm_compute; reflexivity. exact RP3. }
  pose proof (proj1 TN3) as OBN3. pose proof OBN3 as (_ & _ & NL8 & _). cbn [L5.bo_len] in NL8. replace (F + 96 + 8) with (F + 104) in NL8 by (clear; lia).
  pose proof (rlen_le wX) as RLE. pose proof (proj1 (proj1 (proj2 TX))) as LWX. rewrite LWX in RLE.
  assert (OFF23 : offx (BXc ++ LB) L5DLA.NORM_SCR (fun a => E - 220 <= a < E - 216) M2' M3).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG3. exact Ha. exact NX. }
  pose proof (offx_trans _ _ _ _ _ _ _ OFF23 OFF3) as OFFN. cbv beta in OFFN.
  assert (INQ2' : In (q2, 8 * 8) (BXc ++ LB)) by (exact (proj2 (proj2 (proj2 TN3)) 8 q2 eq_refl)).
  assert (INWN : forall a, L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn) a -> F + 32 <= a < F + 128 \/ E - 220 <= a < E - 216 \/ q2 <= a < q2 + 8 * 8).
  { intros a (rr & Hr & IR). unfold L5DLA.norm_W, L5DLA.dyn_area in Hr. rewrite STD, STN in Hr. cbn [app In] in Hr. unfold L5.in_rng in IR.
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in IR. left; clear - IR; lia. left; clear - IR; lia. right; left; clear - IR; lia. right; right; exact IR. }
  assert (S88_3 : L5.u64_at RSEGS M3' (E - 296) X).
  { destruct (SPL2 (E - 296) X ltac:(subst cells; do 2 right; left; reflexivity)) as (Hc & H1 & H2).
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BXc ++ LB) L5DLA.NORM_SCR _ M2' M3' _ _ Hc H1 H2 OFFN).
    intros i Hi [Y|Y]. clear - Y Hi; lia. destruct (INWN i Y) as [Z0|[Z0|Z0]]. clear - Z0 Hi SFB; lia. clear - Z0 Hi; lia.
    destruct (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 [] BXc M2' model2' LK2' cr2' A2 q2 (8 * 8) i BI2 INQ2' Z0) as (_ & _ & Y3). apply Y3. clear - Hi; lia. }
  apply (G4s fx3 R3' M3' model3 [] BXc LK3 cr3 A3 0 X (L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1)) (Z.of_nat (rlen wX)) BI3 RI3 R10 R19 R25 ltac:(clear; lia) XRG S88_3 (proj1 (proj2 (proj2 TD3))) (proj1 TD3) NL8 ltac:(clear - RLE LENX; lia)).
  intros fx4 R4 M4 model4 BI4 RI4 KS4 p1 p10 p11 p20 p24 AG4 S264 S272 S112.
  cbn [L5.bo_len] in p11. unfold L5.bo_data in S264. cbn [L5.bo_st L5.bo_len] in S264, S272, S112. replace (F + 32 + 16) with (F + 48) in S264 by (clear; lia).
  (* [comment removed for export] *)
  set (X4 := fun a => E - 120 <= a < E - 104 \/ E - 272 <= a < E - 264).
  assert (OFF4 : offx (BXc ++ LB) L5DLA.NORM_SCR X4 M3' M4).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG4. exact Ha. intros Y. apply NX. left; exact Y. intros Y. apply NX. right; exact Y. }
  pose proof (offx_trans _ _ _ _ _ _ _ (offx_trans _ _ _ _ _ _ _ OFF23 OFF3) OFF4) as OFFA. cbv beta in OFFA.
  pose proof BI3 as (B3 & _). pose proof BI2 as (B2 & _).
  assert (NOFR4 : forall o b ws a, aobj FF' o 32 -> tob (BXc ++ LB) M3' o b ws -> L5ADVEA.oreg o b a -> ~ X4 a).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BXc M3' model3 LK3 cr3 A3 o b ws a BI3 AO TO OR). subst X4; cbn beta in X0. clear - X0 HSCR; lia. }
  assert (TD4 : tob (BXc ++ LB) M4 (F + 32) (L5.BO fbd' 1 (L5.BInl L5DSA.MWORD d1)) [L5DSA.MWORD]).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXc ++ LB) (BXc ++ LB) (BXc ++ LB) LK3 cr3 A3 model3 L5DLA.NORM_SCR _ M3' M4 (F + 32) _ _ B3 AOD' TD3 OFF4).
    intros cap q Eq. discriminate Eq. intros a OR. exact (NOFR4 _ _ _ a AOD' TD3 OR). }
  assert (TN4 : tob (BXc ++ LB) M4 (F + 96) (L5.BO fbn' (rlen wX) (L5.BDyn 8 q2)) (firstn (rlen wX) wX)).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXc ++ LB) (BXc ++ LB) (BXc ++ LB) LK3 cr3 A3 model3 L5DLA.NORM_SCR _ M3' M4 (F + 96) _ _ B3 AON' TN3 OFF4).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TN3)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR4 _ _ _ a AON' TN3 OR). }
  assert (INQ2 : In (q2, 8 * 8) (BXc ++ LB)) by (exact (proj2 (proj2 (proj2 TN4)) 8 q2 eq_refl)).
  assert (XST : forall a, SPA <= a < E -> ~ (E - 220 <= a < E - 216) -> ~ X4 a -> ~ (((E - 220 <= a < E - 216) \/ L5ADVEA.inW (L5DLA.norm_W (F + 32) (F + 96) (E - 220) bd bn) a) \/ X4 a)).
  { intros a Ha N1 N4 [[Y|Y]|Y]. exact (N1 Y). 2: exact (N4 Y). destruct (INWN a Y) as [Z0|[Z0|Z0]]. clear - Z0 Ha SFB; lia. exact (N1 Z0).
    destruct (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 [] BXc M2' model2' LK2' cr2' A2 q2 (8 * 8) a BI2 INQ2 Z0) as (_ & _ & Y3). exact (Y3 Ha). }
  assert (SPL4 : spl E M4 cells).
  { intros a v Hin. destruct (SPL2 a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
    apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BXc ++ LB) L5DLA.NORM_SCR _ M2' M4 a v Hc H1 H2 OFFA).
    intros i Hi. apply XST. clear - Hi H1 H2; lia.
    all: subst cells X4; cbn beta; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; clear - Hi; lia|]); destruct Hin. }
  assert (HDR4 : L5.u64_at RSEGS M4 F 1102416563).
  { eapply L5C.u64_at_agree. 4: exact HDR2. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply OFFA. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA L5DLA.NORM_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia.
    intros [[Y|Y]|Y]. clear - Y Hi SFB; lia. 2: subst X4; cbn beta in Y; clear - Y Hi SFB; lia.
    destruct (INWN i Y) as [Z0|[Z0|Z0]]. clear - Z0 Hi; lia. clear - Z0 Hi SFB; lia.
    destruct (L5ADVEA.blk_frame L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BXc M2' model2' LK2' cr2' A2 q2 (8 * 8) F BI2 INQ2) as (Y1 & _). clear - Y1 Z0 Hi; lia. }
  assert (STK4 : forall o b blk, L5ADVD.obj_at M2' o b blk -> E - 216 <= o -> o + 32 <= E - 152 -> L5ADVD.obj_at M4 o b blk).
  { intros o b blk OA H1 H2. apply (L5ADVD.obj_at_agree M2' M4 o b blk OA ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia)). intros i Hi. apply OFFA. clear - Hi H1 H2 ER; lia.
    apply stack_client. destruct G as [Hk SPT SLO SHI SPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. clear - Hi H1 H2 SLO SHI SPT HSCR; lia. clear - Hi H1; lia.
    apply XST. clear - Hi H1 H2; lia. clear - Hi H1; lia. subst X4; cbn beta. clear - Hi H1 H2; lia. }
  assert (S360_4 : L5.u64_at RSEGS M4 (E - 360) F).
  { apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BXc ++ LB) L5DLA.NORM_SCR _ M2' M4 _ _ S360_2 ltac:(clear; lia) ltac:(clear; lia) OFFA).
    intros i Hi. apply XST. clear - Hi; lia. clear - Hi; lia. subst X4; cbn beta. clear - Hi; lia. }
  assert (PX4 : L5.u32_at RSEGS M4 (E - 220) 0).
  { eapply L5ARED.u32_at_agree1. 4: exact PX3. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply AG4. clear - Hi ER; lia. clear - Hi; lia. clear - Hi; lia. }
  assert (DSH4 : dsh M4 F 0 248 248 248 248).
  { eapply L5ADVHA.dsh_keep; [exact G | exact ER | exact DSH2 | exact OFFA | ]. intros j Hj [[Y|Y]|Y]. clear - Hj Y SHQ ER; lia. 2: subst X4; cbn beta in Y; clear - Hj Y SHQ ER; lia.
    destruct (INWN j Y) as [Z0|[Z0|Z0]]. clear - Z0 Hj SHQ FBIG; lia. clear - Z0 Hj SHQ ER; lia.
    destruct (L5ADVEA.blk_avoid L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G HSCR0 [] BXc M2' model2' LK2' cr2' A2 q2 (8 * 8) j BI2 INQ2 Z0) as (_ & Y2 & _). apply Y2. change (ff_bytes 3 / 8) with 64. unfold SB. exact Hj. }
  assert (SGD4 : Z.testbit fbd' 1 = false).
  { destruct POST3 as (_ & _ & _ & _ & _ & _ & (std0 & stn0 & OAD & _) & _). exact (after_sgn_gn M3' (F + 32) bd _ Same std0 fbd' _ _ OAD (proj1 TD3) SGN_D). }
  assert (SGN4 : Z.testbit fbn' 1 = false).
  { destruct POST3 as (_ & _ & _ & _ & _ & _ & (std0 & stn0 & _ & OAN) & _). exact (after_sgn_gn M3' (F + 96) bn _ Same stn0 fbn' _ _ OAN (proj1 TN3) SGN_N). }
  apply (KF fx4 R4 M4 model4 q0 bn0 bd0 fbd' fbn' d1 cr3 LK3 A3 BI4 RI4).
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
  - apply (STK4 _ _ _ ON0). clear; lia. clear; lia.
  - apply (STK4 _ _ _ OD0). clear; lia. clear; lia.
  - rewrite LNN0. exact LNB.
  - exact STN0.
  - rewrite LND0. exact LND.
  - rewrite STD0. exact STD.
  - exact SGD4.
  - exact SGN4.
  - exact DSH4.
  - exact SPL4.
  - exact S360_4.
  - exact S264.
  - exact S272.
  - exact S112.
  - exact HDR4.
  - exact PX4.
  - rewrite ECR3, ECR2. reflexivity.
  - intros x Hx. apply IA3. apply IA2. exact Hx.
  - intros x Hx. apply ILK2. apply ILK3. exact Hx.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGN.

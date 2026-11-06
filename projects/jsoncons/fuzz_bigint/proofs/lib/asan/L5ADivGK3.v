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
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivHL L5ADivHM L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB L5ADivGC L5ADivGD L5ADivGU L5ARed L5ADivHH L5ADivHS L5ADivGE L5ADivN L5ADivO1 L5ANorm L5ADivGN L5ADivGK L5ARzHuge L5ADivGK2.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGK3.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resize_stage2 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac o pcn (n : nat) b ws :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (Z.of_nat n) -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  L5.big_at RSEGS Mc o b -> L5C.obj_limbs RSEGS Mc b ws -> aobj FF o 32 -> shadow_zero Mc o 4 ->
  Z.of_nat n <= 2 ^ 23 ->
  (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
  ((3 <= n)%nat -> L5.bo_dyn b = false -> acredit_ok L crc (8 * round_up (Z.of_nat n))) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(o, 32)] a) ->
  ((L5.bo_dyn b = true \/ (n <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W1 a ->
      ~ L5.in_rng (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b))) a) ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      resize_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' o SPA n b ws g LBn cr' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc RESIZE Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn OB OL AOB SZ LEN CAPOK CROK INB WSUB WTAIL KF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  edestruct L5ADVEA.callee_pre with (SCRc := RESIZE_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI | vm_compute; discriminate | clear - HSCR; change RESIZE_SCR with 4496; lia | ].
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & _ & _ & OFR & OF & OSH & _).
  pose proof RI as (Z2 & _ & _ & _ & Z4).
  assert (OCR : forall a, docell E a -> SPA <= a < E). { destruct G as [_ _ _ _ _ OCR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact OCR0. }
  apply (Hrsz fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac o SPA pcn n b ws B1 B2 HK).
  - rewrite r10. exact X10.
  - rewrite r11. exact X11.
  - exact LEN.
  - exact CAPOK.
  - exact CROK.
  - rewrite r1. exact X1.
  - exact RAn.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - apply (ffrk_le 1 FF' LKc 4 4 ROOMc). clear; lia.
  - exact RSc.
  - exact OB.
  - exact OL.
  - apply aobj_cons. exact AOB.
  - exact SZ.
  - exact INB.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    assert (BI3 : binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M3 model3 LK3 cr3 A3).
    { pose proof POST as (_ & PG).
      destruct g as [|qn capn].
      - destruct PG as (DY & ELB & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX BX Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 RESIZE_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change RESIZE_SCR with 4496; lia.
        + intros rr a [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          * split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
            change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
          * destruct b as [fb len sto]. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_st L5.bo_len] in IR.
            -- assert (LE2 : (n <= 2)%nat).
               { destruct DY as [DY|DY]. 2: exact DY. exfalso. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY, BT. rewrite BT in DY. discriminate DY. }
               split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR LE2. lia. }
               change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH LE2. lia.
            -- assert (CAPB : Z.of_nat n <= cap).
               { apply CAPOK. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn. cbn [L5.bo_fb]. exact BT. }
               edestruct L5ADVEA.blk_avoid with (a := a) as (Y1 & Y2 & _); try first [exact LY | exact HIok | exact G | exact HSCR]; [exact BI | exact (INB cap q eq_refl) | clear - IR CAPB; lia | ].
               split. exact Y1. exact Y2.
        + intros a Hc X rr [Hr|[Hr|[]]]; subst rr. apply (proj2 (WSUB a X) (o, 32)). left; reflexivity. exact (WTAIL DY a Hc X).
        + intros a X. exact (proj1 (WSUB a X)).
      - destruct PG as (_ & _ & _ & ELB & _ & _ & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX ((qn, 8 * capn) :: BX) Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 RESIZE_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change RESIZE_SCR with 4496; lia.
        + intros rr a [Hr|[]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
          change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
        + intros a _ X rr [Hr|[]]. subst rr. apply (proj2 (WSUB a X) (o, 32)). left; reflexivity.
        + intros a X. exact (proj1 (WSUB a X)). }
    apply (KF fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
Lemma arg_resize2 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac o pcn (n : nat) b ws :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (Z.of_nat n) -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> Z.of_nat n <= 2 ^ 23 ->
  (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
  ((3 <= n)%nat -> L5.bo_dyn b = false -> acredit_ok L crc (8 * round_up (Z.of_nat n))) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(o, 32)] a) ->
  ((L5.bo_dyn b = true \/ (n <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W1 a ->
      ~ L5.in_rng (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b))) a) ->
  (forall (fx' : FPState) R' M' model' (g : growth) b1 cr' LK' A',
      regs_preserved Rc R' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      tob ((match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) ++ LB) M' o b1 (resize_limbs ws n) -> L5.bo_len b1 = n ->
      match g with
      | Same => L5.bo_fb b1 = L5.bo_fb b /\ L5ADVEA.same_store b (L5.bo_st b1) /\ cr' = crc
      | Grown q cap => L5.bo_fb b1 = Z.lor (L5.bo_fb b) 1 /\ L5.bo_st b1 = L5.BDyn cap q /\ cap = round_up (Z.of_nat n) /\ cr' = adebit L crc (8 * cap) /\ L5.bo_dyn b = false /\ (3 <= n)%nat
      end ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) RESIZE_SCR (L5ADVEA.oreg o b) Mc M' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc RESIZE Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn AOB TO LEN CAPOK CROK WSUB WTAIL KF.
  pose proof TO as (OB & OL & SZ & INB).
  apply (resize_stage2 fx Rc Mc modelc W W1 BX LKc crc Ac o pcn n b ws BI RI X10 X11 X1 RAn OB OL AOB SZ LEN CAPOK CROK INB WSUB WTAIL).
  intros fx' R' M' model' g LBn cr' LK' A' POST BI' IA ILK.
  destruct POST as (RP & PG).
  assert (WIN : forall Wc, (Wc = [(o, 32)] \/ ((L5.bo_dyn b = true \/ (n <= 2)%nat) /\ Wc = [(o, 32); (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b)))])) ->
                 forall a, L5ADVEA.inW Wc a -> o <= a < o + 32 \/ (exists cap q, L5.bo_st b = L5.BDyn cap q /\ q <= a < q + 8 * cap)).
  { intros Wc HW a (rr & Hr & IR). unfold L5.in_rng in IR. destruct HW as [->|(DY & ->)].
    - destruct Hr as [<-|[]]. cbn [fst snd] in IR. left. exact IR.
    - destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in IR. left. exact IR.
      pose proof (len_le_cap Mc o b OB) as LC. destruct b as [fb len sto]. unfold L5.bo_data, L5.bo_dyn, L5.bo_cap in *. cbn [L5.bo_st L5.bo_len L5.bo_fb] in *.
      destruct sto as [v0 v1|cap q].
      + left. destruct DY as [DY|DY]. { exfalso. destruct OB as (_ & _ & _ & (BT & _)). cbn [L5.bo_fb] in BT. rewrite BT in DY. discriminate DY. }
        clear - IR LC DY. lia.
      + right. exists cap, q. split. reflexivity. assert (NC : Z.of_nat n <= cap). { apply CAPOK. destruct OB as (_ & _ & _ & (BT & _)). exact BT. } clear - IR LC NC. lia. }
  destruct g as [|q cap].
  - destruct PG as (DY & _ & ECR & (st' & OB' & OL' & SS) & AH).
    destruct (ARG_AFTER W BX Mc modelc LKc crc Ac M' o b ws (L5.bo_fb b) 0 n (resize_limbs ws n) Same RESIZE_SCR _ BI AOB TO ltac:(exists st'; split; [exact OB' | split; [exact OL' | exact SS]]) AH
                (WIN _ (or_intror (conj DY eq_refl)))) as (b1 & T1 & L1 & F1 & S1).
    apply (KF fx' R' M' model' Same b1 cr' LK' A' RP BI' T1 L1 (conj F1 (conj S1 ECR))). 2: exact IA. 2: exact ILK.
    intros a Ha Hc NX. apply (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) RESIZE_SCR _ Mc M' AH a Ha Hc). intros Y. apply NX.
    destruct (WIN _ (or_intror (conj DY eq_refl)) a Y) as [Z0|Z0]. left; exact Z0. right; right; exact Z0.
  - destruct PG as (DY & N3 & ECAP & _ & ECR & _ & OB' & OL' & AH).
    destruct (ARG_AFTER W BX Mc modelc LKc crc Ac M' o b ws 0 (Z.lor (L5.bo_fb b) 1) n (resize_limbs ws n) (Grown q cap) RESIZE_SCR _ BI AOB TO (conj OB' OL') AH (WIN _ (or_introl eq_refl)))
      as (b1 & T1 & L1 & F1 & S1).
    apply (KF fx' R' M' model' (Grown q cap) b1 cr' LK' A' RP BI' T1 L1 (conj F1 (conj S1 (conj ECAP (conj ECR (conj DY N3)))))). 2: exact IA. 2: exact ILK.
    intros a Ha Hc NX. apply (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) RESIZE_SCR _ Mc M' AH a Ha Hc). intros Y. apply NX.
    destruct (WIN _ (or_introl eq_refl) a Y) as [Z0|Z0]. left; exact Z0. right; right; exact Z0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma assign_stage2 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac o k pcn b b' ws' :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (F + k) -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  32 <= k -> k + 32 <= 504 -> k mod 8 = 0 ->
  L5.big_at RSEGS Mc o b -> aobj FF o 32 -> shadow_zero Mc o 4 ->
  L5.big_at RSEGS Mc (F + k) b' -> L5C.obj_limbs RSEGS Mc b' ws' -> shadow_zero Mc (F + k) 4 ->
  Z.of_nat (L5.bo_len b') <= 2 ^ 23 ->
  (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b') <= L5.bo_cap b) ->
  ((3 <= L5.bo_len b')%nat -> L5.bo_dyn b = false -> acredit_ok L crc (8 * round_up (Z.of_nat (L5.bo_len b')))) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st b' = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(o, 32)] a) ->
  ((L5.bo_dyn b = true \/ (L5.bo_len b' <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W1 a -> ~ L5.in_rng (L5.bo_data o b, 8 * Z.of_nat (L5.bo_len b')) a) ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      assign_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' o (F + k) SPA b b' ws' g LBn cr' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc ASSIGN Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn K1 K2 K8 OB AOB SZ OB' OL' SZ' LEN CAPOK CROK INB INB' NOAL WSUB WTAIL KF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  edestruct L5ADVEA.callee_pre with (SCRc := ASSIGN_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI | vm_compute; discriminate | clear - HSCR; change ASSIGN_SCR with 4560; lia | ].
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & _ & _ & OFR & OF & OSH & _).
  pose proof RI as (Z2 & _ & _ & _ & Z4).
  assert (OCR : forall a, docell E a -> SPA <= a < E). { destruct G as [_ _ _ _ _ OCR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact OCR0. }
  apply (Hasg fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac o (F + k) SPA pcn b b' ws' B1 B2 HK).
  - rewrite r10. exact X10.
  - rewrite r11. exact X11.
  - exact LEN.
  - exact CAPOK.
  - exact CROK.
  - rewrite r1. exact X1.
  - exact RAn.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - apply (ffrk_le 1 FF' LKc 4 4 ROOMc). clear; lia.
  - exact RSc.
  - exact OB.
  - apply aobj_cons. exact AOB.
  - exact SZ.
  - exact OB'.
  - exact OL'.
  - eapply L5ADVEA.loc_aobj; [exact G | exact K1 | exact K2 | exact K8].
  - exact SZ'.
  - exact INB.
  - exact INB'.
  - clear - OF K1 K2. lia.
  - exact NOAL.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    assert (BI3 : binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M3 model3 LK3 cr3 A3).
    { pose proof POST as (_ & _ & PG).
      destruct g as [|qn capn].
      - destruct PG as (DY & ELB & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX BX Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 ASSIGN_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change ASSIGN_SCR with 4560; lia.
        + intros rr a [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          * split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
            change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
          * destruct b as [fb len sto]. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_st] in IR.
            -- assert (LE2 : (L5.bo_len b' <= 2)%nat).
               { destruct DY as [DY|DY]. 2: exact DY. exfalso. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY, BT. rewrite BT in DY. discriminate DY. }
               split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR LE2. lia. }
               change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH LE2. lia.
            -- assert (CAPB : Z.of_nat (L5.bo_len b') <= cap).
               { apply CAPOK. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn. cbn [L5.bo_fb]. exact BT. }
               edestruct L5ADVEA.blk_avoid with (a := a) as (Y1 & Y2 & _); try first [exact LY | exact HIok | exact G | exact HSCR]; [exact BI | exact (INB cap q eq_refl) | clear - IR CAPB; lia | ].
               split. exact Y1. exact Y2.
        + intros a Hc X rr [Hr|[Hr|[]]]; subst rr. apply (proj2 (WSUB a X) (o, 32)). left; reflexivity. exact (WTAIL DY a Hc X).
        + intros a X. exact (proj1 (WSUB a X)).
      - destruct PG as (_ & _ & _ & ELB & _ & _ & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX ((qn, 8 * capn) :: BX) Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 ASSIGN_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change ASSIGN_SCR with 4560; lia.
        + intros rr a [Hr|[]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
          change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
        + intros a _ X rr [Hr|[]]. subst rr. apply (proj2 (WSUB a X) (o, 32)). left; reflexivity.
        + intros a X. exact (proj1 (WSUB a X)). }
    apply (KF fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3).
Qed.

Lemma g6_2 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac (br bn : L5.bigobj) wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 20) = Z_to_bv 64 (F + 96) -> getr Rc (reg 23) = Z_to_bv 64 ro ->
  L5.big_at RSEGS Mc ro br -> aobj FF ro 32 -> shadow_zero Mc ro 4 ->
  L5.big_at RSEGS Mc (F + 96) bn -> L5C.obj_limbs RSEGS Mc bn wn -> shadow_zero Mc (F + 96) 4 ->
  Z.of_nat (L5.bo_len bn) <= 2 ^ 23 ->
  (L5.bo_dyn br = true -> Z.of_nat (L5.bo_len bn) <= L5.bo_cap br) ->
  ((3 <= L5.bo_len bn)%nat -> L5.bo_dyn br = false -> acredit_ok L crc (8 * round_up (Z.of_nat (L5.bo_len bn)))) ->
  (forall cap q, L5.bo_st br = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bn = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32)] a) ->
  ((L5.bo_dyn br = true \/ (L5.bo_len bn <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W1 a -> ~ L5.in_rng (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn)) a) ->
  (forall (fx' : FPState) R1 R' M' model' (g : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G6 -> getr R1 (reg x) = getr Rc (reg x)) ->
      assign_post L ar (BX ++ LB) FF' LK' crc Mc M' R1 R' ro (F + 96) SPA br bn wn g LBn cr' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x927cc M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x927c0 Mc modelc) K.
Proof.
  intros BI RI X20 X23 OBR AOR SZR OBN OLN SZN LEN CAPOK CROK INR INN NOAL WSUB WTAIL KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & _).
  open_ctx BI. pose proof BI as (B1 & B2 & _). pose proof RI as (X2 & X8 & X9 & X3 & X4).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487584 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  assert (ROR : 0 <= ro <= 18446744073709551615) by (clear - ORP ORG; lia).
  pose proof (v5G6_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & pR1 & pR10 & pR11)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x927c0 R1 ASSIGN K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  eapply (assign_stage2) with (W := W) (W1 := W1) (BX := BX) (o := ro) (k := 96) (pcn := 0x927cc) (b := br) (b' := bn) (ws' := wn);
    try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact RA | exact UR1 | exact G2 | exact G4 | exact HSCR | exact FFR1 | exact FFRS | exact Hdel | exact Hasg | exact BI1].
  - apply (rinvD_ks R E Rc R1 KS_v5G6 RI pKS). vm_compute; reflexivity.
  - exact pR10.
  - exact pR11.
  - exact pR1.
  - split. clear; lia. reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - exact OBR.
  - exact AOR.
  - exact SZR.
  - exact OBN.
  - exact OLN.
  - exact SZN.
  - exact LEN.
  - exact CAPOK.
  - exact CROK.
  - exact INR.
  - exact INN.
  - exact NOAL.
  - exact WSUB.
  - exact WTAIL.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3. apply (KF fx3 R1 R3 M3 model3 g LBn cr3 LK3 A3 pKS POST BI3 IA3 ILK3).
Qed.

Lemma g6_arg2 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac (br bn : L5.bigobj) wr wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 20) = Z_to_bv 64 (F + 96) -> getr Rc (reg 23) = Z_to_bv 64 ro ->
  aobj FF ro 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc (F + 96) bn wn ->
  Z.of_nat (L5.bo_len bn) <= 2 ^ 23 ->
  (L5.bo_dyn br = true -> Z.of_nat (L5.bo_len bn) <= L5.bo_cap br) ->
  ((3 <= L5.bo_len bn)%nat -> L5.bo_dyn br = false -> acredit_ok L crc (8 * round_up (Z.of_nat (L5.bo_len bn)))) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bn = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32)] a) ->
  ((L5.bo_dyn br = true \/ (L5.bo_len bn <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W1 a -> ~ L5.in_rng (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn)) a) ->
  (forall (fx' : FPState) R1 R' M' model' (g : growth) b1 cr' LK' A',
      (forall x, In x KS_v5G6 -> getr R1 (reg x) = getr Rc (reg x)) -> regs_preserved R1 R' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      tob ((match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) ++ LB) M' ro b1 wn -> L5.bo_len b1 = L5.bo_len bn ->
      match g with
      | Same => L5.bo_fb b1 = assign_fb (L5.bo_fb br) (L5.bo_fb bn) (L5.bo_len bn) false /\ L5ADVEA.same_store br (L5.bo_st b1) /\ cr' = crc
      | Grown q cap => L5.bo_fb b1 = assign_fb (L5.bo_fb br) (L5.bo_fb bn) (L5.bo_len bn) true /\ L5.bo_st b1 = L5.BDyn cap q /\ cap = round_up (Z.of_nat (L5.bo_len bn))
                       /\ cr' = adebit L crc (8 * cap) /\ L5.bo_dyn br = false
      end ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) ASSIGN_SCR (L5ADVEA.oreg ro br) Mc M' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x927cc M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x927c0 Mc modelc) K.
Proof.
  intros BI RI X20 X23 AOR TR TN LEN CAPOK CROK NOAL WSUB WTAIL KF.
  pose proof TR as (OBR & OLR & SZR & INR). pose proof TN as (OBN & OLN & SZN & INN).
  apply (g6_2 fx Rc Mc modelc W W1 BX LKc crc Ac br bn wn BI RI X20 X23 OBR AOR SZR OBN OLN SZN LEN CAPOK CROK INR INN NOAL WSUB WTAIL).
  intros fx' R1 R' M' model' g LBn cr' LK' A' KS1 POST BI' IA ILK.
  destruct POST as (RP & _ & PG). cbv zeta in PG. set (n := L5.bo_len bn) in *.
  assert (WIN : forall Wc, (Wc = [(ro, 32)] \/ ((L5.bo_dyn br = true \/ (n <= 2)%nat) /\ Wc = [(ro, 32); (L5.bo_data ro br, 8 * Z.of_nat n)])) ->
                 forall a, L5ADVEA.inW Wc a -> ro <= a < ro + 32 \/ (exists cap q, L5.bo_st br = L5.BDyn cap q /\ q <= a < q + 8 * cap)).
  { intros Wc HW a (rr & Hr & IR). unfold L5.in_rng in IR. destruct HW as [->|(DY & ->)].
    - destruct Hr as [<-|[]]. cbn [fst snd] in IR. left. exact IR.
    - destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in IR. left. exact IR.
      destruct br as [fb len sto]. unfold L5.bo_data, L5.bo_dyn, L5.bo_cap in *. cbn [L5.bo_st L5.bo_len L5.bo_fb] in *.
      destruct sto as [v0 v1|cap q].
      + left. destruct DY as [DY|DY]. { exfalso. destruct OBR as (_ & _ & _ & (BT & _)). cbn [L5.bo_fb] in BT. rewrite BT in DY. discriminate DY. }
        clear - IR DY. lia.
      + right. exists cap, q. split. reflexivity. assert (NC : Z.of_nat n <= cap). { apply CAPOK. destruct OBR as (_ & _ & _ & (BT & _)). exact BT. } clear - IR NC. lia. }
  destruct g as [|q cap].
  - destruct PG as (DY & _ & ECR & (st' & OB' & OL' & SS) & AH).
    destruct (ARG_AFTER W BX Mc modelc LKc crc Ac M' ro br wr _ 0 n wn Same ASSIGN_SCR _ BI AOR TR ltac:(exists st'; split; [exact OB' | split; [exact OL' | exact SS]]) AH
                (WIN _ (or_intror (conj DY eq_refl)))) as (b1 & T1 & L1 & F1 & S1).
    apply (KF fx' R1 R' M' model' Same b1 cr' LK' A' KS1 RP BI' T1 L1 (conj F1 (conj S1 ECR))). 2: exact IA. 2: exact ILK.
    intros a Ha Hc NX. apply (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) ASSIGN_SCR _ Mc M' AH a Ha Hc). intros Y. apply NX.
    destruct (WIN _ (or_intror (conj DY eq_refl)) a Y) as [Z0|Z0]. left; exact Z0. right; right; exact Z0.
  - destruct PG as (DY & N3 & ECAP & _ & ECR & _ & OB' & OL' & AH).
    destruct (ARG_AFTER W BX Mc modelc LKc crc Ac M' ro br wr 0 _ n wn (Grown q cap) ASSIGN_SCR _ BI AOR TR (conj OB' OL') AH (WIN _ (or_introl eq_refl)))
      as (b1 & T1 & L1 & F1 & S1).
    apply (KF fx' R1 R' M' model' (Grown q cap) b1 cr' LK' A' KS1 RP BI' T1 L1 (conj F1 (conj S1 (conj ECAP (conj ECR DY))))). 2: exact IA. 2: exact ILK.
    intros a Ha Hc NX. apply (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) ASSIGN_SCR _ Mc M' AH a Ha Hc). intros Y. apply NX.
    destruct (WIN _ (or_introl eq_refl) a Y) as [Z0|Z0]. left; exact Z0. right; right; exact Z0.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGK3.

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
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivHL L5ADivHM L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB L5ADivGC L5ADivGD L5ADivGU L5ARed L5ADivHH L5ADivHS L5ADivGE L5ADivN L5ADivO1 L5ANorm L5ADivGN L5ARzHuge.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGK.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN.
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
Lemma arg_resize (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac o pcn (n : nat) b ws :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (Z.of_nat n) -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> Z.of_nat n <= 2 ^ 23 ->
  (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
  ((3 <= n)%nat -> L5.bo_dyn b = false -> acredit_ok L crc (8 * round_up (Z.of_nat n))) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(o, 32); (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b)))] a) ->
  (forall (fx' : FPState) R' M' model' (g : growth) b1 cr' LK' A',
      regs_preserved Rc R' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      tob ((match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) ++ LB) M' o b1 (resize_limbs ws n) -> L5.bo_len b1 = n ->
      match g with
      | Same => L5.bo_fb b1 = L5.bo_fb b /\ L5ADVEA.same_store b (L5.bo_st b1) /\ cr' = crc
      | Grown q cap => L5.bo_fb b1 = Z.lor (L5.bo_fb b) 1 /\ L5.bo_st b1 = L5.BDyn cap q /\ cap = round_up (Z.of_nat n) /\ cr' = adebit L crc (8 * cap) /\ L5.bo_dyn b = false
      end ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) RESIZE_SCR (L5ADVEA.oreg o b) Mc M' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc RESIZE Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn AOB TO LEN CAPOK CROK WSUB KF.
  pose proof TO as (OB & OL & SZ & INB).
  apply (RSZ fx Rc Mc modelc W W1 BX LKc crc Ac o pcn n b ws BI RI X10 X11 X1 RAn OB OL AOB SZ LEN CAPOK CROK INB WSUB).
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
    apply (KF fx' R' M' model' (Grown q cap) b1 cr' LK' A' RP BI' T1 L1 (conj F1 (conj S1 (conj ECAP (conj ECR DY))))). 2: exact IA. 2: exact ILK.
    intros a Ha Hc NX. apply (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) RESIZE_SCR _ Mc M' AH a Ha Hc). intros Y. apply NX.
    destruct (WIN _ (or_introl eq_refl) a Y) as [Z0|Z0]. left; exact Z0. right; right; exact Z0.
Qed.

(* [comment removed for export] *)
Lemma g6_arg (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac (br bn : L5.bigobj) wr wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 20) = Z_to_bv 64 (F + 96) -> getr Rc (reg 23) = Z_to_bv 64 ro ->
  aobj FF ro 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc (F + 96) bn wn ->
  Z.of_nat (L5.bo_len bn) <= 2 ^ 23 ->
  (L5.bo_dyn br = true -> Z.of_nat (L5.bo_len bn) <= L5.bo_cap br) ->
  ((3 <= L5.bo_len bn)%nat -> L5.bo_dyn br = false -> acredit_ok L crc (8 * round_up (Z.of_nat (L5.bo_len bn)))) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bn = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32); (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn))] a) ->
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
  intros BI RI X20 X23 AOR TR TN LEN CAPOK CROK NOAL WSUB KF.
  pose proof TR as (OBR & OLR & SZR & INR). pose proof TN as (OBN & OLN & SZN & INN).
  apply (G6 fx Rc Mc modelc W W1 BX LKc crc Ac br bn wn BI RI X20 X23 OBR AOR SZR OBN OLN SZN LEN CAPOK CROK INR INN NOAL WSUB).
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
End L5ADVGK.

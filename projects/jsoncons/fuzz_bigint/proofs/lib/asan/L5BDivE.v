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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPE.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVE.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADIVPE.
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
Hypothesis Hdel : opdel_sized_spec L ar HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4096 <= SCRD.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation Gx := (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G).
Local Notation SH := (F / 8 + 2147450880).

(* [comment removed for export] *)
Lemma apart_of_client (P : Z -> Prop) x lx y ly : 0 < lx -> 0 < ly -> (forall a, x <= a < x + lx -> P a) -> (forall a, y <= a < y + ly -> ~ P a) -> x + lx <= y \/ y + ly <= x.
Proof.
  intros Hx Hy PX PY. destruct (Z_le_gt_dec (x + lx) y) as [A1|A1]. left; exact A1. destruct (Z_le_gt_dec (y + ly) x) as [A2|A2]. right; exact A2.
  exfalso. apply (PY (Z.max x y)). lia. apply PX. lia.
Qed.

Lemma arg_facts W BX Mc modelc LKc crc Ac o : binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> shadow_zero Mc o 4 ->
  let MV := mrestrict (ahid Ac modelc) Mc in
  (4096 <= o <= 140737488355296 /\ 0 <= o < 2 ^ 64 /\ o mod 8 = 0) /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784)
  /\ L5KA.zeros_at MV (o / 8 + 2147450880) 4 /\ L5.writable RSEGS MV o 32
  /\ (E - 384 + 384 <= o \/ o + 32 <= E - 384) /\ (o + 32 <= F \/ F + 512 <= o) /\ (o + 32 <= SH \/ SH + 64 <= o)
  /\ (o / 8 + 2147450880 + 4 <= F \/ F + 512 <= o / 8 + 2147450880) /\ (o / 8 + 2147450880 + 4 <= SH \/ SH + 64 <= o / 8 + 2147450880)
  /\ (o / 8 + 2147450880 + 4 <= E - 384 \/ E - 384 + 384 <= o / 8 + 2147450880)
  /\ (forall v, L5.u8_at RSEGS Mc o v -> L5.u8_at RSEGS MV o v)
  /\ (forall a v, o <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v)
  /\ (forall a, o <= a < o + 32 -> aclientw L ar (BX ++ LB) FF' 0 0 a /\ ~ (0x10000 <= a < 0x634000) /\ a <> fl /\ ~ docell E a).      (* [comment removed for export] *)
Proof.
  intros BI AOB SZ MV. pose proof BI as (B1 & _).
  assert (AOB' : aobj FF' o 32) by (apply aobj_cons; exact AOB).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB' ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  assert (CL0 : forall a, o <= a < o + 32 -> aclient L ar LB FF E SCRD a). { intros a Ha. apply (obj_client L ar LB FF E SCRD o 32 a AOB Ha). }
  assert (CLS : forall a, o / 8 + 2147450880 <= a < o / 8 + 2147450880 + 4 -> aclient L ar LB FF E SCRD a).
  { intros a Ha. pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M2 model2 o 32 E SCRD) as X. clear X.
    destruct AOB as (f & Hf & X1 & X2 & X8). right; right; right; right; right; left. exists f. split. exact Hf. unfold in_shadow_of, S.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HB : 0 < ff_bytes (ff_class f)). { unfold ff_bytes. apply Z.mul_pos_pos. clear; lia. apply Z.pow_pos_nonneg. clear; lia.
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & WF & _). pose proof (WF f ltac:(right; exact Hf)) as (_ & _ & _ & Y4 & _). clear - Y4. destruct Y4 as [Y|[Y|[Y|[]]]]; rewrite <- Y; lia. }
    clear - Ha X1 X2 X8 HB OR. unfold SB. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SFR : S F = F / 8 + 2147450880 /\ S (F + 512 - 1) = F / 8 + 2147450880 + 63). { unfold S, SB. rewrite (proj1 (proj2 F8)). split; clear; lia. }
  destruct SFR as [SF0 SF1].
  split. { clear - OR. lia. } split. exact OBIG.
  split. { apply (proj2 (zeros_at_vis _ Mc _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  split. { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis _ Mc o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  split. { pose proof (apart_of_client (aclient L ar LB FF E SCRD) o 32 (E - 384) 384 ltac:(clear; lia) ltac:(clear; lia) CL0 ltac:(intros a Ha; apply NCS; clear - Ha; lia)) as X. clear - X; lia. }
  split. { apply (apart_of_client (aclient L ar LB FF E SCRD) o 32 F 512 ltac:(clear; lia) ltac:(clear; lia) CL0). intros a Ha. apply NCF. left. exact Ha. }
  split. { apply (apart_of_client (aclient L ar LB FF E SCRD) o 32 SH 64 ltac:(clear; lia) ltac:(clear; lia) CL0). intros a Ha. apply NCF. right. rewrite SF0, SF1. clear - Ha; lia. }
  split. { apply (apart_of_client (aclient L ar LB FF E SCRD) (o / 8 + 2147450880) 4 F 512 ltac:(clear; lia) ltac:(clear; lia) CLS). intros a Ha. apply NCF. left. exact Ha. }
  split. { apply (apart_of_client (aclient L ar LB FF E SCRD) (o / 8 + 2147450880) 4 SH 64 ltac:(clear; lia) ltac:(clear; lia) CLS). intros a Ha. apply NCF. right. rewrite SF0, SF1. clear - Ha; lia. }
  split. { apply (apart_of_client (aclient L ar LB FF E SCRD) (o / 8 + 2147450880) 4 (E - 384) 384 ltac:(clear; lia) ltac:(clear; lia) CLS). intros a Ha. apply NCS. clear - Ha; lia. }
  split. { intros v Hc. apply (proj2 (u8_at_vis _ Mc o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc. }
  split. { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis _ Mc a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc. }
  intros a Ha. split. { exact (obj_client L ar (BX ++ LB) FF' 0 0 o 32 a AOB' Ha). } split. clear - Ha OR; lia.
  split. { intros X. subst a. apply FLNC. apply (obj_client L ar LB FF' 0 0 o 32 fl AOB'). exact Ha. }
  intros X. pose proof (OCR a X) as Y. apply (NCS a ltac:(clear - Y SPC; lia)). apply CL0. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma ea5 (fx : FPState) Rc Mc modelc W BXf LKc crc Ac bn on bd od fr bits :
  binv W (ostr on ++ ostr od ++ BXf) Mc modelc LKc crc Ac -> (forall a, ro <= a < ro + 1 -> ~ L5.outside W a) ->
  rinvTL R E F Rc -> getr Rc (reg 19) = Z_to_bv 64 ro ->
  obj_at Mc (F + 96) bn on -> obj_at Mc (F + 32) bd od -> aobj FF ro 32 -> shadow_zero Mc ro 4 ->
  L5.u64_at RSEGS Mc (E - 328) bits -> 0 <= bits <= 2 -> L5.u8_at RSEGS Mc ro fr -> 0 <= fr < 256 ->
  (forall (fxf : FPState) Rf Mf modelf Af,
      regs_preserved R Rf -> incl Ac Af -> ahpres L ar LB FF E SCRD W M Mf ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXf ++ LB) FF' SPA OPDEL_SCR a -> ~ L5AFK.Wret F fl 3 a -> ~ (F / 8 + SB + 12 <= a < F / 8 + SB + 16) -> ~ (ro <= a < ro + 1) ->
                 Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u8_at RSEGS Mf ro (Z.lor (Z.land fr 253) bits) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI (BXf ++ LB) FF LKc crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92d68 Mc modelc) K.
Proof.
  intros BI WRO RI X19 ON OD AOR SZR SP64 BITS RFB FRR KF.
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as PF.
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof (arg_facts W _ Mc modelc LKc crc Ac ro BI AOR SZR) as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  destruct (Gx W _ Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & _ & SV & _)).
  pose proof RI as ((X2 & X8 & X9 & X3 & X4 & XSB) & X18 & X20 & X21 & X24 & X27).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ALO : aligned ro 8) by exact O8.
  assert (SP64v : L5.u64_at RSEGS MV (E - 328) bits).
  { apply (proj2 (u64_at_vis _ Mc (E - 328) bits ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact SP64. }
  assert (HVB : 0 <= bits <= 2 /\ 0 <= bits < 2 ^ 64) by (clear - BITS; lia). destruct HVB as [HVB HVB'].
  assert (HVF : 0 <= fr <= 255 /\ 0 <= fr < 2 ^ 64) by (clear - FRR; lia). destruct HVF as [HVF HVF'].
  pose proof (v5EA5_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 59%nat => bits | 60%nat => fr | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XB; sc) ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & _ & _ & pFB)).
  set (Wp := fun a => ro <= a < ro + 1).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92d68 R1 0x936e8 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn. lia. }
  { intros a Ha Wa. subst Wp; cbn beta in Wa. destruct (OCL a ltac:(clear - Wa; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WRO. exact Wa. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  assert (RI1 : rinvTL R E F R1). { apply (rinvTL_ks R E F ER Rc R1 KS_v5EA5 RI pKS). vm_compute; reflexivity. }
  assert (KEEPF : forall i, F <= i < F + 512 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)). { intros i Hi. apply FRM1. clear - Hi FRP; lia. subst Wp; cbn beta. clear - Hi OF; lia. }
  assert (ON1 : obj_at M1 (F + 96) bn on). { apply (obj_at_agree Mc M1 _ _ _ ON ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KEEPF. clear - Hi; lia. }
  assert (OD1 : obj_at M1 (F + 32) bd od). { apply (obj_at_agree Mc M1 _ _ _ OD ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KEEPF. clear - Hi; lia. }
  assert (FB1 : L5.u8_at RSEGS M1 ro (Z.lor (Z.land fr 253) bits)).
  { destruct (OCL ro ltac:(clear; lia)) as (_ & _ & _ & _).
    pose proof (arg_facts W _ M1 model1 LKc crc Ac ro BI1 AOR) as X. clear X.
    assert (OVIS : avis (ahid Ac modelc) ro 32).
    { pose proof BI as (B1 & _). assert (AOB' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
      exact (proj1 (proj2 (proj2 (proj2 (aobj_facts L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc ro 32 0 0 B1 AOB' ltac:(clear; lia) ltac:(reflexivity)))))). }
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 ro _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))). rewrite VIS1. exact pFB. }
  apply (div_dtors L ar C HI LY HIok Hdel R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK RA UR1 G2 G4 HSCR fx1 R1 M1 model1 W (ostr on ++ ostr od ++ BXf) (ostr od ++ BXf) BXf LKc crc Ac bn on bd od BI1 RI1 ON1 OD1).
  { destruct on as [[q n]|]; cbn [ostr app]. split. left; reflexivity. apply lb_remove_head. reflexivity. }
  { destruct od as [[q n]|]; cbn [ostr app]. split. left; reflexivity. apply lb_remove_head. reflexivity. }
  { intros a Hc. rewrite <- app_assoc. apply aclient_appb. exact Hc. }
  intros fxf Rf Mf modelf Af RPf IAf AHf AGf RTf AMf HHf.
  apply (KF fxf Rf Mf modelf Af RPf IAf AHf).
  - intros a Ha Hc Hw Hp Hr. rewrite (AGf a Ha Hc Hw Hp). apply FRM1. exact Ha. exact Hr.
  - destruct (OCL ro ltac:(clear; lia)) as (C1 & C2 & C3 & C4).
    eapply L5C.u8_at_agree. 4: exact FB1. 2: clear - ORP; lia. 2: clear - ORP; lia. intros j Hj. assert (j = ro) by (clear - Hj; lia). subst j. apply AGf. clear - ORP; lia.
    + apply (obj_client L ar (BXf ++ LB) FF' SPA OPDEL_SCR ro 32 ro). apply aobj_cons. exact AOR. clear; lia.
    + unfold L5AFK.Wret. change (ff_bytes 3 / 8) with 64. intros X. clear - X OF OSH C3. unfold SB in X. lia.
    + unfold SB. clear - OSH. lia.
  - exact RTf.
  - exact AMf.
  - exact HHf.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVE.

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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5Mul10W L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BRed L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5BLeafK L5BShlP L5BShlK L5DivLeafSpecsAB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5ASHL16.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5MULW. Import L5BLK. Import L5ASHLP. Import L5ASHLK. Import L5DLA. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Lemma SCR_EQ : SHL_SCR + 16 = 4640. Proof. reflexivity. Qed.
Lemma RZSCR_EQ : RESIZE_SCR + 0 = 4496. Proof. reflexivity. Qed.


Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 884736 /\ L5.u64_at RSEGS MV 911160 2147450880 /\ L5.u32_at RSEGS MV 911168 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 911160 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG 911168 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma block_vis LB FF LK cr A M model q c sp :
  ri_inv HI LB FF LK cr A M (vml_of model) -> In (q, 8 * c) LB -> 1 <= c -> ahl_ceil ar + 4096 <= sp -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  let MV := mrestrict (ahid A model) M in
  (4096 <= q /\ q + 8 * c <= 140737479966720) /\ q mod 8 = 0 /\ (2147446784 + 17592186048512 <= q \/ q + 8 * c <= 2147446784)
  /\ (sp <= q \/ q + 8 * c <= sp - 4096) /\ (q + 8 * c <= q / 8 + SB \/ q / 8 + SB + c <= q) /\ (q + 8 * c <= 65536 \/ 6504448 <= q)
  /\ L5.writable RSEGS MV q (8 * c) /\ L5KA.zeros_at MV (q / 8 + SB) c /\ avis (ahid A model) q (8 * c)
  /\ (forall a v, q <= a -> a + 8 <= q + 8 * c -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
Proof.
  intros HH INB Hc SLO SPT MV.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (WB _ INB) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & QDEF & QSH & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5, QDEF, QSH.
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & _ & _ & VBLK & VBSH & _).
  assert (QV : avis (ahid A model) q (8 * c)). { apply (VBLK q (8 * c)). exact INB. lia. lia. }
  split. lia. split. lia. split. lia. split. lia. split. { unfold SB. lia. } split. lia.
  split. { apply (proj2 (writable_vis _ M q (8 * c) QV ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact QDEF. lia. lia. }
  split. { apply (proj2 (zeros_at_vis _ M (q / 8 + SB) c ltac:(apply (VBSH q (8 * c)); [exact INB | intros i Hi; unfold in_shadow_of, S; lia]))).
           intros i Hi. destruct QSH as [SZq _]. unfold shadow_zero, byte_at, S in SZq. apply SZq. lia. }
  split. exact QV.
  intros a v Ha Hb Hx. apply (proj2 (u64_at_vis _ M a v ltac:(eapply avis_sub; [exact QV | lia | lia]) ltac:(lia) ltac:(lia))). exact Hx.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma in_firstn {A} (x : A) : forall n (l : list A), In x (firstn n l) -> In x l.
Proof. induction n as [|n IH]; intros [|y l] H; cbn in H; try contradiction. destruct H as [->|H]. left; reflexivity. right. apply IH. exact H. Qed.


(* [comment removed for export] *)
Lemma data_facts LB FF LK cr A M model o sp fb (n : nat) sto :
  ri_inv HI LB FF LK cr A M (vml_of model) -> astk ar M sp 4640 -> aobj FF o 32 -> shadow_zero M o 4 -> L5KA.zeros_at M ((sp - 112) / 8 + SB) 1 ->
  L5.big_at RSEGS M o (L5.BO fb n sto) -> match sto with L5.BDyn c q => In (q, 8 * c) LB | L5.BInl _ _ => True end ->
  let H := ahid A model in let MV := mrestrict H M in
  let d := L5.bo_data o (L5.BO fb n sto) in let cap := L5.bo_cap (L5.BO fb n sto) in
  mfacts MV sp o d cap /\ avis H d (8 * cap)
  /\ (forall a v, d <= a -> a + 8 <= d + 8 * cap -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
  /\ match sto with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end
  /\ (forall a, d <= a < d + 8 * cap -> aclientw L ar LB FF 0 0 a /\ ~ (0x10000 <= a < 0x634000))
  /\ L5.big_at RSEGS MV o (L5.BO fb n sto) /\ Z.of_nat n <= cap.
Proof.
  intros HH STK AOB SZ VZm OB STB H MV d cap.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491808 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4640 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  fold H in OVIS, OVSH, VIS. 
  assert (OZv : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (W64 : L5.writable RSEGS MV (sp - 128) 128).
  { apply (proj2 (writable_vis H M (sp - 128) 128 (VIS (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (VZvis : avis H ((sp - 112) / 8 + SB) 1). { apply VSTSH; intros i Hi; unfold in_shadow_of, S, HeapIfaceA.SB, SB. clear - Hi SLO SHI SPT A16. Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VZv : L5KA.zeros_at MV ((sp - 112) / 8 + SB) 1). { apply (proj2 (zeros_at_vis H M _ 1 VZvis)). exact VZm. }
  assert (OBv : L5.big_at RSEGS MV o (L5.BO fb n sto)).
  { eapply L5C.big_at_agree. 4: exact OB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. unfold MV. apply mrestrict_visible. replace j with (o + (j - o)) by (clear; lia). apply (OVIS (j - o)). clear - Hj; lia. }
  pose proof OB as (O0b & HfbR & O8b & OSTb). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0b, HfbR, O8b, OSTb.
  subst d cap. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct sto as [u0 u1|c q].
  - destruct OSTb as (Bb & O16b & O24b & Hl2b & Ru0 & Ru1). split. 2: split. 3: split. 4: split. 5: split. 6: split.
    + constructor. clear - SPR A16; lia. exact W64. split. exact IMGC. split. exact CSB. exact CUAR. clear - OR OBIG SLO; lia. exact OZv. exact OWv.
      { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        repeat split; clear - OR OBIG SLO SPT; unfold SB; lia. }
      eapply L5.writable_sub. exact OWv. clear; lia. clear; lia. eapply L5KA.zeros_at_sub. exact OZv. 2: clear; lia. clear - OR. lia. exact VZv.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      eapply avis_sub. exact OVIS. clear; lia. clear; lia.
    + intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc.
    + exact I.
    + intros a Ha. split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Ha; lia. clear - Ha OR; lia.
    + exact OBv. + clear - Hl2b; lia.
  - destruct OSTb as (Bb & O16b & O24b & Hlcb & Hcapb & Q8b & Q4096b & Q47b & QHb).
    pose proof (block_vis LB FF LK cr A M model q c sp HH STB ltac:(clear - Hcapb; lia) ltac:(clear - SLO; lia) SPT) as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ).
    fold H in QV, XQ. fold MV in QW, QZ, XQ.
    assert (QO : o + 32 <= q \/ q + 8 * c <= o).
    { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ STB)))))) g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X. clear - X X1 X2 Hcapb. lia. }
    split. 2: split. 3: split. 4: split. 5: split. 6: split.
    + constructor. clear - SPR A16; lia. exact W64. split. exact IMGC. split. exact CSB. exact CUAR. clear - OR OBIG SLO; lia. exact OZv. exact OWv.
      { split. exact QR. split. exact QD8. split. exact QBIG. split. clear - Hcapb; lia. split. exact QFR. split. clear - QO; lia. split. exact QSHD. exact QIMG. } exact QW. exact QZ. exact VZv.
    + exact QV. + exact XQ. + exact QO.
    + intros a Ha. split. apply (block_client L ar LB FF 0 0 q (8 * c)). exact STB. clear - Ha; lia. clear - Ha QIMG; lia.
    + exact OBv. + clear - Hlcb; lia.
Qed.

Theorem shl_ok_at : resize_spec_at 0 L ar HI -> shl_specA_at 16 L ar HI.
Proof.
  intros RZ fx R M model K LB FF LK cr A o sp r k b ws HH AM HK G10 G11 Hk Lpos Hlen CAPD CR3 G1 RA G2 A32 G4 STK SSH ROOM RS OB OL AOB SZ INB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491808 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA : (sp - 112) mod 32 = 0 /\ (sp - 112) mod 16 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as [SA32 SA16].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (VZm : L5KA.zeros_at M ((sp - 112) / 8 + SB) 1).
  { unfold L5OMA.stksh in SSH. rewrite SCR_EQ in SSH. eapply zeros_of_shadow_zero. exact SSH. clear - A32; Lia.lia. clear - A32; Lia.lia. clear - SPR; Lia.lia. clear - SHI A32; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4640 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (XO : forall a v, o <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc. }
  assert (XB : forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV o v).
  { intros v Hc. apply (proj2 (u8_at_vis H M o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc. }
  assert (OZv : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (W64 : L5.writable RSEGS MV (sp - 128) 128).
  { apply (proj2 (writable_vis H M (sp - 128) 128 (VIS (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  destruct b as [fb len sto]. unfold L5.bo_dyn, L5.bo_cap, L5.bo_len in CAPD, CR3, Hlen, Lpos. cbn [L5.bo_fb L5.bo_st] in CAPD, CR3, Hlen, Lpos.
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  pose proof OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact (proj1 (proj2 (proj2 (proj2 OR)))).
  assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia). assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia).
  assert (FRO : sp - 128 + 128 <= o \/ o + 32 <= sp - 128) by (clear - OR SLO; lia). assert (HVF : 0 <= fb <= 255) by (clear - Hfb; lia).
  assert (HVL : 0 <= Z.of_nat len <= 134217728) by (clear - Hlen; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  destruct (Z.eq_dec k 0) as [K0|KN0].
  { (* [comment removed for export] *)
    subst k.
    pose proof (data_facts LB FF LK cr A M model o sp fb len sto HH STK AOB SZ VZm OB ltac:(destruct sto as [w0 w1|c q]; [exact I | exact (INB c q eq_refl)]))
      as (MF0 & DV & XD & ODYN & DCL & OBv & LCAP). fold H in DV, XD. fold MV in MF0, XD, OBv.
    set (d := L5.bo_data o (L5.BO fb len sto)) in *. set (capR := L5.bo_cap (L5.BO fb len sto)) in *.
    assert (OLv : L5C.obj_limbs RSEGS MV (L5.BO fb len sto) ws).
    { split. exact Lws. split. exact Rws. cbn [L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q]. exact LAT.
      subst d capR. unfold L5.bo_data, L5.bo_cap in XD, LCAP. cbn [L5.bo_st] in XD, LCAP. intros i Hi. apply XD. clear - Hi; lia. rewrite Lws in Hi. clear - Hi LCAP; lia. apply LAT. exact Hi. }
    destruct (shl0_core fx R MV sp o r (L5.BO fb len sto) ws) as (fx3 & R3 & M3v & MS3 & K3 & R3_2 & R3_10 & OB3 & FR3 & GR3).
    { rewrite <- r2. exact G2. } { rewrite <- r10. exact G10. } { rewrite <- r11. exact G11. } { rewrite <- r1. exact G1. } { exact RA. }
    { exact MF0. } { exact OBv. } { exact OLv. } { cbn [L5.bo_len]. clear - Hlen; lia. }
    cbn zeta in OB3. cbn [L5.bo_fb L5.bo_st] in OB3.
    set (W3 := fun a => o <= a < o + 16 \/ sp - 128 <= a < sp).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx3 R SHL R3 r M3v W3 K HH AM MS3 GR3).
    { intros a Ha Hna. apply FR3. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|Wa].
      - split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia.
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp 4640). { eapply astk_grows. exact STK. exact MGM3. }
    set (n' := L5W.rlen ws) in *.
    set (fbF := if Nat.eqb n' 0 then Z.land fb 253 else fb) in *.
    assert (OB3' : L5.big_at RSEGS M3 o (L5.BO fbF n' sto)).
    { eapply L5C.big_at_agree. 4: exact OB3. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. symmetry. rewrite <- VIS3. apply mrestrict_visible.
      replace j with (o + (j - o)) by (clear; lia). apply (OVIS (j - o)). clear - Hj; lia. }
    assert (OL3' : L5C.obj_limbs RSEGS M3 (L5.BO fbF len sto) ws).
    { split. exact Lws. split. exact Rws. cbn [L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q]. exact LAT.
      destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      pose proof (proj1 (WB _ (INB c q eq_refl))) as (_ & _ & _ & _ & QB4 & _). cbn [fst snd] in QB4.
      pose proof (DCL) as DCLq. subst d capR. unfold L5.bo_data, L5.bo_cap in DCLq, ODYN. cbn [L5.bo_st] in DCLq, ODYN.
      eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - Q4096; lia. 2: rewrite Lws; clear - Q47 Hlc; lia. intros j Hj. apply FRM3. clear - Hj Q4096 Q47 Hlc Hcap Lws; rewrite Lws in Hj; lia.
      rewrite Lws in Hj. subst W3. cbn beta. intros [X|X]. clear - X Hj ODYN Hlc; lia. clear - X Hj QB4 Hlc SLO; lia. }
    assert (SDEF3 : L5.defined M3 (sp - 4640) 4640). { eapply astk_defined. exact ASTK3. clear; lia. clear; lia. }
    apply (KONT fx3 R3 M3 model3 Same LB cr LK A).
    + unfold shl_postA_at. split.
      { apply preserved_by_index. intros j Hj. cbn in Hj.
        destruct Hj as [<-|Hj]. { rewrite R3_2. rewrite <- r2, G2. reflexivity. }
        apply K3. clear - Hj. cbn. tauto. }
      split. { rewrite r10. exact R3_10. }
      cbn zeta. unfold shl_result. change (0 =? 0) with true. cbn iota. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data]. rewrite Lws. fold n'. fold fbF.
      split. exact Rws. split. { subst n'. pose proof (L5W.rlen_le ws) as X. rewrite Lws in X. exact X. }
      exists sto. split. exact OB3'. split. exact OL3'.
      split. { unfold L5.bo_dyn. cbn [L5.bo_fb]. destruct sto as [w0 w1|c q]. right. destruct OST as (_ & _ & _ & Hl2 & _). exact Hl2. left. destruct OST as (B1 & _). exact B1. }
      split. reflexivity. split. reflexivity.
      split. { destruct sto as [w0 w1|c q]. exact I. split; reflexivity. }
      rewrite SCR_EQ. apply ahpres_of. 2: exact SDEF3. 2:{ apply dk_grows. exact MGM3. }
      intros a (Ha & Hc & Ho). apply FRM3. exact Ha. subst W3. cbn beta. intros [X|X].
      { apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia. }
      destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4640 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia.
    + exact RT3.
    + apply incl_refl.
    + exact AM3.
    + apply incl_refl.
    + exact HH3. }
  (* [comment removed for export] *)
  assert (Hk1 : 1 <= k <= 63) by (clear - Hk KN0; lia).
  assert (HVK : 1 <= k <= 63) by exact Hk1.
  (* [comment removed for export] *)
  assert (RUN : exists fx1 R1 M1v, mem_grows MV M1v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp - 112 + 112) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R SHL MV) (st fx1 R1 RESIZE M1v) /\ (forall j, In j [3; 4; 10; 27]%nat -> getr R1 (reg j) = getr R (reg j))
            /\ getr R1 (reg 1) = Z_to_bv 64 607896 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 112) /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 k
            /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat len + 1) /\ getr R1 (reg 18) = Z_to_bv 64 (o + 8) /\ getr R1 (reg 21) = Z_to_bv 64 2147450880
            /\ getr R1 (reg 22) = Z_to_bv 64 (o / 8 + 2147450880) /\ getr R1 (reg 23) = Z_to_bv 64 ((o + 8) / 8 + 2147450880)
            /\ L5.u64_at RSEGS M1v (sp - 96) (U R 26) /\ L5.u64_at RSEGS M1v (sp - 88) (U R 25) /\ L5.u64_at RSEGS M1v (sp - 80) (U R 24) /\ L5.u64_at RSEGS M1v (sp - 72) (U R 23)
            /\ L5.u64_at RSEGS M1v (sp - 64) (U R 22) /\ L5.u64_at RSEGS M1v (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1v (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1v (sp - 40) (U R 19)
            /\ L5.u64_at RSEGS M1v (sp - 32) (U R 18) /\ L5.u64_at RSEGS M1v (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1v (sp - 16) (U R 8) /\ L5.u64_at RSEGS M1v (sp - 8) (U R 1)).
  { destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1).
      pose proof (vshA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 41%nat => k | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | clear; lia | sc]) | (apply XB; sc) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR21 & aR22 & aR23 & aR24 & CVL & CVD & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. split. exact MG1. split. exact aFZ. split. exact aMS. split. { intros j Hj. apply aKS. revert Hj; apply (L5K.incl_b _ KS_vshA); vm_compute; reflexivity. }
      unfold U. repeat split; assumption.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia).
      pose proof (vshAd_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 41%nat => k | 59%nat => q | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | clear; lia | sc]) | (apply XB; sc) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR21 & aR22 & aR23 & aR24 & CVL & CVD & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. split. exact MG1. split. exact aFZ. split. exact aMS. split. { intros j Hj. apply aKS. revert Hj; apply (L5K.incl_b _ KS_vshAd); vm_compute; reflexivity. }
      unfold U. repeat split; assumption. }
  destruct RUN as (fx1 & R1 & M1v & MG1 & AFZ & AMS & AKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR18 & aR21 & aR22 & aR23 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R SHL R1 RESIZE M1v (fun a => sp - 112 <= a < sp) K HH AM AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp 4640). { eapply astk_grows. exact STK. exact MGM1. }
  assert (AG1 : forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha Hc. apply FRM1. clear - Ha Hc SPT; lia. clear - Hc SLO; lia. }
  (* [comment removed for export] *)
  apply (RZ fx1 R1 M1 model1 K LB FF LK cr A o (sp - 112) 0x94698 (Datatypes.S len) (L5.BO fb len sto) ws HH1 AM1 HK).
  - rewrite r10, (AKS 10%nat) by inl. rewrite <- r10. exact G10.
  - rewrite r11, aR11. f_equal. clear; lia.
  - clear - Hlen; lia.
  - unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st]. intros D. specialize (CAPD D). clear - CAPD; lia.
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. intros H3 D. destruct sto as [w0 w1|cap q]. 2:{ exfalso. destruct OST as (B1 & _). rewrite B1 in D. discriminate. }
    destruct OST as (_ & _ & _ & Hl2 & _). replace (Z.of_nat (Datatypes.S len)) with 3 by (clear - H3 Hl2; lia). change (8 * round_up 3) with 64. apply CR3. clear - Hk1; lia. exact D. clear - H3 Hl2; lia.
  - rewrite r1. exact aR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact aR2.
  - exact SA32.
  - rewrite r4, (AKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite RZSCR_EQ. apply (astk_sub ar M1 M1 sp 4640 112 4496 ASTK1 (mem_grows_refl M1)). clear; lia. clear; lia. clear; lia. exact SA16.
  - exact ROOM.
  - intros f Hf. specialize (RS f Hf). clear - RS; lia.
  - eapply L5C.big_at_agree. 4: exact OB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AG1. clear - Hj OR; lia. clear - Hj OR; lia.
  - destruct OL as (Lws' & Rws' & LAT'). cbn [L5.bo_len L5.bo_st] in Lws', LAT' |- *. split. exact Lws'. split. exact Rws'. destruct sto as [w0 w1|cap q]. exact LAT'.
    destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
    pose proof (proj1 (WB _ (INB cap q eq_refl))) as (_ & _ & _ & _ & QB4 & _). cbn [fst snd] in QB4.
    eapply L5C.limbs_at_agree. 4: exact LAT'. 2: clear - Q4096; lia. 2: rewrite Lws'; clear - Q47 Hlc; lia. intros j Hj. apply AG1. clear - Hj Q4096; lia. rewrite Lws' in Hj; clear - Hj QB4 Hlc; lia.
  - exact AOB.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    intros j Hj. unfold byte_at. rewrite AG1. apply SZ. exact Hj. all: unfold S; clear - Hj OR SPT; unfold SB; lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    exact INB.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 LK2 A2 POST RT2 IA2 AM2 LKI2 HH2.

    destruct POST as [RP2 GPOST].
    set (wsR := resize_limbs ws (Datatypes.S len)) in *.
    assert (EWS : wsR = ws ++ [0]). { subst wsR. unfold resize_limbs. rewrite Lws. rewrite firstn_all2 by (rewrite Lws; clear; lia). replace (Datatypes.S len - len)%nat with 1%nat by (clear; lia). reflexivity. }
    assert (CM : exists fbR stR (W12 : list L5.range),
        L5.big_at RSEGS M2 o (L5.BO fbR (Datatypes.S len) stR) /\ L5C.obj_limbs RSEGS M2 (L5.BO fbR (Datatypes.S len) stR) wsR
        /\ ahpres L ar LB FF (sp - 112) (RESIZE_SCR + 0) W12 M1 M2
        /\ (forall a, L5.outside [(o, 32); (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] a -> L5.outside W12 a)
        /\ Z.testbit fbR 1 = Z.testbit fb 1 /\ incl LB LB2
        /\ match stR with L5.BDyn c q => In (q, 8 * c) LB2 | L5.BInl _ _ => True end
        /\ match g with
           | Same => fbR = fb /\ LB2 = LB /\ cr2 = cr /\ (Z.testbit fb 0 = true \/ (Datatypes.S len <= 2)%nat)
                     /\ match sto, stR with L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end
           | Grown q c => fbR = Z.lor fb 1 /\ stR = L5.BDyn c q /\ Z.testbit fb 0 = false /\ len = 2%nat /\ c = 8 /\ LB2 = (q, 64) :: LB /\ cr2 = adebit L cr 64
                     /\ afresh L ar LB (FF ++ LK2) M2 q 64 /\ W12 = [(o, 32)]
           end).
    { destruct g as [|gq gc].
      - destruct GPOST as (DY & ELB & ECR & (st' & OB2 & OL2 & STM) & AH2). exists fb, st', [(o, 32); (L5.bo_data o (L5.BO fb len sto) + 8 * Z.of_nat (L5.bo_len (L5.BO fb len sto)), 8 * Z.max 0 (Z.of_nat (Datatypes.S len) - Z.of_nat (L5.bo_len (L5.BO fb len sto))))].
        cbn [L5.bo_fb L5.bo_st L5.bo_len] in OB2, OL2, STM, AH2 |- *.
        split. exact OB2. split. exact OL2. split. exact AH2.
        split. { intros a Ho rr [<-|[<-|[]]]. apply (Ho (o, 32)). left; reflexivity. intros X. apply (Ho (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))). right; left; reflexivity.
                 unfold L5.in_rng in X |- *. cbn [fst snd] in X |- *. clear - X. lia. }
        split. reflexivity. split. { subst LB2. apply incl_refl. }
        split. { destruct sto as [w0 w1|c q]; destruct st' as [u0 u1|c' q']; try exact I; try (exfalso; exact STM). destruct STM as [-> ->]. subst LB2. exact (INB c q eq_refl). }
        split. reflexivity. split. exact ELB. split. exact ECR. split. { unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY. exact DY. } exact STM.
      - destruct GPOST as (DY & H3 & EC & ELB & ECR & FRESH & OB2 & OL2 & AH2). cbn [L5.bo_fb L5.bo_st L5.bo_len] in OB2, OL2, AH2, DY.
        unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY.
        assert (L2 : len = 2%nat). { destruct sto as [w0 w1|c q]. destruct OST as (_ & _ & _ & Hl2 & _). clear - H3 Hl2; lia. destruct OST as (B1 & _). rewrite B1 in DY. discriminate. }
        assert (GC8 : gc = 8). { rewrite EC, L2. reflexivity. }
        exists (Z.lor fb 1), (L5.BDyn gc gq), [(o, 32)]. split. exact OB2. split. exact OL2. split. exact AH2.
        split. { intros a Ho rr [<-|[]]. apply (Ho (o, 32)). left; reflexivity. }
        split. apply lor1_bit1. split. { subst LB2. intros x Hx. right. exact Hx. }
        split. { subst LB2. rewrite GC8. left. reflexivity. }
        split. reflexivity. split. reflexivity. split. exact DY. split. exact L2. split. exact GC8. split. rewrite ELB, GC8; reflexivity. split. rewrite ECR, EC, L2; reflexivity.
        split. replace 64 with (8 * gc) by (rewrite GC8; reflexivity). exact FRESH. reflexivity. }
    clear GPOST. destruct CM as (fbR & stR & W12 & OB2 & OL2 & AH2 & WSUB & SGN & LBI & STB & GC).
    rewrite RZSCR_EQ in AH2.
    assert (Hh2 : m_halted model2 = None) by exact (proj1 AM2).
    assert (ASTK2 : astk ar M2 sp 4640).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (sp - 112) 4496 W12 HH STK MGM1 AH2). clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
    pose proof (statics_vis LB2 FF LK2 cr2 A2 M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    pose proof (aobj_facts L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 o 32 0 0 HH2 AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & OVSH2 & _). change (32 / 8) with 4 in OVSH2.
    set (H2 := ahid A2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB2 & WF2 & _).
    (* [comment removed for export] *)
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (K12 : forall a, (sp - 112 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ a = (sp - 112) / 8 + SB) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      apply (proj1 AH2 a). split. exact Ha. split. destruct Ra as [Ra|[Ra|Ra]]. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
      2:{ apply stk_shadow_client. unfold in_shadow_of, S, HeapIfaceA.SB. clear - Ra SLO SHI SPT A16; unfold SB in *; Lia.lia. clear - SPT; lia. }
      replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (aclient_narrow L ar LB FF sp 4640). apply OCLSH. clear - Ra; lia. clear - Ra OR OBIG SLO SHI SPT; unfold SB in *; lia.
      apply WSUB. intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Ra OR OBIG SLO SHI SPT; unfold SB in *; lia.
      destruct sto as [w0 w1|c q]; cbn [L5.bo_data L5.bo_st]. { destruct OST as (_ & _ & _ & Hl2 & _). clear - Ra OR OBIG SLO SHI SPT Hl2; unfold SB in *; lia. }
      destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). pose proof (proj1 (WB _ (INB c q eq_refl))) as (_ & _ & _ & _ & QB4 & QB5). cbn [fst snd] in QB4, QB5.
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QB5. clear - Ra OR SLO SHI SPT QB4 QB5 Hcap Hlc; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (V2F : forall a, (sp - 112 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ a = (sp - 112) / 8 + SB) -> H2 (Z_to_bv 64 a) = false /\ H (Z_to_bv 64 a) = false).
    { intros a [Ra|[Ra|Ra]]; split.
      - replace a with ((sp - 112) + (a - (sp - 112))) by (clear; lia). apply (VIS2 (sp - 112) 112). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with ((sp - 112) + (a - (sp - 112))) by (clear; lia). apply (VIS (sp - 112) 112). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH (a - (o / 8 + SB))). clear - Ra; lia.
      - subst a. replace ((sp - 112) / 8 + SB) with ((sp - 112) / 8 + SB + 0) by (clear; lia). apply (VSTSH2 ((sp - 112) / 8 + SB) 1). 2: clear; lia.
        intros i Hi; unfold in_shadow_of, S, HeapIfaceA.SB, SB. clear - Hi SLO SHI SPT A16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
      - subst a. replace ((sp - 112) / 8 + SB) with ((sp - 112) / 8 + SB + 0) by (clear; lia). apply (VSTSH ((sp - 112) / 8 + SB) 1). 2: clear; lia.
        intros i Hi; unfold in_shadow_of, S, HeapIfaceA.SB, SB. clear - Hi SLO SHI SPT A16. Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (XF : forall a v, sp - 112 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj.
      destruct (V2F j ltac:(left; clear - Ha Hb Hj; lia)) as [Vj Vj0]. unfold MV2. rewrite (mrestrict_visible H2 M2) by exact Vj. rewrite K12 by (left; clear - Ha Hb Hj; lia).
      rewrite <- VIS1. symmetry. apply mrestrict_visible. exact Vj0. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + SB) 4).
    { intros i Hi. destruct (V2F (o / 8 + SB + i) ltac:(right; clear - Hi; lia)) as [Vj Vj0]. unfold MV2. rewrite (mrestrict_visible H2 M2) by exact Vj.
      rewrite K12 by (right; clear - Hi; lia). rewrite FRM1. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. clear - Hi OR; unfold SB; lia. clear - Hi OR SLO SPT; unfold SB; lia. }
    assert (OW2 : L5.writable RSEGS MV2 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    assert (W64b : L5.writable RSEGS MV2 (sp - 128) 128).
    { apply (proj2 (writable_vis H2 M2 (sp - 128) 128 (VIS2 (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. clear; lia. clear; lia. clear; lia. }
    assert (VZ2 : L5KA.zeros_at MV2 ((sp - 112) / 8 + SB) 1).
    { intros i Hi. assert (Ei : (sp - 112) / 8 + SB + i = (sp - 112) / 8 + SB) by (clear - Hi; lia). rewrite Ei.
      destruct (V2F ((sp - 112) / 8 + SB) ltac:(right; right; reflexivity)) as [Vj Vj0]. unfold MV2. rewrite (mrestrict_visible H2 M2) by exact Vj.
      rewrite K12 by (right; right; reflexivity). rewrite FRM1. rewrite <- Ei. apply VZm. exact Hi.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - SPR; unfold SB; Lia.lia. clear - SPR SLO SPT; unfold SB; Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    set (d := L5.bo_data o (L5.BO fbR (Datatypes.S len) stR)). set (capR := L5.bo_cap (L5.BO fbR (Datatypes.S len) stR)).
    pose proof OB2 as (O0b & HfbR & O8b & OSTb). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0b, HfbR, O8b, OSTb.
    assert (DF : mfacts MV2 sp o d capR /\ avis H2 d (8 * capR) /\ (forall a v, d <= a -> a + 8 <= d + 8 * capR -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS MV2 a v)
                 /\ Z.of_nat len + 1 <= capR /\ match stR with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end
                 /\ (forall a, d <= a < d + 8 * (Z.of_nat len + 1) -> aclientw L ar LB2 FF 0 0 a /\ ~ (0x10000 <= a < 0x634000))).
    { subst d capR. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct stR as [u0 u1|c q].
      - destruct OSTb as (Bb & O16b & O24b & Hl2b & Ru0 & Ru1). split. 2: split. 3: split. 4: split. 5: split.
        + constructor. clear - SPR A16; lia. exact W64b. split. exact IMGC2. split. exact CSB2. exact CUAR2. clear - OR OBIG SLO; lia. exact OZ2. exact OW2.
          { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            repeat split; clear - OR OBIG SLO SPT; unfold SB; lia. }
          eapply L5.writable_sub. exact OW2. clear; lia. clear; lia. eapply L5KA.zeros_at_sub. exact OZ2. 2: clear; lia. clear - OR. lia. exact VZ2.
        + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          eapply avis_sub. exact OVIS2. clear; lia. clear; lia.
        + intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H2 M2 a v ltac:(eapply avis_sub; [exact OVIS2 | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc.
        + clear - Hl2b; lia. + exact I.
        + intros a Ha. split. apply (obj_client L ar LB2 FF 0 0 o 32 a AOB). clear - Ha Hl2b; lia. clear - Ha OR Hl2b; lia.
      - destruct OSTb as (Bb & O16b & O24b & Hlcb & Hcapb & Q8b & Q4096b & Q47b & QHb).
        pose proof (block_vis LB2 FF LK2 cr2 A2 M2 model2 q c sp HH2 STB ltac:(clear - Hcapb; lia) ltac:(clear - SLO; lia) SPT) as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ).
        fold H2 in QV, XQ. fold MV2 in QW, QZ, XQ.
        assert (QO : o + 32 <= q \/ q + 8 * c <= o).
        { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB2 _ STB)))))) g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X. clear - X X1 X2 Hcapb. lia. }
        split. 2: split. 3: split. 4: split. 5: split.
        + constructor. clear - SPR A16; lia. exact W64b. split. exact IMGC2. split. exact CSB2. exact CUAR2. clear - OR OBIG SLO; lia. exact OZ2. exact OW2.
          { split. exact QR. split. exact QD8. split. exact QBIG. split. clear - Hcapb; lia. split. exact QFR. split. clear - QO; lia. split. exact QSHD. exact QIMG. } exact QW. exact QZ. exact VZ2.
        + exact QV. + exact XQ. + clear - Hlcb; lia. + exact QO.
        + intros a Ha. split. apply (block_client L ar LB2 FF 0 0 q (8 * c)). exact STB. clear - Ha Hlcb; lia. clear - Ha QIMG Hlcb; lia. }
    destruct DF as (MF2 & DV & XD & CAPb & ODYN & DCL).
    (* [comment removed for export] *)
    assert (TOP0 : nth len wsR 0 = 0). { rewrite EWS. rewrite app_nth2 by (rewrite Lws; clear; lia). rewrite Lws, Nat.sub_diag. reflexivity. }
    assert (EWF : firstn len wsR = ws). { rewrite EWS. rewrite firstn_app, Lws, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. rewrite Lws. clear; lia. }
    destruct (shl_core fx2 R2 MV2 sp o r k fbR len stR wsR (U R 8) (U R 9) (U R 18) (U R 19) (U R 20) (U R 21) (U R 22) (U R 23) (U R 24) (U R 25) (U R 26)) as (fx3 & R3 & M3v & MS3 & K3 & R3_2 & R3_10 & R3_8 & R3_9 & R3_18 & R3_19 & R3_20 & R3_21 & R3_22 & R3_23 & R3_24 & R3_25 & R3_26 & [OB3 LIM3] & FR3 & GR3).
    all: try (rewrite (cs_of_preserved R1 R2 _ RP2) by inl).
    { exact aR2. } { exact aR8. } { exact aR9. } { exact Hk1. } { exact aR18. } { exact aR21. } { exact aR22. } { exact aR23. } { exact Lpos. }
    { apply XF. clear; lia. clear; lia. rewrite <- UR1. exact C8. } { exact RA. }
    { apply XF. clear; lia. clear; lia. exact C16. } { apply XF. clear; lia. clear; lia. exact C24. } { apply XF. clear; lia. clear; lia. exact C32. } { apply XF. clear; lia. clear; lia. exact C40. } { apply XF. clear; lia. clear; lia. exact C48. } { apply XF. clear; lia. clear; lia. exact C56. } { apply XF. clear; lia. clear; lia. exact C64. } { apply XF. clear; lia. clear; lia. exact C72. } { apply XF. clear; lia. clear; lia. exact C80. } { apply XF. clear; lia. clear; lia. exact C88. } { apply XF. clear; lia. clear; lia. exact C96. }
    { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. }
    { exact MF2. }
    { eapply L5C.big_at_agree. 4: exact OB2. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. unfold MV2. apply mrestrict_visible. replace j with (o + (j - o)) by (clear; lia). apply (OVIS2 (j - o)). clear - Hj; lia. }
    { destruct OL2 as (L1 & R1' & LAT2). cbn [L5.bo_len L5.bo_st] in L1, LAT2 |- *. split. exact L1. split. exact R1'. destruct stR as [u0 u1|c q]. exact LAT2.
      subst d capR. unfold L5.bo_data, L5.bo_cap in XD, CAPb. cbn [L5.bo_st] in XD, CAPb. intros i Hi. apply XD. clear - Hi; lia. rewrite L1 in Hi. clear - Hi CAPb; lia. apply LAT2. exact Hi. }
    { exact TOP0. } { exact CAPb. } { exact ODYN. }
    set (W3 := fun a => d <= a < d + 8 * (Z.of_nat len + 1) \/ o <= a < o + 16 \/ sp - 128 <= a < sp - 96).
    apply (apiece L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 fx2 fx3 R2 0x94698 R3 r M3v W3 K HH2 AM2 MS3 GR3).
    { intros a Ha Hna. apply FR3. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - apply DCL. exact Wa.
      - split. apply (obj_client L ar LB2 FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia.
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp 4640). { eapply astk_grows. exact ASTK2. exact MGM3. }

    (* [comment removed for export] *)
    rewrite EWF in OB3, LIM3.
    set (wl := shl_words ws k) in *.
    assert (WOK : words_ok ws) by exact Rws.
    assert (WLL : length wl = Datatypes.S len) by (subst wl; rewrite shl_words_length, Lws; reflexivity).
    assert (WLO : words_ok wl) by (subst wl; apply shl_words_ok; [clear - Hk1; lia | exact WOK]).
    pose proof (L5W.rlen_le wl) as RLE. rewrite WLL in RLE.
    set (n' := L5W.rlen wl) in *.
    set (stF := st_after stR wl) in *.
    set (fbF := if Nat.eqb n' 0 then Z.land fbR 253 else fbR) in *.
    assert (OVIS3 : avis (ahid A2 model3) o 32). { rewrite AH3. exact OVIS2. }
    assert (OB3' : L5.big_at RSEGS M3 o (L5.BO fbF n' stF)).
    { eapply L5C.big_at_agree. 4: exact OB3. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. symmetry. rewrite <- VIS3. apply mrestrict_visible.
      replace j with (o + (j - o)) by (clear; lia). apply (OVIS2 (j - o)). clear - Hj; lia. }
    assert (OL3' : L5C.obj_limbs RSEGS M3 (L5.BO fbF (Datatypes.S len) stF) wl).
    { split. exact WLL. split. exact WLO.
      cbn [L5.bo_st L5.bo_len]. subst stF. unfold st_after. destruct stR as [u0 u1|cR qR].
      - destruct OSTb as (_ & _ & _ & Hl2b & _). assert (EL1 : len = 1%nat) by (clear - Hl2b Lpos; lia).
        assert (E2 : forall l : list Z, length l = 2%nat -> l = firstn 2 [nth_w l 0; nth_w l 1]). { intros l Hl. destruct l as [|a0 [|b0 [|c0 l]]]; cbn in Hl; try discriminate. reflexivity. }
        rewrite EL1. apply E2. rewrite WLL, EL1. reflexivity.
      - intros i Hi. rewrite WLL in Hi.
        subst d. cbn [L5.bo_data L5.bo_st] in LIM3, DV. apply (proj1 (u64_at_vis (ahid A2 model2) M3 (qR + 8 * Z.of_nat i) (nth i wl 0) ltac:(eapply avis_sub; [exact DV | clear - Hi; lia | clear - Hi CAPb; lia])
                 ltac:(destruct OSTb as (_ & _ & _ & _ & _ & _ & Q4 & _); clear - Q4 Hi; lia) ltac:(destruct OSTb as (_ & _ & _ & Hlc4 & _ & _ & _ & Q47' & _); clear - Q47' Hlc4 Hi; lia))).
        rewrite VIS3. apply LIM3. rewrite WLL. exact Hi. }
    (* [comment removed for export] *)
    assert (WD : forall a, W3 a -> d <= a < d + 8 * (Z.of_nat len + 1) \/ o <= a < o + 16 \/ sp - 128 <= a < sp - 96) by (intros a Wa; exact Wa).
    assert (E03 : forall Wc, (forall a, aclient L ar LB FF sp 4640 a -> L5.outside Wc a -> ~ (o <= a < o + 32) /\ (d <= a < d + 8 * (Z.of_nat len + 1) -> False))
                 -> (forall a, L5.outside Wc a -> L5.outside [(o, 32); (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] a \/ (LB2 <> LB /\ L5.outside [(o, 32)] a))
                 -> ek L ar LB FF sp 4640 Wc M M3).
    { intros Wc HWc HW12. eapply ek_trans. { apply (ek_piece L ar LB FF sp 4640 Wc M M1 (fun a => sp - 112 <= a < sp) FRM1).
        intros a Ha Hc _ X. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4640 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
      eapply ek_trans. { intros a (Ha & Hc & Ho). apply (proj1 AH2 a). split. exact Ha. split. eapply aclient_mono. exact Hc. intros x Hx; clear - Hx; lia.
        destruct (HW12 a Ho) as [X|[NE X]]. apply WSUB. exact X. destruct g as [|gq gc]. exfalso. apply NE. exact (proj1 (proj2 GC)).
        (* [comment removed for export] *) destruct GC as (_ & _ & _ & _ & _ & _ & _ & _ & EW12). rewrite EW12. exact X. }
      intros a (Ha & Hc & Ho). apply FRM3. exact Ha. intros Wa. apply WD in Wa. destruct (HWc a Hc Ho) as [N1 N2]. destruct Wa as [Wa|[Wa|Wa]].
      exact (N2 Wa). clear - Wa N1; lia. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4640 a HH SPT Hc) as [Y|Y]. clear - Wa Y; lia. clear - Wa Y SLO; lia. }
    assert (D03 : dk L ar LB FF sp 4640 M M3).
    { eapply dk_trans. apply dk_grows. exact MGM1. eapply dk_trans. 2:{ apply dk_grows. exact MGM3. }
      intros a Ha Hc HM. destruct AH2 as (_ & SD & DK). destruct (rng_dec a (sp - 112 - 4496) (sp - 112)) as [I|O].
      replace a with (sp - 112 - 4496 + (a - (sp - 112 - 4496))) by (clear; lia). apply SD. clear - I; lia.
      apply DK. exact Ha. eapply aclient_narrow. exact Hc. exact O. exact HM. }
    assert (SDEF3 : L5.defined M3 (sp - 4640) 4640). { eapply astk_defined. exact ASTK3. clear; lia. clear; lia. }
    apply (KONT fx3 R3 M3 model3 g LB2 cr2 LK2 A2).
    + unfold shl_postA_at. split.
      { apply preserved_by_index. intros j Hj. cbn in Hj.
        assert (CH : forall j, In j KSC -> In j [3; 4; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
        { intros j' Hj1 Hj2. rewrite (K3 j' Hj1). rewrite (cs_of_preserved R1 R2 j' RP2). apply AKS. revert Hj2. apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity.
          revert Hj1. apply (L5K.incl_b KSC); vm_compute; reflexivity. }
        destruct Hj as [<-|Hj]. { rewrite R3_2. rewrite <- r2, G2. reflexivity. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { rewrite R3_8. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_9. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_18. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_19. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_20. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_21. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_22. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_23. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_24. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_25. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite R3_26. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj. }
      split. { rewrite r10. exact R3_10. }
      assert (ERW : shl_result ws k = wl). { unfold shl_result. destruct (Z.eqb_spec k 0) as [E0|_]. exfalso; exact (KN0 E0). reflexivity. }
      cbn zeta. rewrite ERW, WLL. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data]. fold n'.
      replace (Z.of_nat (Datatypes.S len)) with (Z.of_nat len + 1) by (clear; lia).
      split. exact WLO. split. exact RLE.
      exists stF. rewrite SCR_EQ.
      destruct g as [|gq gc].
      * destruct GC as (EF & ELB & ECR & DY & STM). subst fbR. split. exact OB3'. split. exact OL3'.
        split. { unfold L5.bo_dyn. cbn [L5.bo_fb]. exact DY. }
        split. exact ELB. split. exact ECR.
        split. { subst stF. unfold st_after. destruct sto as [w0 w1|c q]; destruct stR as [u0 u1|c' q']; first [exact STM | exact I | exfalso; exact STM]. }
        apply ahpres_of. 2: exact SDEF3. 2: exact D03.
        apply E03. 2:{ intros a Ho. left. exact Ho. }
        intros a Hc Ho. split. { intros X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact X. }
        intros X. apply (Ho (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd].
        subst d. destruct sto as [w0 w1|c q]; destruct stR as [u0 u1|c' q']; try (exfalso; exact STM); cbn [L5.bo_data L5.bo_st] in X |- *. exact X.
        destruct STM as [-> ->]. exact X.
      * destruct GC as (EF & EST & DY & L2 & C8' & ELB & ECR & FRESH & EW12). subst fbR.
        assert (EstF : stF = L5.BDyn 8 gq). { subst stF. rewrite EST, C8'. reflexivity. }
        split. exact OB3'. split. exact OL3'. unfold L5.bo_dyn. cbn [L5.bo_fb].
        split. exact DY. split. exact L2. split. { clear - Hk1; lia. } split. exact C8'. split. exact EstF. split. exact ELB. split. exact ECR.
        split. { destruct FRESH as (FB1 & FB2 & FB3 & FB4 & FB5). split. exact FB1. split. exact FB2. split. exact FB3.
                 split. { eapply L5.defined_grows. exact MGM3. exact FB4. }
                 destruct FB5 as [SZq SPq]. split. 2:{ intros X. exfalso. apply X. reflexivity. }
                 intros j Hj. unfold byte_at. rewrite FRM3. apply SZq. exact Hj.
                 { destruct FB1 as (F0 & F1 & F2 & F3 & F4 & F5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F5. unfold S. clear - Hj F0 F4 F5 SPT. unfold SB.
                   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
                 { intros Wa. apply WD in Wa. subst d. rewrite EST in Wa. cbn [L5.bo_data L5.bo_st] in Wa.
                   destruct FB1 as (F0 & F1 & F2 & F3 & F4 & F5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F5. unfold S in Wa. clear - Hj Wa F0 F4 F5 SPT OR OBIG SLO L2 C8'. unfold SB in *. lia. } }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        apply ahpres_of. 2: exact SDEF3. 2: exact D03.
        apply E03. 2:{ intros a Ho. right. split. rewrite ELB. clear. intros X. assert (L : length ((gq, 64) :: LB) = length LB) by (rewrite X; reflexivity). cbn in L. lia. exact Ho. }
        intros a Hc Ho. split. { intros X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact X. }
        intros X. subst d. rewrite EST in X. cbn [L5.bo_data L5.bo_st] in X.
        destruct FRESH as (FB1 & FB2 & FB3 & _). apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp 4640 gq 64 a HH SPT FB1 FB2).
        eapply fframes_apart_incl. exact FB3. intros g0 Hg; apply in_or_app; left; exact Hg. clear - X L2 C8'; lia. exact Hc.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3.
    + exact IA2.
    + exact AM3.
    + exact LKI2.
    + exact HH3.
Qed.

End WithIface.
End SCFG_1.
End L5ASHL16.

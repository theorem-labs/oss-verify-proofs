(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5Mul10W L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ARed L5AMul10P L5AMulArith L5AMul10K.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AMUL.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AMULP. Import L5MULW. Import L5AMULK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Lemma SCR_EQ : MUL10_SCR = 4560. Proof. reflexivity. Qed.
Lemma RZSCR_EQ : RESIZE_SCR = 4496. Proof. reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 880640 /\ L5.u64_at RSEGS MV 908088 2147450880 /\ L5.u32_at RSEGS MV 908096 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 908088 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG 908096 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma block_vis LB FF LK cr A M model q c sp :
  ri_inv HI LB FF LK cr A M (vml_of model) -> In (q, 8 * c) LB -> 1 <= c -> ahl_ceil ar + 4096 <= sp -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  let MV := mrestrict (ahid A model) M in
  (4096 <= q /\ q + 8 * c <= 140737479966720) /\ q mod 8 = 0 /\ (2147446784 + 17592186048512 <= q \/ q + 8 * c <= 2147446784)
  /\ (sp - 64 + 64 <= q \/ q + 8 * c <= sp - 4096) /\ (q + 8 * c <= q / 8 + SB \/ q / 8 + SB + c <= q) /\ (q + 8 * c <= 65536 \/ 6500352 <= q)
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

Theorem mul10_ok : resize_spec L ar HI -> mul10_spec L ar HI.
Proof.
  intros RZ fx R M model K LB FF LK cr A o sp r b ws HH AM HK G10 G11 Hlen CAPD CR3 G1 RA G2 A32 G4 STK ROOM RS OB OL NEG AOB SZ INB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491728 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA : (sp - 64) mod 32 = 0 /\ (sp - 64) mod 16 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as [SA32 SA16].
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4560 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (XO : forall a v, o <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc. }
  assert (XB : forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV o v).
  { intros v Hc. apply (proj2 (u8_at_vis H M o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc. }
  assert (OZv : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (W64 : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  destruct b as [fb len sto]. unfold L5.bo_dyn, L5.bo_cap, L5.bo_len, L5.bo_neg in CAPD, CR3, NEG, Hlen. cbn [L5.bo_fb L5.bo_st] in CAPD, CR3, NEG, Hlen.
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  pose proof OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact (proj1 (proj2 (proj2 (proj2 OR)))).
  assert (HV2 : 140735332487232 <= sp <= 140737488355328) by (clear - SPR; lia). assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia).
  assert (FRO : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - OR SLO; lia). assert (HVF : 0 <= fb <= 255) by (clear - Hfb; lia).
  assert (HVL : 0 <= Z.of_nat len <= 134217728) by (clear - Hlen; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  (* [comment removed for export] *)
  assert (RUN : exists x0 fx1 R1 M1v, 0 <= x0 < 2 ^ 64 /\ ((1 <= len)%nat -> x0 = nth 0 ws 0) /\ mem_grows MV M1v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R MUL10 MV) (st fx1 R1 RESIZE M1v) /\ (forall k, In k [3; 4; 10; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k))
            /\ getr R1 (reg 1) = Z_to_bv 64 585876 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 10
            /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat len + 1) /\ getr R1 (reg 18) = Z_to_bv 64 2147450880 /\ getr R1 (reg 19) = Z_to_bv 64 (Z.of_nat len)
            /\ getr R1 (reg 20) = Z_to_bv 64 x0 /\ getr R1 (reg 21) = Z_to_bv 64 (o / 8 + 2147450880)
            /\ L5.u64_at RSEGS M1v (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1v (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1v (sp - 40) (U R 19)
            /\ L5.u64_at RSEGS M1v (sp - 32) (U R 18) /\ L5.u64_at RSEGS M1v (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1v (sp - 16) (U R 8) /\ L5.u64_at RSEGS M1v (sp - 8) (U R 1)).
  { destruct sto as [w0 w1|cap q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1).
      assert (HVL2 : 0 <= Z.of_nat len <= 2) by (clear - Hl2; lia).
      pose proof (amAi_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 42%nat => w0 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | clear; lia | sc]) | (apply XB; sc) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR19 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists w0, fx1, R1, M1v. split. exact Rw0. split. { intros H1. rewrite LAT. destruct len as [|ly]. exfalso; clear - H1; lia. reflexivity. }
      split. exact MG1. split. exact aFZ. split. exact aMS. split. { intros k Hk. apply aKS. revert Hk; apply (L5K.incl_b _ KS_amAi); vm_compute; reflexivity. }
      unfold U. repeat split; assumption.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). specialize (INB cap q eq_refl).
      pose proof (block_vis LB FF LK cr A M model q cap sp HH INB ltac:(clear - Hcap; lia) ltac:(clear - SLO; lia) SPT) as (QR & QD8 & QBIG & QFR & QSH & QIMG & QW & QZ & QV & XQ). fold H in QV, XQ. fold MV in QW, QZ, XQ.
      assert (QO : q + 8 * cap <= o \/ o + 32 <= q).
      { destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ INB)))))) g ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X. clear - X X1 X2 Hcap. lia. }
      assert (QO16 : o + 16 <= q \/ q + 8 * cap <= o) by (clear - QO; lia).
      pose proof (proj1 (proj2 (WB _ INB))) as QDEF. cbn [fst snd] in QDEF.
      assert (X0C : exists x0, 0 <= x0 < 2 ^ 64 /\ L5.u64_at RSEGS M q x0 /\ ((1 <= len)%nat -> x0 = nth 0 ws 0)).
      { destruct (Nat.eq_dec len 0) as [L0|L1].
        - destruct (defined_word M q ltac:(eapply L5.defined_sub; [exact QDEF | clear; lia | clear - Hcap; lia]) ltac:(clear - Q4096; lia) ltac:(clear - Q47 Hcap; lia)) as (x0 & Rx0 & Qx0).
          exists x0. split. exact Rx0. split. exact Qx0. intros H1. exfalso. clear - H1 L0. lia.
        - exists (nth 0 ws 0). split. exact (L5W.words_ok_nth ws 0 Rws). split. 2: intros _; reflexivity.
          pose proof (LAT 0%nat ltac:(rewrite Lws; clear - L1; lia)) as L0. replace (q + 8 * Z.of_nat 0) with q in L0 by (clear; lia). exact L0. }
      destruct X0C as (x0 & Rx0 & Qx0 & X0e).
      assert (ALQ : aligned q 8) by exact QD8. assert (HVQ : 4096 <= q <= 140737488355328) by (clear - QR Hcap; lia). assert (HVC : 1 <= cap <= 134217728) by (clear - Hcap; lia).
      assert (HVQC : 4104 <= q + 8 * cap <= 140737479966720) by (clear - QR Hcap; lia).
      pose proof (amAd_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => cap | 42%nat => x0 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | clear; lia | sc]) | (apply XB; sc) | (apply XQ; [clear; lia | clear - Hcap; lia | sc]) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR19 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists x0, fx1, R1, M1v. split. exact Rx0.
      split. exact X0e.
      split. exact MG1. split. exact aFZ. split. exact aMS. split. { intros k Hk. apply aKS. revert Hk; apply (L5K.incl_b _ KS_amAd); vm_compute; reflexivity. }
      unfold U. repeat split; assumption. }
  destruct RUN as (x0 & fx1 & R1 & M1v & Rx0 & X0 & MG1 & AFZ & AMS & AKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR18 & aR19 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R MUL10 R1 RESIZE M1v (fun a => sp - 64 <= a < sp) K HH AM AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp 4560). { eapply astk_grows. exact STK. exact MGM1. }
  assert (AG1 : forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha Hc. apply FRM1. clear - Ha Hc SPT; lia. clear - Hc SLO; lia. }
  (* [comment removed for export] *)
  apply (RZ fx1 R1 M1 model1 K LB FF LK cr A o (sp - 64) 0x8f094 (Datatypes.S len) (L5.BO fb len sto) ws HH1 AM1 HK).
  - rewrite r10, (AKS 10%nat) by inl. rewrite <- r10. exact G10.
  - rewrite r11, aR11. f_equal. clear; lia.
  - clear - Hlen; lia.
  - unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st]. intros D. specialize (CAPD D). clear - CAPD; lia.
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. intros H3 D. destruct sto as [w0 w1|cap q]. 2:{ exfalso. destruct OST as (B1 & _). rewrite B1 in D. discriminate. }
    destruct OST as (_ & _ & _ & Hl2 & _). replace (Z.of_nat (Datatypes.S len)) with 3 by (clear - H3 Hl2; lia). change (8 * round_up 3) with 64. apply CR3. exact D. clear - H3 Hl2; lia.
  - rewrite r1. exact aR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact aR2.
  - exact SA32.
  - rewrite r4, (AKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite RZSCR_EQ. apply (astk_sub ar M1 M1 sp 4560 64 4496 ASTK1 (mem_grows_refl M1)). clear; lia. clear; lia. clear; lia. exact SA16.
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
        /\ ahpres L ar LB FF (sp - 64) RESIZE_SCR W12 M1 M2
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
    assert (ASTK2 : astk ar M2 sp 4560).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (sp - 64) 4496 W12 HH STK MGM1 AH2). clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & _).
    pose proof (statics_vis LB2 FF LK2 cr2 A2 M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    pose proof (aobj_facts L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 o 32 0 0 HH2 AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & OVSH2 & _). change (32 / 8) with 4 in OVSH2.
    set (H2 := ahid A2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB2 & WF2 & _).
    (* [comment removed for export] *)
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (K12 : forall a, (sp - 64 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 4) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      apply (proj1 AH2 a). split. exact Ha. split. destruct Ra as [Ra|Ra]. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
      replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (aclient_narrow L ar LB FF sp 4560). apply OCLSH. clear - Ra; lia. clear - Ra OR OBIG SLO SPT; unfold SB in *; lia.
      apply WSUB. intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Ra OR OBIG SLO SPT; unfold SB in *; lia.
      destruct sto as [w0 w1|c q]; cbn [L5.bo_data L5.bo_st]. { destruct OST as (_ & _ & _ & Hl2 & _). clear - Ra OR OBIG SLO SPT Hl2; unfold SB in *; lia. }
      destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). pose proof (proj1 (WB _ (INB c q eq_refl))) as (_ & _ & _ & _ & QB4 & QB5). cbn [fst snd] in QB4, QB5.
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QB5. clear - Ra OR SLO SPT QB4 QB5 Hcap Hlc; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (V2F : forall a, (sp - 64 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 4) -> H2 (Z_to_bv 64 a) = false /\ H (Z_to_bv 64 a) = false).
    { intros a [Ra|Ra]; split.
      - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH (a - (o / 8 + SB))). clear - Ra; lia. }
    assert (XF : forall a v, sp - 64 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj.
      destruct (V2F j ltac:(left; clear - Ha Hb Hj; lia)) as [Vj Vj0]. unfold MV2. rewrite (mrestrict_visible H2 M2) by exact Vj. rewrite K12 by (left; clear - Ha Hb Hj; lia).
      rewrite <- VIS1. symmetry. apply mrestrict_visible. exact Vj0. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + SB) 4).
    { intros i Hi. destruct (V2F (o / 8 + SB + i) ltac:(right; clear - Hi; lia)) as [Vj Vj0]. unfold MV2. rewrite (mrestrict_visible H2 M2) by exact Vj.
      rewrite K12 by (right; clear - Hi; lia). rewrite FRM1. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. clear - Hi OR; unfold SB; lia. clear - Hi OR SLO SPT; unfold SB; lia. }
    assert (OW2 : L5.writable RSEGS MV2 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    assert (W64b : L5.writable RSEGS MV2 (sp - 64) 64).
    { apply (proj2 (writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. clear; lia. clear; lia. clear; lia. }
    assert (W80 : L5.writable RSEGS MV2 (sp - 80) 16).
    { apply (proj2 (writable_vis H2 M2 (sp - 80) 16 (VIS2 (sp - 80) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      apply (L5C.writable_of_defined RSEGS). eapply astk_defined. exact ASTK2. clear; lia. clear; lia. clear - SPR; lia. clear - SPR; lia. }
    (* [comment removed for export] *)
    set (d := L5.bo_data o (L5.BO fbR (Datatypes.S len) stR)). set (capR := L5.bo_cap (L5.BO fbR (Datatypes.S len) stR)).
    pose proof OB2 as (O0b & HfbR & O8b & OSTb). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0b, HfbR, O8b, OSTb.
    assert (DF : mfacts MV2 sp o d capR /\ avis H2 d (8 * capR) /\ (forall a v, d <= a -> a + 8 <= d + 8 * capR -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS MV2 a v)
                 /\ Z.of_nat len + 1 <= capR /\ match stR with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end
                 /\ (forall a, d <= a < d + 8 * (Z.of_nat len + 1) -> aclientw L ar LB2 FF 0 0 a /\ ~ (0x10000 <= a < 0x633000))).
    { subst d capR. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct stR as [u0 u1|c q].
      - destruct OSTb as (Bb & O16b & O24b & Hl2b & Ru0 & Ru1). split. 2: split. 3: split. 4: split. 5: split.
        + constructor. clear - SPR A16; lia. exact W64b. split. exact IMGC2. split. exact CSB2. exact CUAR2. clear - OR OBIG SLO; lia. exact OZ2. exact OW2.
          { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            repeat split; clear - OR OBIG SLO SPT; unfold SB; lia. }
          eapply L5.writable_sub. exact OW2. clear; lia. clear; lia. eapply L5KA.zeros_at_sub. exact OZ2. 2: clear; lia. clear - OR. lia.
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
          { split. exact QR. split. exact QD8. split. exact QBIG. split. clear - Hcapb; lia. split. exact QFR. split. clear - QO; lia. split. exact QSHD. exact QIMG. } exact QW. exact QZ.
        + exact QV. + exact XQ. + clear - Hlcb; lia. + exact QO.
        + intros a Ha. split. apply (block_client L ar LB2 FF 0 0 q (8 * c)). exact STB. clear - Ha Hlcb; lia. clear - Ha QIMG Hlcb; lia. }
    destruct DF as (MF2 & DV & XD & CAPb & ODYN & DCL).
    (* [comment removed for export] *)
    assert (TOP0 : nth len wsR 0 = 0). { rewrite EWS. rewrite app_nth2 by (rewrite Lws; clear; lia). rewrite Lws, Nat.sub_diag. reflexivity. }
    destruct (mul10_core fx2 R2 MV2 sp o r x0 fbR len stR wsR (U R 8) (U R 9) (U R 18) (U R 19) (U R 20) (U R 21)) as (fx3 & R3 & M3v & MS3 & K3 & R3_2 & R3_10 & R3_8 & R3_9 & R3_18 & R3_19 & R3_20 & R3_21 & [OB3 LIM3] & FR3 & GR3).
    all: try (rewrite (cs_of_preserved R1 R2 _ RP2) by inl).
    { exact aR2. } { exact aR8. } { exact aR9. } { exact aR18. } { exact aR19. } { exact aR20. } { exact Rx0. }
    { intros H1. rewrite EWS. rewrite app_nth1 by (rewrite Lws; clear - H1; lia). apply X0. exact H1. }
    { exact aR21. }
    { apply XF. clear; lia. clear; lia. rewrite <- UR1. exact C8. } { exact RA. }
    { apply XF. clear; lia. clear; lia. exact C16. } { apply XF. clear; lia. clear; lia. exact C24. } { apply XF. clear; lia. clear; lia. exact C32. }
    { apply XF. clear; lia. clear; lia. exact C40. } { apply XF. clear; lia. clear; lia. exact C48. } { apply XF. clear; lia. clear; lia. exact C56. }
    { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. } { apply UR. }
    { exact MF2. } { exact W80. }
    { eapply L5C.big_at_agree. 4: exact OB2. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. unfold MV2. apply mrestrict_visible. replace j with (o + (j - o)) by (clear; lia). apply (OVIS2 (j - o)). clear - Hj; lia. }
    { destruct OL2 as (L1 & R1' & LAT2). cbn [L5.bo_len L5.bo_st] in L1, LAT2 |- *. split. exact L1. split. exact R1'. destruct stR as [u0 u1|c q]. exact LAT2.
      subst d capR. unfold L5.bo_data, L5.bo_cap in XD, CAPb. cbn [L5.bo_st] in XD, CAPb. intros i Hi. apply XD. clear - Hi; lia. rewrite L1 in Hi. clear - Hi CAPb; lia. apply LAT2. exact Hi. }
    { exact TOP0. } { exact CAPb. } { exact ODYN. }
    set (W3 := fun a => d <= a < d + 8 * (Z.of_nat len + 1) \/ o <= a < o + 16 \/ sp - 80 <= a < sp - 64).
    apply (apiece L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 fx2 fx3 R2 0x8f094 R3 r M3v W3 K HH2 AM2 MS3 GR3).
    { intros a Ha Hna. apply FR3. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - apply DCL. exact Wa.
      - split. apply (obj_client L ar LB2 FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia.
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp 4560). { eapply astk_grows. exact ASTK2. exact MGM3. }

    (* [comment removed for export] *)
    set (Vv := BigFactsBase.val wsR) in *. set (wl := BigFactsDigits.wlist (10 * Vv) (Datatypes.S len)) in *.
    assert (EV : Vv = BigFactsBase.val ws). { subst Vv. rewrite EWS. rewrite <- (val_firstn_zeros (ws ++ [0]) len). rewrite firstn_app, Lws, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite Lws; clear; lia). reflexivity.
      rewrite length_app, Lws; cbn; clear; lia. intros i Hi. rewrite length_app, Lws in Hi. cbn in Hi. rewrite app_nth2 by (rewrite Lws; clear - Hi; lia). rewrite Lws. replace (i - len)%nat with 0%nat by (clear - Hi; lia). reflexivity. }
    assert (WOK : words_ok ws) by exact Rws.
    pose proof (BigFactsBase.val_bound ws WOK) as VB. rewrite Lws, BigFactsBase.M_val in VB.
    assert (WLL : length wl = Datatypes.S len) by (subst wl; apply BigFactsDigits.wlist_length).
    pose proof (L5W.rlen_le wl) as RLE. rewrite WLL in RLE.
    set (n' := L5W.rlen wl) in *. set (ws' := firstn n' wl).
    assert (Lws' : length ws' = n'). { subst ws'. rewrite length_firstn, WLL. clear - RLE; lia. }
    assert (VAL : L5.limbs_val ws' = 10 * L5.limbs_val ws).
    { rewrite (limbs_val_val ws'), (limbs_val_val ws), <- EV. subst ws'. rewrite val_firstn_zeros. subst wl. apply val_wlist_small. rewrite EV, BigFactsBase.M_val. rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; lia). clear - VB; lia.
      rewrite WLL; clear - RLE; lia. intros i Hi. apply (L5W.rlen_zeros wl i). exact Hi. }
    assert (RED : reduced ws').
    { unfold reduced. destruct (Nat.eq_dec n' 0) as [Z0|NZ]. left. subst ws'. rewrite Z0. reflexivity.
      right. rewrite Lws'. subst ws'. rewrite nth_firstn. replace (Nat.ltb (n' - 1) n') with true by (symmetry; apply Nat.ltb_lt; clear - NZ; lia). apply (L5W.rlen_top wl). clear - NZ; subst n'; lia. }
    assert (FBID : (if Nat.eqb n' 0 then Z.land fbR 253 else fbR) = fbR).
    { destruct (Nat.eqb n' 0). apply land253_id. exact HfbR. rewrite SGN. exact NEG. reflexivity. }
    rewrite FBID in OB3.
    set (stF := st_after stR len Vv) in *.
    assert (OVIS3 : avis (ahid A2 model3) o 32). { rewrite AH3. exact OVIS2. }
    assert (OB3' : L5.big_at RSEGS M3 o (L5.BO fbR (length ws') stF)).
    { rewrite Lws'. eapply L5C.big_at_agree. 4: exact OB3. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. symmetry. rewrite <- VIS3. apply mrestrict_visible.
      replace j with (o + (j - o)) by (clear; lia). apply (OVIS2 (j - o)). clear - Hj; lia. }
    assert (OL3' : L5C.obj_limbs RSEGS M3 (L5.BO fbR (length ws') stF) ws').
    { split. reflexivity. split. { subst ws' wl. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) (Forall_wlist (10 * Vv) (Datatypes.S len)) w). eapply in_firstn. exact Hw. }
      cbn [L5.bo_st L5.bo_len]. subst stF. unfold st_after. destruct stR as [u0 u1|cR qR].
      - destruct OSTb as (_ & _ & _ & Hl2b & _). subst ws'. rewrite Lws'. subst wl n'. destruct len as [|[|k]]; [| |exfalso; clear - Hl2b; lia].
        + cbn [Nat.eqb]. set (r1 := L5W.rlen (BigFactsDigits.wlist (10 * Vv) 1)) in *. change (BigFactsDigits.wlist (10 * Vv) 1) with [BigFactsDigits.wordi (10 * Vv) 0] in *.
          destruct r1 as [|[|r2]]; [reflexivity|reflexivity|exfalso; clear - RLE; lia].
        + cbn [Nat.eqb]. set (r1 := L5W.rlen (BigFactsDigits.wlist (10 * Vv) 2)) in *. change (BigFactsDigits.wlist (10 * Vv) 2) with [BigFactsDigits.wordi (10 * Vv) 0; BigFactsDigits.wordi (10 * Vv) 1] in *.
          destruct r1 as [|[|[|r2]]]; [reflexivity|reflexivity|reflexivity|exfalso; clear - RLE; lia].
      - subst ws'. intros i Hi. rewrite Lws' in Hi. rewrite nth_firstn. replace (Nat.ltb i n') with true by (symmetry; apply Nat.ltb_lt; exact Hi).
        subst d. cbn [L5.bo_data L5.bo_st] in LIM3, DV. apply (proj1 (u64_at_vis (ahid A2 model2) M3 (qR + 8 * Z.of_nat i) (nth i wl 0) ltac:(eapply avis_sub; [exact DV | clear - Hi RLE; lia | clear - Hi RLE CAPb; lia])
                 ltac:(destruct OSTb as (_ & _ & _ & _ & _ & _ & Q4 & _); clear - Q4 Hi; lia) ltac:(destruct OSTb as (_ & _ & _ & Hlc4 & _ & _ & _ & Q47' & _); clear - Q47' Hlc4 Hi RLE; lia))).
        rewrite VIS3. apply LIM3. rewrite WLL. clear - Hi RLE; lia. }
    (* [comment removed for export] *)
    assert (WD : forall a, W3 a -> d <= a < d + 8 * (Z.of_nat len + 1) \/ o <= a < o + 16 \/ sp - 80 <= a < sp - 64) by (intros a Wa; exact Wa).
    assert (E03 : forall Wc, (forall a, aclient L ar LB FF sp 4560 a -> L5.outside Wc a -> ~ (o <= a < o + 32) /\ (d <= a < d + 8 * (Z.of_nat len + 1) -> False))
                 -> (forall a, L5.outside Wc a -> L5.outside [(o, 32); (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] a \/ (LB2 <> LB /\ L5.outside [(o, 32)] a))
                 -> ek L ar LB FF sp 4560 Wc M M3).
    { intros Wc HWc HW12. eapply ek_trans. { apply (ek_piece L ar LB FF sp 4560 Wc M M1 (fun a => sp - 64 <= a < sp) FRM1).
        intros a Ha Hc _ X. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4560 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
      eapply ek_trans. { intros a (Ha & Hc & Ho). apply (proj1 AH2 a). split. exact Ha. split. eapply aclient_mono. exact Hc. intros x Hx; clear - Hx; lia.
        destruct (HW12 a Ho) as [X|[NE X]]. apply WSUB. exact X. destruct g as [|gq gc]. exfalso. apply NE. exact (proj1 (proj2 GC)).
        (* [comment removed for export] *) destruct GC as (_ & _ & _ & _ & _ & _ & _ & _ & EW12). rewrite EW12. exact X. }
      intros a (Ha & Hc & Ho). apply FRM3. exact Ha. intros Wa. apply WD in Wa. destruct (HWc a Hc Ho) as [N1 N2]. destruct Wa as [Wa|[Wa|Wa]].
      exact (N2 Wa). clear - Wa N1; lia. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4560 a HH SPT Hc) as [Y|Y]. clear - Wa Y; lia. clear - Wa Y SLO; lia. }
    assert (D03 : dk L ar LB FF sp 4560 M M3).
    { eapply dk_trans. apply dk_grows. exact MGM1. eapply dk_trans. 2:{ apply dk_grows. exact MGM3. }
      intros a Ha Hc HM. destruct AH2 as (_ & SD & DK). destruct (rng_dec a (sp - 64 - 4496) (sp - 64)) as [I|O].
      replace a with (sp - 64 - 4496 + (a - (sp - 64 - 4496))) by (clear; lia). apply SD. clear - I; lia.
      apply DK. exact Ha. eapply aclient_narrow. exact Hc. exact O. exact HM. }
    assert (SDEF3 : L5.defined M3 (sp - 4560) 4560). { eapply astk_defined. exact ASTK3. clear; lia. clear; lia. }
    apply (KONT fx3 R3 M3 model3 g LB2 cr2 LK2 A2).
    + unfold arith_post. split.
      { apply preserved_by_index. intros k Hk. cbn in Hk.
        assert (CH : forall k, In k KSC -> In k [3; 4; 10; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k) = getr R (reg k)).
        { intros k' Hk1 Hk2. rewrite (K3 k' Hk1). rewrite (cs_of_preserved R1 R2 k' RP2). apply AKS. exact Hk2. revert Hk1. apply (L5K.incl_b KSC); vm_compute; reflexivity. }
        destruct Hk as [<-|Hk]. { rewrite R3_2. rewrite <- r2, G2. reflexivity. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { rewrite R3_8. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite R3_9. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite R3_18. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite R3_19. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite R3_20. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite R3_21. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk as [<-|Hk]. { apply CH; inl. }
        destruct Hk. }
      split. { rewrite r10. exact R3_10. }
      exists ws', stF. split. exact VAL. split. exact RED. split. { cbn [L5.bo_len]. rewrite Lws'. clear - RLE; lia. }
      cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data]. rewrite SCR_EQ.
      destruct g as [|gq gc].
      * destruct GC as (EF & ELB & ECR & DY & STM). subst fbR. split. exact OB3'. split. exact OL3'.
        split. { unfold L5.bo_dyn. cbn [L5.bo_fb]. destruct DY as [DY|DY]. left; exact DY. right; clear - DY; lia. }
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
        split. exact DY. split. exact L2. split. exact C8'. split. exact EstF. split. exact ELB. split. exact ECR.
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
        destruct FRESH as (FB1 & FB2 & FB3 & _). apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp 4560 gq 64 a HH SPT FB1 FB2).
        eapply fframes_apart_incl. exact FB3. intros g0 Hg; apply in_or_app; left; exact Hg. clear - X L2 C8'; lia. exact Hc.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3.
    + exact IA2.
    + exact AM3.
    + exact LKI2.
    + exact HH3.
Qed.

End WithIface.
End SCFG_1.
End L5AMUL.

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
     L5CoreA L5CoreSpecsA L5StepA L5ARed L5AAdddP L5AAdddK As0_code_8f368_90368.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AADD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AADDP. Import L5MULW. Import L5AADDK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Lemma SCR_EQ : ADDD_SCR = 4656. Proof. reflexivity. Qed.
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
  (4096 <= q /\ q + 8 * c <= 140737479966720 /\ (q + 8 * c <= 2147446784 \/ 17594333495296 <= q)) /\ q mod 8 = 0 /\ (2147446784 + 17592186048512 <= q \/ q + 8 * c <= 2147446784)
  /\ (sp - 160 + 160 <= q \/ q + 8 * c <= sp - 4096) /\ (q + 8 * c <= q / 8 + SB \/ q / 8 + SB + c <= q) /\ (q + 8 * c <= 65536 \/ 6500352 <= q)
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



Theorem addd_ok : resize_spec L ar HI -> addd_spec L ar HI.
Proof.
  intros RZ dd Hdd fx R M model K LB FF LK cr A o sp r b ws HH AM HK G10 G11 Hlen CAPD CR3 G1 RA G2 A32 G4 STK ROOM RS OB OL NEG AOB SZ INB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491824 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA : (sp - 160) mod 32 = 0 /\ (sp - 160) mod 16 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as [SA32 SA16].
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4656 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W160 : L5.writable RSEGS MV (sp - 160) 160).
  { apply (proj2 (writable_vis H M (sp - 160) 160 (VIS (sp - 160) 160 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  destruct b as [fb len sto]. unfold L5.bo_dyn, L5.bo_cap, L5.bo_len, L5.bo_neg in CAPD, CR3, NEG, Hlen. cbn [L5.bo_fb L5.bo_st] in CAPD, CR3, NEG, Hlen.
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  pose proof OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  assert (ALS : aligned sp 32) by exact A32. assert (ALO : aligned o 8) by exact (proj1 (proj2 (proj2 (proj2 OR)))).
  assert (HV2 : 140735332487328 <= sp <= 140737488355328) by (clear - SPR; lia). assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia).
  assert (FRO : sp - 160 + 160 <= o \/ o + 32 <= sp - 160) by (clear - OR SLO; lia). assert (HVF : 0 <= fb <= 255) by (clear - Hfb; lia).
  assert (HVL : 0 <= Z.of_nat len <= 134217728) by (clear - Hlen; lia). assert (HVY : 0 <= dd < 2 ^ 64) by (clear - Hdd; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  (* [comment removed for export] *)
  pose proof (adA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 39%nat => dd | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR19 & aR20 & aR24 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R ADDD R1 SM1 M1v (fun a => sp - 160 <= a < sp) K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (AG1 : forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha Hc. apply FRM1. clear - Ha Hc SPT; lia. clear - Hc SLO; lia. }
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = sp - 160). { rewrite r2, aR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. apply (astack_ok_of_astk L ar C LY M M1 sp 4656 160 512 STK MGM1). clear; lia. clear; lia. clear; lia. exact SA16.
  - clear - ROOM. unfold ffr in ROOM. unfold ff_room. lia.
  - intros f Hf. rewrite U2. specialize (RS f Hf). clear - RS. lia.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, aR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 1 (sp - 160 + 32) fl HH2 ltac:(left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 sp 4656).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (sp - 160) 512 HH STK MGM1 PRES2). clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (AOB2 : aobj FF' o 32). { apply aobj_cons. exact AOB. }

    (* [comment removed for export] *)
    assert (K2o : forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra OR; unfold SB in *; lia).
      rewrite (proj1 PRES2 a). 2: exact Ha. 2:{ apply (aclient_narrow L ar LB FF sp 4656). destruct Ra as [Ra|Ra]. replace a with (o + (a - o)) by (clear; lia). apply OCL. clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ra; lia. clear - Ra OR SLO SPT; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      apply AG1. clear - Ra OR; unfold SB in *; lia. clear - Ra OR SPT; unfold SB in *; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (K2f : forall a, sp - 160 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ra. apply (proj1 PRES2 a). clear - Ra SPR; lia. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. }
    pose proof (aobj_facts L ar C HI LY HIok LB FF' LK2 cr A M2 model2 o 32 0 0 HH2 AOB2 ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & OVSH2 & _). change (32 / 8) with 4 in OVSH2.
    assert (V2 : forall a, (sp - 160 <= a < sp \/ o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> H2 (Z_to_bv 64 a) = false).
    { intros a [Ra|[Ra|Ra]].
      - replace a with ((sp - 160) + (a - (sp - 160))) by (clear; lia). apply (VIS2 (sp - 160) 160). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia. }
    assert (XO2 : forall a v, o <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. unfold MV2. rewrite (mrestrict_visible H2 M2). apply K2o. left; clear - Ha Hb Hj; lia. apply V2. right; left; clear - Ha Hb Hj; lia. }
    assert (XB2 : forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV2 o v).
    { intros v Hc. eapply L5C.u8_at_agree. 4: exact Hc. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. unfold MV2. rewrite (mrestrict_visible H2 M2). apply K2o. left; clear - Hj; lia. apply V2. right; left; clear - Hj; lia. }
    assert (XF2 : forall a v, sp - 160 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. unfold MV2. rewrite (mrestrict_visible H2 M2) by (apply V2; left; clear - Ha Hb Hj; lia).
      rewrite K2f by (clear - Ha Hb Hj; lia). rewrite <- VIS1. symmetry. apply mrestrict_visible. replace j with ((sp - 160) + (j - (sp - 160))) by (clear; lia). apply (VIS (sp - 160) 160). clear - SLO; lia. clear - SPR; lia. clear - Ha Hb Hj; lia. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + SB) 4). { intros i Hi. unfold MV2. rewrite (mrestrict_visible H2 M2) by (apply V2; right; right; clear - Hi; lia). rewrite K2o by (right; clear - Hi; lia). unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
    assert (OW2 : L5.writable RSEGS MV2 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    assert (W160b : L5.writable RSEGS MV2 (sp - 160) 160).
    { apply (proj2 (writable_vis H2 M2 (sp - 160) 160 (VIS2 (sp - 160) 160 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. clear; lia. clear; lia. clear; lia. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl sp 4656 o 32 HH2 SPT ltac:(left; reflexivity) ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC OCL ltac:(clear; lia)) as (OF & OFSH & OFL).
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl sp 0 (sp - 160) 160 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 1) with 128 in OF, SF. change (ff_bytes 1 / 8) with 16 in OFSH, SFSH.
    assert (OF40 : o + 40 <= F \/ F + 128 <= o - 32).
    { destruct AOB as (g & Hg & X1 & X2 & _). pose proof (FAPART g ltac:(apply in_or_app; left; exact Hg)) as X. clear - X X1 X2. unfold ff_bytes in *. destruct (ff_class g); cbn in *; lia || nia. }
    assert (OFSS : o / 8 + 2147450880 + 4 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 16 <= o / 8 + 2147450880) by (clear - OF OR F8; lia).
    assert (HVFr : 4096 <= F <= 140737488355200) by (clear - FR; lia). assert (HVFL : 4096 <= fl <= 140737488355327) by (clear - FLR; lia). assert (ALF : aligned F 32) by exact F32.
    assert (FLCv' : L5.u64_at RSEGS MV2 (F + 120) fl). { replace (F + 120) with (F + 128 - 8) by (clear; lia). exact FLCv. }
    (* [comment removed for export] *)
    pose proof (adB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 39%nat => dd | 40%nat => F | 41%nat => fl | 43%nat => U R2 1 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XO2; [clear; lia | clear; lia | sc]) | (apply XB2; sc) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR18 & bR21 & bR22 & bR23 & bR25 & bR26 & bC136 & bB_V40nat & bB_V40nat_1 & bB_V40nat_2 & bB_V40nat_3 & bB_V40nat_4 & bB_V40nat_5 & bB_V40nat_6 & bB_V40nat_7 & bB_V40nat_8 & bB_V40nat_9 & bB_V40nat_10 & bB_V40nat_11 & bQ_V40nat & bQ_V40nat_1 & bQ_V40nat_2 & bDF)).
    set (W2 := fun a => sp - 136 <= a < sp - 128 \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 12).
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 0x8f258 R3 RESIZE M3v W2 K HH2 (conj Hh2 MI2) bMS MG3).
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W2; cbn beta in Hna; unfold SB in *; lia. }
    { intros a Ha Wa. subst W2; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 1 (sp - 160 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 1 (sp - 160 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp 4656). { eapply astk_grows. exact ASTK2. exact MGM3. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as WF2.
    assert (ND2 : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF2. decompose [and] WF2. assumption. }
    assert (K3o : forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ra. rewrite FRM3. apply K2o. exact Ra. clear - Ra OR; unfold SB in *; lia. subst W2; cbn beta. clear - Ra OR OBIG SLO SPT OF OFSS FR F8 FBIG; unfold SB in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    apply (RZ fx3 R3 M3 model3 K LB FF' LK2 cr A o (sp - 160) 0x8f334 (Datatypes.S len) (L5.BO fb len sto) ws HH3 AM3 HK).
    + rewrite r10. exact bR10.
    + rewrite r11, bR11. f_equal. clear; lia.
    + clear - Hlen; lia.
    + unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st]. intros DY. specialize (CAPD DY). clear - CAPD; lia.
    + unfold L5.bo_dyn. cbn [L5.bo_fb]. intros H3 DY. destruct sto as [w0 w1|cap q]. 2:{ exfalso. destruct OST as (B1 & _). rewrite B1 in DY. discriminate. }
      destruct OST as (_ & _ & _ & Hl2 & _). replace (Z.of_nat (Datatypes.S len)) with 3 by (clear - H3 Hl2; lia). change (8 * round_up 3) with 64. apply CR3. exact DY. clear - H3 Hl2; lia.
    + rewrite r1. exact bR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. rk.
    + exact SA32.
    + rewrite r4. rk.
    + rewrite RZSCR_EQ. apply (astk_sub ar M3 M3 sp 4656 160 4496 ASTK3 (mem_grows_refl M3)). clear; lia. clear; lia. clear; lia. exact SA16.
    + apply (ffr_push FF LK LK2 (F, 1, sp - 160 + 32) 5 4 ROOM LKI2 ND2). clear; lia. clear; lia.
    + apply (ffrs_push FF sp). exact RS. clear; lia. clear; lia.
    + eapply L5C.big_at_agree. 4: exact OB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply K3o. left; clear - Hj; lia.
    + destruct OL as (Lws' & Rws' & LAT'). cbn [L5.bo_len L5.bo_st] in Lws', LAT' |- *. split. exact Lws'. split. exact Rws'. destruct sto as [w0 w1|cap q]. exact LAT'.
      destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      pose proof (proj1 (WB _ (INB cap q eq_refl))) as (_ & _ & _ & _ & QB4 & QB5). cbn [fst snd] in QB4, QB5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QB5.
      pose proof (FBLK _ (INB cap q eq_refl)) as QF. cbn [fst snd] in QF.
      eapply L5C.limbs_at_agree. 4: exact LAT'. 2: clear - Q4096; lia. 2: rewrite Lws'; clear - Q47 Hlc; lia. intros j Hj. rewrite Lws' in Hj.
      rewrite FRM3. 2: clear - Hj Q4096 Q47 Hlc; lia. 2:{ subst W2; cbn beta. clear - Hj QB4 QB5 QF Hlc Hcap SLO SPT FR F8; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      rewrite (proj1 PRES2 j). apply AG1. clear - Hj Q4096; lia. clear - Hj QB4 Hlc; lia. clear - Hj Q4096 Q47 Hlc; lia.
      apply (block_client L ar LB FF _ _ q (8 * cap)). exact (INB cap q eq_refl). clear - Hj Hlc; lia.
    + exact AOB2.
    + intros j Hj. unfold byte_at. rewrite K3o. apply SZ. exact Hj. right. unfold S. clear - Hj; lia.
    + exact INB.
    + (* [comment removed for export] *)
      intros fx4 R4 M4 model4 g LB4 cr4 LK4 A4 POST RT4 IA4 AM4 LKI4 HH4.
    destruct POST as [RP4 GPOST].
      set (wsR := resize_limbs ws (Datatypes.S len)) in *.
      assert (EWS : wsR = ws ++ [0]). { subst wsR. unfold resize_limbs. rewrite Lws. rewrite firstn_all2 by (rewrite Lws; clear; lia). replace (Datatypes.S len - len)%nat with 1%nat by (clear; lia). reflexivity. }
      assert (CM : exists fbR stR (W12 : list L5.range),
          L5.big_at RSEGS M4 o (L5.BO fbR (Datatypes.S len) stR) /\ L5C.obj_limbs RSEGS M4 (L5.BO fbR (Datatypes.S len) stR) wsR
          /\ ahpres L ar LB FF' (sp - 160) RESIZE_SCR W12 M3 M4
          /\ (forall a, L5.outside [(o, 32); (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))] a -> L5.outside W12 a)
          /\ Z.testbit fbR 1 = Z.testbit fb 1 /\ incl LB LB4
          /\ match stR with L5.BDyn c q => In (q, 8 * c) LB4 | L5.BInl _ _ => True end
          /\ match g with
             | Same => fbR = fb /\ LB4 = LB /\ cr4 = cr /\ (Z.testbit fb 0 = true \/ (Datatypes.S len <= 2)%nat)
                       /\ match sto, stR with L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end
             | Grown q c => fbR = Z.lor fb 1 /\ stR = L5.BDyn c q /\ Z.testbit fb 0 = false /\ len = 2%nat /\ c = 8 /\ LB4 = (q, 64) :: LB /\ cr4 = adebit L cr 64
                       /\ afresh L ar LB (FF' ++ LK4) M4 q 64 /\ W12 = [(o, 32)]
             end).
      { destruct g as [|gq gc].
        - destruct GPOST as (DY & ELB & ECR & (st' & OB2 & OL2 & STM) & AH2). exists fb, st', [(o, 32); (L5.bo_data o (L5.BO fb len sto) + 8 * Z.of_nat (L5.bo_len (L5.BO fb len sto)), 8 * Z.max 0 (Z.of_nat (Datatypes.S len) - Z.of_nat (L5.bo_len (L5.BO fb len sto))))].
          cbn [L5.bo_fb L5.bo_st L5.bo_len] in OB2, OL2, STM, AH2 |- *.
          split. exact OB2. split. exact OL2. split. exact AH2.
          split. { intros a Ho rr [<-|[<-|[]]]. apply (Ho (o, 32)). left; reflexivity. intros X. apply (Ho (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))). right; left; reflexivity.
                   unfold L5.in_rng in X |- *. cbn [fst snd] in X |- *. clear - X. lia. }
          split. reflexivity. split. { subst LB4. apply incl_refl. }
          split. { destruct sto as [w0 w1|c q]; destruct st' as [u0 u1|c' q']; try exact I; try (exfalso; exact STM). destruct STM as [-> ->]. subst LB4. exact (INB c q eq_refl). }
          split. reflexivity. split. exact ELB. split. exact ECR. split. { unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY. exact DY. } exact STM.
        - destruct GPOST as (DY & H3 & EC & ELB & ECR & FRESH & OB2 & OL2 & AH2). cbn [L5.bo_fb L5.bo_st L5.bo_len] in OB2, OL2, AH2, DY.
          unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY.
          assert (L2 : len = 2%nat). { destruct sto as [w0 w1|c q]. destruct OST as (_ & _ & _ & Hl2 & _). clear - H3 Hl2; lia. destruct OST as (B1 & _). rewrite B1 in DY. discriminate. }
          assert (GC8 : gc = 8). { rewrite EC, L2. reflexivity. }
          exists (Z.lor fb 1), (L5.BDyn gc gq), [(o, 32)]. split. exact OB2. split. exact OL2. split. exact AH2.
          split. { intros a Ho rr [<-|[]]. apply (Ho (o, 32)). left; reflexivity. }
          split. apply lor1_bit1. split. { subst LB4. intros x Hx. right. exact Hx. }
          split. { subst LB4. rewrite GC8. left. reflexivity. }
          split. reflexivity. split. reflexivity. split. exact DY. split. exact L2. split. exact GC8. split. rewrite ELB, GC8; reflexivity. split. rewrite ECR, EC, L2; reflexivity.
          split. replace 64 with (8 * gc) by (rewrite GC8; reflexivity). exact FRESH. reflexivity. }
      clear GPOST. destruct CM as (fbR & stR & W12 & OB4 & OL4 & AH4 & WSUB & SGN & LBI & STB & GC).
      rewrite RZSCR_EQ in AH4.
      assert (Hh4 : m_halted model4 = None) by exact (proj1 AM4).
      assert (ASTK4 : astk ar M4 sp 4656).
      { apply (astk_after L ar C HI HIok LB FF' LK2 cr A M3 M3 M4 _ sp _ (sp - 160) 4496 W12 HH3 ASTK3 (mem_grows_refl M3) AH4). clear; lia. clear; lia. clear; lia. }
      pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & _).
      pose proof (statics_vis LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4).
      pose proof (aobj_facts L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 o 32 0 0 HH4 AOB2 ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF4 & OVIS4 & OVSH4 & _). change (32 / 8) with 4 in OVSH4.
      set (H4 := ahid A4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (WB4 & WF4 & FSAPP & _).
      pose proof FSAPP as FSAPP'. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP'.
      pose proof FAPP as FAPP'. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FAPP'.
      assert (FLAPP : fl + 1 <= 2147446784 \/ 17594333495296 <= fl) by (clear - FLP FSAPP'; unfold FS_BYTES in *; lia).
      assert (OAPP : o + 32 <= 2147446784 \/ 17594333495296 <= o).
      { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (WF g0 Hg) as (Y1 & Y2 & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP0 & _).
        unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP0, Y2. clear - X1 X2 Y1 Y2 FSAPP0. lia. }
      assert (FLNC4 : ~ aclient L ar LB4 FF' 0 0 fl).
      { destruct g as [|gq gc]. { destruct GC as (_ & ELB & _). rewrite ELB. exact FLNC. }
        destruct GC as (_ & EST & _ & _ & GC8 & ELB & _). intros X. rewrite ELB in X. destruct (aclient_consb_inv L ar LB FF' _ 0 0 fl X) as [Y|[Y|Y]]. exact (FLNC Y).
        - cbn [fst snd] in Y. pose proof (WB4 (gq, 64) ltac:(rewrite ELB; left; reflexivity)) as (_ & _ & _ & _ & _ & _ & Z7). cbn [fst snd] in Z7. clear - Y Z7 FLP. unfold FS_BYTES in *. lia.
        - cbn [fst snd] in Y. unfold in_shadow_of, S in Y. pose proof (proj1 (WB4 (gq, 64) ltac:(rewrite ELB; left; reflexivity))) as (Q0 & _ & _ & _ & Q4 & _). cbn [fst snd] in Q0, Q4.
          clear - Y Q0 Q4 FLAPP SLO SPR. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      pose proof OB4 as (O0b & HfbR & O8b & OSTb). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0b, HfbR, O8b, OSTb.
      (* [comment removed for export] *)
      set (RNG := fun a => sp - 160 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16).   (* [comment removed for export] *)
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
      assert (K34 : forall a, RNG a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR FR F8; subst RNG; cbn beta in Ra; unfold SB in *; lia).
        apply (proj1 AH4 a). split. exact Ha. split.
        { subst RNG; cbn beta in Ra. destruct Ra as [Ra|[Ra|[Ra|Ra]]].
          - apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
          - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply aclient_cons. apply (aclient_narrow L ar LB FF sp 4656). apply OCLSH. clear - Ra; lia. clear - Ra OR OBIG SLO SPT; unfold SB in *; lia.
          - apply (fframe_client L ar LB FF' _ _ F 1 (sp - 160 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ra; lia.
          - apply (fframe_shadow_client L ar LB FF' _ _ F 1 (sp - 160 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Ra F8 FQ15; unfold SB in *; lia. }
        subst RNG; cbn beta in Ra.
      assert (NO : ~ (o <= a < o + 32)) by (clear - Ra OR OBIG SLO SPT OF40 FR F8 FBIG; unfold SB in *; lia).
      destruct g as [|gq gc]. 2:{ destruct GC as (_ & _ & _ & _ & _ & _ & _ & _ & EW12). rewrite EW12. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. exact NO. }
      destruct GC as (_ & _ & _ & _ & STM).
      apply WSUB. intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. exact NO.
      destruct sto as [w0 w1|c q]; cbn [L5.bo_data L5.bo_st]. { destruct OST as (_ & _ & _ & Hl2 & _). destruct stR as [u0 u1|c' q']. 2: exfalso; exact STM. destruct OSTb as (_ & _ & _ & Hl2b & _).
          clear - Ra OR OBIG SLO SPT Hl2 Hl2b OF40 FR F8 FBIG; unfold SB in *; lia. }
      destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). pose proof (proj1 (WB _ (INB c q eq_refl))) as (_ & _ & _ & _ & QB4 & QB5). cbn [fst snd] in QB4, QB5.
      pose proof (FBLK _ (INB c q eq_refl)) as QF. cbn [fst snd] in QF. destruct stR as [u0 u1|c' q']. exfalso; exact STM. destruct STM as [-> ->]. destruct OSTb as (_ & _ & _ & Hlcb & _).
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QB5. clear - Ra OR SLO SPT QB4 QB5 QF Hcap Hlc Hlcb FR F8; unfold SB in *. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (V4 : forall a, RNG a -> H4 (Z_to_bv 64 a) = false /\ H2 (Z_to_bv 64 a) = false).
      { intros a Ra; subst RNG; cbn beta in Ra; destruct Ra as [Ra|[Ra|[Ra|Ra]]]; split.
        - replace a with ((sp - 160) + (a - (sp - 160))) by (clear; lia). apply (VIS4 (sp - 160) 160). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
        - replace a with ((sp - 160) + (a - (sp - 160))) by (clear; lia). apply (VIS2 (sp - 160) 160). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
        - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH4 (a - (o / 8 + SB))). clear - Ra; lia.
        - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia.
        - replace a with (F + (a - F)) by (clear; lia). apply (VFS4 F 128 FS1 FS2). clear - Ra; lia.
        - replace a with (F + (a - F)) by (clear; lia). apply (VFS2 F 128 FS1 FS2). clear - Ra; lia.
        - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH4 (F / 8 + SB) 16). 2: clear - Ra; lia.
          intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VSH (a - (F / 8 + SB))). clear - Ra; lia. }
      (* [comment removed for export] *)
      assert (X34 : forall a v, (sp - 160 <= a /\ a <= sp - 8 \/ F <= a /\ a <= F + 16) -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV4 a v).
      { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR FR; lia. 2: clear - Ha SPR FR; lia. intros j Hj.
        destruct (V4 j ltac:(subst RNG; cbn beta; clear - Ha Hj; lia)) as [Vj Vj2]. unfold MV4. rewrite (mrestrict_visible H4 M4) by exact Vj. rewrite K34 by (subst RNG; cbn beta; clear - Ha Hj; lia).
        apply EQ3. exact Vj2. }
      assert (X13 : forall a v, sp - 128 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M3v a v).
      { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4:{ apply XF2. clear - Ha; lia. exact Hb. exact Hc. } 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. apply bFZ. clear - Ha Hb Hj SPR; lia.
        all: subst W2; cbn beta. all: clear - Ha Hb Hj SF SFSH FR F8 SPR SLO SPT; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). all: lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (C160' : L5.u64_at RSEGS M3v (sp - 160) 0).
      { eapply L5C.u64_at_agree. 4:{ apply XF2. clear; lia. clear; lia. exact C160. } 2: clear - SPR; lia. 2: clear - SPR; lia. intros j Hj. apply bFZ. clear - Hj SPR; lia.
        all: subst W2; cbn beta. all: clear - Hj SF SFSH FR F8 SPR SLO SPT; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). all: lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (OZ4 : L5KA.zeros_at MV4 (o / 8 + SB) 4).
      { intros i Hi. destruct (V4 (o / 8 + SB + i) ltac:(subst RNG; cbn beta; clear - Hi; lia)) as [Vj _]. unfold MV4. rewrite (mrestrict_visible H4 M4) by exact Vj.
        rewrite K34 by (subst RNG; cbn beta; clear - Hi; lia). rewrite K3o by (right; clear - Hi; lia). unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
      assert (OW4 : L5.writable RSEGS MV4 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H4 M4 o 32 OVIS4)). exact ODEF4. clear - OR; lia. clear - OR; lia. }
      assert (W160d : L5.writable RSEGS MV4 (sp - 160) 160).
      { apply (proj2 (writable_vis H4 M4 (sp - 160) 160 (VIS4 (sp - 160) 160 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M4 sp). exact ASTK4. clear; lia. clear; lia. clear; lia. }
      assert (W176 : L5.writable RSEGS MV4 (sp - 176) 16).
      { apply (proj2 (writable_vis H4 M4 (sp - 176) 16 (VIS4 (sp - 176) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        apply (L5C.writable_of_defined RSEGS). eapply astk_defined. exact ASTK4. clear; lia. clear; lia. clear - SPR; lia. clear - SPR; lia. }
      (* [comment removed for export] *)
      set (d := L5.bo_data o (L5.BO fbR (Datatypes.S len) stR)). set (capR := L5.bo_cap (L5.BO fbR (Datatypes.S len) stR)).
      assert (DF : afacts MV4 sp o d capR F fl /\ avis H4 d (8 * capR) /\ (forall a v, d <= a -> a + 8 <= d + 8 * capR -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS MV4 a v)
                   /\ Z.of_nat len + 1 <= capR /\ match stR with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end
                   /\ (forall a, d <= a < d + 8 * (Z.of_nat len + 1) -> aclientw L ar LB4 FF' 0 0 a /\ ~ (0x10000 <= a < 0x633000))
                   /\ ((d + 8 * capR <= F \/ F + 128 <= d) /\ (d + 8 * capR <= F / 8 + SB \/ F / 8 + SB + 16 <= d))).
      { subst d capR. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct stR as [u0 u1|c q].
        - destruct OSTb as (Bb & O16b & O24b & Hl2b & Ru0 & Ru1). split. 2: split. 3: split. 4: split. 5: split. 6: split.
          + constructor. clear - SPR A32; lia. exact W160d. split. exact IMGC4. split. exact CSB4. exact CUAR4. clear - OR OBIG SLO; lia. exact OZ4. exact OW4.
            { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
              repeat split; clear - OR OBIG SLO SPT OF OFL; unfold SB; lia. }
            eapply L5.writable_sub. exact OW4. clear; lia. clear; lia. eapply L5KA.zeros_at_sub. exact OZ4. 2: clear; lia. clear - OR. lia.
          + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
            eapply avis_sub. exact OVIS4. clear; lia. clear; lia.
          + intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H4 M4 a v ltac:(eapply avis_sub; [exact OVIS4 | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc.
          + clear - Hl2b; lia. + exact I.
          + intros a Ha. split. apply (obj_client L ar LB4 FF' 0 0 o 32 a AOB2). clear - Ha Hl2b; lia. clear - Ha OR Hl2b; lia.
          + split. clear - OF; lia. clear - OFSH; lia.
        - destruct OSTb as (Bb & O16b & O24b & Hlcb & Hcapb & Q8b & Q4096b & Q47b & QHb).
          pose proof (block_vis LB4 FF' LK4 cr4 A4 M4 model4 q c sp HH4 STB ltac:(clear - Hcapb; lia) ltac:(clear - SLO; lia) SPT) as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ).
          fold H4 in QV, XQ. fold MV4 in QW, QZ, XQ.
          assert (QO : o + 32 <= q \/ q + 8 * c <= o).
          { destruct AOB2 as (g0 & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ STB)))))) g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X. clear - X X1 X2 Hcapb. lia. }
          assert (QF : q + 8 * c <= F \/ F + 128 <= q).
          { pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ STB)))))) (F, 1, sp - 160 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as X. cbn [fst snd ff_addr ff_class] in X. change (ff_bytes 1) with 128 in X. clear - X; lia. }
          assert (QFL : fl + 1 <= q \/ q + 8 * c <= fl). { pose proof (WB4 _ STB) as (_ & _ & _ & _ & X). cbn [fst snd] in X. clear - X FLP. unfold FS_BYTES in *. lia. }
          split. 2: split. 3: split. 4: split. 5: split. 6: split.
          + constructor. clear - SPR A32; lia. exact W160d. split. exact IMGC4. split. exact CSB4. exact CUAR4. clear - OR OBIG SLO; lia. exact OZ4. exact OW4.
            { split. clear - QR; lia. split. exact QD8. split. exact QBIG. split. clear - Hcapb; lia. split. exact QFR. split. clear - QO; lia. split. exact QSHD. split. exact QIMG. split. clear - QF; lia. exact QFL. } exact QW. exact QZ.
          + exact QV. + exact XQ. + clear - Hlcb; lia. + exact QO.
          + intros a Ha. split. apply (block_client L ar LB4 FF' 0 0 q (8 * c)). exact STB. clear - Ha Hlcb; lia. clear - Ha QIMG Hlcb; lia.
          + split. clear - QF Hlcb Hcapb; lia. clear - QF QR FR F8 Hcapb; unfold SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct DF as (AF4 & DV & XD & CAPb & ODYN & DCL & [DF' DFSH]).
      (* [comment removed for export] *)
      assert (CS4 : forall k, In k cs_all -> getr R4 (reg k) = getr R3 (reg k)) by (intros k Hk; apply (cs_of_preserved R3 R4 k RP4 Hk)).
      assert (CS2 : forall k, In k cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (cs_of_preserved R1 R2 k RP2 Hk)).
      assert (I2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 160)). { rewrite CS4 by inl. rewrite (bKS 2%nat) by inl. rewrite CS2 by inl. exact aR2. }
      assert (I8 : getr R4 (reg 8) = Z_to_bv 64 sp). { rewrite CS4 by inl. rewrite (bKS 8%nat) by inl. rewrite CS2 by inl. exact aR8. }
      assert (I9 : getr R4 (reg 9) = Z_to_bv 64 (sp - 160)). { rewrite CS4 by inl. rewrite (bKS 9%nat) by inl. rewrite CS2 by inl. exact aR9. }
      assert (I18 : getr R4 (reg 18) = Z_to_bv 64 F). { rewrite CS4 by inl. exact bR18. }
      assert (I19 : getr R4 (reg 19) = Z_to_bv 64 o). { rewrite CS4 by inl. rewrite (bKS 19%nat) by inl. rewrite CS2 by inl. exact aR19. }
      assert (I20 : getr R4 (reg 20) = Z_to_bv 64 dd). { rewrite CS4 by inl. rewrite (bKS 20%nat) by inl. rewrite CS2 by inl. exact aR20. }
      assert (I21 : getr R4 (reg 21) = Z_to_bv 64 (o + 8)). { rewrite CS4 by inl. exact bR21. }
      assert (I22 : getr R4 (reg 22) = Z_to_bv 64 (F / 8 + 2147450880)). { rewrite CS4 by inl. exact bR22. }
      assert (I23 : getr R4 (reg 23) = Z_to_bv 64 F). { rewrite CS4 by inl. exact bR23. }
      assert (I24 : getr R4 (reg 24) = Z_to_bv 64 2147450880). { rewrite CS4 by inl. rewrite (bKS 24%nat) by inl. rewrite CS2 by inl. exact aR24. }
      assert (I25 : getr R4 (reg 25) = Z_to_bv 64 ((o + 8) / 8 + 2147450880)). { rewrite CS4 by inl. exact bR25. }
      assert (I26 : getr R4 (reg 26) = Z_to_bv 64 (o / 8 + 2147450880)). { rewrite CS4 by inl. exact bR26. }
      (* [comment removed for export] *)
      assert (TOP0 : nth len wsR 0 = 0). { rewrite EWS. rewrite app_nth2 by (rewrite Lws; clear; lia). rewrite Lws, Nat.sub_diag. reflexivity. }
      destruct (addd_core fx4 R4 MV4 sp o dd F fl fbR len stR wsR) as (fx5 & R5 & M5v & MS5 & K5 & R5_2 & R5_10 & [OB5 LIM5] & FR5 & GR5).
      { unfold in_regs. repeat split; assumption. }
      { exact I24. } { exact I20. } { exact Hdd. } { clear - FR; lia. } { clear - FLR; lia. }
      { exact AF4. } { exact W176. }
      { eapply L5C.big_at_agree. 4: exact OB4. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. unfold MV4. apply mrestrict_visible. replace j with (o + (j - o)) by (clear; lia). apply (OVIS4 (j - o)). clear - Hj; lia. }
      { destruct OL4 as (L1 & R1' & LAT4). cbn [L5.bo_len L5.bo_st] in L1, LAT4 |- *. split. exact L1. split. exact R1'. destruct stR as [u0 u1|c q]. exact LAT4.
        subst d capR. unfold L5.bo_data, L5.bo_cap in XD, CAPb. cbn [L5.bo_st] in XD, CAPb. intros i Hi. apply XD. clear - Hi; lia. rewrite L1 in Hi. clear - Hi CAPb; lia. apply LAT4. exact Hi. }
      { exact TOP0. } { exact CAPb. } { exact ODYN. }
      set (W3 := fun a => d <= a < d + 8 * (Z.of_nat len + 1) \/ o <= a < o + 16 \/ sp - 176 <= a < sp - 160).
      apply (apiece L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 fx4 fx5 R4 0x8f334 R5 REDRET M5v W3 K HH4 AM4 MS5 GR5).
      { intros a Ha Hna. apply FR5. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
      { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
        - apply DCL. exact Wa.
        - split. apply (obj_client L ar LB4 FF' 0 0 o 32 a AOB2). clear - Wa; lia. clear - Wa OR; lia.
        - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
      intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
      assert (ASTK5 : astk ar M5 sp 4656). { eapply astk_grows. exact ASTK4. exact MGM5. }
      (* [comment removed for export] *)
      pose proof (afacts_keep MV4 M5v sp o d capR F fl AF4 GR5 ltac:(intros i Hi N1 N2 N3; apply FR5; [exact Hi | clear - N1 CAPb; lia | exact N2 | exact N3])) as AF5.
      pose proof AF5 as [[SPR5 A32'] W160e [IMGC5 [CSB5 CUAR5]] _ OZ5 OW5 DFACTS DW5 DZ5].
      assert (AG34 : forall j, RNG j -> MV4 (Z_to_bv 64 j) = M3v (Z_to_bv 64 j)).
      { intros j Rj. destruct (V4 j Rj) as [Vj Vj2]. unfold MV4. rewrite (mrestrict_visible H4 M4) by exact Vj. rewrite K34 by exact Rj. apply EQ3. exact Vj2. }
      assert (X45 : forall a v, (sp - 160 <= a /\ a <= sp - 8 \/ F <= a /\ a <= F + 120) -> L5.u64_at RSEGS MV4 a v -> L5.u64_at RSEGS M5v a v).
      { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR FR; lia. 2: clear - Ha SPR FR; lia. intros j Hj. apply FR5. clear - Ha Hj SPR FR; lia.
        clear - Ha Hj DFACTS CAPb; lia. clear - Ha Hj FRO OF; lia. clear - Ha Hj FR SLO; lia. }
      assert (XC : forall a v, sp - 128 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M5v a v).
      { intros a v Ha Hb Hc. apply X45. clear - Ha Hb; lia. apply X34. clear - Ha Hb; lia. apply X13. exact Ha. exact Hb. exact Hc. }
      assert (E160 : L5.u64_at RSEGS M5v (sp - 160) 0). { apply X45. left; clear; lia. apply X34. clear; lia. exact C160'. }
      assert (E136 : L5.u64_at RSEGS M5v (sp - 136) F). { apply X45. left; clear; lia. apply X34. clear; lia. exact bC136. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (FLC3 : L5.u64_at RSEGS M3v (F + 120) fl).
      { eapply L5C.u64_at_agree. 4: exact FLCv'. 2: clear - FR; lia. 2: clear - FR; lia. intros j Hj. apply bFZ. clear - Hj FR; lia.
        clear - Hj FR SLO; lia. clear - Hj; lia. clear - Hj FR F8 FBIG; unfold SB in *; lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (EFL : L5.u64_at RSEGS M5v (F + 120) fl).
      { apply X45. right; clear; lia.   (* [comment removed for export] *)
        pose proof (proj2 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model4 F 1 _ _ fl HH2 HH4 (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) FLC)) as X.
        change (ff_bytes 1) with 128 in X. replace (F + 128 - 8) with (F + 120) in X by (clear; lia). exact X. }
      assert (FDEF4 : L5.defined MV4 F 128). { apply (proj2 (defined_vis H4 M4 F 128 (VFS4 F 128 FS1 FS2))). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))))). }
      assert (FDEF5 : L5.defined M5v F 128). { eapply L5.defined_grows. exact GR5. exact FDEF4. }
      assert (FW5 : L5.writable RSEGS M5v F 128). { apply (L5C.writable_of_defined RSEGS). exact FDEF5. clear - FR; lia. clear - FR; lia. }
      assert (FSHD4 : L5.defined MV4 (F / 8 + SB) 16).
      { eapply L5C.defined_agree. 2:{ eapply L5.defined_grows. exact MG3. eapply L5KA.zeros_at_defined. exact FSHZ. } intros j Hj. apply AG34. subst RNG; cbn beta. clear - Hj; lia. }
      assert (FSHW5 : L5.writable RSEGS M5v (F / 8 + 2147450880) 16).
      { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact GR5. exact FSHD4. clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
      pose proof (fl_writable L ar C HI LY HIok _ FF' LK4 _ A4 M4 _ fl HH4 FLP) as [FLD4 FLW4].
      pose proof (fl_vis L ar C HI LY HIok _ FF' LK4 _ A4 M4 model4 fl HH4 FLP) as FLV4.
      assert (FLW5 : L5.writable RSEGS M5v fl 1).
      { eapply L5.writable_grows. exact GR5. apply (proj2 (writable_vis H4 M4 fl 1 FLV4 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW4. }
      assert (J8 : getr R5 (reg 8) = Z_to_bv 64 sp) by (rewrite (K5 8%nat) by inl; exact I8).
      assert (J9 : getr R5 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (K5 9%nat) by inl; exact I9).
      assert (J18 : getr R5 (reg 18) = Z_to_bv 64 F) by (rewrite (K5 18%nat) by inl; exact I18).
      assert (J19 : getr R5 (reg 19) = Z_to_bv 64 o) by (rewrite (K5 19%nat) by inl; exact I19).
      assert (J22 : getr R5 (reg 22) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (K5 22%nat) by inl; exact I22).
      assert (J23 : getr R5 (reg 23) = Z_to_bv 64 F) by (rewrite (K5 23%nat) by inl; exact I23).
      (* [comment removed for export] *)
      pose proof (adE_conc fx5 R5 M5v (fun j => match j with 2%nat => sp | 33%nat => o | 40%nat => F | 41%nat => fl | 43%nat => U R5 1
                    | 44%nat => U R 1 | 45%nat => U R 8 | 46%nat => U R 9 | 47%nat => U R 18 | 48%nat => U R 19 | 49%nat => U R 20 | 50%nat => U R 21
                    | 51%nat => U R 22 | 52%nat => U R 23 | 53%nat => U R 24 | 54%nat => U R 25 | 55%nat => U R 26 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XC; [clear; lia | clear; lia | unfold U; assumption]) ]).
      destruct P as (fx6 & R6 & M6v & MG6 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eFL0 & eB1 & eB2 & eB3 & eB4 & eB5 & eB6 & eB7 & eB8 & eB9 & eB10 & eB11 & eB12 & eB13 & eB14 & eB15 & eB16 & eQF & eDF)).
      pose proof (ret_to fx6 R6 M6v 0x8f558 W_8f558 r F_8f558 eq_refl D_8f558 ltac:(rewrite eR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
      pose proof (msteps_trans _ _ _ _ eMS RET) as MS7. clear eMS RET.
      set (W7 := fun a => (F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + 16) \/ a = fl).
      assert (MV5E : mrestrict (ahid A4 model5) M5 = M5v) by (rewrite AH5; exact VIS5).
      apply (apiece_retire L ar C HI LY HIok LB4 FF LK4 cr4 A4 M5 model5 fx5 fx6 R5 0x8f48c R6 r M6v W7 F 1 (sp - 160 + 32) fl K HH5 AM5).
      { change (ff_bytes 1) with 128. replace (F + 128 - 8) with (F + 120) by (clear; lia).
        apply (proj1 (u64_at_vis H4 M5 (F + 120) fl ltac:(eapply avis_sub; [exact (VFS4 F 128 FS1 FS2) | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
        replace (mrestrict H4 M5) with M5v by (symmetry; exact VIS5). exact EFL. }
      { exact FLNC4. }
      { rewrite AH5. exact FLV4. }
      { clear - FLR; lia. }
      { rewrite MV5E. exact MS7. }
      { rewrite MV5E. exact MG6. }
      { rewrite MV5E. intros a Ha Hna. apply eFZ. exact Ha. all: clear - Hna; subst W7; cbn beta in Hna; unfold SB in *; lia. }
      { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [[Wa|Wa]|Wa].
        - right. apply (fframe_client L ar LB4 _ 0 0 F 1 (sp - 160 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia.
        - right. apply (fframe_shadow_client L ar LB4 _ 0 0 F 1 (sp - 160 + 32)). left; reflexivity. change (ff_bytes 1) with 128.
          unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        - left; exact Wa. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      { intros a. subst W7; cbn beta. repeat match goal with X : _ |- _ => clear X end.
        destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 16)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
      { exact eFL0. }
      intros M6 model6 HH6 AM6 RT6 AH6 VIS6 MGM6 FRM6 EQ6.
      assert (ASTK6 : astk ar M6 sp 4656). { eapply astk_grows. exact ASTK5. exact MGM6. }
      (* [comment removed for export] *)
      set (Vv := BigFactsBase.val wsR) in *. set (wl := BigFactsDigits.wlist (Vv + dd) (Datatypes.S len)) in *.
      assert (EV : Vv = BigFactsBase.val ws). { subst Vv. rewrite EWS. rewrite <- (val_firstn_zeros (ws ++ [0]) len). rewrite firstn_app, Lws, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite Lws; clear; lia). reflexivity.
        rewrite length_app, Lws; cbn; clear; lia. intros i Hi. rewrite length_app, Lws in Hi. cbn in Hi. rewrite app_nth2 by (rewrite Lws; clear - Hi; lia). rewrite Lws. replace (i - len)%nat with 0%nat by (clear - Hi; lia). reflexivity. }
      assert (WOK : words_ok ws) by exact Rws.
      pose proof (BigFactsBase.val_bound ws WOK) as VB. rewrite Lws, BigFactsBase.M_val in VB.
      assert (WLL : length wl = Datatypes.S len) by (subst wl; apply BigFactsDigits.wlist_length).
      pose proof (L5W.rlen_le wl) as RLE. rewrite WLL in RLE.
      set (n' := L5W.rlen wl) in *. set (ws' := firstn n' wl).
      assert (Lws' : length ws' = n'). { subst ws'. rewrite length_firstn, WLL. clear - RLE; lia. }
      assert (VAL : L5.limbs_val ws' = L5.limbs_val ws + dd).
      { rewrite (limbs_val_val ws'), (limbs_val_val ws), <- EV. subst ws'. rewrite val_firstn_zeros. subst wl. apply val_wlist_small. rewrite EV, BigFactsBase.M_val. rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; lia). clear - VB Hdd; lia.
        rewrite WLL; clear - RLE; lia. intros i Hi. apply (L5W.rlen_zeros wl i). exact Hi. }
      assert (RED : reduced ws').
      { unfold reduced. destruct (Nat.eq_dec n' 0) as [Z0|NZ]. left. subst ws'. rewrite Z0. reflexivity.
        right. rewrite Lws'. subst ws'. rewrite nth_firstn. replace (Nat.ltb (n' - 1) n') with true by (symmetry; apply Nat.ltb_lt; clear - NZ; lia). apply (L5W.rlen_top wl). clear - NZ; subst n'; lia. }
      assert (FBID : (if Nat.eqb n' 0 then Z.land fbR 253 else fbR) = fbR).
      { destruct (Nat.eqb n' 0). apply land253_id. exact HfbR. rewrite SGN. exact NEG. reflexivity. }
      rewrite FBID in OB5.
      set (stF := st_afterA stR len (Vv + dd)) in *.
      (* [comment removed for export] *)
      pose proof DFACTS as (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG & DFf & DFL).
      assert (AG65 : forall a, (o <= a < o + 32 \/ d <= a < d + 8 * capR) -> M6 (Z_to_bv 64 a) = M5v (Z_to_bv 64 a)).
      { intros a Ra. rewrite FRM6. 2: clear - Ra OR DR; lia.
        2:{ subst W7; cbn beta. clear - Ra OF OFSH OFL DF' DFSH DFL. unfold SB in *. lia. }
        apply EQ5. destruct Ra as [Ra|Ra]. replace a with (o + (a - o)) by (clear; lia). apply (OVIS4 (a - o)). clear - Ra; lia.
        replace a with (d + (a - d)) by (clear; lia). apply (DV (a - d)). clear - Ra; lia. }
      assert (OB6 : L5.big_at RSEGS M6 o (L5.BO fbR (length ws') stF)).
      { rewrite Lws'. eapply L5C.big_at_agree. 4: exact OB5. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AG65. left; exact Hj. }
      assert (LIM6 : L5.limbs_at RSEGS M6 d wl).
      { intros i Hi. rewrite WLL in Hi. eapply L5C.u64_at_agree. 4:{ apply LIM5. rewrite WLL. exact Hi. } 2: clear - DR; lia. 2: clear - Hi DR CAPb; lia.
        intros j Hj. apply AG65. right. clear - Hi Hj CAPb; lia. }
      assert (OL6 : L5C.obj_limbs RSEGS M6 (L5.BO fbR (length ws') stF) ws').
      { split. reflexivity. split. { subst ws' wl. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) (Forall_wlist (Vv + dd) (Datatypes.S len)) w). eapply in_firstn. exact Hw. }
        cbn [L5.bo_st L5.bo_len]. subst stF. unfold st_afterA. destruct stR as [u0 u1|cR qR].
        - destruct OSTb as (_ & _ & _ & Hl2b & _). subst ws'. rewrite Lws'. subst wl n'. destruct len as [|[|k]]; [| |exfalso; clear - Hl2b; lia].
          + cbn [Nat.eqb]. set (r1 := L5W.rlen (BigFactsDigits.wlist (Vv + dd) 1)) in *. change (BigFactsDigits.wlist (Vv + dd) 1) with [BigFactsDigits.wordi (Vv + dd) 0] in *.
            destruct r1 as [|[|r2]]; [reflexivity|reflexivity|exfalso; clear - RLE; lia].
          + cbn [Nat.eqb]. set (r1 := L5W.rlen (BigFactsDigits.wlist (Vv + dd) 2)) in *. change (BigFactsDigits.wlist (Vv + dd) 2) with [BigFactsDigits.wordi (Vv + dd) 0; BigFactsDigits.wordi (Vv + dd) 1] in *.
            destruct r1 as [|[|[|r2]]]; [reflexivity|reflexivity|reflexivity|exfalso; clear - RLE; lia].
        - subst ws'. intros i Hi. rewrite Lws' in Hi. rewrite nth_firstn. replace (Nat.ltb i n') with true by (symmetry; apply Nat.ltb_lt; exact Hi).
          subst d. cbn [L5.bo_data L5.bo_st] in LIM6. apply LIM6. rewrite WLL. clear - Hi RLE; lia. }
      (* [comment removed for export] *)
      assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF sp 4656 a).
      { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ sp 4656 F 128 a HH SPT).
        clear - FR; lia. exact FCEIL. exact FAPP. exact (proj2 FQ15). clear; lia. reflexivity.
        eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
      assert (WD : forall a, W3 a -> d <= a < d + 8 * (Z.of_nat len + 1) \/ o <= a < o + 16 \/ sp - 176 <= a < sp - 160) by (intros a Wa; exact Wa).
      assert (E06 : forall Wc, (forall a, aclient L ar LB FF sp 4656 a -> L5.outside Wc a -> ~ (o <= a < o + 32) /\ (d <= a < d + 8 * (Z.of_nat len + 1) -> False))
                   -> (forall a, aclient L ar LB FF sp 4656 a -> L5.outside Wc a -> L5.outside W12 a)
                   -> ek L ar LB FF sp 4656 Wc M M6).
      { intros Wc HWc HW12.
        eapply ek_trans. { apply (ek_piece L ar LB FF sp 4656 Wc M M1 (fun a => sp - 160 <= a < sp) FRM1).
          intros a Ha Hc _ X. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4656 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
        eapply ek_trans. { apply (ek_rt L ar LB FF [] sp 4656 (sp - 160) 512 Wc M1 M2 PRES2). clear; lia. clear; lia. }
        eapply ek_trans. { apply (ek_piece L ar LB FF sp 4656 Wc M2 M3 W2 FRM3). intros a Ha Hc Ho X. subst W2; cbn beta in X. destruct X as [X|[X|X]].
          - destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4656 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia.
          - apply (NCF a). left; clear - X; lia. exact Hc.
          - apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc. }
        eapply ek_trans. { apply (ek_callee L ar LB [] FF [(F, 1, sp - 160 + 32)] sp 4656 (sp - 160) 4496 Wc W12 M3 M4 AH4). clear; lia. clear; lia. exact HW12. }
        eapply ek_trans. { apply (ek_piece L ar LB FF sp 4656 Wc M4 M5 W3 FRM5). intros a Ha Hc Ho X. apply WD in X. destruct (HWc a Hc Ho) as [N1 N2]. destruct X as [X|[X|X]].
          - exact (N2 X). - clear - X N1; lia.
          - destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4656 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
        intros a (Ha & Hc & Ho). apply FRM6. exact Ha. subst W7; cbn beta. intros [[X|X]|X].
        - apply (NCF a). left; clear - X; lia. exact Hc.
        - apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc.
        - subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc. }
      assert (D06 : dk L ar LB FF sp 4656 M M6).
      { eapply dk_trans. apply dk_grows. exact MGM1.
        eapply dk_trans. apply (dk_rt L ar LB FF [] sp 4656 (sp - 160) 512 M1 M2 PRES2). clear; lia. clear; lia.
        eapply dk_trans. apply dk_grows. exact MGM3.
        eapply dk_trans. apply (dk_callee L ar LB [] FF [(F, 1, sp - 160 + 32)] sp 4656 (sp - 160) 4496 W12 M3 M4 AH4). clear; lia. clear; lia.
        eapply dk_trans. apply dk_grows. exact MGM5. apply dk_grows. exact MGM6. }
      assert (SDEF6 : L5.defined M6 (sp - 4656) 4656). { eapply astk_defined. exact ASTK6. clear; lia. clear; lia. }
      (* [comment removed for export] *)
      apply (KONT fx6 R6 M6 model6 g LB4 cr4 LK4 A4).
      * unfold arith_post. split.
        { apply preserved_by_index. intros k Hk. cbn in Hk.
          assert (CH : forall k, In k KS_adE -> In k KSA -> In k cs_all -> In k KS_adB -> In k KS_adA -> getr R6 (reg k) = getr R (reg k)).
          { intros k' Hk1 Hk2 Hk3 Hk4 Hk5. rewrite (eKS k' Hk1), (K5 k' Hk2), (CS4 k' Hk3), (bKS k' Hk4), (CS2 k' Hk3). apply aKS. exact Hk5. }
          destruct Hk as [<-|Hk]. { rewrite eR2. rewrite <- r2, G2. reflexivity. }
          destruct Hk as [<-|Hk]. { apply CH; inl. }
          destruct Hk as [<-|Hk]. { apply CH; inl. }
          destruct Hk as [<-|Hk]. { rewrite eR8. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR9. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR18. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR19. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR20. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR21. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR22. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR23. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR24. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR25. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite eR26. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { apply CH; inl. }
          destruct Hk. }
        split. { rewrite r10. exact eR10. }
        exists ws', stF. split. exact VAL. split. exact RED. split. { cbn [L5.bo_len]. rewrite Lws'. clear - RLE; lia. }
        cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data]. rewrite SCR_EQ.
        destruct g as [|gq gc].
        -- destruct GC as (EF & ELB & ECR & DY & STM). subst fbR. split. exact OB6. split. exact OL6.
          split. { unfold L5.bo_dyn. cbn [L5.bo_fb]. destruct DY as [DY|DY]. left; exact DY. right; clear - DY; lia. }
          split. exact ELB. split. exact ECR.
          split. { subst stF. unfold st_afterA. destruct sto as [w0 w1|c q]; destruct stR as [u0 u1|c' q']; first [exact STM | exact I | exfalso; exact STM]. }
          apply ahpres_of. 2: exact SDEF6. 2: exact D06.
          apply E06. 2:{ intros a Hc Ho. apply WSUB. exact Ho. }
          intros a Hc Ho. split. { intros X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact X. }
          intros X. apply (Ho (L5.bo_data o (L5.BO fb len sto), 8 * (Z.of_nat len + 1))). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd].
          subst d. destruct sto as [w0 w1|c q]; destruct stR as [u0 u1|c' q']; try (exfalso; exact STM); cbn [L5.bo_data L5.bo_st] in X |- *. exact X.
          destruct STM as [-> ->]. exact X.
        -- destruct GC as (EF & EST & DY & L2 & C8' & ELB & ECR & FRESH & EW12). subst fbR.
          assert (EstF : stF = L5.BDyn 8 gq). { subst stF. rewrite EST, C8'. reflexivity. }
          split. exact OB6. split. exact OL6. unfold L5.bo_dyn. cbn [L5.bo_fb].
          split. exact DY. split. exact L2. split. exact C8'. split. exact EstF. split. exact ELB. split. exact ECR.
          destruct FRESH as (FB1 & FB2 & FB3 & FB4 & FB5).
          assert (GQF : gq + 64 <= F \/ F + 128 <= gq). { pose proof (FB3 (F, 1, sp - 160 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as X. cbn [fst snd ff_addr ff_class] in X. change (ff_bytes 1) with 128 in X. clear - X; lia. }
          pose proof FB1 as (Fq0 & Fq1 & Fq2 & Fq3 & Fq4 & Fq5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Fq5.
          split. { split. exact FB1. split. exact FB2. split. { eapply fframes_apart_incl. exact FB3. intros g0 Hg. apply in_or_app. apply in_app_or in Hg. destruct Hg as [Hg|Hg]. left; right; exact Hg. right; exact Hg. }
                   split. { eapply L5.defined_grows. exact MGM6. eapply L5.defined_grows. exact MGM5. exact FB4. }
                   destruct FB5 as [SZq SPq]. split. 2:{ intros X. exfalso. apply X. reflexivity. }
                   intros j Hj. unfold byte_at.
                   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
                   assert (SHJ : SB <= S gq + j /\ S gq + j + 1 <= 17594333495296 /\ (S gq + j + 1 <= F / 8 + SB \/ F / 8 + SB + 16 <= S gq + j) /\ (S gq + j + 1 <= gq \/ gq + 64 <= S gq + j)).
                   { unfold S. clear - Hj Fq0 Fq4 Fq5 GQF F8 SLO SPR. unfold SB in *. lia. }
                   rewrite FRM6. 2: clear - SHJ; unfold SB in *; lia. 2:{ subst W7; cbn beta. clear - SHJ FAPP' FLAPP. unfold SB in *. lia. }
                   rewrite FRM5. apply SZq. exact Hj. clear - SHJ; unfold SB in *; lia.
                   intros Wa. apply WD in Wa. subst d. rewrite EST in Wa. cbn [L5.bo_data L5.bo_st] in Wa. clear - SHJ Wa OAPP SLO SPR L2. unfold SB in *. lia. }
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          apply ahpres_of. 2: exact SDEF6. 2: exact D06.
          apply E06. 2:{ intros a Hc Ho. rewrite EW12. exact Ho. }
          intros a Hc Ho. split. { intros X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact X. }
          intros X. subst d. rewrite EST in X. cbn [L5.bo_data L5.bo_st] in X.
          apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp 4656 gq 64 a HH SPT FB1 FB2).
          eapply fframes_apart_incl. exact FB3. intros g0 Hg; apply in_or_app; left; right; exact Hg. clear - X L2 C8'; lia. exact Hc.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3.
        eapply L5LZ.model_rt_trans. exact RT4. eapply L5LZ.model_rt_trans. exact RT5. exact RT6.
      * exact IA4.
      * exact AM6.
      * intros x Hx. apply LKI2. apply LKI4. exact Hx.
      * exact HH6.
Qed.

End WithIface.
End SCFG_1.
End L5AADD.

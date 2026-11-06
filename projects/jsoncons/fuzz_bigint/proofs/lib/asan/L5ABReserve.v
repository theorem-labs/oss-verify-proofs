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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun As0_code_8f368_90368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ABReserveP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ARSV.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5ARSVP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 880640 /\ L5.u64_at RSEGS MV (0 + 908088) 2147450880 /\ L5.u32_at RSEGS MV (0 + 908096) 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG (0 + 908088) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG (0 + 908096) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

Theorem reserve_ok : areserve_spec L ar HI -> reserve_spec L ar HI.
Proof.
  intros ARS fx R M model K LB FF LK cr A o n sp r b HH AM HK G10 G11 Hn CAP CR G1 RA G2 A32 G4 STK ROOM RS OB AOB SZ KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487280 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp RESERVE_SCR HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap] in *.
  assert (C1624 : exists c16 c24, L5.u64_at RSEGS M (o + 16) c16 /\ L5.u64_at RSEGS M (o + 24) c24 /\ 0 <= c16 < 2 ^ 64 /\ 0 <= c24 < 2 ^ 64 /\
            match sto with L5.BInl v0 v1 => c16 = v0 /\ c24 = v1 /\ Z.testbit fb 0 = false | L5.BDyn cap q => c16 = cap /\ c24 = q /\ Z.testbit fb 0 = true end).
  { destruct sto as [v0 v1|cap q]. destruct OST as (B0 & O16 & O24 & Hl & R0 & R1). exists v0, v1. repeat split; try lia; assumption.
    destruct OST as (B0 & O16 & O24 & Hl & Hc & Aq & Qlo & Qhi & _). exists cap, q. repeat split; try lia; assumption. }
  destruct C1624 as (c16 & c24 & O16 & O24 & Hc16 & Hc24 & Ec).
  (* [comment removed for export] *)
  assert (XO : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))). exact Hc. }
  assert (XO0 : L5.u8_at RSEGS MV o fb). { apply (proj2 (u8_at_vis H M o fb ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact O0. }
  assert (OZ : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OW : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (W112 : L5.writable RSEGS MV (sp - 112) 112).
  { apply (proj2 (writable_vis H M (sp - 112) 112 (VIS (sp - 112) 112 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  set (VA := fun j : nat => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => fb | 36%nat => Z.of_nat len | 37%nat => c16 | 38%nat => c24 | _ => 0 end).
  (* [comment removed for export] *)
  assert (NOOP : forall fx1 R1 M1v (ks : list nat),
            mem_grows MV M1v -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp - 112 + 112) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) ->
            msteps RSEGS (st fx R RESERVE MV) (st fx1 R1 0x8fdfc M1v) -> (forall x, In x ks -> getr R1 (reg x) = getr R (reg x)) ->
            incl (1%nat :: cs_all) ks -> (Z.testbit fb 0 = true \/ n <= 2) ->
            srealizes RSEGS SCFG (cfg (fx:=fx) R RESERVE M model) K).
  { intros fx1 R1 M1v ks MG1 FZ1 MS1 KS1 KSI HG.
    assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
    pose proof (ret_to fx1 R1 M1v 0x8fdfc W_8fdfc r F_8fdfc eq_refl D_8fdfc ltac:(rewrite (KS1 1%nat (KSI _ (or_introl eq_refl))), (U_to R 1), UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ MS1 RET) as MS2. clear MS1 RET.
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R RESERVE R1 r M1v (fun a => sp - 112 <= a < sp) K HH AM MS2 MG1).
    { intros a Ha Hna. apply FZ1. exact Ha. clear - Hna; lia. }
    { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    apply (KONT fx1 R1 M1 model1 Same LB cr LK A).
    - split. { apply preserved_by_index. intros k Hk. apply KS1. apply KSI. right. exact Hk. }
      cbn [reserve_post]. split. exact HG. split. reflexivity. split. reflexivity.
      split. { eapply (L5C.big_at_agree RSEGS M M1). intros j Hj. apply FRM1. clear - Hj OR; lia. clear - Hj OR SLO SPT; lia. clear - OR; lia. clear - OR; lia. exact OB. }
      apply ahpres_of.
      + apply (ek_piece L ar LB FF sp RESERVE_SCR [] M M1 _ FRM1). intros a Ha Hc _ X.
        destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp RESERVE_SCR a HH SPT Hc) as [Y|Y].
        unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
      + eapply astk_defined. eapply astk_grows. exact STK. exact MGM1. clear; lia. clear; lia.
      + apply dk_grows. exact MGM1.
    - exact RT1.
    - apply incl_refl.
    - exact AM1.
    - apply incl_refl.
    - exact HH1. }
  destruct sto as [v0 v1|cap q].
  2:{ (* [comment removed for export] *)
      destruct Ec as (-> & -> & B0).
      pose proof (rsvD_conc fx R MV VA) as P. cbn beta iota delta [VA] in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | sc]) | (apply CAP; exact B0) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & dFR & dFZ & (dMS & dKS & _)).
      apply (NOOP fx1 R1 M1v KS_rsvD MG1 dFZ dMS dKS). vm_compute; intros k Hk; exact Hk || (cbn in Hk |- *; tauto). left; exact B0. }
  destruct Ec as (-> & -> & B0). destruct OST as (_ & _ & _ & Hl2 & Rv0 & Rv1).
  destruct (Z_lt_le_dec 2 n) as [GROW|SMALL].
  2:{ pose proof (rsvI_conc fx R MV VA) as P. cbn beta iota delta [VA] in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | sc]) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & iFR & iFZ & (iMS & iKS & _)).
      apply (NOOP fx1 R1 M1v KS_rsvI MG1 iFZ iMS iKS). vm_compute; intros k Hk; exact Hk || (cbn in Hk |- *; tauto). right; exact SMALL. }
  (* [comment removed for export] *)
  assert (RUN : 8 <= round_up n <= n + 8 /\ round_up n <= 8388616).
  { unfold round_up. clear - Hn GROW. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (rsvM_conc fx R MV VA) as P. cbn beta iota delta [VA] in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | sc]) ]).
  destruct P as (fx1 & R1 & M1v & MG1 & mFR & mFZ & (mMS & mKS & mR1 & mR2 & mR8 & mR9 & mR10 & mR11 & mR12 & mR18 & mR19 & mR20 & mR21 & mR22 & mR23 & mR24 & mR25 & mR26 & mR27 & mB_V33nat & mQ_V2nat & mQ_V2nat_1 & mQ_V2nat_2 & mQ_V2nat_3 & mQ_V2nat_4 & mQ_V2nat_5 & mQ_V2nat_6 & mQ_V2nat_7 & mQ_V2nat_8 & mQ_V2nat_9 & mQ_V2nat_10 & mQ_V2nat_11 & mQ_V2nat_12)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R RESERVE R1 0x5e570 M1v (fun a => sp - 112 <= a < sp \/ o <= a < o + 1) K HH AM mMS MG1).
  { intros a Ha Hna. apply mFZ. exact Ha. clear - Hna; lia. clear - Hna; lia. }
  { intros a Ha [Wa|Wa]. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
    split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp RESERVE_SCR). { eapply astk_grows. exact STK. exact MGM1. }
  (* [comment removed for export] *)
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  assert (U2 : bv_unsigned (getr R1 2%bv) = sp - 112). { rewrite r2, mR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (MS fx1 R1 M1 model1 LB FF LK cr A (o + 8) 0 24 K); clear MS.
  { split. exact HH1. split. exact (proj1 AM1). split. exact (proj2 AM1).
    split. rewrite r10. exact mR10. split. rewrite r12. exact mR12. split. clear; lia.
    split. rewrite r4. rk. split. rewrite r1, mR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U2. apply (astack_ok_of_astk L ar C LY M M1 sp RESERVE_SCR 112 2560 STK MGM1). clear; lia. clear; lia.
             unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
             clear - A16. replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    split. { (* [comment removed for export] *)
             intros a Ha. left. unfold byte_at, S. rewrite FRM1. unfold shadow_zero, byte_at, S in SZ.
             replace (a / 8 + SB) with (o / 8 + SB + (a / 8 - o / 8)) by (clear; lia). apply SZ.
             clear - Ha OR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             clear - Ha OR; unfold SB; lia. clear - Ha OR OBIG SLO SPT; unfold SB; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { intros i Hi. rewrite U2. apply (obj_client L ar LB FF _ _ o 32 _ AOB). clear - Hi; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M1 (o + 8) 24). eapply L5.defined_grows. exact MGM1. eapply L5.defined_sub. exact ODEF.
             clear; lia. clear; lia. clear - OR; lia. clear - OR; lia. exact Hi. exact Hm. }
    split. exact HK. apply (app_rng_aobj L ar C HI HIok LB FF LK cr A M1 _ o 32 (o + 8) 24 HH1 AOB); clear; lia. }
  { rewrite r11. exact mR11. }
  (* [comment removed for export] *)
  intros R2 M2 model2 pR10 RP2 ZB PRES2 SDEF2 RT2 MI2 HH2. rewrite U2 in PRES2, SDEF2. rewrite r1, mR1.
  assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
  assert (ASTK2 : astk ar M2 sp RESERVE_SCR).
  { apply (astk_after_eq L ar C HI HIok LB FF LK cr A M1 M1 M2 _ sp _ (sp - 112) 2560 HH1 ASTK1 (mem_grows_refl M1)).
    intros a Ha Hs Hns. apply PRES2. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs OR; lia. exact SDEF2.
    unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M2 model2 HH2) as (HOFF2 & VIS2 & _).
  pose proof (statics_vis LB FF LK cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
  set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (W112b : L5.writable RSEGS MV2 (sp - 112) 112).
  { apply (proj2 (writable_vis H2 M2 (sp - 112) 112 (VIS2 (sp - 112) 112 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M2 sp). exact ASTK2. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (rsvB_conc fx1 R2 MV2 VA) as P. cbn beta iota delta [VA] in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12)).
  apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M2 model2 fx1 fx3 R2 0x8fce8 R3 ARESERVE M3v K HH2 (conj Hh2 MI2) bMS MG3 bFZ).
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 EQ3. pose proof (mem_eq_of_agree M2 M3 EQ3) as EM. subst M3.
  (* [comment removed for export] *)
  assert (Z24 : L5KA.zeros_at M2 (o + 8) 24).
  { intros i Hi. destruct (ZB i Hi) as (v & -> & Bv). unfold byte_at in Bv. rewrite Bv. reflexivity. }
  (* [comment removed for export] *)
  apply (ARS fx3 R3 M2 model3 K LB FF LK cr A o n (sp - 112) 0x8fcf8 HH3 AM3 HK).
  - rewrite r10. exact bR10.
  - rewrite r11. exact bR11.
  - clear - Hn GROW; lia.
  - apply CR. exact B0. clear - GROW; lia.
  - rewrite r1. exact bR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. rk.
  - clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). rewrite r4. rk.
  - apply (astk_sub ar M2 M2 sp RESERVE_SCR 112 ARESERVE_SCR ASTK2 (mem_grows_refl M2)). clear; lia. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
    unfold RESERVE_SCR; clear; lia. clear - A16. replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
  - exact ROOM.
  - eapply ffrs_le. exact RS. clear; lia.
  - exact AOB.
  - (* [comment removed for export] *)
    intros j Hj. unfold byte_at, S. rewrite PRES2. rewrite FRM1. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj.
    clear - Hj OR; unfold SB; lia. clear - Hj OR OBIG SLO SPT; unfold SB; lia. clear - Hj OR; unfold SB; lia.
    replace (o / 8 + SB + j) with (o / 8 + SB + j) by reflexivity. apply (aclient_narrow L ar LB FF sp RESERVE_SCR). apply OCLSH. exact Hj.
    clear - Hj OR SLO SPT; unfold SB; lia. clear - Hj OR OBIG; unfold SB; lia.
  - apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z24. clear; lia. clear; lia. clear - OR; lia. clear - OR; lia.
  - apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z24. clear; lia. clear; lia. clear - OR; lia. clear - OR; lia.
  - (* [comment removed for export] *)
    intros fx4 R4 M4 model4 LK4 A4 q RP4 (BRq & BAq & FAq & DEFq & SHBq) [E16 E24] PRES4 RT4 IA4 AM4 LKI4 HH4.
    pose proof BRq as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
    set (LB4 := (q, 8 * round_up n) :: LB) in *.
    assert (ASTK4 : astk ar M4 sp RESERVE_SCR).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M2 M2 M4 _ sp _ (sp - 112) ARESERVE_SCR [(o + 16, 16)] HH3 ASTK2 (mem_grows_refl M2) PRES4).
      unfold RESERVE_SCR; clear; lia. clear; lia. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB4 FF LK4 _ A4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
    pose proof (statics_vis LB4 FF LK4 _ A4 M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4).
    set (H4 := ahid A4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
    pose proof (aobj_facts L ar C HI LY HIok LB4 FF LK4 _ A4 M4 model4 o 32 0 0 HH4 AOB ltac:(clear; lia) ltac:(reflexivity))
      as (_ & _ & ODEF4 & OVIS4 & OVSH4 & _). change (32 / 8) with 4 in OVSH4.
    assert (W112d : L5.writable RSEGS MV4 (sp - 112) 112).
    { apply (proj2 (writable_vis H4 M4 (sp - 112) 112 (VIS4 (sp - 112) 112 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M4 sp). exact ASTK4. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
    assert (OW4 : L5.writable RSEGS MV4 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H4 M4 o 32 OVIS4)). exact ODEF4. clear - OR; lia. clear - OR; lia. }
    (* [comment removed for export] *)
    assert (DDEC : forall a, (o + 8 <= a < o + 8 + 24) \/ ~ (o + 8 <= a < o + 8 + 24)). { intros a. destruct (rng_dec a (o + 8) (o + 8 + 24)); tauto. }
    assert (E14 : ek L ar LB FF (sp - 112) ARESERVE_SCR [(o + 8, 24)] M1 M4).
    { eapply ek_trans. { apply (ek_mem L ar LB FF (sp - 112) ARESERVE_SCR (sp - 112) 2560 (fun a => o + 8 <= a < o + 8 + 24) [(o + 8, 24)] M1 M2 PRES2).
        unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. intros a _ Ho X. apply (Ho (o + 8, 24)). left; reflexivity. exact X. }
      apply (ek_callee L ar LB [] FF [] (sp - 112) ARESERVE_SCR (sp - 112) ARESERVE_SCR [(o + 8, 24)] [(o + 16, 16)] M2 M4 PRES4).
      clear; lia. clear; lia. intros a _ Ho rr [<-|[]] X. apply (Ho (o + 8, 24)). left; reflexivity. unfold L5.in_rng in X |- *; cbn [fst snd] in X |- *. clear - X; lia. }
    assert (AG14 : forall a, (sp - 112 <= a < sp \/ o <= a < o + 1 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> MV4 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ra.
      assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in Ra; lia).
      assert (Ca : aclient L ar LB FF (sp - 112) ARESERVE_SCR a).
      { destruct Ra as [Ra|[Ra|Ra]]. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
        apply (obj_client L ar LB FF _ _ o 32 a AOB). clear - Ra; lia.
        apply (aclient_narrow L ar LB FF sp RESERVE_SCR). replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ra; lia.
        clear - Ra OR SLO SPT; unfold SB, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in *; lia. }
      unfold MV4. rewrite (mrestrict_visible H4 M4).
      2:{ destruct Ra as [Ra|[Ra|Ra]]. replace a with ((sp - 112) + (a - (sp - 112))) by (clear; lia). apply (VIS4 (sp - 112) 112). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          replace a with (o + (a - o)) by (clear; lia). apply (OVIS4 (a - o)). clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH4 (a - (o / 8 + SB))). clear - Ra; lia. }
      rewrite (E14 a). 2:{ split. exact Ha. split. exact Ca. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ra OR OBIG SLO SPT; unfold SB in *; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible.
      destruct Ra as [Ra|[Ra|Ra]]. replace a with ((sp - 112) + (a - (sp - 112))) by (clear; lia). apply (VIS (sp - 112) 112). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      replace a with (o + (a - o)) by (clear; lia). apply (OVIS (a - o)). clear - Ra; lia.
      replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH (a - (o / 8 + SB))). clear - Ra; lia. }
    assert (XC4 : forall a v, sp - 104 <= a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV4 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AG14. clear - Ha Hj; lia. clear - Ha SPR; lia. clear - Ha SPR; lia. }
    assert (OB4 : L5.u8_at RSEGS MV4 o (4 * (fb / 4) + 1)). { eapply L5C.u8_at_agree. 4: exact mB_V33nat. intros j Hj. apply AG14. clear - Hj; lia. clear - OR; lia. clear - OR; lia. }
    assert (OZ4 : L5KA.zeros_at MV4 (o / 8 + SB) 4).
    { eapply L5KA.zeros_at_agree1. 2:{ eapply L5KA.zeros_at_agree1. 2: exact OZ. intros j Hj. apply mFZ. clear - Hj OR; unfold SB in *; lia. clear - Hj OR SLO SPT; unfold SB in *; lia. clear - Hj OR OBIG; unfold SB in *; lia. }
      intros j Hj. apply AG14. clear - Hj; lia. }
    assert (O24q : L5.u64_at RSEGS MV4 (o + 24) q).
    { apply (proj2 (u64_at_vis H4 M4 (o + 24) q ltac:(eapply avis_sub; [exact OVIS4 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact E24. }
    assert (QV : avis H4 q 16). { apply (VBLK4 q (8 * round_up n) q 16). left; reflexivity. clear; lia. clear - RUN; lia. }
    assert (QW : L5.writable RSEGS MV4 q 16).
    { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H4 M4 q 16 QV)). eapply L5.defined_sub. exact DEFq. clear; lia. clear - RUN; lia. clear - Q0; lia. clear - Q5 RUN; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Q8 : q / 8 * 8 = q /\ q mod 8 = 0) by (clear - Q2; lia).
    assert (QSH : SB <= q / 8 + SB /\ (q + 8 * round_up n - 1) / 8 + SB < 0x10007fff8000 /\ (q + 8 * round_up n - 1) / 8 = q / 8 + round_up n - 1) by (clear - Q0 Q5 RUN Q8; unfold SB; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (QZ : L5KA.zeros_at MV4 (q / 8 + SB) 2).
    assert (QZV : avis H4 (q / 8 + SB) 2).
    { apply (VBSH4 q (8 * round_up n)). left; reflexivity. intros i Hi. unfold in_shadow_of, S. clear - Hi QSH RUN. destruct QSH as (X1 & X2 & X3). rewrite X3. lia. }
    { apply (proj2 (zeros_at_vis H4 M4 _ 2 QZV)).
      destruct SHBq as [SZq _]. intros i Hi. unfold shadow_zero, byte_at, S in SZq. apply SZq. replace (8 * round_up n / 8) with (round_up n). clear - Hi RUN; lia.
      clear; rewrite Z.mul_comm, Z_div_mult; [reflexivity | lia]. }
    assert (OQ : o + 32 <= q \/ q + 16 <= o).
    { destruct AOB as (g & Hg & X1 & X2 & _). specialize (FAq g ltac:(apply in_or_app; left; exact Hg)). clear - FAq X1 X2 RUN. lia. }
    (* [comment removed for export] *)
    pose proof (rsvC_conc fx4 R4 MV4 (fun j : nat => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => fb | 36%nat => Z.of_nat len | 37%nat => v0 | 38%nat => v1
                  | 39%nat => 4 * (fb / 4) + 1 | 40%nat => q | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18 | 45%nat => U R 19 | 46%nat => U R 20
                  | 47%nat => U R 21 | 48%nat => U R 22 | 49%nat => U R 23 | 50%nat => U R 24 | 51%nat => U R 25 | 52%nat => U R 26 | 53%nat => U R 27 | 54%nat => U R4 1 | _ => 0 end)) as P.
    cbn beta iota in P.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FBR : 0 <= 4 * (fb / 4) + 1 < 2 ^ 64 /\ 0 <= 4 * (fb / 4) + 1 <= 255) by (clear - Hfb; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XC4; [clear; lia | unfold U; sc]) ]).
    destruct P as (fx5 & R5 & M5v & MG5 & cFR & cFZ & (cMS & cKS & cR1 & cR2 & cR8 & cR9 & cR10 & cR11 & cR18 & cR19 & cR20 & cR21 & cR22 & cR23 & cR24 & cR25 & cR26 & cR27 & cQ_V40nat & cQ_V40nat_1 & cB_V33nat & cQ_V33nat)).
    assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
    pose proof (ret_to fx5 R5 M5v 0x8fdfc W_8fdfc r F_8fdfc eq_refl D_8fdfc ltac:(rewrite cR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ cMS RET) as MS6. clear cMS RET.
    apply (apiece L ar C HI LY HIok LB4 FF LK4 _ A4 M4 model4 fx4 fx5 R4 0x8fcf8 R5 r M5v (fun a => sp - 112 <= a < sp \/ o <= a < o + 16 \/ q <= a < q + 16) K HH4 AM4 MS6 MG5).
    { intros a Ha Hna. apply cFZ. exact Ha. all: clear - Hna; lia. }
    { intros a Ha [Wa|[Wa|Wa]]. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
      split. apply (obj_client L ar LB4 FF _ _ o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia.
      split. apply (block_client L ar LB4 FF 0 0 q (8 * round_up n)). left; reflexivity. clear - Wa RUN; lia. clear - Wa Q1 RUN; lia. }
    intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
    assert (XV5 : forall a m v, avis H4 a m -> 0 <= a -> a + 8 <= 2 ^ 64 -> 8 <= m -> (L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v) /\ (L5.u8_at RSEGS M5v a v -> L5.u8_at RSEGS M5 a v)).
    { intros a m v Va Ha H8 Hm. split; intros Hc.
      apply (proj1 (u64_at_vis H4 M5 a v ltac:(eapply avis_sub; [exact Va | clear; lia | clear - Hm; lia]) Ha H8)). unfold H4. rewrite VIS5. exact Hc.
      apply (proj1 (u8_at_vis H4 M5 a v ltac:(eapply avis_sub; [exact Va | clear; lia | clear - Hm; lia]) Ha ltac:(clear - H8; lia))). unfold H4. rewrite VIS5. exact Hc. }
    apply (KONT fx5 R5 M5 model5 (Grown q (round_up n)) LB4 (adebit L cr (8 * round_up n)) LK4 A4).
    + cbn [reserve_post]. split.
      { apply preserved_by_index. intros k Hk. cbn in Hk.
        destruct Hk as [<-|Hk]. { rewrite cR2. rewrite <- r2, G2. reflexivity. }
        destruct Hk as [<-|Hk]. { rk. } destruct Hk as [<-|Hk]. { rk. }
        repeat (destruct Hk as [<-|Hk]; [first [rewrite cR8 | rewrite cR9 | rewrite cR18 | rewrite cR19 | rewrite cR20 | rewrite cR21 | rewrite cR22 | rewrite cR23
                                               | rewrite cR24 | rewrite cR25 | rewrite cR26 | rewrite cR27]; symmetry; apply U_to |]). destruct Hk. }
      split. exact B0. split. clear - GROW; lia. split. reflexivity. split. reflexivity. split. reflexivity.
      split. { split. exact BRq. split. exact BAq. split. exact FAq. split. eapply L5.defined_grows. exact MGM5. exact DEFq.
               destruct SHBq as [SZq SPq]. split. 2:{ intros X. exfalso. apply X. clear. rewrite Z.mul_comm. apply Z_mod_mult. }
               intros j Hj. unfold byte_at. rewrite FRM5. apply SZq. exact Hj. unfold S; clear - Hj QSH RUN; unfold SB in *. 
               replace (8 * round_up n / 8) with (round_up n) in Hj by (clear; rewrite Z.mul_comm, Z_div_mult; [reflexivity | lia]). lia.
               replace (8 * round_up n / 8) with (round_up n) in Hj by (clear; rewrite Z.mul_comm, Z_div_mult; [reflexivity | lia]).
               unfold S. clear - Hj QSH RUN SPR OR OBIG Q5 Q0 SLO SPT. unfold SB in *. lia. }
      split. { exists v0, v1. split. reflexivity. split. apply (proj1 (XV5 q 16 v0 QV ltac:(clear - Q0; lia) ltac:(clear - Q5 RUN; lia) ltac:(clear; lia))). exact cQ_V40nat_1.
               apply (proj1 (XV5 (q + 8) 8 v1 ltac:(eapply avis_sub; [exact QV | clear; lia | clear; lia]) ltac:(clear - Q0; lia) ltac:(clear - Q5 RUN; lia) ltac:(clear; lia))). exact cQ_V40nat. }
      pose proof (lor1_facts fb Hfb) as [LR LB1].
      split. { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
               split. { rewrite <- (reserve_flags fb Hfb). apply (proj2 (XV5 o 32 _ OVIS4 ltac:(clear - OR; lia) ltac:(clear - OR; lia) ltac:(clear; lia))). exact cB_V33nat. }
               split. exact LR.
               split. { apply (proj1 (XV5 (o + 8) 24 _ ltac:(eapply avis_sub; [exact OVIS4 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia) ltac:(clear; lia))). exact cQ_V33nat. }
               split. exact LB1.
               split. { eapply L5C.u64_at_agree. 4: exact E16. intros j Hj. apply FRM5. clear - Hj OR; lia. clear - Hj OQ SLO SPT OR; lia. clear - OR; lia. clear - OR; lia. }
               split. { eapply L5C.u64_at_agree. 4: exact E24. intros j Hj. apply FRM5. clear - Hj OR; lia. clear - Hj OQ SLO SPT OR; lia. clear - OR; lia. clear - OR; lia. }
               split. clear - Hl2 RUN; lia. split. clear - RUN Hn; lia. split. exact (proj2 Q8). split. exact Q0. split. clear - Q4 SPT; lia.
               apply hull_apart_of. exact Q1. }
      apply ahpres_of.
      * eapply ek_trans. { apply (ek_piece L ar LB FF sp RESERVE_SCR [(o, 32)] M M1 _ FRM1). intros a Ha Hc Ho [X|X].
          destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp RESERVE_SCR a HH SPT Hc) as [Y|Y].
          unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
          apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]; clear - X; lia. }
        eapply ek_trans. { apply (ek_mono L ar LB FF sp RESERVE_SCR (sp - 112) ARESERVE_SCR [(o, 32)] [(o + 8, 24)] M1 M4 E14). unfold RESERVE_SCR; clear; intros x Hx; lia.
          intros a Ho rr [<-|[]] X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng in X |- *; cbn [fst snd] in X |- *; clear - X; lia. }
        apply (ek_piece L ar LB FF sp RESERVE_SCR [(o, 32)] M4 M5 _ FRM5). intros a Ha Hc Ho [X|[X|X]].
        -- destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp RESERVE_SCR a HH SPT Hc) as [Y|Y].
          unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
        -- apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]; clear - X; lia.
        -- refine (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp RESERVE_SCR q (8 * round_up n) a HH SPT BRq BAq _ _ Hc).
          eapply fframes_apart_incl. exact FAq. intros g Hg; apply in_or_app; left; exact Hg. clear - X RUN; lia.
      * eapply astk_defined. eapply astk_grows. exact ASTK4. exact MGM5. clear; lia. clear; lia.
      * eapply dk_trans. apply dk_grows. exact MGM1.
        eapply dk_trans. { apply (dk_mem L ar LB FF sp RESERVE_SCR (sp - 112) 2560 (fun a => o + 8 <= a < o + 8 + 24) M1 M2 PRES2 SDEF2).
          intros a Ha. destruct (ZB (a - (o + 8)) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (o + 8 + (a - (o + 8))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
          exact DDEC. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
        eapply dk_trans. apply (dk_callee L ar LB [] FF [] sp RESERVE_SCR (sp - 112) ARESERVE_SCR [(o + 16, 16)] M2 M4 PRES4). unfold RESERVE_SCR; clear; lia. clear; lia.
        apply dk_grows. exact MGM5.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4. exact RT5.
    + exact IA4.
    + exact AM5.
    + exact LKI4.
    + exact HH5.
Qed.

End WithIface.
End SCFG_1.
End L5ARSV.

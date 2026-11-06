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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5AChk L5AChkAs0 L5AStrInitP As0_code_8e368_8f368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASTR.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5ASTRP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Lemma SCR_EQ : STRINIT_SCR = 4176. Proof. reflexivity. Qed.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma str_cap_23 : str_cap 23 = 26. Proof. reflexivity. Qed.
Lemma str_cap_ge n : 24 <= n -> str_cap n = 8 * (n / 8) + 8.
Proof.
  intros Hn. unfold str_cap.
  assert (E : Z.lor n 7 = 8 * (n / 8) + 7).
  { pose proof (Z.add_lor_land n 7) as A. change 7 with (Z.ones 3) in A at 2. rewrite Z.land_ones in A by lia. change (2 ^ 3) with 8 in A.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite E. replace (8 * (n / 8) + 7 =? 23) with false. lia. symmetry. apply Z.eqb_neq. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma aacc_of_block M u m p n : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + n <= u + m -> aacc M p n.
Proof.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  intros [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
  - left. rewrite E. apply SZ. lia.
  - right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = m / 8) by lia.
    split. rewrite E, G. apply SP. exact NZ. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Lemma tail_run fx R MV (sp a r : Z) (v44 v45 v46 v47 v48 v49 v50 : Z) :
  getr R (reg 10) = Z_to_bv 64 a -> getr R (reg 11) = Z_to_bv 64 (a / 8 + 2147450880) -> getr R (reg 2) = Z_to_bv 64 (sp - 64) ->
  140735332487232 <= sp <= 140737488355328 -> aligned sp 16 -> L5.writable RSEGS MV (sp - 64) 64 ->
  L5.img_clear MV 860160 880640 -> L5.u64_at RSEGS MV 908088 2147450880 -> L5.u32_at RSEGS MV 908096 1 ->
  L5.u64_at RSEGS MV (sp - 8) v44 -> L5.u64_at RSEGS MV (sp - 16) v45 -> L5.u64_at RSEGS MV (sp - 24) v46 -> L5.u64_at RSEGS MV (sp - 32) v47 ->
  L5.u64_at RSEGS MV (sp - 40) v48 -> L5.u64_at RSEGS MV (sp - 48) v49 -> L5.u64_at RSEGS MV (sp - 56) v50 ->
  0 <= v44 < 2 ^ 64 -> 0 <= v45 < 2 ^ 64 -> 0 <= v46 < 2 ^ 64 -> 0 <= v47 < 2 ^ 64 -> 0 <= v48 < 2 ^ 64 -> 0 <= v49 < 2 ^ 64 -> 0 <= v50 < 2 ^ 64 ->
  v44 = r -> L5.ra_ok r ->
  4096 <= a <= 140737488355327 -> L5.writable RSEGS MV a 1 -> (sp - 64 + 64 <= a \/ a + 1 <= sp - 64) -> aacc MV a 1 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x8e5c0 MV) (st fx' R' r M') /\ mem_grows MV M'
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (a <= i < a + 1) -> M' (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    /\ (forall x, In x KS_siT2 -> x <> 11%nat -> x <> 12%nat -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 v44 /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = Z_to_bv 64 v45 /\ getr R' (reg 9) = Z_to_bv 64 v46
    /\ getr R' (reg 18) = Z_to_bv 64 v47 /\ getr R' (reg 19) = Z_to_bv 64 v48 /\ getr R' (reg 20) = Z_to_bv 64 v49 /\ getr R' (reg 21) = Z_to_bv 64 v50
    /\ L5.u8_at RSEGS M' a 0.
Proof.
  intros G10 G11 G2 HV2 ALS W64 IMGC CSB CUAR C8 C16 C24 C32 C40 C48 C56 R44 R45 R46 R47 R48 R49 R50 Er RA HVA WA FRA ACC.
  destruct (L5ACHK0.chk_8e26c fx R MV a ltac:(unfold S, SB; exact G11) G10 ltac:(clear - HVA; lia) ACC) as (R1 & MS1 & K1).
  pose proof (siT2_conc fx R1 MV (fun j => match j with 2%nat => sp | 38%nat => a | 43%nat => U R1 1 | 44%nat => v44 | 45%nat => v45 | 46%nat => v46 | 47%nat => v47
                | 48%nat => v48 | 49%nat => v49 | 50%nat => v50 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | assumption | (rewrite K1; [assumption | clear; lia | clear; lia | clear; lia]) | sc]).
  destruct P as (fx2 & R2 & M2 & MG2 & tFR & tFZ & (tMS & tKS & tR1 & tR2 & tR8 & tR9 & tR18 & tR19 & tR20 & tR21 & tB)).
  pose proof (ret_to fx2 R2 M2 0x8e5ec W_8e5ec r F_8e5ec eq_refl D_8e5ec ltac:(rewrite tR1, Er; reflexivity) (proj1 RA) (proj2 RA)) as RET.
  exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact tMS. exact RET. }
  split. exact MG2. split. { intros i Hi Hn. apply tFZ. exact Hi. clear - Hn; lia. }
  split. { intros x Hx N1 N2. rewrite (tKS x Hx). apply K1. revert Hx. clear. intros Hx. unfold KS_siT2 in Hx. cbn in Hx. lia. exact N1. exact N2. }
  repeat split; assumption.
Qed.

Theorem strinit_ok : opnew_spec L ar HI -> strinit_spec L ar HI.
Proof.
  intros NEW fx R M model K LB FF LK cr A o s n sp r cs HH AM HK G10 G11 G12 Hn CR G1 RA G2 A32 G4 STK AOB SZ RDN SRCB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491344 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 24 sp 4176 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (24 / 8) with 3 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & _).
  assert (OAPP : o + 24 <= 2147446784 \/ 17594333495296 <= o).
  { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (WF g0 Hg) as (Y1 & Y2 & _).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP, Y2. clear - X1 X2 Y1 Y2 FSAPP. lia. }
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W64 : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  assert (OZv : L5KA.zeros_at MV (o / 8 + 2147450880) 3). { apply (proj2 (zeros_at_vis H M _ 3 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 24). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 24 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact (proj1 (proj2 (proj2 (proj2 OR)))).
  assert (HV2 : 140735332487232 <= sp <= 140737488355328) by (clear - SPR; lia). assert (HVO : 4096 <= o <= 140737488355304) by (clear - OR; lia).
  assert (FRO : sp - 64 + 64 <= o \/ o + 24 <= sp - 64) by (clear - OR SLO; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (ODSJ : o + 24 <= o / 8 + 2147450880 \/ o / 8 + 2147450880 + 3 <= o) by (clear - OAPP OR; lia).
  assert (O8 : (o / 8) * 8 = o) by (clear - ALO; unfold aligned in ALO; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  (* [comment removed for export] *)
  assert (EKP : forall M0 M1 (P : Z -> Prop), (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
            (forall a, P a -> sp - 64 <= a < sp \/ o <= a < o + 24) -> ek L ar LB FF sp 4176 [(o, 24)] M0 M1).
  { intros M0 M1 P FRM HP. apply (ek_piece L ar LB FF sp 4176 [(o, 24)] M0 M1 P FRM). intros a Ha Hc Ho X. destruct (HP a X) as [Y|Y].
    - destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4176 a HH SPT Hc) as [Z1|Z1]. clear - Y Z1; lia. clear - Y Z1 SLO; lia.
    - apply (Ho (o, 24)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Y. }
  destruct (Z.eq_dec n 0) as [N0|N0].
  { (* [comment removed for export] *)
    subst n.
    pose proof (siZ_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => U R 11 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR2 & aR8 & aR9 & aR10 & aR11 & aR18 & aR19 & aR21 & aB0 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    destruct (tail_run fx1 R1 M1v sp (o + 1) r (U R 1) (U R 8) (U R 9) (U R 18) (U R 19) (U R 20) (U R 21))
      as (fx2 & R2 & M2v & MS2 & MG2 & FZ2 & K2 & tR1 & tR2 & tR8 & tR9 & tR18 & tR19 & tR20 & tR21 & tB).
    all: try (unfold U; assumption). all: try apply UR.
    { eapply L5.writable_grows. exact MG1. exact W64. }
    { intros i Hi. rewrite aFZ. apply IMGC. exact Hi. clear - Hi; lia. clear - Hi SPR; lia. clear - Hi OR; lia. }
    { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros j Hj. apply aFZ. clear - Hj; lia. clear - Hj SPR; lia. clear - Hj OR; lia. }
    { eapply u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros j Hj. apply aFZ. clear - Hj; lia. clear - Hj SPR; lia. clear - Hj OR; lia. }
    { clear - OR; lia. }
    { eapply L5.writable_grows. exact MG1. eapply L5.writable_sub. exact OWv. clear; lia. clear; lia. }
    { clear - FRO; lia. }
    { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      intros b Hb. left. unfold byte_at. replace (S b) with (o / 8 + 2147450880 + 0). rewrite aFZ. apply OZv. clear; lia.
      1-3: clear - OR ODSJ SPR; lia. unfold S, SB. clear - Hb O8. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    set (W1 := fun i => sp - 64 <= i < sp \/ o <= i < o + 2).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx2 R STRINIT R2 r M2v W1 K HH AM (msteps_trans _ _ _ _ aMS MS2) (mem_grows_trans _ _ _ MG1 MG2)).
    { intros i Hi Hni. rewrite FZ2. apply aFZ. exact Hi. all: clear - Hi Hni; subst W1; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W1; cbn beta in Wi. destruct Wi as [Wi|Wi].
      - split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia.
      - split. apply (obj_client L ar LB FF 0 0 o 24 i AOB). clear - Wi; lia. clear - Wi OR; lia. }
    intros M2 model2 HH2 AM2 RT2 AH2 VIS2 MGM2 FRM2 EQ2.
    apply (KONT fx2 R2 M2 model2 LB cr LK A).
    - split.
      { apply preserved_by_index. intros k Hk. cbn in Hk.
        assert (CH : forall k, In k KS_siT2 -> k <> 11%nat -> k <> 12%nat -> In k KS_siZ -> getr R2 (reg k) = getr R (reg k)).
        { intros k' H1 N1 N2 H2. rewrite (K2 k' H1 N1 N2). apply aKS. exact H2. }
        destruct Hk as [<-|Hk]. { rewrite tR2. rewrite <- r2, G2. reflexivity. }
        destruct Hk as [<-|Hk]. { apply CH; [inl | clear; lia | clear; lia | inl]. }
        destruct Hk as [<-|Hk]. { apply CH; [inl | clear; lia | clear; lia | inl]. }
        destruct Hk as [<-|Hk]. { rewrite tR8. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR9. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR18. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR19. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR20. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR21. symmetry. apply U_to. }
        all: repeat (destruct Hk as [<-|Hk]; [apply CH; [inl | clear; lia | clear; lia | inl] |]). destruct Hk. }
      split.
      { intros _. split. reflexivity. split. reflexivity.
        split. { apply (proj1 (u8_at_vis H M2 o 0 ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). replace (mrestrict H M2) with M2v by (symmetry; exact VIS2).
                 eapply L5C.u8_at_agree. 4: exact aB0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FZ2. clear - Hj OR; lia. clear - Hj; lia. }
        split. { intros i Hi. exfalso. clear - Hi; lia. }
        split. { apply (proj1 (u8_at_vis H M2 (o + 1 + 0) 0 ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). replace (mrestrict H M2) with M2v by (symmetry; exact VIS2).
                 replace (o + 1 + 0) with (o + 1) by (clear; lia). exact tB. }
        rewrite SCR_EQ. apply ahpres_of.
        + apply (EKP M M2 W1 FRM2). intros a Wa. subst W1; cbn beta in Wa. clear - Wa; lia.
        + eapply astk_defined. eapply astk_grows. exact STK. exact MGM2. clear; lia. clear; lia.
        + apply dk_grows. exact MGM2. }
      intros X. exfalso. clear - X; lia.
    - exact RT2.
    - apply incl_refl.
    - exact AM2.
    - apply incl_refl.
    - exact HH2. }
  destruct SRCB as [N0'|(bA & bm & INB & BA1 & BA2)]. { exfalso. exact (N0 N0'). }
  pose proof (WB _ INB) as ((BQ0 & BQ1 & BQ2 & BQ3 & BQ4 & BQ5) & BDEF & BSH & _ & BBA & BFA & BFS). cbn [fst snd] in BQ0, BQ1, BQ2, BQ3, BQ4, BQ5, BDEF, BSH, BBA, BFA, BFS.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BQ5. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in BQ1.
  assert (SR : 0 <= s /\ s + n <= 2 ^ 47) by (clear - BQ0 BQ4 BA1 BA2 SPT; lia).
  assert (HVS : 0 <= s < 2 ^ 64) by (clear - SR Hn; lia).
  assert (US11 : U R 11 = s). { apply (U_of R 11 s). rewrite <- r11. exact G11. exact HVS. }
  assert (BO : o + 24 <= bA \/ bA + bm <= o).
  { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (BFA g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [ff_addr ff_class fst snd] in X. clear - X X1 X2 BQ3. lia. }
  assert (ACC : aacc M s n).
  { apply (aacc_of_block M bA bm s n BSH). clear - BQ2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. clear - BQ0; lia. exact BA1. exact BA2. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (Z_le_gt_dec n 22) as [N22|N23].
  { (* [comment removed for export] *)
    assert (HVN : 1 <= n <= 22) by (clear - N0 N22 Hn; lia).
    pose proof (siS_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => U R 11 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR18 & aR19 & aR21 & aB0 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    set (W1 := fun i => sp - 64 <= i < sp \/ o <= i < o + 1).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R STRINIT R1 0x5e7b0 M1v W1 K HH AM aMS MG1).
    { intros i Hi Hni. apply aFZ. exact Hi. all: clear - Hni; subst W1; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W1; cbn beta in Wi. destruct Wi as [Wi|Wi].
      - split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia.
      - split. apply (obj_client L ar LB FF 0 0 o 24 i AOB). clear - Wi; lia. clear - Wi OR; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    (* [comment removed for export] *)
    pose proof (aio_memmove _ _ _ _ _ HIok) as MMV. unfold amemmove_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
    rewrite (aly_segs L C LY), (aly_memmove L C LY), (aly_scr_mem L C LY) in MMV.
    assert (U12 : bv_unsigned (getr R1 2%bv) = sp - 64). { rewrite r2, aR2. apply L5.unsigned_lit. clear - SPR; lia. }
    assert (SA16 : (sp - 64) mod 16 = 0). { clear - A16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    eapply (MMV fx1 R1 M1 model1 LB FF LK cr A (o + 1) s n cs K); clear MMV.
    { split. exact HH1. split. exact (proj1 AM1). split. exact (proj2 AM1).
      split. rewrite r10. exact aR10. split. rewrite r12, (aKS 12%nat) by inl. rewrite <- r12. exact G12. split. clear - Hn; lia.
      split. rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4. split. rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
      split. { rewrite U12. apply (astack_ok_of_astk L ar C LY M M1 sp 4176 64 2560 STK MGM1). clear; lia. clear; lia. clear; lia. exact SA16. }
      split. { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
               intros b Hb. left. unfold byte_at. rewrite FRM1. 2: unfold S, SB; clear - Hb OR HVN; lia. 2:{ subst W1; cbn beta. unfold S, SB. clear - Hb ODSJ OR SPR HVN O8; lia. }
               unfold shadow_zero, byte_at in SZ. replace (S b) with (S o + (b / 8 - o / 8)) by (unfold S; clear; lia). apply SZ. clear - Hb HVN O8. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      split. { intros i Hi. rewrite U12. apply (obj_client L ar LB FF _ _ o 24 (o + 1 + i) AOB). clear - Hi HVN; lia. }
      split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS M1 o 24 ltac:(eapply L5.defined_grows; [exact MGM1 | exact ODEF]) ltac:(clear - OR; lia) ltac:(clear - OR; lia)) as W.
               replace (o + 1 + i) with (o + (1 + i)) by (clear; lia). apply W. clear - Hi; lia. clear - Hi Hm HVN; lia. }
      split. exact HK. apply (app_rng_aobj L ar C HI HIok LB FF LK cr A M1 _ o 24 (o + 1) n HH1 AOB). clear; lia. clear - HVN; lia. }
    { rewrite r11, (aKS 11%nat) by inl. rewrite <- r11. exact G11. }
    { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      intros b Hb. assert (E1 : M1 (Z_to_bv 64 (S b)) = M (Z_to_bv 64 (S b))). { apply FRM1. unfold S, SB; clear - Hb SR; lia. subst W1; cbn beta. unfold S, SB. clear - Hb SR OAPP SPR; lia. }
      unfold byte_at. rewrite E1. exact (ACC b Hb). }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    { exact SR. }
    { apply (app_rng_block L ar C HI HIok LB FF LK cr A M1 _ bA bm s n HH1 INB BA1 BA2). }
    { intros i Hi. right. apply (block_client L ar LB FF _ _ bA bm). exact INB. clear - Hi BA1 BA2; lia. }      (* [comment removed for export] *)
    { rewrite (L5C.rdn_agree RSEGS M M1 (Z.to_nat n) s). exact RDN. clear - SR; lia. clear - SR Hn; lia.
      intros i Hi. rewrite Z2Nat.id in Hi by (clear - Hn; lia). apply FRM1. clear - Hi SR Hn; lia. subst W1; cbn beta. clear - Hi BA1 BA2 BO BQ4 SLO; lia. }
    { intros _. clear - BA1 BA2 BO HVN; lia. }                                                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    intros R2 M2 model2 mR10 RP2 BYTES PRES2 SDEF2 RT2 MI2 HH2. rewrite U12 in PRES2, SDEF2. rewrite r1, aR1.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 sp 4176).
    { apply (astk_after_eq L ar C HI HIok LB FF LK cr A M1 M1 M2 _ sp _ (sp - 64) 2560 HH1 ltac:(eapply astk_grows; [exact STK | exact MGM1]) (mem_grows_refl M1)).
      intros a Ha Hs Hns. apply PRES2. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs OR HVN; lia.
      exact SDEF2. clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M2 model2 HH2) as (HOFF2 & VIS2 & _).
    pose proof (statics_vis LB FF LK cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M2 model2 o 24 (sp - 64) 2560 HH2 AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS2 & OVSH2 & OCL2 & OCLSH2).
    change (24 / 8) with 3 in OVSH2, OCLSH2.
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (K12 : forall a, (sp - 64 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 3 \/ (o <= a < o + 24 /\ ~ (o + 1 <= a < o + 1 + n))) -> MV2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      unfold MV2. rewrite (mrestrict_visible H2 M2).
      2:{ destruct Ra as [Ra|[Ra|[Ra _]]].
          - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia.
          - replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ra; lia. }
      apply PRES2. exact Ha.
      { destruct Ra as [Ra|[Ra|[Ra _]]].
        - apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
        - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH2. clear - Ra; lia.
        - replace a with (o + (a - o)) by (clear; lia). apply OCL2. clear - Ra; lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      destruct Ra as [Ra|[Ra|[Ra Na]]]. clear - Ra OR SLO HVN; lia. clear - Ra ODSJ HVN OR; unfold SB in *; lia. exact Na. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (AG1f : forall a, sp - 64 <= a < sp -> M1 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ra. apply EQ1. replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia. }
    assert (CS2 : forall k, In k cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (cs_of_preserved R1 R2 k RP2 Hk)).
    assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite CS2 by inl; exact aR2).
    assert (J8 : getr R2 (reg 8) = Z_to_bv 64 n) by (rewrite CS2 by inl; exact aR8).
    assert (J19 : getr R2 (reg 19) = Z_to_bv 64 (o + 1)) by (rewrite CS2 by inl; exact aR19).
    assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact aR21).
    assert (HVQ : 4096 <= o + 1 <= 140737488355328) by (clear - OR; lia). assert (HVN' : 0 <= n <= 1048576) by (clear - HVN; lia).
    assert (W64b : L5.writable RSEGS MV2 (sp - 64) 64).
    { apply (proj2 (writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. clear; lia. clear; lia. clear; lia. }
    (* [comment removed for export] *)
    pose proof (siT1_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 34%nat => n | 39%nat => o + 1 | 43%nat => U R2 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx3 & R3 & M3v & MG3 & cFR & cFZ & (cMS & cKS & cR10 & cR11)).
    assert (XC : forall a v, sp - 64 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M3v a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. rewrite cFZ by (clear - Ha Hb Hj SPR; lia).
      rewrite K12 by (left; clear - Ha Hb Hj; lia). apply AG1f. clear - Ha Hb Hj; lia. }
    pose proof (L5.defined_grows M M1 o 24 MGM1 ODEF) as ODEF1.
    destruct (tail_run fx3 R3 M3v sp (n + (o + 1)) r (U R 1) (U R 8) (U R 9) (U R 18) (U R 19) (U R 20) (U R 21))
      as (fx4 & R4 & M4v & MS4 & MG4 & FZ4 & K4 & tR1 & tR2 & tR8 & tR9 & tR18 & tR19 & tR20 & tR21 & tB).
    all: try apply UR.
    { exact cR10. } { exact cR11. } { rewrite (cKS 2%nat) by inl. exact J2. } { exact HV2. } { exact ALS. }
    { eapply L5.writable_grows. exact MG3. exact W64b. }
    { intros i Hi. rewrite cFZ. apply IMGC2. exact Hi. clear - Hi; lia. }
    { eapply L5C.u64_at_agree. 4: exact CSB2. 2: clear; lia. 2: clear; lia. intros j Hj. apply cFZ. clear - Hj; lia. }
    { eapply u32_at_agree1. 4: exact CUAR2. 2: clear; lia. 2: clear; lia. intros j Hj. apply cFZ. clear - Hj; lia. }
    { apply XC. clear; lia. clear; lia. unfold U; exact C8. } { apply XC. clear; lia. clear; lia. unfold U; exact C16. }
    { apply XC. clear; lia. clear; lia. unfold U; exact C24. } { apply XC. clear; lia. clear; lia. unfold U; exact C32. }
    { apply XC. clear; lia. clear; lia. unfold U; exact C40. } { apply XC. clear; lia. clear; lia. unfold U; exact C48. }
    { apply XC. clear; lia. clear; lia. unfold U; exact C56. }
    { exact UR1. } { exact RA. } { clear - OR HVN; lia. }
    { eapply L5.writable_grows. exact MG3. apply (L5C.writable_of_defined RSEGS). 2: clear - OR HVN; lia. 2: clear - OR HVN; lia.
      intros i Hi. replace (n + (o + 1) + i) with (o + (1 + n)) by (clear - Hi; lia). rewrite K12. apply (ODEF1 (1 + n)). clear - HVN; lia. right; right. clear - HVN; lia. }
    { clear - FRO HVN; lia. }
    { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      intros b Hb. left. unfold byte_at. rewrite cFZ. 2: unfold S, SB; clear - Hb OR HVN; lia.
      rewrite K12. 2:{ right; left. unfold S, SB. clear - Hb O8 HVN; lia. }
      rewrite FRM1. 2: unfold S, SB; clear - Hb OR HVN; lia. 2:{ subst W1; cbn beta. unfold S, SB. clear - Hb ODSJ OR SPR HVN O8; lia. }
      unfold shadow_zero, byte_at in SZ. replace (S b) with (S o + (b / 8 - o / 8)) by (unfold S; clear; lia). apply SZ. clear - Hb HVN O8; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    set (W3 := fun i => n + (o + 1) <= i < n + (o + 1) + 1).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M2 model2 fx1 fx4 R2 0x8e5b4 R4 r M4v W3 K HH2 (conj Hh2 MI2) (msteps_trans _ _ _ _ cMS MS4) (mem_grows_trans _ _ _ MG3 MG4)).
    { intros i Hi Hni. rewrite FZ4. apply cFZ. exact Hi. exact Hi. clear - Hni; subst W3; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W3; cbn beta in Wi. split. apply (obj_client L ar LB FF 0 0 o 24 i AOB). clear - Wi HVN; lia. clear - Wi OR HVN; lia. }
    intros M4 model4 HH4 AM4 RT4 AH4 VIS4 MGM4 FRM4 EQ4.
    apply (KONT fx4 R4 M4 model4 LB cr LK A).
    - split.
      { apply preserved_by_index. intros k Hk. cbn in Hk.
        assert (CH : forall k, In k KS_siT2 -> k <> 11%nat -> k <> 12%nat -> In k KS_siT1 -> In k cs_all -> In k KS_siS -> getr R4 (reg k) = getr R (reg k)).
        { intros k' H1 N1 N2 H3 H4 H5. rewrite (K4 k' H1 N1 N2), (cKS k' H3), (CS2 k' H4). apply aKS. exact H5. }
        destruct Hk as [<-|Hk]. { rewrite tR2. rewrite <- r2, G2. reflexivity. }
        destruct Hk as [<-|Hk]. { apply CH; [inl | clear; lia | clear; lia | inl | inl | inl]. }
        destruct Hk as [<-|Hk]. { apply CH; [inl | clear; lia | clear; lia | inl | inl | inl]. }
        destruct Hk as [<-|Hk]. { rewrite tR8. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR9. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR18. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR19. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR20. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR21. symmetry. apply U_to. }
        all: repeat (destruct Hk as [<-|Hk]; [apply CH; [inl | clear; lia | clear; lia | inl | inl | inl] |]). destruct Hk. }
      split.
      { intros _. split. reflexivity. split. reflexivity.
        split. { apply (proj1 (u8_at_vis H2 M4 o (2 * n) ltac:(eapply avis_sub; [exact OVIS2 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). replace (mrestrict H2 M4) with M4v by (symmetry; exact VIS4).
                 eapply L5C.u8_at_agree. 4: exact aB0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj.
                 rewrite FZ4 by first [clear - Hj OR; lia | subst W3; cbn beta; clear - Hj HVN; lia]. rewrite cFZ by (clear - Hj OR; lia).
                 rewrite K12 by (right; right; clear - Hj HVN; lia). apply EQ1. replace j with (o + (j - o)) by (clear; lia). apply (OVIS (j - o)). clear - Hj; lia. }
        split. { intros i Hi. destruct (BYTES i Hi) as (v & [Nv _] & Bv). exists (Z_to_bv 8 v). split. exact Nv. unfold byte_at in Bv. rewrite FRM4. exact Bv. clear - Hi OR HVN; lia.
                 subst W3; cbn beta. clear - Hi; lia. }
        split. { apply (proj1 (u8_at_vis H2 M4 (o + 1 + n) 0 ltac:(eapply avis_sub; [exact OVIS2 | clear - HVN; lia | clear - HVN; lia]) ltac:(clear - OR HVN; lia) ltac:(clear - OR HVN; lia))).
                 replace (mrestrict H2 M4) with M4v by (symmetry; exact VIS4). replace (o + 1 + n) with (n + (o + 1)) by (clear; lia). exact tB. }
        rewrite SCR_EQ. apply ahpres_of.
        + eapply ek_trans. { apply (EKP M M1 W1 FRM1). intros a Wa. subst W1; cbn beta in Wa. clear - Wa; lia. }
          eapply ek_trans. { apply (ek_mem L ar LB FF sp 4176 (sp - 64) 2560 (fun a => o + 1 <= a < o + 1 + n) [(o, 24)] M1 M2). exact PRES2. clear; lia. clear; lia.
            intros a Hc Ho X. apply (Ho (o, 24)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X HVN; lia. }
          apply (EKP M2 M4 W3 FRM4). intros a Wa. subst W3; cbn beta in Wa. clear - Wa HVN; lia.
        + eapply astk_defined. eapply astk_grows. exact ASTK2. exact MGM4. clear; lia. clear; lia.
        + eapply dk_trans. apply dk_grows. exact MGM1.
          eapply dk_trans. 2:{ apply dk_grows. exact MGM4. }
          apply (dk_mem L ar LB FF sp 4176 (sp - 64) 2560 (fun a => o + 1 <= a < o + 1 + n) M1 M2). exact PRES2. exact SDEF2.
          { intros a Ha. destruct (BYTES (a - (o + 1)) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (o + 1 + (a - (o + 1))) with a in Bv by (clear; lia). rewrite Bv. discriminate. }
          { intros a. clear. destruct (rng_dec a (o + 1) (o + 1 + n)); tauto. }
          clear; lia. clear; lia. }
      intros X. exfalso. clear - X N22; lia.
    - eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT4.
    - apply incl_refl.
    - exact AM4.
    - apply incl_refl.
    - exact HH4. }
  (* [comment removed for export] *)
  assert (HVN : 23 <= n <= 67108863) by (clear - N23 Hn; lia).
  set (cap := str_cap n) in *.
  assert (CAPE : (n = 23 /\ cap = 26) \/ (24 <= n /\ cap = 8 * (n / 8) + 8)).
  { destruct (Z.eq_dec n 23) as [E|E]. left. split. exact E. subst cap. rewrite E. reflexivity.
    right. split. clear - E HVN; lia. subst cap. apply str_cap_ge. clear - E HVN; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (CAPR : 24 <= cap <= 67108872 /\ n + 1 <= cap /\ 3 <= cap / 8 /\ 8 * (cap / 8) <= cap) by (clear - CAPE HVN; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (HEAD : exists fx1 R1 M1v, mem_grows MV M1v
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R STRINIT MV) (st fx1 R1 OPNEW M1v)
      /\ (forall x, In x [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
      /\ getr R1 (reg 1) = Z_to_bv 64 583000 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 n
      /\ getr R1 (reg 9) = Z_to_bv 64 (U R 11) /\ getr R1 (reg 10) = Z_to_bv 64 cap /\ getr R1 (reg 18) = Z_to_bv 64 o
      /\ getr R1 (reg 20) = Z_to_bv 64 cap /\ getr R1 (reg 21) = Z_to_bv 64 2147450880
      /\ L5.u64_at RSEGS M1v (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1v (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1v (sp - 40) (U R 19)
      /\ L5.u64_at RSEGS M1v (sp - 32) (U R 18) /\ L5.u64_at RSEGS M1v (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1v (sp - 16) (U R 8)
      /\ L5.u64_at RSEGS M1v (sp - 8) (U R 1)).
  { destruct CAPE as [[E23 EC]|[E24 EC]].
    - pose proof (siH23_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => U R 11 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- E23; sc)]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR18 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. rewrite EC, E23.
      split. exact MG1. split. exact aFZ. split. exact aMS.
      split. { intros x Hx. apply aKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      repeat split; assumption.
    - assert (ELOR : 24 <= Z.lor n 7 <= 67108871).
      { assert (E : Z.lor n 7 = 8 * (n / 8) + 7).
        { pose proof (Z.add_lor_land n 7) as A'. change 7 with (Z.ones 3) in A' at 2. rewrite Z.land_ones in A' by (clear; lia). change (2 ^ 3) with 8 in A'.
          clear - A' E24. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        rewrite E. clear - E24 HVN. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      pose proof (siHg_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => U R 11 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR18 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. rewrite EC.
      split. exact MG1. split. exact aFZ. split. exact aMS.
      split. { intros x Hx. apply aKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      repeat split; assumption. }
  destruct HEAD as (fx1 & R1 & M1v & MG1 & aFZ & aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR18 & aR20 & aR21 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  set (W1 := fun i => sp - 64 <= i < sp).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R STRINIT R1 OPNEW M1v W1 K HH AM aMS MG1).
  { intros i Hi Hni. apply aFZ. exact Hi. clear - Hni; subst W1; cbn beta in Hni; lia. }
  { intros i Hi Wi. subst W1; cbn beta in Wi. split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp 4176) by (eapply astk_grows; [exact STK | exact MGM1]).
  assert (SA16 : (sp - 64) mod 16 = 0). { clear - A16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (NEW fx1 R1 M1 model1 K LB FF LK cr A cap (sp - 64) 0x8e558 HH1 AM1 HK).
  + rewrite r10. exact aR10.
  + clear - CAPR; lia.
  + apply CR. clear - HVN; lia.
  + rewrite r1. exact aR1.
  + split. clear; lia. reflexivity.
  + rewrite r2. exact aR2.
  + rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4.
  + apply (astk_sub ar M1 M1 sp 4176 64 OPNEW_SCR ASTK1 (mem_grows_refl M1)). clear; lia. unfold OPNEW_SCR, MALLOC_SCR; clear; lia.
    unfold OPNEW_SCR, MALLOC_SCR; clear; lia. exact SA16.
  + intros fx2 R2 M2 model2 A2 p nR10 RP2 (BRp & BAp & FAp & DEFp & SHBp) PRES2 RT2 IA2 AM2 HH2.
    set (LB2 := (p, cap) :: LB) in *. set (cr2 := adebit L cr cap) in *.
    assert (ASTK2 : astk ar M2 sp 4176).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M1 M1 M2 _ sp _ (sp - 64) OPNEW_SCR [] HH1 ASTK1 (mem_grows_refl M1) PRES2).
      unfold OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK cr2 A2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
    pose proof (statics_vis LB2 FF LK cr2 A2 M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    pose proof (aobj_facts L ar C HI LY HIok LB2 FF LK cr2 A2 M2 model2 o 24 (sp - 64) 2560 HH2 AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & OVSH2 & OCL2 & OCLSH2).
    pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 24 (sp - 64) OPNEW_SCR HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & OCL1 & OCLSH1).
    change (24 / 8) with 3 in OVSH2, OCLSH2, OCLSH1.
    set (H2 := ahid A2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
    pose proof BRp as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Q1.
    (* [comment removed for export] *)
    assert (AG2 : forall a, (sp - 64 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 3 \/ o <= a < o + 24) -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      unfold MV2. rewrite (mrestrict_visible H2 M2).
      2:{ destruct Ra as [Ra|[Ra|Ra]].
          - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia.
          - replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ra; lia. }
      rewrite (proj1 PRES2 a).
      2:{ split. exact Ha. split. 2: intros rr [ ].
          destruct Ra as [Ra|[Ra|Ra]].
          - apply stack_client. clear - Ra SLO SHI SPT; lia. unfold OPNEW_SCR, MALLOC_SCR. clear - Ra; lia.
          - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH1. clear - Ra; lia.
          - replace a with (o + (a - o)) by (clear; lia). apply OCL1. clear - Ra; lia. }
      apply EQ1. destruct Ra as [Ra|[Ra|Ra]].
      - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH (a - (o / 8 + SB))). clear - Ra; lia.
      - replace a with (o + (a - o)) by (clear; lia). apply (OVIS (a - o)). clear - Ra; lia. }
    assert (CS2 : forall k, In k cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (cs_of_preserved R1 R2 k RP2 Hk)).
    assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite CS2 by inl; exact aR2).
    assert (J8 : getr R2 (reg 8) = Z_to_bv 64 n) by (rewrite CS2 by inl; exact aR8).
    assert (J9 : getr R2 (reg 9) = Z_to_bv 64 (U R 11)) by (rewrite CS2 by inl; exact aR9).
    assert (J18 : getr R2 (reg 18) = Z_to_bv 64 o) by (rewrite CS2 by inl; exact aR18).
    assert (J20 : getr R2 (reg 20) = Z_to_bv 64 cap) by (rewrite CS2 by inl; exact aR20).
    assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact aR21).
    assert (J10 : getr R2 (reg 10) = Z_to_bv 64 p) by (rewrite <- r10; exact nR10).
    assert (W64b : L5.writable RSEGS MV2 (sp - 64) 64).
    { apply (proj2 (writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. clear; lia. clear; lia. clear; lia. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + 2147450880) 3).
    { intros i Hi. rewrite AG2 by (right; left; unfold SB; clear - Hi; lia). rewrite aFZ. apply OZv. exact Hi. clear - Hi OR; lia. clear - Hi OR ODSJ SPR; lia. }
    assert (OW2 : L5.writable RSEGS MV2 o 24). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 24 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    (* [comment removed for export] *)
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (PSH : 0 <= p / 8 /\ p / 8 + cap / 8 <= 17592186044416 - 1048576 /\ (p / 8) * 8 = p) by (clear - Q0 Q4 Q2 CAPR SPT; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (PV : avis H2 p cap). { apply (VBLK2 p cap). left; reflexivity. clear; lia. clear; lia. }
    assert (PW2 : L5.writable RSEGS MV2 p cap).
    { apply (proj2 (writable_vis H2 M2 p cap PV ltac:(clear - Q0; lia) ltac:(clear - Q4 SPT; lia))).
      apply (L5C.writable_of_defined RSEGS). exact DEFp. clear - Q0; lia. clear - Q4 SPT; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (PVSH : avis H2 (p / 8 + 2147450880) (cap / 8)).
    { apply (VBSH2 p cap). left; reflexivity. intros i Hi. unfold in_shadow_of, S, SB. clear - Hi PSH CAPR Q0. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (PZ2 : L5KA.zeros_at MV2 (p / 8 + 2147450880) (cap / 8)).
    { apply (proj2 (zeros_at_vis H2 M2 (p / 8 + 2147450880) (cap / 8) PVSH)).
      intros i Hi. destruct SHBp as [SZp _]. unfold shadow_zero, byte_at, S, SB in SZp. apply SZp. exact Hi. }
    assert (PO : p + cap <= o \/ o + 24 <= p).
    { destruct AOB as (g & Hg & X1 & X2 & _). specialize (FAp g ltac:(apply in_or_app; left; exact Hg)). clear - FAp X1 X2. lia. }
    assert (HVP : 4096 <= p <= 140737488355328) by (clear - Q0 Q4 SPT CAPR; lia). assert (ALP : aligned p 16) by exact Q2.
    assert (HVPC : 4120 <= p + cap <= 140737479966720) by (clear - Q0 Q4 SPT CAPR; lia).
    assert (PAPP : 2147446784 + 17592186048512 <= p \/ p + cap <= 2147446784) by (clear - Q5; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (PDSJ : p + cap <= p / 8 + 2147450880 \/ p / 8 + 2147450880 + cap / 8 <= p) by (clear - Q5 Q0 CAPR; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (FRP : sp - 64 + 64 <= p \/ p + cap <= sp - 64) by (clear - Q4 SLO; lia).
    assert (OP : o + 24 <= p \/ p + cap <= o) by (clear - PO; lia).
    assert (XC2 : forall a v, sp - 64 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. apply AG2. left. clear - Ha Hb Hj; lia. }
    (* [comment removed for export] *)
    pose proof (siN_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => U R 11 | 36%nat => p | 37%nat => cap | 43%nat => U R2 1 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx3 & R3 & M3v & MG3 & nFR & nFZ & (nMS & nKS & nR1 & nR11 & nR12 & nR19 & nR20 & nO8 & nO0 & nO16)).
    set (W3 := fun i => o <= i < o + 24).
    apply (apiece L ar C HI LY HIok LB2 FF LK cr2 A2 M2 model2 fx2 fx3 R2 0x8e558 R3 0x5e7b0 M3v W3 K HH2 AM2 nMS MG3).
    { intros i Hi Hni. apply nFZ. exact Hi. clear - Hni; subst W3; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W3; cbn beta in Wi. split. apply (obj_client L ar LB2 FF 0 0 o 24 i AOB). exact Wi. clear - Wi OR; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp 4176) by (eapply astk_grows; [exact ASTK2 | exact MGM3]).
    (* [comment removed for export] *)
    pose proof (aio_memmove _ _ _ _ _ HIok) as MMV. unfold amemmove_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
    rewrite (aly_segs L C LY), (aly_memmove L C LY), (aly_scr_mem L C LY) in MMV.
    assert (U32 : bv_unsigned (getr R3 2%bv) = sp - 64). { rewrite r2, (nKS 2%nat) by inl. rewrite J2. apply L5.unsigned_lit. clear - SPR; lia. }
    (* [comment removed for export] *)
    assert (SHB3 : shadow_blk M3 p cap).
    { destruct SHBp as [SZp SPp]. split.
      - intros j Hj. unfold byte_at. rewrite FRM3. apply SZp. exact Hj. unfold S, SB; clear - Hj PSH; lia.
        subst W3; cbn beta. unfold S, SB. clear - Hj PSH OAPP. lia.
      - intros NZ. unfold byte_at. rewrite FRM3. apply SPp. exact NZ. unfold S, SB; clear - PSH CAPR; lia.
        subst W3; cbn beta. unfold S, SB. clear - PSH CAPR OAPP. lia. }
    assert (AGS3 : forall a, (s <= a < s + n \/ S s <= a <= S (s + n - 1)) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hq.
      assert (Ca : aclient L ar LB FF 0 0 a). { destruct Hq as [Ha|Ha]. apply (block_client L ar LB FF 0 0 bA bm). exact INB. clear - Ha BA1 BA2; lia.
        right; right; right; right; right; right. exists (bA, bm). split. exact INB. cbn [fst snd]. unfold in_shadow_of, S in *.
        clear - Ha BA1 BA2 HVN. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      assert (AR : 0 <= a < 2 ^ 64 /\ a + 1 <= ahl_ceil ar /\ ~ (o <= a < o + 24)).
      { unfold S in Hq. clear - Hq BA1 BA2 BO BQ4 BQ5 BQ0 SLO SPT OAPP OR HVN SR. unfold SB in *. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct AR as (A0 & A1 & A2').
      rewrite FRM3. 2: exact A0. 2:{ subst W3; cbn beta. exact A2'. }
      rewrite (proj1 PRES2 a). 2:{ split. exact A0. split. apply (aclient_narrow L ar LB FF 0 0). exact Ca. unfold OPNEW_SCR, MALLOC_SCR; clear - A1 SLO; lia. intros rr [ ]. }
      apply FRM1. exact A0. subst W1; cbn beta. clear - A1 SLO; lia. }
    eapply (MMV fx3 R3 M3 model3 LB2 FF LK cr2 A2 p s n cs K); clear MMV.
    { split. exact HH3. split. exact (proj1 AM3). split. exact (proj2 AM3).
      split. rewrite r10, (nKS 10%nat) by inl. exact J10. split. rewrite r12. exact nR12. split. clear - HVN; lia.
      split. rewrite r4, (nKS 4%nat) by inl. rewrite (CS2 4%nat) by inl. rewrite (aKS 4%nat) by inl. rewrite <- r4. exact G4.
      split. rewrite r1, nR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
      split. { rewrite U32. apply (astack_ok_of_astk L ar C LY M2 M3 sp 4176 64 2560 ASTK2 MGM3). clear; lia. clear; lia. clear; lia. exact SA16. }
      split. { apply (aacc_of_block M3 p cap p n SHB3). clear - Q2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. clear - Q0; lia. clear; lia. clear - CAPR; lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      split. { intros i Hi. rewrite U32. apply (block_client L ar LB2 FF _ _ p cap). left; reflexivity. clear - Hi CAPR; lia. }
      split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M3 p cap). eapply L5.defined_grows. exact MGM3. exact DEFp. clear - Q0; lia. clear - Q4 SPT; lia. exact Hi. clear - Hm CAPR; lia. }
      split. exact HK. apply (app_rng_block L ar C HI HIok LB2 FF LK cr2 A2 M3 _ p cap p n HH3 ltac:(left; reflexivity)). clear; lia. clear - CAPR; lia. }
    { rewrite r11, nR11, US11. reflexivity. }
    { intros b Hb. unfold byte_at. rewrite AGS3. exact (ACC b Hb). right. unfold S. clear - Hb HVN. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    { exact SR. }
    { apply (app_rng_block L ar C HI HIok LB2 FF LK cr2 A2 M3 _ bA bm s n HH3 ltac:(right; exact INB) BA1 BA2). }
    { intros i Hi. right. apply (block_client L ar LB2 FF _ _ bA bm). right; exact INB. clear - Hi BA1 BA2; lia. }      (* [comment removed for export] *)
    { rewrite (L5C.rdn_agree RSEGS M M3 (Z.to_nat n) s). exact RDN. clear - SR; lia. clear - SR Hn; lia.
      intros i Hi. rewrite Z2Nat.id in Hi by (clear - Hn; lia). apply AGS3. left. exact Hi. }
    { intros _. pose proof (BAp _ INB) as X. cbn [fst snd] in X. clear - X BA1 BA2 CAPR; lia. }                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    intros R4 M4 model4 mR10 RP4 BYTES PRES4 SDEF4 RT4 MI4 HH4. rewrite U32 in PRES4, SDEF4. rewrite r1, nR1.
    assert (Hh4 : m_halted model4 = None). { rewrite (L5LZ.model_rt_halted _ _ RT4). exact (proj1 AM3). }
    assert (ASTK4 : astk ar M4 sp 4176).
    { apply (astk_after_eq L ar C HI HIok LB2 FF LK cr2 A2 M3 M3 M4 _ sp _ (sp - 64) 2560 HH3 ASTK3 (mem_grows_refl M3)).
      intros a Ha Hs Hns. apply PRES4. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs Q4 CAPR; lia.
      exact SDEF4. clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK cr2 A2 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
    pose proof (statics_vis LB2 FF LK cr2 A2 M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4).
    set (H4 := ahid A2 model4) in *. set (MV4 := mrestrict H4 M4) in *.
    assert (FAF : fframes_apart p cap FF). { eapply fframes_apart_incl. exact FAp. apply incl_appl. apply incl_refl. }
    assert (PNC : forall a, p <= a < p + cap -> ~ aclient L ar LB FF sp 4176 a).
    { intros a Ha. exact (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M1 _ sp 4176 p cap a HH1 SPT BRp BAp FAF Ha). }
    assert (PRES4' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 64) 2560 a -> ~ (p <= a < p + n) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha Hc Hn'. apply PRES4. exact Ha. apply aclient_consb. exact Hc. exact Hn'. }
    (* [comment removed for export] *)
    assert (AG4s : forall a, sp - 64 <= a < sp -> MV4 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR; lia).
      unfold MV4. rewrite (mrestrict_visible H4 M4).
      2:{ replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS4 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia. }
      rewrite PRES4. 2: exact Ha. 2:{ apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. } 2: clear - Ra Q4 SLO CAPR; lia.
      rewrite FRM3. 2: exact Ha. 2:{ subst W3; cbn beta. clear - Ra FRO; lia. }
      rewrite <- (AG2 a (or_introl Ra)). unfold MV2. rewrite (mrestrict_visible H2 M2). reflexivity.
      replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia. }
    assert (CS4 : forall k, In k cs_all -> getr R4 (reg k) = getr R3 (reg k)) by (intros k Hk; apply (cs_of_preserved R3 R4 k RP4 Hk)).
    assert (L2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite CS4 by inl; rewrite (nKS 2%nat) by inl; exact J2).
    assert (L8 : getr R4 (reg 8) = Z_to_bv 64 n) by (rewrite CS4 by inl; rewrite (nKS 8%nat) by inl; exact J8).
    assert (L19 : getr R4 (reg 19) = Z_to_bv 64 p) by (rewrite CS4 by inl; exact nR19).
    assert (L21 : getr R4 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS4 by inl; rewrite (nKS 21%nat) by inl; exact J21).
    assert (W64d : L5.writable RSEGS MV4 (sp - 64) 64).
    { apply (proj2 (writable_vis H4 M4 (sp - 64) 64 (VIS4 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M4 sp). exact ASTK4. clear; lia. clear; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (DEF4 : L5.defined M4 p cap).
    { intros i Hi. destruct (rng_dec (p + i) p (p + n)) as [X|X].
      { destruct (BYTES (p + i - p) ltac:(clear - X; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (p + (p + i - p)) with (p + i) in Bv by (clear; lia). rewrite Bv. discriminate. }
      rewrite PRES4. apply MGM3. apply DEFp. exact Hi. clear - Hi Q0 Q4 SPT; lia.
      apply (block_client L ar LB2 FF _ _ p cap). left; reflexivity. clear - Hi; lia. exact X. }
    assert (SHC : forall j, 0 <= j <= cap / 8 -> (j < cap / 8 \/ cap mod 8 <> 0) -> aclient L ar LB2 FF (sp - 64) 2560 (S p + j)).
    { intros j Hj Hm. right; right; right; right; right; right. exists (p, cap). split. left; reflexivity. cbn [fst snd]. unfold in_shadow_of, S.
      clear - Hj Hm PSH CAPR Q0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (SHB4 : shadow_blk M4 p cap).
    { destruct SHB3 as [SZ3 SP3]. split.
      - intros j Hj. unfold byte_at. rewrite PRES4. apply SZ3. exact Hj. unfold S, SB; clear - Hj PSH; lia. apply SHC. clear - Hj; lia. left; clear - Hj; lia.
        unfold S, SB. clear - Hj PSH Q5 CAPR. lia.
      - intros NZ. unfold byte_at. rewrite PRES4. apply SP3. exact NZ. unfold S, SB; clear - PSH CAPR; lia. apply SHC. clear - CAPR; lia. right; exact NZ.
        unfold S, SB. clear - PSH Q5 CAPR. lia. }
    assert (PV4 : avis H4 p cap). { apply (VBLK4 p cap). left; reflexivity. clear; lia. clear; lia. }
    assert (PVS4 : forall j, 0 <= j <= cap / 8 -> (j < cap / 8 \/ cap mod 8 <> 0) -> H4 (Z_to_bv 64 (S p + j)) = false).
    { intros j Hj Hm. replace (S p + j) with (S p + j + 0) by (clear; lia). apply (VBSH4 p cap (S p + j) 1). left; reflexivity. 2: clear; lia.
      intros i Hi. unfold in_shadow_of, S. clear - Hi Hj Hm PSH CAPR Q0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    pose proof (siT1_conc fx3 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => n | 39%nat => p | 43%nat => U R4 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx5 & R5 & M5v & MG5 & cFR & cFZ & (cMS & cKS & cR10 & cR11)).
    assert (XC4 : forall a v, sp - 64 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M5v a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. rewrite cFZ by (clear - Ha Hb Hj SPR; lia).
      apply AG4s. clear - Ha Hb Hj; lia. }
    destruct (tail_run fx5 R5 M5v sp (n + p) r (U R 1) (U R 8) (U R 9) (U R 18) (U R 19) (U R 20) (U R 21))
      as (fx6 & R6 & M6v & MS6 & MG6 & FZ6 & K6 & tR1 & tR2 & tR8 & tR9 & tR18 & tR19 & tR20 & tR21 & tB).
    all: try apply UR.
    { exact cR10. } { exact cR11. } { rewrite (cKS 2%nat) by inl. exact L2. } { exact HV2. } { exact ALS. }
    { eapply L5.writable_grows. exact MG5. exact W64d. }
    { intros i Hi. rewrite cFZ. apply IMGC4. exact Hi. clear - Hi; lia. }
    { eapply L5C.u64_at_agree. 4: exact CSB4. 2: clear; lia. 2: clear; lia. intros j Hj. apply cFZ. clear - Hj; lia. }
    { eapply u32_at_agree1. 4: exact CUAR4. 2: clear; lia. 2: clear; lia. intros j Hj. apply cFZ. clear - Hj; lia. }
    { apply XC4. clear; lia. clear; lia. exact C8. } { apply XC4. clear; lia. clear; lia. exact C16. }
    { apply XC4. clear; lia. clear; lia. exact C24. } { apply XC4. clear; lia. clear; lia. exact C32. }
    { apply XC4. clear; lia. clear; lia. exact C40. } { apply XC4. clear; lia. clear; lia. exact C48. }
    { apply XC4. clear; lia. clear; lia. exact C56. }
    { exact UR1. } { exact RA. } { clear - Q0 Q4 SPT CAPR HVN; lia. }
    { eapply L5.writable_grows. exact MG5. eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS MV4 p cap). apply (proj2 (defined_vis H4 M4 p cap PV4)). exact DEF4.
      clear - Q0; lia. clear - Q4 SPT; lia. clear - HVN; lia. clear - CAPR; lia. }
    { clear - FRP CAPR HVN; lia. }
    { apply (aacc_of_block M5v p cap (n + p) 1). 2:{ clear - Q2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      2: clear - Q0; lia. 2: clear - HVN; lia. 2: clear - CAPR; lia.
      destruct SHB4 as [SZ4 SP4]. split.
      - intros j Hj. unfold byte_at. rewrite cFZ by (unfold S, SB; clear - Hj PSH; lia). unfold MV4. rewrite (mrestrict_visible H4 M4). apply SZ4. exact Hj.
        apply PVS4. clear - Hj; lia. left. clear - Hj; lia.
      - intros NZ. unfold byte_at. rewrite cFZ by (unfold S, SB; clear - PSH CAPR; lia). unfold MV4. rewrite (mrestrict_visible H4 M4). apply SP4. exact NZ.
        apply PVS4. clear - CAPR; lia. right. exact NZ. }
    set (W5 := fun i => n + p <= i < n + p + 1).
    apply (apiece L ar C HI LY HIok LB2 FF LK cr2 A2 M4 model4 fx3 fx6 R4 0x8e5b4 R6 r M6v W5 K HH4 (conj Hh4 MI4) (msteps_trans _ _ _ _ cMS MS6) (mem_grows_trans _ _ _ MG5 MG6)).
    { intros i Hi Hni. rewrite FZ6. apply cFZ. exact Hi. exact Hi. clear - Hni; subst W5; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W5; cbn beta in Wi. split. apply (block_client L ar LB2 FF 0 0 p cap). left; reflexivity. clear - Wi CAPR HVN; lia. clear - Wi Q1 CAPR HVN; lia. }
    intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
    (* [comment removed for export] *)
    assert (AGO5 : forall a, o <= a < o + 24 -> M5 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a)).
    { intros a Ha. assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha OR; lia).
      rewrite FRM5. 2: exact Ha'. 2:{ subst W5; cbn beta. clear - Ha PO CAPR HVN; lia. }
      rewrite PRES4. 2: exact Ha'. 2:{ apply (obj_client L ar LB2 FF _ _ o 24 a AOB). exact Ha. } 2: clear - Ha PO CAPR; lia.
      apply EQ3. replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ha; lia. }
    apply (KONT fx6 R6 M5 model5 LB2 cr2 LK A2).
    - split.
      { apply preserved_by_index. intros k Hk. cbn in Hk.
        assert (CH : forall k, In k KS_siT2 -> k <> 11%nat -> k <> 12%nat -> In k KS_siT1 -> In k cs_all -> In k KS_siN -> In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg k) = getr R (reg k)).
        { intros k' H1 N1 N2 H3 H4' H5 H6. rewrite (K6 k' H1 N1 N2), (cKS k' H3), (CS4 k' H4'), (nKS k' H5), (CS2 k' H4'). apply aKS. exact H6. }
        destruct Hk as [<-|Hk]. { rewrite tR2. rewrite <- r2, G2. reflexivity. }
        destruct Hk as [<-|Hk]. { apply CH; [inl | clear; lia | clear; lia | inl | inl | inl | inl]. }
        destruct Hk as [<-|Hk]. { apply CH; [inl | clear; lia | clear; lia | inl | inl | inl | inl]. }
        destruct Hk as [<-|Hk]. { rewrite tR8. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR9. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR18. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR19. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR20. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite tR21. symmetry. apply U_to. }
        all: repeat (destruct Hk as [<-|Hk]; [apply CH; [inl | clear; lia | clear; lia | inl | inl | inl | inl] |]). destruct Hk. }
      split. { intros X. exfalso. clear - X HVN; lia. }
      intros _. exists p. cbn zeta. fold cap.
      split. reflexivity. split. reflexivity.
      split.
      { split. exact BRp. split. exact BAp. split. exact FAp.
        split. { eapply L5.defined_grows. exact MGM5. exact DEF4. }
        destruct SHB4 as [SZ4 SP4]. split.
        - intros j Hj. unfold byte_at. rewrite FRM5. apply SZ4. exact Hj. unfold S, SB; clear - Hj PSH; lia. subst W5; cbn beta. unfold S, SB. clear - Hj PSH Q5 CAPR HVN. lia.
        - intros NZ. unfold byte_at. rewrite FRM5. apply SP4. exact NZ. unfold S, SB; clear - PSH CAPR; lia. subst W5; cbn beta. unfold S, SB. clear - PSH Q5 CAPR HVN. lia. }
      split. { eapply L5C.u64_at_agree. 4: exact nO0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AGO5. clear - Hj; lia. }
      split. { eapply L5C.u64_at_agree. 4: exact nO8. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AGO5. clear - Hj; lia. }
      split. { eapply L5C.u64_at_agree. 4: exact nO16. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AGO5. clear - Hj; lia. }
      split. { intros i Hi. destruct (BYTES i Hi) as (v & [Nv _] & Bv). exists (Z_to_bv 8 v). split. exact Nv. unfold byte_at in Bv. rewrite FRM5. exact Bv. clear - Hi Q0 Q4 SPT CAPR; lia.
               subst W5; cbn beta. clear - Hi; lia. }
      split. { apply (proj1 (u8_at_vis H4 M5 (p + n) 0 ltac:(eapply avis_sub; [exact PV4 | clear - HVN; lia | clear - CAPR; lia]) ltac:(clear - Q0 HVN; lia) ltac:(clear - Q4 SPT CAPR; lia))).
               replace (mrestrict H4 M5) with M6v by (symmetry; exact VIS5). replace (p + n) with (n + p) by (clear; lia). exact tB. }
      rewrite SCR_EQ. apply ahpres_of.
      * eapply ek_trans. { apply (EKP M M1 W1 FRM1). intros a Wa. subst W1; cbn beta in Wa. clear - Wa; lia. }
        eapply ek_trans. { apply (ek_callee L ar LB [] FF [] sp 4176 (sp - 64) OPNEW_SCR [(o, 24)] [] M1 M2 PRES2). unfold OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. intros a _ _ rr [ ]. }
        eapply ek_trans. { apply (EKP M2 M3 W3 FRM3). intros a Wa. subst W3; cbn beta in Wa. clear - Wa; lia. }
        eapply ek_trans. { apply (ek_mem L ar LB FF sp 4176 (sp - 64) 2560 (fun a => p <= a < p + n) [(o, 24)] M3 M4 PRES4'). clear; lia. clear; lia.
          intros a Hc Ho X. apply (PNC a). clear - X CAPR; lia. exact Hc. }
        apply (ek_piece L ar LB FF sp 4176 [(o, 24)] M4 M5 W5 FRM5). intros a Ha Hc Ho X. apply (PNC a). subst W5; cbn beta in X. clear - X CAPR HVN; lia. exact Hc.
      * eapply astk_defined. eapply astk_grows. exact ASTK4. exact MGM5. clear; lia. clear; lia.
      * eapply dk_trans. apply dk_grows. exact MGM1.
        eapply dk_trans. apply (dk_callee L ar LB [] FF [] sp 4176 (sp - 64) OPNEW_SCR [] M1 M2 PRES2). unfold OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
        eapply dk_trans. apply dk_grows. exact MGM3.
        eapply dk_trans. 2:{ apply dk_grows. exact MGM5. }
        apply (dk_mem L ar LB FF sp 4176 (sp - 64) 2560 (fun a => p <= a < p + n) M3 M4 PRES4' SDEF4).
        { intros a Ha. destruct (BYTES (a - p) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (p + (a - p)) with a in Bv by (clear; lia). rewrite Bv. discriminate. }
        { intros a. clear. destruct (rng_dec a p (p + n)); tauto. }
        clear; lia. clear; lia.
    - eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4. exact RT5.
    - exact IA2.
    - exact AM5.
    - apply incl_refl.
    - exact HH5.
Qed.

End WithIface.
End SCFG_1.
End L5ASTR.

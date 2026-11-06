(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5AChk L5BChkAs0 L5BTobigP Bo0_code_8e368_8f368 Bo0_code_91368_92368.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5ArithSpecsB0 L5ParseSpecsBB0 L5BStkSh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ATB.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5ASB. Import L5PSB. Import L5ATBP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma vblk_pos m : 0 <= vblk m.
Proof. unfold vblk. destruct (m <? 39)%nat. lia. unfold round_up. pose proof (Z.div_pos (Z.of_nat (num_words_est m)) 8 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma DSCR_EQ : DETAIL_SCRB = 4864. Proof. reflexivity. Qed.
Lemma TSCR_EQ : TOBIG_SCRB = 4880. Proof. reflexivity. Qed.
Lemma split_sign_cons c t : split_sign (c :: t) = if Z.eqb c 45 then (true, t) else (false, c :: t). Proof. reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.   (* [comment removed for export] *)
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.

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
Theorem tobig4_ok : detail_specB L ar IL HI -> tobig4_specB L ar IL HI.
Proof.
  intros DET fx R M model K LB FF LK cr A p o sp r fb neg0 s HH AM HK G10 G11 _ G12 LEN CR G1 RA G2 A32 G4 STK SSH FFR FFR2 FFRS BIG FB3 AOB SZ BYTES BR SRC APART KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite TSCR_EQ in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487184 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 0 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W16 : L5.writable RSEGS MV (sp - 16) 16).
  { apply (proj2 (writable_vis H M (sp - 16) 16 (VIS (sp - 16) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. clear; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (HV2 : 140735332487184 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (OFR : forall a, o <= a < o + 32 -> ~ (sp - 16 <= a < sp - 16 + 16)) by (intros a Ha; clear - Ha OR SLO; lia).
  (* [comment removed for export] *)
  assert (EKF : forall SCR0 W0 M0 M1, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) -> 16 <= SCR0 ->
            ek L ar LB FF sp SCR0 W0 M0 M1).
  { intros SCR0 W0 M0 M1 FRM HS. apply (ek_piece L ar LB FF sp SCR0 W0 M0 M1 (fun a => sp - 16 <= a < sp) FRM). intros a Ha Hc Ho X.
    destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp SCR0 a HH SPT Hc) as [Z1|Z1]. clear - X Z1 HS; lia. clear - X Z1 SLO; lia. }
  destruct (Nat.eq_dec (length s) 0) as [L0|L0].
  { (* [comment removed for export] *)
    assert (Es : s = []) by (destruct s; [reflexivity | discriminate L0]). subst s. cbn [length Z.of_nat] in G11.
    pose proof (tqA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => U R 10 | 36%nat => U R 12 | 37%nat => U R 13 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r11; exact G11)]).
    destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR11)).
    pose proof (ret_to fx1 R1 M1v 0x8ed0c W_8ed0c r F_8ed0c eq_refl D_8ed0c ltac:(rewrite (aKS 1%nat) by inl; rewrite <- r1; exact G1) (proj1 RA) (proj2 RA)) as RET.
    set (W1 := fun i => sp - 16 <= i < sp).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R TOBIG4 R1 r M1v W1 K HH AM (msteps_trans _ _ _ _ aMS RET) MG1).
    { intros i Hi Hni. apply aFZ. exact Hi. clear - Hni; subst W1; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W1; cbn beta in Wi. split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    apply (KONT fx1 R1 M1 model1 LB cr LK A).
    - split.
      { apply preserved_by_index. intros k Hk. apply aKS. revert Hk. clear. unfold cs_all. cbn [In]. intros Hk.
        repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk. }
      right. split. left; reflexivity. split. rewrite r11. exact aR11.
      split. reflexivity.
      split. { eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply FRM1. clear - Hi OR; lia. subst W1; cbn beta. intros X. apply (OFR i Hi). clear - X; lia. }
      split. { unfold parse_debit. eapply credit_le_trans. apply adebit_le. exact LY2. apply vblk_pos. apply adebit_le. exact LY2. apply vblk_pos. }
      apply ahpres_of.
      + apply (EKF TOBIG_SCRB [] M M1). exact FRM1. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
      + eapply astk_defined. eapply astk_grows. exact STK. exact MGM1. clear; lia. clear; lia.
      + apply dk_grows. exact MGM1.
    - exact RT1.
    - apply incl_refl.
    - exact AM1.
    - apply incl_refl.
    - exact HH1. }
  (* [comment removed for export] *)
  destruct s as [|b0 t]; [exfalso; apply L0; reflexivity|]. clear L0.
  set (n := Z.of_nat (length (b0 :: t))) in *.
  assert (HVN : 1 <= n <= 4999) by (subst n; cbn [length] in *; clear - LEN; lia).
  pose proof (asrc_range L ar C IL HI LY ILY HIok LB FF LK cr A M _ p n HH SRC ltac:(clear - HVN; lia)) as [P0 P1].
  assert (PFR : forall a, p <= a < p + n -> ~ (sp - 16 <= a < sp - 16 + 16)) by (intros a Ha; clear - Ha P1 SLO; lia).
  assert (B0R : 0 <= b0 < 256) by (inversion BR; assumption).
  assert (B0 : L5.u8_at RSEGS M p b0). { pose proof (BYTES 0%nat ltac:(cbn [length]; clear; lia)) as X. cbn [nth] in X. change (Z.of_nat 0) with 0 in X. replace (p + 0) with p in X by (clear; lia). exact X. }
  pose proof (asrc_vis L ar C IL HI LY ILY HIok LB FF LK cr A M model p n HH SRC) as PVIS.
  assert (B0v : L5.u8_at RSEGS MV p b0). { apply (proj2 (u8_at_vis H M p b0 ltac:(eapply avis_sub; [exact PVIS | clear; lia | clear - HVN; lia]) ltac:(clear - P0; lia) ltac:(clear - P1 SPT HVN; lia))). exact B0. }
  assert (ACCv : aacc MV p 1).
  { apply (aacc_vis H M p 1). eapply aacc_sub. apply (asrc_aacc L ar C IL HI ILY HIok ICok LB FF LK cr A M _ p n HH SRC). clear; lia. clear - HVN; lia.
    intros a Ha. apply (asrc_shadow_vis L ar C IL HI LY ILY HIok ICok LB FF LK cr A M model p n a HH SRC). clear - Ha HVN; lia. }
  pose proof (tqB_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R 13 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r10; exact G10) | (rewrite <- r11; exact G11) | (rewrite <- r12; exact G12)]).
  destruct P as (fx1 & R1 & M1v & MG1 & bFR & bFZ & (bMS & bKS & bR2 & bR12 & bR13 & bR14 & bR15 & bC8)).
  assert (ACC1 : aacc M1v p 1).
  { intros a Ha. unfold byte_at. rewrite bFZ. exact (ACCv a Ha). unfold S, SB. clear - Ha P0 P1 SPT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    unfold S, SB. clear - Ha P0 P1 SPT SLO. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (L5ACHK0.chk_8e974 fx1 R1 M1v p ltac:(unfold S, SB; exact bR12) ltac:(rewrite (bKS 10%nat) by inl; rewrite <- r10; exact G10) ltac:(clear - P0 P1 SPT HVN; lia) ACC1)
    as (R1' & MS1' & K1').
  assert (B01 : L5.u8_at RSEGS M1v p b0). { eapply L5C.u8_at_agree. 4: exact B0v. 2: clear - P0; lia. 2: clear - P1 SPT HVN; lia. intros i Hi. apply bFZ. clear - Hi P0 P1 SPT; lia. apply PFR. clear - Hi HVN; lia. }
  assert (W16b : L5.writable RSEGS M1v (sp - 16) 16) by (eapply L5.writable_grows; [exact MG1 | exact W16]).
  assert (ST1 : L5.img_clear M1v 860160 884736 /\ L5.u64_at RSEGS M1v 911160 2147450880 /\ L5.u32_at RSEGS M1v 911168 1).
  { split. { intros i Hi. rewrite bFZ. apply IMGC. exact Hi. clear - Hi; lia. clear - Hi SPR; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros j Hj. apply bFZ. clear - Hj; lia. clear - Hj SPR; lia. }
    eapply u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros j Hj. apply bFZ. clear - Hj; lia. clear - Hj SPR; lia. }
  destruct ST1 as (IMGC1 & CSB1 & CUAR1).
  set (ng := fst (split_sign (b0 :: t))). set (ds := snd (split_sign (b0 :: t))).
  (* [comment removed for export] *)
  assert (CALL : exists fx2 R2, msteps RSEGS (st fx1 R1' 0x8ecd0 M1v) (st fx2 R2 DETAIL M1v)
      /\ (forall x, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R1' (reg x))
      /\ getr R2 (reg 1) = Z_to_bv 64 0x8ecfc /\ getr R2 (reg 2) = Z_to_bv 64 (sp - 16)
      /\ getr R2 (reg 10) = Z_to_bv 64 (if ng then p + 1 else p) /\ getr R2 (reg 11) = Z_to_bv 64 (Z.of_nat (length ds))
      /\ getr R2 (reg 12) = Z_to_bv 64 (if ng then 1 else 0) /\ getr R2 (reg 13) = Z_to_bv 64 o).
  { assert (J2 : getr R1' (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite K1' by (clear; lia); exact bR2).
    assert (J10 : getr R1' (reg 10) = Z_to_bv 64 p) by (rewrite K1' by (clear; lia); rewrite (bKS 10%nat) by inl; rewrite <- r10; exact G10).
    assert (J11 : getr R1' (reg 11) = Z_to_bv 64 n) by (rewrite K1' by (clear; lia); rewrite (bKS 11%nat) by inl; rewrite <- r11; exact G11).
    assert (J13 : getr R1' (reg 13) = Z_to_bv 64 o) by (rewrite K1' by (clear; lia); exact bR13).
    assert (HVP : 4096 <= p <= 140737479966720) by (clear - P0 P1 SPT HVN; lia).
    assert (FRP : sp - 16 + 16 <= p \/ p + 1 <= sp - 16) by (right; clear - P1 SLO HVN; lia).
    assert (HVN' : 1 <= n <= 67108863) by (clear - HVN; lia).
    destruct (Z.eq_dec b0 45) as [E45|N45].
    - pose proof (tqCm_conc fx1 R1' M1v (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R1' 14 | 56%nat => b0 | 59%nat => U R1' 12 | 60%nat => U R1' 15 | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx2 & R2 & M2v & MG2 & cFR & cFZ & (cMS & cKS & cR1 & cR10 & cR11 & cR12 & _)).
      assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; exact cFZ). subst M2v.
      exists fx2, R2. subst ng ds. rewrite split_sign_cons. rewrite (proj2 (Z.eqb_eq b0 45) E45). cbn [fst snd].
      split. exact cMS. split. { intros x Hx. apply cKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      split. exact cR1. split. { rewrite (cKS 2%nat) by inl. exact J2. } split. exact cR10.
      split. { rewrite cR11. f_equal. subst n. cbn [length]. clear; lia. } split. exact cR12. rewrite (cKS 13%nat) by inl. exact J13.
    - assert (NE : (b0 =? 45) = false) by (apply Z.eqb_neq; exact N45).
      destruct (Z_lt_le_dec b0 45) as [LT|GE].
      + pose proof (tqCl_conc fx1 R1' M1v (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R1' 14 | 56%nat => b0 | 59%nat => U R1' 12 | 60%nat => U R1' 15 | _ => 0 end)) as P.
        cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx2 & R2 & M2v & MG2 & cFR & cFZ & (cMS & cKS & cR1 & cR12 & _)).
        assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; exact cFZ). subst M2v.
        exists fx2, R2. subst ng ds. rewrite split_sign_cons, NE. cbn [fst snd].
        split. exact cMS. split. { intros x Hx. apply cKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
        split. exact cR1. split. { rewrite (cKS 2%nat) by inl. exact J2. } split. { rewrite (cKS 10%nat) by inl. exact J10. }
        split. { rewrite (cKS 11%nat) by inl. exact J11. } split. exact cR12. rewrite (cKS 13%nat) by inl. exact J13.
      + pose proof (tqCh_conc fx1 R1' M1v (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R1' 14 | 56%nat => b0 | 59%nat => U R1' 12 | 60%nat => U R1' 15 | _ => 0 end)) as P.
        cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx2 & R2 & M2v & MG2 & cFR & cFZ & (cMS & cKS & cR1 & cR12 & _)).
        assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; exact cFZ). subst M2v.
        exists fx2, R2. subst ng ds. rewrite split_sign_cons, NE. cbn [fst snd].
        split. exact cMS. split. { intros x Hx. apply cKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
        split. exact cR1. split. { rewrite (cKS 2%nat) by inl. exact J2. } split. { rewrite (cKS 10%nat) by inl. exact J10. }
        split. { rewrite (cKS 11%nat) by inl. exact J11. } split. exact cR12. rewrite (cKS 13%nat) by inl. exact J13. }
  destruct CALL as (fx2 & R2 & cMS & cKS & cR1 & cR2 & cR10 & cR11 & cR12 & cR13).
  set (W1 := fun i => sp - 16 <= i < sp).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx2 R TOBIG4 R2 DETAIL M1v W1 K HH AM
           (msteps_trans _ _ _ _ bMS (msteps_trans _ _ _ _ MS1' cMS)) MG1).
  { intros i Hi Hni. apply bFZ. exact Hi. clear - Hni; subst W1; cbn beta in Hni; lia. }
  { intros i Hi Wi. subst W1; cbn beta in Wi. split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp TOBIG_SCRB) by (eapply astk_grows; [exact STK | exact MGM1]).
  (* [comment removed for export] *)
  set (p' := if ng then p + 1 else p) in *.
  assert (DSF : p <= p' /\ p' + Z.of_nat (length ds) = p + n /\ L5.bytes_at RSEGS M p' ds /\ Forall (fun c => 0 <= c < 256) ds /\ (length ds <= 4999)%nat).
  { subst p' ng ds n. rewrite split_sign_cons. destruct (b0 =? 45); cbn [fst snd length].
    - split. clear; lia. split. clear; lia. split. { intros i Hi. pose proof (BYTES (Datatypes.S i) ltac:(cbn [length]; clear - Hi; lia)) as X. cbn [nth] in X.
        replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (Datatypes.S i)) by (clear; lia). exact X. }
      split. inversion BR; assumption. cbn [length] in LEN. clear - LEN; lia.
    - split. clear; lia. split. clear; lia. split. exact BYTES. split. exact BR. exact LEN. }
  destruct DSF as (PP1 & PP2 & BYT' & BR' & LEN').
  assert (SA16 : (sp - 16) mod 32 = 16). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (DET fx2 R2 M1 model1 K LB FF LK cr A p' o (sp - 16) 0x8ecfc fb ng ds HH1 AM1 HK).
  - rewrite r10. exact cR10.
  - rewrite r11. exact cR11.
  - intros _. rewrite r12. exact cR12.
  - rewrite r13. exact cR13.
  - exact LEN'.
  - exact CR.
  - rewrite r1. exact cR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact cR2.
  - exact SA16.
  - rewrite r4, (cKS 4%nat) by inl. rewrite K1' by (clear; lia). rewrite (bKS 4%nat) by inl. rewrite <- r4. exact G4.
  - apply (astk_sub ar M1 M1 sp TOBIG_SCRB 16 DETAIL_SCRB ASTK1 (mem_grows_refl M1)). clear; lia.
    rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
    clear - SA16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF0.
    assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (M8 : (sp - TOBIG_SCRB) mod 8 = 0 /\ (sp - 16 - DETAIL_SCRB) mod 8 = 0) by (rewrite TSCR_EQ, DSCR_EQ; clear - A32; Lia.lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (L5BSS.stksh_frame ar M M1 (sp - TOBIG_SCRB) (sp - 16 - DETAIL_SCRB) (sp - 16) sp SSH);
      [ rewrite TSCR_EQ, DSCR_EQ; clear; lia | exact (proj1 M8) | exact (proj2 M8) | rewrite TSCR_EQ; clear - SLO; lia | rewrite TSCR_EQ; clear - SLO SPR; lia
      | exact TOP | clear - SPT; lia | clear - SPR; lia | ].
    intros a Ha Hn. apply FRM1. exact Ha. subst W1; cbn beta. exact Hn.
  - exact FFR.
  - exact FFR2.
  - eapply ffrs_le. exact FFRS. clear; lia.
  - eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply FRM1. clear - Hi OR; lia. subst W1; cbn beta. intros X. apply (OFR i Hi). clear - X; lia.
  - exact FB3.
  - exact AOB.
  - intros j Hj. unfold byte_at. rewrite FRM1. exact (SZ j Hj). unfold S, SB; clear - Hj OR; lia. subst W1; cbn beta. unfold S, SB. clear - Hj OR SLO SPT. lia.
  - eapply L5C.bytes_at_agree. 4: exact BYT'. 2: clear - PP1 P0; lia. 2: clear - PP2 P1 SPT; lia. intros i Hi. apply FRM1. clear - Hi PP1 PP2 P0 P1 SPT; lia.
    subst W1; cbn beta. intros X. apply (PFR i). clear - Hi PP1 PP2; lia. clear - X; lia.
  - exact BR'.
  - eapply (asrc_keep IL LB LB FF FF M M1). eapply asrc_sub. exact SRC. exact PP1. clear - PP2; lia. clear; lia. apply incl_refl. apply incl_refl.
    intros so AO SZo j Hj. unfold byte_at. rewrite FRM1. exact (SZo j Hj).
    { pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp 0 HH AO ltac:(clear; lia) ltac:(reflexivity)) as (OR' & _). unfold S, SB; clear - Hj OR'; lia. }
    { pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp 0 HH AO ltac:(clear; lia) ltac:(reflexivity)) as (OR' & _). subst W1; cbn beta. unfold S, SB. clear - Hj OR' SLO SPT. lia. }
  - clear - APART PP1 PP2. lia.
  - (* [comment removed for export] *)
    intros fx3 R3 M3 model3 LB3 cr3 LK3 A3 (RP3 & POST3) RT3 IA3 AM3 ILK3 HH3.
    pose proof (vis_pack L ar C HI LY HIok LB3 FF LK3 cr3 A3 M3 model3 HH3) as (HOFF3 & VIS3 & _).
    pose proof (statics_vis LB3 FF LK3 cr3 A3 M3 model3 HH3) as (IMGC3 & CSB3 & CUAR3).
    set (H3 := ahid A3 model3) in *. set (MV3 := mrestrict H3 M3) in *.
    assert (HP3 : ahpres L ar LB FF (sp - 16) DETAIL_SCRB [(o, 32)] M1 M3).
    { destruct POST3 as [(_ & _ & _ & PP)|(_ & _ & PP)].
      - destruct PP as (st' & _ & _ & _ & _ & HP). exact HP.
      - destruct PP as (_ & _ & _ & (E & D & Kk)). split. { intros a (Ha & Hc & _). apply E. split. exact Ha. split. exact Hc. intros rr []. } split. exact D. exact Kk. }
    assert (ASTK3 : astk ar M3 sp TOBIG_SCRB).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M1 M1 M3 _ sp _ (sp - 16) DETAIL_SCRB [(o, 32)] HH1 ASTK1 (mem_grows_refl M1) HP3).
      rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. }
    assert (W16c : L5.writable RSEGS MV3 (sp - 16) 16).
    { apply (proj2 (writable_vis H3 M3 (sp - 16) 16 (VIS3 (sp - 16) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M3 sp). exact ASTK3. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. clear; lia. }
    assert (C8v : L5.u64_at RSEGS MV3 (sp - 8) (U R 1)).
    { apply (proj2 (u64_at_vis H3 M3 (sp - 8) _ (VIS3 (sp - 8) 8 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply L5C.u64_at_agree. 4: exact bC8. 2: clear - SPR; lia. 2: clear - SPR; lia. intros j Hj.
      rewrite (proj1 HP3 j). 2:{ split. clear - Hj SPR; lia. split. apply stack_client. clear - Hj SLO SHI SPT; lia. clear - Hj; lia.
        intros rr [E|[]]. subst rr. unfold L5.in_rng; cbn [fst snd]. clear - Hj OR SLO; lia. }
      apply EQ1. replace j with ((sp - 16) + (j - (sp - 16))) by (clear; lia). apply (VIS (sp - 16) 16). clear - SLO; lia. clear - SPR; lia. clear - Hj; lia. }
    assert (EC : exists ec, getr R3 (reg 11) = Z_to_bv 64 ec /\ 0 <= ec <= 22).
    { destruct POST3 as [(_ & _ & E & _)|(_ & E & _)]; rewrite r11 in E. exists 0. split. exact E. clear; lia. exists 22. split. exact E. clear; lia. }
    destruct EC as (ec & EC1 & EC2).
    pose proof (tqD_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 42%nat => U R 1 | 58%nat => U R3 1 | 61%nat => U R3 10 | 62%nat => ec | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (cs_of_preserved R2 R3 2 RP3) by inl; exact cR2)]).
    destruct P as (fx4 & R4 & M4v & MG4 & dFR & dFZ & (dMS & dKS & dR1 & dR2)).
    pose proof (ret_to fx4 R4 M4v 0x8ed0c W_8ed0c r F_8ed0c eq_refl D_8ed0c ltac:(rewrite dR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M3 model3 fx3 fx4 R3 0x8ecfc R4 r M4v K HH3 AM3 (msteps_trans _ _ _ _ dMS RET) MG4 dFZ).
    intros M4 model4 HH4 AM4 RT4 AH4 VIS4 MGM4 FRM4.
    assert (E4 : M4 = M3) by (apply mem_eq_of_agree; exact FRM4). subst M4.
    assert (RPF : regs_preserved R R4).
    { apply preserved_by_index. intros k Hk.
      assert (CH : forall k, In k KS_tqD -> In k cs_all -> In k [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> k <> 12%nat -> k <> 15%nat -> In k KS_tqB -> getr R4 (reg k) = getr R (reg k)).
      { intros k' H1 H2 H3' N1 N2 H4. rewrite (dKS k' H1), (cs_of_preserved R2 R3 k' RP3 H2), (cKS k' H3'), K1'. apply bKS. exact H4.
        revert H2. clear. unfold cs_all. cbn [In]. intros H2. repeat (destruct H2 as [<-|H2]; [lia|]). destruct H2. exact N1. exact N2. }
      unfold cs_all in Hk. cbn [In] in Hk.
      destruct Hk as [<-|Hk]. { rewrite dR2. rewrite <- r2, G2. reflexivity. }
      repeat (destruct Hk as [<-|Hk]; [apply CH; [inl | inl | inl | clear; lia | clear; lia | inl] |]). destruct Hk. }
    assert (EK13 : ek L ar LB FF sp TOBIG_SCRB [(o, 32)] M M3).
    { eapply ek_trans. apply (EKF TOBIG_SCRB [(o, 32)] M M1 FRM1). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
      apply (ek_callee L ar LB [] FF [] sp TOBIG_SCRB (sp - 16) DETAIL_SCRB [(o, 32)] [(o, 32)] M1 M3 HP3). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. intros a _ X. exact X. }
    assert (DK13 : dk L ar LB FF sp TOBIG_SCRB M M3).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_callee L ar LB [] FF [] sp TOBIG_SCRB (sp - 16) DETAIL_SCRB [(o, 32)] M1 M3 HP3). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. }
    apply (KONT fx4 R4 M3 model4 LB3 cr3 LK3 A3).
    + split. exact RPF.
      destruct POST3 as [(D1 & D2 & D3 & PP)|(D1 & D3 & PP)].
      * left. split. { split. exact D1. exact D2. }
        split. { rewrite r11, (dKS 11%nat) by inl. exact D3. }
        destruct PP as (st' & Q1 & Q2 & Q3 & Q4 & Q5). exists st'. split. exact Q1. split. exact Q2. split. exact Q3. split. exact Q4.
        apply ahpres_of. exact EK13. eapply astk_defined. exact ASTK3. clear; lia. clear; lia. exact DK13.
      * right. split. exact D1. split. { rewrite r11, (dKS 11%nat) by inl. exact D3. }
        destruct PP as (Q1 & Q2 & Q3 & Q4). split. exact Q1. split. exact Q2. split. exact Q3.
        apply ahpres_of.
        { eapply ek_trans. apply (EKF TOBIG_SCRB [] M M1 FRM1). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
          apply (ek_callee L ar LB [] FF [] sp TOBIG_SCRB (sp - 16) DETAIL_SCRB [] [] M1 M3 Q4). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. intros a _ X. exact X. }
        eapply astk_defined. exact ASTK3. clear; lia. clear; lia. exact DK13.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT3. exact RT4.
    + exact IA3.
    + exact AM4.
    + exact ILK3.
    + exact HH4.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem tobig3_ok : detail_specB L ar IL HI -> tobig3_specB L ar IL HI.
Proof.
  intros DET fx R M model K LB FF LK cr A p o sp r fb neg0 s HH AM HK G10 G11 _ G12 LEN CR G1 RA G2 A32 G4 STK SSH FFR FFR2 FFRS BIG FB3 AOB SZ BYTES BR SRC APART KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite TSCR_EQ in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487184 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 0 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W16 : L5.writable RSEGS MV (sp - 16) 16).
  { apply (proj2 (writable_vis H M (sp - 16) 16 (VIS (sp - 16) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. clear; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (HV2 : 140735332487184 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (OFR : forall a, o <= a < o + 32 -> ~ (sp - 16 <= a < sp - 16 + 16)) by (intros a Ha; clear - Ha OR SLO; lia).
  (* [comment removed for export] *)
  assert (EKF : forall SCR0 W0 M0 M1, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) -> 16 <= SCR0 ->
            ek L ar LB FF sp SCR0 W0 M0 M1).
  { intros SCR0 W0 M0 M1 FRM HS. apply (ek_piece L ar LB FF sp SCR0 W0 M0 M1 (fun a => sp - 16 <= a < sp) FRM). intros a Ha Hc Ho X.
    destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp SCR0 a HH SPT Hc) as [Z1|Z1]. clear - X Z1 HS; lia. clear - X Z1 SLO; lia. }
  destruct (Nat.eq_dec (length s) 0) as [L0|L0].
  { (* [comment removed for export] *)
    assert (Es : s = []) by (destruct s; [reflexivity | discriminate L0]). subst s. cbn [length Z.of_nat] in G11.
    pose proof (trA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => U R 10 | 36%nat => U R 12 | 37%nat => U R 13 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r11; exact G11)]).
    destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR11)).
    pose proof (ret_to fx1 R1 M1v 0x920a8 W_920a8 r F_920a8 eq_refl D_920a8 ltac:(rewrite (aKS 1%nat) by inl; rewrite <- r1; exact G1) (proj1 RA) (proj2 RA)) as RET.
    set (W1 := fun i => sp - 16 <= i < sp).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R TOBIG3 R1 r M1v W1 K HH AM (msteps_trans _ _ _ _ aMS RET) MG1).
    { intros i Hi Hni. apply aFZ. exact Hi. clear - Hni; subst W1; cbn beta in Hni; lia. }
    { intros i Hi Wi. subst W1; cbn beta in Wi. split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    apply (KONT fx1 R1 M1 model1 LB cr LK A).
    - split.
      { apply preserved_by_index. intros k Hk. apply aKS. revert Hk. clear. unfold cs_all. cbn [In]. intros Hk.
        repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk. }
      right. split. left; reflexivity. split. rewrite r11. exact aR11.
      split. reflexivity.
      split. { eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply FRM1. clear - Hi OR; lia. subst W1; cbn beta. intros X. apply (OFR i Hi). clear - X; lia. }
      split. { unfold parse_debit. eapply credit_le_trans. apply adebit_le. exact LY2. apply vblk_pos. apply adebit_le. exact LY2. apply vblk_pos. }
      apply ahpres_of.
      + apply (EKF TOBIG_SCRB [] M M1). exact FRM1. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
      + eapply astk_defined. eapply astk_grows. exact STK. exact MGM1. clear; lia. clear; lia.
      + apply dk_grows. exact MGM1.
    - exact RT1.
    - apply incl_refl.
    - exact AM1.
    - apply incl_refl.
    - exact HH1. }
  (* [comment removed for export] *)
  destruct s as [|b0 t]; [exfalso; apply L0; reflexivity|]. clear L0.
  set (n := Z.of_nat (length (b0 :: t))) in *.
  assert (HVN : 1 <= n <= 4999) by (subst n; cbn [length] in *; clear - LEN; lia).
  pose proof (asrc_range L ar C IL HI LY ILY HIok LB FF LK cr A M _ p n HH SRC ltac:(clear - HVN; lia)) as [P0 P1].
  assert (PFR : forall a, p <= a < p + n -> ~ (sp - 16 <= a < sp - 16 + 16)) by (intros a Ha; clear - Ha P1 SLO; lia).
  assert (B0R : 0 <= b0 < 256) by (inversion BR; assumption).
  assert (B0 : L5.u8_at RSEGS M p b0). { pose proof (BYTES 0%nat ltac:(cbn [length]; clear; lia)) as X. cbn [nth] in X. change (Z.of_nat 0) with 0 in X. replace (p + 0) with p in X by (clear; lia). exact X. }
  pose proof (asrc_vis L ar C IL HI LY ILY HIok LB FF LK cr A M model p n HH SRC) as PVIS.
  assert (B0v : L5.u8_at RSEGS MV p b0). { apply (proj2 (u8_at_vis H M p b0 ltac:(eapply avis_sub; [exact PVIS | clear; lia | clear - HVN; lia]) ltac:(clear - P0; lia) ltac:(clear - P1 SPT HVN; lia))). exact B0. }
  assert (ACCv : aacc MV p 1).
  { apply (aacc_vis H M p 1). eapply aacc_sub. apply (asrc_aacc L ar C IL HI ILY HIok ICok LB FF LK cr A M _ p n HH SRC). clear; lia. clear - HVN; lia.
    intros a Ha. apply (asrc_shadow_vis L ar C IL HI LY ILY HIok ICok LB FF LK cr A M model p n a HH SRC). clear - Ha HVN; lia. }
  pose proof (trB_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R 13 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r10; exact G10) | (rewrite <- r11; exact G11) | (rewrite <- r12; exact G12)]).
  destruct P as (fx1 & R1 & M1v & MG1 & bFR & bFZ & (bMS & bKS & bR2 & bR12 & bR13 & bR14 & bC8)).
  assert (ACC1 : aacc M1v p 1).
  { intros a Ha. unfold byte_at. rewrite bFZ. exact (ACCv a Ha). unfold S, SB. clear - Ha P0 P1 SPT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    unfold S, SB. clear - Ha P0 P1 SPT SLO. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (L5ACHK0.chk_91d08 fx1 R1 M1v p ltac:(unfold S, SB; exact bR12) ltac:(rewrite (bKS 10%nat) by inl; rewrite <- r10; exact G10) ltac:(clear - P0 P1 SPT HVN; lia) ACC1)
    as (R1' & MS1' & K1').
  assert (B01 : L5.u8_at RSEGS M1v p b0). { eapply L5C.u8_at_agree. 4: exact B0v. 2: clear - P0; lia. 2: clear - P1 SPT HVN; lia. intros i Hi. apply bFZ. clear - Hi P0 P1 SPT; lia. apply PFR. clear - Hi HVN; lia. }
  assert (W16b : L5.writable RSEGS M1v (sp - 16) 16) by (eapply L5.writable_grows; [exact MG1 | exact W16]).
  assert (ST1 : L5.img_clear M1v 860160 884736 /\ L5.u64_at RSEGS M1v 911160 2147450880 /\ L5.u32_at RSEGS M1v 911168 1).
  { split. { intros i Hi. rewrite bFZ. apply IMGC. exact Hi. clear - Hi; lia. clear - Hi SPR; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros j Hj. apply bFZ. clear - Hj; lia. clear - Hj SPR; lia. }
    eapply u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros j Hj. apply bFZ. clear - Hj; lia. clear - Hj SPR; lia. }
  destruct ST1 as (IMGC1 & CSB1 & CUAR1).
  set (ng := fst (split_sign (b0 :: t))). set (ds := snd (split_sign (b0 :: t))).
  (* [comment removed for export] *)
  assert (CALL : exists fx2 R2, msteps RSEGS (st fx1 R1' 0x92064 M1v) (st fx2 R2 DETAIL M1v)
      /\ (forall x, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R1' (reg x))
      /\ getr R2 (reg 1) = Z_to_bv 64 0x92098 /\ getr R2 (reg 2) = Z_to_bv 64 (sp - 16)
      /\ getr R2 (reg 10) = Z_to_bv 64 (if ng then p + 1 else p) /\ getr R2 (reg 11) = Z_to_bv 64 (Z.of_nat (length ds))
      /\ getr R2 (reg 12) = Z_to_bv 64 (if ng then 1 else 0) /\ getr R2 (reg 13) = Z_to_bv 64 o).
  { assert (J2 : getr R1' (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite K1' by (clear; lia); exact bR2).
    assert (J10 : getr R1' (reg 10) = Z_to_bv 64 p) by (rewrite K1' by (clear; lia); rewrite (bKS 10%nat) by inl; rewrite <- r10; exact G10).
    assert (J11 : getr R1' (reg 11) = Z_to_bv 64 n) by (rewrite K1' by (clear; lia); rewrite (bKS 11%nat) by inl; rewrite <- r11; exact G11).
    assert (J13 : getr R1' (reg 13) = Z_to_bv 64 o) by (rewrite K1' by (clear; lia); exact bR13).
    assert (HVP : 4096 <= p <= 140737479966720) by (clear - P0 P1 SPT HVN; lia).
    assert (FRP : sp - 16 + 16 <= p \/ p + 1 <= sp - 16) by (right; clear - P1 SLO HVN; lia).
    assert (HVN' : 1 <= n <= 67108863) by (clear - HVN; lia).
    destruct (Z.eq_dec b0 45) as [E45|N45].
    - pose proof (trCm_conc fx1 R1' M1v (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R1' 14 | 56%nat => b0 | 59%nat => U R1' 12 | 60%nat => U R1' 14 | _ => 0 end)) as P.
      cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx2 & R2 & M2v & MG2 & cFR & cFZ & (cMS & cKS & cR1 & cR10 & cR11 & cR12 & _)).
      assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; exact cFZ). subst M2v.
      exists fx2, R2. subst ng ds. rewrite split_sign_cons. rewrite (proj2 (Z.eqb_eq b0 45) E45). cbn [fst snd].
      split. exact cMS. split. { intros x Hx. apply cKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      split. exact cR1. split. { rewrite (cKS 2%nat) by inl. exact J2. } split. exact cR10.
      split. { rewrite cR11. f_equal. subst n. cbn [length]. clear; lia. } split. exact cR12. rewrite (cKS 13%nat) by inl. exact J13.
    - assert (NE : (b0 =? 45) = false) by (apply Z.eqb_neq; exact N45).
      destruct (Z_lt_le_dec b0 45) as [LT|GE].
      + pose proof (trCl_conc fx1 R1' M1v (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R1' 14 | 56%nat => b0 | 59%nat => U R1' 12 | 60%nat => U R1' 14 | _ => 0 end)) as P.
        cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx2 & R2 & M2v & MG2 & cFR & cFZ & (cMS & cKS & cR1 & cR12 & _)).
        assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; exact cFZ). subst M2v.
        exists fx2, R2. subst ng ds. rewrite split_sign_cons, NE. cbn [fst snd].
        split. exact cMS. split. { intros x Hx. apply cKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
        split. exact cR1. split. { rewrite (cKS 2%nat) by inl. exact J2. } split. { rewrite (cKS 10%nat) by inl. exact J10. }
        split. { rewrite (cKS 11%nat) by inl. exact J11. } split. exact cR12. rewrite (cKS 13%nat) by inl. exact J13.
      + pose proof (trCh_conc fx1 R1' M1v (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | 36%nat => o | 37%nat => U R1' 14 | 56%nat => b0 | 59%nat => U R1' 12 | 60%nat => U R1' 14 | _ => 0 end)) as P.
        cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx2 & R2 & M2v & MG2 & cFR & cFZ & (cMS & cKS & cR1 & cR12 & _)).
        assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; exact cFZ). subst M2v.
        exists fx2, R2. subst ng ds. rewrite split_sign_cons, NE. cbn [fst snd].
        split. exact cMS. split. { intros x Hx. apply cKS. revert Hx. clear. cbn [In]. intros Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
        split. exact cR1. split. { rewrite (cKS 2%nat) by inl. exact J2. } split. { rewrite (cKS 10%nat) by inl. exact J10. }
        split. { rewrite (cKS 11%nat) by inl. exact J11. } split. exact cR12. rewrite (cKS 13%nat) by inl. exact J13. }
  destruct CALL as (fx2 & R2 & cMS & cKS & cR1 & cR2 & cR10 & cR11 & cR12 & cR13).
  set (W1 := fun i => sp - 16 <= i < sp).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx2 R TOBIG3 R2 DETAIL M1v W1 K HH AM
           (msteps_trans _ _ _ _ bMS (msteps_trans _ _ _ _ MS1' cMS)) MG1).
  { intros i Hi Hni. apply bFZ. exact Hi. clear - Hni; subst W1; cbn beta in Hni; lia. }
  { intros i Hi Wi. subst W1; cbn beta in Wi. split. apply stack_client. clear - Wi SLO SHI SPT; lia. clear; lia. clear - Wi SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp TOBIG_SCRB) by (eapply astk_grows; [exact STK | exact MGM1]).
  (* [comment removed for export] *)
  set (p' := if ng then p + 1 else p) in *.
  assert (DSF : p <= p' /\ p' + Z.of_nat (length ds) = p + n /\ L5.bytes_at RSEGS M p' ds /\ Forall (fun c => 0 <= c < 256) ds /\ (length ds <= 4999)%nat).
  { subst p' ng ds n. rewrite split_sign_cons. destruct (b0 =? 45); cbn [fst snd length].
    - split. clear; lia. split. clear; lia. split. { intros i Hi. pose proof (BYTES (Datatypes.S i) ltac:(cbn [length]; clear - Hi; lia)) as X. cbn [nth] in X.
        replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (Datatypes.S i)) by (clear; lia). exact X. }
      split. inversion BR; assumption. cbn [length] in LEN. clear - LEN; lia.
    - split. clear; lia. split. clear; lia. split. exact BYTES. split. exact BR. exact LEN. }
  destruct DSF as (PP1 & PP2 & BYT' & BR' & LEN').
  assert (SA16 : (sp - 16) mod 32 = 16). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (DET fx2 R2 M1 model1 K LB FF LK cr A p' o (sp - 16) 0x92098 fb ng ds HH1 AM1 HK).
  - rewrite r10. exact cR10.
  - rewrite r11. exact cR11.
  - intros _. rewrite r12. exact cR12.
  - rewrite r13. exact cR13.
  - exact LEN'.
  - exact CR.
  - rewrite r1. exact cR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact cR2.
  - exact SA16.
  - rewrite r4, (cKS 4%nat) by inl. rewrite K1' by (clear; lia). rewrite (bKS 4%nat) by inl. rewrite <- r4. exact G4.
  - apply (astk_sub ar M1 M1 sp TOBIG_SCRB 16 DETAIL_SCRB ASTK1 (mem_grows_refl M1)). clear; lia.
    rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
    clear - SA16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF0.
    assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (M8 : (sp - TOBIG_SCRB) mod 8 = 0 /\ (sp - 16 - DETAIL_SCRB) mod 8 = 0) by (rewrite TSCR_EQ, DSCR_EQ; clear - A32; Lia.lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (L5BSS.stksh_frame ar M M1 (sp - TOBIG_SCRB) (sp - 16 - DETAIL_SCRB) (sp - 16) sp SSH);
      [ rewrite TSCR_EQ, DSCR_EQ; clear; lia | exact (proj1 M8) | exact (proj2 M8) | rewrite TSCR_EQ; clear - SLO; lia | rewrite TSCR_EQ; clear - SLO SPR; lia
      | exact TOP | clear - SPT; lia | clear - SPR; lia | ].
    intros a Ha Hn. apply FRM1. exact Ha. subst W1; cbn beta. exact Hn.
  - exact FFR.
  - exact FFR2.
  - eapply ffrs_le. exact FFRS. clear; lia.
  - eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply FRM1. clear - Hi OR; lia. subst W1; cbn beta. intros X. apply (OFR i Hi). clear - X; lia.
  - exact FB3.
  - exact AOB.
  - intros j Hj. unfold byte_at. rewrite FRM1. exact (SZ j Hj). unfold S, SB; clear - Hj OR; lia. subst W1; cbn beta. unfold S, SB. clear - Hj OR SLO SPT. lia.
  - eapply L5C.bytes_at_agree. 4: exact BYT'. 2: clear - PP1 P0; lia. 2: clear - PP2 P1 SPT; lia. intros i Hi. apply FRM1. clear - Hi PP1 PP2 P0 P1 SPT; lia.
    subst W1; cbn beta. intros X. apply (PFR i). clear - Hi PP1 PP2; lia. clear - X; lia.
  - exact BR'.
  - eapply (asrc_keep IL LB LB FF FF M M1). eapply asrc_sub. exact SRC. exact PP1. clear - PP2; lia. clear; lia. apply incl_refl. apply incl_refl.
    intros so AO SZo j Hj. unfold byte_at. rewrite FRM1. exact (SZo j Hj).
    { pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp 0 HH AO ltac:(clear; lia) ltac:(reflexivity)) as (OR' & _). unfold S, SB; clear - Hj OR'; lia. }
    { pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp 0 HH AO ltac:(clear; lia) ltac:(reflexivity)) as (OR' & _). subst W1; cbn beta. unfold S, SB. clear - Hj OR' SLO SPT. lia. }
  - clear - APART PP1 PP2. lia.
  - (* [comment removed for export] *)
    intros fx3 R3 M3 model3 LB3 cr3 LK3 A3 (RP3 & POST3) RT3 IA3 AM3 ILK3 HH3.
    pose proof (vis_pack L ar C HI LY HIok LB3 FF LK3 cr3 A3 M3 model3 HH3) as (HOFF3 & VIS3 & _).
    pose proof (statics_vis LB3 FF LK3 cr3 A3 M3 model3 HH3) as (IMGC3 & CSB3 & CUAR3).
    set (H3 := ahid A3 model3) in *. set (MV3 := mrestrict H3 M3) in *.
    assert (HP3 : ahpres L ar LB FF (sp - 16) DETAIL_SCRB [(o, 32)] M1 M3).
    { destruct POST3 as [(_ & _ & _ & PP)|(_ & _ & PP)].
      - destruct PP as (st' & _ & _ & _ & _ & HP). exact HP.
      - destruct PP as (_ & _ & _ & (E & D & Kk)). split. { intros a (Ha & Hc & _). apply E. split. exact Ha. split. exact Hc. intros rr []. } split. exact D. exact Kk. }
    assert (ASTK3 : astk ar M3 sp TOBIG_SCRB).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M1 M1 M3 _ sp _ (sp - 16) DETAIL_SCRB [(o, 32)] HH1 ASTK1 (mem_grows_refl M1) HP3).
      rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. }
    assert (W16c : L5.writable RSEGS MV3 (sp - 16) 16).
    { apply (proj2 (writable_vis H3 M3 (sp - 16) 16 (VIS3 (sp - 16) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M3 sp). exact ASTK3. rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. clear; lia. }
    assert (C8v : L5.u64_at RSEGS MV3 (sp - 8) (U R 1)).
    { apply (proj2 (u64_at_vis H3 M3 (sp - 8) _ (VIS3 (sp - 8) 8 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply L5C.u64_at_agree. 4: exact bC8. 2: clear - SPR; lia. 2: clear - SPR; lia. intros j Hj.
      rewrite (proj1 HP3 j). 2:{ split. clear - Hj SPR; lia. split. apply stack_client. clear - Hj SLO SHI SPT; lia. clear - Hj; lia.
        intros rr [E|[]]. subst rr. unfold L5.in_rng; cbn [fst snd]. clear - Hj OR SLO; lia. }
      apply EQ1. replace j with ((sp - 16) + (j - (sp - 16))) by (clear; lia). apply (VIS (sp - 16) 16). clear - SLO; lia. clear - SPR; lia. clear - Hj; lia. }
    assert (EC : exists ec, getr R3 (reg 11) = Z_to_bv 64 ec /\ 0 <= ec <= 22).
    { destruct POST3 as [(_ & _ & E & _)|(_ & E & _)]; rewrite r11 in E. exists 0. split. exact E. clear; lia. exists 22. split. exact E. clear; lia. }
    destruct EC as (ec & EC1 & EC2).
    pose proof (trD_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 42%nat => U R 1 | 58%nat => U R3 1 | 61%nat => U R3 10 | 62%nat => ec | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (cs_of_preserved R2 R3 2 RP3) by inl; exact cR2)]).
    destruct P as (fx4 & R4 & M4v & MG4 & dFR & dFZ & (dMS & dKS & dR1 & dR2)).
    pose proof (ret_to fx4 R4 M4v 0x920a8 W_920a8 r F_920a8 eq_refl D_920a8 ltac:(rewrite dR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M3 model3 fx3 fx4 R3 0x92098 R4 r M4v K HH3 AM3 (msteps_trans _ _ _ _ dMS RET) MG4 dFZ).
    intros M4 model4 HH4 AM4 RT4 AH4 VIS4 MGM4 FRM4.
    assert (E4 : M4 = M3) by (apply mem_eq_of_agree; exact FRM4). subst M4.
    assert (RPF : regs_preserved R R4).
    { apply preserved_by_index. intros k Hk.
      assert (CH : forall k, In k KS_trD -> In k cs_all -> In k [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> k <> 12%nat -> k <> 14%nat -> In k KS_trB -> getr R4 (reg k) = getr R (reg k)).
      { intros k' H1 H2 H3' N1 N2 H4. rewrite (dKS k' H1), (cs_of_preserved R2 R3 k' RP3 H2), (cKS k' H3'), K1'. apply bKS. exact H4.
        revert H2. clear. unfold cs_all. cbn [In]. intros H2. repeat (destruct H2 as [<-|H2]; [lia|]). destruct H2. exact N1. exact N2. }
      unfold cs_all in Hk. cbn [In] in Hk.
      destruct Hk as [<-|Hk]. { rewrite dR2. rewrite <- r2, G2. reflexivity. }
      repeat (destruct Hk as [<-|Hk]; [apply CH; [inl | inl | inl | clear; lia | clear; lia | inl] |]). destruct Hk. }
    assert (EK13 : ek L ar LB FF sp TOBIG_SCRB [(o, 32)] M M3).
    { eapply ek_trans. apply (EKF TOBIG_SCRB [(o, 32)] M M1 FRM1). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
      apply (ek_callee L ar LB [] FF [] sp TOBIG_SCRB (sp - 16) DETAIL_SCRB [(o, 32)] [(o, 32)] M1 M3 HP3). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. intros a _ X. exact X. }
    assert (DK13 : dk L ar LB FF sp TOBIG_SCRB M M3).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_callee L ar LB [] FF [] sp TOBIG_SCRB (sp - 16) DETAIL_SCRB [(o, 32)] M1 M3 HP3). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. }
    apply (KONT fx4 R4 M3 model4 LB3 cr3 LK3 A3).
    + split. exact RPF.
      destruct POST3 as [(D1 & D2 & D3 & PP)|(D1 & D3 & PP)].
      * left. split. { split. exact D1. exact D2. }
        split. { rewrite r11, (dKS 11%nat) by inl. exact D3. }
        destruct PP as (st' & Q1 & Q2 & Q3 & Q4 & Q5). exists st'. split. exact Q1. split. exact Q2. split. exact Q3. split. exact Q4.
        apply ahpres_of. exact EK13. eapply astk_defined. exact ASTK3. clear; lia. clear; lia. exact DK13.
      * right. split. exact D1. split. { rewrite r11, (dKS 11%nat) by inl. exact D3. }
        destruct PP as (Q1 & Q2 & Q3 & Q4). split. exact Q1. split. exact Q2. split. exact Q3.
        apply ahpres_of.
        { eapply ek_trans. apply (EKF TOBIG_SCRB [] M M1 FRM1). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia.
          apply (ek_callee L ar LB [] FF [] sp TOBIG_SCRB (sp - 16) DETAIL_SCRB [] [] M1 M3 Q4). rewrite ?TSCR_EQ, ?DSCR_EQ; clear; lia. clear; lia. intros a _ X. exact X. }
        eapply astk_defined. exact ASTK3. clear; lia. clear; lia. exact DK13.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT3. exact RT4.
    + exact IA3.
    + exact AM4.
    + exact ILK3.
    + exact HH4.
Qed.
(* [comment removed for export] *)

End WithIface.
End SCFG_1.
End L5ATB.

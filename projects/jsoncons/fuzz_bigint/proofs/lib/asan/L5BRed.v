(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun Bo0_code_90368_91368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BRedP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ARED.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AREDP.
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

Definition REDUCE : Z := 0x90d58.
Definition HEADL : Z := 0x90e24.
(* [comment removed for export] *)
Definition KS : list nat := [3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%nat.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma r28 : (28%bv : bv 5) = reg 28. Proof. apply bv_eq; reflexivity. Qed.
(* [comment removed for export] *)
Local Lemma fz segs (p : word) (z : Z) w : fetch_word segs p = Some w -> p = Z_to_bv 64 z -> fetch_word segs (Z_to_bv 64 z) = Some w.
Proof. intros H E. rewrite <- E. exact H. Qed.
Lemma br_90af0_tk fx R M : getr R (reg 28) <> Z_to_bv 64 0 -> msteps RSEGS (st fx R 0x90e44 M) (st fx R 0x90e68 M).
Proof.
  intros H. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 0x90e68) with (btgt (Z_to_bv 64 0x90e44) (bv_signed (36%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
  eapply (step_bne_tk RSEGS R _ M _ _ 28%bv 0%bv _ (fz _ _ 0x90e44 _ F_90e44 ltac:(apply bv_eq; reflexivity)) eq_refl D_90e44).
  rewrite getr_zero, r28. unfold c_eq. apply bv_eqb_neq. exact H.
Qed.
Lemma br_90af0_ft fx R M : getr R (reg 28) = Z_to_bv 64 0 -> msteps RSEGS (st fx R 0x90e44 M) (st fx R 0x90e48 M).
Proof.
  intros H. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 0x90e48) with (v_addi (Z_to_bv 64 0x90e44) 4) by (apply bv_eq; reflexivity).
  eapply (step_bne_ft RSEGS R _ M _ _ 28%bv 0%bv _ (fz _ _ 0x90e44 _ F_90e44 ltac:(apply bv_eq; reflexivity)) eq_refl D_90e44).
  rewrite getr_zero, r28, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Record rfacts (M : word -> option byte) (sp o fb d cap : Z) : Prop := RF {
  rf_sp : 140735332487184 <= sp <= 140737488355328 /\ sp mod 16 = 0;
  rf_w16 : L5.writable RSEGS M (sp - 16) 16;
  rf_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  rf_o : 6504448 <= o <= 140737488355296 /\ o mod 8 = 0 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\ (sp - 16 + 16 <= o \/ o + 32 <= sp - 16);
  rf_oz : L5KA.zeros_at M (o / 8 + SB) 4;
  rf_ow : L5.writable RSEGS M o 32;
  rf_fb : L5.u8_at RSEGS M o fb /\ 0 <= fb <= 255;
  rf_d : (4096 <= d /\ d + 8 * cap <= 140737488355328) /\ d mod 8 = 0 /\ (2147446784 + 17592186048512 <= d \/ d + 8 * cap <= 2147446784) /\ 1 <= cap <= 134217728
         /\ (sp - 16 + 16 <= d \/ d + 8 * cap <= sp - 16) /\ (o + 16 <= d \/ d + 8 * cap <= o);
  rf_dw : L5.writable RSEGS M d (8 * cap);
  rf_dz : L5KA.zeros_at M (d / 8 + SB) cap }.

Lemma rfacts_keep M M' sp o fb d cap :
  rfacts M sp o fb d cap -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (o + 8 <= i < o + 16) -> ~ (sp - 16 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> rfacts M' sp o fb d cap.
Proof.
  intros [S1 W [I [C1 C2]] O OZ OW [FB FR] D DW DZ] G K.
  assert (AG : forall a n, (a + n <= o + 8 \/ o + 16 <= a) -> (a + n <= sp - 16 \/ sp <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M' a n).
  { intros a n Ha Hs H0 Hn i Hi. apply K. lia. lia. lia. }
  constructor; auto.
  - eapply L5.writable_grows; eauto.
  - split. { intros a Ha. rewrite K. apply I. exact Ha. clear - Ha; lia. clear - Ha O; lia. clear - Ha S1; lia. }
    split. eapply L5C.u64_at_agree. apply AG. clear - O; lia. clear - S1; lia. clear; lia. clear; lia. clear; lia. clear; lia. exact C1.
    eapply u32_at_agree1. 4: exact C2. intros i Hi; apply K. clear - Hi; lia. clear - Hi O; lia. clear - Hi S1; lia. clear; lia. clear; lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact OZ. intros i Hi. apply K. clear - Hi O; unfold SB in *; lia. clear - Hi O; unfold SB in *; lia. clear - Hi O S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - eapply L5.writable_grows; eauto.
  - split. eapply L5C.u8_at_agree. apply AG. clear; lia. clear - O; lia. clear - O; lia. clear - O; lia. clear - O; lia. clear - O; lia. exact FB. exact FR.
  - eapply L5.writable_grows; eauto.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact DZ. intros i Hi. apply K. clear - Hi D; unfold SB in *; lia. clear - Hi D O; unfold SB in *; lia. clear - Hi D S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma KS_trans R R' R'' : (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> (forall x, In x KS -> getr R'' (reg x) = getr R' (reg x)) ->
  forall x, In x KS -> getr R'' (reg x) = getr R (reg x).
Proof. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.

(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (sp o d : Z) (L : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R (reg 5) = Z_to_bv 64 (Z.of_nat L - 1) /\ getr R (reg 10) = Z_to_bv 64 o /\
  getr R (reg 11) = Z_to_bv 64 (o + 8) /\ getr R (reg 12) = Z_to_bv 64 (d + 8 * Z.of_nat L - 8) /\ getr R (reg 13) = Z_to_bv 64 SB /\
  getr R (reg 14) = Z_to_bv 64 (o / 8) /\ getr R (reg 15) = Z_to_bv 64 ((o + 8) / 8 + SB) /\ getr R (reg 16) = Z_to_bv 64 d /\
  getr R (reg 17) = Z_to_bv 64 0 /\ getr R (reg 6) = Z_to_bv 64 9 /\ getr R (reg 28) = Z_to_bv 64 (d + 8 * Z.of_nat L - 8).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rloop (L : nat) : forall fx R M (sp o fb d cap r : Z) (ws : list Z),
  rfacts M sp o fb d cap -> L5.limbs_at RSEGS M d ws -> L5W.words_ok ws -> (L <= length ws)%nat -> Z.of_nat (length ws) <= cap ->
  at_head R sp o d L -> (1 <= L)%nat -> L5.u64_at RSEGS M (o + 8) (Z.of_nat L) -> L5.u64_at RSEGS M (sp - 8) r -> L5.ra_ok r ->
  exists fx' R' M' (n' : nat),
    msteps RSEGS (st fx R HEADL M) (st fx' R' r M')
    /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp
    /\ (n' <= L)%nat
    /\ L5.u64_at RSEGS M' (o + 8) (Z.of_nat n')
    /\ L5.u8_at RSEGS M' o (if Nat.eqb n' 0 then Z.land fb 253 else fb)
    /\ ((1 <= n')%nat -> L5W.nth_w ws (n' - 1) <> 0)
    /\ (forall i : nat, (n' <= i < L)%nat -> L5W.nth_w ws i = 0)
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (o <= i < o + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ mem_grows M M'.
Proof.
  induction L as [|L IH]; intros fx R M sp o fb d cap r ws RFM WS WO WL WC AT HL O8 C8 RA. { exfalso. clear - HL. lia. }
  pose proof RFM as [[SPR A16] W16 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW [FB FBR] (DR & D8 & DBIG & CAPR & FRD & OD) DW DZ].
  destruct AT as (A2 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16r & A17 & A6 & A28).
  set (X := L5W.nth_w ws L).
  assert (RX : 0 <= X < 2 ^ 64) by (apply L5W.words_ok_nth; exact WO).
  assert (OX : L5.u64_at RSEGS M (8 * Z.of_nat (Datatypes.S L) + d - 8) X). { replace (8 * Z.of_nat (Datatypes.S L) + d - 8) with (d + 8 * Z.of_nat L) by (clear; lia). apply WS. clear - WL; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (HVL : 1 <= Z.of_nat (Datatypes.S L) <= 134217728) by (clear - WL WC CAPR; lia). assert (HVCL : 0 <= cap - Z.of_nat (Datatypes.S L) <= 134217728) by (clear - WL WC CAPR; lia).
  (* [comment removed for export] *)
  pose proof (rdaL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat (Datatypes.S L) | 35%nat => fb | 36%nat => d | 37%nat => cap | 38%nat => X
                | 43%nat => U R 1 | 45%nat => U R 7 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR7 & lR28)).
  assert (EM1 : M1 = M). { apply functional_extensionality. intros a. apply lFR. }
  subst M1.
  assert (K1 : forall k, In k [2; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%nat -> getr R1 (reg k) = getr R (reg k)). { intros k Hk. apply lKS. revert Hk. apply (L5K.incl_b _ KS_rdaL); vm_compute; reflexivity. }
  destruct (Z.eq_dec X 0) as [X0 | XNZ].
  - (* [comment removed for export] *)
    pose proof (br_90af0_ft fx1 R1 M ltac:(rewrite lR28, X0; reflexivity)) as MB.
    destruct (Nat.eq_dec L 0) as [L0 | Lpos].
    + (* [comment removed for export] *)
      subst L. cbn [Z.of_nat Pos.of_succ_nat] in *.
      pose proof (rdaPZ_conc fx1 R1 M (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => fb | 36%nat => d | 37%nat => cap | 43%nat => U R1 1 | 44%nat => r | 46%nat => U R1 28 | _ => 0 end)) as P.
      cbn beta iota in P.
      assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
      destruct P as (fx2 & R2 & M2 & MG2 & qFR & qFZ & (qMS & qKS & qR1 & qR2 & qR5 & qR11 & qR12 & qR13 & qR28 & qB0 & qQ8)).
      pose proof (ret_to fx2 R2 M2 0x90e98 W_90e98 r F_90e98 eq_refl D_90e98 qR1 (proj1 RA) (proj2 RA)) as RET.
      exists fx2, R2, M2, 0%nat.
      split. { eapply msteps_trans. exact lMS. eapply msteps_trans. exact MB. eapply msteps_trans. exact qMS. exact RET. }
      split. { intros k Hk. rewrite (qKS k). apply lKS. revert Hk; apply (L5K.incl_b _ KS_rdaL); vm_compute; reflexivity. revert Hk; apply (L5K.incl_b _ KS_rdaPZ); vm_compute; reflexivity. }
      split. exact qR2. split. clear; lia. split. exact qQ8. split. exact qB0. split. intros; exfalso; lia.
      split. { intros i Hi. replace i with 0%nat by lia. exact X0. }
      split. { intros i Hi Hn. apply qFZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } exact MG2.
    + (* [comment removed for export] *)
      pose proof (rdaP_conc fx1 R1 M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat (Datatypes.S L) | 35%nat => fb | 36%nat => d | 37%nat => cap | 43%nat => U R1 1 | 46%nat => U R1 28 | _ => 0 end)) as P.
      cbn beta iota in P.
      assert (HVL2 : 2 <= Z.of_nat (Datatypes.S L) <= 134217728) by (clear - Lpos HVL; lia).
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
      destruct P as (fx2 & R2 & M2 & MG2 & pFR & pFZ & (pMS & pKS & pR5 & pR12 & pR28 & pQ8)).
      assert (RF2 : rfacts M2 sp o fb d cap). { eapply rfacts_keep. exact RFM. exact MG2. intros i Hi Hn _. apply pFZ. exact Hi. clear - Hn; lia. }
      assert (WS2 : L5.limbs_at RSEGS M2 d ws).
      { intros i Hi. eapply L5C.u64_at_agree. 4: exact (WS i Hi). 2: clear - DR; lia. 2:{ clear - Hi WC DR CAPR. lia. } intros j Hj. apply pFZ. clear - Hj Hi WC DR CAPR; lia. clear - Hj Hi WC OD; lia. }
      assert (C82 : L5.u64_at RSEGS M2 (sp - 8) r).
      { eapply L5C.u64_at_agree. 4: exact C8. 2: clear - SPR; lia. 2: clear - SPR; lia. intros j Hj. apply pFZ. clear - Hj SPR; lia. clear - Hj FRO; lia. }
      destruct (IH fx2 R2 M2 sp o fb d cap r ws RF2 WS2 WO ltac:(clear - WL; lia) WC) as (fx' & R' & M' & n' & MS & K & R2' & Hn' & Q8 & Q0 & TOP & ZER & FR' & GR').
      { unfold at_head. repeat split.
        - rewrite (pKS 2%nat) by inl. exact (proj1 (conj A2 I) ) || (rewrite (K1 2%nat) by inl; exact A2).
        - rewrite pR5. f_equal. clear; lia.
        - rewrite (pKS 10%nat) by inl. rewrite (K1 10%nat) by inl. exact A10.
        - rewrite (pKS 11%nat) by inl. rewrite (K1 11%nat) by inl. exact A11.
        - rewrite pR12. f_equal. clear; lia.
        - rewrite (pKS 13%nat) by inl. rewrite (K1 13%nat) by inl. exact A13.
        - rewrite (pKS 14%nat) by inl. rewrite (K1 14%nat) by inl. exact A14.
        - rewrite (pKS 15%nat) by inl. rewrite (K1 15%nat) by inl. exact A15.
        - rewrite (pKS 16%nat) by inl. rewrite (K1 16%nat) by inl. exact A16r.
        - rewrite (pKS 17%nat) by inl. rewrite (K1 17%nat) by inl. exact A17.
        - rewrite (pKS 6%nat) by inl. rewrite (K1 6%nat) by inl. exact A6.
        - rewrite pR28. f_equal. clear; lia. }
      { clear - Lpos; lia. } { replace (Z.of_nat L) with (Z.of_nat (Datatypes.S L) - 1) by (clear; lia). exact pQ8. } { exact C82. } { exact RA. }
      exists fx', R', M', n'.
      split. { eapply msteps_trans. exact lMS. eapply msteps_trans. exact MB. eapply msteps_trans. exact pMS. exact MS. }
      split. { intros k Hk. rewrite (K k Hk). rewrite (pKS k). apply lKS. revert Hk; apply (L5K.incl_b _ KS_rdaL); vm_compute; reflexivity. revert Hk; apply (L5K.incl_b _ KS_rdaP); vm_compute; reflexivity. }
      split. exact R2'. split. clear - Hn'; lia. split. exact Q8. split. exact Q0. split. exact TOP.
      split. { intros i Hi. destruct (Nat.eq_dec i L) as [->|NE]. exact X0. apply ZER. clear - Hi NE; lia. }
      split. { intros a Ha Hn. rewrite (FR' a Ha Hn). apply pFZ. exact Ha. clear - Hn; lia. } eapply mem_grows_trans; eauto.
  - (* [comment removed for export] *)
    pose proof (br_90af0_tk fx1 R1 M ltac:(rewrite lR28; intros E; apply XNZ; apply (f_equal bv_unsigned) in E; rewrite !L5.unsigned_lit in E by (clear - RX; lia); exact E)) as MB.
    pose proof (rdaK_conc fx1 R1 M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat (Datatypes.S L) | 35%nat => fb | 36%nat => d | 37%nat => cap | 43%nat => U R1 1 | 44%nat => r
                | 45%nat => U R1 7 | 46%nat => U R1 28 | _ => 0 end)) as P.
    cbn beta iota in P.
    assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
    destruct P as (fx2 & R2 & M2 & MG2 & kFR & kFZ & (kMS & kKS & kR1 & kR2 & kR12)).
    assert (EM2 : M2 = M). { apply functional_extensionality. intros a. apply kFR. } subst M2.
    pose proof (ret_to fx2 R2 M 0x90e98 W_90e98 r F_90e98 eq_refl D_90e98 kR1 (proj1 RA) (proj2 RA)) as RET.
    exists fx2, R2, M, (Datatypes.S L).
    split. { eapply msteps_trans. exact lMS. eapply msteps_trans. exact MB. eapply msteps_trans. exact kMS. exact RET. }
    split. { intros k Hk. rewrite (kKS k). apply lKS. revert Hk; apply (L5K.incl_b _ KS_rdaL); vm_compute; reflexivity. revert Hk; apply (L5K.incl_b _ KS_rdaK); vm_compute; reflexivity. }
    split. exact kR2. split. clear; lia. split. exact O8. split. cbn [Nat.eqb]. exact FB.
    split. { intros _. replace (Datatypes.S L - 1)%nat with L by (clear; lia). exact XNZ. }
    split. { intros; exfalso; lia. }
    split. { intros; reflexivity. } apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma testbit0_land253 fb : Z.testbit (Z.land fb 253) 0 = Z.testbit fb 0.
Proof. rewrite Z.land_spec. change (Z.testbit 253 0) with true. apply Bool.andb_true_r. Qed.

Definition reduce_post (M M' : word -> option byte) (o sp : Z) (b : L5.bigobj) (ws : list Z) (R R' : bvmap 5 word) : Prop :=
  let n' := L5W.rlen ws in
  L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land (L5.bo_fb b) 253 else L5.bo_fb b) n' (L5.bo_st b))
  /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
  /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (o <= i < o + 16) -> ~ (sp - 16 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.

Theorem reduce_run (fx : FPState) R M (o sp r : Z) (b : L5.bigobj) (ws : list Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp ->
  140735332487184 <= sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M (sp - 16) 16 ->
  L5.img_clear M 860160 884736 -> L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  6504448 <= o <= 140737488355296 -> o mod 8 = 0 -> (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) -> (sp - 16 + 16 <= o \/ o + 32 <= sp - 16) ->
  L5KA.zeros_at M (o / 8 + SB) 4 -> L5.writable RSEGS M o 32 ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
  (let d := L5.bo_data o b in let cap := L5.bo_cap b in
   (2147446784 + 17592186048512 <= d \/ d + 8 * cap <= 2147446784) /\ (sp - 16 + 16 <= d \/ d + 8 * cap <= sp - 16) /\ (o + 16 <= d \/ d + 8 * cap <= o)
   /\ L5.writable RSEGS M d (8 * cap) /\ L5KA.zeros_at M (d / 8 + SB) cap /\ cap <= 2 ^ 27) ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R REDUCE M) (st fx' R' r M') /\ reduce_post M M' o sp b ws R R'.
Proof.
  intros H10 H1 RA H2 SPR A16 W16 IMGC CSB CUAR OR O8a OBIG FRO OZ OW OB OL (DBIG & FRD & OD & DW & DZ & CAP8). unfold REDUCE.
  destruct b as [fb len sto]. unfold L5.big_at in OB. unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct OB as (O0 & Ffb & O8 & OST). destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  set (cap := match sto with L5.BInl _ _ => 2 | L5.BDyn c _ => c end) in *.
  assert (WS : L5.limbs_at RSEGS M d ws /\ (4096 <= d /\ d + 8 * cap <= 140737488355328) /\ d mod 8 = 0 /\ 1 <= cap <= 134217728 /\ Z.of_nat len <= cap).
  { subst d cap. destruct sto as [v0 v1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1). split. { rewrite LAT. intros i Hi. rewrite length_firstn in Hi. cbn [length Nat.min] in Hi.
        destruct i as [|[|i]]. { destruct len as [|ly]. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by (clear; lia). exact O16. }
        { destruct len as [|[|ly]]. exfalso; clear - Hi; lia. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by (clear; lia). exact O24. }
        exfalso. destruct len as [|[|[|ly]]]; cbn in Hi; clear - Hi Hl2; lia. }
      split. clear - OR; lia. split. { clear - O8a. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. } split. clear; lia. clear - Hl2; lia.
    - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split. exact LAT. split. clear - Q4096 Q47 Hcap; lia. split. exact Q8. split. clear - Hcap CAP8; lia. exact Hlc. }
  destruct WS as (WS & DR & D8 & CAPR & LC).
  assert (WO : L5W.words_ok ws) by exact Rws.
  assert (RFM : rfacts M sp o fb d cap). { constructor; auto. split. exact O0. clear - Ffb; lia. destruct DR as [DR1 DR2]. repeat split; try assumption; clear - CAPR; lia. }
  assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  (* [comment removed for export] *)
  assert (PACK : forall (fx' : FPState) R' M' (n' : nat),
    (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> getr R' (reg 2) = Z_to_bv 64 sp -> (n' <= len)%nat ->
    L5.u64_at RSEGS M' (o + 8) (Z.of_nat n') -> L5.u8_at RSEGS M' o (if Nat.eqb n' 0 then Z.land fb 253 else fb) ->
    ((1 <= n')%nat -> L5W.nth_w ws (n' - 1) <> 0) -> (forall i : nat, (n' <= i < len)%nat -> L5W.nth_w ws i = 0) ->
    (forall i, 0 <= i < 2 ^ 64 -> ~ (o <= i < o + 16) -> ~ (sp - 16 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mem_grows M M' ->
    reduce_post M M' o sp (L5.BO fb len sto) ws R R').
  { intros fx' R' M' n' K R2' Hn Q8 Q0 TOP ZER FR' GR'.
    assert (RL : L5W.rlen ws = n').
    { apply L5W.rlen_charact. rewrite Lws; exact Hn. intros i Hi. apply ZER. rewrite <- Lws; exact Hi. destruct (Nat.eq_dec n' 0). left; exact e. right. apply TOP. lia. }
    unfold reduce_post. cbn [L5.bo_fb L5.bo_len L5.bo_st]. rewrite RL.
    assert (AGH : forall a v, o + 16 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR'. clear - Hj Ha Hb OR; lia. clear - Hj Ha; lia. clear - Hj Ha Hb FRO; lia. }
    split. { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact Q0.
             split. { destruct (Nat.eqb n' 0). pose proof (L5K.land_le_r fb 253 ltac:(clear - Ffb; lia) ltac:(clear; lia)). clear - H Ffb; lia. exact Ffb. }
             split. exact Q8.
             destruct sto as [v0 v1 | c q].
             - destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1). repeat split; try (clear - Hn Hl2 Rv0 Rv1; lia).
               + destruct (Nat.eqb n' 0); [rewrite testbit0_land253|]; exact B0.
               + apply AGH. clear; lia. clear; lia. exact O16.
               + apply AGH. clear; lia. clear; lia. exact O24.
             - destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & QLO & QHI & HAP). repeat split; try assumption; try (clear - Hn Hlc Hcap; lia).
               + destruct (Nat.eqb n' 0); [rewrite testbit0_land253|]; exact B0.
               + apply AGH. clear; lia. clear; lia. exact O16.
               + apply AGH. clear; lia. clear; lia. exact O24. }
    split. exact K. split. exact R2'. split. { rewrite (K 10%nat) by inl. exact H10. } split. exact FR'. exact GR'. }
  destruct (Nat.eq_dec len 0) as [L0 | Lpos].
  - (* [comment removed for export] *)
    rewrite L0 in *. 
    pose proof (rda0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
    assert (O80 : L5.u64_at RSEGS M (o + 8) 0) by exact O8.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx2 & R2 & M2 & MG2 & zFR & zFZ & (zMS & zKS & zR11 & zR12 & zR13 & zR14 & zR15 & zB0)).
    pose proof (ret_to fx2 R2 M2 0x90e98 W_90e98 r F_90e98 eq_refl D_90e98 ltac:(rewrite (zKS 1%nat) by inl; exact H1) (proj1 RA) (proj2 RA)) as RET.
    exists fx2, R2, M2. split. { eapply msteps_trans. exact zMS. exact RET. }
    apply (PACK fx2 R2 M2 0%nat). { intros k Hk. apply zKS. revert Hk; apply (L5K.incl_b _ KS_rda0); vm_compute; reflexivity. } { rewrite (zKS 2%nat) by inl. exact H2. } clear; lia.
    + eapply L5C.u64_at_agree. 4: exact O80. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply zFZ. clear - Hj OR; lia. clear - Hj FRO; lia. clear - Hj; lia.
    + exact zB0.
    + intros; exfalso; lia.
    + intros; exfalso; lia.
    + intros a Ha Hn Hs; apply zFZ. exact Ha. clear - Hs; lia. clear - Hn; lia. + exact MG2.
  - assert (HVL : 1 <= Z.of_nat len <= 134217728) by (clear - Lpos LC CAPR; lia).
    assert (ENTRY : exists fx1 R1 M1, msteps RSEGS (st fx R 0x90d58 M) (st fx1 R1 HEADL M1) /\ mem_grows M M1
              /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
              /\ (forall x, In x KS -> getr R1 (reg x) = getr R (reg x)) /\ at_head R1 sp o d len /\ L5.u64_at RSEGS M1 (sp - 8) r).
    { subst d cap. destruct sto as [v0 v1 | c q].
      + destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1).
        assert (HVL2 : 1 <= Z.of_nat len <= 2) by (clear - Lpos Hl2; lia).
        pose proof (rdaAi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR2 & iR5 & iR6 & iR11 & iR12 & iR13 & iR14 & iR15 & iR16 & iR17 & iR28 & iC8)).
        exists fx1, R1, M1. split. exact iMS. split. exact MG1. split. { intros i Hi Hn. apply iFZ. exact Hi. clear - Hn; lia. }
        split. { intros k Hk. apply iKS. revert Hk; apply (L5K.incl_b _ KS_rdaAi); vm_compute; reflexivity. }
        split. { unfold at_head. repeat split; try assumption. rewrite (iKS 10%nat) by inl; exact H10. rewrite iR12; f_equal; clear; lia. rewrite iR28; f_equal; clear; lia. }
        unfold U in iC8. rewrite H1, L5.unsigned_lit in iC8 by exact HVR. exact iC8.
      + destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
        assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVCL : 0 <= c - Z.of_nat len <= 134217728) by (clear - Hlc Hcap CAP8; lia).
        pose proof (rdaAd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx1 & R1 & M1 & MG1 & dFR & dFZ & (dMS & dKS & dR2 & dR5 & dR6 & dR11 & dR12 & dR13 & dR14 & dR15 & dR16 & dR17 & dR28 & dC8)).
        exists fx1, R1, M1. split. exact dMS. split. exact MG1. split. { intros i Hi Hn. apply dFZ. exact Hi. clear - Hn; lia. }
        split. { intros k Hk. apply dKS. revert Hk; apply (L5K.incl_b _ KS_rdaAd); vm_compute; reflexivity. }
        split. { unfold at_head. repeat split; try assumption. rewrite (dKS 10%nat) by inl; exact H10. rewrite dR12; f_equal; clear; lia. rewrite dR28; f_equal; clear; lia. }
        unfold U in dC8. rewrite H1, L5.unsigned_lit in dC8 by exact HVR. exact dC8. }
    destruct ENTRY as (fx1 & R1 & M1 & MS1 & MG1 & FZ1 & K1 & AT1 & C8).
    assert (RF1 : rfacts M1 sp o fb d cap). { eapply rfacts_keep. exact RFM. exact MG1. intros i Hi _ Hs. apply FZ1. exact Hi. exact Hs. }
    assert (WS1 : L5.limbs_at RSEGS M1 d ws).
    { intros i Hi. eapply L5C.u64_at_agree. 4: exact (WS i Hi). 2: clear - DR; lia. 2:{ rewrite Lws in Hi. clear - Hi LC DR CAPR. lia. } intros j Hj. apply FZ1. rewrite Lws in Hi; clear - Hj Hi LC DR CAPR; lia. rewrite Lws in Hi; clear - Hj Hi LC FRD; lia. }
    assert (O81 : L5.u64_at RSEGS M1 (o + 8) (Z.of_nat len)).
    { eapply L5C.u64_at_agree. 4: exact O8. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FZ1. clear - Hj OR; lia. clear - Hj FRO; lia. }
    destruct (rloop len fx1 R1 M1 sp o fb d cap r ws RF1 WS1 WO ltac:(rewrite Lws; clear; lia) ltac:(rewrite Lws; exact LC) AT1 ltac:(clear - Lpos; lia) O81 C8 RA)
      as (fx' & R' & M' & n' & MS & K & R2' & Hn' & Q8 & Q0 & TOP & ZER & FR' & GR').
    exists fx', R', M'. split. { eapply msteps_trans. exact MS1. exact MS. }
    apply (PACK fx' R' M' n' (KS_trans _ _ _ K1 K) R2' Hn' Q8 Q0 TOP ZER).
    { intros a Ha Hn Hs. rewrite (FR' a Ha Hn). apply FZ1. exact Ha. exact Hs. } { eapply mem_grows_trans; eauto. }
Qed.
End SCFG_1.
End L5ARED.

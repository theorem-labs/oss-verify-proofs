(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun As0_code_94368_944b0 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ARedP L5ARed L5AMul10K L5AShrP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASHR.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5ASHRP. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?G |- ?G => exact H end.
Local Ltac sc := first [ asm | rk | gmem | arith_goal; first [asm | blia] ].
Local Notation U := L5AMULK.U.
Local Notation UR := L5AMULK.UR.
Local Notation U_to := L5AMULK.U_to.
Local Notation mfacts := L5AMULK.mfacts.

Definition SHR : Z := 0x9423c.
Definition HEAD : Z := 0x94374.
Definition REDRET : Z := 0x943d4.
Definition RET : Z := 0x943fc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor64 a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros Ha Hb. split. { apply Z.lor_nonneg. split; [apply Ha | apply Hb]. }
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]. { rewrite E. reflexivity. }
  assert (P : 0 < Z.lor a b). { pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))) as Q. clear - Q NE. Lia.lia. }
  apply Z.log2_lt_pow2. exact P. rewrite Z.log2_lor by (first [apply Ha | apply Hb]).
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|Na]. { cbn. clear; Lia.lia. } apply Z.log2_lt_pow2. { clear - Ha Na; Lia.lia. } apply Ha.
  - destruct (Z.eq_dec b 0) as [->|Nb]. { cbn. clear; Lia.lia. } apply Z.log2_lt_pow2. { clear - Hb Nb; Lia.lia. } apply Hb.
Qed.
Lemma shr64 w s : 0 <= w < 2 ^ 64 -> 0 <= w / 2 ^ s < 2 ^ 64.
Proof.
  intros Hw. destruct (Z_lt_le_dec s 0) as [Hs|Hs].
  { rewrite Z.pow_neg_r by exact Hs. rewrite Z.div_0_r. clear; Lia.lia. }
  assert (P : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; [clear; Lia.lia | exact Hs]).
  split. { apply Z.div_pos. apply Hw. exact P. }
  eapply Z.le_lt_trans. 2: apply Hw. apply Z.div_le_upper_bound. exact P.
  clear - Hw P. Lia.nia.
Qed.

(* [comment removed for export] *)
Lemma mfacts_keep_f M M' sp o d cap :
  mfacts M sp o d cap -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * cap) -> ~ (o <= i < o + 16) -> ~ (sp - 80 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mfacts M' sp o d cap.
Proof.
  intros [S1 W [I [C1 C2]] O OZ OW D DW DZ] G K.
  constructor; auto.
  - eapply L5.writable_grows; eauto.
  - split. { intros a Ha. rewrite K. apply I. exact Ha. clear - Ha; lia. clear - Ha D O; lia. clear - Ha O; lia. clear - Ha S1; lia. }
    split. eapply L5C.u64_at_agree. 4: exact C1. 2: clear; lia. 2: clear; lia. intros i Hi; apply K. clear - Hi; lia. clear - Hi D O; lia. clear - Hi O; lia. clear - Hi S1; lia.
    eapply L5AMULK.u32_at_agree1. 4: exact C2. 2: clear; lia. 2: clear; lia. intros i Hi; apply K. clear - Hi; lia. clear - Hi D O; lia. clear - Hi O; lia. clear - Hi S1; lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact OZ. intros i Hi. apply K. clear - Hi O; unfold SB in *; lia. clear - Hi O D; unfold SB in *; lia. clear - Hi O; unfold SB in *; lia. clear - Hi O S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - eapply L5.writable_grows; eauto.
  - eapply L5.writable_grows; eauto.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact DZ. intros i Hi. apply K. clear - Hi D; unfold SB in *; lia. clear - Hi D; unfold SB in *; lia. clear - Hi D O; unfold SB in *; lia. clear - Hi D S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Definition KSL : list nat := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition at_shead (R : bvmap 5 word) (sp o d k : Z) (len i : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 k /\
  getr R (reg 10) = Z_to_bv 64 (d + 8 * Z.of_nat i) /\ getr R (reg 12) = Z_to_bv 64 (d + 8 * Z.of_nat i) /\ getr R (reg 13) = Z_to_bv 64 (Z.of_nat i) /\
  getr R (reg 14) = Z_to_bv 64 (64 - k) /\ getr R (reg 15) = Z_to_bv 64 (Z.of_nat len - 1) /\ getr R (reg 16) = Z_to_bv 64 (Z.of_nat len) /\
  getr R (reg 17) = Z_to_bv 64 (d / 8 + 2147450880) /\ getr R (reg 18) = Z_to_bv 64 (o + 8) /\ getr R (reg 20) = Z_to_bv 64 2147450880 /\
  getr R (reg 21) = Z_to_bv 64 (o / 8 + 2147450880) /\ getr R (reg 22) = Z_to_bv 64 ((o + 8) / 8 + 2147450880).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sloop (m : nat) : forall fx R M (sp o d cap k : Z) (len i : nat) (wsi ws : list Z),
  mfacts M sp o d cap -> m = (len - i)%nat -> (i < len)%nat -> Z.of_nat len <= cap -> 1 <= k <= 63 ->
  length wsi = i -> words_ok wsi -> (forall j, (j < i)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w wsi j)) ->
  length ws = len -> words_ok ws -> (forall j, (i <= j < len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w ws j)) ->
  at_shead R sp o d k len i ->
  exists fx' R' M' (rw : list Z),
    msteps RSEGS (st fx R HEAD M) (st fx' R' L5ARED.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 1) = Z_to_bv 64 REDRET
    /\ length rw = len /\ words_ok rw /\ (forall j, (j < len)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat j) (nth_w rw j))
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * Z.of_nat len) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp o d cap k len i wsi ws MFM Hm IL CAP Hk WIL WIO LOW WL WO HIGH AT. { exfalso. clear - Hm IL. lia. }
  pose proof MFM as [[SPR A16] W64 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ].
  destruct AT as (A2 & A8 & A9 & A10 & A12 & A13 & A14 & A15 & A16r & A17 & A18 & A20 & A21 & A22).
  set (X := nth_w ws i) in *.
  assert (RX : 0 <= X < 2 ^ 64) by (subst X; apply words_ok_nth; exact WO).
  assert (CI : L5.u64_at RSEGS M (d + 8 * Z.of_nat i) X). { subst X. apply HIGH. clear - IL; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - FRO; lia). assert (FRDp : sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 64) by (clear - FRD; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia).
  assert (HVL : 1 <= Z.of_nat len <= 134217728) by (clear - IL CAP CAPR; lia).
  assert (HVI : 0 <= Z.of_nat i <= 134217727) by (clear - IL CAP CAPR; lia).
  assert (HVX : 0 <= X <= 18446744073709551615) by (clear - RX; lia).
  assert (HV52 : 1 <= 64 - k <= 63) by (clear - Hk; lia).
  assert (SP2 : 140735332487232 <= sp <= 140737488355328) by (clear - SPR; lia).
  destruct m as [|m'].
  - (* [comment removed for export] *)
    assert (EI : (i + 1 = len)%nat) by (clear - Hm IL; lia).
    assert (HVCI : 1 <= cap - Z.of_nat i <= 134217728) by (clear - IL CAP CAPR; lia).
    assert (HVLI : 1 <= Z.of_nat len - Z.of_nat i <= 1) by (clear - EI; lia).
    pose proof (vsrL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X
                  | 40%nat => Z.of_nat i | 41%nat => k | 43%nat => U R 1 | 52%nat => 64 - k | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR5 & lR6 & lR10 & lR11 & lR12 & lR13 & lCW)).
    set (v := X / 2 ^ (k mod 64)) in *.
    assert (Rv : 0 <= v < 2 ^ 64) by (subst v; apply shr64; exact RX).
    exists fx1, R1, M1, (wsi ++ [v]). split. exact lMS.
    split. { intros x Hx. apply lKS. revert Hx; apply (L5K.incl_b _ KS_vsrL); vm_compute; reflexivity. }
    split. exact lR10. split. exact lR1.
    split. { rewrite length_app, WIL. cbn [length]. exact EI. }
    split. { apply words_ok_app. exact WIO. constructor. exact Rv. constructor. }
    split. { intros j Hj. unfold nth_w. destruct (Nat.eq_dec j i) as [->|NE].
      - rewrite app_nth2 by (rewrite WIL; clear; lia). rewrite WIL, Nat.sub_diag. cbn [nth]. exact lCW.
      - rewrite app_nth1 by (rewrite WIL; clear - Hj NE EI; lia).
        eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hj NE EI; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hj; lia.
        intros a Ha. apply lFZ. clear - Ha DR CAPR CAP Hj; lia. clear - Ha Hj NE EI; lia. }
    split. { intros a Ha Hn. apply lFZ. exact Ha. clear - Hn IL; lia. } exact MG1.
  - (* [comment removed for export] *)
    assert (IL2 : (i + 1 < len)%nat) by (clear - Hm IL; lia).
    assert (HVCI : 2 <= cap - Z.of_nat i <= 134217728) by (clear - IL2 CAP CAPR; lia).
    assert (HVLI : 2 <= Z.of_nat len - Z.of_nat i <= 134217728) by (clear - IL2 HVL; lia).
    set (X' := nth_w ws (Datatypes.S i)).
    assert (RX' : 0 <= X' < 2 ^ 64) by (subst X'; apply words_ok_nth; exact WO).
    assert (HVX' : 0 <= X' <= 18446744073709551615) by (clear - RX'; lia).
    assert (CI' : L5.u64_at RSEGS M (d + 8 * Z.of_nat i + 8) X'). { subst X'. replace (d + 8 * Z.of_nat i + 8) with (d + 8 * Z.of_nat (Datatypes.S i)) by (clear; lia). apply HIGH. clear - IL2; lia. }
    pose proof (vsrI_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat i | 41%nat => k | 43%nat => U R 1 | 52%nat => 64 - k | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR5 & iR6 & iR7 & iR10 & iR11 & iR12 & iR13 & iCW)).
    match type of iCW with L5.u64_at _ _ _ ?e => set (v := e) in * end.
    assert (Rv : 0 <= v < 2 ^ 64).
    { subst v. apply lor64. apply Z.mod_pos_bound. reflexivity. apply shr64. exact RX. }
    assert (MF1 : mfacts M1 sp o d cap). { eapply L5AMULK.mfacts_keep. exact MFM. exact MG1. intros a Ha Hd _ _. apply iFZ. exact Ha. clear - Hd IL CAP; lia. }
    destruct (IH fx1 R1 M1 sp o d cap k len (Datatypes.S i) (wsi ++ [v]) ws MF1 ltac:(clear - Hm; lia) ltac:(clear - IL2; lia) CAP Hk) as (fx' & R' & M' & rw & MS & K & R10' & R1' & RL & RO & LIMBS & FR' & GR').
    + rewrite length_app, WIL. cbn [length]. clear; lia.
    + apply words_ok_app. exact WIO. constructor. exact Rv. constructor.
    + intros j Hj. unfold nth_w. destruct (Nat.eq_dec j i) as [->|NE].
      * rewrite app_nth2 by (rewrite WIL; clear; lia). rewrite WIL, Nat.sub_diag. cbn [nth]. exact iCW.
      * rewrite app_nth1 by (rewrite WIL; clear - Hj NE; lia).
        eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hj NE; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hj IL; lia.
        intros a Ha. apply iFZ. clear - Ha DR CAPR CAP Hj IL; lia. clear - Ha Hj NE; lia.
    + exact WL.
    + exact WO.
    + intros j Hj. eapply L5C.u64_at_agree. 4:{ apply HIGH. clear - Hj; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hj; lia.
      intros a Ha. apply iFZ. clear - Ha DR CAPR CAP Hj; lia. clear - Ha Hj; lia.
    + unfold at_shead.
      assert (KK : forall x, In x [2; 8; 9; 14; 15; 16; 17; 18; 20; 21; 22]%nat -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply iKS. revert Hx; apply (L5K.incl_b _ KS_vsrI); vm_compute; reflexivity. }
      repeat split.
      * rewrite (KK 2%nat) by inl; exact A2. * rewrite (KK 8%nat) by inl; exact A8. * rewrite (KK 9%nat) by inl; exact A9.
      * rewrite iR10. f_equal. clear; lia. * rewrite iR12. f_equal. clear; lia. * rewrite iR13. f_equal. clear; lia.
      * rewrite (KK 14%nat) by inl; exact A14. * rewrite (KK 15%nat) by inl; exact A15. * rewrite (KK 16%nat) by inl; exact A16r.
      * rewrite (KK 17%nat) by inl; exact A17. * rewrite (KK 18%nat) by inl; exact A18. * rewrite (KK 20%nat) by inl; exact A20.
      * rewrite (KK 21%nat) by inl; exact A21. * rewrite (KK 22%nat) by inl; exact A22.
    + exists fx', R', M', rw. split. { eapply msteps_trans. exact iMS. exact MS. }
      split. { intros x Hx. rewrite (K x Hx). apply iKS. revert Hx; apply (L5K.incl_b _ KS_vsrI); vm_compute; reflexivity. }
      split. exact R10'. split. exact R1'. split. exact RL. split. exact RO. split. exact LIMBS.
      split. { intros a Ha Hn. rewrite (FR' a Ha Hn). apply iFZ. exact Ha. clear - Hn IL; lia. }
      eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSF : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition st_after (sto : L5.bstore) (rw : list Z) : L5.bstore :=
  match sto with
  | L5.BInl v0 v1 => L5.BInl (nth_w rw 0) (if (2 <=? length rw)%nat then nth_w rw 1 else v1)
  | L5.BDyn c q => L5.BDyn c q
  end.

Definition shr_postA (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp : Z) (b : L5.bigobj) : Prop :=
  exists rw : list Z,
    length rw = L5.bo_len b /\ words_ok rw
    /\ (let n' := rlen rw in
        L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land (L5.bo_fb b) 253 else L5.bo_fb b) n' (st_after (L5.bo_st b) rw))
        /\ L5.limbs_at RSEGS M' (L5.bo_data o b) rw)
    /\ (forall x, In x KSF -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (L5.bo_data o b <= a < L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b)) -> ~ (o <= a < o + 16) -> ~ (sp - 80 <= a < sp) ->
                  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.

Theorem shr_runA fx R M (o sp r k : Z) (b : L5.bigobj) (ws : list Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 k -> 1 <= k <= 63 ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp -> (1 <= L5.bo_len b)%nat ->
  mfacts M sp o (L5.bo_data o b) (L5.bo_cap b) -> L5.writable RSEGS M (sp - 80) 16 ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
  match L5.bo_st b with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R SHR M) (st fx' R' r M') /\ shr_postA M M' R R' o sp b.
Proof.
  intros G10 G11 Hk G1 RA G2 Lpos MFM W80 OB OL ODYN.
  destruct b as [fb len sto]. unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  set (cap := match sto with L5.BInl _ _ => 2 | L5.BDyn c _ => c end) in *.
  pose proof MFM as [[SPR A16] W64 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ].
  pose proof OB as (O0 & Ffb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Ffb, O8, OST. destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  assert (WO : words_ok ws) by exact Rws.
  assert (LC : Z.of_nat len <= cap). { subst cap. destruct sto as [w0 w1|c q]. destruct OST as (_ & _ & _ & Hl2 & _). clear - Hl2; lia. destruct OST as (_ & _ & _ & Hlc & _). exact Hlc. }
  assert (WS : L5.limbs_at RSEGS M d ws).
  { subst d. destruct sto as [w0 w1|c q]. 2: exact LAT. destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). rewrite LAT. intros i Hi. rewrite length_firstn in Hi. cbn [length Nat.min] in Hi.
    destruct i as [|[|i]]. { destruct len as [|ly]. exfalso; clear - Lpos; lia. cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by (clear; lia). exact O16. }
    { destruct len as [|[|ly]]; try (exfalso; cbn in Hi; clear - Hi; lia). cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by (clear; lia). exact O24. }
    exfalso. destruct len as [|[|ly]]; cbn in Hi; clear - Hi Hl2; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - FRO; lia). assert (FRDp : sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 64) by (clear - FRD; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia). assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  assert (HVL : 1 <= Z.of_nat len <= 134217728) by (clear - Lpos LC CAPR; lia).
  assert (SP2 : 140735332487232 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  (* [comment removed for export] *)
  assert (ENTRY : exists fx1 R1 M1, msteps RSEGS (st fx R SHR M) (st fx1 R1 HEAD M1) /\ mem_grows M M1
            /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
            /\ (forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) /\ at_shead R1 sp o d k len 0
            /\ L5.u64_at RSEGS M1 (sp - 8) r /\ L5.u64_at RSEGS M1 (sp - 16) (U R 8) /\ L5.u64_at RSEGS M1 (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1 (sp - 32) (U R 18)
            /\ L5.u64_at RSEGS M1 (sp - 40) (U R 19) /\ L5.u64_at RSEGS M1 (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1 (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1 (sp - 64) (U R 22)).
  { subst d cap. destruct sto as [w0 w1|c q].
    + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (HVL2 : 1 <= Z.of_nat len <= 2) by (clear - Lpos Hl2; lia).
      pose proof (vsrAi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 41%nat => k | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1 & MG1 & aFR & aFZ & (aMS & aKS & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR13 & aR14 & aR15 & aR16 & aR17 & aR18 & aR20 & aR21 & aR22
                        & aC64 & aC56 & aC48 & aC40 & aC32 & aC24 & aC16 & aC8)).
      exists fx1, R1, M1. split. exact aMS. split. exact MG1. split. { intros a Ha Hn. apply aFZ. exact Ha. clear - Hn; lia. }
      split. { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vsrAi); vm_compute; reflexivity. }
      split. { unfold at_shead. change (Z.of_nat 0) with 0. repeat split; try assumption.
               all: first [rewrite aR10 | rewrite aR12 | rewrite aR14 | rewrite aR17]; f_equal; clear; lia. }
      unfold U in aC8. rewrite G1, L5.unsigned_lit in aC8 by exact HVR. repeat split; assumption.
    + destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia).
      pose proof (vsrAd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 41%nat => k | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1 & MG1 & aFR & aFZ & (aMS & aKS & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR13 & aR14 & aR15 & aR16 & aR17 & aR18 & aR20 & aR21 & aR22
                        & aC64 & aC56 & aC48 & aC40 & aC32 & aC24 & aC16 & aC8)).
      exists fx1, R1, M1. split. exact aMS. split. exact MG1. split. { intros a Ha Hn. apply aFZ. exact Ha. clear - Hn; lia. }
      split. { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vsrAd); vm_compute; reflexivity. }
      split. { unfold at_shead. change (Z.of_nat 0) with 0. repeat split; try assumption.
               all: first [rewrite aR10 | rewrite aR12 | rewrite aR14 | rewrite aR17]; f_equal; clear; lia. }
      unfold U in aC8. rewrite G1, L5.unsigned_lit in aC8 by exact HVR. repeat split; assumption. }
  destruct ENTRY as (fx1 & R1 & M1 & MS1 & GR1 & FZ1 & K1 & AT1 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64).
  assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep_f. exact MFM. exact GR1. intros a Ha _ _ Hs. apply FZ1. exact Ha. clear - Hs; lia. }
  assert (WS1 : forall j, (0 <= j < len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat j) (nth_w ws j)).
  { intros j Hj. eapply L5C.u64_at_agree. 4:{ apply WS. rewrite Lws. clear - Hj; lia. } 2: clear - DR; lia. 2: clear - DR CAPR LC Hj; lia.
    intros a Ha. apply FZ1. clear - Ha DR CAPR LC Hj; lia. clear - Ha Hj LC FRD; lia. }
  (* [comment removed for export] *)
  destruct (sloop len fx1 R1 M1 sp o d cap k len 0 [] ws MF1 ltac:(clear; lia) ltac:(clear - Lpos; lia) LC Hk eq_refl ltac:(constructor)
              ltac:(intros j Hj; exfalso; clear - Hj; lia) Lws WO WS1 AT1)
    as (fx2 & R2 & M2 & rw & MS2 & K2 & R2_10 & R2_1 & RL & RO & LIMBS2 & FR2 & GR2).
  assert (MF2 : mfacts M2 sp o d cap). { eapply L5AMULK.mfacts_keep. exact MF1. exact GR2. intros a Ha Hd _ _. apply FR2. exact Ha. clear - Hd LC; lia. }
  pose proof MF2 as [_ W64b [IMGC2 [CSB2 CUAR2]] _ OZ2 OW2 _ DW2 DZ2].
  assert (W80b : L5.writable RSEGS M2 (sp - 64 - 16) 16). { replace (sp - 64 - 16) with (sp - 80) by (clear; lia). eapply L5.writable_grows. exact GR2. eapply L5.writable_grows. exact GR1. exact W80. }
  assert (T12 : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= d \/ d + 8 * Z.of_nat len <= a) -> (a + 8 <= sp - 64 \/ sp <= a) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
  { intros a v Ha Hb Hd Hs Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: exact Ha. 2: exact Hb. intros j Hj. rewrite FR2. apply FZ1.
    clear - Hj Ha Hb; lia. clear - Hj Hs; lia. clear - Hj Ha Hb; lia. clear - Hj Hd; lia. }
  assert (FB2 : L5.u8_at RSEGS M2 o fb).
  { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. rewrite FR2. apply FZ1.
    clear - Hj OR; lia. clear - Hj FRO; lia. clear - Hj OR; lia. clear - Hj OD LC; lia. }
  set (b2 := L5.BO fb len (st_after sto rw)).
  assert (OB2 : L5.big_at RSEGS M2 o b2 /\ L5C.obj_limbs RSEGS M2 b2 rw).
  { subst b2 d cap. unfold L5.big_at, L5C.obj_limbs, st_after. cbn [L5.bo_fb L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). split.
      + split. exact FB2. split. exact Ffb. split. { apply T12. clear - OR; lia. clear - OR; lia. clear; lia. clear - FRO; lia. exact O8. } split. exact B0.
        split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS2. exact Lpos. }
        split. { destruct (Nat.leb_spec 2 (length rw)) as [H2|H2].
                 - replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by (clear; lia). apply LIMBS2. rewrite RL in H2. exact H2.
                 - apply T12. clear - OR; lia. clear - OR; lia. rewrite RL in H2. clear - H2; lia. clear - FRO; lia. exact O24. }
        split. exact Hl2. split. apply words_ok_nth; exact RO. destruct (2 <=? length rw)%nat. apply words_ok_nth; exact RO. exact Rw1.
      + split. exact RL. split. exact RO. rewrite <- RL.
        destruct rw as [|a [|b0 [|c0 l]]]; cbn [length] in *; try (exfalso; clear - RL Hl2 Lpos; lia); reflexivity.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split.
      + split. exact FB2. split. exact Ffb. split. { apply T12. clear - OR; lia. clear - OR; lia. clear - ODYN Hlc; lia. clear - FRO; lia. exact O8. } split. exact B1.
        split. { apply T12. clear - OR; lia. clear - OR; lia. clear - ODYN Hlc; lia. clear - FRO; lia. exact O16. }
        split. { apply T12. clear - OR; lia. clear - OR; lia. clear - ODYN Hlc; lia. clear - FRO; lia. exact O24. }
        split. exact Hlc. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH.
      + split. exact RL. split. exact RO. intros i Hi. rewrite RL in Hi. apply LIMBS2. exact Hi. }
  destruct OB2 as [OB2 OL2].
  assert (RAred : L5.ra_ok REDRET). { split. unfold REDRET; clear; lia. reflexivity. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16' : (sp - 64) mod 16 = 0) by (clear - A16; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (AT1' := AT1). destruct AT1' as (B2 & B8 & _).
  assert (G2' : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (K2 2%nat) by inl; exact B2).
  destruct (L5ARED.reduce_run fx2 R2 M2 o (sp - 64) REDRET b2 rw R2_10 R2_1 RAred G2' ltac:(clear - SPR; lia) A16' W80b IMGC2 CSB2 CUAR2
              ltac:(clear - OR; lia) O8a OBIG ltac:(clear - FRO; lia) OZ2 OW2 OB2 OL2)
    as (fx3 & R3 & M3 & MS3 & OB3 & K3 & R3_2 & R3_10 & FR3 & GR3).
  { subst b2 d cap. unfold L5.bo_data, L5.bo_cap, st_after. cbn [L5.bo_st]. destruct sto as [w0 w1|c q]; cbn iota.
    all: split; [exact DBIG|]. all: split; [clear - FRD; lia|]. all: split; [exact OD|]. all: split; [exact DW2|]. all: split; [exact DZ2|]. all: clear - CAPR; lia. }
  cbn zeta in OB3. replace (L5.bo_fb b2) with fb in OB3 by reflexivity. replace (L5.bo_st b2) with (st_after sto rw) in OB3 by reflexivity.
  assert (MF3 : mfacts M3 sp o d cap). { eapply L5AMULK.mfacts_keep. exact MF2. exact GR3. intros a Ha _ Ho Hs. apply FR3. exact Ha. exact Ho. clear - Hs; lia. }
  pose proof MF3 as [_ W64c [IMGC3 [CSB3 CUAR3]] _ _ _ _ _ _].
  assert (XF : forall a v, sp - 64 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M3 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. rewrite FR3. apply FR2.
    clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRD LC; lia. clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRO; lia. clear - Hj Ha Hb; lia. }
  (* [comment removed for export] *)
  pose proof (vsrE_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => o | 43%nat => U R3 1 | 44%nat => r | 45%nat => U R 8 | 46%nat => U R 9 | 47%nat => U R 18
                | 48%nat => U R 19 | 49%nat => U R 20 | 50%nat => U R 21 | 51%nat => U R 22 | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (G8' : getr R3 (reg 8) = Z_to_bv 64 o). { rewrite (K3 8%nat) by inl. rewrite (K2 8%nat) by inl. exact B8. }
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc]) ]).
  destruct P as (fx4 & R4 & M4 & MG4 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22)).
  assert (EM4 : M4 = M3). { apply functional_extensionality. exact eFR. } subst M4.
  pose proof (ret_to fx4 R4 M3 0x943fc W_943fc r F_943fc eq_refl D_943fc eR1 (proj1 RA) (proj2 RA)) as RETs.
  exists fx4, R4, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MS3. eapply msteps_trans. exact eMS. exact RETs. }
  unfold shr_postA, L5.bo_data. cbn [L5.bo_fb L5.bo_len L5.bo_st]. fold d.
  exists rw. split. exact RL. split. exact RO.
  split. { cbn zeta. split. exact OB3. intros i Hi. rewrite RL in Hi. eapply L5C.u64_at_agree. 4:{ apply LIMBS2. exact Hi. }
           2: clear - DR; lia. 2: clear - DR CAPR LC Hi; lia. intros j Hj. apply FR3. clear - Hj DR CAPR LC Hi; lia. clear - Hj Hi LC OD; lia. clear - Hj Hi LC FRD; lia. }
  split. { intros x Hx. unfold KSF in Hx. cbn [In] in Hx.
           destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]].
           all: first [ (rewrite eR8; symmetry; apply U_to) | (rewrite eR9; symmetry; apply U_to) | (rewrite eR18; symmetry; apply U_to) | (rewrite eR19; symmetry; apply U_to)
                      | (rewrite eR20; symmetry; apply U_to) | (rewrite eR21; symmetry; apply U_to) | (rewrite eR22; symmetry; apply U_to)
                      | (rewrite (eKS _) by inl; rewrite (K3 _) by inl; rewrite (K2 _) by inl; apply K1; inl) ]. }
  split. exact eR2. split. exact eR10.
  split. { intros a Ha Hd Ho Hs. rewrite FR3. rewrite FR2. apply FZ1. exact Ha. clear - Hs; lia. exact Ha. exact Hd. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. exact GR1. eapply mem_grows_trans. exact GR2. exact GR3.
Qed.

End SCFG_1.
End L5ASHR.

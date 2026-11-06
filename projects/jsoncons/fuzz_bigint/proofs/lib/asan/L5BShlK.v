(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun Bo0_code_94368_9505c BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BRedP L5BRed L5BLeafK L5BShlP.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASHLK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5ASHLP. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?G |- ?G => exact H end.
Local Ltac sc := first [ asm | rk | gmem | arith_goal; first [asm | blia] ].
Local Notation U := L5BLK.U.
Local Notation UR := L5BLK.UR.
Local Notation U_to := L5BLK.U_to.
Definition mfacts := L5BLK.mfacts 128 112 1.
Lemma mfacts_keep M M' sp o d cap :
  mfacts M sp o d cap -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * cap) -> ~ (o <= i < o + 16) -> ~ (sp - 128 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mfacts M' sp o d cap.
Proof. apply L5BLK.mfacts_keep; clear; lia. Qed.

Definition SHL : Z := 0x94518.
Definition HEAD : Z := 0x946fc.
Definition RZRET : Z := 0x94698.
Definition REDRET : Z := 0x9478c.
Definition RET : Z := 0x947c4.
Definition MAXW : Z := 18446744073709551615.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mask_range k : 0 <= k <= 63 -> 0 <= 2 ^ k - 1 < 2 ^ 64.
Proof. intros Hk. split. pose proof (Z.pow_pos_nonneg 2 k); lia. pose proof (Z.pow_le_mono_r 2 k 63); lia. Qed.
Lemma pow_k_pos k : 0 <= k -> 0 < 2 ^ k. Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.
Lemma mulM1 x : 0 <= x < 2 ^ 64 -> (MAXW * x) mod 2 ^ 64 = (2 ^ 64 - x) mod 2 ^ 64.
Proof. intros Hx. unfold MAXW. replace (18446744073709551615 * x) with ((2 ^ 64 - x) + (x - 1) * 2 ^ 64) by lia. apply Z_mod_plus_full. Qed.
Lemma mask_ident k : 1 <= k <= 63 -> ((MAXW * ((MAXW * 2 ^ (k mod 64)) mod 2 ^ 64)) mod 2 ^ 64 + MAXW) mod 2 ^ 64 = 2 ^ k - 1.
Proof.
  intros Hk. rewrite (Z.mod_small k 64) by lia.
  pose proof (pow_k_pos k ltac:(lia)) as P. pose proof (Z.pow_le_mono_r 2 k 63 ltac:(lia) ltac:(lia)) as P63.
  rewrite (mulM1 (2 ^ k)) by lia. rewrite (Z.mod_small (2 ^ 64 - 2 ^ k)) by lia.
  rewrite mulM1 by lia. replace (2 ^ 64 - (2 ^ 64 - 2 ^ k)) with (2 ^ k) by lia. rewrite (Z.mod_small (2 ^ k)) by lia.
  unfold MAXW. replace (2 ^ k + 18446744073709551615) with ((2 ^ k - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma mask_identL k : 1 <= k <= 63 -> ((18446744073709551615 * ((18446744073709551615 * 2 ^ (k mod 64)) mod 2 ^ 64)) mod 2 ^ 64 + 18446744073709551615) mod 2 ^ 64 = 2 ^ k - 1.
Proof. exact (mask_ident k). Qed.
Definition lo (k w : Z) : Z := BigModel.W.shl w k.
Definition hi (k w c : Z) : Z := Z.lor (Z.land (w / 2 ^ (64 - k)) (2 ^ k - 1)) c.
Lemma lo_ident k w : 1 <= k <= 63 -> (w * 2 ^ (k mod 64)) mod 2 ^ 64 = lo k w.
Proof. intros Hk. rewrite (Z.mod_small k 64) by lia. unfold lo, BigModel.W.shl, BigModel.W.wrap. rewrite BigFactsBase.M_val. reflexivity. Qed.
Lemma hi_ident k w c : 1 <= k <= 63 -> Z.lor (Z.land (w / 2 ^ ((64 - k) mod 64)) (2 ^ k - 1)) c = hi k w c.
Proof. intros Hk. rewrite (Z.mod_small (64 - k) 64) by lia. reflexivity. Qed.
Lemma lo_range k w : 0 <= lo k w < 2 ^ 64.
Proof. unfold lo, BigModel.W.shl, BigModel.W.wrap. rewrite BigFactsBase.M_val. apply Z.mod_pos_bound. lia. Qed.
Lemma lo_0 k : lo k 0 = 0.
Proof. unfold lo, BigModel.W.shl, BigModel.W.wrap. rewrite Z.mul_0_l. apply Zmod_0_l. Qed.
Lemma shlG_0 k orig : BigFactsOps.shlG k orig 0 = lo k (nth_w orig 0).
Proof. reflexivity. Qed.
Lemma shlG_S k orig j : (1 <= j)%nat -> 1 <= k <= 63 -> 0 <= nth_w orig (j - 1)%nat ->
  BigFactsOps.shlG k orig j = hi k (nth_w orig (j - 1)%nat) (lo k (nth_w orig j)).
Proof.
  intros Hj Hk Hw. unfold BigFactsOps.shlG, hi, lo. destruct (Nat.ltb_spec 0 j). 2: lia.
  unfold BigModel.W.lor, BigModel.W.land, BigModel.W.shr. rewrite Z.lor_comm. f_equal. f_equal.
  unfold BigModel.W.sub, BigModel.W.shl, BigModel.W.wrap. rewrite BigFactsBase.M_val.
  pose proof (pow_k_pos k ltac:(lia)). pose proof (Z.pow_le_mono_r 2 k 63 ltac:(lia) ltac:(lia)).
  rewrite (Z.mod_small (1 * 2 ^ k)) by lia. rewrite Z.mod_small by lia. lia.
Qed.


Definition KSL : list nat := [2; 3; 4; 8; 9; 20; 21; 22; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition at_shead (R : bvmap 5 word) (M : word -> option byte) (sp o d k : Z) (n i : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 112) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 k /\
  getr R (reg 18) = Z_to_bv 64 (Z.of_nat i) /\ getr R (reg 20) = Z_to_bv 64 (64 - k) /\ getr R (reg 21) = Z_to_bv 64 2147450880 /\
  getr R (reg 22) = Z_to_bv 64 (2 ^ k - 1) /\
  L5.u64_at RSEGS M (sp - 112) d /\ L5.u64_at RSEGS M (sp - 104) (Z.of_nat n + 1).

(* [comment removed for export] *)
Definition cells_at (M : word -> option byte) (d k : Z) (orig : list Z) (i n : nat) : Prop :=
  (forall j, (j <= i)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (nth_w orig j)) /\
  (forall j, (i < j <= n)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat j) (BigFactsOps.shlG k orig j)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sloop (i : nat) : forall fx R M (sp o d cap k : Z) (n : nat) (orig : list Z),
  mfacts M sp o d cap -> (i <= n)%nat -> (1 <= n)%nat -> Z.of_nat n + 1 <= cap -> 1 <= k <= 63 -> words_ok orig ->
  cells_at M d k orig i n ->
  at_shead R M sp o d k n i ->
  exists fx' R' M',
    msteps RSEGS (st fx R HEAD M) (st fx' R' L5ARED.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 1) = Z_to_bv 64 REDRET
    /\ (forall j, (j <= n)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat j) (BigFactsOps.shlG k orig j))
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat n + 1)) -> ~ (sp - 120 <= a < sp - 112) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  induction i as [|i IH]; intros fx R M sp o d cap k n orig MFM Hi Hn CAP Hk WO (C1 & C3) AT.
  all: pose proof MFM as [[SPR A16] W128 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ VZ].
  all: destruct AT as (A2 & A8 & A9 & A18 & A20 & A21 & A22 & VD & VL).
  all: pose proof (mask_range k ltac:(clear - Hk; lia)) as MR.
  all: assert (ALS : aligned sp 16) by exact A16; assert (ALO : aligned o 8) by exact O8a; assert (ALD : aligned d 8) by exact D8.
  all: assert (FROp : sp - 128 + 128 <= o \/ o + 32 <= sp - 128) by (clear - FRO; lia); assert (FRDp : sp - 128 + 128 <= d \/ d + 8 * cap <= sp - 128) by (clear - FRD; lia).
  all: assert (DIMGp : 65536 + 6438912 <= d \/ d + 8 * cap <= 65536) by (clear - DIMG; lia).
  all: assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  all: assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia); assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  all: assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia).
  all: assert (HVN : 1 <= Z.of_nat n <= 134217728) by (clear - Hn CAP CAPR; lia).
  all: assert (HV56 : 1 <= 64 - k <= 63) by (clear - Hk; lia); assert (HV57 : 0 <= 2 ^ k - 1 <= 18446744073709551615) by (clear - MR; lia).
  all: assert (VZp : L5KA.zeros_at M ((sp - 112) / 8 + 2147450880) 1) by exact VZ.
  - (* [comment removed for export] *)
    set (w := nth_w orig 0) in *.
    assert (Rw : 0 <= w < 2 ^ 64) by (subst w; apply words_ok_nth; exact WO).
    assert (HVw : 0 <= w <= 18446744073709551615) by (clear - Rw; lia).
    assert (Cw : L5.u64_at RSEGS M d w). { replace d with (d + 8 * Z.of_nat 0) by (clear; lia). apply C1. clear; lia. }
    change (Z.of_nat 0) with 0 in A18.
    pose proof (vshL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat n | 36%nat => d | 37%nat => cap | 38%nat => w
                  | 41%nat => k | 43%nat => U R 1 | 56%nat => 64 - k | 57%nat => 2 ^ k - 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11 & lR12 & lR13 & lR14 & lCLO & lCRA)).
    rewrite (lo_ident k w Hk) in lCLO.
    exists fx1, R1, M1. split. exact lMS.
    split. { intros x Hx. apply lKS. revert Hx; apply (L5K.incl_b _ KS_vshL); vm_compute; reflexivity. }
    split. exact lR10. split. exact lR1.
    split. { intros j Hj. destruct (Nat.eq_dec j 0) as [->|NE0].
      { rewrite shlG_0. replace (d + 8 * Z.of_nat 0) with d by (clear; lia). exact lCLO. }
      eapply L5C.u64_at_agree. 4:{ apply C3. clear - Hj NE0; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hj; lia.
      intros a Ha. apply lFZ. clear - Ha DR CAPR CAP Hj; lia. clear - Ha Hj NE0; lia. clear - Ha Hj CAP FRD SPR; lia. }
    split. { intros a Ha Hd Hs. apply lFZ. exact Ha. clear - Hd Hn; lia. clear - Hs; lia. } exact MG1.
  - (* [comment removed for export] *)
    set (I1 := Datatypes.S i) in *.
    set (w := nth_w orig I1) in *. set (w' := nth_w orig i) in *.
    assert (Rw : 0 <= w < 2 ^ 64) by (subst w; apply words_ok_nth; exact WO).
    assert (Rw' : 0 <= w' < 2 ^ 64) by (subst w'; apply words_ok_nth; exact WO).
    assert (HVw : 0 <= w <= 18446744073709551615) by (clear - Rw; lia). assert (HVw' : 0 <= w' <= 18446744073709551615) by (clear - Rw'; lia).
    assert (Cw : L5.u64_at RSEGS M (d + 8 * Z.of_nat I1) w). { apply C1. clear; lia. }
    assert (Cw' : L5.u64_at RSEGS M (d + 8 * Z.of_nat I1 + -8) w'). { replace (d + 8 * Z.of_nat I1 + -8) with (d + 8 * Z.of_nat i) by (subst I1; clear; lia). apply C1. subst I1; clear; lia. }
    assert (HV40 : 1 <= Z.of_nat I1 <= 134217728) by (subst I1; clear - Hi HVN; lia).
    assert (HVCI : 1 <= cap - Z.of_nat I1 <= 134217728) by (clear - Hi CAP CAPR HV40; lia).
    pose proof (vshI_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat n | 36%nat => d | 37%nat => cap | 38%nat => w | 39%nat => w'
                  | 40%nat => Z.of_nat I1 | 41%nat => k | 43%nat => U R 1 | 56%nat => 64 - k | 57%nat => 2 ^ k - 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR11 & iR12 & iR13 & iR14 & iR18 & iR19 & iR23 & iCW & iCRA)).
    rewrite (lo_ident k w Hk) in iCW. rewrite Z.lor_comm in iCW. rewrite (hi_ident k w' (lo k w) Hk) in iCW.
    assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact MG1. intros a Ha Hd _ Hs. apply iFZ. exact Ha. clear - Hd Hi CAP HV40; lia. clear - Hs; lia. }
    assert (KEEP : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= d + 8 * Z.of_nat I1 \/ d + 8 * Z.of_nat I1 + 8 <= a) -> (a + 8 <= sp - 120 \/ sp - 112 <= a) ->
                   L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hd Hs Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: exact Ha. 2: exact Hb. intros j Hj. apply iFZ. clear - Hj Ha Hb; lia. clear - Hj Hd; lia. clear - Hj Hs; lia. }
    destruct (IH fx1 R1 M1 sp o d cap k n orig MF1 ltac:(clear - Hi; lia) Hn CAP Hk WO) as (fx' & R' & M' & MS & K & R10' & R1' & LIMBS & FR' & GR').
    + split. { intros j Hj. apply KEEP. clear - DR; lia. clear - DR CAPR CAP Hj Hi; lia. subst I1; clear - Hj; lia. clear - Hj Hi CAP FRD SPR; lia. apply C1. subst I1; clear - Hj; lia. }
      intros j Hj. destruct (Nat.eq_dec j I1) as [->|NE].
      { rewrite (shlG_S k orig I1 ltac:(subst I1; clear; lia) Hk ltac:(replace (I1 - 1)%nat with i by (subst I1; clear; lia); clear - Rw'; subst w'; lia)).
        replace (I1 - 1)%nat with i by (subst I1; clear; lia). exact iCW. }
      apply KEEP. clear - DR; lia. clear - DR CAPR CAP Hj; lia. subst I1; clear - Hj NE; lia. clear - Hj CAP FRD SPR; lia. apply C3. subst I1; clear - Hj NE; lia.
    + unfold at_shead.
      assert (KK : forall x, In x [2; 8; 9; 20; 21; 22]%nat -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply iKS. revert Hx; apply (L5K.incl_b _ KS_vshI); vm_compute; reflexivity. }
      repeat split.
      * rewrite (KK 2%nat) by inl; exact A2. * rewrite (KK 8%nat) by inl; exact A8. * rewrite (KK 9%nat) by inl; exact A9.
      * rewrite iR18. f_equal. subst I1; clear; lia.
      * rewrite (KK 20%nat) by inl; exact A20. * rewrite (KK 21%nat) by inl; exact A21. * rewrite (KK 22%nat) by inl; exact A22.
      * apply KEEP. clear - SPR; lia. clear - SPR; lia. clear - FRD CAP Hi HV40 SPR; lia. clear; lia. exact VD.
      * apply KEEP. clear - SPR; lia. clear - SPR; lia. clear - FRD CAP Hi HV40 SPR; lia. clear; lia. exact VL.
    + exists fx', R', M'. split. { eapply msteps_trans. exact iMS. exact MS. }
      split. { intros x Hx. rewrite (K x Hx). apply iKS. revert Hx; apply (L5K.incl_b _ KS_vshI); vm_compute; reflexivity. }
      split. exact R10'. split. exact R1'. split. exact LIMBS.
      split. { intros a Ha Hd Hs. rewrite (FR' a Ha Hd Hs). apply iFZ. exact Ha. clear - Hd Hi HV40; lia. clear - Hs; lia. }
      eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSC : list nat := [3; 4; 27]%nat.
Definition KSP : list nat := [2; 3; 4; 8; 9; 21; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition st_after (sto : L5.bstore) (wl : list Z) : L5.bstore :=
  match sto with
  | L5.BInl _ _ => L5.BInl (nth_w wl 0) (nth_w wl 1)
  | L5.BDyn c q => L5.BDyn c q
  end.

Lemma saved_back M M2 sp (FRs : forall a, 0 <= a < 2 ^ 64 -> sp - 96 <= a < sp -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) :
  140735332487296 <= sp <= 140737488355328 ->
  forall a v, sp - 96 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v.
Proof.
  intros SPR a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia.
  intros j Hj. apply FRs. clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb; lia.
Qed.

(* [comment removed for export] *)
Lemma shl_tail fx1 R1 M1 (sp o r : Z) (b1 : L5.bigobj) (wl : list Z) (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 : Z) :
  let d := L5.bo_data o b1 in let cap := L5.bo_cap b1 in
  getr R1 (reg 2) = Z_to_bv 64 (sp - 112) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 10) = Z_to_bv 64 o -> getr R1 (reg 1) = Z_to_bv 64 REDRET ->
  L5.u64_at RSEGS M1 (sp - 8) r -> L5.ra_ok r ->
  L5.u64_at RSEGS M1 (sp - 16) v8 -> L5.u64_at RSEGS M1 (sp - 24) v9 -> L5.u64_at RSEGS M1 (sp - 32) v18 -> L5.u64_at RSEGS M1 (sp - 40) v19 -> L5.u64_at RSEGS M1 (sp - 48) v20 -> L5.u64_at RSEGS M1 (sp - 56) v21 -> L5.u64_at RSEGS M1 (sp - 64) v22 -> L5.u64_at RSEGS M1 (sp - 72) v23 -> L5.u64_at RSEGS M1 (sp - 80) v24 -> L5.u64_at RSEGS M1 (sp - 88) v25 -> L5.u64_at RSEGS M1 (sp - 96) v26 ->
  0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 -> 0 <= v20 < 2 ^ 64 -> 0 <= v21 < 2 ^ 64 -> 0 <= v22 < 2 ^ 64 -> 0 <= v23 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v25 < 2 ^ 64 -> 0 <= v26 < 2 ^ 64 ->
  mfacts M1 sp o d cap ->
  L5.big_at RSEGS M1 o b1 -> L5C.obj_limbs RSEGS M1 b1 wl ->
  exists fx' R' M',
    msteps RSEGS (st fx1 R1 L5ARED.REDUCE M1) (st fx' R' r M')
    /\ (forall x, In x KSC -> getr R' (reg x) = getr R1 (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ getr R' (reg 8) = Z_to_bv 64 v8 /\ getr R' (reg 9) = Z_to_bv 64 v9 /\ getr R' (reg 18) = Z_to_bv 64 v18 /\ getr R' (reg 19) = Z_to_bv 64 v19 /\ getr R' (reg 20) = Z_to_bv 64 v20 /\ getr R' (reg 21) = Z_to_bv 64 v21 /\ getr R' (reg 22) = Z_to_bv 64 v22 /\ getr R' (reg 23) = Z_to_bv 64 v23 /\ getr R' (reg 24) = Z_to_bv 64 v24 /\ getr R' (reg 25) = Z_to_bv 64 v25 /\ getr R' (reg 26) = Z_to_bv 64 v26
    /\ (let n' := L5W.rlen wl in L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land (L5.bo_fb b1) 253 else L5.bo_fb b1) n' (L5.bo_st b1)))
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> ~ (sp - 128 <= a < sp - 112) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
    /\ mem_grows M1 M'.
Proof.
  cbn zeta. intros G2 G8 R1_10 R1_1 C8 RA C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 C96 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 MF1 OB1 OL1.
  pose proof MF1 as [[SPR A16] W128a [IMGC1 [CSB1 CUAR1]] (OR & O8a & OBIG & FRO) OZ1 OW1 (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW1 DZ1 VZ1].
  assert (W16a : L5.writable RSEGS M1 (sp - 112 - 16) 16). { eapply L5.writable_sub. exact W128a. clear; lia. clear; lia. }
  assert (RAred : L5.ra_ok REDRET). { split. unfold REDRET; clear; lia. reflexivity. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16' : (sp - 112) mod 16 = 0) by (clear - A16; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (L5ARED.reduce_run fx1 R1 M1 o (sp - 112) REDRET b1 wl R1_10 R1_1 RAred G2 ltac:(clear - SPR; lia) A16' W16a IMGC1 CSB1 CUAR1
              ltac:(clear - OR; lia) O8a OBIG ltac:(clear - FRO; lia) OZ1 OW1 OB1 OL1)
    as (fx2 & R2 & M2 & MS2 & OB2 & K2 & R2_2 & R2_10 & FR2 & GR2).
  { split; [exact DBIG|]. split; [clear - FRD; lia|]. split; [exact OD|]. split; [exact DW1|]. split; [exact DZ1|]. clear - CAPR; lia. }
  cbn zeta in OB2.
  assert (XF : forall a v, sp - 96 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
  { apply saved_back. 2: clear - SPR; lia. intros a Ha Hs. apply FR2. exact Ha. clear - Hs FRO; lia. clear - Hs; lia. }
  assert (MF2 : mfacts M2 sp o (L5.bo_data o b1) (L5.bo_cap b1)). { eapply mfacts_keep. exact MF1. exact GR2. intros i Hi _ Ho Hs. apply FR2. exact Hi. exact Ho. clear - Hs; lia. }
  pose proof MF2 as [_ W128b [IMGC2 [CSB2 CUAR2]] _ _ _ _ _ _ _].
  assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  assert (ALS : aligned sp 16) by exact A16. assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 0 <= o < 2 ^ 64) by (clear - OR; lia).
  pose proof (vshE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => o | 43%nat => U R2 1 | 44%nat => r | 45%nat => v8 | 46%nat => v9 | 47%nat => v18 | 48%nat => v19 | 49%nat => v20 | 50%nat => v21 | 51%nat => v22 | 52%nat => v23 | 53%nat => v24 | 54%nat => v25 | 55%nat => v26 | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (G8' : getr R2 (reg 8) = Z_to_bv 64 o). { rewrite (K2 8%nat) by inl. exact G8. }
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc]) ]).
  destruct P as (fx3 & R3 & M3 & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26)).
  assert (EM3 : M3 = M2). { apply functional_extensionality. exact eFR. } subst M3.
  pose proof (ret_to fx3 R3 M2 0x947c4 W_947c4 r F_947c4 eq_refl D_947c4 eR1 (proj1 RA) (proj2 RA)) as RETs.
  exists fx3, R3, M2. split. { eapply msteps_trans. exact MS2. eapply msteps_trans. exact eMS. exact RETs. }
  split. { intros x Hx. rewrite (eKS x). apply K2. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. }
  split. exact eR2. split. exact eR10. split. exact eR8. split. exact eR9. split. exact eR18. split. exact eR19. split. exact eR20. split. exact eR21. split. exact eR22. split. exact eR23. split. exact eR24. split. exact eR25. split. exact eR26.
  split. exact OB2. split. { intros a Ha Ho Hs. apply FR2. exact Ha. exact Ho. clear - Hs; lia. } exact GR2.
Qed.

Theorem shl_core fx R M (sp o r k fb : Z) (len : nat) (sto : L5.bstore) (wsR : list Z) (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 : Z) :
  let b := L5.BO fb (Datatypes.S len) sto in let d := L5.bo_data o b in let cap := L5.bo_cap b in let ws := firstn len wsR in
  getr R (reg 2) = Z_to_bv 64 (sp - 112) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 k -> 1 <= k <= 63 ->
  getr R (reg 18) = Z_to_bv 64 (o + 8) -> getr R (reg 21) = Z_to_bv 64 SB -> getr R (reg 22) = Z_to_bv 64 (o / 8 + SB) ->
  getr R (reg 23) = Z_to_bv 64 ((o + 8) / 8 + SB) -> (1 <= len)%nat ->
  L5.u64_at RSEGS M (sp - 8) r -> L5.ra_ok r ->
  L5.u64_at RSEGS M (sp - 16) v8 -> L5.u64_at RSEGS M (sp - 24) v9 -> L5.u64_at RSEGS M (sp - 32) v18 -> L5.u64_at RSEGS M (sp - 40) v19 -> L5.u64_at RSEGS M (sp - 48) v20 -> L5.u64_at RSEGS M (sp - 56) v21 -> L5.u64_at RSEGS M (sp - 64) v22 -> L5.u64_at RSEGS M (sp - 72) v23 -> L5.u64_at RSEGS M (sp - 80) v24 -> L5.u64_at RSEGS M (sp - 88) v25 -> L5.u64_at RSEGS M (sp - 96) v26 ->
  0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 -> 0 <= v20 < 2 ^ 64 -> 0 <= v21 < 2 ^ 64 -> 0 <= v22 < 2 ^ 64 -> 0 <= v23 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v25 < 2 ^ 64 -> 0 <= v26 < 2 ^ 64 ->
  mfacts M sp o d cap ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b wsR -> nth len wsR 0 = 0 -> Z.of_nat len + 1 <= cap ->
  match sto with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end ->
  exists fx' R' M',
    msteps RSEGS (st fx R RZRET M) (st fx' R' r M')
    /\ (forall x, In x KSC -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ getr R' (reg 8) = Z_to_bv 64 v8 /\ getr R' (reg 9) = Z_to_bv 64 v9 /\ getr R' (reg 18) = Z_to_bv 64 v18 /\ getr R' (reg 19) = Z_to_bv 64 v19 /\ getr R' (reg 20) = Z_to_bv 64 v20 /\ getr R' (reg 21) = Z_to_bv 64 v21 /\ getr R' (reg 22) = Z_to_bv 64 v22 /\ getr R' (reg 23) = Z_to_bv 64 v23 /\ getr R' (reg 24) = Z_to_bv 64 v24 /\ getr R' (reg 25) = Z_to_bv 64 v25 /\ getr R' (reg 26) = Z_to_bv 64 v26
    /\ (let wl := shl_words ws k in let n' := L5W.rlen wl in
        L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land fb 253 else fb) n' (st_after sto wl)) /\ L5.limbs_at RSEGS M' d wl)
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (o <= a < o + 16) -> ~ (sp - 128 <= a < sp - 96) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  cbn zeta. intros G2 G8 G9 Hk G18 G21 G22 G23 Lpos C8 RA C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 C96 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 MFM OB OL TOP0 CAP ODYN.
  pose proof MFM as [[SPR A16] W128 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ VZ].
  unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  set (cap := match sto with L5.BInl _ _ => 2 | L5.BDyn c _ => c end) in *.
  pose proof OB as (O0 & Ffb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Ffb, O8, OST. destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  set (ws := firstn len wsR) in *.
  assert (WOR : words_ok wsR) by exact Rws.
  assert (WL : length ws = len). { subst ws. rewrite length_firstn, Lws. clear; lia. }
  assert (WO : words_ok ws). { subst ws. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) WOR w). eapply L5BLK.in_firstn. exact Hw. }
  assert (WS : L5.limbs_at RSEGS M d wsR).
  { subst d. destruct sto as [w0 w1|c q]. 2: exact LAT. destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). rewrite LAT. intros i Hi. rewrite length_firstn in Hi. cbn [length Nat.min] in Hi.
    destruct i as [|[|i]]. { cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by (clear; lia). exact O16. }
    { destruct len as [|ly]. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by (clear; lia). exact O24. }
    exfalso. destruct len as [|[|ly]]; cbn in Hi; clear - Hi Hl2; lia. }
  set (orig := ws ++ [0]).
  assert (NTH : forall i, (i <= len)%nat -> nth i wsR 0 = nth_w orig i).
  { intros i Hi. unfold nth_w, orig. destruct (Nat.eq_dec i len) as [->|NE].
    - rewrite app_nth2 by (rewrite WL; clear; lia). rewrite WL, Nat.sub_diag. cbn [nth]. exact TOP0.
    - rewrite app_nth1 by (rewrite WL; clear - Hi NE; lia). subst ws. rewrite <- (firstn_skipn len wsR) at 1. rewrite app_nth1. reflexivity. rewrite length_firstn, Lws. clear - Hi NE; lia. }
  assert (LIMBS : forall i, (i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (nth_w orig i)). { intros i Hi. rewrite <- NTH by exact Hi. apply WS. rewrite Lws. clear - Hi; lia. }
  assert (WOO : words_ok orig). { apply words_ok_app. exact WO. constructor. clear; lia. constructor. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 128 + 128 <= o \/ o + 32 <= sp - 128) by (clear - FRO; lia). assert (FRDp : sp - 128 + 128 <= d \/ d + 8 * cap <= sp - 128) by (clear - FRD; lia).
  assert (DIMGp : 65536 + 6438912 <= d \/ d + 8 * cap <= 65536) by (clear - DIMG; lia).
  assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia). assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  assert (HVL1 : 1 <= Z.of_nat len <= 134217728) by (clear - Lpos CAP CAPR; lia). assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by (clear - CAP CAPR Lpos; lia).
  pose proof (mask_range k ltac:(clear - Hk; lia)) as MR.
  set (wl := shl_words ws k).
  assert (WLL : length wl = Datatypes.S len) by (subst wl; rewrite shl_words_length, WL; reflexivity).
  assert (WLO : words_ok wl) by (subst wl; apply shl_words_ok; [clear - Hk; lia | exact WO]).
  (* [comment removed for export] *)
  assert (PART1 : exists fx1 R1 M1, msteps RSEGS (st fx R RZRET M) (st fx1 R1 L5ARED.REDUCE M1)
      /\ (forall x, In x KSP -> getr R1 (reg x) = getr R (reg x)) /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 1) = Z_to_bv 64 REDRET
      /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (nth_w wl i))
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (sp - 120 <= a < sp - 96) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ mem_grows M M1).
  { assert (RUN : exists fx1 R1 M1, mem_grows M M1 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 112 <= a < sp - 96) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
               /\ msteps RSEGS (st fx R RZRET M) (st fx1 R1 HEAD M1) /\ (forall x, In x [2; 3; 4; 8; 9; 21; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
               /\ getr R1 (reg 18) = Z_to_bv 64 (Z.of_nat len) /\ getr R1 (reg 20) = Z_to_bv 64 (64 - k) /\ getr R1 (reg 22) = Z_to_bv 64 (2 ^ k - 1)
               /\ L5.u64_at RSEGS M1 (sp - 112) d /\ L5.u64_at RSEGS M1 (sp - 104) (Z.of_nat len + 1)).
    { subst d cap. destruct sto as [w0 w1|c q].
      + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (EL1 : len = 1%nat) by (clear - Lpos Hl2; lia).
        assert (O8two : L5.u64_at RSEGS M (o + 8) 2). { rewrite EL1 in O8. exact O8. }
        pose proof (vshBi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => fb | 41%nat => k | 43%nat => U R 1 | 58%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR18 & bR20 & bR22 & bVL & bVD)).
        rewrite (mask_identL k Hk) in bR22.
        exists fx1, R1, M1. split. exact MG1. split. { intros a Ha Hn. apply bFZ. exact Ha. clear - Hn; lia. } split. exact bMS.
        split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_vshBi); vm_compute; reflexivity. }
        rewrite EL1. change (Z.of_nat 1) with 1.
        split. exact bR18. split. { rewrite bR20. f_equal. clear; lia. } split. { rewrite <- bR22. symmetry. apply Z_to_bv_bv_unsigned. }
        split. exact bVD. exact bVL.
      + destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
        assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 0 <= c < 2 ^ 64) by (clear - Hcap; lia).
        assert (HVLC : 1 <= c - Z.of_nat len <= 134217728) by (clear - HVCL; lia).
        assert (O8s : L5.u64_at RSEGS M (o + 8) (Z.of_nat len + 1)). { replace (Z.of_nat len + 1) with (Z.of_nat (Datatypes.S len)) by (clear; lia). exact O8. }
        pose proof (vshBd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 41%nat => k | 43%nat => U R 1 | 58%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR18 & bR20 & bR22 & bVL & bVD)).
        rewrite (mask_identL k Hk) in bR22.
        exists fx1, R1, M1. split. exact MG1. split. { intros a Ha Hn. apply bFZ. exact Ha. clear - Hn; lia. } split. exact bMS.
        split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_vshBd); vm_compute; reflexivity. }
        split. exact bR18. split. { rewrite bR20. f_equal. clear; lia. } split. { rewrite <- bR22. symmetry. apply Z_to_bv_bv_unsigned. }
        split. exact bVD. exact bVL. }
    destruct RUN as (fx1 & R1 & M1 & MG1 & FR1 & MS1 & K1 & B18 & B20 & B22 & BVD & BVL).
    assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact MG1. intros a Ha _ _ Hs. apply FR1. exact Ha. clear - Hs; lia. }
    destruct (sloop len fx1 R1 M1 sp o d cap k len orig MF1 ltac:(clear; lia) Lpos CAP Hk WOO) as (fx2 & R2 & M2 & MS2 & K2 & R2_10 & R2_1 & LIMBS2 & FR2 & GR2).
    { split. { intros j Hj. eapply L5C.u64_at_agree. 4:{ apply LIMBS. exact Hj. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hj; lia.
               intros a Ha. apply FR1. clear - Ha DR CAPR CAP Hj; lia. clear - Ha Hj CAP FRD; lia. }
      intros j Hj. exfalso. clear - Hj. lia. }
    { unfold at_shead. repeat split; try (first [assumption | rewrite (K1 _) by inl; assumption]). }
    exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. exact MS2. }
    split. { intros x Hx. rewrite (K2 x). apply K1. exact Hx. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. }
    split. exact R2_10. split. exact R2_1.
    split. { intros i Hi. subst wl. rewrite shl_words_nth by (rewrite WL; exact Hi). apply LIMBS2. exact Hi. }
    split. { intros a Ha Hn Hs. rewrite (FR2 a Ha Hn). apply FR1. exact Ha. clear - Hs; lia. clear - Hs; lia. }
    eapply mem_grows_trans; eauto. }
  destruct PART1 as (fx1 & R1 & M1 & MS1 & K1 & R1_10 & R1_1 & LIMBS1 & FR1 & GR1).
  assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact GR1. intros i Hi Hd _ Hs. apply FR1. exact Hi. clear - Hd CAP CAPR; lia. clear - Hs; lia. }
  assert (HDR1 : forall a v, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb OD CAP; lia. clear - Hj Ha Hb FRO; lia. }
  assert (FB1 : L5.u8_at RSEGS M1 o fb). { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR1. clear - Hj OR; lia. clear - Hj OD CAP; lia. clear - Hj FRO; lia. }
  set (b1 := L5.BO fb (Datatypes.S len) (st_after sto wl)).
  assert (OB1 : L5.big_at RSEGS M1 o b1 /\ L5C.obj_limbs RSEGS M1 b1 wl).
  { subst b1 d cap. unfold L5.big_at, L5C.obj_limbs, st_after. cbn [L5.bo_fb L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (EL1 : len = 1%nat) by (clear - Hl2 Lpos; lia). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B0.
        split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS1. clear; lia. }
        split. { replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by (clear; lia). apply LIMBS1. clear - EL1; lia. }
        split. exact Hl2. split. apply words_ok_nth; exact WLO. apply words_ok_nth; exact WLO.
      + split. exact WLL. split. exact WLO.
        assert (E2 : forall l : list Z, length l = 2%nat -> l = firstn 2 [nth_w l 0; nth_w l 1]). { intros l Hl. destruct l as [|a [|b0 [|c0 l]]]; cbn in Hl; try discriminate. reflexivity. }
        rewrite EL1. apply E2. rewrite WLL, EL1. reflexivity.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B1.
        assert (HDR2 : forall a v, o + 16 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
        { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb ODYN CAP; lia. clear - Hj Ha Hb FRO; lia. }
        split. { apply HDR2. clear; lia. clear; lia. exact O16. } split. { apply HDR2. clear; lia. clear; lia. exact O24. }
        split. exact Hlc. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH.
      + split. exact WLL. split. exact WLO. intros i Hi. rewrite WLL in Hi. apply LIMBS1. clear - Hi; lia. }
  destruct OB1 as [OB1 OL1].
  assert (XF1 : forall a v, sp - 96 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { apply saved_back. 2: clear - SPR; lia. intros a Ha Hs. apply FR1. exact Ha. clear - Hs FRD CAP; lia. clear - Hs; lia. }
  assert (EDC : L5.bo_data o b1 = d /\ L5.bo_cap b1 = cap). { subst b1 d cap. unfold L5.bo_data, L5.bo_cap, st_after. cbn [L5.bo_st]. destruct sto; split; reflexivity. }
  destruct EDC as [ED EC].
  destruct (shl_tail fx1 R1 M1 sp o r b1 wl v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26) as (fx3 & R3 & M3 & MS3 & K3 & T2 & T10 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & OB3 & FR3 & GR3).
  all: try (apply XF1; [clear; lia | clear; lia | assumption]); try assumption.
  { rewrite (K1 2%nat) by inl. exact G2. } { rewrite (K1 8%nat) by inl. exact G8. }
  { rewrite ED, EC. exact MF1. }
  cbn zeta in OB3. replace (L5.bo_fb b1) with fb in OB3 by reflexivity. replace (L5.bo_st b1) with (st_after sto wl) in OB3 by reflexivity.
  exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. exact MS3. }
  split. { intros x Hx. rewrite (K3 x Hx). apply K1. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. }
  split. exact T2. split. exact T10. split. exact T8. split. exact T9. split. exact T18. split. exact T19. split. exact T20. split. exact T21. split. exact T22. split. exact T23. split. exact T24. split. exact T25. split. exact T26.
  split. { split. exact OB3. intros i Hi. rewrite WLL in Hi. eapply L5C.u64_at_agree. 4:{ apply LIMBS1. clear - Hi; lia. }
           2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply FR3. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi CAP OD; lia. clear - Hj Hi CAP FRD; lia. }
  split. { intros a Ha Hd Ho Hs. rewrite FR3. apply FR1. exact Ha. exact Hd. clear - Hs; lia. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. exact GR1. exact GR3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem shl0_core fx R M (sp o r : Z) (b : L5.bigobj) (ws : list Z) :
  let d := L5.bo_data o b in let cap := L5.bo_cap b in
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  mfacts M sp o d cap ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> Z.of_nat (L5.bo_len b) <= 134217728 ->
  exists fx' R' M',
    msteps RSEGS (st fx R SHL M) (st fx' R' r M')
    /\ (forall x, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ (let n' := L5W.rlen ws in L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land (L5.bo_fb b) 253 else L5.bo_fb b) n' (L5.bo_st b)))
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> ~ (sp - 128 <= a < sp) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  cbn zeta. intros G2 G10 G11 G1 RA MFM OB OL LEN.
  pose proof MFM as [[SPR A16] W128 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ VZ].
  pose proof OB as (O0 & Ffb & O8 & OST).
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a.
  assert (FROp : sp - 128 + 128 <= o \/ o + 32 <= sp - 128) by (clear - FRO; lia).
  assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia).
  assert (HVL : 0 <= Z.of_nat (L5.bo_len b) <= 134217728) by (clear - LEN; lia).
  assert (HVF : 0 <= L5.bo_fb b <= 255) by (clear - Ffb; lia).
  assert (ENTRY : exists fx1 R1 M1, mem_grows M M1 /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp - 112 + 112) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
       /\ msteps RSEGS (st fx R SHL M) (st fx1 R1 L5ARED.REDUCE M1) /\ (forall x, In x [3; 4; 10; 27]%nat -> getr R1 (reg x) = getr R (reg x))
       /\ getr R1 (reg 1) = Z_to_bv 64 REDRET /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 112) /\ getr R1 (reg 8) = Z_to_bv 64 o
       /\ L5.u64_at RSEGS M1 (sp - 96) (U R 26) /\ L5.u64_at RSEGS M1 (sp - 88) (U R 25) /\ L5.u64_at RSEGS M1 (sp - 80) (U R 24) /\ L5.u64_at RSEGS M1 (sp - 72) (U R 23)
       /\ L5.u64_at RSEGS M1 (sp - 64) (U R 22) /\ L5.u64_at RSEGS M1 (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1 (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1 (sp - 40) (U R 19)
       /\ L5.u64_at RSEGS M1 (sp - 32) (U R 18) /\ L5.u64_at RSEGS M1 (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1 (sp - 16) (U R 8) /\ L5.u64_at RSEGS M1 (sp - 8) (U R 1)).
  { destruct b as [fb len sto]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1).
      pose proof (vshA0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1 & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR21 & aR22 & aR23 & aR24 & CVL & CVD & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1. split. exact MG1. split. exact aFZ. split. exact aMS.
      split. { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vshA0); vm_compute; reflexivity. }
      unfold U. repeat split; assumption.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia).
      pose proof (vshA0d_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 59%nat => q | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1 & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR21 & aR22 & aR23 & aR24 & CVL & CVD & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1. split. exact MG1. split. exact aFZ. split. exact aMS.
      split. { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vshA0d); vm_compute; reflexivity. }
      unfold U. repeat split; assumption. }
  destruct ENTRY as (fx1 & R1 & M1 & MG1 & aFZ & aMS & aKS & aR1 & aR2 & aR8 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  assert (MF1 : mfacts M1 sp o (L5.bo_data o b) (L5.bo_cap b)). { eapply mfacts_keep. exact MFM. exact MG1. intros i Hi _ _ Hn. apply aFZ. exact Hi. clear - Hn; lia. }
  assert (OB1 : L5.big_at RSEGS M1 o b). { eapply L5C.big_at_agree. 4: exact OB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply aFZ. clear - Hj OR; lia. clear - Hj FRO; lia. }
  assert (OL1 : L5C.obj_limbs RSEGS M1 b ws).
  { destruct OL as (L1 & W1 & LAT). split. exact L1. split. exact W1. destruct b as [fb len sto]. cbn [L5.bo_len L5.bo_st] in *. destruct sto as [w0 w1|c q]. exact LAT.
    unfold L5.bo_data, L5.bo_cap in DR, FRD, CAPR. cbn [L5.bo_st] in DR, FRD, CAPR. destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). cbn [L5.bo_len L5.bo_st] in Hlc.
    eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - Q4096; lia. 2: rewrite L1; clear - Q47 Hlc Hcap; lia. intros j Hj. apply aFZ. clear - Hj Q4096 Q47 Hcap Hlc L1; lia. rewrite L1 in Hj. clear - Hj FRD Hlc; lia. }
  assert (RR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  assert (C8r : L5.u64_at RSEGS M1 (sp - 8) r). { rewrite <- (L5BLK.U_of R 1 r G1 RR). exact C8. }
  destruct (shl_tail fx1 R1 M1 sp o r b ws (U R 8) (U R 9) (U R 18) (U R 19) (U R 20) (U R 21) (U R 22) (U R 23) (U R 24) (U R 25) (U R 26)) as (fx3 & R3 & M3 & MS3 & K3 & T2 & T10 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & OB3 & FR3 & GR3).
  all: try apply UR; try assumption.
  { rewrite (aKS 10%nat) by inl. exact G10. }
  exists fx3, R3, M3. split. { eapply msteps_trans. exact aMS. exact MS3. }
  split. { intros x Hx. cbn in Hx.
    destruct Hx as [<-|Hx]. { rewrite (K3 3%nat) by inl. apply aKS. inl. }
    destruct Hx as [<-|Hx]. { rewrite (K3 4%nat) by inl. apply aKS. inl. }
    destruct Hx as [<-|Hx]. { rewrite T8. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T9. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T18. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T19. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T20. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T21. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T22. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T23. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T24. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T25. symmetry. apply U_to. } destruct Hx as [<-|Hx]. { rewrite T26. symmetry. apply U_to. }
    destruct Hx as [<-|[]]. rewrite (K3 27%nat) by inl. apply aKS. inl. }
  split. exact T2. split. exact T10. split. exact OB3.
  split. { intros a Ha Ho Hs. rewrite FR3. apply aFZ. exact Ha. clear - Hs; lia. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. exact MG1. exact GR3.
Qed.

End SCFG_1.
End L5ASHLK.

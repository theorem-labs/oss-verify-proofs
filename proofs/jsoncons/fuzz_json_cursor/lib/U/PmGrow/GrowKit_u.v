(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module GK.
Abbreviation RSEGS := PML.RSEGS.
Definition HULL_LO : Z := 0x10000.  Definition HULL_HI : Z := 0xf8000.

Definition has (cells : list kentry) (X : kentry) : bool := existsb (APC.kentry_eqb X) cells.
Lemma has_In : forall cells X, has cells X = true -> In X cells.
Proof. intros cells X HX. unfold has in HX. apply existsb_exists in HX as (Y & HY & He). apply APS.kentry_eqb_eq in He. subst Y. exact HY. Qed.

Lemma kword8_intro : forall E (M : PML.mem) a v A z, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  L5.u8_at RSEGS M A z -> kentry_ok RSEGS E M (KWord a 1 v).
Proof.
  intros E M a v A z Ha H0 H1 Hv Hz Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 1)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u64_of_Z by exact Hz. exact Hu.
Qed.
Lemma kword8_elim : forall E (M : PML.mem) a v A z, kentry_ok RSEGS E M (KWord a 1 v) -> estart E a = A -> bv_unsigned (edenot E v) = z -> L5.u8_at RSEGS M A z.
Proof.
  intros E M a v A z (_ & Hfl & Hr) Ha Hz. unfold L5.u8_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr, <- Hz. reflexivity.
Qed.

Lemma u8_at_mod : forall (M : PML.mem) a z, L5.u8_at RSEGS M a z <-> L5.u8_at RSEGS M a (z mod 256).
Proof.
  intros M a z. unfold L5.u8_at. replace (Z_to_bv 8 (z mod 256)) with (Z_to_bv 8 z); [tauto|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma defined_of_u64 : forall (M : PML.mem) a v, L5.u64_at RSEGS M a v -> HULL_HI <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof.
  intros M a v Hu Ha H8 i Hi. unfold L5.u64_at in Hu. unfold HULL_HI in Ha.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) 8 _ Hu).
  - rewrite !u64_of_Z by lia. cbn. lia.
  - rewrite u64_of_Z by lia. unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma defined_of_u8 : forall (M : PML.mem) a v, L5.u8_at RSEGS M a v -> HULL_HI <= a -> a + 1 <= 2 ^ 64 -> L5.defined M a 1.
Proof.
  intros M a v Hu Ha H8 i Hi. unfold L5.u8_at in Hu. unfold HULL_HI in Ha.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) 1 _ Hu).
  - rewrite !u64_of_Z by lia. cbn. lia.
  - rewrite u64_of_Z by lia. unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma defined_3x8 : forall (M : PML.mem) o, L5.defined M o 8 -> L5.defined M (o + 8) 8 -> L5.defined M (o + 16) 8 -> L5.defined M o 24.
Proof.
  intros M o D0 D8 D16 i Hi. destruct (Z_lt_dec i 8); [|destruct (Z_lt_dec i 16)].
  - exact (D0 i ltac:(lia)).
  - replace (o + i) with (o + 8 + (i - 8)) by lia. exact (D8 (i - 8) ltac:(lia)).
  - replace (o + i) with (o + 16 + (i - 16)) by lia. exact (D16 (i - 16) ltac:(lia)).
Qed.

Lemma rdn_overlay_nth : forall (M : PML.mem) (n : nat) a bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hr Hd i Hi; [lia|].
  cbn [rdn] in Hr. rewrite (L5C.add1_lit a) in Hr. pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (M (Z_to_bv 64 a)) as [b0|] eqn:EM; [|contradiction].
  destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:ER; [|discriminate]. injection Hr as <-.
  destruct i as [|i]; [cbn [nth Z.of_nat]; rewrite Z.add_0_r; exact EM|].
  cbn [nth]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest ER); [|lia].
  intros j Hj. replace (a + 1 + j) with (a + (1 + j)) by lia. apply Hd. lia.
Qed.
Definition zeros (M : PML.mem) (a n : Z) : Prop := forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Lemma zeros_of_u64 : forall (M : PML.mem) a, L5.u64_at RSEGS M a 0 -> HULL_HI <= a -> a + 8 <= 2 ^ 64 -> zeros M a 8.
Proof.
  intros M a Hu Ha H8 i Hi. pose proof (defined_of_u64 M a 0 Hu Ha H8) as Hd. unfold L5.u64_at in Hu.
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (rdn_overlay_nth M 8 a _ Hu Hd (Z.to_nat i) ltac:(lia)). f_equal.
  assert (Hc : (Z.to_nat i < 8)%nat) by lia. revert Hc. generalize (Z.to_nat i). intros k Hk.
  do 8 (destruct k as [|k]; [apply bv_eq; reflexivity|]). lia.
Qed.
Lemma zeros_app : forall (M : PML.mem) a n m, 0 <= n -> zeros M a n -> zeros M (a + n) m -> zeros M a (n + m).
Proof. intros M a n m Hn H1 H2 i Hi. destruct (Z_lt_dec i n); [apply H1; lia|]. replace (a + i) with (a + n + (i - n)) by lia. apply H2. lia. Qed.
Lemma kzero_intro : forall E (M : PML.mem) a n A N, estart E a = A -> elenZ E n = N -> 0 <= A -> A + N <= 2 ^ 64 -> A < 2 ^ 64 -> 0 <= N -> zeros M A N -> kentry_ok RSEGS E M (KZero a n).
Proof. intros E M a n A N Ha Hn H0 H1 H2 H3 Hz. cbn [kentry_ok]. rewrite Ha, Hn. split; [unfold flat; rewrite Ha; lia | exact Hz]. Qed.

Lemma den_hd : forall E bl, snd (hd (0, 0) (CH2.den E bl)) = bv_unsigned (edenot E (snd (hd (ELit 0, ELit 0) bl))).
Proof. intros E [|b r]; reflexivity. Qed.
Lemma den_hd_fst : forall E bl, fst (hd (0, 0) (CH2.den E bl)) = bv_unsigned (edenot E (fst (hd (ELit 0, ELit 0) bl))).
Proof. intros E [|b r]; reflexivity. Qed.

Lemma hpres_scr : forall (L : heap_layout) LBk sp scr scr' W (M M' : PML.mem),
  0 <= scr <= scr' -> L5.defined M (sp - scr') scr' -> 0 <= sp - scr' -> hl_errno L + 4 <= sp - scr' -> hl_ceil L <= sp - scr' -> sp <= 2 ^ 47 ->
  L5C.hpres L LBk sp scr W M M' -> L5C.hpres L LBk sp scr' W M M'.
Proof.
  intros L LBk sp scr scr' W M M' Hle Hdef H0 He Hceil Htop HP. apply L5C.hpres_intro.
  - intros a (K1 & K2 & K3 & K4). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). split; [exact K1|]. split; [|split; assumption].
    destruct K2 as [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C].
  - intros j Hj. destruct (Z_lt_dec j (scr' - scr)) as [Hlo|Hhi].
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - scr' + j) HP); [lia | right; left; split; lia | unfold in_errno; lia | apply Hdef; lia].
    + replace (sp - scr' + j) with (sp - scr + (j - (scr' - scr))) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ HP). lia.
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [|exact HE | exact Hd].
    destruct HC as [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C].
Qed.
End GK.

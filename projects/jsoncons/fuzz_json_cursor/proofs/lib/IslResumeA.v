(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec SymStepR StoreOk IslInterpA IslSoundA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISLRA.
Import ISLA. Import ISLSA.

Section Resume.
Variable segs : list Segment.
Variable C : cfg.
Variable E : nat -> word.
Hypothesis IO : init_ok C E.
Definition CSAVEDZ : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma clobber_length : forall l k, length (clobber_regs k l) = length l.
Proof. induction l as [|v t IH]; intros k; cbn; [reflexivity|]. f_equal. apply IH. Qed.
Lemma nth_clobber : forall l k r, (r < length l)%nat ->
  nth r (clobber_regs k l) (AL 0) = if (Nat.eqb (k + r) 0 || existsb (Nat.eqb (k + r)) CSAVEDN)%bool then nth r l (AL 0) else AU.
Proof.
  induction l as [|v t IH]; intros k [|r] H; cbn [length] in H; try lia; cbn [clobber_regs nth].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S k) r) by lia. rewrite Nat.add_succ_r. reflexivity.
Qed.
Lemma getreg_after_call : forall s v ret spoff r, length (s_regs s) = 32%nat ->
  getreg (after_call C s v ret spoff) r =
    if Nat.eqb (rnat r) 10 then v else if (Nat.eqb (rnat r) 0 || existsb (Nat.eqb (rnat r)) CSAVEDN)%bool then getreg s r else AU.
Proof.
  intros s v ret spoff r Hl. unfold getreg, after_call. cbn [s_regs]. pose proof (rnat_lt r) as Hr.
  destruct (Nat.eqb_spec (rnat r) 10) as [H10|H10].
  - rewrite H10. apply nth_upd_same. rewrite clobber_length, Hl. lia.
  - rewrite nth_upd_other by (intro Hc; apply H10; symmetry; exact Hc). rewrite nth_clobber by (rewrite Hl; exact Hr). reflexivity.
Qed.
Lemma csavedn_z : forall r : reg, existsb (Nat.eqb (rnat r)) CSAVEDN = true -> In (bv_unsigned r) CSAVEDZ.
Proof.
  intros r H. unfold CSAVEDN in H. unfold rnat in H. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  cbn [existsb] in H. repeat (apply orb_true_iff in H; destruct H as [H|H]; [apply Nat.eqb_eq in H; cbn; lia|]). discriminate H.
Qed.
Lemma rnat_of_nat : forall k, (k < 32)%nat -> rnat (Z_to_bv 5 (Z.of_nat k)) = k.
Proof. intros k Hk. unfold rnat. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 5) with 32; lia). apply Nat2Z.id. Qed.

Lemma prune_below_find : forall lo t k b, PositiveMap.find k (prune_below lo t) = Some b -> PositiveMap.find k t = Some b /\ lo <= unzkey k.
Proof.
  intros lo t k b. unfold prune_below.
  assert (G : forall (L : list (positive * abyte)) (acc : PositiveMap.t abyte),
              PositiveMap.find k (fold_left (fun acc (kb : positive * abyte) => if unzkey (fst kb) <? lo then PositiveMap.remove (fst kb) acc else acc) L acc) = Some b ->
              PositiveMap.find k acc = Some b /\ (forall b' : abyte, In (k, b') L -> ~ unzkey k < lo)).
  { induction L as [|[q b'] L IH]; intros acc H; cbn [fold_left] in H.
    - split; [exact H | intros b' []].
    - destruct (IH _ H) as [H1 H2]. cbn [fst] in H1. destruct (Z.ltb_spec (unzkey q) lo) as [Hlt|Hge].
      + destruct (Pos.eq_dec k q) as [->|Hne]; [rewrite PositiveMap.grs in H1; discriminate|]. rewrite PositiveMap.gro in H1 by exact Hne.
        split; [exact H1|]. intros b'' [Hin|Hin]; [injection Hin as <- <-; contradiction | exact (H2 _ Hin)].
      + split; [exact H1|]. intros b'' [Hin|Hin]; [injection Hin as <- <-; lia | exact (H2 _ Hin)]. }
  intros H. destruct (G _ _ H) as [H1 H2]. split; [exact H1|]. pose proof (H2 b (PositiveMap.elements_correct t k H1)). lia.
Qed.
Lemma unzkey_zkey : forall z, unzkey (zkey z) = z.
Proof. intros [|p|p]; reflexivity. Qed.
Lemma prune_rgs_nth : forall rgs ts lo j t', nth_error (prune_rgs C rgs ts lo) j = Some t' ->
  exists t, nth_error ts j = Some t /\
    forall off b, PositiveMap.find (zkey off) t' = Some b -> PositiveMap.find (zkey off) t = Some b /\ (forall rg, nth_error rgs j = Some rg -> rg_k rg = c_spk C -> lo <= off).
Proof.
  induction rgs as [|rg rgs IH]; intros ts lo j t' H; cbn [prune_rgs] in H.
  - exists t'. split; [exact H|]. intros off b Hf. split; [exact Hf|]. intros rg0 Hn. destruct j; discriminate Hn.
  - destruct ts as [|t ts]; [destruct j; discriminate H|]. destruct j as [|j]; cbn [nth_error] in H |- *.
    + injection H as <-. exists t. split; [reflexivity|]. intros off b Hf. destruct (Nat.eqb_spec (rg_k rg) (c_spk C)) as [Hk|Hk].
      * destruct (prune_below_find _ _ _ _ Hf) as [H1 H2]. rewrite unzkey_zkey in H2. split; [exact H1|]. intros rg0 Hn _. injection Hn as <-. exact H2.
      * split; [exact Hf|]. intros rg0 Hn Hk0. injection Hn as <-. contradiction.
    + exact (IH ts lo j t' H).
Qed.

Lemma wrbs_abs_lit : forall n s a b s1, wrbs segs C s (AAbs a) (repeat (BL b) n) = Some s1 ->
  s_regs s1 = s_regs s /\ s_rgs s1 = s_rgs s /\ s_pc s1 = s_pc s /\ s_resv s1 = s_resv s /\
  (forall a', PositiveMap.find (zkey a') (s_abs s1) = if ((a <=? a') && (a' <? a + Z.of_nat n))%bool then Some (BL b) else PositiveMap.find (zkey a') (s_abs s)) /\
  (forall a', a <= a' < a + Z.of_nat n -> wr_chk segs C (AAbs a') = true).
Proof.
  induction n as [|n IH]; intros s a b s1 H; cbn [repeat wrbs] in H.
  - injection H as <-. repeat split; try reflexivity. 2: intros; lia.
    intros a'. destruct ((a <=? a') && (a' <? a + Z.of_nat 0))%bool eqn:Hc; [|reflexivity]. apply andb_true_iff in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. apply andb_true_iff in Hc. destruct Hc as [Hchk _].
    cbn [ashift] in H. destruct (IH _ _ _ _ H) as (R1 & R2 & R3 & R4 & R5 & R6). cbn [wrb s_regs s_rgs s_pc s_resv s_abs] in R1, R2, R3, R4, R5.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split.
    + intros a'. rewrite R5. destruct (Z.eq_dec a' a) as [->|Hne].
      * rewrite PositiveMap.gss. replace ((a <=? a) && (a <? a + Z.of_nat (S n)))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        destruct ((a + 1 <=? a) && (a <? a + 1 + Z.of_nat n))%bool eqn:Hc; [|reflexivity]. apply andb_true_iff in Hc. destruct Hc as [H1 _]. apply Z.leb_le in H1. lia.
      * rewrite PositiveMap.gso by (intro Hc; apply Hne; apply zkey_inj; exact Hc).
        destruct ((a + 1 <=? a') && (a' <? a + 1 + Z.of_nat n))%bool eqn:H1; destruct ((a <=? a') && (a' <? a + Z.of_nat (S n)))%bool eqn:H2; try reflexivity; exfalso.
        -- apply andb_true_iff in H1. destruct H1 as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y. apply Bool.andb_false_iff in H2. destruct H2 as [H2|H2]; [apply Z.leb_gt in H2 | apply Z.ltb_ge in H2]; lia.
        -- apply andb_true_iff in H2. destruct H2 as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y. apply Bool.andb_false_iff in H1. destruct H1 as [H1|H1]; [apply Z.leb_gt in H1 | apply Z.ltb_ge in H1]; lia.
    + intros a' Ha'. destruct (Z.eq_dec a' a) as [->|Hne]; [exact Hchk|]. apply R6. lia.
Qed.

Lemma sum_memset_facts : forall M0 s R M rv dst c n spoff ret tp s2,
  sim segs C E M0 s R M rv -> sum_memset segs C s = Some (EvMemset dst c n spoff ret tp, s2) ->
  getr R (Z_to_bv 5 10) = Z_to_bv 64 dst /\ getr R (Z_to_bv 5 11) = Z_to_bv 64 c /\ getr R (Z_to_bv 5 12) = Z_to_bv 64 n /\
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ getr R (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (E (c_spk C)) + spoff) /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 tp /\ rv = None /\
  0 <= n /\ span_in (c_msok C) dst (Z.to_nat n) = true /\ (forall a', dst <= a' < dst + n -> wr_chk segs C (AAbs a') = true) /\
  s_pc s2 = ret /\ s_resv s2 = None.
Proof.
  intros M0 s R M rv dst c n spoff ret tp s2 Hsim H. unfold sum_memset in H.
  destruct (gr s 10) as [dst'| |] eqn:G10; try discriminate. destruct (gr s 11) as [c'| |] eqn:G11; try discriminate.
  destruct (gr s 12) as [n'| |] eqn:G12; try discriminate. destruct (gr s 1) as [ret'| |] eqn:G1; try discriminate.
  destruct (gr s 2) as [|k2 spoff'|] eqn:G2; try discriminate. destruct (gr s 4) as [tp'| |] eqn:G4; try discriminate. destruct (s_resv s) eqn:Gv; [discriminate|].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
  apply andb_true_iff in Hc. destruct Hc as [Hc Hsp]. apply andb_true_iff in Hc. destruct Hc as [Hk Hn]. apply Nat.eqb_eq in Hk. apply Z.leb_le in Hn.
  destruct (wrbs segs C s (AAbs dst') (repeat (BL (c' mod 256)) (Z.to_nat n'))) as [s1|] eqn:Hw; [|discriminate]. injection H as <- <- <- <- <- <- <-.
  destruct (wrbs_abs_lit _ _ _ _ _ Hw) as (_ & _ & _ & _ & _ & R6).
  assert (GR : forall k z, gr s k = z -> (k < 32)%nat -> z <> AU -> getr R (Z_to_bv 5 (Z.of_nat k)) = vden E z).
  { intros k z Hg Hk32 Hz. apply (sm_regs' segs C E M0 s R M rv _ z Hsim); [|exact Hz]. unfold getreg. rewrite rnat_of_nat by exact Hk32. exact Hg. }
  repeat split.
  - exact (GR 10%nat _ G10 ltac:(lia) ltac:(discriminate)).
  - exact (GR 11%nat _ G11 ltac:(lia) ltac:(discriminate)).
  - exact (GR 12%nat _ G12 ltac:(lia) ltac:(discriminate)).
  - exact (GR 1%nat _ G1 ltac:(lia) ltac:(discriminate)).
  - rewrite <- Hk. exact (GR 2%nat _ G2 ltac:(lia) ltac:(discriminate)).
  - exact (GR 4%nat _ G4 ltac:(lia) ltac:(discriminate)).
  - rewrite (sm_resv segs C E M0 _ _ _ _ Hsim), Gv. reflexivity.
  - exact Hn.
  - exact Hsp.
  - intros a' Ha'. apply R6. rewrite Z2Nat.id by lia. exact Ha'.
Qed.

Lemma resume_memset : forall M0 s R M rv dst c n spoff ret tp s2 (R' : bvmap 5 word) (M' : word -> option byte),
  sim segs C E M0 s R M rv -> sum_memset segs C s = Some (EvMemset dst c n spoff ret tp, s2) ->
  (forall r : reg, In (bv_unsigned r) CSAVEDZ -> getr R' r = getr R r) ->
  getr R' (Z_to_bv 5 10) = Z_to_bv 64 dst ->
  (forall i, 0 <= i < n -> M' (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 (c mod 256))) ->
  (forall a, 0 < a < c_abs_hi C -> ~ (dst <= a < dst + n) -> (in_ivs (c_wabs C) a = true \/ rdb0 segs C a <> None) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall j rg off, nth_error (c_rgs C) j = Some rg -> rg_lo rg <= off < rg_hi rg -> (rg_k rg = c_spk C -> spoff <= off) ->
      M' (Z_to_bv 64 (rbase E rg + off)) = M (Z_to_bv 64 (rbase E rg + off))) ->
  (forall j rg off, nth_error (c_rgs C) j = Some rg -> rg_lo rg <= off < rg_hi rg -> M' (Z_to_bv 64 (rbase E rg + off)) <> None) ->
  sim segs C E M' s2 R' M' None.
Proof.
  intros M0 s R M rv dst c n spoff ret tp s2 R' M' Hsim H CS A0 NEWB KA KR DR.
  pose proof H as H0. unfold sum_memset in H.
  destruct (gr s 10) as [dst'| |] eqn:G10; try discriminate. destruct (gr s 11) as [c'| |] eqn:G11; try discriminate.
  destruct (gr s 12) as [n'| |] eqn:G12; try discriminate. destruct (gr s 1) as [ret'| |] eqn:G1; try discriminate.
  destruct (gr s 2) as [|k2 spoff'|] eqn:G2; try discriminate. destruct (gr s 4) as [tp'| |] eqn:G4; try discriminate. destruct (s_resv s) eqn:Gv; [discriminate|].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
  apply andb_true_iff in Hc. destruct Hc as [Hc Hsp]. apply andb_true_iff in Hc. destruct Hc as [Hk Hn]. apply Nat.eqb_eq in Hk. apply Z.leb_le in Hn.
  destruct (wrbs segs C s (AAbs dst') (repeat (BL (c' mod 256)) (Z.to_nat n'))) as [s1|] eqn:Hw; [|discriminate]. injection H as <- <- <- <- <- <- <-.
  destruct (wrbs_abs_lit _ _ _ _ _ Hw) as (R1 & R2 & R3 & R4 & R5 & R6). rewrite Z2Nat.id in R5, R6 by lia.
  destruct Hsim as [Hr Hl Hz Hm Hv]. pose proof (io_hi C E IO) as Hhi.
  constructor.
  -
    intros r Hau. rewrite getreg_after_call in Hau |- * by (rewrite R1; exact Hl).
    destruct (Nat.eqb_spec (rnat r) 10) as [H10|H10].
    + assert (r = Z_to_bv 5 10) as -> by (apply rnat_inj; rewrite H10; reflexivity). rewrite A0. reflexivity.
    + destruct (Nat.eqb (rnat r) 0 || existsb (Nat.eqb (rnat r)) CSAVEDN)%bool eqn:Hcs; [|exfalso; exact (Hau eq_refl)].
      rewrite (getreg_newmem _ _ r R1) in Hau |- *.
      apply orb_true_iff in Hcs. destruct Hcs as [Hcs|Hcs].
      * apply Nat.eqb_eq in Hcs. assert (r = Z_to_bv 5 0) as -> by (apply rnat_inj; rewrite Hcs; reflexivity).
        unfold getreg. change (rnat (Z_to_bv 5 0)) with 0%nat. rewrite Hz. reflexivity.
      * rewrite (CS r (csavedn_z r Hcs)). exact (Hr r Hau).
  -   unfold after_call. cbn [s_regs]. rewrite upd_length, clobber_length, R1. exact Hl.
  -   unfold after_call. cbn [s_regs]. rewrite nth_upd_other by lia. rewrite nth_clobber by (rewrite R1, Hl; lia). cbn. rewrite R1. exact Hz.
  -
    destruct Hm as [MA MR MT MX MD]. unfold after_call. constructor; cbn [s_abs s_rgs].
    + intros a ab Hf. rewrite R5 in Hf. destruct ((dst' <=? a) && (a <? dst' + n'))%bool eqn:Hin.
      * apply andb_true_iff in Hin. destruct Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y. injection Hf as <-.
        pose proof (R6 a ltac:(lia)) as W. cbn [wr_chk] in W. apply andb_true_iff in W. destruct W as [W _]. apply andb_true_iff in W. destruct W as [W1 W2].
        apply andb_true_iff in W1. destruct W1 as [W0 W1]. apply Z.ltb_lt in W0. apply Z.ltb_lt in W1.
        split; [lia|]. split; [exact W2|]. replace a with (dst' + (a - dst')) by lia. rewrite (NEWB (a - dst')) by lia. reflexivity.
      * apply Bool.andb_false_iff in Hin. destruct (MA a ab Hf) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|].
        rewrite (KA a X1); [exact X3 | | left; exact X2]. destruct Hin as [Hin|Hin]; [apply Z.leb_gt in Hin | apply Z.ltb_ge in Hin]; lia.
    + intros j rg t' off ab Hj Ht' Hf'. rewrite R2 in Ht'. destruct (prune_rgs_nth _ _ _ _ _ Ht') as (t & Ht & PR). destruct (PR off ab Hf') as [Hf Hlo].
      destruct (MR j rg t off ab Hj Ht Hf) as [X1 X2]. split; [exact X1|]. rewrite (KR j rg off Hj X1 (Hlo rg Hj)). exact X2.
    + intros a Ha Hf ab Hab. rewrite R5 in Hf. destruct ((dst' <=? a) && (a <? dst' + n'))%bool eqn:Hin; [discriminate|].
      apply Bool.andb_false_iff in Hin. unfold rt_at, rb in MT |- *.
      rewrite (KA a Ha); [exact (MT a Ha Hf ab Hab) | | right; rewrite Hab; discriminate]. destruct Hin as [Hin|Hin]; [apply Z.leb_gt in Hin | apply Z.ltb_ge in Hin]; lia.
    + intros x. left. reflexivity.
    + exact DR.
  -   reflexivity.
Qed.

Lemma rdbs_rg_range : forall n s j off l rg, rdbs segs C s (ARg j off) n = Some l -> nth_error (c_rgs C) j = Some rg ->
  forall i, 0 <= i < Z.of_nat n -> rg_lo rg <= off + i < rg_hi rg.
Proof.
  induction n as [|n IH]; intros s j off l rg H Hj i Hi; [lia|]. cbn [rdbs] in H.
  destruct (rdb segs C s (ARg j off)) as [b|] eqn:Hb; [|discriminate]. cbn [ashift] in H.
  destruct (rdbs segs C s (ARg j (off + 1)) n) as [r|] eqn:Hr; [|discriminate].
  cbn [rdb] in Hb. rewrite Hj in Hb. destruct (nth_error (s_rgs s) j); [|discriminate].
  destruct ((rg_lo rg <=? off) && (off <? rg_hi rg))%bool eqn:Hc; [|discriminate]. apply andb_true_iff in Hc. destruct Hc as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  destruct (Z.eq_dec i 0) as [->|Hne]; [lia|]. pose proof (IH s j (off + 1) r rg Hr Hj (i - 1) ltac:(lia)). lia.
Qed.

Lemma sum_memcmp_facts : forall M0 s R M rv poff q n zs1 zs2 spoff ret tp s2,
  sim segs C E M0 s R M rv -> sum_memcmp segs C s = Some (EvMemcmp poff q n zs1 zs2 spoff ret tp, s2) ->
  getr R (Z_to_bv 5 10) = Z_to_bv 64 (bv_unsigned (E (c_spk C)) + poff) /\ getr R (Z_to_bv 5 11) = Z_to_bv 64 q /\ getr R (Z_to_bv 5 12) = Z_to_bv 64 n /\
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ getr R (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (E (c_spk C)) + spoff) /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 tp /\ rv = None /\
  0 <= n /\ span_in (c_rook C) q (Z.to_nat n) = true /\ spoff <= poff /\
  (exists j rg, nth_error (c_rgs C) j = Some rg /\ rg_k rg = c_spk C /\ forall i, 0 <= i < n -> rg_lo rg <= poff + i < rg_hi rg) /\
  rdn segs M (Z_to_bv 64 (bv_unsigned (E (c_spk C)) + poff)) (Z.to_nat n) = Some (zbytes zs1) /\
  rdn segs M (Z_to_bv 64 q) (Z.to_nat n) = Some (zbytes zs2) /\
  s_pc s2 = ret /\ s_resv s2 = None /\ s2 = after_call C s (AL (zmemcmp (zbytes zs1) (zbytes zs2))) ret spoff.
Proof.
  intros M0 s R M rv poff q n zs1 zs2 spoff ret tp s2 Hsim H. unfold sum_memcmp in H.
  destruct (gr s 10) as [|kp poff'|] eqn:G10; try discriminate. destruct (gr s 11) as [q'| |] eqn:G11; try discriminate.
  destruct (gr s 12) as [n'| |] eqn:G12; try discriminate. destruct (gr s 1) as [ret'| |] eqn:G1; try discriminate.
  destruct (gr s 2) as [|k2 spoff'|] eqn:G2; try discriminate. destruct (gr s 4) as [tp'| |] eqn:G4; try discriminate. destruct (s_resv s) eqn:Gv; [discriminate|].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
  apply andb_true_iff in Hc. destruct Hc as [Hc Hle]. apply andb_true_iff in Hc. destruct Hc as [Hc Hsp]. apply andb_true_iff in Hc. destruct Hc as [Hc Hn].
  apply andb_true_iff in Hc. destruct Hc as [Hk2 Hkp]. apply Nat.eqb_eq in Hk2. apply Nat.eqb_eq in Hkp. apply Z.leb_le in Hn. apply Z.leb_le in Hle.
  destruct (classify C (AS kp poff')) as [adp|] eqn:Hcl; [|discriminate].
  destruct (rdbs segs C s adp (Z.to_nat n')) as [l1|] eqn:Hr1; [|discriminate]. destruct (rdbs segs C s (AAbs q') (Z.to_nat n')) as [l2|] eqn:Hr2; [|discriminate].
  destruct (lits l1) as [zs1'|] eqn:Hl1; [|discriminate]. destruct (lits l2) as [zs2'|] eqn:Hl2; [|discriminate]. injection H as <- <- <- <- <- <- <- <- <-.
  assert (GR : forall k z, gr s k = z -> (k < 32)%nat -> z <> AU -> getr R (Z_to_bv 5 (Z.of_nat k)) = vden E z).
  { intros k z Hg Hk32 Hz. apply (sm_regs' segs C E M0 s R M rv _ z Hsim); [|exact Hz]. unfold getreg. rewrite rnat_of_nat by exact Hk32. exact Hg. }
  pose proof (classify_sound C E _ _ Hcl) as Had. pose proof Hcl as Hcl'. cbn [classify] in Hcl'.
  destruct (find_rg (c_rgs C) kp poff' 0) as [j|] eqn:Hfr; [|discriminate]. injection Hcl' as <-.
  destruct (find_rg_sound _ _ _ _ _ Hfr) as (rg & Hnth & _ & Hrk). rewrite Nat.sub_0_r in Hnth.
  pose proof (rdbs_sound segs C E M0 s M _ _ _ (sm_mem _ _ _ _ _ _ _ _ Hsim) Hr1) as D1. rewrite Had in D1. cbn [vden] in D1. rewrite (lits_sound _ _ _ Hl1) in D1.
  pose proof (rdbs_sound segs C E M0 s M _ _ _ (sm_mem _ _ _ _ _ _ _ _ Hsim) Hr2) as D2. cbn [aden] in D2. rewrite (lits_sound _ _ _ Hl2) in D2.
  rewrite <- Hkp. repeat split.
  - exact (GR 10%nat _ G10 ltac:(lia) ltac:(discriminate)).
  - exact (GR 11%nat _ G11 ltac:(lia) ltac:(discriminate)).
  - exact (GR 12%nat _ G12 ltac:(lia) ltac:(discriminate)).
  - exact (GR 1%nat _ G1 ltac:(lia) ltac:(discriminate)).
  - rewrite Hkp, <- Hk2. exact (GR 2%nat _ G2 ltac:(lia) ltac:(discriminate)).
  - exact (GR 4%nat _ G4 ltac:(lia) ltac:(discriminate)).
  - rewrite (sm_resv segs C E M0 _ _ _ _ Hsim), Gv. reflexivity.
  - exact Hn.
  - exact Hsp.
  - exact Hle.
  - exists j, rg. split; [exact Hnth|]. split; [exact Hrk|]. intros i Hi. apply (rdbs_rg_range _ _ _ _ _ _ Hr1 Hnth). rewrite Z2Nat.id by lia. exact Hi.
  - exact D1.
  - exact D2.
Qed.

Lemma resume_memcmp : forall M0 s R M rv poff q n zs1 zs2 spoff ret tp s2 (R' : bvmap 5 word) (M' : word -> option byte),
  sim segs C E M0 s R M rv -> sum_memcmp segs C s = Some (EvMemcmp poff q n zs1 zs2 spoff ret tp, s2) ->
  (forall r : reg, In (bv_unsigned r) CSAVEDZ -> getr R' r = getr R r) ->
  getr R' (Z_to_bv 5 10) = Z_to_bv 64 (zmemcmp (zbytes zs1) (zbytes zs2)) ->
  (forall a, 0 < a < c_abs_hi C -> (in_ivs (c_wabs C) a = true \/ rdb0 segs C a <> None) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall j rg off, nth_error (c_rgs C) j = Some rg -> rg_lo rg <= off < rg_hi rg -> (rg_k rg = c_spk C -> spoff <= off) ->
      M' (Z_to_bv 64 (rbase E rg + off)) = M (Z_to_bv 64 (rbase E rg + off))) ->
  (forall j rg off, nth_error (c_rgs C) j = Some rg -> rg_lo rg <= off < rg_hi rg -> M' (Z_to_bv 64 (rbase E rg + off)) <> None) ->
  sim segs C E M' s2 R' M' None.
Proof.
  intros M0 s R M rv poff q n zs1 zs2 spoff ret tp s2 R' M' Hsim H CS A0 KA KR DR.
  destruct (sum_memcmp_facts M0 s R M rv poff q n zs1 zs2 spoff ret tp s2 Hsim H) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs2). subst s2.
  destruct Hsim as [Hr Hl Hz Hm Hv]. pose proof (io_hi C E IO) as Hhi.
  constructor.
  - intros r Hau. rewrite getreg_after_call in Hau |- * by exact Hl.
    destruct (Nat.eqb_spec (rnat r) 10) as [H10|H10].
    + assert (r = Z_to_bv 5 10) as -> by (apply rnat_inj; rewrite H10; reflexivity). rewrite A0. reflexivity.
    + destruct (Nat.eqb (rnat r) 0 || existsb (Nat.eqb (rnat r)) CSAVEDN)%bool eqn:Hcs; [|exfalso; exact (Hau eq_refl)].
      apply orb_true_iff in Hcs. destruct Hcs as [Hcs|Hcs].
      * apply Nat.eqb_eq in Hcs. assert (r = Z_to_bv 5 0) as -> by (apply rnat_inj; rewrite Hcs; reflexivity).
        unfold getreg. change (rnat (Z_to_bv 5 0)) with 0%nat. rewrite Hz. reflexivity.
      * rewrite (CS r (csavedn_z r Hcs)). exact (Hr r Hau).
  - unfold after_call. cbn [s_regs]. rewrite upd_length, clobber_length. exact Hl.
  - unfold after_call. cbn [s_regs]. rewrite nth_upd_other by lia. rewrite nth_clobber by (rewrite Hl; lia). cbn. exact Hz.
  - destruct Hm as [MA MR MT MX MD]. unfold after_call. constructor; cbn [s_abs s_rgs].
    + intros a ab Hf. destruct (MA a ab Hf) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. rewrite (KA a X1); [exact X3 | left; exact X2].
    + intros j rg t' off ab Hj Ht' Hf'. destruct (prune_rgs_nth _ _ _ _ _ Ht') as (t & Ht & PR). destruct (PR off ab Hf') as [Hf Hlo].
      destruct (MR j rg t off ab Hj Ht Hf) as [X1 X2]. split; [exact X1|]. rewrite (KR j rg off Hj X1 (Hlo rg Hj)). exact X2.
    + intros a Ha Hf ab Hab. unfold rt_at, rb in MT |- *. rewrite (KA a Ha); [exact (MT a Ha Hf ab Hab) | right; rewrite Hab; discriminate].
    + intros x. left. reflexivity.
    + exact DR.
  - reflexivity.
Qed.
End Resume.
End ISLRA.

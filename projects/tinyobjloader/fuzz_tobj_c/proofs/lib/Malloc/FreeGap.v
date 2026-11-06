(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "modulo"; "sub"; "of_nat"; "leb"; "div"; "eqb"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "iff"; "not"; "@Corelib.Init.Datatypes"; "snd"; "prod"; "fst"; "list"; "pair"; "bool"; "length"; "true"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap"; "S"; "F"; "class_of"; "total"; "PG"; "ARENA"; "slot"; "disjoint"; "page_len"; "zpair"; "nslots"; "well_placed"; "CEIL"; "BUDGET"; "below_F"; "pairwise"; "zrange"; "NCLASS"; "entry_ok"; "ledger_budget_ok"; "ledger_disciplined"; "slot_idx"; "@Stdlib.Lists.List"; "In"; "filter"; "fold_right"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_round_up_Z"; "region_free"; "page_size"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition PG : Z := 4096.
Definition F : Z := 0x2aaaaaaab000.
Definition CEIL : Z := 0x7fff7f800000.
Definition ARENA : Z := 2 ^ 42.
Definition NCLASS : Z := 21.
Definition BUDGET : Z := 2 ^ 41.

Definition S (j : Z) : Z := 2 ^ (j + 12).
Definition nslots (j : Z) : Z := 2 ^ (30 - j).

Definition class_of (len : Z) : Z := Z.max 0 (Z.log2_up len - 12).

Definition slot (j i : Z) : Z := ltac2:(tb__ "0|0|
S2S2S1cS4Vj;S20A2A2S4Vi;S1bVj;A1A2A2").

Definition well_placed (e : Z * Z) : Prop := ltac2:(tb__ "0|0|
S1dS12S0S0Ve;A3A1S0SeS0S0ScScS1Z0R1A2S3R1S25R2A1A2A2SdS0S14S0S0Ve;A3S21R2R1A2A3A2Li;A2Tj;").

Definition below_F (e : Z * Z) : Prop := ltac2:(tb__ "0|1|
ScS1Z0S14S0S0Ve;A3M0A2S1S2G0S12S0S0Ve;A3A2S1cA2A2").

Definition page_len (len : Z) : Prop := ltac2:(tb__ "0|1|
ScS3Z0M0Vlen;A2SdS0S6Vlen;S1fA2G0A3A2").

Definition disjoint (a b : Z * Z) : Prop := ltac2:(tb__ "0|2|
SfS1S2S14S0S0Va;A3M0S12S0S0Va;A3A2S14S0S0Vb;A3M1A2S1S2G1S12S0S0Vb;A3A2G0A2A2").

Fixpoint pairwise {A} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with [] => True | x :: t => (forall y, In y t -> R x y) /\ pairwise R t end.

Definition total (l : list (Z * Z)) : Z := ltac2:(tb__ "0|1|
S33S0S13S0S0A2M0G0S0S2S12S0S0R2A3R1A2Lacc;Le;Z0Vl;A5").

Lemma S_pos : ltac2:(tb__ "0|1|
S0S1Z0M0R1A2S3G0S1bR2A1A2F_;Fj;").
Proof. intros. unfold S. apply Z.pow_pos_nonneg; lia. Qed.

Lemma class_of_range : ltac2:(tb__ "0|2|
S0ScS3Z0M0R1A2S1R1S5Z2Z20A2A2A2ScS1G0S1dR2A1M1A2S1G1Z14A2A2F_;Flen;").
Proof.
  intros len H. unfold class_of.
  pose proof (Z.log2_up_le_mono len (2 ^ 32) ltac:(lia)) as M.
  rewrite Z.log2_up_pow2 in M by lia. lia.
Qed.

Lemma class_of_fits : ltac2:(tb__ "0|0|
S0ScS3Z0R1A2S1R1S5Z2Z20A2A2A2S1R2S1bS1dR2A1A1A2F_;Flen;").
Proof.
  intros len H. unfold class_of, S.
  destruct (Z.eq_dec len 1) as [->|Hne].
  - apply Z.le_trans with (2 ^ 12); [lia|]. apply Z.pow_le_mono_r; lia.
  - pose proof (Z.log2_up_spec len ltac:(lia)) as [_ U].
    apply Z.le_trans with (2 ^ Z.log2_up len); [exact U|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma class_of_big : ltac2:(tb__ "0|1|
S0S3Z0R1A2S1Z1M0S1dR2A1A2S3S1bS7S1dR3A1G0A2A1R3A2F_;F_;Flen;").
Proof.
  intros len Hl Hj. unfold class_of, S in *.
  assert (Hlt : 1 < len).
  { destruct (Z.eq_dec len 1) as [->|]; [|lia]. exfalso. rewrite (Z.log2_up_1) in Hj. lia. }
  pose proof (Z.log2_up_spec len Hlt) as [L _].
  replace (Z.max 0 (Z.log2_up len - 12) - 1 + 12) with (Z.pred (Z.log2_up len)) by lia. exact L.
Qed.

Lemma S_succ : ltac2:(tb__ "0|0|
S0S1Z0R1A2SdS0S1bS2R2Z1A2A1S4Z2S1bR2A1A2A3F_;Fj;").
Proof. intros. unfold S. replace (j + 1 + 12) with (Z.succ (j + 12)) by lia. rewrite Z.pow_succ_r; lia. Qed.

Lemma S_nslots : ltac2:(tb__ "0|0|
S0ScS1Z0R1A2S1R1Z14A2A2SdS0S4S1bR2A1S25R2A1A2S20A3F_;Fj;").
Proof.
  intros. unfold S, nslots, ARENA. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma nslots_pos : ltac2:(tb__ "0|1|
S0ScS1Z0M0R1A2S1R1Z14A2A2S3G0S25R2A1A2F_;Fj;").
Proof. intros. unfold nslots. apply Z.pow_pos_nonneg; lia. Qed.

Lemma S0 : S 0 = PG. Proof. reflexivity. Qed.

Lemma slot_bounds : ltac2:(tb__ "0|2|
S0S0ScS1Z0R2A2M0S1R2Z14A2A2ScG0S3R2S25R3A1A2A2ScS1S2S1cS4R4S20A2A2S21R4R3A2M1A2S1S2G1S1bR4A1A2S2S1cS4S2R4Z1A2S20A2A2A2A2F_;F_;Fi;Fj;").
Proof.
  intros j i Hj Hi. unfold slot. pose proof (S_nslots j Hj). pose proof (S_pos j ltac:(lia)).
  split; [nia|]. assert (i * S j + S j <= nslots j * S j) by nia. nia.
Qed.

Lemma arenas_below_ceiling : ltac2:(tb__ "0|0|
S1S2S1cS4S2cS20A2A2S27A2").
Proof. vm_compute. discriminate. Qed.

Lemma F_page : F mod PG = 0. Proof. reflexivity. Qed.
Lemma ARENA_page : ARENA mod PG = 0. Proof. reflexivity. Qed.
Lemma S_page : ltac2:(tb__ "0|1|
S0S1Z0M0R1A2SdS0S6S1bR2A1S1fA2G0A3F_;Fj;").
Proof.
  intros. unfold S, PG. replace (j + 12) with (j + 12 - 12 + 12) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. apply Z_mod_mult.
Qed.

Lemma slot_page : ltac2:(tb__ "0|2|
S0S0S1Z0M0R2A2M1G1SdS0S6S21R4R3A2S1fA2G0A3F_;F_;Fi;Fj;").
Proof.
  intros. unfold slot.
  rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, S_page by lia. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, ARENA_page. rewrite Z.mul_0_r, Z.add_0_r. apply F_page.
Qed.

Lemma slot_inj : ltac2:(tb__ "0|0|
S0S0S0S1Z0R3A2SdS0S21R4R3A2S21R4R2A2A3SdS0R4R3A3F_;F_;Fi';Fi;Fj;").
Proof. intros j i i' Hj E. unfold slot in E. pose proof (S_pos j Hj). nia. Qed.

Definition slot_idx (e : Z * Z) : Z := ltac2:(tb__ "0|1|
SaS7S7S14S0S0Ve;A3S1cA2S4S1dS12S0S0Ve;A3A1M0S20A2A2S1bG0A1A2").

Lemma slot_idx_of : ltac2:(tb__ "0|1|
S13S0S0A2S0S1dS12S0S0R2A3A1S0S1Z0M0R1A2SdS0S14S0S0R4A3S21R2R3A2A3S1G0R4A2SdS0S30R6A1R5A3F_;F_;F_;Tj;Fi;Fe;").
Proof.
  intros e i j Hj E Hi. unfold slot_idx. fold j. rewrite E. unfold slot.
  replace (F + j * ARENA + i * S j - F - j * ARENA) with (i * S j) by lia.
  apply Z.div_mul. pose proof (S_pos j Hj). lia.
Qed.

Definition zrange (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

Lemma In_zrange : ltac2:(tb__ "0|0|
S0S0S10S31S0R1S2bR2A1A3ScS1Z0R1A2S3R1R2A2A2A2Fi;Fn;").
Proof.
  intros n i. unfold zrange. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros H. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.

Lemma NoDup_zrange : forall n, NoDup (zrange n).
Proof.
  intros n. unfold zrange. apply NoDup_map_inv with (f := Z.to_nat).
  rewrite map_map. erewrite map_ext by (intros; apply Nat2Z.id). rewrite map_id. apply seq_NoDup.
Qed.

Lemma length_zrange : ltac2:(tb__ "0|0|
S0S1Z0R1A2SdS0S8S18S0S2bR2A1A2A1R2A3F_;Fn;").
Proof. intros. unfold zrange. rewrite length_map, length_seq. lia. Qed.

Lemma exists_free_index : ltac2:(tb__ "0|1|
S15S0A1S0S1Z0R1A2M0S3S8S18S0R3A2A1R2A2SeS0S0ScScG0S3R1R4A2A2S11S31S0R1R5A3A1A2Li;A2F_;F_;Fn;FL;").
Proof.
  intros L n Hn Hlen.
  destruct (Exists_dec (fun i => ~ In i L) (zrange n)) as [E|NE].
  - intros i. destruct (in_dec Z.eq_dec i L); [right | left]; tauto.
  - apply Exists_exists in E as (i & Hi & Hni). apply In_zrange in Hi. exists i. auto.
  - exfalso. assert (Hincl : incl (zrange n) L).
    { intros i Hi. destruct (in_dec Z.eq_dec i L) as [|Hn']; [assumption|].
      exfalso. apply NE. apply Exists_exists. exists i. auto. }
    pose proof (NoDup_incl_length (NoDup_zrange n) Hincl) as Hle.
    rewrite <- (length_zrange n Hn) in Hlen. lia.
Qed.

Lemma total_app : ltac2:(tb__ "0|2|
S15S13S0S0A2M0A1M1G1SdS0S1eS1aG0R2R1A3A1S2S1eR2A1S1eR1A1A2A3Fl2;Fl1;").
Proof. induction l1 as [|x t IH]; intros; [reflexivity|]. cbn [total fold_right app]. fold (total (t ++ l2)). fold (total t). rewrite IH. lia. Qed.

Lemma total_nonneg : ltac2:(tb__ "0|2|
S15S13S0S0A2M0A1G0S31G0R1R2A3S3Z0M1S12S0S0R2A3A2F_;Fe;S1G1S1eR2A1A2F_;Fl;").
Proof.
  induction l as [|x t IH]; intros H; [cbn; lia|].
  cbn [total fold_right]. fold (total t).
  pose proof (H x ltac:(left; reflexivity)). pose proof (IH ltac:(intros e He; apply H; right; exact He)). lia.
Qed.

Lemma total_filter_le : ltac2:(tb__ "0|1|
S13S0S0A2M0S17F_;S15G0A1G0S31G0R1R2A3S3Z0S12S0S0R2A3A2F_;Fe;S1S1eS32G0R3R2A3A1S1eR2A1A2F_;Fl;Ff;").
Proof.
  induction l as [|x t IH]; intros H; [cbn; lia|].
  pose proof (H x ltac:(left; reflexivity)).
  pose proof (IH ltac:(intros e He; apply H; right; exact He)).
  cbn [filter]. destruct (f x); cbn [total fold_right]; fold (total t); fold (total (filter f t)); lia.
Qed.

Lemma total_lower : ltac2:(tb__ "0|1|
S15S13S0S0A2M0A1S0G0S31G0R1R3A3S1R3S12S0S0R2A3A2F_;Fe;S1S4S8S18G0R3A2A1R2A2S1eR3A1A2F_;Flo;Fl;").
Proof.
  induction l as [|x t IH]; intros lo H; [cbn; lia|].
  pose proof (H x ltac:(left; reflexivity)).
  pose proof (IH lo ltac:(intros e He; apply H; right; exact He)).
  cbn [length total fold_right]. fold (total t). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma class_min_len : ltac2:(tb__ "0|1|
S0S23R1A1S1R2S5Z2Z20A2A2S1dR3A1S0ScSdS0R1Z0A3S1S1fR5A2F_;S1Z1M0R1A2S1S2S1bS7R2G0A2A1S1fA2R5A2F_;A2Tj;F_;F_;Flen;").
Proof.
  intros len [Hpos Hpg] Hmax j. split.
  - intros _. unfold PG in *.
    destruct (Z_lt_le_dec len 4096) as [Hlt|Hge]; [|exact Hge].
    exfalso. rewrite Z.mod_small in Hpg by lia. lia.
  - intros Hj. pose proof (class_of_big len Hpos Hj) as B. fold j in B.

    assert (Hs : S (j - 1) mod PG = 0) by (apply S_page; lia).
    unfold PG in *.
    pose proof (Z.div_mod len 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (S (j - 1)) 4096 ltac:(lia)) as D2.
    rewrite Hpg in D1. rewrite Hs in D2.
    assert (S (j - 1) / 4096 < len / 4096) by nia. nia.
Qed.

Definition classb (j : Z) (e : Z * Z) : bool := ltac2:(tb__ "0|0|
SbS1dS12S0S0Ve;A3A1Vj;A2").

Theorem free_gap_exists : ltac2:(tb__ "0|3|
S15S13S0S0A2M0A1S0G0S31G0R1R3A3ScSfS26R2A1S29R2A1A2ScS23S12S0S0R2A3M1A1S1G1S5Z2Z20A2M2A2A2A2F_;Fe;S2aG0S22R3A3S1S1eS32G0G0S9S1cS14S0S0R1A3A2Le;R4A3A1S28A2S23R4A1S1R5G2A2SeS0S0ScS26S16S0S0R1R7A4A1ScSdS0S6R1S1fA2Z0A3ScS1S1cR1A2ScS1S2R1R7A2S27A2G0S31G0R1R9A3S22S16S0S0R3R9A4R2A2F_;Fe;A2A2A2A2La;A2F_;F_;F_;F_;F_;Fn;Fmaps;").
Proof.
  intros maps n Hall Hpw Hbud Hn Hnmax.
  set (j := class_of n).
  pose proof (class_of_range n ltac:(destruct Hn; lia)) as Hj. fold j in Hj.

  set (Cj := filter (fun e => (F <=? fst e) && classb j e) maps).
  set (L := map slot_idx Cj).
  assert (HCj : forall e, In e Cj -> In e maps /\ well_placed e /\ class_of (snd e) = j /\ page_len (snd e) /\ snd e <= 2 ^ 32).
  { intros e He. subst Cj. apply filter_In in He as [Hin Hb]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.leb_le in Hb1. unfold classb in Hb2. apply Z.eqb_eq in Hb2.
    destruct (Hall e Hin) as ([W | [B1 B2]] & P & M); [auto 6|].
    exfalso. destruct P. lia. }

  assert (Hcount : Z.of_nat (length L) < nslots j).
  { subst L. rewrite length_map.
    assert (Htot : total Cj <= BUDGET).
    { apply Z.le_trans with (total (filter (fun e => F <=? fst e) maps)); [|exact Hbud].
      subst Cj. clear -Hall.
      induction maps as [|x t IH]; [cbn; lia|].
      assert (Hx : 0 < snd x) by (destruct (Hall x ltac:(left; reflexivity)) as (_ & [P _] & _); exact P).
      specialize (IH ltac:(intros e He; apply Hall; right; exact He)).
      cbn [filter andb]. destruct (F <=? fst x); [|exact IH].
      destruct (classb j x); cbn [andb total fold_right];
        fold (total (filter (fun e : Z * Z => (F <=? fst e) && classb j e) t));
        fold (total (filter (fun e : Z * Z => F <=? fst e) t)); lia. }
    destruct (Z.eq_dec j 0) as [Hj0 | Hjpos].
    - assert (Hlo : Z.of_nat (length Cj) * PG <= total Cj).
      { apply total_lower. intros e He. destruct (HCj e He) as (_ & _ & C & P & M).
        destruct (class_min_len (snd e) P M) as [A _]. apply A. lia. }
      unfold BUDGET, nslots, PG in *. rewrite Hj0. change (2 ^ (30 - 0)) with (2 ^ 30).
      assert (Z.of_nat (length Cj) <= 2 ^ 41 / 4096) by (apply Z.div_le_lower_bound; lia).
      change (2 ^ 41 / 4096) with (2 ^ 29) in H.
      assert (2 ^ 29 < 2 ^ 30) by (apply Z.pow_lt_mono_r; lia). lia.
    - assert (Hlo : Z.of_nat (length Cj) * (S (j - 1) + PG) <= total Cj).
      { apply total_lower. intros e He. destruct (HCj e He) as (_ & _ & C & P & M).
        destruct (class_min_len (snd e) P M) as [_ B]. rewrite C in B. apply B. lia. }

      assert (Hhalf : S (j - 1) * nslots j = BUDGET).
      { unfold S, nslots, BUDGET. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      pose proof (nslots_pos j Hj). pose proof (S_pos (j - 1) ltac:(lia)). unfold PG in *. nia. }

  destruct (exists_free_index L (nslots j) ltac:(pose proof (nslots_pos j Hj); lia) Hcount) as (i & Hi & Hni).
  exists (slot j i).
  pose proof (slot_bounds j i Hj Hi) as [SB1 SB2].
  pose proof (class_of_fits n ltac:(destruct Hn; lia)) as Hfit. fold j in Hfit.
  assert (Harena : F + (j + 1) * ARENA <= CEIL).
  { pose proof arenas_below_ceiling. unfold NCLASS in *. assert ((j + 1) * ARENA <= 21 * ARENA) by (unfold ARENA; nia). lia. }
  split; [exists i; split; [exact Hi | reflexivity]|].
  split; [apply slot_page; lia|].
  split; [unfold ARENA in *; nia|].
  split; [lia|].
  intros e He. destruct (Hall e He) as ([W | B] & P & M).
  -
    destruct W as (i' & Hi' & Eb).
    set (j' := class_of (snd e)) in *.
    pose proof (class_of_range (snd e) ltac:(destruct P; lia)) as Hj'.
    pose proof (slot_bounds j' i' Hj' Hi') as [SB1' SB2'].
    pose proof (class_of_fits (snd e) ltac:(destruct P; lia)) as Hfit'. fold j' in Hfit'.
    destruct (Z.eq_dec j' j) as [Ejj | Nj].
    +
      assert (Hne : i' <> i).
      { intros ->. apply Hni. subst L. apply in_map_iff. exists e. split.
        - apply (slot_idx_of e i); [lia | exact Eb | lia].
        - subst Cj. apply filter_In. split; [exact He|]. apply andb_true_intro. split.
          + apply Z.leb_le. rewrite Eb. unfold ARENA in SB1'. nia.
          + unfold classb. apply Z.eqb_eq. exact Ejj. }
      unfold disjoint. cbn [fst snd]. rewrite Eb.
      assert (ES : S j' = S j) by (rewrite Ejj; reflexivity).
      unfold slot. rewrite ES, Ejj. pose proof (S_pos j ltac:(lia)).
      rewrite Ejj in Hfit'.
      destruct (Z_lt_le_dec i' i); [right | left]; nia.
    +
      unfold disjoint. cbn [fst snd]. rewrite Eb.
      destruct (Z_lt_le_dec j' j); [right | left].
      * assert ((j' + 1) * ARENA <= j * ARENA) by (unfold ARENA; nia). lia.
      * assert ((j + 1) * ARENA <= j' * ARENA) by (unfold ARENA; nia). lia.
  -
    unfold disjoint, below_F in *. cbn [fst snd]. right. unfold ARENA in *. nia.
Qed.

Example free_gap_constants :
  F = 46912496119808 /\ CEIL = 140735332483072 /\ F + NCLASS * ARENA = 139271472852992.
Proof. repeat split; vm_compute; reflexivity. Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Close Scope bv_scope.

Definition zpair (e : word * word) : Z * Z := ltac2:(tb__ "0|2|
S16S0S0S36Q40M0S14S34G0A1M1G1Ve;A3A2S36G0S12G1G1Ve;A3A2A4").

Definition entry_ok (e : Z * Z) : Prop := ltac2:(tb__ "0|1|
ScSfS26Ve;A1S29Ve;A1A2ScS23S12S0S0Ve;A3M0A1S1G0S5Z2Z20A2A2A2A2").

Definition ledger_disciplined (maps : list (word * word)) : Prop := ltac2:(tb__ "0|3|
ScS13S34Q40A1M0G0A2M1S31G1R1Vmaps;A3S2dS24R2A1A1F_;Fe;S2aS13S0S0A2M2S22S37G1G2S24Vmaps;A4A3A2").

Definition ledger_budget_ok (maps : list (word * word)) : Prop := ltac2:(tb__ "0|2|
S1S1eS32S13S0S0A2M0G0S9S1cS14S0S0R1A3A2Le;S37S13S34Q40A1M1G1A2G0S24Vmaps;A4A3A1S28A2").

Lemma region_free_of_disjoint : ltac2:(tb__ "0|4|
S15S13S34Q40M0A1M1G1A2M2A1S0S0S1Z0M3R2A2S3G3R2A2S3S2R4R3A2S5Z2Z40A2A2G2S31G2R1R7A3S22S16S0S0R7R6A4S24R2A1A2F_;Fe;SdS17S39R7S35G0R6A2S35G0R5A2A3S19A3F_;F_;F_;F_;Fn;Fa;Fmaps;").
Proof.
  intros maps a n Ha Hn Han H. induction maps as [|[b l] t IH]; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros e He; apply H; right; exact He).
  rewrite Bool.andb_true_r. unfold iv_overlap.
  assert (two64 : bv_modulus 64 = 2 ^ 64) by reflexivity.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (rewrite two64; lia).
  specialize (H (b, l) ltac:(left; reflexivity)). unfold FreeGap.disjoint, zpair in H. cbn [fst snd] in H.
  apply Bool.negb_true_iff. apply Bool.andb_false_iff.
  destruct H as [H|H]; [right | left]; apply Z.ltb_ge; lia.
Qed.

Theorem free_gap_exists_ledger : ltac2:(tb__ "0|4|
S15S13S34Q40M0A1M1G1A2M2A1S0S2fR2A1S2eR3A1S23R3A1S1R4S5Z2Z20A2A2SeS0S0ScS26S16S0S0R1R6A4A1ScSdS0S6R1S1fA2Z0M3A3ScS1S1cR1A2ScS1S2R1R6A2S27A2ScS3G3R1A2ScSdS17S39R7S35G0R1A2S35G0R6A2A3S19A3G2S31G2R1R8A3S22S16S0S0R3R8A4S24R2A1A2F_;Fe;A2A2A2A2A2A2La;A2F_;F_;F_;F_;Fn;Fmaps;").
Proof.
  intros maps n [Hent Hpw] Hbud Hn Hnmax.
  destruct (free_gap_exists (map zpair maps) n) as (a & W & P & HF & HC & D).
  - intros e He. apply in_map_iff in He as (e' & <- & He'). exact (Hent e' He').
  - exact Hpw.
  - exact Hbud.
  - exact Hn.
  - exact Hnmax.
  - exists a. assert (Hd : forall e, In e maps -> FreeGap.disjoint (a, n) (zpair e)).
    { intros e He. apply D. apply in_map_iff. exists e. auto. }
    repeat split; auto.
    + unfold F in HF. lia.
    + apply region_free_of_disjoint; auto.
      * unfold F in HF; lia.
      * destruct Hn; lia.
      * unfold CEIL in HC. lia.
Qed.

Lemma page_round_up_Z_ge : ltac2:(tb__ "0|0|
S0S1R1S38R1A1A2Fz;").
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

Lemma page_round_up_Z_aligned : ltac2:(tb__ "0|0|
S0SdS0S6S38R1A1S3aA2Z0A3Fz;").
Proof. intros z. unfold page_round_up_Z, page_size. apply Z_mod_mult. Qed.

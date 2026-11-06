(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCLemmas1 BzR3aFs BzR1a.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rl_bytes (r : rlst) : list Z := block_of (rl_block r) (rl_nblock r).
Definition rl_pend (r : rlst) : list Z :=
  if (rl_ch r <? 256) && (0 <? rl_len r) then repeat (rl_ch r) (Z.to_nat (rl_len r)) else [].
Definition rl_data (r : rlst) : list Z := unrle1 (rl_bytes r).

Definition IU01 (inUse : zarr) : Prop := forall i, 0 <= i < 256 -> zget inUse i = 0 \/ zget inUse i = 1.
(* [comment removed for export] *)
Definition PEND (runs : list (Z * Z)) (ch len : Z) : Prop :=
  (ch = 256 /\ len = 0) \/
  (0 <= ch < 256 /\ 1 <= len <= 255 /\ match last runs (256, 255) with (c, L) => ADJ c L ch end).

Definition RLI (r : rlst) : Prop :=
  rl_inv r /\ zbok (rl_block r) /\ IU01 (rl_inUse r) /\
  exists runs, RWF runs /\ rl_bytes r = rl_enc runs /\ rl_crc r = crc_list crc_init (rl_dec runs) /\
    PEND runs (rl_ch r) (rl_len r) /\ (forall b, In b (rl_enc runs) -> zget (rl_inUse r) b = 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma block_of_snoc : forall a n v, 0 <= n -> block_of (zset a n v) (n + 1) = block_of a n ++ [v].
Proof.
  intros a n v Hn. unfold block_of. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite seq_S, map_app. cbn [map Nat.add]. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. unfold rd8. apply zget_zset_other. lia.
  - unfold rd8. rewrite ?Nat.add_0_l, Z2Nat.id by lia. rewrite zget_zset_same. reflexivity.
Qed.
(* [comment removed for export] *)

Lemma land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma rl_put_view : forall r b, 0 <= rl_nblock r -> 0 <= b < 256 ->
  rl_bytes (rl_put r b) = rl_bytes r ++ [b] /\ rl_nblock (rl_put r b) = rl_nblock r + 1 /\
  rl_inUse (rl_put r b) = rl_inUse r /\ rl_crc (rl_put r b) = rl_crc r /\ rl_ch (rl_put r b) = rl_ch r /\ rl_len (rl_put r b) = rl_len r /\
  (zbok (rl_block r) -> zbok (rl_block (rl_put r b))).
Proof.
  intros r b Hn Hb. unfold rl_put, rl_bytes. cbn [rl_block rl_nblock rl_inUse rl_crc rl_ch rl_len].
  rewrite land255 by exact Hb. split; [apply block_of_snoc; exact Hn|]. repeat (split; [reflexivity|]).
  intros Z0 i. rewrite zget_zset. destruct (i =? rl_nblock r); [lia| apply Z0].
Qed.

(* [comment removed for export] *)
Fixpoint rl_putn (k : nat) (r : rlst) (b : Z) : rlst := match k with O => r | S k' => rl_put (rl_putn k' r b) b end.
Lemma rl_putn_view : forall k r b, 0 <= rl_nblock r -> 0 <= b < 256 ->
  rl_bytes (rl_putn k r b) = rl_bytes r ++ repeat b k /\ rl_nblock (rl_putn k r b) = rl_nblock r + Z.of_nat k /\
  rl_inUse (rl_putn k r b) = rl_inUse r /\ rl_crc (rl_putn k r b) = rl_crc r /\ rl_ch (rl_putn k r b) = rl_ch r /\ rl_len (rl_putn k r b) = rl_len r /\
  (zbok (rl_block r) -> zbok (rl_block (rl_putn k r b))).
Proof.
  induction k as [|k IH]; intros r b Hn Hb; cbn [rl_putn].
  - rewrite app_nil_r, Z.add_0_r. repeat (split; [reflexivity|]). auto.
  - cps_destruct (IH r b Hn Hb) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    cps_destruct (rl_put_view (rl_putn k r b) b ltac:(lia) Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    rewrite B1, A1, B2, A2, B3, A3, B4, A4, B5, A5, B6, A6. rewrite <- app_assoc. replace (repeat b k ++ [b]) with (repeat b (S k)) by (apply repeat_cons).
    repeat (split; [first [reflexivity | lia] |]). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma add_pair_view : forall r, rl_inv r -> 0 <= rl_ch r < 256 -> 1 <= rl_len r ->
  let r' := add_pair_to_block r in
  rl_bytes r' = rl_bytes r ++ rcode (rl_ch r) (rl_len r) /\
  rl_nblock r' = rl_nblock r + Z.of_nat (length (rcode (rl_ch r) (rl_len r))) /\
  rl_crc r' = crc_list (rl_crc r) (repeat (rl_ch r) (Z.to_nat (rl_len r))) /\
  rl_ch r' = rl_ch r /\ rl_len r' = rl_len r /\
  (forall i, zget (rl_inUse r') i = (if (i =? rl_ch r) || ((4 <=? rl_len r) && (i =? rl_len r - 4)) then 1 else zget (rl_inUse r) i)%bool) /\
  (zbok (rl_block r) -> zbok (rl_block r')).
Proof.
  intros r RI Hc Hl. cbv zeta. destruct RI as [(A & B & C & D & E) P].
  unfold add_pair_to_block. rewrite land255 by exact Hc. rewrite <- crc_list_repeat.
  set (r1 := RL (rl_nblock r) (rl_block r) (zset (rl_inUse r) (rl_ch r) 1) (crc_list (rl_crc r) (repeat (rl_ch r) (Z.to_nat (rl_len r)))) (rl_ch r) (rl_len r)).
  assert (V1 : rl_bytes r1 = rl_bytes r /\ rl_nblock r1 = rl_nblock r /\ rl_block r1 = rl_block r) by (repeat split; reflexivity).
  cps_destruct V1 as (V1 & V2 & V3).
  unfold rcode.
  destruct (Z.eqb_spec (rl_len r) 1) as [E1|N1].
  { change (rl_put r1 (rl_ch r)) with (rl_putn 1 r1 (rl_ch r)).
    cps_destruct (rl_putn_view 1 r1 (rl_ch r) ltac:(subst r1; cbn; lia) Hc) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    rewrite B1, B2, B3, B4, B5, B6, V1, V2. subst r1. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len] in *. rewrite E1.
    change (1 <? 4) with true. cbv iota. change (Z.to_nat 1) with 1%nat.
    repeat (split; [reflexivity|]). split; [| exact B7].
    intros i. rewrite zget_zset. change (4 <=? 1) with false. rewrite Bool.andb_false_l, Bool.orb_false_r. reflexivity. }
  destruct (Z.eqb_spec (rl_len r) 2) as [E2|N2].
  { change (rl_put (rl_put r1 (rl_ch r)) (rl_ch r)) with (rl_putn 2 r1 (rl_ch r)).
    cps_destruct (rl_putn_view 2 r1 (rl_ch r) ltac:(subst r1; cbn; lia) Hc) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    rewrite B1, B2, B3, B4, B5, B6, V1, V2. subst r1. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len] in *. rewrite E2.
    change (2 <? 4) with true. cbv iota. change (Z.to_nat 2) with 2%nat.
    repeat (split; [reflexivity|]). split; [| exact B7].
    intros i. rewrite zget_zset. change (4 <=? 2) with false. rewrite Bool.andb_false_l, Bool.orb_false_r. reflexivity. }
  destruct (Z.eqb_spec (rl_len r) 3) as [E3|N3].
  { change (rl_put (rl_put (rl_put r1 (rl_ch r)) (rl_ch r)) (rl_ch r)) with (rl_putn 3 r1 (rl_ch r)).
    cps_destruct (rl_putn_view 3 r1 (rl_ch r) ltac:(subst r1; cbn; lia) Hc) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    rewrite B1, B2, B3, B4, B5, B6, V1, V2. subst r1. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len] in *. rewrite E3.
    change (3 <? 4) with true. cbv iota. change (Z.to_nat 3) with 3%nat.
    repeat (split; [reflexivity|]). split; [| exact B7].
    intros i. rewrite zget_zset. change (4 <=? 3) with false. rewrite Bool.andb_false_l, Bool.orb_false_r. reflexivity. }
  (* [comment removed for export] *)
  subst r1. clear V1 V2 V3. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
  set (r2 := RL (rl_nblock r) (rl_block r) (zset (zset (rl_inUse r) (rl_ch r) 1) (rl_len r - 4) 1) (crc_list (rl_crc r) (repeat (rl_ch r) (Z.to_nat (rl_len r)))) (rl_ch r) (rl_len r)).
  change (rl_put (rl_put (rl_put (rl_put r2 (rl_ch r)) (rl_ch r)) (rl_ch r)) (rl_ch r)) with (rl_putn 4 r2 (rl_ch r)).
  cps_destruct (rl_putn_view 4 r2 (rl_ch r) ltac:(subst r2; cbn; lia) Hc) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  cps_destruct (rl_put_view (rl_putn 4 r2 (rl_ch r)) (rl_len r - 4) ltac:(rewrite B2; subst r2; cbn; lia) ltac:(lia)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  rewrite C1, B1, C2, B2, C3, B3, C4, B4, C5, B5, C6, B6. subst r2. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len]. unfold rl_bytes. cbn [rl_block rl_nblock].
  replace (rl_len r <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite <- app_assoc, length_app, repeat_length. cbn [length Z.of_nat Nat.add].
  split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros i. rewrite !zget_zset. replace (4 <=? rl_len r) with true by (symmetry; apply Z.leb_le; lia). rewrite Bool.andb_true_l.
    destruct (Z.eqb_spec i (rl_len r - 4)), (Z.eqb_spec i (rl_ch r)); reflexivity.
  - intros Z0. apply C7. apply B7. exact Z0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RLI_facts : forall r, RLI r ->
  rlcodes (rl_bytes r) (rl_data r) /\ rl_crc r = crc_list crc_init (rl_data r) /\
  Forall (fun b => 0 <= b < 256) (rl_bytes r) /\ Forall (fun b => 0 <= b < 256) (rl_data r) /\
  (forall b, In b (rl_bytes r) -> zget (rl_inUse r) b = 1) /\ IU01 (rl_inUse r) /\ zbok (rl_block r) /\ rl_inv r /\
  length (rl_bytes r) = Z.to_nat (rl_nblock r) /\ 0 <= rl_nblock r /\
  Forall (fun b => 0 <= b < 256) (rl_pend r) /\ Z.of_nat (length (rl_pend r)) = (if rl_ch r <? 256 then rl_len r else 0).
Proof.
  (intros r; cps_intros (RI & ZB & IU & runs & W & EB & EC & PD & CV)).
  assert (ED : rl_data r = rl_dec runs) by (unfold rl_data; rewrite EB; apply unrle1_enc; exact W).
  split; [exists runs; auto|]. split; [rewrite ED; exact EC|]. split; [rewrite EB; apply rl_enc_bytes; exact W|].
  split; [rewrite ED; apply rl_dec_bytes; exact W|]. split; [rewrite EB; exact CV|]. split; [exact IU|]. split; [exact ZB|]. split; [exact RI|].
  split; [unfold rl_bytes; apply block_of_length|]. split; [destruct RI as [(A & _) _]; exact A|].
  unfold rl_pend. destruct RI as [(A & B & C & D & E) P]. destruct PD as [[P1 P2]|(P1 & P2 & P3)].
  - rewrite P1, P2. cbn. split; [constructor| reflexivity].
  - replace ((rl_ch r <? 256) && (0 <? rl_len r))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
    replace (rl_ch r <? 256) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|]. rewrite repeat_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rl_enc_nil_inv : forall runs, RWF runs -> rl_enc runs = [] -> runs = [].
Proof.
  intros runs W E. pose proof (rl_enc_length_ge runs W) as L. rewrite E in L. cbn in L. destruct runs; [reflexivity| cbn in L; lia].
Qed.

Lemma add_pair_core : forall r runs,
  rl_inv r -> zbok (rl_block r) -> IU01 (rl_inUse r) -> RWF runs -> rl_bytes r = rl_enc runs ->
  rl_crc r = crc_list crc_init (rl_dec runs) -> (forall b, In b (rl_enc runs) -> zget (rl_inUse r) b = 1) ->
  0 <= rl_ch r < 256 -> 1 <= rl_len r <= 255 -> (match last runs (256, 255) with (c, L) => ADJ c L (rl_ch r) end) ->
  let r' := add_pair_to_block r in
  let runs' := runs ++ [(rl_ch r, rl_len r)] in
  RWF runs' /\ rl_bytes r' = rl_enc runs' /\ rl_crc r' = crc_list crc_init (rl_dec runs') /\
  (forall b, In b (rl_enc runs') -> zget (rl_inUse r') b = 1) /\ zbok (rl_block r') /\ IU01 (rl_inUse r') /\
  rl_ch r' = rl_ch r /\ rl_len r' = rl_len r /\ rl_nblock r + 1 <= rl_nblock r' <= rl_nblock r + 5 /\
  rl_dec runs' = rl_dec runs ++ repeat (rl_ch r) (Z.to_nat (rl_len r)).
Proof.
  intros r runs RI ZB IU W EB EC CV Hc Hl AD. cbv zeta.
  cps_destruct (add_pair_view r RI Hc ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  set (r' := add_pair_to_block r) in *.
  assert (W' : RWF (runs ++ [(rl_ch r, rl_len r)])).
  { apply RWF_snoc. split; [exact W|]. split; [lia|]. split; [lia|]. destruct (last runs (256, 255)) as [c0 L0]. exact AD. }
  split; [exact W'|]. split; [rewrite A1, EB, rl_enc_app; cbn [rl_enc]; rewrite app_nil_r; reflexivity|].
  split; [rewrite A3, EC, rl_dec_app; cbn [rl_dec]; rewrite app_nil_r, crc_list_app; reflexivity|].
  split.
  { intros b Hb. rewrite A6. rewrite rl_enc_app in Hb. apply in_app_iff in Hb as [Hb|Hb].
    - destruct (_ || _)%bool; [reflexivity| apply CV; exact Hb].
    - cbn [rl_enc] in Hb. rewrite app_nil_r in Hb. unfold rcode in Hb. destruct (Z.ltb_spec (rl_len r) 4).
      + apply repeat_spec in Hb. subst b. rewrite Z.eqb_refl. reflexivity.
      + apply in_app_iff in Hb as [Hb|Hb]; [apply repeat_spec in Hb; subst b; rewrite Z.eqb_refl; reflexivity|].
        destruct Hb as [<-|[]]. replace (4 <=? rl_len r) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.eqb_refl, Bool.andb_true_l, Bool.orb_true_r. reflexivity. }
  split; [apply A7; exact ZB|]. split.
  { intros i Hi. rewrite A6. destruct (_ || _)%bool; [right; reflexivity| apply IU; exact Hi]. }
  split; [exact A4|]. split; [exact A5|]. split.
  { rewrite A2. pose proof (rcode_length (rl_ch r) (rl_len r) ltac:(lia)) as RL. destruct (Z.ltb_spec (rl_len r) 4); lia. }
  rewrite rl_dec_app. cbn [rl_dec]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem flush_RL_RLI : forall r, RLI r ->
  RLI (flush_RL r) /\ rl_data (flush_RL r) = rl_data r ++ rl_pend r /\ rl_pend (flush_RL r) = [] /\
  rl_nblock r <= rl_nblock (flush_RL r) <= rl_nblock r + 5 /\ rl_ch (flush_RL r) = 256 /\ rl_len (flush_RL r) = 0.
Proof.
  intros r RL0. cps_pose RL0 as (RI & ZB & IU & runs & W & EB & EC & PD & CV).
  cps_pose (flush_RL_inv r RI) as (RI' & NB & _).
  assert (ED : rl_data r = rl_dec runs) by (unfold rl_data; rewrite EB; apply unrle1_enc; exact W).
  unfold flush_RL in *. destruct PD as [[P1 P2]|(P1 & P2 & P3)].
  - (* [comment removed for export] *)
    replace (rl_ch r <? 256) with false in * by (symmetry; apply Z.ltb_ge; lia).
    unfold init_RL. unfold RLI, rl_pend, rl_data, rl_bytes in *. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len] in *.
    rewrite P1, P2. cbn. rewrite app_nil_r.
    split; [| repeat split; try reflexivity; lia].
    split; [exact RI'|]. split; [exact ZB|]. split; [exact IU|]. exists runs. split; [exact W|]. split; [exact EB|]. split; [exact EC|].
    split; [left; auto| exact CV].
  - replace (rl_ch r <? 256) with true in * by (symmetry; apply Z.ltb_lt; lia).
    cps_destruct (add_pair_core r runs RI ZB IU W EB EC CV ltac:(lia) ltac:(lia) P3) as (W' & EB' & EC' & CV' & ZB' & IU' & CH' & LN' & NB' & DD').
    set (r' := add_pair_to_block r) in *. set (runs' := runs ++ [(rl_ch r, rl_len r)]) in *.
    split; [| split; [| split; [| split; [exact NB| split; reflexivity]]]].
    + split; [exact RI'|]. split; [unfold init_RL; cbn [rl_block]; exact ZB'|]. split; [unfold init_RL; cbn [rl_inUse]; exact IU'|].
      exists runs'. split; [exact W'|]. split; [unfold init_RL, rl_bytes in *; cbn [rl_block rl_nblock]; exact EB'|].
      split; [unfold init_RL; cbn [rl_crc]; exact EC'|]. split; [left; split; reflexivity|]. unfold init_RL; cbn [rl_inUse]. exact CV'.
    + unfold rl_data at 1. unfold init_RL, rl_bytes. cbn [rl_block rl_nblock]. fold (rl_bytes r'). rewrite EB', unrle1_enc, DD', ED by exact W'.
      unfold rl_pend. replace ((rl_ch r <? 256) && (0 <? rl_len r))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia). reflexivity.
    + unfold rl_pend, init_RL. cbn [rl_ch rl_len]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem add_char_RLI : forall r c, RLI r -> 0 <= c < 256 -> (rl_ch r = 256 -> rl_nblock r = 0) ->
  let r' := add_char_to_block r c in
  RLI r' /\ rl_data r' ++ rl_pend r' = rl_data r ++ rl_pend r ++ [c] /\
  rl_nblock r <= rl_nblock r' <= rl_nblock r + 5 /\ rl_ch r' = c /\ 1 <= rl_len r' <= 255.
Proof.
  intros r c RL0 Hc EMP. cbv zeta. cps_pose RL0 as (RI & ZB & IU & runs & W & EB & EC & PD & CV).
  pose proof (add_char_to_block_inv r c RI Hc) as [RI' NB].
  assert (ED : rl_data r = rl_dec runs) by (unfold rl_data; rewrite EB; apply unrle1_enc; exact W).
  pose proof RI as [(A & B & C & D & E) P].
  unfold add_char_to_block in *.
  destruct (negb (c =? rl_ch r) && (rl_len r =? 1))%bool eqn:K1.
  - (* [comment removed for export] *)
    apply andb_prop in K1. destruct K1 as [K1a K1b]. apply Z.eqb_eq in K1b. apply Bool.negb_true_iff in K1a. apply Z.eqb_neq in K1a.
    assert (Hch : 0 <= rl_ch r < 256) by lia.
    destruct PD as [[P1 P2]|(P1 & P2 & P3)]; [lia|].
    rewrite land255 by exact Hch. rewrite land255 in RI' by exact Hch. rewrite land255 in NB by exact Hch.
    assert (W' : RWF (runs ++ [(rl_ch r, 1)])).
    { apply RWF_snoc. split; [exact W|]. split; [lia|]. split; [lia|]. exact P3. }
    assert (EB' : rl_bytes (RL (rl_nblock r + 1) (zset (rl_block r) (rl_nblock r) (rl_ch r)) (zset (rl_inUse r) (rl_ch r) 1) (crc_update (rl_crc r) (rl_ch r)) c (rl_len r))
                  = rl_enc (runs ++ [(rl_ch r, 1)])).
    { unfold rl_bytes. cbn [rl_block rl_nblock]. rewrite block_of_snoc by lia. fold (rl_bytes r). rewrite EB, rl_enc_app. reflexivity. }
    split; [| split; [| cbn [rl_nblock rl_ch rl_len]; lia]].
    + split; [exact RI'|]. split.
      { cbn [rl_block]. intros i. rewrite zget_zset. destruct (i =? rl_nblock r); [lia| apply ZB]. }
      split. { cbn [rl_inUse]. intros i Hi. rewrite zget_zset. destruct (i =? rl_ch r); [right; reflexivity| apply IU; exact Hi]. }
      exists (runs ++ [(rl_ch r, 1)]). split; [exact W'|]. split; [exact EB'|]. split.
      { cbn [rl_crc]. rewrite EC, rl_dec_app, crc_list_app. reflexivity. }
      split.
      { right. cbn [rl_ch rl_len]. split; [lia|]. split; [lia|]. rewrite last_last. unfold ADJ. intros _. exact K1a. }
      intros b Hb. cbn [rl_inUse]. rewrite zget_zset. rewrite rl_enc_app in Hb. apply in_app_iff in Hb as [Hb|Hb].
      * destruct (b =? rl_ch r); [reflexivity| apply CV; exact Hb].
      * cbn in Hb. destruct Hb as [<-|[]]. rewrite Z.eqb_refl. reflexivity.
    + unfold rl_data at 1. rewrite EB', unrle1_enc, rl_dec_app by exact W'. cbn [rl_dec]. change (Z.to_nat 1) with 1%nat. cbn [repeat]. rewrite app_nil_r, ED.
      unfold rl_pend. cbn [rl_ch rl_len]. rewrite K1b.
      replace ((c <? 256) && (0 <? 1))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
      replace ((rl_ch r <? 256) && (0 <? 1))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
      change (Z.to_nat 1) with 1%nat. cbn [repeat]. rewrite <- app_assoc. reflexivity.
  - destruct (negb (c =? rl_ch r) || (rl_len r =? 255))%bool eqn:K2.
    + (* [comment removed for export] *)
      destruct PD as [[P1 P2]|(P1 & P2 & P3)].
      * (* [comment removed for export] *)
        replace (rl_ch r <? 256) with false in * by (symmetry; apply Z.ltb_ge; lia).
        assert (RN : runs = []).
        { apply rl_enc_nil_inv; [exact W|]. rewrite <- EB. unfold rl_bytes. rewrite (EMP P1). reflexivity. }
        subst runs. cbn [rl_enc rl_dec crc_list fold_left] in *.
        split; [| split; [| cbn [rl_nblock rl_ch rl_len]; lia]].
        -- split; [exact RI'|]. split; [exact ZB|]. split; [exact IU|]. exists []. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
           split; [exact I|]. split; [exact EB|]. split; [exact EC|]. split; [| exact CV]. right. cbn [last]. unfold ADJ. repeat split; lia.
        -- unfold rl_data, rl_bytes, rl_pend in *. cbn [rl_nblock rl_block rl_ch rl_len]. rewrite EB, P1, P2. cbn.
           replace ((c <? 256) && true)%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.ltb_lt; lia| reflexivity]). reflexivity.
      * replace (rl_ch r <? 256) with true in * by (symmetry; apply Z.ltb_lt; lia).
        cps_destruct (add_pair_core r runs RI ZB IU W EB EC CV ltac:(lia) ltac:(lia) P3) as (W' & EB' & EC' & CV' & ZB' & IU' & CH' & LN' & NB' & DD').
        set (r1 := add_pair_to_block r) in *. set (runs' := runs ++ [(rl_ch r, rl_len r)]) in *.
        split; [| split; [| cbn [rl_nblock rl_ch rl_len]; lia]].
        -- split; [exact RI'|]. split; [cbn [rl_block]; exact ZB'|]. split; [cbn [rl_inUse]; exact IU'|].
           exists runs'. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len]. split; [exact W'|]. split; [exact EB'|]. split; [exact EC'|].
           split; [| exact CV']. right. split; [lia|]. split; [lia|]. subst runs'. rewrite last_last. unfold ADJ. intros HL.
           apply Bool.orb_true_iff in K2. destruct K2 as [K2|K2]; [apply Bool.negb_true_iff in K2; apply Z.eqb_neq in K2; exact K2| apply Z.eqb_eq in K2; lia].
        -- unfold rl_data at 1. unfold rl_bytes. cbn [rl_block rl_nblock rl_ch rl_len]. fold (rl_bytes r1). rewrite EB', unrle1_enc, DD', ED by exact W'.
           unfold rl_pend. cbn [rl_ch rl_len].
           replace ((c <? 256) && (0 <? 1))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
           replace ((rl_ch r <? 256) && (0 <? rl_len r))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
           change (Z.to_nat 1) with 1%nat. cbn [repeat]. rewrite <- !app_assoc. reflexivity.
    + (* [comment removed for export] *)
      apply Bool.orb_false_elim in K2. destruct K2 as [K2a K2b]. apply Bool.negb_false_iff in K2a. apply Z.eqb_eq in K2a. apply Z.eqb_neq in K2b.
      destruct PD as [[P1 P2]|(P1 & P2 & P3)]; [lia|].
      split; [| split; [| cbn [rl_nblock rl_ch rl_len]; lia]].
      * split; [exact RI'|]. split; [exact ZB|]. split; [exact IU|]. exists runs. cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
        split; [exact W|]. split; [exact EB|]. split; [exact EC|]. split; [| exact CV]. right. split; [lia|]. split; [lia| exact P3].
      * unfold rl_data, rl_bytes, rl_pend. cbn [rl_nblock rl_block rl_ch rl_len].
        replace ((rl_ch r <? 256) && (0 <? rl_len r + 1))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
        replace ((rl_ch r <? 256) && (0 <? rl_len r))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
        replace (Z.to_nat (rl_len r + 1)) with (S (Z.to_nat (rl_len r))) by lia. rewrite <- K2a. cbn [repeat]. rewrite repeat_cons. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem RLI_init : forall r, rl_nblock r = 0 -> rl_crc r = crc_init -> rl_ch r = 256 -> rl_len r = 0 -> zbok (rl_block r) ->
  (forall i, 0 <= i < 256 -> zget (rl_inUse r) i = 0) -> RLI r /\ rl_data r = [] /\ rl_pend r = [].
Proof.
  intros r N C CH LN ZB IU.
  split; [| unfold rl_data, rl_bytes, rl_pend; rewrite N, CH, LN; cbn; split; reflexivity].
  split. { unfold rl_inv, rl_ok. rewrite N, C, CH, LN. unfold crc_init. repeat split; lia. }
  split; [exact ZB|]. split; [intros i Hi; left; apply IU; exact Hi|].
  exists []. cbn [RWF rl_enc rl_dec crc_list fold_left]. split; [exact I|]. split; [unfold rl_bytes; rewrite N; reflexivity|].
  split; [exact C|]. split; [left; auto| intros b []].
Qed.

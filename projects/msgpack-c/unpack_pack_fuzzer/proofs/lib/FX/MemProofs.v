(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step.
Open Scope Z_scope.
Unset Lia Cache.

Module MemP.

Section WithSegs.
Variable segs : list Segment.

Definition wok (w : int) : Prop := to_Z w = 1 \/ to_Z w = 2 \/ to_Z w = 4 \/ to_Z w = 8.

Lemma segment_read_bytes_at : forall bytes n start l, segment_read_bytes bytes start n = Some l ->
  forall k, (k < n)%nat -> exists b, segment_byte_at bytes (start + N.of_nat k)%N = Some b.
Proof.
  intros bytes n. induction n as [|n IH]; intros start l H k Hk; [lia|].
  cbn [segment_read_bytes] in H.
  destruct (segment_byte_at bytes start) as [b|] eqn:E; [|discriminate].
  destruct (segment_read_bytes bytes (start + 1)%N n) as [l'|] eqn:E'; [|discriminate].
  destruct k as [|k].
  - exists b. rewrite N.add_0_r. exact E.
  - destruct (IH _ _ E' k ltac:(lia)) as [b' Hb']. exists b'.
    replace (start + N.of_nat (S k))%N with (start + 1 + N.of_nat k)%N by lia. exact Hb'.
Qed.

Lemma find_segment_In : forall sgs a n sg, find_segment sgs a n = Some sg ->
  In sg sgs /\ Z.of_N (seg_base sg) <= a /\ a + n <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction sgs as [|s0 rest IH]; cbn [find_segment]; intros a n sg H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base s0)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)));
    cbn [andb] in H.
  - injection H as ->. split; [left; reflexivity| lia].
  - destruct (IH _ _ _ H) as [A B]; split; [right; exact A| exact B].
  - destruct (IH _ _ _ H) as [A B]; split; [right; exact A| exact B].
  - destruct (IH _ _ _ H) as [A B]; split; [right; exact A| exact B].
Qed.

Lemma half63 : two63 / 2 = 2 ^ 62. Proof. reflexivity. Qed.
Lemma to_Z_7 : to_Z 7%uint63 = Z.ones 3. Proof. reflexivity. Qed.
Lemma to_Z_hi3 : to_Z 8070450532247928832%uint63 = 7 * 2 ^ 60. Proof. reflexivity. Qed.

Lemma keyZ_cases : forall i,
  (0 <= to_Z i < 2 ^ 62 /\ keyZ i = to_Z i) \/ (2 ^ 62 <= to_Z i < 2 ^ 63 /\ keyZ i = to_Z i - 2 ^ 63).
Proof.
  intros i. unfold keyZ, Mem.keyZ. pose proof (int_range i) as R. rewrite two63_eq in *.
  destruct (ltbP i bit62i) as [L|L]; rewrite to_Z_bit62i in L; [left|right]; split; lia.
Qed.

Lemma keyZ_range : forall i, - 2 ^ 62 <= keyZ i < 2 ^ 62.
Proof. intros i. destruct (keyZ_cases i); lia. Qed.

Lemma okey_sound : forall o key, okey o = Some key -> keyZ key = w2Zs o /\ - two63 / 2 <= keyZ key < two63 / 2.
Proof.
  intros o key. unfold okey. rewrite half63. pose proof (wl_range o) as R. rewrite two63_eq in R.
  unfold w2Zs, w2Z. rewrite two63_eq, two64_eq.
  destruct (wt o).
  - destruct (lebP bit62i (wl o)) as [L|L]; [|discriminate]. rewrite to_Z_bit62i in L.
    intros E. injection E as <-. destruct (keyZ_cases (wl o)); lia.
  - destruct (ltbP (wl o) bit62i) as [L|L]; [|discriminate]. rewrite to_Z_bit62i in L.
    intros E. injection E as <-. destruct (keyZ_cases (wl o)); lia.
Qed.

Lemma keyZ_add_small : forall key w, - two63 / 2 <= keyZ key < two63 / 2 - 16 -> 0 <= to_Z w <= 8 ->
  keyZ (PrimInt63.add key w) = keyZ key + to_Z w.
Proof.
  intros key w. rewrite half63. intros Hk Hw.
  pose proof (int_range key). pose proof (int_range w). rewrite two63_eq in *.
  destruct (keyZ_cases (PrimInt63.add key w)) as [[R E]|[R E]]; rewrite E; clear E;
  rewrite add_spec, wB_two63, two63_eq in *;
  destruct (keyZ_cases key) as [[R' E']|[R' E']]; rewrite E' in *;
  first [ rewrite Z.mod_small in * by lia; lia
        | rewrite (mod_cases2 _ (2 ^ 63)) in * by lia; destruct (Z.ltb_spec (to_Z key + to_Z w) (2 ^ 63)); lia ].
Qed.

Lemma lxor_pow2_lo : forall x n, 0 <= n -> 0 <= x < 2 ^ n -> Z.lxor x (2 ^ n) = x + 2 ^ n.
Proof.
  intros x n Hn Hx. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
  destruct (Z.eqb_spec n m); [|apply andb_false_r]. subst.
  rewrite (testbit_high _ m); [reflexivity| lia | lia].
Qed.

Lemma lxor_pow2_hi : forall x n, 0 <= n -> 2 ^ n <= x < 2 ^ (n + 1) -> Z.lxor x (2 ^ n) = x - 2 ^ n.
Proof.
  intros x n Hn Hx. rewrite Z.pow_add_r, Z.pow_1_r in Hx by lia.
  replace x with (Z.lxor (x - 2 ^ n) (2 ^ n)) at 1.
  - rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
  - rewrite lxor_pow2_lo; lia.
Qed.

Lemma to_Z_flip62 : forall a, to_Z (PrimInt63.lxor a bit62i) = keyZ a + 2 ^ 62.
Proof.
  intros a. rewrite lxor_spec', to_Z_bit62i. pose proof (int_range a) as R. rewrite two63_eq in R.
  destruct (keyZ_cases a) as [[R' ->]|[R' ->]].
  - apply lxor_pow2_lo; lia.
  - rewrite lxor_pow2_hi; [lia|lia|]. change (62 + 1) with 63. lia.
Qed.

Lemma kltb_keyZ : forall a b, kltb a b = Z.ltb (keyZ a) (keyZ b).
Proof.
  intros a b. unfold kltb. destruct (ltbP (PrimInt63.lxor a bit62i) (PrimInt63.lxor b bit62i)) as [L|L];
  rewrite !to_Z_flip62 in L; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma kleb_keyZ : forall a b, kleb a b = Z.leb (keyZ a) (keyZ b).
Proof.
  intros a b. unfold kleb. rewrite kltb_keyZ.
  destruct (Z.ltb_spec (keyZ b) (keyZ a)), (Z.leb_spec (keyZ a) (keyZ b)); cbn; lia || reflexivity.
Qed.

Lemma kleb_sound : forall a b, - two63/2 <= keyZ a < two63/2 -> - two63/2 <= keyZ b < two63/2 ->
  kleb a b = true <-> keyZ a <= keyZ b.
Proof. intros a b _ _. rewrite kleb_keyZ. apply Z.leb_le. Qed.

Lemma kltb_sound : forall a b, kltb a b = true <-> keyZ a < keyZ b.
Proof. intros a b. rewrite kltb_keyZ. apply Z.ltb_lt. Qed.

Lemma keyZ_add_nowrap : forall key w, 0 <= to_Z w <= 8 -> kltb key (PrimInt63.add key w) = true ->
  keyZ (PrimInt63.add key w) = keyZ key + to_Z w.
Proof.
  intros key w Hw K. apply kltb_sound in K. revert K.
  pose proof (int_range key). pose proof (int_range w). rewrite two63_eq in *.
  destruct (keyZ_cases (PrimInt63.add key w)) as [[R E]|[R E]]; rewrite E; clear E;
  rewrite add_spec, wB_two63, two63_eq in *;
  destruct (keyZ_cases key) as [[R' E']|[R' E']]; rewrite E' in *;
  rewrite (mod_cases2 _ (2 ^ 63)) in * by lia; destruct (Z.ltb_spec (to_Z key + to_Z w) (2 ^ 63)); lia.
Qed.

Lemma gidx_ok : forall key, to_Z (gidx key) = to_Z key mod 8 /\ 0 <= to_Z (gidx key) < 8.
Proof.
  intros key. unfold gidx. rewrite land_spec', to_Z_7, Z.land_ones by lia. change (2 ^ 3) with 8.
  pose proof (Z.mod_pos_bound (to_Z key) 8 ltac:(lia)). lia.
Qed.
Lemma granule_gidx : forall key, - two63 / 2 <= keyZ key < two63 / 2 ->
  keyZ key = 8 * keyZ (granule key) + to_Z (gidx key) /\ 0 <= to_Z (gidx key) < 8.
Proof.
  intros key _. destruct (gidx_ok key) as [Eg Rg]. rewrite Eg. split; [|lia].
  pose proof (int_range key) as R. rewrite two63_eq in R.
  pose proof (Z.div_mod (to_Z key) 8 ltac:(lia)) as DM.
  assert (Q : 0 <= to_Z key / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  unfold granule. destruct (ltbP key bit62i) as [L|L]; rewrite to_Z_bit62i in L.
  - destruct (keyZ_cases key) as [[_ ->]|[? _]]; [|lia].
    destruct (keyZ_cases (PrimInt63.lsr key 3)) as [[_ ->]|[X _]]; rewrite lsr_spec in *;
      change (2 ^ to_Z 3) with 8 in *; lia.
  - destruct (keyZ_cases key) as [[? _]|[_ ->]]; [lia|].
    assert (E : to_Z (PrimInt63.lor (PrimInt63.lsr key 3) hi3) = to_Z key / 8 + 7 * 2 ^ 60).
    { rewrite lor_spec', lsr_spec. unfold hi3. rewrite to_Z_hi3. change (2 ^ to_Z 3) with 8.
      rewrite <- Z.lxor_lor by (apply Z.bits_inj'; intros m Hm; rewrite Z.land_spec, Z.bits_0, tb_mul_pow2 by lia;
        destruct (Z.leb_spec 60 m); [rewrite (testbit_high _ 60) by lia; reflexivity| apply andb_false_r]).
      symmetry. apply Z.add_nocarry_lxor.
      apply Z.bits_inj'; intros m Hm; rewrite Z.land_spec, Z.bits_0, tb_mul_pow2 by lia.
      destruct (Z.leb_spec 60 m); [rewrite (testbit_high _ 60) by lia; reflexivity| apply andb_false_r]. }
    destruct (keyZ_cases (PrimInt63.lor (PrimInt63.lsr key 3) hi3)) as [[X _]|[_ ->]]; rewrite E in *; [lia|].
    lia.
Qed.

Lemma keyZ_inj : forall a b, keyZ a = keyZ b -> a = b.
Proof.
  intros a b E. apply to_Z_inj.
  destruct (keyZ_cases a) as [[? Ea]|[? Ea]]; destruct (keyZ_cases b) as [[? Eb]|[? Eb]]; lia.
Qed.

Definition addrZ (E : env) (k : int) (key : int) : Z := bv_unsigned (ev E k) + keyZ key.

Lemma Z_to_bv_succ : forall A, (Z_to_bv 64 A + 1)%bv = Z_to_bv 64 (A + 1).
Proof.
  intros A. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned 1%bv) with 1.
  apply bv_wrap_add_idemp_l.
Qed.

Lemma Z_to_bv_eqb : forall a b, 0 <= a < two64 -> 0 <= b < two64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (rewrite bv_modulus_64; lia).
  reflexivity.
Qed.

Lemma rb_unfold : forall m A,
  rb segs m A = match m (Z_to_bv 64 A) with
                | Some b => Some b
                | None => match memory_read segs (Z_to_bv 64 A) 1 with Some (b :: _) => Some b | _ => None end
                end.
Proof. reflexivity. Qed.

Lemma rb_ext : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> rb segs m' a = rb segs m a.
Proof. intros m m' a E. rewrite !rb_unfold, E. reflexivity. Qed.

Lemma wb_ext : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> wb segs m' a = wb segs m a.
Proof. intros m m' a E. unfold wb, wview. rewrite E. reflexivity. Qed.

Lemma in_priv_b_false : forall priv key w a,
  in_priv_b priv key w = false -> to_Z key + to_Z w < two63 ->
  to_Z key <= a < to_Z key + to_Z w -> ~ in_priv priv a.
Proof.
  intros priv key w a Hb Hnw Ha Hin. unfold in_priv in Hin. apply Exists_exists in Hin.
  destruct Hin as [iv [Hiv R]].
  assert (T : existsb (fun iv => PrimInt63.ltb key (snd iv) && PrimInt63.ltb (fst iv) (PrimInt63.add key w))%bool priv = true).
  { apply existsb_exists. exists iv. split; [exact Hiv|].
    pose proof (int_range key). pose proof (int_range w).
    apply andb_true_intro. split; apply ltb_spec; [lia|]. rewrite add_spec, wB_two63, Z.mod_small by lia. lia. }
  unfold in_priv_b in Hb. rewrite Hb in T. discriminate.
Qed.

Lemma ev0_zero : forall E, ev E 0%uint63 = Z_to_bv 64 0 -> bv_unsigned (ev E 0%uint63) = 0.
Proof. intros E ->. reflexivity. Qed.

Lemma rb_rom : forall m a b rest, memory_read segs (Z_to_bv 64 a) 1 = Some (b :: rest) -> rb segs m a <> None.
Proof.
  intros m a b rest H. rewrite rb_unfold. destruct (m (Z_to_bv 64 a)); [discriminate|]. rewrite H. discriminate.
Qed.

Lemma two62Z_eq : Mem.two62Z = 2 ^ 62. Proof. reflexivity. Qed.

Lemma img_bytes_spec : forall a n bs, img_bytes segs a n = Some bs ->
  length bs = n /\ forall t, (t < n)%nat ->
    exists rest, memory_read segs (Z_to_bv 64 (a + Z.of_nat t)) 1 = Some (nth t bs (Z_to_bv 8 0) :: rest).
Proof.
  intros a n. revert a. induction n as [|n IH]; intros a bs H.
  - cbn in H. injection H as <-. split; [reflexivity| intros; lia].
  - cbn [img_bytes] in H.
    destruct (memory_read segs (Z_to_bv 64 a) 1) as [[|b rest]|] eqn:M; try discriminate.
    destruct (img_bytes segs (a + 1) n) as [bs'|] eqn:IB; [|discriminate]. injection H as <-.
    destruct (IH _ _ IB) as [Len By]. split; [cbn; lia|].
    intros [|t] Ht.
    + rewrite Z.add_0_r. exists rest. exact M.
    + destruct (By t ltac:(lia)) as [rest' Hr]. exists rest'.
      replace (a + Z.of_nat (S t)) with (a + 1 + Z.of_nat t) by lia. exact Hr.
Qed.

Lemma img_bytes_complete : forall n a,
  (forall i, 0 <= i < Z.of_nat n -> exists b rest, memory_read segs (Z_to_bv 64 (a + i)) 1 = Some (b :: rest)) ->
  exists bs, img_bytes segs a n = Some bs.
Proof.
  induction n as [|n IH]; intros a H; [exists []; reflexivity|].
  cbn [img_bytes]. destruct (H 0 ltac:(lia)) as (b & rest & M). rewrite Z.add_0_r in M. rewrite M.
  destruct (IH (a + 1)) as [bs ->]; [| exists (b :: bs); reflexivity].
  intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia.
Qed.

Lemma abs_readable_sound : forall a n, 0 <= n -> Mem.abs_readable segs a n = true ->
  a + n < 2 ^ 62 /\
  forall i, 0 <= i < n -> exists b rest, memory_read segs (Z_to_bv 64 (a + i)) 1 = Some (b :: rest).
Proof.
  intros a n Hn H. unfold Mem.abs_readable in H. apply andb_prop in H. destruct H as [B H].
  apply Z.ltb_lt in B. rewrite two62Z_eq in B. split; [exact B|].
  destruct (img_bytes segs a (Z.to_nat n)) as [bs|] eqn:IB; [|discriminate].
  destruct (img_bytes_spec _ _ _ IB) as [Len By].
  intros i Hi. destruct (By (Z.to_nat i) ltac:(lia)) as [rest M]. rewrite Z2Nat.id in M by lia.
  exists (nth (Z.to_nat i) bs (Z_to_bv 8 0)), rest. exact M.
Qed.

Lemma abs_writable_bytes_sound : forall n a i, Mem.abs_writable_bytes segs a n = true -> 0 <= i < Z.of_nat n ->
  exists seg b, find_segment segs (a + i) 1 = Some seg /\ seg_writable seg = true /\ seg_readable seg = true
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg))) = Some b.
Proof.
  induction n as [|n IH]; intros a i H Hi; [cbn in Hi; lia|].
  cbn [Mem.abs_writable_bytes] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.add_0_r. destruct (find_segment segs a 1) as [seg|]; [|discriminate].
    apply andb_prop in H1. destruct H1 as [H1 SB]. apply andb_prop in H1. destruct H1 as [SW SR].
    destruct (segment_byte_at _ _) as [b|] eqn:EB; [|discriminate]. exists seg, b. auto.
  - destruct (IH (a + 1) (i - 1) H2 ltac:(lia)) as (seg & b & P). exists seg, b.
    replace (a + i) with (a + 1 + (i - 1)) by lia. exact P.
Qed.

Lemma find_segment_memory_read : forall a seg b, 0 <= a < two64 ->
  find_segment segs a 1 = Some seg -> seg_readable seg = true ->
  segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) = Some b ->
  memory_read segs (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros a seg b Ha Hf Hr Hb. unfold memory_read.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; lia).
  change (Z.of_N 1) with 1. rewrite Hf, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  rewrite Hb. reflexivity.
Qed.

Lemma find_segment_wb : forall m a seg b, 0 <= a < two64 ->
  find_segment segs a 1 = Some seg -> seg_writable seg = true ->
  segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) = Some b ->
  wb segs m a = true.
Proof.
  intros m a seg b Ha Hf Hw Hb. unfold wb, wview. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; lia). rewrite Hf, Hw, Hb. reflexivity.
Qed.

Lemma abs_writable_sound : forall a n, 0 <= a -> 0 <= n -> Mem.abs_writable segs a n = true ->
  Mem.abs_readable segs a n = true /\
  forall i, 0 <= i < n -> (forall m, wb segs m (a + i) = true) /\
    exists seg, find_segment segs (a + i) 1 = Some seg /\ seg_writable seg = true.
Proof.
  intros a n Ha Hn H. unfold Mem.abs_writable in H. apply andb_prop in H. destruct H as [B H].
  pose proof B as B'. apply Z.ltb_lt in B'. rewrite two62Z_eq in B'.
  assert (BY : forall i, 0 <= i < n -> exists seg b, find_segment segs (a + i) 1 = Some seg /\ seg_writable seg = true
            /\ seg_readable seg = true /\ segment_byte_at (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg))) = Some b).
  { intros i Hi. apply (abs_writable_bytes_sound (Z.to_nat n)); [exact H| lia]. }
  split.
  - unfold Mem.abs_readable. rewrite B. cbn [andb].
    destruct (img_bytes_complete (Z.to_nat n) a) as [bs ->]; [|reflexivity].
    intros i Hi. destruct (BY i ltac:(lia)) as (seg & b & F & W & R & SB).
    exists b, []. apply (find_segment_memory_read _ seg); [unfold two64; lia| assumption..].
  - intros i Hi. destruct (BY i Hi) as (seg & b & F & W & R & SB). split.
    + intros m. apply (find_segment_wb m _ seg b); [unfold two64; lia| assumption..].
    + exists seg. auto.
Qed.

Lemma can_read_hi : forall E fs r key w,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 -> 0 <= to_Z w <= 8 ->
  kltb key (PrimInt63.add key w) = true ->
  match rg_hi r with
  | VL h => match okey h with Some hk => kleb (PrimInt63.add key w) hk | None => false end
  | hi' => (PrimInt63.ltb key bit62i &&
          match decide_ltu fs hi' (VL (wlit (PrimInt63.add key w))) with Some false => true | _ => false end)%bool
  end = true ->
  keyZ key + to_Z w <= hiZ E r.
Proof.
  intros E fs r key w Hfs Hz Hw Knw H. unfold hiZ.
  pose proof (keyZ_add_nowrap key w Hw Knw) as Ea.
  pose proof (int_range key) as Rk. pose proof (int_range w) as Rw. rewrite two63_eq in *.
  assert (SYM : forall hi', (PrimInt63.ltb key bit62i &&
          match decide_ltu fs hi' (VL (wlit (PrimInt63.add key w))) with Some false => true | _ => false end)%bool = true ->
          keyZ key + to_Z w <= bv_unsigned (den E hi')).
  { clear H. intros hi' H. apply andb_prop in H. destruct H as [L D].
    destruct (decide_ltu fs hi' (VL (wlit (PrimInt63.add key w)))) as [[|]|] eqn:Dq; try discriminate.
    apply (ValP.decide_ltu_sound E fs Hfs) in Dq. unfold bv_ltu in Dq. cbn [den] in Dq.
    rewrite wbv_unsigned, wlit_ok, add_spec, wB_two63, two63_eq in Dq.
    destruct (ltbP key bit62i) as [L'|L']; [|discriminate]. rewrite to_Z_bit62i in L'.
    rewrite Z.mod_small in Dq by lia. apply Z.ltb_ge in Dq.
    destruct (keyZ_cases key) as [[_ ->]|[? _]]; lia. }
  destruct (rg_hi r); try (apply SYM; exact H). clear SYM.
  destruct (okey w0) as [hk|] eqn:Ok; [|discriminate].
  destruct (okey_sound _ _ Ok) as [Ek _]. rewrite kleb_keyZ in H. apply Z.leb_le in H.
  cbn [den]. rewrite wbv_unsigned. pose proof (w2Z_range w0). unfold w2Zs in Ek.
  destruct (wt w0); lia.
Qed.

Lemma can_read_sound : forall priv E m fs k r key w,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r -> wok w ->
  can_read segs fs priv k r key w = true ->
  let A := addrZ E k key in
  0 <= A /\ A + to_Z w <= two64
  /\ (forall i, 0 <= i < to_Z w -> rb segs m (A + i) <> None)
  /\ (PrimInt63.eqb k 0%uint63 = false -> forall i, 0 <= i < to_Z w -> loZ r <= keyZ key + i < hiZ E r)
  /\ (PrimInt63.eqb k 0%uint63 = true ->
        forall i, 0 <= i < to_Z w -> (exists bs, memory_read segs (Z_to_bv 64 (A + i)) 1 = Some bs) /\ ~ in_priv priv (A + i)).
Proof.
  intros priv E m fs k r key w Hfs Hz RO Hw CR. cbv zeta. unfold addrZ.
  assert (Hw8 : 0 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  pose proof (int_range key) as Rk. rewrite two63_eq in Rk.
  unfold can_read in CR. destruct (PrimInt63.eqb k 0%uint63) eqn:K.
  - apply eqb_correct in K. subst k. rewrite (ev0_zero E Hz). rewrite !Z.add_0_l.
    apply andb_prop in CR. destruct CR as [CR P]. apply andb_prop in CR. destruct CR as [L AR].
    destruct (ltbP key bit62i) as [L'|]; [|discriminate]. rewrite to_Z_bit62i in L'.
    destruct (keyZ_cases key) as [[_ ->]|[? _]]; [|lia].
    destruct (abs_readable_sound (to_Z key) (to_Z w) ltac:(lia) AR) as [B62 BY].
    split; [lia|]. split; [unfold two64; lia|]. split; [|split].
    + intros i Hi. destruct (BY i Hi) as (b & rest & Hb). eapply rb_rom. exact Hb.
    + intros X; discriminate X.
    + intros _ i Hi. split.
      * destruct (BY i Hi) as (b & rest & Hb). eauto.
      * apply (in_priv_b_false priv key w); [| rewrite two63_eq; lia | lia]. destruct (in_priv_b priv key w); [discriminate|reflexivity].
  - apply andb_prop in CR. destruct CR as [CR HI]. apply andb_prop in CR. destruct CR as [LO NW].
    pose proof (can_read_hi E fs r key w Hfs Hz Hw8 NW HI) as HB.
    rewrite kleb_keyZ in LO. apply Z.leb_le in LO.
    pose proof (ro_range _ _ _ _ _ _ RO K) as RR. pose proof (ro_valid _ _ _ _ _ _ RO K) as RV.
    unfold loZ in *.
    split; [lia|]. split; [lia|]. split; [|split].
    + intros i Hi. apply RV. lia.
    + intros _ i Hi. lia.
    + intros X; discriminate X.
Qed.

Lemma can_write_sound : forall priv E m fs k r key w,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r -> wok w ->
  can_write segs fs priv k r key w = true ->
  can_read segs fs priv k r key w = true
  /\ (forall i, 0 <= i < to_Z w -> wb segs m (addrZ E k key + i) = true)
  /\ (PrimInt63.eqb k 0%uint63 = true ->
        forall i, 0 <= i < to_Z w -> exists seg, find_segment segs (addrZ E k key + i) 1 = Some seg /\ seg_writable seg = true).
Proof.
  intros priv E m fs k r key w Hfs Hz RO Hw CW. unfold addrZ.
  assert (Hw8 : 0 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  pose proof (int_range key) as Rk. rewrite two63_eq in Rk.
  unfold can_write, can_read in CW |- *. destruct (PrimInt63.eqb k 0%uint63) eqn:K.
  - pose proof (eqb_correct _ _ K) as K'. subst k. rewrite (ev0_zero E Hz). rewrite !Z.add_0_l.
    apply andb_prop in CW. destruct CW as [CW P]. apply andb_prop in CW. destruct CW as [L AW].
    destruct (ltbP key bit62i) as [L'|]; [|discriminate]. rewrite to_Z_bit62i in L'.
    destruct (keyZ_cases key) as [[_ ->]|[? _]]; [|lia].
    destruct (abs_writable_sound (to_Z key) (to_Z w) ltac:(lia) ltac:(lia) AW) as [AR BY].
    rewrite AR, P. split; [reflexivity|]. split.
    + intros i Hi. apply (proj1 (BY i Hi)).
    + intros _ i Hi. exact (proj2 (BY i Hi)).
  - apply andb_prop in CW. destruct CW as [W CR]. split; [exact CR|]. split; [|intros X; discriminate X].
    pose proof CR as CR'.
    apply andb_prop in CR. destruct CR as [CR HI]. apply andb_prop in CR. destruct CR as [LO NW].
    pose proof (can_read_hi E fs r key w Hfs Hz Hw8 NW HI) as HB.
    rewrite kleb_keyZ in LO. apply Z.leb_le in LO.
    pose proof (ro_valid _ _ _ _ _ _ RO K) as RV. unfold loZ in *.
    intros i Hi. apply RV; [lia| exact W].
Qed.

Lemma den_VP_addr : forall E k o key, okey o = Some key ->
  0 <= addrZ E k key < two64 ->
  den E (VP k o) = Z_to_bv 64 (addrZ E k key).
Proof.
  intros E k o key Hk _. unfold addrZ. destruct (okey_sound o key Hk) as [-> _].
  cbn [den]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, wbv_unsigned.
  unfold bv_wrap. rewrite bv_modulus_64. unfold w2Zs. destruct (wt o); [|reflexivity].
  replace (bv_unsigned (ev E k) + (w2Z o - two64)) with (bv_unsigned (ev E k) + w2Z o + (-1) * two64) by lia.
  rewrite Z.mod_add; [reflexivity|]. rewrite two64_eq. lia.
Qed.

Lemma ov_read_bytes_rb : forall m A n bs,
  0 <= A -> A + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i)) ->
  length bs = n ->
  ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs.
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs HA HAn Hrb Hlen.
  - destruct bs; [reflexivity| discriminate].
  - destruct bs as [|b bs']; [discriminate|]. cbn [ov_read_bytes].
    pose proof (Hrb 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite rb_unfold in H0. cbn [Z.to_nat nth_error] in H0.
    rewrite H0. rewrite Z_to_bv_succ.
    rewrite (IH (A + 1) bs'); [reflexivity| lia | lia | | cbn in Hlen; lia].
    intros i Hi. replace (A + 1 + i) with (A + (i + 1)) by lia. rewrite Hrb by lia.
    rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. reflexivity.
Qed.

Definition store_bytes (w : int) (x : word) : list byte := Z_to_le_bytes (Z.to_nat (to_Z w)) (bv_unsigned x).

Lemma store_ok_wb : forall m A n,
  0 <= A -> A + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> wb segs m (A + i) = true) ->
  store_ok segs m (Z_to_bv 64 A) n = true.
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A HA HAn Hwb; [reflexivity|].
  cbn [store_ok]. pose proof (Hwb 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold wb in H0.
  destruct (wview segs m (Z_to_bv 64 A)); [|discriminate]. rewrite Z_to_bv_succ.
  apply IH; [lia|lia|]. intros i Hi. replace (A + 1 + i) with (A + (i + 1)) by lia. apply Hwb. lia.
Qed.

Lemma write_to_mem_frame : forall m A bs a,
  0 <= A -> A + Z.of_nat (length bs) <= two64 -> 0 <= a < two64 ->
  ~ (A <= a < A + Z.of_nat (length bs)) ->
  write_to_mem m (Z_to_bv 64 A) bs (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m A bs. revert m A. induction bs as [|b bs IH]; intros m A a HA HAn Ha Hout; [reflexivity|].
  cbn [write_to_mem length] in *. rewrite Z_to_bv_succ.
  rewrite IH; [| lia | lia | lia | lia].
  rewrite Z_to_bv_eqb by lia. destruct (Z.eqb_spec a A); [lia| reflexivity].
Qed.

Lemma write_to_mem_in : forall m A bs i,
  0 <= A -> A + Z.of_nat (length bs) <= two64 -> 0 <= i < Z.of_nat (length bs) ->
  write_to_mem m (Z_to_bv 64 A) bs (Z_to_bv 64 (A + i)) = nth_error bs (Z.to_nat i).
Proof.
  intros m A bs. revert m A. induction bs as [|b bs IH]; intros m A i HA HAn Hi; [cbn in Hi; lia|].
  cbn [write_to_mem length] in *. rewrite Z_to_bv_succ.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.add_0_r. rewrite write_to_mem_frame; [| lia | lia | lia | lia].
    rewrite Z_to_bv_eqb, Z.eqb_refl by lia. reflexivity.
  - replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite IH by lia.
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma write_to_mem_mapped : forall m addr bs a, m a <> None -> write_to_mem m addr bs a <> None.
Proof.
  intros m addr bs. revert m addr. induction bs as [|b bs IH]; intros m addr a H; cbn [write_to_mem]; [exact H|].
  apply IH. destruct (bv_eqb a addr); [discriminate| exact H].
Qed.

Lemma slot_ok_nil : forall E m base, slot_ok segs E m base [].
Proof. intros. split; [exact I| constructor]. Qed.

Definition zbyte (z t : Z) : Z := (z / 2 ^ (8 * t)) mod 256.

Lemma zbyte_range : forall z t, 0 <= zbyte z t < 256.
Proof. intros. unfold zbyte. apply Z.mod_pos_bound. lia. Qed.

Lemma zbyte_testbit : forall z t r, 0 <= t -> 0 <= r < 8 ->
  Z.testbit (zbyte z t) r = Z.testbit z (8 * t + r).
Proof.
  intros z t r Ht Hr. unfold zbyte. change 256 with (2 ^ 8).
  rewrite Z.mod_pow2_bits_low, Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma zbytes_eq : forall x y n, 0 <= n ->
  (forall t, 0 <= t < n -> zbyte x t = zbyte y t) -> x mod 2 ^ (8 * n) = y mod 2 ^ (8 * n).
Proof.
  intros x y n Hn H. apply Z.bits_inj'. intros m Hm.
  rewrite !Z.testbit_mod_pow2 by lia. destruct (Z.ltb_spec m (8 * n)); [|reflexivity]. cbn [andb].
  pose proof (Z.div_mod m 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as MB.
  assert (D : 0 <= m / 8 < n) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace m with (8 * (m / 8) + m mod 8) by lia.
  rewrite <- !zbyte_testbit by lia. rewrite (H (m / 8)) by lia. reflexivity.
Qed.

Lemma byte_of_zbyte : forall (x : word) i, 0 <= i -> bv_unsigned (byte_of x i) = zbyte (bv_unsigned x) i.
Proof.
  intros x i Hi. unfold byte_of, zbyte. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zbyte_small : forall b, 0 <= b < 256 -> zbyte b 0 = b.
Proof. intros b Hb. unfold zbyte. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. apply Z.mod_small. lia. Qed.

Lemma bytes_le_to_Z_cons : forall b bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
  intros b bs. cbn [bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
  pose proof (ValP.bytes_le_to_Z_nonneg bs) as Hbs.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor; [lia| |];
  apply Z.bits_inj'; intros m Hm; rewrite Z.land_spec, Z.bits_0, tb_mul_pow2 by lia;
  (destruct (Z.leb_spec 8 m); [rewrite (testbit_high _ 8) by lia; reflexivity| apply andb_false_r]).
Qed.

Lemma zbyte_succ : forall b z t, 0 <= b < 256 -> 0 <= t -> zbyte (b + 256 * z) (t + 1) = zbyte z t.
Proof.
  intros b z t Hb Ht. unfold zbyte. f_equal.
  replace (8 * (t + 1)) with (8 + 8 * t) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma zbyte_bytes_le : forall bs t, (t < length bs)%nat ->
  zbyte (bytes_le_to_Z bs) (Z.of_nat t) = bv_unsigned (nth t bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b bs IH]; intros t Ht; [cbn in Ht; lia|].
  rewrite bytes_le_to_Z_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  destruct t as [|t].
  - cbn [nth Z.of_nat]. unfold zbyte. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - cbn [nth]. replace (Z.of_nat (S t)) with (Z.of_nat t + 1) by lia. rewrite zbyte_succ by lia.
    apply IH. cbn in Ht. lia.
Qed.

Lemma bytes_le_to_Z_bound : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; [cbn; lia|]. rewrite bytes_le_to_Z_cons. cbn [length].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma ext_Z_mod : forall sx n x y, x mod 2 ^ (8 * n) = y mod 2 ^ (8 * n) -> ext_Z sx 0 n x = ext_Z sx 0 n y.
Proof. intros sx n x y H. unfold ext_Z. rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r, H. reflexivity. Qed.

Lemma ext_Z_compose0 : forall sx lo n z, 0 <= n -> ext_Z sx lo n z = ext_Z sx 0 n (ext_Z false lo n z).
Proof.
  intros sx lo n z Hn. unfold ext_Z. rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma ext_Z_false_range : forall lo n z, 0 <= n -> 0 <= ext_Z false lo n z < 2 ^ (8 * n).
Proof. intros. unfold ext_Z. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zbyte_eq_bits : forall x y t, 0 <= t ->
  (forall r, 0 <= r < 8 -> Z.testbit x (8 * t + r) = Z.testbit y (8 * t + r)) -> zbyte x t = zbyte y t.
Proof.
  intros x y t Ht H. apply Z.bits_inj'. intros r Hr.
  pose proof (zbyte_range x t). pose proof (zbyte_range y t).
  destruct (Z.lt_ge_cases r 8).
  - rewrite !zbyte_testbit by lia. apply H. lia.
  - rewrite !(testbit_high _ 8); [reflexivity| | lia | | lia]; change (2 ^ 8) with 256; lia.
Qed.

Lemma zbyte_mod : forall x K t, 0 <= t -> 8 * (t + 1) <= K -> zbyte (x mod 2 ^ K) t = zbyte x t.
Proof.
  intros x K t Ht HK. apply zbyte_eq_bits; [lia|]. intros r Hr. apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma zbyte_add_mul : forall x k K t, 0 <= t -> 8 * (t + 1) <= K -> zbyte (x + k * 2 ^ K) t = zbyte x t.
Proof.
  intros x k K t Ht HK. rewrite <- (zbyte_mod (x + k * 2 ^ K) K), <- (zbyte_mod x K) by lia.
  rewrite Z.mod_add; [reflexivity|]. apply Z.pow_nonzero; lia.
Qed.

Lemma zbyte_ext_Z : forall sx lo n z t, 0 <= lo -> 1 <= n <= 8 -> 0 <= t < n -> 0 <= z ->
  zbyte (ext_Z sx lo n z) t = zbyte z (lo + t).
Proof.
  intros sx lo n z t Hlo Hn Ht Hz.
  transitivity (zbyte (ext_Z false lo n z) t); [| unfold zbyte; apply ValP.ext_Z_byte; lia].
  destruct sx; [|reflexivity].
  assert (Hu : 0 <= ext_Z false lo n z < 2 ^ (8 * n)) by (unfold ext_Z; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  assert (HP : 2 ^ (8 * n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  assert (HP1 : 2 ^ (8 * n - 1) < 2 ^ (8 * n)) by (apply Z.pow_lt_mono_r; lia).
  unfold ext_Z in *. set (u := (z / 2 ^ (8 * lo)) mod 2 ^ (8 * n)) in *. clearbody u. rewrite two64_eq.
  destruct (Z.leb_spec (2 ^ (8 * n - 1)) u).
  - rewrite <- (Z.mod_unique_pos (u - 2 ^ (8 * n)) (2 ^ 64) (-1) (u + (-1) * 2 ^ (8 * n) + 1 * 2 ^ 64)) by lia.
    rewrite !zbyte_add_mul by lia. reflexivity.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma add_small : forall a b, to_Z a + to_Z b < two63 -> to_Z (PrimInt63.add a b) = to_Z a + to_Z b.
Proof.
  intros a b H. pose proof (int_range a). pose proof (int_range b).
  rewrite add_spec, wB_two63, Z.mod_small; lia.
Qed.
Lemma sub_small : forall a b, to_Z b <= to_Z a -> to_Z (PrimInt63.sub a b) = to_Z a - to_Z b.
Proof.
  intros a b H. pose proof (int_range a). pose proof (int_range b).
  rewrite sub_spec, wB_two63, Z.mod_small; lia.
Qed.
Lemma to_Z_max : forall a b, to_Z (if PrimInt63.ltb a b then b else a) = Z.max (to_Z a) (to_Z b).
Proof. intros a b. destruct (ltbP a b); lia. Qed.
Lemma to_Z_min : forall a b, to_Z (if PrimInt63.ltb a b then a else b) = Z.min (to_Z a) (to_Z b).
Proof. intros a b. destruct (ltbP a b); lia. Qed.

Definition ciZ (c : cell) : Z := to_Z (c_idx c).
Definition ceZ (c : cell) : Z := to_Z (c_idx c) + to_Z (c_w c).
Definition cell_wf (c : cell) : Prop := 0 <= to_Z (c_idx c) /\ 0 < to_Z (c_w c) /\ to_Z (c_idx c) + to_Z (c_w c) <= 8.

Fixpoint cover (cs : list cell) (j : Z) : option cell :=
  match cs with
  | [] => None
  | c :: cs' => if (Z.leb (ciZ c) j && Z.ltb j (ceZ c))%bool then Some c else cover cs' j
  end.

Definition csorted (cs : list cell) : Prop := Sorted.StronglySorted (fun a b => ceZ a <= ciZ b) cs.

Lemma slot_sorted_csorted : forall s, slot_sorted s -> Forall cell_wf s -> csorted s.
Proof.
  induction s as [|c s IH]; intros Hs Hw; [constructor|].
  inversion Hw as [|c' s' Wc Ws]; subst.
  assert (Hs' : slot_sorted s) by exact (proj2 Hs).
  constructor; [apply IH; assumption|].
  specialize (IH Hs' Ws).
  destruct s as [|c2 s2]; [constructor|]. cbn [slot_sorted] in Hs. destruct Hs as [H12 _].
  constructor; [unfold ceZ, ciZ; lia|].
  inversion IH as [|x l S2 F2]; subst.
  inversion Ws as [|y l' W2 Ws2]; subst.
  eapply Forall_impl; [|exact F2]. intros c3 H23. unfold cell_wf, ceZ, ciZ in *. lia.
Qed.

Lemma cover_In : forall cs j c, cover cs j = Some c -> In c cs /\ ciZ c <= j < ceZ c.
Proof.
  induction cs as [|c0 cs IH]; cbn [cover]; intros j c H; [discriminate|].
  destruct (Z.leb_spec (ciZ c0) j); destruct (Z.ltb_spec j (ceZ c0)); cbn [andb] in H;
    first [injection H as ->; split; [left; reflexivity| lia] | destruct (IH _ _ H); split; [right|]; tauto].
Qed.

Lemma cover_None : forall cs j, cover cs j = None -> Forall (fun c => ~ (ciZ c <= j < ceZ c)) cs.
Proof.
  induction cs as [|c0 cs IH]; cbn [cover]; intros j H; [constructor|].
  destruct (Z.leb_spec (ciZ c0) j); destruct (Z.ltb_spec j (ceZ c0)); cbn [andb] in H; try discriminate;
    (constructor; [lia| apply IH; exact H]).
Qed.

Lemma cover_head : forall c cs j, Forall (fun b => ceZ c <= ciZ b) cs -> ciZ c <= j < ceZ c -> cover cs j = None.
Proof.
  intros c cs j F Hj. induction F as [|c' cs' Hc' F' IH]; [reflexivity|]. cbn [cover].
  destruct (Z.leb_spec (ciZ c') j); [lia|]. cbn [andb]. exact IH.
Qed.

Definition ago (i w : int) :=
  fix go (cs : list cell) (pos : int) (acc : option sv) (tiled : bool) {struct cs} : option sv :=
    match cs with
    | [] => if tiled && negb (PrimInt63.eqb pos (PrimInt63.add i w)) then None else acc
    | c :: cs' =>
        let ci := c_idx c in let cw := c_w c in
        let lo := if PrimInt63.ltb ci i then i else ci in
        let hi := let ce := PrimInt63.add ci cw in let e := PrimInt63.add i w in
                  if PrimInt63.ltb ce e then ce else e in
        if tiled && negb (PrimInt63.eqb lo pos) then None else
        let piece := sv_ext false (PrimInt63.sub lo ci) (PrimInt63.sub hi lo) (c_v c) in
        let acc' := match acc with
                    | Some a => Some (sv_ins (PrimInt63.sub lo i) (PrimInt63.sub hi lo) a piece)
                    | None => None
                    end in
        go cs' hi acc' tiled
    end.

Lemma assemble_ago : forall base cs i w,
  Mem.assemble base cs i w =
  match base with Some b => ago i w cs i (Some b) false | None => ago i w cs i (Some (VL wzero)) true end.
Proof. reflexivity. Qed.

Lemma Z_to_bv_small : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. exact Hz. Qed.

Section Ago.
Variable E : env.
Variables i w : int.
Hypothesis Hw : 1 <= to_Z w.
Hypothesis Hiw : to_Z i + to_Z w <= 8.

Definition dbyte (v : sv) (t : Z) : Z := zbyte (bv_unsigned (den E v)) t.

Lemma ago_nil : forall pos acc tiled,
  ago i w [] pos acc tiled = if tiled && negb (PrimInt63.eqb pos (PrimInt63.add i w)) then None else acc.
Proof. reflexivity. Qed.

Lemma ago_cons : forall c cs pos acc tiled,
  ago i w (c :: cs) pos acc tiled =
  let ci := c_idx c in let cw := c_w c in
  let lo := if PrimInt63.ltb ci i then i else ci in
  let hi := let ce := PrimInt63.add ci cw in let e := PrimInt63.add i w in
            if PrimInt63.ltb ce e then ce else e in
  if tiled && negb (PrimInt63.eqb lo pos) then None else
  let piece := sv_ext false (PrimInt63.sub lo ci) (PrimInt63.sub hi lo) (c_v c) in
  let acc' := match acc with
              | Some a => Some (sv_ins (PrimInt63.sub lo i) (PrimInt63.sub hi lo) a piece)
              | None => None
              end in
  ago i w cs hi acc' tiled.
Proof. reflexivity. Qed.

Lemma ago_spec : forall cs pos a tiled v,
  csorted cs -> Forall cell_wf cs -> Forall (fun c => ciZ c < to_Z i + to_Z w /\ to_Z i < ceZ c) cs ->
  to_Z i <= to_Z pos <= to_Z i + to_Z w ->
  ago i w cs pos (Some a) tiled = Some v ->
  (forall t, 0 <= t < to_Z w ->
     dbyte v t = match cover cs (to_Z i + t) with
                 | Some c => dbyte (c_v c) (to_Z i + t - ciZ c)
                 | None => dbyte a t
                 end)
  /\ (tiled = true -> forall t, to_Z pos - to_Z i <= t < to_Z w -> cover cs (to_Z i + t) <> None).
Proof.
  pose proof (int_range i) as Ri. pose proof (int_range w) as Rw. rewrite two63_eq in Ri, Rw.
  induction cs as [|c cs IH]; intros pos a tiled v S W O Hpos H.
  - rewrite ago_nil in H. pose proof (int_range pos) as Rp.
    destruct tiled; cbn [andb negb] in H.
    + destruct (eqbP pos (PrimInt63.add i w)) as [P|P]; [|discriminate]. injection H as <-.
      rewrite add_small in P by (rewrite two63_eq; lia).
      split; [intros; reflexivity|]. intros _ t Ht. exfalso. lia.
    + injection H as <-. split; [intros; reflexivity| intros X; discriminate X].
  - rewrite ago_cons in H. cbv zeta in H.
    inversion S as [|x l S' Fc]; subst. inversion W as [|x l Wc W']; subst. inversion O as [|x l [Oc1 Oc2] O']; subst.
    unfold cell_wf in Wc. unfold ciZ, ceZ in Oc1, Oc2.
    set (lo := if PrimInt63.ltb (c_idx c) i then i else c_idx c) in H.
    set (hi := if PrimInt63.ltb (PrimInt63.add (c_idx c) (c_w c)) (PrimInt63.add i w)
               then PrimInt63.add (c_idx c) (c_w c) else PrimInt63.add i w) in H.
    assert (Elo : to_Z lo = Z.max (to_Z (c_idx c)) (to_Z i)) by (subst lo; apply to_Z_max).
    assert (Ehi : to_Z hi = Z.min (to_Z (c_idx c) + to_Z (c_w c)) (to_Z i + to_Z w)).
    { subst hi. rewrite to_Z_min, !add_small by (rewrite two63_eq; lia). reflexivity. }
    assert (Hlohi : to_Z lo < to_Z hi) by lia.
    destruct (tiled && negb (PrimInt63.eqb lo pos)) eqn:T; [discriminate|].
    assert (Es1 : to_Z (PrimInt63.sub lo (c_idx c)) = to_Z lo - to_Z (c_idx c)) by (apply sub_small; lia).
    assert (Es2 : to_Z (PrimInt63.sub hi lo) = to_Z hi - to_Z lo) by (apply sub_small; lia).
    assert (Es3 : to_Z (PrimInt63.sub lo i) = to_Z lo - to_Z i) by (apply sub_small; lia).
    match type of H with ago _ _ _ _ (Some ?a') _ = _ => set (a1 := a') in H end.
    destruct (IH hi a1 tiled v S' W' O' ltac:(lia) H) as [B1 B2].

    assert (Da1 : forall t, 0 <= t < to_Z w ->
      dbyte a1 t = if (Z.leb (to_Z lo - to_Z i) t && Z.ltb t (to_Z hi - to_Z i))%bool
                   then dbyte (c_v c) (to_Z i + t - to_Z (c_idx c)) else dbyte a t).
    { intros t Ht. subst a1. unfold dbyte at 1.
      rewrite ValP.den_sv_ins by (unfold ValP.width_ok; lia).
      rewrite ValP.den_sv_ext by (unfold ValP.width_ok; lia).
      unfold ext_word. rewrite Es1, Es2, Es3.
      pose proof (bv_unsigned_in_range 64 (den E a)) as Ra. rewrite bv_modulus_64 in Ra.
      pose proof (bv_unsigned_in_range 64 (den E (c_v c))) as Rc. rewrite bv_modulus_64 in Rc.
      pose proof (ValP.ext_Z_range false (to_Z lo - to_Z (c_idx c)) (to_Z hi - to_Z lo) (bv_unsigned (den E (c_v c)))
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Re.
      rewrite (Z_to_bv_small (ext_Z _ _ _ _)) by exact Re.
      rewrite Z_to_bv_small by (apply ValP.ins_Z_range; unfold two64 in *; lia).
      destruct (Z.leb_spec (to_Z lo - to_Z i) t); [destruct (Z.ltb_spec t (to_Z hi - to_Z i))|]; cbn [andb].
      - unfold zbyte at 1. rewrite ValP.ins_Z_byte_in by lia. fold (zbyte (ext_Z false (to_Z lo - to_Z (c_idx c)) (to_Z hi - to_Z lo) (bv_unsigned (den E (c_v c)))) (t - (to_Z lo - to_Z i))).
        rewrite zbyte_ext_Z by lia. unfold dbyte. f_equal. lia.
      - unfold zbyte at 1. rewrite ValP.ins_Z_byte_out by (unfold two64 in *; lia). reflexivity.
      - unfold zbyte at 1. rewrite ValP.ins_Z_byte_out by (unfold two64 in *; lia). reflexivity. }
    assert (CH : forall j, to_Z (c_idx c) <= j < to_Z (c_idx c) + to_Z (c_w c) -> cover cs j = None).
    { intros j Hj. apply (cover_head c); [exact Fc| unfold ciZ, ceZ; lia]. }
    split.
    + intros t Ht. rewrite B1 by lia. cbn [cover]. unfold ciZ, ceZ.
      destruct (Z.leb_spec (to_Z (c_idx c)) (to_Z i + t));
        [destruct (Z.ltb_spec (to_Z i + t) (to_Z (c_idx c) + to_Z (c_w c)))|]; cbn [andb].
      * rewrite CH by lia. rewrite Da1 by lia.
        destruct (Z.leb_spec (to_Z lo - to_Z i) t); [|lia]. destruct (Z.ltb_spec t (to_Z hi - to_Z i)); [|lia]. reflexivity.
      * destruct (cover cs (to_Z i + t)); [reflexivity|]. rewrite Da1 by lia.
        destruct (Z.leb_spec (to_Z lo - to_Z i) t); [|reflexivity]. destruct (Z.ltb_spec t (to_Z hi - to_Z i)); [lia|reflexivity].
      * destruct (cover cs (to_Z i + t)); [reflexivity|]. rewrite Da1 by lia.
        destruct (Z.leb_spec (to_Z lo - to_Z i) t); [|reflexivity]. destruct (Z.ltb_spec t (to_Z hi - to_Z i)); [lia|reflexivity].
    + intros Ht t Htr. subst tiled. cbn [andb] in T.
      destruct (eqbP lo pos) as [P|P]; [|discriminate].
      cbn [cover]. unfold ciZ, ceZ.
      destruct (Z.leb_spec (to_Z (c_idx c)) (to_Z i + t));
        [destruct (Z.ltb_spec (to_Z i + t) (to_Z (c_idx c) + to_Z (c_w c)))|]; cbn [andb].
      * discriminate.
      * apply B2; [reflexivity| lia].
      * exfalso. lia.
Qed.
End Ago.

Definition overlapsb (i w : int) (c : cell) : bool :=
  negb (Z.leb (ceZ c) (to_Z i)) && negb (Z.leb (to_Z i + to_Z w) (ciZ c)).

Lemma overlapping_spec : forall s i w, csorted s -> Forall cell_wf s -> to_Z i + to_Z w <= 16 ->
  overlapping s i w = List.filter (overlapsb i w) s.
Proof.
  induction s as [|c s IH]; intros i w S W Hiw; [reflexivity|].
  pose proof (int_range i). pose proof (int_range w). rewrite two63_eq in *.
  inversion S as [|x l S' Fc]; subst. inversion W as [|x l Wc W']; subst. unfold cell_wf in Wc.
  cbn [overlapping List.filter]. unfold overlapsb at 1. unfold ceZ at 1. unfold ciZ at 1.
  destruct (lebP (PrimInt63.add (c_idx c) (c_w c)) i) as [L|L]; rewrite add_small in L by (rewrite two63_eq; lia).
  - destruct (Z.leb_spec (to_Z (c_idx c) + to_Z (c_w c)) (to_Z i)); [|lia]. cbn [negb andb]. apply IH; assumption.
  - destruct (Z.leb_spec (to_Z (c_idx c) + to_Z (c_w c)) (to_Z i)); [lia|]. cbn [negb andb].
    destruct (lebP (PrimInt63.add i w) (c_idx c)) as [L2|L2]; rewrite add_small in L2 by (rewrite two63_eq; lia).
    + destruct (Z.leb_spec (to_Z i + to_Z w) (to_Z (c_idx c))); [|lia]. cbn [negb].
      symmetry. apply IMap.filter_all_false. eapply Forall_impl; [|exact Fc].
      intros c' Hc'. cbv beta in Hc'. unfold overlapsb. destruct (Z.leb_spec (to_Z i + to_Z w) (ciZ c')); [apply andb_false_r|].
      unfold ceZ, ciZ in *. lia.
    + destruct (Z.leb_spec (to_Z i + to_Z w) (to_Z (c_idx c))); [lia|]. cbn [negb]. f_equal. apply IH; assumption.
Qed.

Lemma overlapping_csorted : forall s i w, csorted s -> Forall cell_wf s -> to_Z i + to_Z w <= 16 ->
  csorted (overlapping s i w) /\ Forall cell_wf (overlapping s i w)
  /\ Forall (fun c => ciZ c < to_Z i + to_Z w /\ to_Z i < ceZ c) (overlapping s i w)
  /\ incl (overlapping s i w) s.
Proof.
  intros s i w S W H. rewrite overlapping_spec by assumption. split; [|split; [|split]].
  - apply IMap.sorted_filter. exact S.
  - apply incl_Forall with (l1 := s); [apply List.incl_filter| exact W].
  - apply Forall_forall. intros c Hc. apply List.filter_In in Hc. destruct Hc as [_ Hc]. unfold overlapsb in Hc.
    apply andb_prop in Hc. destruct Hc as [A B].
    destruct (Z.leb_spec (ceZ c) (to_Z i)); [discriminate|]. destruct (Z.leb_spec (to_Z i + to_Z w) (ciZ c)); [discriminate|]. lia.
  - apply List.incl_filter.
Qed.

Lemma overlapping_uncovered : forall s i w j, csorted s -> Forall cell_wf s -> to_Z i + to_Z w <= 16 ->
  to_Z i <= j < to_Z i + to_Z w -> cover (overlapping s i w) j = None ->
  Forall (fun c => ~ covers c j) s.
Proof.
  intros s i w j S W H Hj C. apply cover_None in C. rewrite overlapping_spec in C by assumption.
  apply Forall_forall. intros c Hc. unfold covers.
  destruct (overlapsb i w c) eqn:Ob.
  - pose proof (proj1 (Forall_forall _ _) C c ltac:(apply List.filter_In; auto)) as P. unfold ciZ, ceZ in P. exact P.
  - unfold overlapsb, ceZ, ciZ in Ob.
    destruct (Z.leb_spec (to_Z (c_idx c) + to_Z (c_w c)) (to_Z i)); [lia|].
    destruct (Z.leb_spec (to_Z i + to_Z w) (to_Z (c_idx c))); [lia|]. discriminate.
Qed.

Lemma lor_disjoint_add : forall a b K, 0 <= a < 2 ^ K -> 0 <= b -> Z.lor a (b * 2 ^ K) = a + b * 2 ^ K.
Proof.
  intros a b K Ha Hb.
  assert (HK : 0 <= K) by (destruct (Z.le_gt_cases 0 K); [assumption|]; rewrite Z.pow_neg_r in Ha; lia).
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor; [reflexivity| |];
  apply Z.bits_inj'; intros m Hm; rewrite Z.land_spec, Z.bits_0, tb_mul_pow2 by lia;
  (destruct (Z.leb_spec K m); [rewrite (testbit_high _ K) by lia; reflexivity| apply andb_false_r]).
Qed.

Lemma bytes_to_int_ok : forall bs, (length bs <= 7)%nat -> to_Z (bytes_to_int bs) = bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; intros Hl; [reflexivity|].
  cbn [bytes_to_int length] in *. rewrite bytes_le_to_Z_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_bound bs) as Hbs.
  assert (HP : 2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 48) by (apply Z.pow_le_mono_r; lia).
  rewrite lor_spec', of_Z_spec, lsl_spec, IH, wB_two63, two63_eq by lia. change (2 ^ to_Z 8) with 256.
  rewrite !Z.mod_small by lia. change (bytes_le_to_Z bs * 256) with (bytes_le_to_Z bs * 2 ^ 8).
  rewrite lor_disjoint_add; [lia| |lia]. change (2 ^ 8) with 256. lia.
Qed.

Lemma bytes_le_to_Z_app1 : forall l' b7,
  bytes_le_to_Z (l' ++ [b7]) = bytes_le_to_Z l' + bv_unsigned b7 * 2 ^ (8 * Z.of_nat (length l')).
Proof.
  induction l' as [|b l' IH]; intros b7; [cbn [app length Z.of_nat]; rewrite bytes_le_to_Z_cons; cbn [bytes_le_to_Z]; lia|].
  cbn [app length]. rewrite !bytes_le_to_Z_cons, IH.
  replace (8 * Z.of_nat (S (length l'))) with (8 + 8 * Z.of_nat (length l')) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma bytes_to_w64_ok : forall bs, (length bs <= 8)%nat -> w2Z (bytes_to_w64 bs) = bytes_le_to_Z bs.
Proof.
  intros bs Hl.
  assert (GEN : forall l, (length l <= 7)%nat -> w2Z (W64 false (bytes_to_int l)) = bytes_le_to_Z l).
  { intros l Hl'. unfold w2Z. cbn [wt wl]. rewrite bytes_to_int_ok by exact Hl'. reflexivity. }
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 bs]]]]]]]]]; try (apply GEN; cbn; lia); [|cbn in Hl; lia].
  unfold bytes_to_w64.
  set (lo7 := bytes_to_int [b0; b1; b2; b3; b4; b5; b6]).
  assert (Elo : to_Z lo7 = bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6]) by (apply bytes_to_int_ok; cbn; lia).
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3; b4; b5; b6]) as B7. change (2 ^ (8 * Z.of_nat (length _))) with (2 ^ 56) in B7.
  transitivity (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6] + bv_unsigned b7 * 2 ^ 56).
  - pose proof (bv_unsigned_in_range 8 b7) as Hb. change (bv_modulus 8) with 256 in Hb.
    unfold w2Z. cbn [wt wl]. rewrite lor_spec', lsl_spec, of_Z_spec, Elo, wB_two63, two63_eq. change (2 ^ to_Z 56) with (2 ^ 56).
    change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
    pose proof (Z.mod_pos_bound (bv_unsigned b7) 128 ltac:(lia)) as M.
    rewrite (Z.mod_small (bv_unsigned b7 mod 128)) by lia.
    rewrite (Z.mod_small (bv_unsigned b7 mod 128 * 2 ^ 56)) by (change (2^63) with (128 * 2^56); nia).
    rewrite lor_disjoint_add by lia.
    pose proof (Z.div_mod (bv_unsigned b7) 128 ltac:(lia)) as DM.
    destruct (Z.leb_spec 128 (bv_unsigned b7)).
    + replace (bv_unsigned b7 / 128) with 1 in DM by (apply Z.div_unique_pos with (r := bv_unsigned b7 - 128); lia).
      change (2 ^ 63) with (128 * 2 ^ 56). lia.
    + rewrite (Z.mod_small (bv_unsigned b7) 128) by lia. lia.
  - change [b0; b1; b2; b3; b4; b5; b6; b7] with ([b0; b1; b2; b3; b4; b5; b6] ++ [b7]).
    rewrite bytes_le_to_Z_app1. change (2 ^ (8 * Z.of_nat (length _))) with (2 ^ 56). reflexivity.
Qed.

Lemma zbyte_high : forall x t, 0 <= t -> 0 <= x < 2 ^ (8 * t) -> zbyte x t = 0.
Proof. intros x t Ht Hx. unfold zbyte. rewrite Z.div_small by lia. reflexivity. Qed.

Lemma zbyte_bytes_le_nth : forall bs t,
  zbyte (bytes_le_to_Z bs) (Z.of_nat t) = bv_unsigned (nth t bs (Z_to_bv 8 0)).
Proof.
  intros bs t. destruct (Nat.lt_ge_cases t (length bs)) as [L|L].
  - apply zbyte_bytes_le. exact L.
  - rewrite nth_overflow by exact L. rewrite zbyte_high; [reflexivity| lia|].
    pose proof (bytes_le_to_Z_bound bs).
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ (8 * Z.of_nat t)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma bg_bytes_nth : forall g off n t, (t < n)%nat -> nth t (bg_bytes g off n) (Z_to_bv 8 0) = g (off + Z.of_nat t).
Proof.
  intros g off n. revert off. induction n as [|n IH]; intros off t Ht; [lia|].
  cbn [bg_bytes]. destruct t as [|t]; [cbn; f_equal; lia|]. cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_firstn_lt : forall {T} (l : list T) n t d, (t < n)%nat -> nth t (firstn n l) d = nth t l d.
Proof.
  intros T l. induction l as [|x l IH]; intros n t d Ht.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct t as [|t]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma bytes_val_false : forall n bs, 1 <= n <= 8 ->
  bv_unsigned (bytes_val false n bs) = ext_Z false 0 n (bytes_le_to_Z bs)
  /\ 0 <= ext_Z false 0 n (bytes_le_to_Z bs) < two64
  /\ forall t, 0 <= t < n -> zbyte (ext_Z false 0 n (bytes_le_to_Z bs)) t = bv_unsigned (nth (Z.to_nat t) bs (Z_to_bv 8 0)).
Proof.
  intros n bs Hn. pose proof (ValP.ext_Z_range false 0 n (bytes_le_to_Z bs) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
  split; [|split; [exact R|]].
  - unfold bytes_val. apply Z_to_bv_small. exact R.
  - intros t Ht. rewrite zbyte_ext_Z by (pose proof (ValP.bytes_le_to_Z_nonneg bs); lia).
    rewrite Z.add_0_l. rewrite <- (Z2Nat.id t) at 1 by lia. apply zbyte_bytes_le_nth.
Qed.

Lemma w2Zs_key : forall o, w2Zs (W64 (negb (PrimInt63.ltb o bit62i)) o) = keyZ o.
Proof.
  intros o. unfold w2Zs, w2Z. cbn [wt wl]. pose proof (int_range o).
  destruct (keyZ_cases o) as [[R ->]|[R ->]]; destruct (ltbP o bit62i) as [L|L]; rewrite to_Z_bit62i in L; cbn [negb];
    unfold two63, two64 in *; lia.
Qed.

Section BG.
Variables (E : env) (k : int) (r : region).

Lemma bg_value_sound : forall o w bv, 1 <= to_Z w <= 8 ->
  bg_value segs k r o w = Some bv ->
  exists x, 0 <= x < two64 /\ den E bv = Z_to_bv 64 x /\
    forall t, 0 <= t < to_Z w -> exists b, bg_byte segs E k r (keyZ o + t) = Some b /\ zbyte x t = bv_unsigned b.
Proof.
  intros o w bv Hw H. unfold bg_value in H. unfold bg_byte.
  pose proof (int_range o) as Ro. rewrite two63_eq in Ro.
  destruct (rg_bg r) as [| | | |j shift].
  - discriminate.
  - injection H as <-. exists 0. split; [unfold two64; lia|]. split; [reflexivity|].
    intros t Ht. exists (Z_to_bv 8 0). split; [reflexivity|]. rewrite zbyte_high; [reflexivity| lia|].
    pose proof (Z.pow_pos_nonneg 2 (8 * t)). lia.
  - destruct (ltbP o bit62i) as [L|L]; [|discriminate]. rewrite to_Z_bit62i in L.
    destruct (img_bytes segs (to_Z o) (Z.to_nat (to_Z w))) as [bs|] eqn:IB; [|discriminate]. injection H as <-.
    destruct (img_bytes_spec _ _ _ IB) as [Len By].
    exists (bytes_le_to_Z bs). pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Len, Z2Nat.id in Bb by lia.
    assert (HP : 2 ^ (8 * to_Z w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    split; [unfold two64; lia|]. split.
    + cbn [den]. unfold wbv. rewrite bytes_to_w64_ok by lia. reflexivity.
    + intros t Ht. destruct (By (Z.to_nat t) ltac:(lia)) as [rest M]. rewrite Z2Nat.id in M by lia.
      exists (nth (Z.to_nat t) bs (Z_to_bv 8 0)). split.
      * unfold img_byte, rom_of. destruct (keyZ_cases o) as [[_ ->]|[? _]]; [|lia]. rewrite M. reflexivity.
      * rewrite <- (Z2Nat.id t) at 1 by lia. apply zbyte_bytes_le_nth.
  - injection H as <-. cbn [den]. rewrite w2Zs_key.
    destruct (bytes_val_false (to_Z w) (bg_bytes (eg E k) (keyZ o) (Z.to_nat (to_Z w))) Hw) as (D & R & By).
    exists (ext_Z false 0 (to_Z w) (bytes_le_to_Z (bg_bytes (eg E k) (keyZ o) (Z.to_nat (to_Z w))))).
    split; [exact R|]. split; [apply bv_eq; rewrite D, Z_to_bv_small by exact R; reflexivity|].
    intros t Ht. exists (eg E k (keyZ o + t)). split; [reflexivity|].
    rewrite By by lia. rewrite bg_bytes_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
  - destruct (ltbP o bit62i) as [L|L]; rewrite ?to_Z_bit62i in L; [|discriminate].
    destruct (lebP shift o) as [L2|L2]; [|discriminate].
    destruct (ltbP shift bit62i) as [L3|L3]; rewrite ?to_Z_bit62i in L3; [|discriminate].
    cbn [andb] in H. injection H as <-. cbn [den]. rewrite ValP.den_vlit.
    rewrite Z_to_bv_small by (pose proof (int_range (PrimInt63.sub o shift)); unfold two63, two64 in *; lia).
    rewrite sub_small by lia.
    set (L0 := blob_bytes (eb E j) (to_Z o - to_Z shift) (to_Z w)).
    destruct (bytes_val_false (to_Z w) L0 Hw) as (D & R & By).
    exists (ext_Z false 0 (to_Z w) (bytes_le_to_Z L0)).
    split; [exact R|]. split; [apply bv_eq; rewrite D, Z_to_bv_small by exact R; reflexivity|].
    intros t Ht. exists (nth (Z.to_nat t) L0 (Z_to_bv 8 0)). split; [| apply By; exact Ht].
    f_equal. subst L0. unfold blob_bytes. rewrite nth_firstn_lt by lia. rewrite nth_skipn. f_equal.
    destruct (keyZ_cases o) as [[_ ->]|[? _]]; [|lia]. lia.
Qed.
End BG.

Section Load.
Variables (priv : list (int * int)) (E : env) (m : word -> option byte) (k : int) (r : region).
Hypothesis Hz : ev E 0%uint63 = Z_to_bv 64 0.
Hypothesis RO : region_ok segs priv E m k r.

Definition validO (o : Z) : Prop :=
  (PrimInt63.eqb k 0%uint63 = false -> loZ r <= o < hiZ E r) /\
  (PrimInt63.eqb k 0%uint63 = true ->
     0 <= o < two63 / 2 /\ (exists bs, memory_read segs (Z_to_bv 64 o) 1 = Some bs) /\ ~ in_priv priv o).

Definition gran_of (g : int) : bool * slot :=
  match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end.

Lemma gran_of_slot_ok : forall g d s, gran_of g = (d, s) ->
  slot_ok segs E m (bv_unsigned (ev E k) + 8 * keyZ g) s.
Proof.
  intros g d s H. unfold gran_of in H.
  destruct (IMap.find g (rg_cells r)) as [[d' s']|] eqn:F.
  - injection H as <- <-. exact (ro_cells _ _ _ _ _ _ RO g _ F).
  - injection H as <- <-. apply slot_ok_nil.
Qed.

Lemma slot_ok_wf : forall base s, slot_ok segs E m base s -> csorted s /\ Forall cell_wf s.
Proof.
  intros base s [Ss Fc].
  assert (W : Forall cell_wf s).
  { eapply Forall_impl; [|exact Fc]. intros c (C1 & C2 & C3 & _). unfold cell_wf. lia. }
  split; [apply slot_sorted_csorted; assumption| exact W].
Qed.

Lemma cell_byte : forall g d s c j, gran_of g = (d, s) -> In c s -> ciZ c <= j < ceZ c ->
  rb segs m (bv_unsigned (ev E k) + 8 * keyZ g + j) = Some (byte_of (den E (c_v c)) (j - ciZ c)).
Proof.
  intros g d s c j Hg Hc Hj. destruct (gran_of_slot_ok g d s Hg) as [_ Fc].
  pose proof (proj1 (Forall_forall _ _) Fc c Hc) as (C1 & C2 & C3 & C4). unfold ciZ, ceZ in Hj.
  specialize (C4 (j - to_Z (c_idx c)) ltac:(lia)).
  replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + (j - to_Z (c_idx c)))
    with (bv_unsigned (ev E k) + 8 * keyZ g + j) in C4 by lia. exact C4.
Qed.

Lemma bg_byte_rb : forall g s j b, gran_of g = (false, s) -> 0 <= j < 8 ->
  Forall (fun c => ~ covers c j) s -> validO (8 * keyZ g + j) ->
  bg_byte segs E k r (8 * keyZ g + j) = Some b ->
  rb segs m (bv_unsigned (ev E k) + 8 * keyZ g + j) = Some b.
Proof.
  intros g s j b Hg Hj NC [V1 V2] Hb.
  pose proof (ro_bg _ _ _ _ _ _ RO (8 * keyZ g + j) V1 V2) as G.
  rewrite Hb, Z.add_assoc in G. apply G.
  intros g' gr Hk Hf.
  assert (Eg : g' = g).
  { apply keyZ_inj. rewrite Hk. symmetry. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  subst g'. unfold gran_of in Hg. rewrite Hf in Hg. destruct gr as [d' s']. injection Hg as -> ->. cbn [g_dirty g_cells].
  split; [reflexivity|].
  replace ((8 * keyZ g + j) mod 8) with j; [exact NC|].
  rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.

Lemma region_load1_sound : forall o w sx v,
  1 <= to_Z w -> to_Z (gidx o) + to_Z w <= 8 ->
  (forall t, 0 <= t < to_Z w -> validO (keyZ o + t)) ->
  region_load1 segs k r o w sx = Some v ->
  exists x, 0 <= x /\ den E v = Z_to_bv 64 (ext_Z sx 0 (to_Z w) x) /\
    forall t, 0 <= t < to_Z w ->
      exists b, rb segs m (bv_unsigned (ev E k) + keyZ o + t) = Some b /\ zbyte x t = bv_unsigned b.
Proof.
  intros o w sx v Hw Hiw VO H.
  destruct (granule_gidx o ltac:(rewrite half63; apply keyZ_range)) as [Eo Ri].
  set (g := granule o) in *. set (i := gidx o) in *.
  unfold Mem.region_load1 in H. fold g in H. fold i in H.
  destruct (gran_of g) as [d s] eqn:GD. unfold gran_of in GD.
  assert (HH : (let '(dirty, s) := match IMap.find g (rg_cells r) with Some (Gran d s) => (d, s) | None => (false, []) end in
           let bgv := if dirty then None else bg_value segs k r o w in
           match overlapping s i w with
           | [] => match bgv with Some v0 => Some (sv_ext sx 0%uint63 w v0) | None => None end
           | [c] => if (PrimInt63.leb (c_idx c) i && PrimInt63.leb (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c)))%bool
                    then Some (sv_ext sx (PrimInt63.sub i (c_idx c)) w (c_v c))
                    else match Mem.assemble bgv [c] i w with Some v0 => Some (sv_ext sx 0%uint63 w v0) | None => None end
           | cs => match Mem.assemble bgv cs i w with Some v0 => Some (sv_ext sx 0%uint63 w v0) | None => None end
           end) = Some v) by exact H.
  clear H. rewrite GD in HH. cbn beta iota zeta in HH.
  set (bgv := if d then None else bg_value segs k r o w) in HH.
  pose proof (gran_of_slot_ok g d s GD) as SOK. destruct (slot_ok_wf _ _ SOK) as [CS WF].
  pose proof (int_range i) as Rii. pose proof (int_range w) as Rw. rewrite two63_eq in Rii, Rw.
  destruct (overlapping_csorted s i w CS WF ltac:(lia)) as (OCS & OWF & OOV & OIN).

  assert (CB : forall c t, In c s -> 0 <= t < to_Z w -> ciZ c <= to_Z i + t < ceZ c ->
    exists b, rb segs m (bv_unsigned (ev E k) + keyZ o + t) = Some b /\
              zbyte (bv_unsigned (den E (c_v c))) (to_Z i + t - ciZ c) = bv_unsigned b).
  { intros c t Hc Ht Hcov. eexists. split.
    - rewrite Eo. replace (bv_unsigned (ev E k) + (8 * keyZ g + to_Z i) + t) with (bv_unsigned (ev E k) + 8 * keyZ g + (to_Z i + t)) by lia.
      apply (cell_byte g d s); [exact GD | exact Hc | exact Hcov].
    - rewrite byte_of_zbyte by lia. reflexivity. }
  assert (BB : forall bv t, bgv = Some bv -> 0 <= t < to_Z w -> cover (overlapping s i w) (to_Z i + t) = None ->
    exists x0, 0 <= x0 < two64 /\ den E bv = Z_to_bv 64 x0 /\
    exists b, rb segs m (bv_unsigned (ev E k) + keyZ o + t) = Some b /\ zbyte x0 t = bv_unsigned b).
  { intros bv t Hbv Ht Hcov. subst bgv. destruct d; [discriminate|].
    destruct (bg_value_sound E k r o w bv ltac:(lia) Hbv) as (x0 & R0 & D0 & BY).
    exists x0. split; [exact R0|]. split; [exact D0|].
    destruct (BY t Ht) as (b & Hb & Zb). exists b. split; [|exact Zb].
    rewrite Eo. replace (bv_unsigned (ev E k) + (8 * keyZ g + to_Z i) + t) with (bv_unsigned (ev E k) + 8 * keyZ g + (to_Z i + t)) by lia.
    apply (bg_byte_rb g s); [exact GD| lia | | | rewrite <- Hb; f_equal; lia].
    - apply (overlapping_uncovered s i w); try assumption; lia.
    - replace (8 * keyZ g + (to_Z i + t)) with (keyZ o + t) by lia. apply VO. exact Ht. }

  assert (GENERIC : forall u, overlapping s i w <> [] ->
    Mem.assemble bgv (overlapping s i w) i w = Some u -> v = sv_ext sx 0%uint63 w u ->
    exists x, 0 <= x /\ den E v = Z_to_bv 64 (ext_Z sx 0 (to_Z w) x) /\
      forall t, 0 <= t < to_Z w -> exists b, rb segs m (bv_unsigned (ev E k) + keyZ o + t) = Some b /\ zbyte x t = bv_unsigned b).
  { intros u NE AS ->. rewrite assemble_ago in AS.
    exists (bv_unsigned (den E u)). split; [apply bv_unsigned_in_range|]. split.
    - rewrite ValP.den_sv_ext by (unfold ValP.width_ok; change (to_Z 0) with 0; lia). unfold ext_word. change (to_Z 0) with 0. reflexivity.
    - intros t Ht. destruct bgv as [bv|] eqn:BGV.
      + destruct (ago_spec E i w ltac:(lia) ltac:(lia) _ i bv false u OCS OWF OOV ltac:(lia) AS) as [B1 _].
        specialize (B1 t Ht). unfold dbyte in B1.
        destruct (cover (overlapping s i w) (to_Z i + t)) as [c|] eqn:CV.
        * destruct (cover_In _ _ _ CV) as [Hc Hcov]. destruct (CB c t (OIN c Hc) Ht Hcov) as (b & Rb & Zb).
          exists b. rewrite B1. auto.
        * destruct (BB bv t eq_refl Ht CV) as (x0 & R0 & D0 & b & Rb & Zb).
          exists b. split; [exact Rb|]. rewrite B1, D0, Z_to_bv_small by exact R0. exact Zb.
      + destruct (ago_spec E i w ltac:(lia) ltac:(lia) _ i (VL wzero) true u OCS OWF OOV ltac:(lia) AS) as [B1 B2].
        specialize (B1 t Ht). unfold dbyte in B1.
        destruct (cover (overlapping s i w) (to_Z i + t)) as [c|] eqn:CV.
        * destruct (cover_In _ _ _ CV) as [Hc Hcov]. destruct (CB c t (OIN c Hc) Ht Hcov) as (b & Rb & Zb).
          exists b. rewrite B1. auto.
        * exfalso. apply (B2 eq_refl t); [lia| exact CV]. }
  destruct (overlapping s i w) as [|c [|c2 cs']] eqn:OV.
  -
    destruct bgv as [bv|] eqn:BGV; [|discriminate]. injection HH as <-.
    destruct (BB bv 0 eq_refl ltac:(lia) eq_refl) as (x0 & R0 & D0 & _).
    exists x0. split; [lia|]. split.
    + rewrite ValP.den_sv_ext by (unfold ValP.width_ok; change (to_Z 0) with 0; lia). unfold ext_word.
      rewrite D0, Z_to_bv_small by exact R0. change (to_Z 0) with 0. reflexivity.
    + intros t Ht. destruct (BB bv t eq_refl Ht eq_refl) as (x1 & R1 & D1 & b & Rb & Zb).
      exists b. split; [exact Rb|].
      assert (x1 = x0) as <-; [|exact Zb].
      rewrite <- (Z_to_bv_small x1), <- (Z_to_bv_small x0) by assumption. rewrite <- D0, <- D1. reflexivity.
  -
    destruct (PrimInt63.leb (c_idx c) i && PrimInt63.leb (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c)))%bool eqn:CT.
    + injection HH as <-. apply andb_prop in CT. destruct CT as [L1 L2].
      assert (Hc : In c s) by (apply OIN; left; reflexivity).
      pose proof (proj1 (Forall_forall _ _) WF c Hc) as Wc. unfold cell_wf in Wc.
      destruct (lebP (c_idx c) i) as [L1'|]; [|discriminate].
      destruct (lebP (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c))) as [L2'|]; [|discriminate].
      rewrite !add_small in L2' by (rewrite two63_eq; lia).
      pose proof (bv_unsigned_in_range 64 (den E (c_v c))) as Rc. rewrite bv_modulus_64 in Rc.
      exists (ext_Z false (to_Z i - to_Z (c_idx c)) (to_Z w) (bv_unsigned (den E (c_v c)))).
      split; [apply (ext_Z_false_range); lia|]. split.
      * rewrite ValP.den_sv_ext by (unfold ValP.width_ok; rewrite sub_small by lia; lia). unfold ext_word.
        rewrite sub_small by lia. rewrite <- ext_Z_compose0 by lia. reflexivity.
      * intros t Ht. destruct (CB c t Hc Ht ltac:(unfold ciZ, ceZ; lia)) as (b & Rb & Zb).
        exists b. split; [exact Rb|]. rewrite zbyte_ext_Z by lia. unfold ciZ in Zb. rewrite <- Zb. f_equal. lia.
    + destruct (Mem.assemble bgv [c] i w) as [u|] eqn:AS; [|discriminate]. injection HH as <-.
      apply (GENERIC u); [discriminate| first [exact AS | reflexivity] | reflexivity].
  - destruct (Mem.assemble bgv (c :: c2 :: cs') i w) as [u|] eqn:AS; [|discriminate]. injection HH as <-.
    apply (GENERIC u); [discriminate| first [exact AS | reflexivity] | reflexivity].
Qed.

Definition rbyte (A : Z) : byte := match rb segs m A with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint rbytes (A : Z) (n : nat) : list byte :=
  match n with O => [] | S n' => rbyte A :: rbytes (A + 1) n' end.

Lemma rbytes_length : forall A n, length (rbytes A n) = n.
Proof. intros A n. revert A. induction n; intros A; cbn; [reflexivity| rewrite IHn; reflexivity]. Qed.

Lemma rbytes_nth_error : forall n A t, (t < n)%nat -> nth_error (rbytes A n) t = Some (rbyte (A + Z.of_nat t)).
Proof.
  induction n as [|n IH]; intros A t Ht; [lia|]. cbn [rbytes]. destruct t as [|t].
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma rbytes_nth : forall n A t d, (t < n)%nat -> nth t (rbytes A n) d = rbyte (A + Z.of_nat t).
Proof.
  intros n A t d Ht. apply nth_error_nth. apply rbytes_nth_error. exact Ht.
Qed.

Lemma load_finish : forall A w sx v x,
  0 <= A -> A + to_Z w <= two64 -> 1 <= to_Z w <= 8 -> 0 <= x ->
  den E v = Z_to_bv 64 (ext_Z sx 0 (to_Z w) x) ->
  (forall t, 0 <= t < to_Z w -> exists b, rb segs m (A + t) = Some b /\ zbyte x t = bv_unsigned b) ->
  exists bs, length bs = Z.to_nat (to_Z w)
    /\ ov_read_bytes segs m (Z_to_bv 64 A) (Z.to_nat (to_Z w)) = Some bs
    /\ den E v = bytes_val sx (to_Z w) bs.
Proof.
  intros A w sx v x HA HAw Hw Hx Dv BY.
  exists (rbytes A (Z.to_nat (to_Z w))). split; [apply rbytes_length|]. split.
  - apply ov_read_bytes_rb; [lia| rewrite Z2Nat.id; lia | | apply rbytes_length].
    intros t Ht. rewrite rbytes_nth_error by lia. rewrite Z2Nat.id by lia. unfold rbyte.
    destruct (BY t ltac:(lia)) as (b & -> & _). reflexivity.
  - rewrite Dv. unfold bytes_val. f_equal. apply ext_Z_mod. apply zbytes_eq; [lia|].
    intros t Ht. rewrite <- (Z2Nat.id t) at 2 by lia. rewrite zbyte_bytes_le_nth, rbytes_nth, Z2Nat.id by lia.
    unfold rbyte. destruct (BY t Ht) as (b & -> & Zb). exact Zb.
Qed.

Lemma keyZ_add_le : forall key w w1, 0 <= to_Z w1 <= to_Z w -> to_Z w <= 8 ->
  keyZ (PrimInt63.add key w) = keyZ key + to_Z w -> keyZ (PrimInt63.add key w1) = keyZ key + to_Z w1.
Proof.
  intros key w w1 Hw1 Hw EE.
  pose proof (int_range key). pose proof (int_range w). pose proof (int_range w1). rewrite two63_eq in *.
  revert EE.
  destruct (keyZ_cases (PrimInt63.add key w)) as [[R1 ->]|[R1 ->]];
  destruct (keyZ_cases (PrimInt63.add key w1)) as [[R2 ->]|[R2 ->]];
  rewrite !add_spec, !wB_two63, !two63_eq in *;
  destruct (keyZ_cases key) as [[R' ->]|[R' ->]];
  rewrite !(mod_cases2 _ (2 ^ 63)) in * by lia;
  destruct (Z.ltb_spec (to_Z key + to_Z w) (2 ^ 63)); destruct (Z.ltb_spec (to_Z key + to_Z w1) (2 ^ 63)); lia.
Qed.

Lemma region_load_sound0 : forall fs key w sx v,
  facts_hold E fs -> wok w ->
  can_read segs fs priv k r key w = true ->
  Mem.region_load segs k r key w sx = Some v ->
  exists bs, length bs = Z.to_nat (to_Z w)
    /\ ov_read_bytes segs m (Z_to_bv 64 (addrZ E k key)) (Z.to_nat (to_Z w)) = Some bs
    /\ den E v = bytes_val sx (to_Z w) bs.
Proof.
  intros fs key w sx v Hfs Hw CR H.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  pose proof (can_read_sound priv E m fs k r key w Hfs Hz RO Hw CR) as (RA & RAw & RB & RNG & ABS).
  unfold addrZ in *.
  pose proof (int_range key) as Rk. pose proof (int_range w) as Rw. rewrite two63_eq in Rk, Rw.

  assert (NW : keyZ (PrimInt63.add key w) = keyZ key + to_Z w).
  { unfold can_read in CR. destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    - apply andb_prop in CR. destruct CR as [CR _]. apply andb_prop in CR. destruct CR as [L AR].
      destruct (ltbP key bit62i) as [L'|]; [|discriminate]. rewrite to_Z_bit62i in L'.
      destruct (abs_readable_sound (to_Z key) (to_Z w) ltac:(lia) AR) as [B62 _].
      destruct (keyZ_cases key) as [[_ ->]|[? _]]; [|lia].
      destruct (keyZ_cases (PrimInt63.add key w)) as [[? ->]|[X _]]; rewrite add_small in * by (rewrite two63_eq; lia); lia.
    - apply andb_prop in CR. destruct CR as [CR _]. apply andb_prop in CR. destruct CR as [_ NW].
      apply keyZ_add_nowrap; [lia| exact NW]. }
  assert (VO : forall t, 0 <= t < to_Z w -> validO (keyZ key + t)).
  { intros t Ht. split; [intros K; apply (RNG K); exact Ht|]. intros K. rewrite half63.
    destruct (ABS K t Ht) as [M P]. pose proof (eqb_correct _ _ K) as ->. rewrite (ev0_zero E Hz), Z.add_0_l in *.
    split; [| split; assumption].
    unfold can_read in CR. change (PrimInt63.eqb 0 0) with true in CR. cbn iota in CR.
    apply andb_prop in CR. destruct CR as [CR _]. apply andb_prop in CR. destruct CR as [L AR].
    destruct (ltbP key bit62i) as [L'|]; [|discriminate]. rewrite to_Z_bit62i in L'.
    destruct (abs_readable_sound (to_Z key) (to_Z w) ltac:(lia) AR) as [B62 _]. destruct (keyZ_cases key) as [[_ ->]|[? _]]; lia. }
  destruct (granule_gidx key ltac:(rewrite half63; apply keyZ_range)) as [Eo Ri].
  unfold Mem.region_load in H. unfold in_granule in H.
  destruct (lebP (PrimInt63.add (gidx key) w) 8) as [IG|IG]; rewrite add_small in IG by (rewrite two63_eq; lia);
    change (to_Z 8) with 8 in IG.
  - destruct (region_load1_sound key w sx v ltac:(lia) IG VO H) as (x & Hx & Dv & BY).
    apply (load_finish _ w sx v x); try assumption; lia.
  - set (w1 := PrimInt63.sub 8 (gidx key)) in H. set (w2 := PrimInt63.sub w w1) in H.
    assert (Ew1 : to_Z w1 = 8 - to_Z (gidx key)) by (subst w1; rewrite sub_small; change (to_Z 8) with 8; lia).
    assert (Ew2 : to_Z w2 = to_Z w - to_Z w1) by (subst w2; rewrite sub_small; lia).
    pose proof (keyZ_add_le key w w1 ltac:(lia) ltac:(lia) NW) as K2.
    destruct (granule_gidx (PrimInt63.add key w1) ltac:(rewrite half63; apply keyZ_range)) as [Eo2 Ri2].
    assert (G2 : to_Z (gidx (PrimInt63.add key w1)) = 0).
    { pose proof (Z.div_mod (keyZ key + to_Z w1) 8 ltac:(lia)) as DM.
      assert (E1 : (keyZ key + to_Z w1) mod 8 = 0).
      { rewrite Eo, Ew1. replace (8 * keyZ (granule key) + to_Z (gidx key) + (8 - to_Z (gidx key))) with ((keyZ (granule key) + 1) * 8) by lia.
        apply Z.mod_mul. lia. }
      assert (E2 : (keyZ key + to_Z w1) mod 8 = to_Z (gidx (PrimInt63.add key w1))).
      { rewrite <- K2, Eo2. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
      lia. }
    destruct (Mem.region_load1 segs k r key w1 false) as [lo|] eqn:L1; [|discriminate].
    destruct (Mem.region_load1 segs k r (PrimInt63.add key w1) w2 false) as [hi|] eqn:L2; [|discriminate].
    injection H as <-.
    destruct (region_load1_sound key w1 false lo ltac:(lia) ltac:(lia) ltac:(intros t Ht; apply VO; lia) L1) as (x1 & Hx1 & D1 & BY1).
    destruct (region_load1_sound (PrimInt63.add key w1) w2 false hi ltac:(lia) ltac:(lia)
                ltac:(intros t Ht; rewrite K2, <- Z.add_assoc; apply VO; lia) L2) as (x2 & Hx2 & D2 & BY2).
    set (u1 := ext_Z false 0 (to_Z w1) x1) in D1. set (u2 := ext_Z false 0 (to_Z w2) x2) in D2.
    pose proof (ext_Z_false_range 0 (to_Z w1) x1 ltac:(lia)) as Ru1. fold u1 in Ru1.
    pose proof (ext_Z_false_range 0 (to_Z w2) x2 ltac:(lia)) as Ru2. fold u2 in Ru2.
    assert (HP1 : 2 ^ (8 * to_Z w1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    assert (HP2 : 2 ^ (8 * to_Z w2) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    pose proof (ValP.ins_Z_range (to_Z w1) (to_Z w2) u1 u2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold two64; lia)) as Rx.
    apply (load_finish _ w sx _ (ins_Z (to_Z w1) (to_Z w2) u1 u2)); try lia.
    + rewrite ValP.den_sv_ext by (unfold ValP.width_ok; change (to_Z 0) with 0; lia).
      rewrite ValP.den_sv_ins by (unfold ValP.width_ok; lia).
      rewrite D1, D2, !Z_to_bv_small by (unfold two64; lia). unfold ext_word. rewrite Z_to_bv_small by exact Rx.
      change (to_Z 0) with 0. reflexivity.
    + intros t Ht. destruct (Z.lt_ge_cases t (to_Z w1)) as [T|T].
      * destruct (BY1 t ltac:(lia)) as (b & Rb & Zb). exists b. split; [exact Rb|].
        unfold zbyte. rewrite ValP.ins_Z_byte_out by (unfold two64; lia). fold (zbyte u1 t). subst u1.
        rewrite zbyte_ext_Z by lia. rewrite Z.add_0_l. exact Zb.
      * destruct (BY2 (t - to_Z w1) ltac:(lia)) as (b & Rb & Zb). exists b. split.
        -- rewrite K2 in Rb. rewrite <- Rb. f_equal. lia.
        -- unfold zbyte. rewrite ValP.ins_Z_byte_in by lia. fold (zbyte u2 (t - to_Z w1)). subst u2.
           rewrite zbyte_ext_Z by lia. rewrite Z.add_0_l. exact Zb.
Qed.
End Load.

Section Cut.
Variable E : env.
Variables i w : int.
Hypothesis Hi : 0 <= to_Z i.
Hypothesis Hw : 1 <= to_Z w.
Hypothesis Hiw : to_Z i + to_Z w <= 8.
Let e : Z := to_Z i + to_Z w.

Definition piece (c c' : cell) : Prop :=
  (c' = c /\ (ceZ c <= to_Z i \/ e <= ciZ c))
  \/ (ciZ c < to_Z i /\ to_Z i < ceZ c /\
      c' = Cell (c_idx c) (PrimInt63.sub i (c_idx c)) (sv_ext false 0%uint63 (PrimInt63.sub i (c_idx c)) (c_v c)))
  \/ (e < ceZ c /\ ciZ c < e /\
      c' = Cell (PrimInt63.add i w) (PrimInt63.sub (PrimInt63.add (c_idx c) (c_w c)) (PrimInt63.add i w))
                (sv_ext false (PrimInt63.sub (PrimInt63.add i w) (c_idx c))
                              (PrimInt63.sub (PrimInt63.add (c_idx c) (c_w c)) (PrimInt63.add i w)) (c_v c))).

Lemma piece_props : forall c c', cell_wf c -> piece c c' ->
  cell_wf c' /\ ciZ c <= ciZ c' /\ ceZ c' <= ceZ c /\ (ceZ c' <= to_Z i \/ e <= ciZ c')
  /\ (forall j, ciZ c' <= j < ceZ c' -> dbyte E (c_v c') (j - ciZ c') = dbyte E (c_v c) (j - ciZ c)).
Proof.
  intros c c' Wc P. unfold cell_wf in Wc.
  pose proof (int_range i) as Ri. pose proof (int_range w) as Rw. rewrite two63_eq in Ri, Rw.
  pose proof (bv_unsigned_in_range 64 (den E (c_v c))) as Rc. rewrite bv_modulus_64 in Rc.
  destruct P as [[-> A]|[(A1 & A2 & ->)|(A1 & A2 & ->)]].
  - split; [unfold cell_wf; lia|]. split; [lia|]. split; [lia|]. split; [exact A|]. intros; reflexivity.
  - unfold ciZ, ceZ in A1, A2. unfold cell_wf, ciZ, ceZ. cbn [c_idx c_w c_v].
    assert (Es : to_Z (PrimInt63.sub i (c_idx c)) = to_Z i - to_Z (c_idx c)) by (apply sub_small; lia).
    rewrite Es. repeat split; try lia. intros j Hj. unfold dbyte.
    rewrite ValP.den_sv_ext by (unfold ValP.width_ok; change (to_Z 0) with 0; rewrite Es; lia).
    unfold ext_word. rewrite Es. change (to_Z 0) with 0.
    rewrite Z_to_bv_small by (apply ValP.ext_Z_range; lia). rewrite zbyte_ext_Z by lia. f_equal.
  - unfold ciZ, ceZ, e in A1, A2. unfold cell_wf, ciZ, ceZ. cbn [c_idx c_w c_v].
    assert (Ea : to_Z (PrimInt63.add i w) = to_Z i + to_Z w) by (apply add_small; rewrite two63_eq; lia).
    assert (Ec : to_Z (PrimInt63.add (c_idx c) (c_w c)) = to_Z (c_idx c) + to_Z (c_w c)) by (apply add_small; rewrite two63_eq; lia).
    assert (Es1 : to_Z (PrimInt63.sub (PrimInt63.add (c_idx c) (c_w c)) (PrimInt63.add i w)) = to_Z (c_idx c) + to_Z (c_w c) - (to_Z i + to_Z w))
      by (rewrite sub_small by (rewrite Ea, Ec; lia); lia).
    assert (Es2 : to_Z (PrimInt63.sub (PrimInt63.add i w) (c_idx c)) = to_Z i + to_Z w - to_Z (c_idx c))
      by (rewrite sub_small by (rewrite Ea; lia); lia).
    rewrite Ea, Es1. unfold e. repeat split; try lia. intros j Hj. unfold dbyte.
    rewrite ValP.den_sv_ext by (unfold ValP.width_ok; rewrite Es1, Es2; lia).
    unfold ext_word. rewrite Es1, Es2.
    rewrite Z_to_bv_small by (apply ValP.ext_Z_range; lia). rewrite zbyte_ext_Z by lia. f_equal. lia.
Qed.

Lemma cut_cons : forall c s,
  cut (c :: s) i w =
  (let ci := c_idx c in let cw := c_w c in
   let ce := PrimInt63.add ci cw in
   let e' := PrimInt63.add i w in
   if PrimInt63.leb ce i then c :: cut s i w
   else if PrimInt63.leb e' ci then c :: s
   else
     (if PrimInt63.ltb ci i then [Cell ci (PrimInt63.sub i ci) (sv_ext false 0%uint63 (PrimInt63.sub i ci) (c_v c))] else [])
     ++ (if PrimInt63.ltb e' ce then [Cell e' (PrimInt63.sub ce e') (sv_ext false (PrimInt63.sub e' ci) (PrimInt63.sub ce e') (c_v c))] else [])
     ++ cut s i w).
Proof. reflexivity. Qed.

Lemma cut_In : forall s c', csorted s -> Forall cell_wf s -> In c' (cut s i w) -> exists c, In c s /\ piece c c'.
Proof.
  pose proof (int_range i) as Ri. pose proof (int_range w) as Rw. rewrite two63_eq in Ri, Rw.
  induction s as [|c s IH]; intros c' S W H; [destruct H|].
  inversion S as [|x l S' Fc]; subst. inversion W as [|x l Wc W']; subst.
  pose proof Wc as Wc'. unfold cell_wf in Wc.
  rewrite cut_cons in H. cbv zeta in H.
  destruct (lebP (PrimInt63.add (c_idx c) (c_w c)) i) as [L|L]; rewrite add_small in L by (rewrite two63_eq; lia).
  - destruct H as [<-|H].
    + exists c. split; [left; reflexivity|]. left. split; [reflexivity|]. left. unfold ceZ. lia.
    + destruct (IH c' S' W' H) as [c0 [Hc0 P]]. exists c0. split; [right; exact Hc0| exact P].
  - destruct (lebP (PrimInt63.add i w) (c_idx c)) as [L2|L2]; rewrite add_small in L2 by (rewrite two63_eq; lia).
    + destruct H as [<-|H].
      * exists c. split; [left; reflexivity|]. left. split; [reflexivity|]. right. unfold ciZ, e. lia.
      * exists c'. split; [right; exact H|]. left. split; [reflexivity|]. right.
        pose proof (proj1 (Forall_forall _ _) Fc c' H) as P. unfold ceZ, ciZ, e in *. lia.
    + apply in_app_iff in H. destruct H as [H|H]; [|apply in_app_iff in H; destruct H as [H|H]].
      * destruct (ltbP (c_idx c) i) as [L3|L3]; [|destruct H]. destruct H as [<-|[]].
        exists c. split; [left; reflexivity|]. right. left. unfold ciZ, ceZ. split; [lia|]. split; [lia|]. reflexivity.
      * destruct (ltbP (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c))) as [L3|L3]; [|destruct H].
        rewrite !add_small in L3 by (rewrite two63_eq; lia). destruct H as [<-|[]].
        exists c. split; [left; reflexivity|]. right. right. unfold ciZ, ceZ, e. split; [lia|]. split; [lia|]. reflexivity.
      * destruct (IH c' S' W' H) as [c0 [Hc0 P]]. exists c0. split; [right; exact Hc0| exact P].
Qed.

Lemma cut_covers : forall s c j, csorted s -> Forall cell_wf s -> In c s -> ciZ c <= j < ceZ c ->
  ~ (to_Z i <= j < e) -> exists c', In c' (cut s i w) /\ ciZ c' <= j < ceZ c'.
Proof.
  pose proof (int_range i) as Ri. pose proof (int_range w) as Rw. rewrite two63_eq in Ri, Rw.
  induction s as [|c0 s IH]; intros c j S W Hc Hj Hnj; [destruct Hc|].
  inversion S as [|x l S' Fc]; subst. inversion W as [|x l Wc W']; subst. unfold cell_wf in Wc.
  rewrite cut_cons. cbv zeta.
  destruct (lebP (PrimInt63.add (c_idx c0) (c_w c0)) i) as [L|L]; rewrite add_small in L by (rewrite two63_eq; lia).
  - destruct Hc as [->|Hc].
    + exists c. split; [left; reflexivity| exact Hj].
    + destruct (IH c j S' W' Hc Hj Hnj) as [c' [H1 H2]]. exists c'. split; [right; exact H1| exact H2].
  - destruct (lebP (PrimInt63.add i w) (c_idx c0)) as [L2|L2]; rewrite add_small in L2 by (rewrite two63_eq; lia).
    + exists c. split; [exact Hc| exact Hj].
    + destruct Hc as [->|Hc].
      * unfold ciZ, ceZ, e in *.
        destruct (Z.lt_ge_cases j (to_Z i)) as [J|J].
        -- destruct (ltbP (c_idx c) i) as [L3|L3]; [|lia].
           eexists. split; [apply in_app_iff; left; left; reflexivity|]. cbn [c_idx c_w]. rewrite sub_small by lia. lia.
        -- destruct (ltbP (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c))) as [L3|L3];
             rewrite !add_small in L3 by (rewrite two63_eq; lia); [|lia].
           eexists. split; [apply in_app_iff; right; apply in_app_iff; left; left; reflexivity|]. cbn [c_idx c_w].
           rewrite sub_small by (rewrite !add_small by (rewrite two63_eq; lia); lia).
           rewrite !add_small by (rewrite two63_eq; lia). lia.
      * destruct (IH c j S' W' Hc Hj Hnj) as [c' [H1 H2]]. exists c'.
        split; [apply in_app_iff; right; apply in_app_iff; right; exact H1| exact H2].
Qed.

Lemma cut_sorted : forall s, csorted s -> Forall cell_wf s ->
  csorted (cut s i w) /\ Forall cell_wf (cut s i w) /\ Forall (fun c' => ceZ c' <= to_Z i \/ e <= ciZ c') (cut s i w).
Proof.
  pose proof (int_range i) as Ri. pose proof (int_range w) as Rw. rewrite two63_eq in Ri, Rw.
  induction s as [|c s IH]; intros S W; [repeat split; constructor|].
  inversion S as [|x l S' Fc]; subst. inversion W as [|x l Wc W']; subst. pose proof Wc as Wc0. unfold cell_wf in Wc.
  destruct (IH S' W') as (CS & CW & CA).

  assert (AFTER : Forall (fun c' => ceZ c <= ciZ c') (cut s i w)).
  { apply Forall_forall. intros c' H'. destruct (cut_In s c' S' W' H') as [c0 [Hc0 P]].
    destruct (piece_props c0 c' (proj1 (Forall_forall _ _) W' c0 Hc0) P) as (_ & X & _).
    assert (ceZ c <= ciZ c0) by exact (proj1 (Forall_forall _ _) Fc c0 Hc0). lia. }
  rewrite cut_cons. cbv zeta.
  destruct (lebP (PrimInt63.add (c_idx c) (c_w c)) i) as [L|L]; rewrite add_small in L by (rewrite two63_eq; lia).
  - split; [constructor; assumption|]. split; [constructor; assumption|]. constructor; [left; unfold ceZ; lia| exact CA].
  - destruct (lebP (PrimInt63.add i w) (c_idx c)) as [L2|L2]; rewrite add_small in L2 by (rewrite two63_eq; lia).
    + split; [exact S|]. split; [exact W|]. constructor; [right; unfold ciZ, e; lia|].
      eapply Forall_impl; [|exact Fc]. intros c' H'. cbv beta in H'. right. unfold ceZ, ciZ, e in *. lia.
    + set (left := if PrimInt63.ltb (c_idx c) i then _ else _).
      set (right := if PrimInt63.ltb (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c)) then _ else _).
      assert (PL : forall c', In c' left -> piece c c' /\ ceZ c' <= to_Z i).
      { intros c' H'. subst left. destruct (ltbP (c_idx c) i) as [L3|L3]; [|destruct H']. destruct H' as [<-|[]].
        split; [right; left; unfold ciZ, ceZ; repeat split; lia || reflexivity|].
        unfold ceZ. cbn [c_idx c_w]. rewrite sub_small by lia. lia. }
      assert (PR : forall c', In c' right -> piece c c' /\ e <= ciZ c').
      { intros c' H'. subst right.
        destruct (ltbP (PrimInt63.add i w) (PrimInt63.add (c_idx c) (c_w c))) as [L3|L3]; [|destruct H'].
        rewrite !add_small in L3 by (rewrite two63_eq; lia). destruct H' as [<-|[]].
        split; [right; right; unfold ciZ, ceZ, e; repeat split; lia || reflexivity|].
        unfold ciZ, e. cbn [c_idx]. rewrite add_small by (rewrite two63_eq; lia). lia. }
      assert (WL : forall c', In c' (left ++ right) -> cell_wf c' /\ ciZ c <= ciZ c' /\ ceZ c' <= ceZ c /\ (ceZ c' <= to_Z i \/ e <= ciZ c')).
      { intros c' H'. apply in_app_iff in H'.
        destruct H' as [H'|H']; [destruct (PL c' H') as [P _]| destruct (PR c' H') as [P _]];
          destruct (piece_props c c' Wc0 P) as (A1 & A2 & A3 & A4 & _); auto. }
      rewrite app_assoc. split; [|split].
      *
        assert (LR : forall a b, In a left -> In b right -> ceZ a <= ciZ b).
        { intros a b Ha Hb. destruct (PL a Ha) as [_ X]. destruct (PR b Hb) as [_ Y]. unfold e in Y. lia. }
        assert (SLR : csorted (left ++ right)).
        { subst left right. destruct (PrimInt63.ltb (c_idx c) i); destruct (PrimInt63.ltb _ _); cbn [app];
            repeat constructor.
          apply LR; cbn; auto. }
        unfold csorted. clear IH.
        induction (left ++ right) as [|a l IHl]; [exact CS|]. cbn [app].
        inversion SLR as [|y l' S1 F1]; subst. constructor.
        -- apply IHl; [intros c' H'; apply WL; right; exact H'| exact S1].
        -- apply Forall_app. split; [exact F1|].
           destruct (WL a ltac:(left; reflexivity)) as (_ & _ & A3 & _).
           eapply Forall_impl; [|exact AFTER]. intros b Hb. cbv beta in Hb. lia.
      * apply Forall_app. split; [|exact CW]. apply Forall_forall. intros c' H'. apply WL. exact H'.
      * apply Forall_app. split; [|exact CA]. apply Forall_forall. intros c' H'. apply WL. exact H'.
Qed.

Lemma insert_sorted_In : forall c s x, In x (insert_sorted c s) <-> x = c \/ In x s.
Proof.
  intros c s x. induction s as [|c' s IH]; cbn [insert_sorted In].
  - intuition (subst; auto).
  - destruct (PrimInt63.ltb (c_idx c) (c_idx c')); cbn [In]; rewrite ?IH; intuition (subst; auto).
Qed.

Lemma insert_sorted_csorted : forall c s, cell_wf c -> csorted s -> Forall cell_wf s ->
  Forall (fun c' => ceZ c' <= ciZ c \/ ceZ c <= ciZ c') s -> csorted (insert_sorted c s).
Proof.
  intros c s Wc. unfold cell_wf in Wc. induction s as [|c' s IH]; intros S W A.
  - cbn. repeat constructor.
  - inversion S as [|x l S' Fc]; subst. inversion W as [|x l Wc' W']; subst. inversion A as [|x l Ac A']; subst.
    unfold cell_wf in Wc'. cbn [insert_sorted].
    destruct (ltbP (c_idx c) (c_idx c')) as [L|L].
    + constructor; [exact S|]. constructor; [unfold ceZ, ciZ in *; lia|].
      eapply Forall_impl; [|exact Fc]. intros b Hb. cbv beta in Hb. unfold ceZ, ciZ in *. lia.
    + constructor; [apply IH; assumption|].
      apply Forall_forall. intros y Hy. apply insert_sorted_In in Hy. destruct Hy as [->|Hy].
      * unfold ceZ, ciZ in *. lia.
      * exact (proj1 (Forall_forall _ _) Fc y Hy).
Qed.

Lemma csorted_slot_sorted : forall s, csorted s -> slot_sorted s.
Proof.
  induction s as [|c s IH]; intros S; [exact I|].
  inversion S as [|x l S' Fc]; subst. cbn [slot_sorted]. split; [|apply IH; exact S'].
  destruct s as [|c' s']; [exact I|]. inversion Fc as [|y l F1 F2]; subst. unfold ceZ, ciZ in F1. exact F1.
Qed.
End Cut.

Lemma Z_to_le_bytes_nth : forall n z t d, (t < n)%nat ->
  nth t (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat t)).
Proof.
  induction n as [|n IH]; intros z t d Ht; [lia|]. cbn [Z_to_le_bytes]. destruct t as [|t].
  - cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma store_bytes_length : forall w x, length (store_bytes w x) = Z.to_nat (to_Z w).
Proof. intros. unfold store_bytes. apply length_Z_to_le_bytes. Qed.

Lemma store_bytes_nth_error : forall w x t, 0 <= t < to_Z w ->
  nth_error (store_bytes w x) (Z.to_nat t) = Some (byte_of x t).
Proof.
  intros w x t Ht. unfold store_bytes.
  rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_Z_to_le_bytes; lia).
  rewrite Z_to_le_bytes_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_app : forall n1 n2 z,
  Z_to_le_bytes (n1 + n2) z = Z_to_le_bytes n1 z ++ Z_to_le_bytes n2 (Z.shiftr z (8 * Z.of_nat n1)).
Proof.
  induction n1 as [|n1 IH]; intros n2 z.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite IH. rewrite Z.shiftr_shiftr by lia. repeat f_equal. lia.
Qed.

Lemma Z_to_le_bytes_ext : forall n a b, (forall t, 0 <= t < Z.of_nat n -> zbyte a t = zbyte b t) ->
  Z_to_le_bytes n a = Z_to_le_bytes n b.
Proof.
  intros n a b H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite !length_Z_to_le_bytes; reflexivity|].
  intros t Ht. rewrite length_Z_to_le_bytes in Ht. rewrite !Z_to_le_bytes_nth by exact Ht.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite !Z.shiftr_div_pow2 by lia. apply (H (Z.of_nat t)). lia.
Qed.

Lemma write_to_mem_app : forall l1 l2 m A,
  write_to_mem m (Z_to_bv 64 A) (l1 ++ l2) = write_to_mem (write_to_mem m (Z_to_bv 64 A) l1) (Z_to_bv 64 (A + Z.of_nat (length l1))) l2.
Proof.
  induction l1 as [|b l1 IH]; intros l2 m A.
  - cbn [app write_to_mem length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [app write_to_mem length]. rewrite Z_to_bv_succ, IH. do 2 f_equal. lia.
Qed.

Section Store.
Variables (priv : list (int * int)) (E : env) (k : int).
Hypothesis Hz : ev E 0%uint63 = Z_to_bv 64 0.

Definition validW (r : region) (o : Z) : Prop :=
  (PrimInt63.eqb k 0%uint63 = false -> loZ r <= o < hiZ E r) /\
  (PrimInt63.eqb k 0%uint63 = true ->
     0 <= o < two63 / 2 /\ (exists seg, find_segment segs o 1 = Some seg) /\ ~ in_priv priv o).

Lemma validW_addr : forall m r o, region_ok segs priv E m k r -> validW r o ->
  0 <= bv_unsigned (ev E k) + o < two64.
Proof.
  intros m r o RO [V1 V2]. destruct (PrimInt63.eqb k 0%uint63) eqn:K.
  - destruct (V2 eq_refl) as (R & _). pose proof (eqb_correct _ _ K) as ->. rewrite (ev0_zero E Hz).
    rewrite half63 in R. unfold two64. lia.
  - pose proof (V1 eq_refl). pose proof (ro_range _ _ _ _ _ _ RO K). lia.
Qed.

Lemma region_store1_sound : forall m r o w v,
  region_ok segs priv E m k r ->
  1 <= to_Z w -> to_Z (gidx o) + to_Z w <= 8 ->
  (forall t, 0 <= t < to_Z w -> validW r (keyZ o + t)) ->
  let A := bv_unsigned (ev E k) + keyZ o in
  let m' := write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v)) in
  region_ok segs priv E m' k (Mem.region_store1 r o w v)
  /\ (forall a, 0 <= a < two64 -> ~ (A <= a < A + to_Z w) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
Proof.
  intros m r o w v RO Hw Hiw VW. cbv zeta.
  set (A := bv_unsigned (ev E k) + keyZ o). set (m' := write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v))).
  pose proof (validW_addr m r _ RO (VW 0 ltac:(lia))) as RA0. rewrite Z.add_0_r in RA0. fold A in RA0.
  pose proof (validW_addr m r _ RO (VW (to_Z w - 1) ltac:(lia))) as RA1.
  assert (RA : 0 <= A /\ A + to_Z w <= two64) by (subst A; lia). clear RA0 RA1.
  assert (FR : forall a, 0 <= a < two64 -> ~ (A <= a < A + to_Z w) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha Hna. subst m'. apply write_to_mem_frame; rewrite ?store_bytes_length, ?Z2Nat.id; lia. }
  assert (WR : forall t, 0 <= t < to_Z w -> m' (Z_to_bv 64 (A + t)) = Some (byte_of (den E v) t)).
  { intros t Ht. subst m'. rewrite write_to_mem_in by (rewrite ?store_bytes_length, ?Z2Nat.id; lia).
    apply store_bytes_nth_error. exact Ht. }
  split; [|exact FR].
  assert (RBW : forall t, 0 <= t < to_Z w -> rb segs m' (A + t) = Some (byte_of (den E v) t)).
  { intros t Ht. rewrite rb_unfold, WR by exact Ht. reflexivity. }
  assert (RBF : forall a, 0 <= a < two64 -> ~ (A <= a < A + to_Z w) -> rb segs m' a = rb segs m a).
  { intros a Ha Hna. apply rb_ext. apply FR; assumption. }
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  destruct (granule_gidx o ltac:(rewrite half63; apply keyZ_range)) as [Eo Ri].
  pose proof (int_range w) as Rw. rewrite two63_eq in Rw.
  unfold Mem.region_store1.
  destruct (gran_of r (granule o)) as [d s] eqn:GD.
  pose proof (gran_of_slot_ok priv E m k r (RegionOk _ _ _ _ _ _ Rbst Rrange Rvalid Rcells Rin Rbg) _ _ _ GD) as SOK.
  destruct (slot_ok_wf _ _ _ _ SOK) as [CS WF].
  unfold gran_of in GD. rewrite GD. cbn beta iota.
  set (g := granule o) in *. set (i := gidx o) in *.
  set (newc := Cell i w v). set (s' := slot_store s i w v).
  destruct (cut_sorted E i w ltac:(lia) ltac:(lia) s CS WF) as (CS' & WF' & AV').
  assert (Wn : cell_wf newc). { unfold cell_wf, newc; cbn [c_idx c_w]. lia. }
  assert (INs' : forall x, In x s' <-> x = newc \/ In x (cut s i w)) by (intros x; unfold s', slot_store; apply insert_sorted_In).

  assert (OLD : forall g1 gr1 c j, IMap.find g1 (rg_cells r) = Some gr1 -> In c (g_cells gr1) -> ciZ c <= j < ceZ c ->
            (g1 = g -> ~ (to_Z i <= j < to_Z i + to_Z w)) ->
            0 <= bv_unsigned (ev E k) + 8 * keyZ g1 + j < two64 /\
            ~ (A <= bv_unsigned (ev E k) + 8 * keyZ g1 + j < A + to_Z w)).
  { intros g1 gr1 c j Hf Hc Hj Hg1.
    pose proof (Rin g1 gr1 c (j - ciZ c) Hf Hc ltac:(unfold ciZ, ceZ in *; lia)) as [P1 P2]. cbv zeta in P1, P2.
    unfold ciZ in P1, P2.
    replace (8 * keyZ g1 + to_Z (c_idx c) + (j - to_Z (c_idx c))) with (8 * keyZ g1 + j) in P1, P2 by lia.
    split.
    - destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      + destruct (P2 eq_refl) as (Q & _). rewrite half63 in Q. pose proof (eqb_correct _ _ K) as ->.
        rewrite (ev0_zero E Hz). unfold two64. lia.
      + pose proof (P1 eq_refl). pose proof (Rrange eq_refl). lia.
    - intros X. subst A. rewrite Eo in X.
      assert (g1 = g).
      { apply keyZ_inj.
        pose proof (proj1 (Forall_forall _ _) (proj2 (slot_ok_wf _ _ _ _ (Rcells g1 gr1 Hf))) c Hc) as Wc.
        unfold cell_wf, ciZ, ceZ in *. lia. }
      subst g1. apply (Hg1 eq_refl). lia. }
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg]; unfold validW, loZ, hiZ in *; cbn [rg_lo rg_hi] in *.
  - apply IMap.bst_add. exact Rbst.
  - exact Rrange.
  - intros K a Ha. destruct (Rvalid K a Ha) as (V1 & V2 & V3). pose proof (Rrange K).
    destruct (Z.lt_ge_cases a A) as [X|X]; [| destruct (Z.lt_ge_cases a (A + to_Z w)) as [Y|Y]].
    + rewrite RBF by lia. rewrite (wb_ext m m') by (apply FR; lia). auto.
    + split; [| split; [| exact V3]].
      * replace a with (A + (a - A)) by lia. rewrite RBW by lia. discriminate.
      * intros _. unfold wb, wview. replace a with (A + (a - A)) by lia. rewrite WR by lia. reflexivity.
    + rewrite RBF by lia. rewrite (wb_ext m m') by (apply FR; lia). auto.
  - intros g1 gr1 Hf. destruct (eqbP g1 g) as [EG|EG].
    + apply to_Z_inj in EG. subst g1. rewrite IMap.find_add_same in Hf by exact Rbst. injection Hf as <-. cbn [g_cells].
      split.
      * apply csorted_slot_sorted. unfold s', slot_store. apply insert_sorted_csorted; try assumption.
      * apply Forall_forall. intros x Hx. apply INs' in Hx. destruct Hx as [->|Hx].
        -- unfold cell_ok, newc. cbn [c_idx c_w c_v]. split; [lia|]. split; [lia|]. split; [lia|].
           intros t Ht. rewrite <- RBW by exact Ht. f_equal. subst A. lia.
        -- destruct (cut_In i w ltac:(lia) s x CS WF Hx) as [c [Hc P]].
           pose proof (proj1 (Forall_forall _ _) WF c Hc) as Wc.
           destruct (piece_props E i w ltac:(lia) ltac:(lia) c x Wc P) as (Wx & S1 & S2 & AVx & BY).
           unfold cell_wf in Wx. unfold cell_ok. split; [lia|]. split; [lia|]. split; [lia|].
           intros t Ht.
           assert (GD' : gran_of r g = (d, s)) by (unfold gran_of; fold g in GD; rewrite GD; reflexivity).
           destruct (IMap.find g (rg_cells r)) as [gr0|] eqn:F0.
           ++ destruct gr0 as [d0 s0]. injection GD as -> ->.
              destruct (OLD g (Gran d s) c (to_Z (c_idx x) + t) F0 Hc ltac:(unfold ciZ, ceZ in *; lia)
                          ltac:(intros _; unfold ciZ, ceZ in *; lia)) as [R1 R2].
              replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx x) + t) with (bv_unsigned (ev E k) + 8 * keyZ g + (to_Z (c_idx x) + t)) by lia.
              rewrite RBF by assumption.
              rewrite (cell_byte priv E m k r (RegionOk _ _ _ _ _ _ Rbst Rrange Rvalid Rcells Rin Rbg) g d s c) by (try exact GD'; unfold ciZ, ceZ in *; try exact Hc; lia).
              f_equal. apply bv_eq. rewrite !byte_of_zbyte by (unfold ciZ in *; lia).
              specialize (BY (to_Z (c_idx x) + t) ltac:(unfold ciZ, ceZ; lia)). unfold dbyte, ciZ in BY.
              replace (to_Z (c_idx x) + t - to_Z (c_idx x)) with t in BY by lia. symmetry. exact BY.
           ++ injection GD as <- <-. destruct Hc.
    + rewrite IMap.find_add_other in Hf by (try exact Rbst; intros X; apply EG; rewrite X; reflexivity).
      destruct (Rcells g1 gr1 Hf) as [SS FC]. split; [exact SS|].
      apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) FC c Hc) as (C1 & C2 & C3 & C4).
      split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros t Ht.
      assert (EG' : g1 <> g) by (intros X; apply EG; rewrite X; reflexivity).
      destruct (OLD g1 gr1 c (to_Z (c_idx c) + t) Hf Hc ltac:(unfold ciZ, ceZ; lia) ltac:(intros X; destruct (EG' X))) as [R1 R2].
      replace (bv_unsigned (ev E k) + 8 * keyZ g1 + to_Z (c_idx c) + t) with (bv_unsigned (ev E k) + 8 * keyZ g1 + (to_Z (c_idx c) + t)) by lia.
      rewrite RBF by assumption.
      replace (bv_unsigned (ev E k) + 8 * keyZ g1 + (to_Z (c_idx c) + t)) with (bv_unsigned (ev E k) + 8 * keyZ g1 + to_Z (c_idx c) + t) by lia.
      apply C4. exact Ht.
  - intros g1 gr1 c t Hf Hc Ht. cbv zeta. destruct (eqbP g1 g) as [EG|EG].
    + apply to_Z_inj in EG. subst g1. rewrite IMap.find_add_same in Hf by exact Rbst. injection Hf as <-. cbn [g_cells] in Hc.
      apply INs' in Hc. destruct Hc as [->|Hc].
      * unfold newc in *. cbn [c_idx c_w] in *.
        replace (8 * keyZ g + to_Z i + t) with (keyZ o + t) by lia. exact (VW t Ht).
      * destruct (cut_In i w ltac:(lia) s c CS WF Hc) as [c0 [Hc0 P]].
        pose proof (proj1 (Forall_forall _ _) WF c0 Hc0) as Wc0.
        destruct (piece_props E i w ltac:(lia) ltac:(lia) c0 c Wc0 P) as (Wx & S1 & S2 & _). unfold ciZ, ceZ in S1, S2.
        destruct (IMap.find g (rg_cells r)) as [[d0 s0]|] eqn:F0; [|injection GD as <- <-; destruct Hc0].
        injection GD as -> ->.
        pose proof (Rin g (Gran d s) c0 (to_Z (c_idx c) + t - to_Z (c_idx c0)) F0 Hc0 ltac:(lia)) as P'. cbv zeta in P'.
        replace (8 * keyZ g + to_Z (c_idx c0) + (to_Z (c_idx c) + t - to_Z (c_idx c0))) with (8 * keyZ g + to_Z (c_idx c) + t) in P' by lia.
        exact P'.
    + rewrite IMap.find_add_other in Hf by (try exact Rbst; intros X; apply EG; rewrite X; reflexivity).
      exact (Rin g1 gr1 c t Hf Hc Ht).
  - intros o' H1 H2 U.

    assert (U0 : uncovered r o').
    { intros g1 gr1 Hk1 Hf1. destruct (eqbP g1 g) as [EG|EG].
      - apply to_Z_inj in EG. subst g1.
        destruct (U g (Gran d s')) as [D NC]; [exact Hk1| cbn [rg_cells]; apply IMap.find_add_same; exact Rbst|].
        cbn [g_dirty g_cells] in D, NC. subst d.
        destruct (IMap.find g (rg_cells r)) as [[d0 s0]|] eqn:F0; [|discriminate]. injection GD as -> E0. injection Hf1 as <-.
        subst s0. cbn [g_dirty g_cells]. split; [reflexivity|].
        apply Forall_forall. intros c Hc COV. unfold covers in COV.
        assert (NI : ~ (to_Z i <= o' mod 8 < to_Z i + to_Z w)).
        { intros X. apply (proj1 (Forall_forall _ _) NC newc); [apply INs'; left; reflexivity|]. unfold covers, newc. cbn [c_idx c_w]. lia. }
        destruct (cut_covers i w ltac:(lia) ltac:(lia) s c (o' mod 8) CS WF Hc ltac:(unfold ciZ, ceZ; lia) NI) as [c' [Hc' COV']].
        apply (proj1 (Forall_forall _ _) NC c'); [apply INs'; right; exact Hc'|]. unfold covers. unfold ciZ, ceZ in COV'. lia.
      - apply (U g1 gr1 Hk1). cbn [rg_cells]. rewrite IMap.find_add_other; [exact Hf1| exact Rbst|].
        intros X; apply EG; rewrite X; reflexivity. }
    pose proof (Rbg o' H1 H2 U0) as G0. unfold bg_byte in *. cbn [rg_bg].
    destruct (match rg_bg r with BGNone => None | BGZero => Some (Z_to_bv 8 0) | BGImage => img_byte segs o'
              | BGUnk => Some (eg E k o') | BGBlob j shift => Some (nth (Z.to_nat (o' - to_Z shift)) (eb E j) (Z_to_bv 8 0)) end) as [b|]; [|exact I].
    rewrite RBF; [exact G0| |].
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      * destruct (H2 eq_refl) as (Q & _). rewrite half63 in Q. pose proof (eqb_correct _ _ K) as ->. rewrite (ev0_zero E Hz). unfold two64. lia.
      * pose proof (H1 eq_refl). pose proof (Rrange eq_refl). lia.
    + intros X. subst A. rewrite Eo in X.
      assert (Ho' : o' = 8 * keyZ g + (o' - 8 * keyZ g)) by lia.
      destruct (U g (Gran d s')) as [D NC].
      * rewrite Z.mul_comm in X. apply Z.div_unique with (r := o' - keyZ g * 8); lia.
      * cbn [rg_cells]. apply IMap.find_add_same. exact Rbst.
      * cbn [g_cells] in NC. apply (proj1 (Forall_forall _ _) NC newc); [apply INs'; left; reflexivity|].
        unfold covers, newc. cbn [c_idx c_w].
        replace (o' mod 8) with (o' - 8 * keyZ g); [lia|].
        apply Z.mod_unique with (q := keyZ g); lia.
Qed.

Lemma region_store1_fields : forall r o w v,
  rg_lo (Mem.region_store1 r o w v) = rg_lo r /\ rg_hi (Mem.region_store1 r o w v) = rg_hi r
  /\ rg_w (Mem.region_store1 r o w v) = rg_w r /\ rg_bg (Mem.region_store1 r o w v) = rg_bg r.
Proof.
  intros r o w v. unfold Mem.region_store1. destruct (IMap.find _ _) as [[d s]|]; cbn; repeat split; reflexivity.
Qed.

Lemma zbyte_shiftr : forall z a t, 0 <= a -> 0 <= t -> zbyte (Z.shiftr z (8 * a)) t = zbyte z (a + t).
Proof.
  intros z a t Ha Ht. unfold zbyte. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  rewrite <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma region_store_sound0 : forall m fs r key w v,
  facts_hold E fs ->
  region_ok segs priv E m k r -> wok w ->
  can_write segs fs priv k r key w = true ->
  let A := addrZ E k key in
  let m' := write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v)) in
  store_ok segs m (Z_to_bv 64 A) (Z.to_nat (to_Z w)) = true
  /\ region_ok segs priv E m' k (Mem.region_store r key w v)
  /\ rg_lo (Mem.region_store r key w v) = rg_lo r /\ rg_hi (Mem.region_store r key w v) = rg_hi r
  /\ rg_w (Mem.region_store r key w v) = rg_w r /\ rg_bg (Mem.region_store r key w v) = rg_bg r
  /\ (forall a, 0 <= a < two64 -> ~ (A <= a < A + to_Z w) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
Proof.
  intros m fs r key w v Hfs RO Hw CW. cbv zeta. unfold addrZ.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  pose proof (can_write_sound priv E m fs k r key w Hfs Hz RO Hw CW) as (CR & WB & SEGW).
  pose proof (can_read_sound priv E m fs k r key w Hfs Hz RO Hw CR) as (RA & RAw & RBn & RNG & ABS).
  unfold addrZ in *.
  pose proof (int_range key) as Rk. pose proof (int_range w) as Rw. rewrite two63_eq in Rk, Rw.
  split.
  { apply store_ok_wb; [lia| rewrite Z2Nat.id; lia |]. intros t Ht. apply WB. lia. }

  assert (NWV : keyZ (PrimInt63.add key w) = keyZ key + to_Z w /\ forall t, 0 <= t < to_Z w -> validW r (keyZ key + t)).
  { unfold can_write, can_read in CW. destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    - apply andb_prop in CW. destruct CW as [CW _]. apply andb_prop in CW. destruct CW as [L AW].
      destruct (ltbP key bit62i) as [L'|]; [|discriminate]. rewrite to_Z_bit62i in L'.
      destruct (abs_writable_sound (to_Z key) (to_Z w) ltac:(lia) ltac:(lia) AW) as [AR' _].
      destruct (abs_readable_sound (to_Z key) (to_Z w) ltac:(lia) AR') as [B62 _].
      destruct (keyZ_cases key) as [[_ EK]|[? _]]; [|lia].
      split.
      + rewrite EK. destruct (keyZ_cases (PrimInt63.add key w)) as [[? ->]|[X _]]; rewrite add_small in * by (rewrite two63_eq; lia); lia.
      + intros t Ht. split; [intros X; rewrite K in X; discriminate X|]. intros _. rewrite half63.
        pose proof (eqb_correct _ _ K) as Ek.
        destruct (ABS eq_refl t Ht) as [_ P]. destruct (SEGW eq_refl t Ht) as [sg' [F' _]].
        rewrite Ek, (ev0_zero E Hz), Z.add_0_l in P, F'.
        split; [lia|]. split; [exists sg'; exact F'| exact P].
    - apply andb_prop in CW. destruct CW as [_ CR']. apply andb_prop in CR'. destruct CR' as [CR' _].
      apply andb_prop in CR'. destruct CR' as [_ NW].
      split; [apply keyZ_add_nowrap; [lia| exact NW]|].
      intros t Ht. split; [intros _; apply (RNG eq_refl); exact Ht| intros X; rewrite K in X; discriminate X]. }
  destruct NWV as [NW VW].
  destruct (granule_gidx key ltac:(rewrite half63; apply keyZ_range)) as [Eo Ri].
  unfold Mem.region_store, in_granule.
  destruct (lebP (PrimInt63.add (gidx key) w) 8) as [IG|IG]; rewrite add_small in IG by (rewrite two63_eq; lia);
    change (to_Z 8) with 8 in IG.
  - destruct (region_store1_sound m r key w v RO ltac:(lia) IG VW) as [RO' FR'].
    split; [exact RO'|]. pose proof (region_store1_fields r key w v) as (F1 & F2 & F3 & F4).
    repeat (split; [assumption|]). exact FR'.
  - set (w1 := PrimInt63.sub 8 (gidx key)). set (w2 := PrimInt63.sub w w1).
    assert (Ew1 : to_Z w1 = 8 - to_Z (gidx key)) by (subst w1; rewrite sub_small; change (to_Z 8) with 8; lia).
    assert (Ew2 : to_Z w2 = to_Z w - to_Z w1) by (subst w2; rewrite sub_small; lia).
    pose proof (keyZ_add_le key w w1 ltac:(lia) ltac:(lia) NW) as K2.
    destruct (granule_gidx (PrimInt63.add key w1) ltac:(rewrite half63; apply keyZ_range)) as [Eo2 Ri2].
    assert (G2 : to_Z (gidx (PrimInt63.add key w1)) = 0).
    { assert (E1 : (keyZ key + to_Z w1) mod 8 = 0).
      { rewrite Eo, Ew1. replace (8 * keyZ (granule key) + to_Z (gidx key) + (8 - to_Z (gidx key))) with ((keyZ (granule key) + 1) * 8) by lia.
        apply Z.mod_mul. lia. }
      assert (E2 : (keyZ key + to_Z w1) mod 8 = to_Z (gidx (PrimInt63.add key w1))).
      { rewrite <- K2, Eo2. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
      lia. }

    destruct (region_store1_sound m r key w1 v RO ltac:(lia) ltac:(lia) ltac:(intros t Ht; apply VW; lia)) as [RO1 FR1].
    set (r1 := Mem.region_store1 r key w1 v) in *.
    set (m1 := write_to_mem m (Z_to_bv 64 (bv_unsigned (ev E k) + keyZ key)) (store_bytes w1 (den E v))) in *.
    pose proof (region_store1_fields r key w1 v) as (F1 & F2 & F3 & F4). fold r1 in F1, F2, F3, F4.

    assert (VW2 : forall t, 0 <= t < to_Z w2 -> validW r1 (keyZ (PrimInt63.add key w1) + t)).
    { intros t Ht. rewrite K2. unfold validW, loZ, hiZ. rewrite F1, F2. rewrite <- Z.add_assoc. apply VW. lia. }
    destruct (region_store1_sound m1 r1 (PrimInt63.add key w1) w2 (sv_ext false w1 w2 v) RO1 ltac:(lia) ltac:(lia) VW2) as [RO2 FR2].
    pose proof (region_store1_fields r1 (PrimInt63.add key w1) w2 (sv_ext false w1 w2 v)) as (F1' & F2' & F3' & F4').

    assert (EM : write_to_mem m (Z_to_bv 64 (bv_unsigned (ev E k) + keyZ key)) (store_bytes w (den E v))
                 = write_to_mem m1 (Z_to_bv 64 (bv_unsigned (ev E k) + keyZ (PrimInt63.add key w1)))
                     (store_bytes w2 (den E (sv_ext false w1 w2 v)))).
    { subst m1. unfold store_bytes at 1 2.
      replace (Z.to_nat (to_Z w)) with (Z.to_nat (to_Z w1) + Z.to_nat (to_Z w2))%nat by lia.
      rewrite Z_to_le_bytes_app, write_to_mem_app, length_Z_to_le_bytes, Z2Nat.id, K2 by lia.
      rewrite Z.add_assoc. f_equal. unfold store_bytes. apply Z_to_le_bytes_ext. intros t Ht. rewrite Z2Nat.id in Ht by lia.
      rewrite zbyte_shiftr by lia.
      rewrite ValP.den_sv_ext by (unfold ValP.width_ok; lia). unfold ext_word.
      pose proof (bv_unsigned_in_range 64 (den E v)) as Rv. rewrite bv_modulus_64 in Rv.
      rewrite Z_to_bv_small by (apply ValP.ext_Z_range; lia). rewrite zbyte_ext_Z by lia. reflexivity. }
    rewrite EM. split; [exact RO2|].
    rewrite F1', F2', F3', F4'. repeat (split; [assumption|]).
    intros a Ha Hna. rewrite FR2; [apply FR1; [exact Ha| lia] | exact Ha | rewrite K2; lia].
Qed.
End Store.

Lemma region_load_sound : forall priv E m fs k r key w sx v,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r -> wok w ->
  can_read segs fs priv k r key w = true ->
  Mem.region_load segs k r key w sx = Some v ->
  exists bs, length bs = Z.to_nat (to_Z w)
    /\ ov_read_bytes segs m (Z_to_bv 64 (addrZ E k key)) (Z.to_nat (to_Z w)) = Some bs
    /\ den E v = bytes_val sx (to_Z w) bs.
Proof.
  intros priv E m fs k r key w sx v Hfs Hz RO Hw CR H.
  exact (region_load_sound0 priv E m k r Hz RO fs key w sx v Hfs Hw CR H).
Qed.

Lemma region_store_sound : forall priv E m fs k r key w v,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r -> wok w ->
  can_write segs fs priv k r key w = true ->
  let A := addrZ E k key in
  let m' := write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v)) in
  store_ok segs m (Z_to_bv 64 A) (Z.to_nat (to_Z w)) = true
  /\ region_ok segs priv E m' k (Mem.region_store r key w v)
  /\ rg_lo (Mem.region_store r key w v) = rg_lo r /\ rg_hi (Mem.region_store r key w v) = rg_hi r
  /\ rg_w (Mem.region_store r key w v) = rg_w r /\ rg_bg (Mem.region_store r key w v) = rg_bg r
  /\ (forall a, 0 <= a < two64 -> ~ (A <= a < A + to_Z w) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
Proof.
  intros priv E m fs k r key w v Hfs Hz RO Hw CW.
  exact (region_store_sound0 priv E k Hz m fs r key w v Hfs RO Hw CW).
Qed.

Lemma memory_read_find_segment : forall o bs, 0 <= o < two64 ->
  memory_read segs (Z_to_bv 64 o) 1 = Some bs -> exists seg, find_segment segs o 1 = Some seg.
Proof.
  intros o bs Ho H. unfold memory_read in H.
  rewrite Z_to_bv_unsigned, bv_wrap_small in H by (rewrite bv_modulus_64; lia).
  change (Z.of_N 1) with 1 in H. destruct (find_segment segs o 1) as [sg|]; [eauto| discriminate].
Qed.

Lemma region_ok_frame : forall priv E m m' k r,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r ->
  (forall a, 0 <= a < two64 ->
     (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
     (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv priv a) ->
     m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  region_ok segs priv E m' k r.
Proof.
  intros priv E m m' k r Hz RO FR.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (HB0 : PrimInt63.eqb k 0%uint63 = true -> bv_unsigned (ev E k) = 0).
  { intros K. apply eqb_correct in K. subst k. apply ev0_zero. exact Hz. }
  rewrite half63 in *.
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha. rewrite (rb_ext m m'), (wb_ext m m'); [apply Rvalid; assumption| |];
      (apply FR; [pose proof (Rrange K); lia | intros _; exact Ha | intros K'; rewrite K in K'; discriminate K']).
  - intros g gr Hf. destruct (Rcells g gr Hf) as [Ss Fc]. split; [exact Ss|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Fc c Hc) as (C1 & C2 & C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
    rewrite (rb_ext m m'); [apply C4; exact Hi|].
    pose proof (Rin g gr c i Hf Hc Hi) as [P1 P2]. cbv zeta in P1, P2. rewrite ?half63 in P2.
    replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i)
      with (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i)) by lia.
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    + destruct (P2 eq_refl) as (Q1 & Q2 & Q3). rewrite (HB0 eq_refl). rewrite Z.add_0_l.
      apply FR; [unfold two64; lia | intros X; discriminate X | intros _; split; assumption].
    + pose proof (P1 eq_refl) as Q. pose proof (Rrange eq_refl) as RR.
      apply FR; [lia | intros _; lia | intros X; discriminate X].
  - exact Rin.
  - intros o H1 H2 U. pose proof (Rbg o H1 H2 U) as G. rewrite ?half63 in H2.
    destruct (bg_byte segs E k r o) as [b|]; [|exact I].
    rewrite (rb_ext m m'); [exact G|].
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    + destruct (H2 eq_refl) as (Q1 & [bs Q2] & Q3). rewrite (HB0 eq_refl). rewrite Z.add_0_l.
      apply FR; [unfold two64; lia | intros X; discriminate X | intros _].
      split; [| exact Q3]. apply (memory_read_find_segment o bs); [unfold two64; lia| exact Q2].
    + pose proof (H1 eq_refl) as Q. pose proof (Rrange eq_refl) as RR.
      apply FR; [lia | intros _; lia | intros X; discriminate X].
Qed.

Lemma fold_dirty_spec : forall (l : list (int * gran)) (m : IMap.t gran), IMap.bst m ->
  IMap.bst (fold_left (fun m kv => IMap.add (fst kv) (Gran true []) m) l m)
  /\ forall g, IMap.find g (fold_left (fun m kv => IMap.add (fst kv) (Gran true []) m) l m) =
       if existsb (fun kv => PrimInt63.eqb g (fst kv)) l then Some (Gran true []) else IMap.find g m.
Proof.
  induction l as [|kv l IH]; intros m B; cbn [fold_left existsb].
  - split; [exact B| intros g; reflexivity].
  - destruct (IH (IMap.add (fst kv) (Gran true []) m) (IMap.bst_add _ _ _ B)) as [B' F].
    split; [exact B'|]. intros g. rewrite F.
    destruct (existsb (fun kv0 => PrimInt63.eqb g (fst kv0)) l); cbn [orb].
    + destruct (PrimInt63.eqb g (fst kv)); reflexivity.
    + destruct (eqbP g (fst kv)) as [E|E].
      * apply to_Z_inj in E. subst g. apply IMap.find_add_same. exact B.
      * apply IMap.find_add_other; [exact B|]. intros E'. apply E. rewrite E'. reflexivity.
Qed.

Lemma region_forget_sound : forall priv E m k r glo ghi,
  region_ok segs priv E m k r ->
  region_ok segs priv E m k (Mem.region_forget r glo ghi)
  /\ rg_lo (Mem.region_forget r glo ghi) = rg_lo r /\ rg_hi (Mem.region_forget r glo ghi) = rg_hi r
  /\ rg_w (Mem.region_forget r glo ghi) = rg_w r /\ rg_bg (Mem.region_forget r glo ghi) = rg_bg r.
Proof.
  intros priv E m k r glo ghi RO. destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  unfold Mem.region_forget. destruct (Mem.is_bgnone (rg_bg r)) eqn:NB.
  {
    split; [| repeat split; reflexivity].
    assert (SUB : forall g gr, IMap.find g (IMap.remove_range glo ghi (rg_cells r)) = Some gr -> IMap.find g (rg_cells r) = Some gr).
    { intros g gr H. rewrite IMap.find_remove_range in H by exact Rbst. destruct (_ && _)%bool; [discriminate H| exact H]. }
    constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
    - apply IMap.remove_range_bst. exact Rbst.
    - exact Rrange.
    - exact Rvalid.
    - intros g gr H. apply Rcells. apply SUB. exact H.
    - intros g gr c i H. apply Rin. apply SUB. exact H.
    - intros o H1 H2 U. destruct (rg_bg r); try discriminate NB. cbn [bg_byte]. exact I. }
  split; [| repeat split; reflexivity].
  destruct (fold_dirty_spec (IMap.find_range glo ghi (rg_cells r)) (rg_cells r) Rbst) as [B' F].
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  - exact B'.
  - exact Rrange.
  - exact Rvalid.
  - intros g gr. rewrite F. destruct (existsb _ _).
    + intros E'. injection E' as <-. apply slot_ok_nil.
    + apply Rcells.
  - intros g gr c i. rewrite F. destruct (existsb _ _).
    + intros E'. injection E' as <-. intros H; destruct H.
    + apply Rin.
  - intros o H1 H2 U. unfold bg_byte. cbn [rg_bg]. fold (bg_byte segs E k r o). apply Rbg; [exact H1| exact H2|].
    intros g gr Hg Hf. unfold uncovered in U. cbn [rg_cells] in U. specialize (U g). rewrite F in U.
    destruct (existsb _ _).
    + destruct (U (Gran true []) Hg eq_refl) as [D _]. discriminate D.
    + apply U; assumption.
Qed.

End WithSegs.
End MemP.

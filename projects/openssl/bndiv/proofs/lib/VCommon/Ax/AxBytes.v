(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExBytes.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require ExLoad.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxKb AxVal.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition xb_bv (ρ : valuation) (x : xb) (b : byte) : Prop := xb_z ρ x (bv_unsigned b).

Lemma byte_range (b : byte) : 0 <= bv_unsigned b < 256.
Proof. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma bs_range (bs : list byte) : Forall (fun b => 0 <= b < 256) (map bv_unsigned bs).
Proof. apply Forall_map. apply Forall_forall. intros b _. apply byte_range. Qed.

Lemma nth_map_seq0 {A : Type} (f : nat -> A) (n i : nat) (d : A) : (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite (map_nth f (seq 0 n) 0%nat i). rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma Forall2_nth_error_ex {X Y : Type} (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) (k : nat) (d : X) :
  Forall2 P l1 l2 -> (k < length l1)%nat -> exists b, nth_error l2 k = Some b /\ P (nth k l1 d) b.
Proof.
  intros H. revert k. induction H as [|x y l1' l2' Hxy H IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; cbn [nth_error nth].
  - exists y. split; [reflexivity | exact Hxy].
  - apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bytes_of (sz : msize) (v : xv) : list xb :=
  let n := msz_n sz in
  match v with
  | XL x => map (fun i => BL (w_byte x i)) (seq 0 n)
  | XS ts o => map (fun i => BF ts o i) (seq 0 n)
  | XB l => if Nat.eqb (length l) 8 then firstn n l else repeat BT n
  | _ => repeat BT n
  end.

Lemma bytes_of_length (sz : msize) (v : xv) : length (bytes_of sz v) = msz_n sz.
Proof.
  unfold bytes_of. destruct v; rewrite ?length_map, ?length_seq, ?repeat_length; try reflexivity.
  destruct (Nat.eqb (length l) 8) eqn:E; [|apply repeat_length].
  apply Nat.eqb_eq in E. rewrite firstn_length_le; [reflexivity|]. rewrite E. destruct sz; cbn; lia.
Qed.

Lemma bytes_of_sound (ρ : valuation) (sz : msize) (v : xv) (w : bv 64) :
  xv_val ρ v w -> Forall2 (xb_bv ρ) (bytes_of sz v) (store_bytes sz w).
Proof.
  intros Hv. rewrite ExLoad.store_bytes_trunc. pose proof (bvu_range w) as Hw.
  assert (Hn8 : (msz_n sz <= 8)%nat) by (destruct sz; cbn; lia).
  assert (Htr : forall i, (i < msz_n sz)%nat -> zbyte (ExLoad.store_trunc sz w) i = zbyte (bv_unsigned w) i).
  { intros i Hi. unfold ExLoad.store_trunc. apply ExLoad.zbyte_mod; [lia|]. destruct sz; cbn [ExLoad.msz_bits msz_n] in *; lia. }
  assert (Htr0 : 0 <= ExLoad.store_trunc sz w) by (unfold ExLoad.store_trunc; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; destruct sz; cbn; lia).
  pose proof (bytes_of_length sz v) as Hlen.
  apply (ExLoad.Forall2_of_nth _ _ _ BT (Z_to_bv 8 0)).
  - rewrite length_Z_to_le_bytes. exact Hlen.
  - intros i Hi. rewrite Hlen in Hi.
    assert (Hb : bv_unsigned (nth i (Z_to_le_bytes (msz_n sz) (ExLoad.store_trunc sz w)) (Z_to_bv 8 0)) = zbyte (bv_unsigned w) i).
    { rewrite (ExLoad.Z_to_le_bytes_nth _ _ _ Htr0 Hi). apply Htr. exact Hi. }
    unfold xb_bv. rewrite Hb. unfold bytes_of. destruct v as [x|ts o|lo hi|km kv|l|]; cbn [xv_val] in Hv.
    + rewrite (nth_map_seq0 (fun i0 => BL (w_byte x i0)) _ i BT Hi). cbn [xb_z].
      rewrite w_byte_spec by lia. rewrite Hv. reflexivity.
    + rewrite (nth_map_seq0 (fun i0 => BF ts o i0) _ i BT Hi). cbn [xb_z]. rewrite Hv. reflexivity.
    + rewrite nth_repeat. exact I.
    + rewrite nth_repeat. exact I.
    + destruct Hv as [Hl Hbs]. rewrite Hl. cbn [Nat.eqb]. rewrite nth_firstn.
      rewrite (proj2 (Nat.ltb_lt _ _) Hi). apply Hbs. lia.
    + rewrite nth_repeat. exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint all_lit (l : list xb) : option (list int) :=
  match l with
  | [] => Some []
  | BL b :: r => match all_lit r with Some bs => Some (b :: bs) | None => None end
  | _ :: _ => None
  end.

Lemma all_lit_map (l : list xb) (bs : list int) : all_lit l = Some bs -> l = map BL bs.
Proof.
  revert bs; induction l as [|[b| |ts o i] r IH]; intros bs H; cbn [all_lit] in H; try discriminate.
  - injection H as <-. reflexivity.
  - destruct (all_lit r) as [bs'|] eqn:E; [|discriminate]. injection H as <-. cbn [map]. f_equal. apply IH. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint frags_n (ts : terms) (o : w64) (i : nat) (l : list xb) : bool :=
  match l with
  | [] => true
  | BF ts' o' j :: r => if Nat.eqb i j then if w_eqb o o' then if teqb ts ts' then frags_n ts o (S i) r else false else false else false
  | _ :: _ => false
  end.

Lemma frags_n_spec (ts : terms) (o : w64) (l : list xb) : forall i, frags_n ts o i l = true ->
  l = map (fun j => BF ts o j) (seq i (length l)).
Proof.
  induction l as [|ab r IH]; intros i H; cbn [frags_n] in H; [reflexivity|].
  destruct ab as [| |ts' o' j]; try discriminate.
  destruct (Nat.eqb i j) eqn:E1; [|discriminate]. destruct (w_eqb o o') eqn:E2; [|discriminate].
  destruct (teqb ts ts') eqn:E3; [|discriminate].
  apply Nat.eqb_eq in E1. rewrite w_eqb_spec in E2. apply Z.eqb_eq in E2. apply wZ_inj in E2. apply teqb_eq in E3. subst.
  cbn [length seq map]. f_equal. exact (IH _ H).
Qed.

(* [comment removed for export] *)
Lemma frag_bytes (ρ : valuation) (ts : terms) (o : w64) (l : list xb) (bs : list byte) (n : nat) :
  Forall2 (xb_bv ρ) l bs -> l = map (fun j => BF ts o j) (seq 0 n) ->
  bytes_le_to_Z bs = smod ρ ts o mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros Hf E. rewrite ExLoad.bytes_le_to_Z_zcombine.
  rewrite <- (zcombine_bytes (smod ρ ts o) n) by (pose proof (smod_range ρ ts o); lia). f_equal.
  subst l. clear -Hf. revert bs Hf. generalize 0%nat as i. induction n as [|n IH]; intros i bs Hf; cbn [seq map] in *.
  - inversion Hf; subst. reflexivity.
  - inversion Hf as [|? b ? bs' Hb Hr]; subst. cbn [map]. f_equal; [exact Hb | exact (IH _ _ Hr)].
Qed.

(* [comment removed for export] *)
Lemma load_bytes_small (sz : msize) (sg : bool) (bs : list byte) :
  length bs = msz_n sz ->
  (sg = false \/ bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (msz_n sz) - 1) \/ sz = SZ8) ->
  bv_unsigned (load_word sz sg bs) = bytes_le_to_Z bs.
Proof.
  intros Hl Hc.
  assert (Hr : 0 <= bytes_le_to_Z bs < 2 ^ ExLoad.msz_bits sz).
  { rewrite ExLoad.bytes_le_to_Z_zcombine. pose proof (zcombine_range _ (bs_range bs)) as X. rewrite length_map, Hl in X.
    destruct sz; cbn [msz_n ExLoad.msz_bits Z.of_nat] in *; exact X. }
  destruct sz; cbn [load_word ExLoad.msz_bits msz_n] in *.
  4: { rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr). reflexivity. }
  all: destruct sg;
    [ rewrite ExLoad.sext64_unsigned by lia; rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr);
      destruct Hc as [Hc|[Hc|Hc]]; try discriminate; cbn in Hc |- *; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity
    | rewrite ExLoad.zext64_unsigned by lia; rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr); reflexivity ].
Qed.

(* [comment removed for export] *)
Definition small_frag (s : store) (sz : msize) (sg : bool) (l : list xb) : option xv :=
  match l with
  | BF ts o O :: _ =>
      if frags_n ts o 0 l then
        match xrange s (XS ts o) with
        | Some (lo, hi) => if (0 <=? lo) && (hi <? 2 ^ (8 * Z.of_nat (msz_n sz) - (if sg then 1 else 0))) then Some (mk_xs ts o)
                           else if sg && (msz_n sz <? 8)%nat && (2 ^ (8 * Z.of_nat (msz_n sz) - 1) <=? lo) && (hi <? 2 ^ (8 * Z.of_nat (msz_n sz)))
                           then Some (mk_xs ts (w_sub o (wofZ (2 ^ (8 * Z.of_nat (msz_n sz)))))) else None
        | None => None
        end
      else None
  | _ => None
  end.

Lemma small_frag_sound (ρ : valuation) (s : store) (sz : msize) (sg : bool) (l : list xb) (bs : list byte) (v : xv) :
  sat ρ s -> Forall2 (xb_bv ρ) l bs -> length l = msz_n sz -> small_frag s sz sg l = Some v ->
  xv_val ρ v (load_word sz sg bs).
Proof.
  intros Hs Hf Hl H. unfold small_frag in H.
  destruct l as [|[| |ts o [|j]] r]; try discriminate.
  destruct (frags_n ts o 0 (BF ts o 0 :: r)) eqn:Eg; [|discriminate].
  destruct (xrange s (XS ts o)) as [[lo hi]|] eqn:Er; [|discriminate].
  pose proof (Forall2_length Hf) as Hlb.
  pose proof (frags_n_spec ts o _ 0 Eg) as E. rewrite Hl in E.
  assert (Hsv : xv_val ρ (XS ts o) (wbv (wofZ (smod ρ ts o)))).
  { cbn [xv_val]. rewrite wbv_unsigned, wZ_wofZ. apply Z.mod_small. apply smod_range. }
  pose proof (xrange_sound ρ s _ _ Hs Hsv _ Er) as Hr.
  rewrite wbv_unsigned, wZ_wofZ, Z.mod_small in Hr by apply smod_range. cbn [fst snd] in Hr.
  assert (Hn : (1 <= msz_n sz <= 8)%nat) by (destruct sz; cbn; lia).
  pose proof (frag_bytes ρ ts o _ bs (msz_n sz) Hf E) as HB.
  destruct ((0 <=? lo) && (hi <? 2 ^ (8 * Z.of_nat (msz_n sz) - (if sg then 1 else 0)))) eqn:Ec.
  - injection H as <-. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    assert (Hpw : 2 ^ (8 * Z.of_nat (msz_n sz) - (if sg then 1 else 0)) <= 2 ^ (8 * Z.of_nat (msz_n sz))) by (apply Z.pow_le_mono_r; destruct sg; lia).
    assert (HBv : bytes_le_to_Z bs = smod ρ ts o) by (rewrite HB; apply Z.mod_small; lia).
    apply mk_xs_sound. rewrite load_bytes_small; [exact HBv | lia |]. destruct sg; [right; left; rewrite HBv; lia | left; reflexivity].
  - destruct (sg && (msz_n sz <? 8)%nat && (2 ^ (8 * Z.of_nat (msz_n sz) - 1) <=? lo) && (hi <? 2 ^ (8 * Z.of_nat (msz_n sz)))) eqn:Ec2; [|discriminate].
    injection H as <-. apply andb_prop in Ec2 as [Ec2 E2]. apply andb_prop in Ec2 as [Ec2 E1]. apply andb_prop in Ec2 as [Esg En8]. subst sg.
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Nat.ltb_lt in En8.
    assert (Hp56 : 2 ^ (8 * Z.of_nat (msz_n sz)) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    assert (HBv : bytes_le_to_Z bs = smod ρ ts o) by (rewrite HB; apply Z.mod_small; lia).
    assert (Hr8 : 0 <= bytes_le_to_Z bs < 2 ^ ExLoad.msz_bits sz).
    { rewrite ExLoad.bytes_le_to_Z_zcombine. pose proof (zcombine_range _ (bs_range bs)) as X. rewrite length_map, <- Hlb, Hl in X.
      destruct sz; cbn [msz_n ExLoad.msz_bits Z.of_nat] in *; exact X. }
    assert (Hld : bv_unsigned (load_word sz true bs) = bytes_le_to_Z bs + two64 - 2 ^ (8 * Z.of_nat (msz_n sz))).
    { destruct sz; cbn [load_word ExLoad.msz_bits msz_n] in *.
      all: try (rewrite ExLoad.sext64_unsigned by lia; rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr8);
                rewrite (proj2 (Z.ltb_ge _ _)) by (cbn in *; lia); cbn; lia).
      all: rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr8); change (2 ^ (8 * Z.of_nat 8)) with two64; lia. }
    apply mk_xs_sound. rewrite Hld.
    assert (Ep : (2 ^ (8 * Z.of_nat (msz_n sz))) mod two64 = 2 ^ (8 * Z.of_nat (msz_n sz))).
    { apply Z.mod_small. split; [apply Z.pow_nonneg; lia | unfold two64; lia]. }
    unfold smod in *. rewrite wZ_sub, wZ_wofZ, Ep. rewrite Zplus_mod_idemp_r.
    replace (teval ρ ts + (wZ o - 2 ^ (8 * Z.of_nat (msz_n sz)))) with ((teval ρ ts + wZ o) + (- 2 ^ (8 * Z.of_nat (msz_n sz)))) by ring.
    rewrite Zplus_mod. rewrite <- HBv.
    assert (Hpos : 0 < 2 ^ (8 * Z.of_nat (msz_n sz) - 1)) by (clear -Hn; apply Z.pow_pos_nonneg; lia).
    assert (Em : (- 2 ^ (8 * Z.of_nat (msz_n sz))) mod two64 = two64 - 2 ^ (8 * Z.of_nat (msz_n sz))).
    { rewrite <- (Z_mod_plus_full _ 1). replace (- 2 ^ (8 * Z.of_nat (msz_n sz)) + 1 * two64) with (two64 - 2 ^ (8 * Z.of_nat (msz_n sz))) by ring.
      apply Z.mod_small. unfold two64 in *. lia. }
    rewrite Em. replace (bytes_le_to_Z bs + (two64 - 2 ^ (8 * Z.of_nat (msz_n sz)))) with (bytes_le_to_Z bs + two64 - 2 ^ (8 * Z.of_nat (msz_n sz))) by ring.
    symmetry. apply Z.mod_small. unfold two64 in *. lia.
Qed.

(* [comment removed for export] *)
Definition lit_load (sz : msize) (sg : bool) (bs : list int) : w64 :=
  ExLoad.load_ext sz sg (match sz with SZ8 => ExLoad.w_of_bytes8 bs | _ => W false (ExLoad.icombine bs) end).

Lemma lit_load_sound (sz : msize) (sg : bool) (ibs : list int) (bs : list byte) :
  length ibs = msz_n sz -> Forall2 (fun i b => bv_unsigned b = to_Z i) ibs bs ->
  bv_unsigned (load_word sz sg bs) = wZ (lit_load sz sg ibs).
Proof.
  intros Hl Hf. pose proof (Forall2_length Hf) as Hlb.
  assert (Hm : map to_Z ibs = map bv_unsigned bs).
  { clear -Hf. induction Hf as [|i b r r' H _ IH]; [reflexivity|]. cbn [map]. rewrite H, IH. reflexivity. }
  assert (H256 : Forall (fun b => to_Z b < 256) ibs).
  { clear -Hf. induction Hf as [|i b r r' H _ IH]; constructor; [|exact IH]. rewrite <- H. apply byte_range. }
  assert (Hz : wZ (match sz with SZ8 => ExLoad.w_of_bytes8 ibs | _ => W false (ExLoad.icombine ibs) end) = bytes_le_to_Z bs).
  { rewrite ExLoad.bytes_le_to_Z_zcombine, <- Hm.
    destruct sz; cbn [msz_n] in Hl;
      try (unfold wZ; cbn [wh wl]; rewrite Z.add_0_l; apply ExLoad.icombine_spec; [lia | exact H256]).
    apply ExLoad.w_of_bytes8_spec; assumption. }
  pose proof (ExLoad.load_ext_spec (fun _ => 0) sz sg _ bs ltac:(lia) Hz) as X. cbn [ExVal.aval_val] in X. exact X.
Qed.

Lemma zbyte_high (z : Z) (n i : nat) : 0 <= z < 2 ^ (8 * Z.of_nat n) -> (n <= i)%nat -> zbyte z i = 0.
Proof.
  intros Hz Hi. unfold zbyte. rewrite Z.div_small; [reflexivity|]. split; [lia|].
  apply Z.lt_le_trans with (2 ^ (8 * Z.of_nat n)); [lia | apply Z.pow_le_mono_r; lia].
Qed.

(* [comment removed for export] *)
Lemma sub_word_XB (ρ : valuation) (sz : msize) (sg : bool) (l : list xb) (bs : list byte) :
  Forall2 (xb_bv ρ) l bs -> length l = msz_n sz ->
  xv_val ρ (XB (l ++ repeat (if sg then BT else BL 0%uint63) (8 - msz_n sz))) (load_word sz sg bs).
Proof.
  intros Hf Hl. pose proof (Forall2_length Hf) as Hlb. assert (Hn : (1 <= msz_n sz <= 8)%nat) by (destruct sz; cbn; lia).
  cbn [xv_val]. split; [rewrite length_app, repeat_length; lia|]. intros i Hi.
  set (B := bytes_le_to_Z bs).
  assert (HB : 0 <= B < 2 ^ (8 * Z.of_nat (msz_n sz))).
  { unfold B. rewrite ExLoad.bytes_le_to_Z_zcombine. pose proof (zcombine_range _ (bs_range bs)) as X. rewrite length_map, <- Hlb, Hl in X. exact X. }
  assert (HBb : forall j, (j < msz_n sz)%nat -> xb_z ρ (nth j l BT) (zbyte B j)).
  { intros j Hj. unfold B. rewrite ExLoad.bytes_le_to_Z_zcombine. rewrite zbyte_zcombine by (try apply bs_range; rewrite length_map; lia).
    destruct (Forall2_nth_error_ex _ l bs j BT Hf ltac:(lia)) as [b [Hb Hab]].
    rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
    rewrite map_nth. rewrite (nth_error_nth _ _ _ Hb). exact Hab. }
  assert (Hr8 : 0 <= B < 2 ^ ExLoad.msz_bits sz) by (destruct sz; cbn [msz_n ExLoad.msz_bits Z.of_nat] in *; exact HB).
  assert (Hld : bv_unsigned (load_word sz sg bs) = B \/ (sg = true /\ (msz_n sz < 8)%nat /\ bv_unsigned (load_word sz sg bs) = B + two64 - 2 ^ (8 * Z.of_nat (msz_n sz)))).
  { destruct sz; cbn [load_word ExLoad.msz_bits msz_n] in *.
    4: { left. rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr8). reflexivity. }
    all: destruct sg;
      [ rewrite ExLoad.sext64_unsigned by lia; rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr8);
        match goal with |- context [if ?c then _ else _] => destruct c end; [left; reflexivity | right; split; [reflexivity | split; [lia | reflexivity]]]
      | left; rewrite ExLoad.zext64_unsigned by lia; rewrite ExLoad.extract_le_unsigned by (try lia; exact Hr8); reflexivity ]. }
  destruct (Nat.lt_ge_cases i (msz_n sz)) as [Hlt|Hge].
  - rewrite app_nth1 by lia.
    destruct Hld as [E|[_ [Hn8 E]]]; rewrite E; [exact (HBb i Hlt)|].
    assert (Hp : 2 ^ (8 * Z.of_nat (msz_n sz)) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    rewrite <- (ExLoad.zbyte_mod (B + two64 - 2 ^ (8 * Z.of_nat (msz_n sz))) (8 * Z.of_nat (msz_n sz)) i) by (unfold two64 in *; lia).
    replace (B + two64 - 2 ^ (8 * Z.of_nat (msz_n sz))) with (B + (2 ^ (64 - 8 * Z.of_nat (msz_n sz)) - 1) * 2 ^ (8 * Z.of_nat (msz_n sz))).
    + rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. exact (HBb i Hlt).
    + rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (64 - 8 * Z.of_nat (msz_n sz) + 8 * Z.of_nat (msz_n sz)) with 64 by lia. unfold two64. lia.
  - rewrite app_nth2 by lia. destruct sg; [rewrite nth_repeat; exact I|].
    rewrite (nth_indep _ BT (BL 0%uint63)) by (rewrite repeat_length; lia). rewrite nth_repeat. cbn [xb_z]. change (to_Z 0%uint63) with 0.
    destruct Hld as [E|[E _]]; [|discriminate]. rewrite E. apply (zbyte_high B (msz_n sz) i HB Hge).
Qed.

Definition val_of_bytes (s : store) (sz : msize) (sg : bool) (l : list xb) : xv :=
  match all_lit l with
  | Some bs => XL (lit_load sz sg bs)
  | None =>
      match sz with
      | SZ8 =>
          match l with
          | BF ts o O :: _ => if frags_n ts o 0 l then XS ts o else XB l
          | _ => XB l
          end
      | _ => match small_frag s sz sg l with
             | Some v => v
             | None => XB (l ++ repeat (if sg then BT else BL 0%uint63) (8 - msz_n sz))   (* [comment removed for export] *)
             end
      end
  end.

Lemma val_of_bytes_sound (ρ : valuation) (s : store) (sz : msize) (sg : bool) (l : list xb) (bs : list byte) :
  sat ρ s -> Forall2 (xb_bv ρ) l bs -> length l = msz_n sz ->
  xv_val ρ (val_of_bytes s sz sg l) (load_word sz sg bs).
Proof.
  intros Hs Hf Hl. unfold val_of_bytes. pose proof (Forall2_length Hf) as Hlb.
  destruct (all_lit l) as [ibs|] eqn:Ea.
  - cbn [xv_val]. apply all_lit_map in Ea. subst l. rewrite length_map in Hl.
    apply lit_load_sound; [exact Hl|]. clear -Hf. revert bs Hf. induction ibs as [|i r IH]; intros bs Hf; inversion Hf; subst; constructor.
    + assumption.
    + apply IH. assumption.
  - assert (HXB : sz = SZ8 -> xv_val ρ (XB l) (load_word sz sg bs)).
    { intros ->. cbn [xv_val msz_n] in *. split; [exact Hl|]. intros i Hi.
      assert (Hw : bv_unsigned (load_word SZ8 sg bs) = bytes_le_to_Z bs) by (apply load_bytes_small; [cbn [msz_n]; lia | right; right; reflexivity]).
      rewrite Hw, ExLoad.bytes_le_to_Z_zcombine. rewrite zbyte_zcombine by (try apply bs_range; rewrite length_map; lia).
      destruct (Forall2_nth_error_ex _ l bs i BT Hf ltac:(lia)) as [b [Hb Hab]].
      rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
      rewrite map_nth. rewrite (nth_error_nth _ _ _ Hb). exact Hab. }
    destruct sz.
    4: { destruct l as [|[| |ts o [|j]] r]; try (apply HXB; reflexivity).
         destruct (frags_n ts o 0 (BF ts o 0 :: r)) eqn:Eg; [|apply HXB; reflexivity].
         cbn [xv_val]. pose proof (frags_n_spec ts o _ 0 Eg) as E. rewrite Hl in E.
         rewrite load_bytes_small by (try lia; right; right; reflexivity).
         rewrite (frag_bytes ρ ts o _ bs 8 Hf E). apply Z.mod_small. pose proof (smod_range ρ ts o). unfold two64 in *. cbn. lia. }
    all: destruct (small_frag s _ sg l) as [v|] eqn:Esf; [exact (small_frag_sound ρ s _ sg l bs v Hs Hf Hl Esf)|];
         apply sub_word_XB; assumption.
Qed.

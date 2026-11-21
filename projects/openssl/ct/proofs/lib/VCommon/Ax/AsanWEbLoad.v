(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the MAP_FIXED overflow answer check_mmap_fixed_overflow; the munmap changes of the model; the start-up over the run's entry stack). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxEntryRel AsanWEntry AsanWEb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition xb_bv' (ρ : valuation) (x : xb) (b : byte) : Prop := xb_z ρ x (bv_unsigned b).

Definition eaddr (v : xv) : option (terms * w64) :=
  match v with
  | XL a => Some ([], a)
  | XS ts o => Some (ts, o)
  | _ => None
  end.

Definition form_bytes (ts : terms) (o : w64) (n : nat) : list xb := map (fun j => BF ts o j) (seq 0 n).
Definition lit_bytes (K : Z) (n : nat) : list xb := map (fun j => BL (of_Z (zbyte (K mod two64) j))) (seq 0 n).

(* Patterns of the 08b1429 block, offsets from sp: the auxv starts at 24 + 8a + 8e
   ([t_ae]); the AT_RANDOM bytes at 488 + 8a + 8e + 8 par ([t_aep]); argv[0] at
   488 + 8a + 8e + g ([t_aeg]); AT_EXECFN's string after argv and envp ([t_xfn]). *)
(** the block's first byte above the auxv, from sp: 488 with rseq, 456 without *)
Definition AUX_OFF (r : bool) : Z := 24 + Z.of_nat (auxv_size r).

Lemma AUX_OFF_rng (r : bool) : 456 <= AUX_OFF r <= 488.
Proof.
  unfold AUX_OFF. destruct r; [change (auxv_size true) with 464%nat | change (auxv_size false) with 432%nat]; lia.
Qed.
Lemma AUX_OFF_true : AUX_OFF true = 488. Proof. reflexivity. Qed.
Lemma AUX_OFF_false : AUX_OFF false = 456. Proof. reflexivity. Qed.
Lemma auxv_size_true : auxv_size true = 464%nat. Proof. reflexivity. Qed.
Lemma auxv_size_false : auxv_size false = 432%nat. Proof. reflexivity. Qed.


Definition t_ae : terms := [(v_argc, 8); (v_envc, 8)].
Definition t_aeg : terms := [(v_argc, 8); (v_envc, 8); (v_g, 1)].
Definition t_aeg0 : terms := [(v_argc, 8); (v_envc, 8); (v_g, 1); (lenvar 0, 1)].
Definition t_aeg01 : terms := [(v_argc, 8); (v_envc, 8); (v_g, 1); (lenvar 0, 1); (lenvar 1, 1)].
Definition t_aep : terms := [(v_argc, 8); (v_envc, 8); (v_par, 8)].
Definition t_xfn : terms := [(v_argc, 8); (v_envc, 8); (v_ta, 1); (v_te, 1); (v_g, 1)].

(** slot [t] of the auxv: keys at even [t], values at odd [t].  The 26 leading pairs are the
    same in both layouts; [r] decides whether the two rseq pairs precede AT_NULL. *)
Definition auxv_key_z (r : bool) (i : nat) : Z :=
  nth i ([33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
         ++ (if r then [27; 28] else []) ++ [0]) 0.

Definition auxv_val_slot (r : bool) (ph : PhdrInfo) (i n : nat) : list xb :=
  match i with
  | 0%nat => form_bytes [(v_vd, 1)] w_zero n
  | 9%nat => form_bytes [(v_mss, 1)] w_zero n
  | 10%nat => form_bytes [(v_hw, 1)] w_zero n
  | 11%nat => lit_bytes 4096 n
  | 12%nat => lit_bytes 100 n
  | 13%nat => lit_bytes (Z.of_N (ph_addr ph)) n
  | 14%nat => lit_bytes (Z.of_N (ph_ent ph)) n
  | 15%nat => lit_bytes (Z.of_N (ph_num ph)) n
  | 18%nat => form_bytes [(v_ent, 1)] w_zero n
  | 19%nat | 20%nat => form_bytes [(v_uid, 1)] w_zero n
  | 21%nat | 22%nat => form_bytes [(v_gid, 1)] w_zero n
  | 24%nat => form_bytes (sp_terms ++ t_aep) (wofZ (AUX_OFF r)) n
  | 25%nat => form_bytes (sp_terms ++ t_xfn) (wofZ (AUX_OFF r)) n
  | 26%nat => if r then lit_bytes 28 n else lit_bytes 0 n
  | 27%nat => if r then lit_bytes 32 n else lit_bytes 0 n
  | _ => lit_bytes 0 n
  end.

Definition auxv_slot (r : bool) (ph : PhdrInfo) (t n : nat) : list xb :=
  if Nat.even t then lit_bytes (auxv_key_z r (Nat.div2 t)) n else auxv_val_slot r ph (Nat.div2 t) n.

Definition str_byte (s : store) (k j : Z) : option (list xb) :=
  match lrange s (lvar (lenvar k) 1) with
  | Some (lo, hi) => if (0 <=? j) && (j <? lo) then Some [BF [(strvar k j, 1)] w_zero 0]
                     else if (lo =? j) && (hi =? j) then Some [BL 0%uint63] else None
  | None => None
  end.

Definition argc_ge2 (s : store) : bool :=
  match lrange s (lvar v_argc 1) with Some (lo, _) => 2 <=? lo | None => false end.
Definition argc_is1 (s : store) : bool :=
  match lrange s (lvar v_argc 1) with Some (lo, hi) => (lo =? 1) && (hi =? 1) | None => false end.

Definition eb_cls (r : bool) (ph : PhdrInfo) (s : store) (d : lin) (n : nat) : option (list xb) :=
  let c := fst d in
  if (n =? 0)%nat then None else
  match snd d with
  | [] =>
      if (c =? 0) && (n <=? 8)%nat then Some (form_bytes [(v_argc, 1)] w_zero n)
      else if (c =? 8) && (n <=? 8)%nat then Some (form_bytes (sp_terms ++ t_aeg) (wofZ (AUX_OFF r)) n)
      else if (c =? 16) && (n <=? 8)%nat then
        (if argc_ge2 s then Some (form_bytes (sp_terms ++ t_aeg0) (wofZ (AUX_OFF r + 1)) n)
         else if argc_is1 s then Some (repeat (BL 0%uint63) n) else None)
      else None
  | td =>
      if teqb td t_ae then
        if (24 <=? c) && (c <? AUX_OFF r) && ((c - 24) mod 8 =? 0) && (n <=? 8)%nat then
          Some (auxv_slot r ph (Z.to_nat ((c - 24) / 8)) n)
        else None
      else if teqb td t_aeg then
        if (AUX_OFF r <=? c) && (n =? 1)%nat then str_byte s 0 (c - AUX_OFF r) else None
      else if teqb td t_aeg0 then
        if (AUX_OFF r + 1 <=? c) && (n =? 1)%nat && argc_ge2 s then str_byte s 1 (c - (AUX_OFF r + 1))
        else if (c =? AUX_OFF r) && (n =? 1)%nat then Some [BL 0%uint63]
        else None
      else if teqb td t_aeg01 then
        if (c =? AUX_OFF r + 1) && (n =? 1)%nat && argc_ge2 s then Some [BL 0%uint63] else None
      else if teqb td t_aep then
        if (AUX_OFF r <=? c) && (c - AUX_OFF r + Z.of_nat n <=? 16) then
          Some (map (fun i => if (i <? 8)%nat then BF [(v_r0, 1)] w_zero i else BF [(v_r1, 1)] w_zero (i - 8))
                    (seq (Z.to_nat (c - AUX_OFF r)) n))
        else None
      else None
  end.

Definition eb_pin (s : store) (x : int) : option Z :=
  match vbound s x with
  | Some (lo, hi) => if lo =? hi then Some lo else None
  | None => None
  end.

Fixpoint eb_canon (s : store) (ts : terms) : Z * terms :=
  match ts with
  | [] => (0, [])
  | (x, a) :: r =>
      let cr := eb_canon s r in
      match eb_pin s x with
      | Some z => (fst cr + a * z, snd cr)
      | None => (fst cr, (x, a) :: snd cr)
      end
  end.

Definition rebase (s : store) (d : lin) (T : terms) : option lin :=
  let cd := eb_canon s (snd d) in
  let cT := eb_canon s T in
  if teqb (snd cd) (snd cT) then Some (fst d + fst cd - fst cT, T) else None.

Definition eb_pats : list terms := [[]; t_ae; t_aeg; t_aeg0; t_aeg01; t_aep].

Fixpoint eb_try (r : bool) (ph : PhdrInfo) (s : store) (d : lin) (n : nat) (pats : list terms) : option (list xb) :=
  match pats with
  | [] => None
  | T :: pats' =>
      match (match rebase s d T with Some d' => eb_cls r ph s d' n | None => None end) with
      | Some l => Some l
      | None => eb_try r ph s d n pats'
      end
  end.

Definition eb_load (r : bool) (ph : PhdrInfo) (s : store) (v : xv) (n : nat) : option (list xb) :=
  match eaddr v with
  | Some (ts, o) =>
      let d := lsub (wS o, ts) (0, sp_terms) in
      match eb_cls r ph s d n with
      | Some l => Some l
      | None => eb_try r ph s d n eb_pats
      end
  | None => None
  end.

Lemma teval_app : forall (ρ : valuation) (a b : terms), teval ρ (a ++ b) = teval ρ a + teval ρ b.
Proof. intros ρ a b. induction a as [|[x k] r IH]; cbn [app teval]; lia. Qed.

Lemma smod_lit : forall ρ ts (c : Z), 0 <= c < two64 -> smod ρ ts (wofZ c) = (teval ρ ts + c) mod two64.
Proof. intros ρ ts c Hc. unfold smod. rewrite wZ_wofZ, (Z.mod_small c two64 Hc). reflexivity. Qed.

Lemma u_zbv : forall z : Z, bv_unsigned (Z_to_bv 64 z) = z mod two64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma nth_word_le8 : forall (w : word) (j : nat), (j < 8)%nat ->
  bv_unsigned (nth j (word_le8 w) (Z_to_bv 8 0)) = zbyte (bv_unsigned w) j.
Proof.
  intros w j Hj. unfold zbyte.
  assert (E : nth j (word_le8 w) (Z_to_bv 8 0) = bv_extract (N.of_nat (8 * j)) 8 w).
  { do 8 (destruct j as [|j]; [reflexivity|]). lia. }
  rewrite E, bv_extract_unsigned. unfold bv_wrap. rewrite Z.shiftr_div_pow2 by lia.
  change (bv_modulus 8) with 256. f_equal. f_equal. f_equal. lia.
Qed.

Lemma F2_nth : forall (ρ : valuation) (l : list xb) (bs : list byte), length l = length bs ->
  (forall j, (j < length l)%nat -> xb_bv' ρ (nth j l BT) (nth j bs (Z_to_bv 8 0))) -> Forall2 (xb_bv' ρ) l bs.
Proof.
  intros ρ l. induction l as [|x l IH]; intros [|b bs] Hl H; cbn in Hl; try discriminate; [constructor|].
  constructor; [exact (H 0%nat ltac:(cbn; lia)) |]. apply IH; [lia|]. intros j Hj. exact (H (S j) ltac:(cbn; lia)).
Qed.

Lemma nth_seq_map : forall {A} (f : nat -> A) (s n j : nat) (d : A), (j < n)%nat -> nth j (map f (seq s n)) d = f (s + j)%nat.
Proof.
  intros A f s n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma F2_form : forall ρ ts o (w : word) (n : nat), (n <= 8)%nat -> bv_unsigned w = smod ρ ts o ->
  Forall2 (xb_bv' ρ) (form_bytes ts o n) (firstn n (word_le8 w)).
Proof.
  intros ρ ts o w n Hn Hw. apply F2_nth.
  - unfold form_bytes. rewrite length_map, length_seq, length_firstn, length_n_to_le_8. lia.
  - intros j Hj. unfold form_bytes in *. rewrite length_map, length_seq in Hj.
    rewrite nth_seq_map by exact Hj. unfold xb_bv', xb_z. rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _) Hj).
    rewrite nth_word_le8 by lia. rewrite Hw. reflexivity.
Qed.

Lemma F2_lit : forall ρ (K : Z) (w : word) (n : nat), (n <= 8)%nat -> bv_unsigned w = K mod two64 ->
  Forall2 (xb_bv' ρ) (lit_bytes K n) (firstn n (word_le8 w)).
Proof.
  intros ρ K w n Hn Hw. apply F2_nth.
  - unfold lit_bytes. rewrite length_map, length_seq, length_firstn, length_n_to_le_8. lia.
  - intros j Hj. unfold lit_bytes in *. rewrite length_map, length_seq in Hj.
    rewrite nth_seq_map by exact Hj. unfold xb_bv', xb_z. rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _) Hj).
    rewrite nth_word_le8 by lia. rewrite Hw. cbn [Nat.add]. rewrite of_Z_spec.
    pose proof (zbyte_range (K mod two64) j). rewrite (Z.mod_small (zbyte (K mod two64) j) wB); [reflexivity|].
    change wB with two63. unfold two63. lia.
Qed.

Lemma F2_zero : forall ρ (n : nat), (n <= 8)%nat ->
  Forall2 (xb_bv' ρ) (repeat (BL 0%uint63) n) (firstn n (word_le8 (Z_to_bv 64 0))).
Proof.
  intros ρ n Hn. apply F2_nth.
  - rewrite repeat_length, length_firstn, length_n_to_le_8. lia.
  - intros j Hj. rewrite repeat_length in Hj.
    rewrite (nth_indep _ BT (BL 0%uint63)) by (rewrite repeat_length; exact Hj). rewrite nth_repeat. unfold xb_bv', xb_z.
    rewrite nth_firstn, (proj2 (Nat.ltb_lt _ _) Hj), nth_word_le8 by lia. rewrite u_zbv. reflexivity.
Qed.

Lemma rdB_prefix : forall (B : list byte) (o n : nat), (n <= 8)%nat -> rdB B o n = firstn n (rdB B o 8).
Proof. intros B o n Hn. unfold rdB. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma rdB_one : forall (B : list byte) (o : nat), (o < length B)%nat -> rdB B o 1 = [nth o B (Z_to_bv 8 0)].
Proof.
  intros B o Ho. unfold rdB. revert B Ho. induction o as [|o IH]; intros [|b B] Ho; cbn in Ho; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma total_first : forall (L : list (list byte)), L <> [] -> Z.of_nat (length (nth 0 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros [|x L] H; [contradiction|]. unfold total_arg_bytes. cbn [fold_right nth].
  pose proof (total_arg_bytes_nonneg L). unfold total_arg_bytes in *. lia.
Qed.

Lemma total_two : forall (L : list (list byte)), (2 <= length L)%nat ->
  Z.of_nat (length (nth 0 L [])) + 1 + Z.of_nat (length (nth 1 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros [|x [|y L]] H; cbn in H; try lia. unfold total_arg_bytes. cbn [fold_right nth].
  pose proof (total_arg_bytes_nonneg L). unfold total_arg_bytes in *. lia.
Qed.

Section Cls.
Local Set Default Proof Using "All".
Variables (r : bool) (ph : PhdrInfo) (ρ : valuation) (s : store).
Hypothesis Hs : sat ρ s.
Hypothesis HF : eb_facts r ρ.

Let B := eb_image r ph ρ.
Let SO : Z := AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g.

Lemma cl_argc : 1 <= ρ v_argc <= 1024. Proof. apply HF. Qed.
Lemma cl_envc : 0 <= ρ v_envc <= 256. Proof. apply HF. Qed.
Lemma cl_g : 16 + 8 * ρ v_par <= ρ v_g. Proof. pose proof (facts_g r (mkPhdrInfo 0 0 0) ρ HF). lia. Qed.
Lemma cl_par : 0 <= ρ v_par <= 1.
Proof. rewrite (facts_par r (mkPhdrInfo 0 0 0) ρ HF). pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)). lia. Qed.
Lemma cl_len : Z.of_nat (length B) = SO + ρ v_ta + ρ v_te + ρ v_xl + 9. Proof. exact (R7_length r ph ρ HF). Qed.
Lemma cl_tx : 0 <= ρ v_te /\ 0 <= ρ v_xl.
Proof.
  pose proof (facts_xl r (mkPhdrInfo 0 0 0) ρ HF). destruct HF as (_ & _ & _ & _ & _ & He & _). rewrite He. split; [apply total_arg_bytes_nonneg | lia].
Qed.

Lemma cl_len0 : ρ (lenvar 0) + 1 <= ρ v_ta.
Proof.
  pose proof cl_argc. pose proof (len_av r (mkPhdrInfo 0 0 0) ρ HF). pose proof (len_k r (mkPhdrInfo 0 0 0) ρ HF 0 ltac:(lia)) as L0.
  destruct HF as (_ & _ & _ & _ & Ht & _). rewrite Ht. change (Z.to_nat 0) with 0%nat in L0. rewrite <- L0.
  apply total_first. intros E. rewrite E in *. cbn in *. lia.
Qed.

Lemma cl_len01 : 2 <= ρ v_argc -> ρ (lenvar 0) + 1 + ρ (lenvar 1) + 1 <= ρ v_ta.
Proof.
  intros H2. pose proof (len_av r (mkPhdrInfo 0 0 0) ρ HF). pose proof (len_k r (mkPhdrInfo 0 0 0) ρ HF 0 ltac:(lia)) as L0. pose proof (len_k r (mkPhdrInfo 0 0 0) ρ HF 1 ltac:(lia)) as L1.
  destruct HF as (_ & _ & _ & _ & Ht & _). rewrite Ht. change (Z.to_nat 0) with 0%nat in L0. change (Z.to_nat 1) with 1%nat in L1.
  rewrite <- L0, <- L1. apply total_two. lia.
Qed.

Lemma argc_ge2_sound : argc_ge2 s = true -> 2 <= ρ v_argc.
Proof.
  unfold argc_ge2. destruct (lrange s (lvar v_argc 1)) as [[lo hi]|] eqn:E; [|discriminate].
  intros H. apply Z.leb_le in H. pose proof (lrange_sound ρ s _ Hs _ E) as R. rewrite leval_lvar in R. cbn [fst snd] in R. lia.
Qed.

Lemma argc_is1_sound : argc_is1 s = true -> ρ v_argc = 1.
Proof.
  unfold argc_is1. destruct (lrange s (lvar v_argc 1)) as [[lo hi]|] eqn:E; [|discriminate].
  intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  pose proof (lrange_sound ρ s _ Hs _ E) as R. rewrite leval_lvar in R. cbn [fst snd] in R. lia.
Qed.

Definition cls_ok (l : list xb) (z0 : Z) (n : nat) : Prop :=
  0 <= z0 /\ z0 + Z.of_nat n <= Z.of_nat (length B) /\ Forall2 (xb_bv' ρ) l (rdB B (Z.to_nat z0) n).

Lemma SO_ge : AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + 16 + 8 * ρ v_par <= SO.
Proof. unfold SO. pose proof cl_g. lia. Qed.

Lemma str0_sound : forall j l, str_byte s 0 j = Some l -> cls_ok l (SO + j) 1.
Proof.
  intros j l H. unfold str_byte in H. pose proof cl_len. pose proof cl_tx. pose proof cl_len0. pose proof cl_argc. pose proof cl_envc.
  pose proof SO_ge. pose proof cl_par. pose proof (AUX_OFF_rng r).
  assert (L0 : 0 <= ρ (lenvar 0) <= 131071) by (destruct HF as (_ & _ & Hs3 & _); apply (Hs3 0); lia).
  destruct (lrange s (lvar (lenvar 0) 1)) as [[lo hi]|] eqn:E; [|discriminate].
  pose proof (lrange_sound ρ s _ Hs _ E) as R. rewrite leval_lvar in R. cbn [fst snd] in R.
  destruct ((0 <=? j) && (j <? lo)) eqn:E1.
  - injection H as <-. apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    split; [lia|]. split; [lia|]. rewrite rdB_one by lia. constructor; [|constructor].
    unfold B, SO, AUX_OFF. rewrite (R5_str0 r ph ρ HF j) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. unfold xb_bv', xb_z. rewrite Z_to_bv_unsigned.
    destruct HF as (_ & _ & Hs3 & _). destruct (Hs3 0 ltac:(pose proof cl_argc; lia)) as [_ Hb].
    specialize (Hb j ltac:(lia)). unfold smod, zbyte. cbn [teval]. rewrite wZ_zero. cbn [Z.of_nat Z.mul].
    rewrite Z.pow_0_r, Z.div_1_r. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite !Z.mod_small by (unfold two64; lia). lia.
  - destruct ((lo =? j) && (hi =? j)) eqn:E2; [|discriminate]. injection H as <-.
    apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3.
    split; [lia|]. split; [lia|]. rewrite rdB_one by lia. constructor; [|constructor].
    unfold B, SO, AUX_OFF. rewrite (R5_str0 r ph ρ HF j) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. unfold xb_bv', xb_z. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma str1_sound : forall j l, 2 <= ρ v_argc -> str_byte s 1 j = Some l -> cls_ok l (SO + ρ (lenvar 0) + 1 + j) 1.
Proof.
  intros j l H2 H. unfold str_byte in H. pose proof cl_len. pose proof cl_tx. pose proof (cl_len01 H2). pose proof cl_argc. pose proof cl_envc.
  pose proof SO_ge. pose proof cl_par. pose proof (AUX_OFF_rng r).
  assert (L0 : 0 <= ρ (lenvar 0) <= 131071) by (destruct HF as (_ & _ & Hs3 & _); apply (Hs3 0); lia).
  assert (L1 : 0 <= ρ (lenvar 1) <= 131071) by (destruct HF as (_ & _ & Hs3 & _); apply (Hs3 1); lia).
  destruct (lrange s (lvar (lenvar 1) 1)) as [[lo hi]|] eqn:E; [|discriminate].
  pose proof (lrange_sound ρ s _ Hs _ E) as R. rewrite leval_lvar in R. cbn [fst snd] in R.
  destruct ((0 <=? j) && (j <? lo)) eqn:E1.
  - injection H as <-. apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    split; [lia|]. split; [lia|]. rewrite rdB_one by lia. constructor; [|constructor].
    unfold B, SO, AUX_OFF. rewrite (R5_str1 r ph ρ HF H2 j) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. unfold xb_bv', xb_z. rewrite Z_to_bv_unsigned.
    destruct HF as (_ & _ & Hs3 & _). destruct (Hs3 1 ltac:(lia)) as [_ Hb].
    specialize (Hb j ltac:(lia)). unfold smod, zbyte. cbn [teval]. rewrite wZ_zero. cbn [Z.of_nat Z.mul].
    rewrite Z.pow_0_r, Z.div_1_r. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite !Z.mod_small by (unfold two64; lia). lia.
  - destruct ((lo =? j) && (hi =? j)) eqn:E2; [|discriminate]. injection H as <-.
    apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3.
    split; [lia|]. split; [lia|]. rewrite rdB_one by lia. constructor; [|constructor].
    unfold B, SO, AUX_OFF. rewrite (R5_str1 r ph ρ HF H2 j) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. unfold xb_bv', xb_z. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma auxv_slot_sound : forall (t n : nat), (t < 2 * auxv_count r)%nat -> (n <= 8)%nat ->
  Forall2 (xb_bv' ρ) (auxv_slot r ph t n) (rdB B (Z.to_nat (24 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * Z.of_nat t)) n).
Proof.
  intros t n Ht Hn. rewrite rdB_prefix by exact Hn.
  pose proof cl_argc. pose proof cl_envc.
  destruct (Nat.Even_or_Odd t) as [[i Hi]|[i Hi]]; subst t.
  - replace (Z.to_nat (24 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * Z.of_nat (2 * i)))
      with (24 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc) + 16 * i)%nat by lia.
    unfold B. rewrite (R4_key r ph ρ HF i) by lia.
    unfold auxv_slot. rewrite Nat.even_mul, Nat.div2_double. cbn [Nat.even orb].
    apply F2_lit; [exact Hn | rewrite u_zbv; reflexivity].
  - replace (Z.to_nat (24 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * Z.of_nat (2 * i + 1)))
      with (24 + 8 * Z.to_nat (ρ v_argc) + 8 * Z.to_nat (ρ v_envc) + 16 * i + 8)%nat by lia.
    unfold B. rewrite (R4_val r ph ρ HF i) by lia.
    unfold auxv_slot. replace (2 * i + 1)%nat with (S (2 * i)) by lia.
    rewrite Nat.even_succ, Nat.odd_mul, Nat.div2_succ_double. cbn [Nat.odd Nat.even andb negb].
    destruct r; cbn [auxv_count] in Ht;
    [do 29 (destruct i as [|i]; [cbn [auxv_val_slot]; unfold auxv_vals; cbn [nth app];
        first [ apply F2_lit; [exact Hn | rewrite u_zbv; reflexivity]
              | apply F2_form; [exact Hn | rewrite u_zbv; unfold smod; cbn [teval]; rewrite wZ_zero; f_equal; lia]
              | apply F2_form; [exact Hn | rewrite u_zbv, ?AUX_OFF_true, ?AUX_OFF_false, smod_lit by (unfold two64; lia);
                  unfold rnd_addr, xfn_addr, str_off, sp_val, sp_terms, t_aep, t_xfn;
                  rewrite ?auxv_size_true, ?auxv_size_false; cbn [teval app]; f_equal; lia] ] |]); lia
    | do 27 (destruct i as [|i];
      [ cbn [auxv_val_slot]; unfold auxv_vals; cbn [nth app];
        first [ apply F2_lit; [exact Hn | rewrite u_zbv; reflexivity]
              | apply F2_form; [exact Hn | rewrite u_zbv; unfold smod; cbn [teval]; rewrite wZ_zero; f_equal; lia]
              | apply F2_form; [exact Hn | rewrite u_zbv, ?AUX_OFF_true, ?AUX_OFF_false, smod_lit by (unfold two64; lia);
                  unfold rnd_addr, xfn_addr, str_off, sp_val, sp_terms, t_aep, t_xfn;
                  rewrite ?auxv_size_true, ?auxv_size_false; cbn [teval app]; f_equal; lia] ]
      |]); lia].
Qed.

Lemma cls_sound : forall (d : lin) (n : nat) (l : list xb), eb_cls r ph s d n = Some l -> cls_ok l (leval ρ d) n.
Proof.
  intros [c td] n l H. unfold eb_cls in H. cbn [fst snd] in H.
  pose proof cl_argc. pose proof cl_envc. pose proof cl_len. pose proof cl_tx. pose proof cl_len0. pose proof SO_ge. pose proof cl_par. pose proof (AUX_OFF_rng r).
  assert (L0 : 0 <= ρ (lenvar 0) <= 131071) by (destruct HF as (_ & _ & Hs3 & _); apply (Hs3 0); lia).
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hr0 & Hr1 & _).
  destruct (Nat.eqb_spec n 0) as [->|Hn0]; [discriminate|].
  destruct td as [|t0 tr].
  - (* [comment removed for export] *)
    unfold leval. cbn [fst snd teval]. rewrite Z.add_0_r.
    destruct ((c =? 0) && (n <=? 8)%nat) eqn:E0.
    + apply andb_prop in E0 as [E0 E0']. apply Z.eqb_eq in E0. apply Nat.leb_le in E0'. subst c. injection H as <-.
      split; [lia|]. split; [lia|]. change (Z.to_nat 0) with 0%nat. rewrite rdB_prefix by exact E0'.
      unfold B. rewrite (R1_argc r ph ρ HF). apply F2_form; [exact E0'|]. rewrite u_zbv. unfold smod. cbn [teval].
      rewrite wZ_zero. f_equal. lia.
    + destruct ((c =? 8) && (n <=? 8)%nat) eqn:E8.
      * apply andb_prop in E8 as [E8 E8']. apply Z.eqb_eq in E8. apply Nat.leb_le in E8'. subst c. injection H as <-.
        split; [lia|]. split; [lia|]. change (Z.to_nat 8) with 8%nat. rewrite rdB_prefix by exact E8'.
        unfold B. rewrite (R2_argv0 r ph ρ HF). apply F2_form; [exact E8'|]. rewrite u_zbv.
        rewrite smod_lit by (unfold two64; lia). unfold AUX_OFF, str_off, sp_val, sp_terms, t_aeg; cbn [teval app]. f_equal. lia.
      * destruct ((c =? 16) && (n <=? 8)%nat) eqn:E16; [|discriminate].
        apply andb_prop in E16 as [E16 E16']. apply Z.eqb_eq in E16. apply Nat.leb_le in E16'. subst c.
        split; [lia|]. split; [lia|]. change (Z.to_nat 16) with 16%nat. rewrite rdB_prefix by exact E16'.
        destruct (argc_ge2 s) eqn:G2.
        -- injection H as <-. pose proof (argc_ge2_sound G2) as HA2.
           unfold B. rewrite (R2_argv1 r ph ρ HF HA2). apply F2_form; [exact E16'|]. rewrite u_zbv.
           rewrite smod_lit by (unfold two64; lia). unfold AUX_OFF, str_off, sp_val, sp_terms, t_aeg0; cbn [teval app]. f_equal. lia.
        -- destruct (argc_is1 s) eqn:G1; [|discriminate]. injection H as <-. pose proof (argc_is1_sound G1) as HA1.
           unfold B. rewrite (R2_argv1_null r ph ρ HF HA1). apply F2_zero. exact E16'.
  -
    destruct (teqb (t0 :: tr) t_ae) eqn:Eae.
    + apply teqb_eq in Eae. rewrite Eae in *. unfold leval. cbn [fst snd]. unfold t_ae. cbn [teval].
      destruct ((24 <=? c) && (c <? AUX_OFF r) && ((c - 24) mod 8 =? 0) && (n <=? 8)%nat) eqn:Ea; [|discriminate].
      injection H as <-. apply andb_prop in Ea as [Ea Ea4]. apply andb_prop in Ea as [Ea Ea3]. apply andb_prop in Ea as [Ea1 Ea2].
      apply Z.leb_le in Ea1. apply Z.ltb_lt in Ea2. apply Z.eqb_eq in Ea3. apply Nat.leb_le in Ea4.
      set (t := Z.to_nat ((c - 24) / 8)).
      assert (Ht : c = 24 + 8 * Z.of_nat t).
      { unfold t. pose proof (Z.div_mod (c - 24) 8 ltac:(lia)). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
      assert (Ht58 : (t < 2 * auxv_count r)%nat) by (unfold AUX_OFF, auxv_size in Ea2; lia).
      split; [lia|]. split; [lia|].
      replace (Z.to_nat (c + (8 * ρ v_argc + (8 * ρ v_envc + 0)))) with (Z.to_nat (24 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * Z.of_nat t))
        by lia.
      apply auxv_slot_sound; assumption.
    + destruct (teqb (t0 :: tr) t_aeg) eqn:Eg.
      * apply teqb_eq in Eg. rewrite Eg in *. unfold leval. cbn [fst snd]. unfold t_aeg. cbn [teval].
        destruct ((AUX_OFF r <=? c) && (n =? 1)%nat) eqn:Es; [|discriminate].
        apply andb_prop in Es as [Es1 Es2]. apply Z.leb_le in Es1. apply Nat.eqb_eq in Es2. subst n.
        pose proof (str0_sound (c - AUX_OFF r) l H) as HS.
        replace (c + (8 * ρ v_argc + (8 * ρ v_envc + (1 * ρ v_g + 0)))) with (SO + (c - AUX_OFF r)) by (unfold SO, str_off; lia). exact HS.
      * destruct (teqb (t0 :: tr) t_aeg0) eqn:Eg0.
        -- apply teqb_eq in Eg0. rewrite Eg0 in *. unfold leval. cbn [fst snd]. unfold t_aeg0. cbn [teval].
           destruct ((AUX_OFF r + 1 <=? c) && (n =? 1)%nat && argc_ge2 s) eqn:Es.
           ++ apply andb_prop in Es as [Es G2]. apply andb_prop in Es as [Es1 Es2]. apply Z.leb_le in Es1. apply Nat.eqb_eq in Es2.
              subst n. pose proof (argc_ge2_sound G2) as HA2.
              pose proof (str1_sound (c - (AUX_OFF r + 1)) l HA2 H) as HS.
              replace (c + (8 * ρ v_argc + (8 * ρ v_envc + (1 * ρ v_g + (1 * ρ (lenvar 0) + 0)))))
                with (SO + ρ (lenvar 0) + 1 + (c - (AUX_OFF r + 1))) by (unfold SO, str_off; lia). exact HS.
           ++ destruct ((c =? AUX_OFF r) && (n =? 1)%nat) eqn:Ez; [|discriminate]. injection H as <-.
              apply andb_prop in Ez as [Ez1 Ez2]. apply Z.eqb_eq in Ez1. apply Nat.eqb_eq in Ez2. subst c n.
              replace (AUX_OFF r + (8 * ρ v_argc + (8 * ρ v_envc + (1 * ρ v_g + (1 * ρ (lenvar 0) + 0)))))
                with (SO + ρ (lenvar 0)) by (unfold SO, str_off; lia).
              split; [lia|]. split; [cbn [Z.of_nat Pos.of_succ_nat]; lia|]. rewrite rdB_one by lia. constructor; [|constructor].
              unfold B, SO, AUX_OFF. rewrite (R5_str0 r ph ρ HF (ρ (lenvar 0))) by lia.
              rewrite Z.ltb_irrefl. unfold xb_bv', xb_z. rewrite Z_to_bv_unsigned. reflexivity.
        -- destruct (teqb (t0 :: tr) t_aeg01) eqn:Eg01.
           ++ apply teqb_eq in Eg01. rewrite Eg01 in *. unfold leval. cbn [fst snd]. unfold t_aeg01. cbn [teval].
              destruct ((c =? AUX_OFF r + 1) && (n =? 1)%nat && argc_ge2 s) eqn:Ez; [|discriminate]. injection H as <-.
              apply andb_prop in Ez as [Ez G2]. apply andb_prop in Ez as [Ez1 Ez2]. apply Z.eqb_eq in Ez1. apply Nat.eqb_eq in Ez2.
              subst c n. pose proof (argc_ge2_sound G2) as HA2. pose proof (cl_len01 HA2).
              assert (L1 : 0 <= ρ (lenvar 1) <= 131071).
              { pose proof cl_argc. destruct HF as (_ & _ & Hs3 & _). apply (Hs3 1). lia. }
              replace (AUX_OFF r + 1 + (8 * ρ v_argc + (8 * ρ v_envc + (1 * ρ v_g + (1 * ρ (lenvar 0) + (1 * ρ (lenvar 1) + 0))))))
                with (SO + ρ (lenvar 0) + 1 + ρ (lenvar 1)) by (unfold SO, str_off; lia).
              split; [lia|]. split; [cbn [Z.of_nat Pos.of_succ_nat]; lia|]. rewrite rdB_one by lia. constructor; [|constructor].
              unfold B, SO, AUX_OFF. rewrite (R5_str1 r ph ρ HF HA2 (ρ (lenvar 1))) by lia.
              rewrite Z.ltb_irrefl. unfold xb_bv', xb_z. rewrite Z_to_bv_unsigned. reflexivity.
           ++ destruct (teqb (t0 :: tr) t_aep) eqn:Ep; [|discriminate].
              apply teqb_eq in Ep. rewrite Ep in *. unfold leval. cbn [fst snd]. unfold t_aep. cbn [teval].
              destruct ((AUX_OFF r <=? c) && (c - AUX_OFF r + Z.of_nat n <=? 16)) eqn:Er; [|discriminate]. injection H as <-.
              apply andb_prop in Er as [Er1 Er2]. apply Z.leb_le in Er1. apply Z.leb_le in Er2.
              split; [lia|]. split; [lia|].
              assert (HR : rdB B (Z.to_nat (c + (8 * ρ v_argc + (8 * ρ v_envc + (8 * ρ v_par + 0))))) n
                           = firstn n (skipn (Z.to_nat (c - AUX_OFF r)) (word_le8 (Z_to_bv 64 (ρ v_r0)) ++ word_le8 (Z_to_bv 64 (ρ v_r1))))).
              { rewrite <- (R6_random r ph ρ HF). fold B. unfold rdB. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
                replace (Nat.min n (16 - Z.to_nat (c - AUX_OFF r))) with n by lia. f_equal. f_equal. unfold AUX_OFF in *. lia. }
              rewrite HR. apply F2_nth.
              ** rewrite length_map, length_seq, length_firstn, length_skipn, length_app, !length_n_to_le_8. lia.
              ** intros j Hj. rewrite length_map, length_seq in Hj. rewrite nth_seq_map by exact Hj.
                 rewrite nth_firstn, (proj2 (Nat.ltb_lt _ _) Hj), nth_skipn. unfold xb_bv', xb_z.
                 destruct (Nat.ltb_spec (Z.to_nat (c - AUX_OFF r) + j) 8) as [Lt|Ge].
                 --- rewrite app_nth1 by (rewrite length_n_to_le_8; exact Lt). rewrite nth_word_le8 by exact Lt.
                     rewrite u_zbv. unfold smod. cbn [teval]. rewrite wZ_zero. f_equal. rewrite !Z.mod_small by (unfold two64; lia). lia.
                 --- rewrite app_nth2 by (rewrite length_n_to_le_8; exact Ge). rewrite length_n_to_le_8.
                     rewrite nth_word_le8 by lia. rewrite u_zbv. unfold smod. cbn [teval]. rewrite wZ_zero. f_equal.
                     rewrite !Z.mod_small by (unfold two64; lia). lia.
Qed.

Lemma eb_canon_sound : forall ts : terms, teval ρ ts = fst (eb_canon s ts) + teval ρ (snd (eb_canon s ts)).
Proof.
  induction ts as [|[x a] ts' IH]; [reflexivity|]. cbn [eb_canon teval].
  destruct (eb_pin s x) as [z|] eqn:Ep; cbn [fst snd teval]; [|lia].
  unfold eb_pin in Ep. destruct (vbound s x) as [[lo hi]|] eqn:E; [|discriminate].
  destruct (Z.eqb_spec lo hi) as [->|]; [|discriminate]. injection Ep as <-.
  pose proof (vbound_sound ρ s x Hs _ E) as Hb. cbn [fst snd] in Hb. assert (ρ x = hi) by lia. nia.
Qed.

Lemma rebase_sound : forall (d d' : lin) (T : terms), rebase s d T = Some d' -> leval ρ d' = leval ρ d.
Proof.
  intros d d' T H. unfold rebase in H. destruct (teqb (snd (eb_canon s (snd d))) (snd (eb_canon s T))) eqn:E; [|discriminate].
  injection H as <-. apply teqb_eq in E. unfold leval. cbn [fst snd].
  rewrite (eb_canon_sound (snd d)), (eb_canon_sound T), E. lia.
Qed.

Lemma try_sound : forall (d : lin) (n : nat) (pats : list terms) (l : list xb), eb_try r ph s d n pats = Some l -> cls_ok l (leval ρ d) n.
Proof.
  intros d n pats. induction pats as [|T pats' IH]; intros l H; [discriminate|]. cbn [eb_try] in H.
  destruct (rebase s d T) as [d'|] eqn:Er.
  - destruct (eb_cls r ph s d' n) as [l'|] eqn:Ec; [|exact (IH l H)]. injection H as <-.
    rewrite <- (rebase_sound d d' T Er). exact (cls_sound d' n l' Ec).
  - exact (IH l H).
Qed.

End Cls.

Lemma rd_block : forall (segs : list Segment) (r : bool) ph ρ m nR (n : nat) (z0 : Z) (a : word),
  eb_rel r ph ρ m (sp_val ρ) nR -> 0 <= z0 -> z0 + Z.of_nat n <= Z.of_nat (length (eb_image r ph ρ)) ->
  bv_unsigned a = sp_val ρ + z0 ->
  rdn segs m a n = Some (rdB (eb_image r ph ρ) (Z.to_nat z0) n).
Proof.
  intros segs r ph ρ m nR n. induction n as [|n IH]; intros z0 a Hrel Hz Hzn Ha; [reflexivity|].
  destruct Hrel as (HF & Hb & HnR & Hm).
  assert (Hsp : sp_val ρ + Z.of_nat (length (eb_image r ph ρ)) <= sp_window_hi).
  { rewrite (R7_length r ph ρ HF). pose proof (facts_win r (mkPhdrInfo 0 0 0) ρ HF) as [_ H2]. unfold dec_top, str_off, AUX_OFF in *. lia. }
  assert (Hsp0 : 0 <= sp_val ρ) by (pose proof (facts_win r (mkPhdrInfo 0 0 0) ρ HF) as [H1 _]; unfold sp_window_lo in H1; lia).
  unfold sp_window_hi in Hsp.
  cbn [rdn]. assert (Ea : a = Z_to_bv 64 (sp_val ρ + z0)) by (apply bv_eq; rewrite Ha, Z_to_bv_unsigned; symmetry; apply bv_wrap_small;
                                                             change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite Ea, (Hm z0) by lia.
  rewrite (IH (z0 + 1)); [ | split; [exact HF|]; split; [exact Hb|]; split; [exact HnR | exact Hm] | lia | lia | ].
  2:{ rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_unsigned 1) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l.
      change (bv_modulus 64) with (2 ^ 64). replace (sp_val ρ + (z0 + 1)) with (sp_val ρ + z0 + 1) by lia.
      apply Z.mod_small. lia. }
  f_equal. unfold rdB. replace (Z.to_nat (z0 + 1)) with (S (Z.to_nat z0)) by lia.
  assert (HL : (Z.to_nat z0 < length (eb_image r ph ρ))%nat) by lia.
  revert HL. generalize (eb_image r ph ρ) as B. generalize (Z.to_nat z0) as k. clear.
  induction k as [|k IHk]; intros [|b B] HL; cbn in HL; try lia; [reflexivity|].
  cbn [skipn nth]. apply IHk. lia.
Qed.

Theorem eb_load_sound : forall (segs : list Segment) (r : bool) (ph : PhdrInfo) (ρ : valuation) (s : store)
                               (m : word -> option byte) (nR : Z) (v : xv) (a : word) (n : nat) (l : list xb),
  sat ρ s -> eb_rel r ph ρ m (sp_val ρ) nR -> xv_val ρ v a -> eb_load r ph s v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv' ρ) l bs.
Proof.
  intros segs r ph ρ s m nR v a n l Hs Hrel Hv H.
  unfold eb_load in H. destruct (eaddr v) as [[ts o]|] eqn:Ev; [|discriminate].
  set (d := lsub (wS o, ts) (0, sp_terms)) in *.
  assert (Hcls : cls_ok r ph ρ l (leval ρ d) n).
  { cbv zeta in H. fold d in H. destruct (eb_cls r ph s d n) as [l0|] eqn:Ec.
    - injection H as <-. exact (cls_sound r ph ρ s Hs (proj1 Hrel) d n l0 Ec).
    - exact (try_sound r ph ρ s Hs (proj1 Hrel) d n eb_pats l H). }
  destruct Hcls as (Hz & Hzn & HF2).
  assert (Hd : leval ρ d = wS o + teval ρ ts - sp_val ρ).
  { unfold d. rewrite leval_lsub. unfold leval, sp_val. cbn [fst snd]. lia. }
  assert (Ha : bv_unsigned a = smod ρ ts o).
  { destruct v as [x|ts' o'| | | |]; cbn [eaddr] in Ev; try discriminate; injection Ev as <- <-; cbn [xv_val] in Hv.
    - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
    - exact Hv. }
  assert (Hsp : sp_val ρ + Z.of_nat (length (eb_image r ph ρ)) <= sp_window_hi).
  { destruct Hrel as (HF & _). rewrite (R7_length r ph ρ HF). pose proof (facts_win r (mkPhdrInfo 0 0 0) ρ HF) as [_ H2]. unfold dec_top, str_off, AUX_OFF in *. lia. }
  assert (Hsp0 : 0 <= sp_val ρ).
  { destruct Hrel as (HF & _). pose proof (facts_win r (mkPhdrInfo 0 0 0) ρ HF) as [H1 _]. unfold sp_window_lo in H1. lia. }
  assert (Ha' : bv_unsigned a = sp_val ρ + leval ρ d).
  { rewrite Ha. unfold smod. rewrite <- (wS_mod o). rewrite Z.add_mod_idemp_r by (unfold two64; lia).
    rewrite Hd. replace (teval ρ ts + wS o) with (sp_val ρ + (wS o + teval ρ ts - sp_val ρ)) by lia.
    apply Z.mod_small. unfold sp_window_hi, two64 in *. lia. }
  exists (rdB (eb_image r ph ρ) (Z.to_nat (leval ρ d)) n). split; [|exact HF2].
  apply (rd_block segs r ph ρ m nR n (leval ρ d) a Hrel Hz Hzn Ha').
Qed.

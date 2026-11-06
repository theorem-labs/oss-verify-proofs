(* CrtEnc: the image-free part of the braid/encoder math of check_round_trip: the rb_* write-list arithmetic of
   lib/Prog/RcBraid.v, memcmp_model, crt_K and nth_seq0, plus (re-exported) lib/Lib/CrtS24.v's 24-bit sample s24
   and its bytes. No item names an image, a segment list or an address, so every image's check_round_trip proof
   can Require this file as is.

   This file loads lib/Prog/RcBraidLib.v, whose global `Ltac exec_pre ::=` / `Ltac post_step ::= idtac`
   (RcBraidLib.v:18, :48) break FP steps in every file that loads it. A file with FP steps Requires
   lib/Lib/CrtS24.v instead.

   PORT of a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:1-355 (the
   image-A record; its image-A part is lib/A/Prog/crtA_enc.v, and its sample lemmas are in lib/Lib/CrtS24.v), plus
   the items that file took from
   a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Spec/StrFun.v (memcmp_model and its
   lemma). Each block below cites its source lines. Lemma names, statements and proofs are the record's; only the
   imports differ (no lib/A file, no StrFun, no crt_convert). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Export CrtS24.
(* rb_byte moved to lib/Lib/CrtS24.v. The alias keeps image B's qualified name CrtEnc.rb_byte
   (lib/B/Prog/crtB_encbcmp.v:147, :149, module CE) resolving after the CrtS24 split; it is the same constant. *)
Notation rb_byte := CrtS24.rb_byte (only parsing).
Import ListNotations.
Open Scope Z_scope.

(* memcmp_model: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Spec/StrFun.v:169-177. *)
Fixpoint memcmp_model (l r : list byte) (n : nat) {struct n} : option Z :=
  match n with
  | O => Some 0
  | S n' =>
      match l, r with
      | a :: l', b :: r' => if bv_unsigned a =? bv_unsigned b then memcmp_model l' r' n' else Some (bv_unsigned a - bv_unsigned b)
      | _, _ => None
      end
  end.

(* memcmp_model_total: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Spec/StrFun.v:179-183. *)
Lemma memcmp_model_total : forall l r n, (n <= length l)%nat -> (n <= length r)%nat -> exists v, memcmp_model l r n = Some v.
Proof.
  intros l r n; revert l r; induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia; try (eexists; reflexivity).
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia| eexists; reflexivity].
Qed.

(* rbx_one .. rb_at: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:11-44. *)
Lemma rbx_one : forall (m : word -> option byte) y b (x : word), 0 <= y < 2^64 ->
  write_to_mem m (wa y) [b] x = if bv_unsigned x =? y then Some b else m x.
Proof.
  intros m y b x Hy. rewrite write_to_mem_spec by (cbn [length]; lia).
  change (Z.of_nat (length [b])) with 1.
  destruct (Z.eqb_spec (bv_unsigned x) y) as [E|E].
  - rewrite E, Z.leb_refl. replace (y <? y + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Z.sub_diag. reflexivity.
  - destruct (Z.leb_spec y (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (y + 1)); cbn [andb];
      try reflexivity. lia.
Qed.

Lemma rb_enc_cons : forall m e L, rb_enc m (e :: L) = rb_enc (write_to_mem m (wa (fst e)) [snd e]) L.
Proof. reflexivity. Qed.

Lemma rb_enc_notin : forall L m (x : word),
  (forall e, In e L -> 0 <= fst e < 2^64 /\ bv_unsigned x <> fst e) -> rb_enc m L x = m x.
Proof.
  induction L as [|e L IH]; intros m x H; [reflexivity|].
  rewrite rb_enc_cons, IH by (intros e' He'; apply H; right; exact He').
  destruct (H e (or_introl eq_refl)) as [R N]. rewrite rbx_one by exact R.
  apply Z.eqb_neq in N. rewrite N. reflexivity.
Qed.

Lemma rb_enc_hit : forall L1 e L2 m (x : word), bv_unsigned x = fst e -> 0 <= fst e < 2^64 ->
  (forall e', In e' L2 -> 0 <= fst e' < 2^64 /\ bv_unsigned x <> fst e') ->
  rb_enc m (L1 ++ e :: L2) x = Some (snd e).
Proof.
  intros L1 e L2 m x E R H. rewrite rb_enc_app, rb_enc_cons, rb_enc_notin by exact H.
  rewrite rbx_one by exact R. rewrite E, Z.eqb_refl. reflexivity.
Qed.

Definition rb_off (p j : Z) : Z := if j =? 0 then 3 + p else if j =? 1 then 5 * p else 1 + p.
Definition rb_at (N s c j : Z) : Z := if j =? 0 then rb_lo N s c else if j =? 1 then rb_mid N s c else rb_hi N s c.

(* rb_at_eq .. rb_cover: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:46-221 (crt_enc.v:45, rb_byte, is in lib/Lib/CrtS24.v). *)
Lemma rb_at_eq : forall N s c j, 0 <= c -> rb_at N s c j = 3 * (s * N) + 6 * (c / 2) + rb_off (c mod 2) j.
Proof.
  intros N s c j Hc. unfold rb_at, rb_off, rb_lo, rb_mid, rb_hi, rb_G.
  pose proof (Z.div_mod c 2 ltac:(lia)) as D.
  destruct (j =? 0); [|destruct (j =? 1)]; lia.
Qed.

Lemma rb_off_rng : forall p j, 0 <= p <= 1 -> 0 <= rb_off p j <= 5.
Proof. intros p j Hp. unfold rb_off. destruct (j =? 0); [|destruct (j =? 1)]; lia. Qed.

Lemma rb_off_inj : forall p p' j j', 0 <= p <= 1 -> 0 <= p' <= 1 -> 0 <= j < 3 -> 0 <= j' < 3 ->
  rb_off p j = rb_off p' j' -> p = p' /\ j = j'.
Proof.
  intros p p' j j' Hp Hp' Hj Hj' E. unfold rb_off in E.
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia. assert (C' : j' = 0 \/ j' = 1 \/ j' = 2) by lia.
  destruct C as [-> | [-> | ->]]; destruct C' as [-> | [-> | ->]]; cbn in E; lia.
Qed.

Lemma rb_turn_in : forall a N s c x e, In e (rb_turn a N s c x) ->
  exists j, 0 <= j < 3 /\ fst e = a + rb_at N s c j.
Proof.
  intros a N s c x e H. cbn [rb_turn In] in H.
  destruct H as [<-|[<-|[<-|[]]]]; [exists 0 | exists 1 | exists 2]; split; try lia; reflexivity.
Qed.

Lemma rb_row_in : forall a N K s n e, In e (rb_row a N K s n) ->
  exists c j, 0 <= c < Z.of_nat n /\ 0 <= j < 3 /\ fst e = a + rb_at N s c j.
Proof.
  intros a N K s n. induction n as [|n IH]; intros e H; cbn [rb_row] in H; [destruct H|].
  apply in_app_or in H as [H|H].
  - destruct (IH e H) as (c & j & Hc & Hj & E). exists c, j. split; [lia|]. split; assumption.
  - destruct (rb_turn_in _ _ _ _ _ _ H) as (j & Hj & E). exists (Z.of_nat n), j. split; [lia|]. split; assumption.
Qed.

Lemma rb_turn_at : forall a N s c x m j, 0 <= c -> 0 <= a + 3 * (s * N) -> a + 3 * (s * N) + 6 * (c / 2) + 6 <= 2^64 ->
  0 <= j < 3 ->
  rb_enc m (rb_turn a N s c x) (wa (a + rb_at N s c j)) = Some (Z_to_bv 8 (rb_byte x j)).
Proof.
  intros a N s c x m j Hc H0 H1 Hj.
  pose proof (Z.div_pos c 2 ltac:(lia) ltac:(lia)) as Q.
  assert (P : 0 <= c mod 2 <= 1) by (pose proof (Z.mod_pos_bound c 2 ltac:(lia)); lia).
  assert (A : forall j', 0 <= j' < 3 -> 0 <= a + rb_at N s c j' < 2^64).
  { intros j' Hj'. rewrite rb_at_eq by lia. pose proof (rb_off_rng (c mod 2) j' P). lia. }
  assert (D : forall j', 0 <= j' < 3 -> j' <> j -> a + rb_at N s c j <> a + rb_at N s c j').
  { intros j' Hj' Hne E. rewrite !rb_at_eq in E by lia.
    destruct (rb_off_inj (c mod 2) (c mod 2) j j' P P Hj Hj' ltac:(lia)). lia. }
  assert (U : bv_unsigned (wa (a + rb_at N s c j)) = a + rb_at N s c j) by (apply wa_unsigned; apply A; exact Hj).
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct C as [-> | [-> | ->]].
  - change (rb_turn a N s c x) with ([] ++ (a + rb_at N s c 0, Z_to_bv 8 (x mod 256)) ::
      [(a + rb_at N s c 1, Z_to_bv 8 (x / 256 mod 256)); (a + rb_at N s c 2, Z_to_bv 8 (x / 65536))]).
    apply rb_enc_hit; [exact U | apply A; lia |].
    intros e' [<-|[<-|[]]]; cbn [fst]; (split; [apply A; lia | rewrite U; apply D; lia]).
  - change (rb_turn a N s c x) with ([(a + rb_at N s c 0, Z_to_bv 8 (x mod 256))] ++
      (a + rb_at N s c 1, Z_to_bv 8 (x / 256 mod 256)) :: [(a + rb_at N s c 2, Z_to_bv 8 (x / 65536))]).
    apply rb_enc_hit; [exact U | apply A; lia |].
    intros e' [<-|[]]; cbn [fst]; (split; [apply A; lia | rewrite U; apply D; lia]).
  - change (rb_turn a N s c x) with ([(a + rb_at N s c 0, Z_to_bv 8 (x mod 256));
      (a + rb_at N s c 1, Z_to_bv 8 (x / 256 mod 256))] ++ (a + rb_at N s c 2, Z_to_bv 8 (x / 65536)) :: []).
    apply rb_enc_hit; [exact U | apply A; lia |].
    intros e' [].
Qed.

Lemma rb_row_at : forall a N K s n m ch j, 0 <= a -> 0 <= s -> 2 <= N -> N mod 2 = 0 -> Z.of_nat n <= N ->
  a + 3 * (s * N) + 3 * N <= 2^64 -> 0 <= ch < Z.of_nat n -> 0 <= j < 3 ->
  rb_enc m (rb_row a N K s n) (wa (a + rb_at N s ch j)) = Some (Z_to_bv 8 (rb_byte (K s ch mod 2^24) j)).
Proof.
  intros a N K s n m ch j Ha Hs HN HE Hn Hb Hch Hj.
  assert (SN : 0 <= s * N) by (apply Z.mul_nonneg_nonneg; lia).
  induction n as [|n IH]; [lia|].
  cbn [rb_row]. rewrite rb_enc_app.
  destruct (Z.eq_dec ch (Z.of_nat n)) as [->|Hne].
  - apply rb_turn_at; try lia.
  - rewrite rb_enc_notin.
    + apply IH; lia.
    + intros e He. destruct (rb_turn_in _ _ _ _ _ _ He) as (j' & Hj' & E). rewrite E.
      assert (Hch' : 0 <= ch < Z.of_nat n) by lia.
      pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as M1.
      pose proof (Z.mod_pos_bound (Z.of_nat n) 2 ltac:(lia)) as M2.
      assert (B1 : 0 <= ch / 2 /\ 6 * (ch / 2) + 6 <= 3 * N /\ ch = 2 * (ch / 2) + ch mod 2).
      { pose proof (Z.div_mod ch 2 ltac:(lia)). pose proof (Z.div_pos ch 2 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_mod N 2 ltac:(lia)). lia. }
      assert (B2 : 0 <= Z.of_nat n / 2 /\ 6 * (Z.of_nat n / 2) + 6 <= 3 * N /\
                   Z.of_nat n = 2 * (Z.of_nat n / 2) + Z.of_nat n mod 2).
      { pose proof (Z.div_mod (Z.of_nat n) 2 ltac:(lia)). pose proof (Z.div_pos (Z.of_nat n) 2 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_mod N 2 ltac:(lia)). lia. }
      pose proof (rb_off_rng (ch mod 2) j ltac:(lia)) as O1.
      pose proof (rb_off_rng (Z.of_nat n mod 2) j' ltac:(lia)) as O2.
      pose proof (rb_off_inj (ch mod 2) (Z.of_nat n mod 2) j j' ltac:(lia) ltac:(lia) Hj Hj') as INJ.
      rewrite !rb_at_eq by lia.
      set (X := s * N) in *. set (U := ch / 2) in *. set (V := Z.of_nat n / 2) in *.
      set (p1 := ch mod 2) in *. set (p2 := Z.of_nat n mod 2) in *.
      set (o1 := rb_off p1 j) in *. set (o2 := rb_off p2 j') in *.
      clearbody X U V p1 p2 o1 o2. clear IH He E.
      split; [lia|].
      rewrite wa_unsigned by lia.
      intros EQ.
      destruct (Z.eq_dec U V) as [Q|Q]; [|lia].
      assert (EO : o1 = o2) by lia. destruct (INJ EO) as [I1 I2]. lia.
Qed.

Lemma rb_rows_at : forall a N K f m s ch j, 0 <= a -> 2 <= N -> N mod 2 = 0 ->
  a + 3 * N * Z.of_nat f <= 2^64 -> 0 <= s < Z.of_nat f -> 0 <= ch < N -> 0 <= j < 3 ->
  rb_enc m (rb_rows a N K f) (wa (a + rb_at N s ch j)) = Some (Z_to_bv 8 (rb_byte (K s ch mod 2^24) j)).
Proof.
  intros a N K f m s ch j Ha HN HE Hb Hs Hch Hj.
  assert (NE : N = 2 * (N / 2)) by (pose proof (Z.div_mod N 2 ltac:(lia)); lia).
  induction f as [|f IH]; [lia|].
  cbn [rb_rows]. rewrite rb_enc_app.
  assert (FF : Z.of_nat (S f) * N = Z.of_nat f * N + N) by lia.
  assert (SF0 : 0 <= Z.of_nat f * N) by (apply Z.mul_nonneg_nonneg; lia).
  assert (HB' : a + 3 * (Z.of_nat f * N) + 3 * N <= 2^64) by lia.
  destruct (Z.eq_dec s (Z.of_nat f)) as [->|Hne].
  - apply rb_row_at; try lia.
  - assert (Hs' : 0 <= s < Z.of_nat f) by lia.
    assert (SF2 : (s + 1) * N <= Z.of_nat f * N) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (SN : 0 <= s * N) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SF3 : s * N + N <= Z.of_nat f * N) by lia.
    rewrite rb_enc_notin.
    + apply IH; [lia | exact Hs'].
    + intros e He. destruct (rb_row_in _ _ _ _ _ _ He) as (c & j' & Hc & Hj' & E). rewrite E.
      rewrite Z2Nat.id in Hc by lia.
      pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as M2.
      assert (B1 : 0 <= 6 * (ch / 2) /\ 6 * (ch / 2) + 6 <= 3 * N).
      { pose proof (Z.div_mod ch 2 ltac:(lia)). pose proof (Z.div_pos ch 2 ltac:(lia) ltac:(lia)). lia. }
      assert (B2 : 0 <= 6 * (c / 2) /\ 6 * (c / 2) + 6 <= 3 * N).
      { pose proof (Z.div_mod c 2 ltac:(lia)). pose proof (Z.div_pos c 2 ltac:(lia) ltac:(lia)). lia. }
      pose proof (rb_off_rng (ch mod 2) j ltac:(lia)) as O1. pose proof (rb_off_rng (c mod 2) j' ltac:(lia)) as O2.
      rewrite !rb_at_eq by lia.
      set (X := s * N) in *. set (Y := Z.of_nat f * N) in *.
      set (U := 6 * (ch / 2)) in *. set (V := 6 * (c / 2)) in *.
      set (o1 := rb_off (ch mod 2) j) in *. set (o2 := rb_off (c mod 2) j') in *.
      clearbody X Y U V o1 o2. clear IH He E.
      split; [lia|].
      rewrite wa_unsigned by lia.
      lia.
Qed.

Lemma rb_cover : forall N ns i, 2 <= N -> N mod 2 = 0 -> 1 <= ns -> 0 <= i < 3 * N * ns ->
  exists s ch j, 0 <= s < ns /\ 0 <= ch < N /\ 0 <= j < 3 /\ i = rb_at N s ch j.
Proof.
  intros N ns i HN HE Hns Hi.
  assert (NE : N = 2 * (N / 2)) by (pose proof (Z.div_mod N 2 ltac:(lia)); lia).
  set (h := N / 2) in *.
  set (s := i / (3 * N)). set (r := i mod (3 * N)).
  assert (Di : i = 3 * N * s + r) by (apply Z.div_mod; lia).
  assert (Rr : 0 <= r < 3 * N) by (apply Z.mod_pos_bound; lia).
  assert (Rs : 0 <= s < ns).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  set (p := r / 6). set (w := r mod 6).
  assert (Dr : r = 6 * p + w) by (apply Z.div_mod; lia).
  assert (Rw : 0 <= w < 6) by (apply Z.mod_pos_bound; lia).
  assert (Rp : 0 <= p < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (E3 : 3 * N * s = 3 * (s * N)) by ring.
  assert (C : w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5) by lia.
  assert (PE : forall q, (2 * q) / 2 = q /\ (2 * q) mod 2 = 0).
  { intros q. rewrite Z.mul_comm. split; [apply Z.div_mul; lia | apply Z.mod_mul; lia]. }
  assert (PO : forall q, (2 * q + 1) / 2 = q /\ (2 * q + 1) mod 2 = 1).
  { intros q. rewrite Z.mul_comm. split.
    - rewrite Z.div_add_l by lia. change (1 / 2) with 0. lia.
    - rewrite Z.add_comm, Z.mod_add by lia. reflexivity. }
  destruct C as [C|[C|[C|[C|[C|C]]]]].
  - exists s, (2 * p), 1. destruct (PE p) as [P1 P2].
    split; [exact Rs|]. split; [lia|]. split; [lia|]. rewrite rb_at_eq, P1, P2 by lia. unfold rb_off. cbn. lia.
  - exists s, (2 * p), 2. destruct (PE p) as [P1 P2].
    split; [exact Rs|]. split; [lia|]. split; [lia|]. rewrite rb_at_eq, P1, P2 by lia. unfold rb_off. cbn. lia.
  - exists s, (2 * p + 1), 2. destruct (PO p) as [P1 P2].
    split; [exact Rs|]. split; [lia|]. split; [lia|]. rewrite rb_at_eq, P1, P2 by lia. unfold rb_off. cbn. lia.
  - exists s, (2 * p), 0. destruct (PE p) as [P1 P2].
    split; [exact Rs|]. split; [lia|]. split; [lia|]. rewrite rb_at_eq, P1, P2 by lia. unfold rb_off. cbn. lia.
  - exists s, (2 * p + 1), 0. destruct (PO p) as [P1 P2].
    split; [exact Rs|]. split; [lia|]. split; [lia|]. rewrite rb_at_eq, P1, P2 by lia. unfold rb_off. cbn. lia.
  - exists s, (2 * p + 1), 1. destruct (PO p) as [P1 P2].
    split; [exact Rs|]. split; [lia|]. split; [lia|]. rewrite rb_at_eq, P1, P2 by lia. unfold rb_off. cbn. lia.
Qed.

(* memcmp_self: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:262-266. *)
Lemma memcmp_self : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|b l] H; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* crt_K: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:271-272. *)
Definition crt_K (pb : Z -> byte) (ns : Z) (s ch : Z) : Z :=
  s24 (pb (3 * (ch * ns + s))) (pb (3 * (ch * ns + s) + 1)) (pb (3 * (ch * ns + s) + 2)).

(* nth_seq0: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:341-345. *)
Lemma nth_seq0 : forall k i, (i < k)%nat -> nth_error (seq 0 k) i = Some i.
Proof.
  intros k i H. rewrite nth_error_nth' with (d := 0%nat) by (rewrite length_seq; exact H).
  rewrite seq_nth by exact H. reflexivity.
Qed.

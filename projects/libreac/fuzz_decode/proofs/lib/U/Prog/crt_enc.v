From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_braid_c crt_convert.
Import ListNotations.
Open Scope Z_scope.

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
Definition rb_byte (x j : Z) : Z := if j =? 0 then x mod 256 else if j =? 1 then x / 256 mod 256 else x / 65536.

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

Lemma braid_off_at : forall N s ch j, 0 <= ch -> 0 <= j < 3 ->
  3 * (s * N + 2 * (ch / 2)) + braid_off ch j = rb_at N s ch j.
Proof.
  intros N s ch j Hch Hj. rewrite rb_at_eq by lia. unfold braid_off, rb_off. rewrite (Zmod_even ch).
  destruct (Z.even ch); destruct (j =? 0); destruct (j =? 1); lia.
Qed.

Lemma s24_mod : forall b0 b1 b2, s24 b0 b1 b2 mod 2^24 = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2.
Proof.
  intros b0 b1 b2. unfold s24. pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
  destruct (128 <=? bv_unsigned b2).
  - replace (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 - 16777216)
      with ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2) + (-1) * 2^24) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.sub_0_r. apply Z.mod_small. lia.
Qed.

Lemma z8_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (byte_range b).
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma s24_byte : forall (b0 b1 b2 : byte) j, 0 <= j < 3 ->
  Z_to_bv 8 (rb_byte (s24 b0 b1 b2 mod 2^24) j) = if j =? 0 then b0 else if j =? 1 then b1 else b2.
Proof.
  intros b0 b1 b2 j Hj. rewrite s24_mod. pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  pose proof (byte_range b2) as R2. unfold rb_byte.
  set (u0 := bv_unsigned b0) in *. set (u1 := bv_unsigned b1) in *. set (u2 := bv_unsigned b2) in *.
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct C as [-> | [-> | ->]]; cbn [Z.eqb].
  - replace ((u0 + 256 * u1 + 65536 * u2) mod 256) with u0 by (clearbody u0 u1 u2; Z.div_mod_to_equations; lia).
    apply z8_self.
  - replace ((u0 + 256 * u1 + 65536 * u2) / 256 mod 256) with u1 by (clearbody u0 u1 u2; Z.div_mod_to_equations; lia).
    apply z8_self.
  - replace ((u0 + 256 * u1 + 65536 * u2) / 65536) with u2 by (clearbody u0 u1 u2; Z.div_mod_to_equations; lia).
    apply z8_self.
Qed.

Lemma memcmp_self : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|b l] H; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Definition crt_rd (m : word -> option byte) (base i : Z) : byte :=
  match mrd rsegs m (wa (base + i)) with Some b => b | None => Z_to_bv 8 0 end.

Definition crt_K (pb : Z -> byte) (ns : Z) (s ch : Z) : Z :=
  s24 (pb (3 * (ch * ns + s))) (pb (3 * (ch * ns + s) + 1)) (pb (3 * (ch * ns + s) + 2)).

Lemma crt_rd_some : forall m base i b, mrd rsegs m (wa (base + i)) = Some b -> crt_rd m base i = b.
Proof. intros m base i b H. unfold crt_rd. rewrite H. reflexivity. Qed.

Lemma crt_pcm_ok : forall m audio pcm nch ns, 1 <= nch -> 1 <= ns -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (pcm + i)) = Some (crt_rd m pcm i).
Proof.
  intros m audio pcm nch ns HN HS BR i Hi.
  set (ch := i / (3 * ns)). set (r := i mod (3 * ns)).
  assert (D1 : i = 3 * ns * ch + r) by (apply Z.div_mod; lia).
  assert (R1 : 0 <= r < 3 * ns) by (apply Z.mod_pos_bound; lia).
  assert (Rc : 0 <= ch < nch) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (s := r / 3). set (j := r mod 3).
  assert (D2 : r = 3 * s + j) by (apply Z.div_mod; lia).
  assert (Rj : 0 <= j < 3) by (apply Z.mod_pos_bound; lia).
  assert (Rs : 0 <= s < ns) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (BR ch s j Rc Rs Rj) as (b & H1 & _).
  assert (E : pcm + 3 * (ch * ns + s) + j = pcm + i) by lia.
  rewrite E in H1. rewrite H1. rewrite (crt_rd_some m pcm i b H1). reflexivity.
Qed.

Lemma crt_audio_hit : forall m audio pcm nch ns, 2 <= nch -> nch mod 2 = 0 -> 1 <= ns -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns -> exists s ch j, 0 <= s < ns /\ 0 <= ch < nch /\ 0 <= j < 3 /\
    i = rb_at nch s ch j /\
    mrd rsegs m (wa (audio + i)) = Some (crt_rd m pcm (3 * (ch * ns + s) + j)) /\
    mrd rsegs m (wa (pcm + (3 * (ch * ns + s) + j))) = Some (crt_rd m pcm (3 * (ch * ns + s) + j)).
Proof.
  intros m audio pcm nch ns HN HE HS BR i Hi.
  destruct (rb_cover nch ns i HN HE HS Hi) as (s & ch & j & Hs & Hch & Hj & Ei).
  destruct (BR ch s j Hch Hs Hj) as (b & H1 & H2).
  assert (EP : pcm + 3 * (ch * ns + s) + j = pcm + (3 * (ch * ns + s) + j)) by lia.
  rewrite EP in H1.
  assert (EA : audio + 3 * (s * nch + 2 * (ch / 2)) + braid_off ch j = audio + i).
  { rewrite Ei, <- (braid_off_at nch s ch j) by lia. lia. }
  rewrite EA in H2.
  exists s, ch, j. rewrite (crt_rd_some m pcm _ b H1).
  split; [exact Hs|]. split; [exact Hch|]. split; [exact Hj|]. split; [exact Ei|].
  split; [exact H2 | exact H1].
Qed.

Lemma crt_audio_ok : forall m audio pcm nch ns, 2 <= nch -> nch mod 2 = 0 -> 1 <= ns -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (audio + i)) = Some (crt_rd m audio i).
Proof.
  intros m audio pcm nch ns HN HE HS BR i Hi.
  destruct (crt_audio_hit m audio pcm nch ns HN HE HS BR i Hi) as (s & ch & j & _ & _ & _ & _ & H & _).
  rewrite H. rewrite (crt_rd_some m audio i _ H). reflexivity.
Qed.

Lemma crt_out : forall m mm O audio pcm nch ns, 2 <= nch -> nch mod 2 = 0 -> 1 <= ns ->
  0 <= O -> O + 3 * nch * ns <= 2^64 -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns ->
    rb_enc mm (rb_rows O nch (crt_K (crt_rd m pcm) ns) (Z.to_nat ns)) (wa (O + i)) = Some (crt_rd m audio i).
Proof.
  intros m mm O audio pcm nch ns HN HE HS H0 H1 BR i Hi.
  destruct (crt_audio_hit m audio pcm nch ns HN HE HS BR i Hi) as (s & ch & j & Hs & Hch & Hj & Ei & HA & _).
  rewrite (crt_rd_some m audio i _ HA).
  rewrite Ei. rewrite rb_rows_at; try lia.
  unfold crt_K. rewrite s24_byte by exact Hj. f_equal.
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct C as [-> | [-> | ->]]; cbn [Z.eqb]; f_equal; lia.
Qed.

Definition crt_list (m : word -> option byte) (base n : Z) : list byte :=
  map (fun k => crt_rd m base (Z.of_nat k)) (seq 0 (Z.to_nat n)).

Lemma crt_list_len : forall m base n, length (crt_list m base n) = Z.to_nat n.
Proof. intros. unfold crt_list. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_seq0 : forall k i, (i < k)%nat -> nth_error (seq 0 k) i = Some i.
Proof.
  intros k i H. rewrite nth_error_nth' with (d := 0%nat) by (rewrite length_seq; exact H).
  rewrite seq_nth by exact H. reflexivity.
Qed.

Lemma crt_list_bytes : forall m m' base A n, 0 <= A -> 0 <= n -> A + n <= 2^64 ->
  (forall i, 0 <= i < n -> mrd rsegs m' (wa (A + i)) = Some (crt_rd m base i)) ->
  bytes_at rsegs m' A (crt_list m base n).
Proof.
  intros m m' base A n H0 Hn H1 H. split; [exact H0|]. rewrite crt_list_len. split; [lia|].
  intros i Hi. unfold crt_list.
  rewrite nth_error_map, nth_seq0 by exact Hi. cbn [option_map].
  apply H. lia.
Qed.

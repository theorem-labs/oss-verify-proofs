(** * Q6DecSplit — dec-stream suffix locality (split / consumer form).

    MAIN RESULT: [dec_stream_split] — if the declarative decoder over
    [b1 ++ b2] succeeds leaving a remainder at least as long as [b2],
    then the decoder over [b1] alone succeeds with the same output.

    RESTRICTION (byte-aligned suffix): the lemma carries the extra
    premise [exists k, length b2 = 8 * k].  It is needed ONLY for the
    stored-block (BTYPE=00) path: [align_byte] drops
    [length bits mod 8] bits, and over [b1 ++ b2] that count agrees
    with the [b1]-only count exactly when [length b2] is a multiple
    of 8.  The intended consumers (gzip/zlib face assemblies) feed
    [b2 = bytes_bits trailer], whose length is [8 * length trailer],
    so they supply the premise trivially.  Without the premise the
    statement is NOT expected to hold in general (the alignment point
    inside a stored block shifts with [length b2 mod 8]).

    Everything below [dec_stream_split] is a per-primitive split lemma
    of the same shape:
      [P (b1 ++ b2) = Some (v, R) -> length b2 <= length R ->
       exists r1, R = r1 ++ b2 /\ P b1 = Some (v, r1)]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Bits Huff DeflateSpec.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** List helpers *)

Lemma skipn_app_le : forall (A : Type) (n : nat) (l1 l2 : list A),
  (n <= length l1)%nat -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros A n l1 l2 Hn. rewrite skipn_app.
  replace (n - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma firstn_app_le : forall (A : Type) (n : nat) (l1 l2 : list A),
  (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros A n l1 l2 Hn. rewrite firstn_app.
  replace (n - length l1)%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

(** ** Leaf splits *)

Lemma read_bits_split : forall n b1 b2 v R,
  read_bits n (b1 ++ b2) = Some (v, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_bits n b1 = Some (v, r1).
Proof.
  intros n b1 b2 v R H HR.
  pose proof (read_bits_length _ _ _ _ H) as HL.
  rewrite length_app in HL.
  destruct (read_bits n b1) as [[v' r']|] eqn:E1.
  - pose proof (read_bits_app _ _ _ _ b2 E1) as H2.
    rewrite H in H2. inversion H2; subst. exists r'. split; reflexivity.
  - apply read_bits_none_iff in E1. lia.
Qed.

Lemma read_bytes_split : forall n b1 b2 bs R,
  read_bytes n (b1 ++ b2) = Some (bs, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_bytes n b1 = Some (bs, r1).
Proof.
  induction n as [|n IH]; intros b1 b2 bs R H HR; cbn [read_bytes] in H |- *.
  - inversion H; subst. exists b1. split; reflexivity.
  - destruct (read_bits 8%nat (b1 ++ b2)) as [[b r]|] eqn:E1; [|discriminate].
    destruct (read_bytes n r) as [[bs' r']|] eqn:E2; [|discriminate].
    inversion H; subst.
    pose proof (read_bytes_le _ _ _ _ E2) as Hle.
    destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eb1]].
    destruct (IH _ _ _ _ E2 HR) as [q2 [-> Eb2]].
    exists q2. split; [reflexivity|].
    rewrite Eb1. lazy beta iota. rewrite Eb2. reflexivity.
Qed.

Lemma hdecode_split : forall (A : Type) (table : list (list bool * A)) b1 b2 a R,
  hdecode table (b1 ++ b2) = Some (a, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ hdecode table b1 = Some (a, r1).
Proof.
  intros A table; induction table as [|[cw a0] rest IH]; intros b1 b2 a R H HR.
  - discriminate.
  - cbn [hdecode] in H |- *.
    destruct (is_prefix cw (b1 ++ b2)) eqn:Hp.
    + inversion H; subst.
      pose proof (is_prefix_length _ _ Hp) as Hlen.
      rewrite length_app in Hlen.
      rewrite length_skipn, length_app in HR.
      assert (Hcw1 : (length cw <= length b1)%nat) by lia.
      assert (Hp1 : is_prefix cw b1 = true).
      { apply is_prefix_of_firstn.
        rewrite <- (firstn_app_le _ (length cw) b1 b2) by lia.
        apply is_prefix_firstn. exact Hp. }
      rewrite Hp1.
      exists (skipn (length cw) b1). split.
      * apply skipn_app_le. exact Hcw1.
      * reflexivity.
    + assert (Hp1 : is_prefix cw b1 = false).
      { destruct (is_prefix cw b1) eqn:Hb; [|reflexivity].
        exfalso. apply is_prefix_true_iff in Hb as [x ->].
        rewrite <- app_assoc, is_prefix_app in Hp. discriminate. }
      rewrite Hp1.
      destruct (IH _ _ _ _ H HR) as [q [Hq Eq]].
      exists q. split; [exact Hq|exact Eq].
Qed.

Lemma read_extra_split : forall bt et idx b1 b2 n R,
  read_extra bt et idx (b1 ++ b2) = Some (n, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_extra bt et idx b1 = Some (n, r1).
Proof.
  intros bt et idx b1 b2 n R H HR. unfold read_extra in H |- *.
  destruct (nth_error bt idx) as [b|]; [|discriminate].
  destruct (nth_error et idx) as [e|]; [|discriminate].
  destruct (read_bits e (b1 ++ b2)) as [[v r]|] eqn:E; [|discriminate].
  inversion H; subst.
  destruct (read_bits_split _ _ _ _ _ E HR) as [q [-> Eq]].
  exists q. split; [reflexivity|].
  rewrite Eq. reflexivity.
Qed.

(** ** One lit/len symbol *)

Lemma decode_lit_len_split : forall ll dl b1 b2 s R,
  decode_lit_len ll dl (b1 ++ b2) = Some (s, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ decode_lit_len ll dl b1 = Some (s, r1).
Proof.
  intros ll dl b1 b2 s R H HR. unfold decode_lit_len in H |- *.
  destruct (hdecode (code_table ll 15%nat) (b1 ++ b2)) as [[sym r1]|] eqn:E1;
    [|discriminate].
  destruct (Nat.ltb sym 256) eqn:Elt.
  { inversion H; subst.
    destruct (hdecode_split _ _ _ _ _ _ E1 HR) as [q [-> Eq]].
    exists q. split; [reflexivity|].
    rewrite Eq. lazy beta iota. rewrite Elt. reflexivity. }
  destruct (Nat.eqb sym 256) eqn:Eeq.
  { inversion H; subst.
    destruct (hdecode_split _ _ _ _ _ _ E1 HR) as [q [-> Eq]].
    exists q. split; [reflexivity|].
    rewrite Eq. lazy beta iota. rewrite Elt, Eeq. reflexivity. }
  destruct (read_extra length_base length_extra (sym - 257)%nat r1)
    as [[len r2]|] eqn:E2; [|discriminate].
  destruct (hdecode (code_table dl 15%nat) r2) as [[ds r3]|] eqn:E3;
    [|discriminate].
  destruct (read_extra dist_base dist_extra ds r3) as [[d r4]|] eqn:E4;
    [|discriminate].
  inversion H; subst.
  pose proof (read_extra_le _ _ _ _ _ _ E4) as L4.
  pose proof (hdecode_code_table_shorter _ _ _ _ _ E3) as L3.
  pose proof (read_extra_le _ _ _ _ _ _ E2) as L2.
  destruct (hdecode_split _ _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
  destruct (read_extra_split _ _ _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Eq2]].
  destruct (hdecode_split _ _ _ _ _ _ E3 ltac:(lia)) as [q3 [-> Eq3]].
  destruct (read_extra_split _ _ _ _ _ _ _ E4 HR) as [q4 [-> Eq4]].
  exists q4. split; [reflexivity|].
  rewrite Eq1. lazy beta iota. rewrite Elt, Eeq, Eq2. lazy beta iota.
  rewrite Eq3. lazy beta iota. rewrite Eq4. reflexivity.
Qed.

(** ** Stored blocks (the byte-aligned-suffix restriction lives here) *)

Lemma align_byte_app8 : forall b1 b2,
  (exists k, length b2 = (8 * k)%nat) ->
  align_byte (b1 ++ b2) = align_byte b1 ++ b2.
Proof.
  intros b1 b2 [k Hk]. unfold align_byte.
  rewrite length_app, Hk.
  assert (Hm : ((length b1 + 8 * k) mod 8 = length b1 mod 8)%nat).
  { rewrite Nat.mul_comm. apply Nat.Div0.mod_add. }
  rewrite Hm. apply skipn_app_le.
  apply Nat.Div0.mod_le.
Qed.

Lemma decode_stored_split : forall b1 b2 payload R,
  (exists k, length b2 = (8 * k)%nat) ->
  decode_stored (b1 ++ b2) = Some (payload, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ decode_stored b1 = Some (payload, r1).
Proof.
  intros b1 b2 payload R Hk H HR. unfold decode_stored in H |- *.
  rewrite (align_byte_app8 b1 b2 Hk) in H.
  destruct (read_bits 16%nat (align_byte b1 ++ b2)) as [[len r1]|] eqn:E1;
    [|discriminate].
  destruct (read_bits 16%nat r1) as [[nlen r2]|] eqn:E2; [|discriminate].
  destruct (Z.eqb (Z.lxor len nlen) 65535) eqn:Ex; [|discriminate].
  pose proof (read_bytes_le _ _ _ _ H) as L3.
  pose proof (read_bits_le _ _ _ _ E2) as L2.
  destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
  destruct (read_bits_split _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Eq2]].
  destruct (read_bytes_split _ _ _ _ _ H HR) as [q3 [-> Eq3]].
  exists q3. split; [reflexivity|].
  rewrite Eq1. lazy beta iota. rewrite Eq2. lazy beta iota.
  rewrite Ex. lazy beta iota. rewrite Eq3. reflexivity.
Qed.

(** ** Dynamic-table primitives *)

Lemma read_3bit_vals_split : forall n b1 b2 vs R,
  read_3bit_vals n (b1 ++ b2) = Some (vs, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_3bit_vals n b1 = Some (vs, r1).
Proof.
  induction n as [|n IH]; intros b1 b2 vs R H HR; cbn [read_3bit_vals] in H |- *.
  - inversion H; subst. exists b1. split; reflexivity.
  - destruct (read_bits 3%nat (b1 ++ b2)) as [[v r]|] eqn:E1; [|discriminate].
    destruct (read_3bit_vals n r) as [[vs' r']|] eqn:E2; [|discriminate].
    inversion H; subst.
    pose proof (read_3bit_vals_le _ _ _ _ E2) as Hle.
    destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
    destruct (IH _ _ _ _ E2 HR) as [q2 [-> Eq2]].
    exists q2. split; [reflexivity|].
    rewrite Eq1. lazy beta iota. rewrite Eq2. reflexivity.
Qed.

Lemma read_cl_lengths_split : forall n b1 b2 cl R,
  read_cl_lengths n (b1 ++ b2) = Some (cl, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_cl_lengths n b1 = Some (cl, r1).
Proof.
  intros n b1 b2 cl R H HR. unfold read_cl_lengths in H |- *.
  destruct (read_3bit_vals n (b1 ++ b2)) as [[vals r]|] eqn:E; [|discriminate].
  inversion H; subst.
  destruct (read_3bit_vals_split _ _ _ _ _ E HR) as [q [-> Eq]].
  exists q. split; [reflexivity|].
  rewrite Eq. reflexivity.
Qed.

Lemma rl_run_split : forall sym acc b1 b2 rep k R,
  rl_run sym acc (b1 ++ b2) = Some (rep, k, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ rl_run sym acc b1 = Some (rep, k, r1).
Proof.
  intros sym acc b1 b2 rep k R H HR. unfold rl_run in H |- *.
  destruct (Nat.eqb sym 16).
  { destruct (last_len acc) as [prev|]; [|discriminate].
    destruct (read_bits 2%nat (b1 ++ b2)) as [[e r]|] eqn:E; [|discriminate].
    inversion H; subst.
    destruct (read_bits_split _ _ _ _ _ E HR) as [q [-> Eq]].
    exists q. split; [reflexivity|]. rewrite Eq. reflexivity. }
  destruct (Nat.eqb sym 17).
  { destruct (read_bits 3%nat (b1 ++ b2)) as [[e r]|] eqn:E; [|discriminate].
    inversion H; subst.
    destruct (read_bits_split _ _ _ _ _ E HR) as [q [-> Eq]].
    exists q. split; [reflexivity|]. rewrite Eq. reflexivity. }
  destruct (Nat.eqb sym 18).
  { destruct (read_bits 7%nat (b1 ++ b2)) as [[e r]|] eqn:E; [|discriminate].
    inversion H; subst.
    destruct (read_bits_split _ _ _ _ _ E HR) as [q [-> Eq]].
    exists q. split; [reflexivity|]. rewrite Eq. reflexivity. }
  discriminate.
Qed.

Lemma read_lengths_fuel_split : forall f cl need acc b1 b2 ls R,
  read_lengths_fuel f cl need acc (b1 ++ b2) = Some (ls, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_lengths_fuel f cl need acc b1 = Some (ls, r1).
Proof.
  induction f as [|f IH]; intros cl need acc b1 b2 ls R H HR.
  - destruct need as [|n]; [|discriminate].
    cbn [read_lengths_fuel] in H |- *. inversion H; subst.
    exists b1. split; reflexivity.
  - destruct need as [|n].
    { cbn [read_lengths_fuel] in H |- *. inversion H; subst.
      exists b1. split; reflexivity. }
    cbn [read_lengths_fuel] in H |- *.
    destruct (hdecode (code_table cl 7%nat) (b1 ++ b2)) as [[sym r1]|] eqn:E1;
      [|discriminate].
    destruct (Nat.leb sym 15) eqn:Es.
    + pose proof (read_lengths_fuel_le _ _ _ _ _ _ _ H) as L.
      destruct (hdecode_split _ _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
      destruct (IH _ _ _ _ _ _ _ H HR) as [q2 [Hq2 Eq2]].
      exists q2. split; [exact Hq2|].
      rewrite Eq1. lazy beta iota. rewrite Es. lazy beta iota. exact Eq2.
    + destruct (rl_run sym acc r1) as [[[rep k] r2]|] eqn:E2; [|discriminate].
      destruct (Nat.ltb (S n) k) eqn:Ek; [discriminate|].
      pose proof (read_lengths_fuel_le _ _ _ _ _ _ _ H) as L.
      pose proof (rl_run_le _ _ _ _ _ _ E2) as L2.
      destruct (hdecode_split _ _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
      destruct (rl_run_split _ _ _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Er2]].
      destruct (IH _ _ _ _ _ _ _ H HR) as [q3 [Hq3 Eq3]].
      exists q3. split; [exact Hq3|].
      rewrite Eq1. lazy beta iota. rewrite Es. lazy beta iota.
      rewrite Er2. lazy beta iota. rewrite Ek. lazy beta iota. exact Eq3.
Qed.

Lemma read_lengths_split : forall cl need b1 b2 ls R,
  read_lengths cl need (b1 ++ b2) = Some (ls, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ read_lengths cl need b1 = Some (ls, r1).
Proof.
  intros cl need b1 b2 ls R H HR. unfold read_lengths in H |- *.
  exact (read_lengths_fuel_split _ _ _ _ _ _ _ _ H HR).
Qed.

Lemma decode_dynamic_tables_split : forall b1 b2 lit dst R,
  decode_dynamic_tables (b1 ++ b2) = Some (lit, dst, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ decode_dynamic_tables b1 = Some (lit, dst, r1).
Proof.
  intros b1 b2 lit dst R H HR. unfold decode_dynamic_tables in H |- *.
  destruct (read_bits 5%nat (b1 ++ b2)) as [[hlit r1]|] eqn:E1; [|discriminate].
  destruct (read_bits 5%nat r1) as [[hdist r2]|] eqn:E2; [|discriminate].
  destruct (read_bits 4%nat r2) as [[hclen r3]|] eqn:E3; [|discriminate].
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|] eqn:E4;
    [|discriminate].
  destruct (valid_lengths_b cl 7%nat) eqn:Ev7; [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|] eqn:E5; [|discriminate].
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat)
    eqn:Evv; [|discriminate].
  inversion H; subst.
  pose proof (read_lengths_le _ _ _ _ _ E5) as L5.
  pose proof (read_cl_lengths_le _ _ _ _ E4) as L4.
  pose proof (read_bits_le _ _ _ _ E3) as L3.
  pose proof (read_bits_le _ _ _ _ E2) as L2.
  destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
  destruct (read_bits_split _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Eq2]].
  destruct (read_bits_split _ _ _ _ _ E3 ltac:(lia)) as [q3 [-> Eq3]].
  destruct (read_cl_lengths_split _ _ _ _ _ E4 ltac:(lia)) as [q4 [-> Eq4]].
  destruct (read_lengths_split _ _ _ _ _ _ E5 HR) as [q5 [-> Eq5]].
  exists q5. split; [reflexivity|].
  rewrite Eq1. lazy beta iota zeta. rewrite Eq2. lazy beta iota zeta.
  rewrite Eq3. lazy beta iota zeta. rewrite Eq4. lazy beta iota zeta.
  rewrite Ev7. lazy beta iota. rewrite Eq5. lazy beta iota.
  rewrite Evv. reflexivity.
Qed.

(** ** Symbol sequences *)

Lemma decode_symbols_fuel_split : forall f ll dl b1 b2 syms R,
  decode_symbols_fuel f ll dl (b1 ++ b2) = Some (syms, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ decode_symbols_fuel f ll dl b1 = Some (syms, r1).
Proof.
  induction f as [|f IH]; intros ll dl b1 b2 syms R H HR; [discriminate|].
  cbn [decode_symbols_fuel] in H |- *.
  destruct (decode_lit_len ll dl (b1 ++ b2)) as [[s r]|] eqn:E1; [|discriminate].
  destruct (lz_is_end s) eqn:Ee.
  - inversion H; subst.
    destruct (decode_lit_len_split _ _ _ _ _ _ E1 HR) as [q [-> Eq]].
    exists q. split; [reflexivity|].
    rewrite Eq. lazy beta iota. rewrite Ee. reflexivity.
  - destruct (decode_symbols_fuel f ll dl r) as [[syms' r']|] eqn:E2;
      [|discriminate].
    inversion H; subst.
    pose proof (decode_symbols_fuel_shorter _ _ _ _ _ _ E2) as L2.
    destruct (decode_lit_len_split _ _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
    destruct (IH _ _ _ _ _ _ E2 HR) as [q2 [-> Eq2]].
    exists q2. split; [reflexivity|].
    rewrite Eq1. lazy beta iota. rewrite Ee. lazy beta iota.
    rewrite Eq2. reflexivity.
Qed.

Lemma decode_symbols_split : forall ll dl b1 b2 syms R,
  decode_symbols ll dl (b1 ++ b2) = Some (syms, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ decode_symbols ll dl b1 = Some (syms, r1).
Proof.
  intros ll dl b1 b2 syms R H HR. unfold decode_symbols in H |- *.
  destruct (decode_symbols_fuel_split _ _ _ _ _ _ _ H HR) as [q [Hq Eq]].
  exists q. split; [exact Hq|].
  rewrite <- Eq. apply decode_symbols_fuel_indep;
    [lia | rewrite length_app; lia].
Qed.

(** ** One block *)

Lemma dec_blk_split : forall b1 b2 acc fin out R,
  (exists k, length b2 = (8 * k)%nat) ->
  dec_blk (b1 ++ b2) acc = Some (fin, out, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ dec_blk b1 acc = Some (fin, out, r1).
Proof.
  intros b1 b2 acc fin out R Hk H HR. unfold dec_blk in H |- *.
  destruct (read_bits 1%nat (b1 ++ b2)) as [[bfinal r1]|] eqn:E1;
    [|discriminate].
  destruct (read_bits 2%nat r1) as [[btype r2]|] eqn:E2; [|discriminate].
  destruct (Z.eqb btype 0) eqn:Et0.
  { destruct (decode_stored r2) as [[payload r3]|] eqn:E3; [|discriminate].
    inversion H; subst.
    pose proof (decode_stored_le _ _ _ E3) as L3.
    pose proof (read_bits_le _ _ _ _ E2) as L2.
    destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
    destruct (read_bits_split _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Eq2]].
    destruct (decode_stored_split _ _ _ _ Hk E3 HR) as [q3 [-> Eq3]].
    exists q3. split; [reflexivity|].
    rewrite Eq1. lazy beta iota zeta. rewrite Eq2. lazy beta iota zeta.
    rewrite Et0. lazy beta iota. rewrite Eq3. reflexivity. }
  destruct (Z.eqb btype 1) eqn:Et1.
  { destruct (decode_symbols fixed_lit_lengths fixed_dist_lengths r2)
      as [[syms r3]|] eqn:E3; [|discriminate].
    destruct (resolve_lz syms acc) as [o|] eqn:Er; [|discriminate].
    inversion H; subst.
    pose proof (decode_symbols_shorter _ _ _ _ _ E3) as L3.
    pose proof (read_bits_le _ _ _ _ E2) as L2.
    destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
    destruct (read_bits_split _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Eq2]].
    destruct (decode_symbols_split _ _ _ _ _ _ E3 HR) as [q3 [-> Eq3]].
    exists q3. split; [reflexivity|].
    rewrite Eq1. lazy beta iota zeta. rewrite Eq2. lazy beta iota zeta.
    rewrite Et0, Et1. lazy beta iota. rewrite Eq3. lazy beta iota.
    rewrite Er. reflexivity. }
  destruct (Z.eqb btype 2) eqn:Et2.
  { destruct (decode_dynamic_tables r2) as [[[lit dst] r3]|] eqn:E3;
      [|discriminate].
    destruct (decode_symbols lit dst r3) as [[syms r4]|] eqn:E4;
      [|discriminate].
    destruct (resolve_lz syms acc) as [o|] eqn:Er; [|discriminate].
    inversion H; subst.
    pose proof (decode_symbols_shorter _ _ _ _ _ E4) as L4.
    pose proof (decode_dynamic_tables_le _ _ _ _ E3) as L3.
    pose proof (read_bits_le _ _ _ _ E2) as L2.
    destruct (read_bits_split _ _ _ _ _ E1 ltac:(lia)) as [q1 [-> Eq1]].
    destruct (read_bits_split _ _ _ _ _ E2 ltac:(lia)) as [q2 [-> Eq2]].
    destruct (decode_dynamic_tables_split _ _ _ _ _ E3 ltac:(lia))
      as [q3 [-> Eq3]].
    destruct (decode_symbols_split _ _ _ _ _ _ E4 HR) as [q4 [-> Eq4]].
    exists q4. split; [reflexivity|].
    rewrite Eq1. lazy beta iota zeta. rewrite Eq2. lazy beta iota zeta.
    rewrite Et0, Et1, Et2. lazy beta iota. rewrite Eq3. lazy beta iota.
    rewrite Eq4. lazy beta iota. rewrite Er. reflexivity. }
  discriminate.
Qed.

(** ** The stream loop *)

Lemma dec_stream_fuel_le : forall f bits acc out rem,
  dec_stream_fuel f bits acc = Some (out, rem) ->
  (length rem <= length bits)%nat.
Proof.
  induction f as [|f IH]; intros bits acc out rem H; [discriminate|].
  cbn [dec_stream_fuel] in H.
  destruct (dec_blk bits acc) as [[[fin acc'] r]|] eqn:E; [|discriminate].
  pose proof (dec_blk_shorter _ _ _ _ _ E) as Hs.
  destruct fin.
  - inversion H; subst. lia.
  - apply IH in H. lia.
Qed.

Lemma dec_stream_fuel_split : forall f b1 b2 acc out R,
  (exists k, length b2 = (8 * k)%nat) ->
  dec_stream_fuel f (b1 ++ b2) acc = Some (out, R) ->
  (length b2 <= length R)%nat ->
  exists r1, R = r1 ++ b2 /\ dec_stream_fuel f b1 acc = Some (out, r1).
Proof.
  induction f as [|f IH]; intros b1 b2 acc out R Hk H HR; [discriminate|].
  cbn [dec_stream_fuel] in H |- *.
  destruct (dec_blk (b1 ++ b2) acc) as [[[fin acc'] r]|] eqn:E; [|discriminate].
  destruct fin.
  - inversion H; subst.
    destruct (dec_blk_split _ _ _ _ _ _ Hk E HR) as [q [Hq Eq]].
    exists q. split; [exact Hq|]. rewrite Eq. reflexivity.
  - pose proof (dec_stream_fuel_le _ _ _ _ _ H) as L.
    destruct (dec_blk_split _ _ _ _ _ _ Hk E ltac:(lia)) as [q [-> Eq]].
    destruct (IH _ _ _ _ _ Hk H HR) as [q2 [Hq2 Eq2]].
    exists q2. split; [exact Hq2|].
    rewrite Eq. lazy beta iota. exact Eq2.
Qed.

(** ** THE RESULT (consumer form; byte-aligned suffix)

    The extra premise [exists k, length b2 = 8 * k] is the documented
    restriction: it is what makes [align_byte] agree between the
    [b1 ++ b2] run and the [b1]-only run inside stored blocks.  The
    consumers instantiate [b2 := bytes_bits trailer] and discharge it
    with [bytes_bits_length]. *)

Lemma dec_stream_split : forall b1 b2 out rem,
  dec_stream_from (b1 ++ b2) [] = Some (out, rem) ->
  (length b2 <= length rem)%nat ->
  (exists k, length b2 = (8 * k)%nat) ->
  dec_stream b1 = Some out.
Proof.
  intros b1 b2 out rem H HR Hk.
  unfold dec_stream_from in H.
  destruct (dec_stream_fuel_split _ _ _ _ _ _ Hk H HR) as [q [Hq Eq]].
  assert (Hind : dec_stream_fuel (S (length b1)) b1 []
                 = dec_stream_fuel (S (length (b1 ++ b2))) b1 []).
  { apply dec_stream_fuel_indep; [lia | rewrite length_app; lia]. }
  unfold dec_stream, dec_stream_rem, dec_stream_from.
  rewrite Hind, Eq. reflexivity.
Qed.

(** The remainder-returning strengthening, for consumers that also need
    the leftover stream: same premises, full conclusion. *)
Lemma dec_stream_rem_split : forall b1 b2 out rem,
  dec_stream_from (b1 ++ b2) [] = Some (out, rem) ->
  (length b2 <= length rem)%nat ->
  (exists k, length b2 = (8 * k)%nat) ->
  exists r1, rem = r1 ++ b2 /\ dec_stream_rem b1 = Some (out, r1).
Proof.
  intros b1 b2 out rem H HR Hk.
  unfold dec_stream_from in H.
  destruct (dec_stream_fuel_split _ _ _ _ _ _ Hk H HR) as [q [Hq Eq]].
  exists q. split; [exact Hq|].
  unfold dec_stream_rem, dec_stream_from.
  rewrite <- Eq. apply dec_stream_fuel_indep; [lia | rewrite length_app; lia].
Qed.

Print Assumptions dec_stream_split.
Print Assumptions dec_stream_rem_split.

(** ** Why the restriction is NOT removable: a countermodel

    The UNRESTRICTED statement — [dec_stream_split] without the
    [exists k, length b2 = 8 * k] premise — is FALSE.  Witness: a
    single stored block.

      cm_total (48 bits)
        = BFINAL=1, BTYPE=00            (3 bits: [1;0;0])
        ++ [0;0;0;0;1]                  (5 pre-alignment bits)
        ++ LEN  = 0   (16 zero bits)
        ++ NLEN = 65535 (16 one bits)
        ++ 8 zero bits                  (the remainder)

    Over cm_b1 ++ cm_b2 (cm_b2 = [false], ONE bit — not a byte
    multiple): after the 3 header bits, 45 bits remain, so [align_byte]
    drops 45 mod 8 = 5 bits — exactly the [0;0;0;0;1] block.  LEN=0,
    NLEN=65535, complement checks, empty payload:
    result Some ([], 8 zero bits), and length cm_b2 = 1 <= 8.

    Over cm_b1 alone (47 bits): after the header, 44 bits remain, so
    [align_byte] drops only 4 bits, leaving the [1] of the junk block
    in front.  Read LSB-first, LEN' = 1 and NLEN' = 65534 — and
    1 lxor 65534 = 65535, so the complement check PASSES at the
    shifted position, and one payload byte [1] is read:
    result Some [1] <> Some [].  *)

Definition cm_total : list bool :=
  [true; false; false] ++ [false; false; false; false; true]
  ++ repeat false 16 ++ repeat true 16 ++ repeat false 8.
Definition cm_b1 : list bool := firstn 47 cm_total.
Definition cm_b2 : list bool := [false].

Example cm_full :
  dec_stream_from (cm_b1 ++ cm_b2) [] = Some ([], repeat false 8).
Proof. vm_compute. reflexivity. Qed.

Example cm_b1_differs : dec_stream cm_b1 = Some [1].
Proof. vm_compute. reflexivity. Qed.

Lemma dec_stream_split_unrestricted_false :
  ~ (forall b1 b2 out rem,
       dec_stream_from (b1 ++ b2) [] = Some (out, rem) ->
       (length b2 <= length rem)%nat ->
       dec_stream b1 = Some out).
Proof.
  intro Hgen.
  assert (Hlen : (length cm_b2 <= length (repeat false 8))%nat)
    by (vm_compute; lia).
  specialize (Hgen cm_b1 cm_b2 [] (repeat false 8) cm_full Hlen).
  rewrite cm_b1_differs in Hgen. discriminate.
Qed.

Print Assumptions dec_stream_split_unrestricted_false.

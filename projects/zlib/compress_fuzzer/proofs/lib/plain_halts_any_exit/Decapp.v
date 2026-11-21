(** * Decapp — GAP7 F3: append-stability of the declarative decoder.

    OWNER: q7-decapp worker fork (zlib z-repro campaign, 2026-08-21).

    TARGET (the pump wrapper's [Hdecapp], Gap7Wrappers.v:569):

      dec_stream_from bits acc = Some (X, rem) ->
      dec_stream_from (bits ++ T) acc = Some (X, rem ++ T)

    PREMISE DELTA — REPORTED LOUDLY.  The statement as spelled is FALSE:
    [decode_stored] aligns via [align_byte bits = skipn (length bits mod 8)
    bits], so the number of padding bits skipped depends on the REMAINING
    length, and appending a T with [length T mod 8 <> 0] shifts a stored
    block's LEN/NLEN reads.  [DecappCex.v] pins a concrete vm_compute
    counterexample.  The provable form adds ONE premise:

      (length T mod 8 = 0)%nat

    which is a bytes fact on T — both wrapper call sites instantiate T as
    [bytes_bits] of a byte-list trailer ([be32 ad] / [TRL]), discharged by
    [bytes_bits_mod8] below.  No other premise is forced: the Huffman-arm
    hazard (a first-match [hdecode] scan can select an EARLIER, longer
    codeword once T lands) is refuted by prefix-freeness, which every
    consulted table has by construction — fixed tables by
    [fixed_lit_valid]/[fixed_dist_valid], dynamic tables by
    [decode_dynamic_tables_valid], the code-length table by the
    [valid_lengths_b cl 7] gate that precedes [read_lengths].

    Shape: [hdecode_app] (the atom, needing [PrefixFreeTable]) →
    per-read-primitive app lemmas → [dec_blk_app] → same-fuel
    [dec_stream_fuel_app] + [dec_stream_fuel_mono] (the fuel bridge; the
    two sides of the target run at fuels [S (length bits)] vs
    [S (length (bits ++ T)))]) → [dec_stream_from_app] = the target. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff DeflateSpec.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* --------------------------------------------------------------------------
   0.  nat mod-8 helpers (stable stdlib names only: div_mod / mod_add /
       mod_small / mod_upper_bound / mod_mul all take the b <> 0 premise).
   -------------------------------------------------------------------------- *)

Lemma add_mod8 : forall a b : nat,
  (b mod 8 = 0)%nat -> ((a + b) mod 8 = a mod 8)%nat.
Proof.
  intros a b Hb.
  pose proof (Nat.div_mod b 8 ltac:(lia)) as Hb8.
  rewrite Hb, Nat.add_0_r, Nat.mul_comm in Hb8.
  rewrite Hb8, Nat.mod_add by lia. reflexivity.
Qed.

Lemma mod8_le : forall n : nat, (n mod 8 <= n)%nat.
Proof.
  intro n. destruct (Nat.le_gt_cases 8 n) as [H|H].
  - pose proof (Nat.mod_upper_bound n 8 ltac:(lia)). lia.
  - rewrite Nat.mod_small by lia. lia.
Qed.

Lemma skipn_app_le : forall (A : Type) n (l1 l2 : list A),
  (n <= length l1)%nat -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros A n l1 l2 H. rewrite skipn_app.
  replace (n - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

(** The call-site discharger: a bit list that comes from bytes is
    byte-aligned. *)
Lemma bytes_bits_mod8 : forall bs, (length (bytes_bits bs) mod 8 = 0)%nat.
Proof.
  intro bs. rewrite bytes_bits_length, Nat.mul_comm.
  apply Nat.mod_mul. lia.
Qed.

(* --------------------------------------------------------------------------
   1.  is_prefix order facts.  [is_prefix_flip] is the load-bearing one:
       if appending T turned a codeword into a prefix, the codeword must
       EXTEND the whole original stream.
   -------------------------------------------------------------------------- *)

Lemma is_prefix_ext : forall p q T,
  is_prefix p q = true -> is_prefix p (q ++ T) = true.
Proof.
  induction p as [|a p IH]; intros q T H; [reflexivity|].
  destruct q as [|b q]; [discriminate|].
  cbn in H |- *. apply andb_true_iff in H as [H1 H2].
  rewrite H1. cbn. apply IH. exact H2.
Qed.

Lemma is_prefix_flip : forall p q T,
  is_prefix p q = false -> is_prefix p (q ++ T) = true ->
  is_prefix q p = true.
Proof.
  induction p as [|a p IH]; intros q T Hf Ht.
  - discriminate Hf.
  - destruct q as [|b q]; [reflexivity|].
    cbn in Hf, Ht |- *.
    apply andb_true_iff in Ht as [He Ht].
    apply Bool.eqb_prop in He. subst b.
    rewrite Bool.eqb_reflx in Hf. cbn in Hf.
    rewrite Bool.eqb_reflx. cbn.
    exact (IH q T Hf Ht).
Qed.

Lemma is_prefix_trans : forall p q r,
  is_prefix p q = true -> is_prefix q r = true -> is_prefix p r = true.
Proof.
  induction p as [|a p IH]; intros q r H1 H2; [reflexivity|].
  destruct q as [|b q]; [discriminate H1|].
  destruct r as [|c r]; [discriminate H2|].
  cbn in H1, H2 |- *.
  apply andb_true_iff in H1 as [E1 H1].
  apply andb_true_iff in H2 as [E2 H2].
  apply Bool.eqb_prop in E1. apply Bool.eqb_prop in E2. subst.
  rewrite Bool.eqb_reflx. cbn. exact (IH q r H1 H2).
Qed.

(* --------------------------------------------------------------------------
   2.  hdecode_app — THE ATOM.  First-match scan + prefix-freeness.
       The dangerous branch: the head codeword [cw0] rejected [bits] but
       accepts [bits ++ T].  Then [bits] is a prefix of [cw0] (flip), the
       codeword [cw] that DID fire is a prefix of [bits] (soundness), so
       [cw] is a prefix of [cw0] (trans) with [cw <> cw0] — refuting
       prefix-freeness.
   -------------------------------------------------------------------------- *)

Lemma PrefixFreeTable_tail : forall (A : Type) e (rest : list (list bool * A)),
  PrefixFreeTable (e :: rest) -> PrefixFreeTable rest.
Proof.
  intros A e rest H cw1 s1 cw2 s2 H1 H2 Hne.
  apply (H cw1 s1 cw2 s2); [right; exact H1 | right; exact H2 | exact Hne].
Qed.

Lemma hdecode_app : forall (A : Type) (table : list (list bool * A)) bits T a rem,
  PrefixFreeTable table ->
  hdecode table bits = Some (a, rem) ->
  hdecode table (bits ++ T) = Some (a, rem ++ T).
Proof.
  intros A table; induction table as [|[cw0 a0] rest IH];
    intros bits T a rem HPF H.
  - discriminate.
  - cbn [hdecode] in H |- *.
    destruct (is_prefix cw0 bits) eqn:Hp.
    + inversion H; subst.
      rewrite (is_prefix_ext _ _ T Hp).
      rewrite skipn_app_le by (apply is_prefix_length; exact Hp).
      reflexivity.
    + destruct (is_prefix cw0 (bits ++ T)) eqn:Hp2.
      * exfalso.
        pose proof (is_prefix_flip _ _ _ Hp Hp2) as Hbp.
        apply hdecode_sound in H as [cw [Hin [Hcb Heq]]].
        pose proof (is_prefix_trans _ _ _ Hcb Hbp) as Hcc.
        assert (Hne : (cw, a) <> (cw0, a0)).
        { intro E. inversion E; subst. rewrite Hcb in Hp. discriminate. }
        pose proof (HPF cw a cw0 a0 (in_cons _ _ _ Hin) (in_eq _ _) Hne) as Hff.
        rewrite Hcc in Hff. discriminate.
      * apply IH; [exact (PrefixFreeTable_tail _ _ _ HPF) | exact H].
Qed.

(** Every table the decoder consults is a [code_table] of ValidLengths. *)
Lemma hdecode_ct_app : forall lens mb bits T s r,
  ValidLengths lens mb ->
  hdecode (code_table lens mb) bits = Some (s, r) ->
  hdecode (code_table lens mb) (bits ++ T) = Some (s, r ++ T).
Proof.
  intros lens mb bits T s r HV H.
  exact (hdecode_app _ _ _ _ _ _ (code_table_prefix_free lens mb HV) H).
Qed.

(* --------------------------------------------------------------------------
   3.  Per-read-primitive app lemmas.  [read_bits_app] is landed (Bits.v).
   -------------------------------------------------------------------------- *)

Lemma read_extra_app : forall bt et idx bits T n rem,
  read_extra bt et idx bits = Some (n, rem) ->
  read_extra bt et idx (bits ++ T) = Some (n, rem ++ T).
Proof.
  intros bt et idx bits T n rem H. unfold read_extra in H |- *.
  destruct (nth_error bt idx) as [b|]; [|discriminate].
  destruct (nth_error et idx) as [e|]; [|discriminate].
  destruct (read_bits e bits) as [[v r]|] eqn:E; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E). cbv beta iota.
  inversion H; subst. reflexivity.
Qed.

Lemma decode_lit_len_app : forall ll dl bits T s r,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  decode_lit_len ll dl bits = Some (s, r) ->
  decode_lit_len ll dl (bits ++ T) = Some (s, r ++ T).
Proof.
  intros ll dl bits T s r HVl HVd H. unfold decode_lit_len in H |- *.
  destruct (hdecode (code_table ll 15%nat) bits) as [[sym r1]|] eqn:E1;
    [|discriminate].
  rewrite (hdecode_ct_app _ _ _ T _ _ HVl E1). cbv beta iota.
  destruct (Nat.ltb sym 256).
  { inversion H; subst. reflexivity. }
  destruct (Nat.eqb sym 256).
  { inversion H; subst. reflexivity. }
  destruct (read_extra length_base length_extra (sym - 257)%nat r1)
    as [[len r2]|] eqn:E2; [|discriminate].
  rewrite (read_extra_app _ _ _ _ T _ _ E2). cbv beta iota.
  destruct (hdecode (code_table dl 15%nat) r2) as [[ds r3]|] eqn:E3;
    [|discriminate].
  rewrite (hdecode_ct_app _ _ _ T _ _ HVd E3). cbv beta iota.
  destruct (read_extra dist_base dist_extra ds r3) as [[d r4]|] eqn:E4;
    [|discriminate].
  rewrite (read_extra_app _ _ _ _ T _ _ E4). cbv beta iota.
  inversion H; subst. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   4.  The symbol loop.  Same-fuel app lemma + fuel monotonicity; the
       wrapper [decode_symbols] runs at [S (length bits)] on each side, so
       the app lemma alone is fuel-mismatched — mono bridges.
   -------------------------------------------------------------------------- *)

Lemma decode_symbols_fuel_app : forall ll dl T,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  forall f bits syms rem,
  decode_symbols_fuel f ll dl bits = Some (syms, rem) ->
  decode_symbols_fuel f ll dl (bits ++ T) = Some (syms, rem ++ T).
Proof.
  intros ll dl T HVl HVd.
  induction f as [|f IH]; intros bits syms rem H; [discriminate|].
  cbn [decode_symbols_fuel] in H |- *.
  destruct (decode_lit_len ll dl bits) as [[s0 r0]|] eqn:E1; [|discriminate].
  rewrite (decode_lit_len_app _ _ _ T _ _ HVl HVd E1). cbv beta iota.
  destruct (lz_is_end s0).
  { inversion H; subst. reflexivity. }
  destruct (decode_symbols_fuel f ll dl r0) as [[syms1 rem1]|] eqn:E2;
    [|discriminate].
  rewrite (IH _ _ _ E2). cbv beta iota.
  inversion H; subst. reflexivity.
Qed.

Lemma decode_symbols_fuel_mono : forall ll dl f f' bits syms rem,
  (f <= f')%nat ->
  decode_symbols_fuel f ll dl bits = Some (syms, rem) ->
  decode_symbols_fuel f' ll dl bits = Some (syms, rem).
Proof.
  intros ll dl f. induction f as [|f IH]; intros f' bits syms rem Hle H;
    [discriminate|].
  destruct f' as [|f']; [lia|].
  cbn [decode_symbols_fuel] in H |- *.
  destruct (decode_lit_len ll dl bits) as [[s0 r0]|]; [|discriminate].
  destruct (lz_is_end s0); [exact H|].
  destruct (decode_symbols_fuel f ll dl r0) as [[syms1 rem1]|] eqn:E2;
    [|discriminate].
  rewrite (IH f' _ _ _ ltac:(lia) E2). exact H.
Qed.

Lemma decode_symbols_app : forall ll dl bits T syms rem,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  decode_symbols ll dl bits = Some (syms, rem) ->
  decode_symbols ll dl (bits ++ T) = Some (syms, rem ++ T).
Proof.
  intros ll dl bits T syms rem HVl HVd H. unfold decode_symbols in H |- *.
  apply (decode_symbols_fuel_mono ll dl (S (length bits))).
  { rewrite length_app. lia. }
  apply (decode_symbols_fuel_app ll dl T HVl HVd). exact H.
Qed.

(* --------------------------------------------------------------------------
   5.  Stored blocks — the arm that FORCES the mod-8 premise.
   -------------------------------------------------------------------------- *)

Lemma align_byte_app : forall bits T,
  (length T mod 8 = 0)%nat ->
  align_byte (bits ++ T) = align_byte bits ++ T.
Proof.
  intros bits T H8. unfold align_byte.
  rewrite length_app, (add_mod8 _ _ H8).
  apply skipn_app_le. apply mod8_le.
Qed.

Lemma read_bytes_app : forall n bits T bs rem,
  read_bytes n bits = Some (bs, rem) ->
  read_bytes n (bits ++ T) = Some (bs, rem ++ T).
Proof.
  induction n as [|n IH]; intros bits T bs rem H;
    cbn [read_bytes] in H |- *.
  - inversion H; subst. reflexivity.
  - destruct (read_bits 8%nat bits) as [[b r]|] eqn:E1; [|discriminate].
    rewrite (read_bits_app _ _ _ _ T E1). cbv beta iota.
    destruct (read_bytes n r) as [[bs1 r1]|] eqn:E2; [|discriminate].
    rewrite (IH _ T _ _ E2). cbv beta iota.
    inversion H; subst. reflexivity.
Qed.

Lemma decode_stored_app : forall bits T p r,
  (length T mod 8 = 0)%nat ->
  decode_stored bits = Some (p, r) ->
  decode_stored (bits ++ T) = Some (p, r ++ T).
Proof.
  intros bits T p r H8 H. unfold decode_stored in H |- *.
  rewrite (align_byte_app bits T H8).
  destruct (read_bits 16%nat (align_byte bits)) as [[len r1]|] eqn:E1;
    [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E1). cbv beta iota.
  destruct (read_bits 16%nat r1) as [[nlen r2]|] eqn:E2; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E2). cbv beta iota.
  destruct (Z.eqb (Z.lxor len nlen) 65535); [|discriminate].
  apply read_bytes_app. exact H.
Qed.

(* --------------------------------------------------------------------------
   6.  Dynamic header.  [read_lengths] runs at fuel = [need] on BOTH sides
       (bits-independent fuel), so no mono bridge is needed there.
   -------------------------------------------------------------------------- *)

Lemma read_3bit_vals_app : forall n bits T vs rem,
  read_3bit_vals n bits = Some (vs, rem) ->
  read_3bit_vals n (bits ++ T) = Some (vs, rem ++ T).
Proof.
  induction n as [|n IH]; intros bits T vs rem H;
    cbn [read_3bit_vals] in H |- *.
  - inversion H; subst. reflexivity.
  - destruct (read_bits 3%nat bits) as [[v r]|] eqn:E1; [|discriminate].
    rewrite (read_bits_app _ _ _ _ T E1). cbv beta iota.
    destruct (read_3bit_vals n r) as [[vs1 r1]|] eqn:E2; [|discriminate].
    rewrite (IH _ T _ _ E2). cbv beta iota.
    inversion H; subst. reflexivity.
Qed.

Lemma read_cl_lengths_app : forall n bits T cl rem,
  read_cl_lengths n bits = Some (cl, rem) ->
  read_cl_lengths n (bits ++ T) = Some (cl, rem ++ T).
Proof.
  intros n bits T cl rem H. unfold read_cl_lengths in H |- *.
  destruct (read_3bit_vals n bits) as [[vals r]|] eqn:E; [|discriminate].
  rewrite (read_3bit_vals_app _ _ T _ _ E). cbv beta iota.
  inversion H; subst. reflexivity.
Qed.

Lemma rl_run_app : forall sym acc bits T rep k rem,
  rl_run sym acc bits = Some (rep, k, rem) ->
  rl_run sym acc (bits ++ T) = Some (rep, k, rem ++ T).
Proof.
  intros sym acc bits T rep k rem H. unfold rl_run in H |- *.
  destruct (Nat.eqb sym 16).
  { destruct (last_len acc) as [prev|]; [|discriminate].
    destruct (read_bits 2%nat bits) as [[e r]|] eqn:E; [|discriminate].
    rewrite (read_bits_app _ _ _ _ T E). cbv beta iota.
    inversion H; subst. reflexivity. }
  destruct (Nat.eqb sym 17).
  { destruct (read_bits 3%nat bits) as [[e r]|] eqn:E; [|discriminate].
    rewrite (read_bits_app _ _ _ _ T E). cbv beta iota.
    inversion H; subst. reflexivity. }
  destruct (Nat.eqb sym 18).
  { destruct (read_bits 7%nat bits) as [[e r]|] eqn:E; [|discriminate].
    rewrite (read_bits_app _ _ _ _ T E). cbv beta iota.
    inversion H; subst. reflexivity. }
  discriminate.
Qed.

Lemma read_lengths_fuel_app : forall cl T,
  ValidLengths cl 7%nat ->
  forall f need acc bits ls rem,
  read_lengths_fuel f cl need acc bits = Some (ls, rem) ->
  read_lengths_fuel f cl need acc (bits ++ T) = Some (ls, rem ++ T).
Proof.
  intros cl T HV. induction f as [|f IH]; intros need acc bits ls rem H.
  - destruct need as [|n]; cbn [read_lengths_fuel] in H |- *;
      [inversion H; subst; reflexivity | discriminate].
  - destruct need as [|n]; cbn [read_lengths_fuel] in H |- *.
    { inversion H; subst. reflexivity. }
    destruct (hdecode (code_table cl 7%nat) bits) as [[sym r1]|] eqn:E1;
      [|discriminate].
    rewrite (hdecode_ct_app _ _ _ T _ _ HV E1). cbv beta iota.
    destruct (Nat.leb sym 15).
    { apply IH. exact H. }
    destruct (rl_run sym acc r1) as [[[rep k] r2]|] eqn:E2; [|discriminate].
    rewrite (rl_run_app _ _ _ T _ _ _ E2). cbv beta iota.
    destruct (Nat.ltb (S n) k); [discriminate|].
    apply IH. exact H.
Qed.

Lemma read_lengths_app : forall cl need bits T ls rem,
  ValidLengths cl 7%nat ->
  read_lengths cl need bits = Some (ls, rem) ->
  read_lengths cl need (bits ++ T) = Some (ls, rem ++ T).
Proof.
  intros cl need bits T ls rem HV H. unfold read_lengths in H |- *.
  apply (read_lengths_fuel_app cl T HV). exact H.
Qed.

Lemma decode_dynamic_tables_app : forall bits T lit dst rem,
  decode_dynamic_tables bits = Some (lit, dst, rem) ->
  decode_dynamic_tables (bits ++ T) = Some (lit, dst, rem ++ T).
Proof.
  intros bits T lit dst rem H. unfold decode_dynamic_tables in H |- *.
  destruct (read_bits 5%nat bits) as [[hlit r1]|] eqn:E1; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E1). cbv beta iota.
  destruct (read_bits 5%nat r1) as [[hdist r2]|] eqn:E2; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E2). cbv beta iota.
  destruct (read_bits 4%nat r2) as [[hclen r3]|] eqn:E3; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E3). cbv beta iota.
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|] eqn:E4;
    [|discriminate].
  rewrite (read_cl_lengths_app _ _ T _ _ E4). cbv beta iota.
  destruct (valid_lengths_b cl 7%nat) eqn:Ev7; [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|] eqn:E5; [|discriminate].
  rewrite (read_lengths_app _ _ _ T _ _ (valid_lengths_b_true _ _ Ev7) E5).
  cbv beta iota.
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat);
    [|discriminate].
  inversion H; subst. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   7.  One block, then the stream.
   -------------------------------------------------------------------------- *)

Lemma dec_blk_app : forall bits T acc fin acc2 rem,
  (length T mod 8 = 0)%nat ->
  dec_blk bits acc = Some (fin, acc2, rem) ->
  dec_blk (bits ++ T) acc = Some (fin, acc2, rem ++ T).
Proof.
  intros bits T acc fin acc2 rem H8 H. unfold dec_blk in H |- *.
  destruct (read_bits 1%nat bits) as [[bfinal r1]|] eqn:E1; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E1). cbv beta iota.
  destruct (read_bits 2%nat r1) as [[btype r2]|] eqn:E2; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E2). cbv beta iota.
  destruct (Z.eqb btype 0).
  { destruct (decode_stored r2) as [[payload r3]|] eqn:E3; [|discriminate].
    rewrite (decode_stored_app _ T _ _ H8 E3). cbv beta iota.
    inversion H; subst. reflexivity. }
  destruct (Z.eqb btype 1).
  { destruct (decode_symbols fixed_lit_lengths fixed_dist_lengths r2)
      as [[syms r3]|] eqn:E3; [|discriminate].
    rewrite (decode_symbols_app _ _ _ T _ _ fixed_lit_valid fixed_dist_valid E3).
    cbv beta iota.
    destruct (resolve_lz syms acc) as [out|]; [|discriminate].
    inversion H; subst. reflexivity. }
  destruct (Z.eqb btype 2); [|discriminate].
  destruct (decode_dynamic_tables r2) as [[[lit dst] r3]|] eqn:E3;
    [|discriminate].
  rewrite (decode_dynamic_tables_app _ T _ _ _ E3). cbv beta iota.
  destruct (decode_symbols lit dst r3) as [[syms r4]|] eqn:E4; [|discriminate].
  destruct (decode_dynamic_tables_valid _ _ _ _ E3) as [HVl HVd].
  rewrite (decode_symbols_app _ _ _ T _ _ HVl HVd E4). cbv beta iota.
  destruct (resolve_lz syms acc) as [out|]; [|discriminate].
  inversion H; subst. reflexivity.
Qed.

(** Same fuel on both sides: the block structure of [bits ++ T] mirrors
    that of [bits] step for step, so the left run's fuel suffices. *)
Lemma dec_stream_fuel_app : forall T,
  (length T mod 8 = 0)%nat ->
  forall f bits acc X rem,
  dec_stream_fuel f bits acc = Some (X, rem) ->
  dec_stream_fuel f (bits ++ T) acc = Some (X, rem ++ T).
Proof.
  intros T H8. induction f as [|f IH]; intros bits acc X rem H;
    [discriminate|].
  cbn [dec_stream_fuel] in H |- *.
  destruct (dec_blk bits acc) as [[[fin acc1] r]|] eqn:E; [|discriminate].
  rewrite (dec_blk_app _ T _ _ _ _ H8 E). cbv beta iota.
  destruct fin.
  { inversion H; subst. reflexivity. }
  apply IH. exact H.
Qed.

Lemma dec_stream_fuel_mono : forall f f' bits acc X rem,
  (f <= f')%nat ->
  dec_stream_fuel f bits acc = Some (X, rem) ->
  dec_stream_fuel f' bits acc = Some (X, rem).
Proof.
  induction f as [|f IH]; intros f' bits acc X rem Hle H; [discriminate|].
  destruct f' as [|f']; [lia|].
  cbn [dec_stream_fuel] in H |- *.
  destruct (dec_blk bits acc) as [[[fin acc1] r]|]; [|discriminate].
  destruct fin; [exact H|].
  apply (IH f' _ _ _ _ ltac:(lia) H).
Qed.

(* --------------------------------------------------------------------------
   8.  THE TARGET.  The wrapper's [Hdecapp] statement with the ONE forced
       premise inserted before the decode premise; binder order otherwise
       verbatim (bits T acc X rem).
   -------------------------------------------------------------------------- *)

Theorem dec_stream_from_app : forall bits T acc X rem,
  (length T mod 8 = 0)%nat ->
  dec_stream_from bits acc = Some (X, rem) ->
  dec_stream_from (bits ++ T) acc = Some (X, rem ++ T).
Proof.
  intros bits T acc X rem H8 H. unfold dec_stream_from in H |- *.
  apply (dec_stream_fuel_mono (S (length bits))).
  { rewrite length_app. lia. }
  apply (dec_stream_fuel_app T H8). exact H.
Qed.

(** Machine-checked falsification of the UNPREMISED statement (the wrapper's
    Hypothesis as spelled): the empty stored final block (0x01, LEN=0x0000,
    NLEN=0xFFFF) decodes to Some ([], []), but ONE stray appended bit shifts
    [align_byte]'s skip from 5 to 6 pad bits, the LEN/NLEN reads slide one
    position, and the decode dies — where the unpremised statement promises
    [Some ([], [false])].  So the mod-8 premise is not an artifact of this
    proof; NO premise-free [Hdecapp] is provable. *)
Example dec_stream_from_app_needs_mod8 :
  dec_stream_from (bytes_bits [1;0;0;255;255]%Z) (@nil Z) = Some ([], [])
  /\ dec_stream_from (bytes_bits [1;0;0;255;255]%Z ++ [false]) (@nil Z) = None.
Proof. split; vm_compute; reflexivity. Qed.

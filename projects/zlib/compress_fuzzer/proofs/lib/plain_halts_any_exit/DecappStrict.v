(** * DecappStrict — GAP7 (viii) ROUND 3: append-stability of the STRICT
    decoder under the (c) builder-accept guard.

    STATUS: PROVISIONAL — built against the round-3 consumer-passed but
    NOT YET FROZEN strict spelling, pinned to an earlier development run's Gap7Strict.v
    md5 (verbatim copy in this bed,
    compiled under the tree namespace).  PIN LINEAGE (both drifts
    byte-proven during the round-3 consumer pass): commissioned
    -> (pure insertion, the Requirement-6 _STMT
    appendix) -> (one hunk, the bridge premise re-spelled at
    the residue INSTANCE per q6's recommendation).  The strict CHAIN
    (lines 1-348) is byte-identical across all three pins, so the
    round-2 twin's ladder replays with only the guard-shape delta
    below.  If the freeze amends Gap7Strict.v again, re-pin and replay.

    OWNER: q7-decode fork (decapp-strict2 bed), zlib z-repro campaign.
    The round-2 twin (decapp-strict/DecappStrict.v, , vs the
    superseded ) is kept as evidence.

    THE TWIN of [Decapp.dec_stream_from_app] (Decapp.v:487-490), mirrored
    token-for-token with strict names:

      dec_stream_from_strict_app : forall bits T acc X rem,
        (length T mod 8 = 0)%nat ->
        dec_stream_from_strict bits acc = Some (X, rem) ->
        dec_stream_from_strict (bits ++ T) acc = Some (X, rem ++ T).

    THE MOD-8 PREMISE CARRIES OVER UNCHANGED: the lax counterexample
    (Decapp.v:505-508) is a stored-block stream, the stored arm is
    guard-free, so the same bits falsify the unpremised STRICT statement
    — machine-checked at the bottom of this file.  Both wrapper call
    sites instantiate T as [bytes_bits] of a byte trailer, discharged by
    [Decapp.bytes_bits_mod8]; the composition is
    [dec_stream_from_strict_app_bytes] below.

    PROOF ECONOMY (round-3 delta vs the round-2 twin): the (c) ruling
    made this bed CHEAPER, as predicted — the guard destructs simplify
    because [build_accepts_b] evaluates on the decoded header LISTS
    ([cl], [firstn]/[skipn] of [ls]), so each guard boolean is literally
    the same closed term in hypothesis and goal and one destruct reduces
    both together; no guard-specific lemma is ever needed.  Every rung
    is still the lax rung's proof replayed verbatim on the strict names,
    EXCEPT [decode_dynamic_tables_strict_app] = the lax
    [Decapp.decode_dynamic_tables_app] (Decapp.v:388-412) + TWO extra
    guard destructs (same count as round 2; only the conjunct spellings
    changed: builder-accept booleans instead of the retired enumeration
    guards).  The [decode_symbols_app] validity side condition comes
    free via [decode_dynamic_tables_strict_weaken] + the lax
    [decode_dynamic_tables_valid].

    Rungs: decode_dynamic_tables_strict_app -> dec_blk_strict_app ->
    dec_stream_strict_fuel_app + dec_stream_strict_fuel_mono (the fuel
    bridge: the two sides of the target run at fuels [S (length bits)]
    vs [S (length (bits ++ T))]) -> dec_stream_from_strict_app.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Decapp Gap7Strict.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* --------------------------------------------------------------------------
   1.  Dynamic header — the lax proof + the two guard destructs.
   -------------------------------------------------------------------------- *)

Lemma decode_dynamic_tables_strict_app : forall bits T lit dst rem,
  decode_dynamic_tables_strict bits = Some (lit, dst, rem) ->
  decode_dynamic_tables_strict (bits ++ T) = Some (lit, dst, rem ++ T).
Proof.
  intros bits T lit dst rem H.
  unfold decode_dynamic_tables_strict in H |- *.
  destruct (read_bits 5%nat bits) as [[hlit r1]|] eqn:E1; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E1). cbv beta iota.
  destruct (read_bits 5%nat r1) as [[hdist r2]|] eqn:E2; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E2). cbv beta iota.
  destruct (read_bits 4%nat r2) as [[hclen r3]|] eqn:E3; [|discriminate].
  rewrite (read_bits_app _ _ _ _ T E3). cbv beta iota.
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|] eqn:E4;
    [|discriminate].
  rewrite (read_cl_lengths_app _ _ T _ _ E4). cbv beta iota.
  (* GUARD 0 (Gap7Strict.v:200-201): [valid_lengths_b cl 7 &&
     build_accepts_b CT_CODES cl 7].  [cl] is the same value on both
     sides; keep [Ev7] for the [read_lengths_app] side condition (as in
     the lax proof).  The builder-accept boolean is a closed term of the
     decoded [cl] alone — one destruct reduces hypothesis and goal. *)
  destruct (valid_lengths_b cl 7%nat) eqn:Ev7; cbn [andb] in H |- *;
    [|discriminate].
  destruct (build_accepts_b CT_CODES cl 7); [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|] eqn:E5; [|discriminate].
  rewrite (read_lengths_app _ _ _ T _ _ (valid_lengths_b_true _ _ Ev7) E5).
  cbv beta iota.
  (* GUARD 1 (Gap7Strict.v:207-212): the A1-caps + LENS/DISTS
     builder-accept conjunction over [firstn]/[skipn] of the same [ls] —
     one boolean term, identical on both sides (the lax proof destructs
     its 2-conjunct the same way). *)
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && (length (firstn (Z.to_nat hlit + 257)%nat ls) <=? 286)%nat
            && (length (skipn (Z.to_nat hlit + 257)%nat ls) <=? 30)%nat
            && build_accepts_b CT_LENS (firstn (Z.to_nat hlit + 257)%nat ls) 9
            && build_accepts_b CT_DISTS (skipn (Z.to_nat hlit + 257)%nat ls) 6);
    [|discriminate].
  inversion H; subst. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   2.  One block — lax replay; validity for [decode_symbols_app] via
       weaken + the lax [decode_dynamic_tables_valid].
   -------------------------------------------------------------------------- *)

Lemma dec_blk_strict_app : forall bits T acc fin acc2 rem,
  (length T mod 8 = 0)%nat ->
  dec_blk_strict bits acc = Some (fin, acc2, rem) ->
  dec_blk_strict (bits ++ T) acc = Some (fin, acc2, rem ++ T).
Proof.
  intros bits T acc fin acc2 rem H8 H. unfold dec_blk_strict in H |- *.
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
  destruct (decode_dynamic_tables_strict r2) as [[[lit dst] r3]|] eqn:E3;
    [|discriminate].
  rewrite (decode_dynamic_tables_strict_app _ T _ _ _ E3). cbv beta iota.
  destruct (decode_symbols lit dst r3) as [[syms r4]|] eqn:E4; [|discriminate].
  destruct (decode_dynamic_tables_valid _ _ _ _
              (decode_dynamic_tables_strict_weaken _ _ _ _ E3)) as [HVl HVd].
  rewrite (decode_symbols_app _ _ _ T _ _ HVl HVd E4). cbv beta iota.
  destruct (resolve_lz syms acc) as [out|]; [|discriminate].
  inversion H; subst. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   3.  The stream — lax replays (same-fuel app + the fuel bridge).
   -------------------------------------------------------------------------- *)

Lemma dec_stream_strict_fuel_app : forall T,
  (length T mod 8 = 0)%nat ->
  forall f bits acc X rem,
  dec_stream_strict_fuel f bits acc = Some (X, rem) ->
  dec_stream_strict_fuel f (bits ++ T) acc = Some (X, rem ++ T).
Proof.
  intros T H8. induction f as [|f IH]; intros bits acc X rem H;
    [discriminate|].
  cbn [dec_stream_strict_fuel] in H |- *.
  destruct (dec_blk_strict bits acc) as [[[fin acc1] r]|] eqn:E; [|discriminate].
  rewrite (dec_blk_strict_app _ T _ _ _ _ H8 E). cbv beta iota.
  destruct fin.
  { inversion H; subst. reflexivity. }
  apply IH. exact H.
Qed.

Lemma dec_stream_strict_fuel_mono : forall f f' bits acc X rem,
  (f <= f')%nat ->
  dec_stream_strict_fuel f bits acc = Some (X, rem) ->
  dec_stream_strict_fuel f' bits acc = Some (X, rem).
Proof.
  induction f as [|f IH]; intros f' bits acc X rem Hle H; [discriminate|].
  destruct f' as [|f']; [lia|].
  cbn [dec_stream_strict_fuel] in H |- *.
  destruct (dec_blk_strict bits acc) as [[[fin acc1] r]|]; [|discriminate].
  destruct fin; [exact H|].
  apply (IH f' _ _ _ _ ltac:(lia) H).
Qed.

(* --------------------------------------------------------------------------
   4.  THE TARGET — mirror of Decapp.dec_stream_from_app, token-for-token.
   -------------------------------------------------------------------------- *)

Theorem dec_stream_from_strict_app : forall bits T acc X rem,
  (length T mod 8 = 0)%nat ->
  dec_stream_from_strict bits acc = Some (X, rem) ->
  dec_stream_from_strict (bits ++ T) acc = Some (X, rem ++ T).
Proof.
  intros bits T acc X rem H8 H. unfold dec_stream_from_strict in H |- *.
  apply (dec_stream_strict_fuel_mono (S (length bits))).
  { rewrite length_app. lia. }
  apply (dec_stream_strict_fuel_app T H8). exact H.
Qed.

(** The wrapper-facing composition: T = [bytes_bits] of a byte trailer,
    the mod-8 premise discharged by [Decapp.bytes_bits_mod8] (stream-side,
    unchanged from the lax consumption). *)
Corollary dec_stream_from_strict_app_bytes : forall bits bs acc X rem,
  dec_stream_from_strict bits acc = Some (X, rem) ->
  dec_stream_from_strict (bits ++ bytes_bits bs) acc
    = Some (X, rem ++ bytes_bits bs).
Proof.
  intros bits bs acc X rem H.
  exact (dec_stream_from_strict_app bits (bytes_bits bs) acc X rem
           (bytes_bits_mod8 bs) H).
Qed.

(** The mod-8 premise carries over UNCHANGED: the lax counterexample
    (Decapp.v:505-508) is a stored-block stream — guard-free — so it
    falsifies the unpremised STRICT statement identically. *)
Example dec_stream_from_strict_app_needs_mod8 :
  dec_stream_from_strict (bytes_bits [1;0;0;255;255]%Z) (@nil Z) = Some ([], [])
  /\ dec_stream_from_strict (bytes_bits [1;0;0;255;255]%Z ++ [false]) (@nil Z)
     = None.
Proof. split; vm_compute; reflexivity. Qed.

Set Printing Width 2000.
Print Assumptions decode_dynamic_tables_strict_app.
Print Assumptions dec_blk_strict_app.
Print Assumptions dec_stream_strict_fuel_app.
Print Assumptions dec_stream_strict_fuel_mono.
Print Assumptions dec_stream_from_strict_app.
Print Assumptions dec_stream_from_strict_app_bytes.

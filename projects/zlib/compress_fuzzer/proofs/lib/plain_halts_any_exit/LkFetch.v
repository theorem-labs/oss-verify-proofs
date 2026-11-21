(** * LkFetch — the fetch-loop kills for the K2/K3 good-only walks
    (q7-decode leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    The two facts every decode-site leave/fuel refutation bottoms out
    on, per the ratified Gap7LeaveKill.v header's CONSEQUENCE note
    ("the leave/fuel refutations then live INSIDE those proofs, at the
    individual NEEDBITS / room / inner-fuel sites, where they are
    decidable"):

    - [lk_fetch_no_fuel]: [inf_fetch]'s fuel [S (Z.to_nat br_have)]
      cannot exhaust — every recursion is a successful PULLBYTE, which
      keeps fuel = have + 1 invariant, and the have-0 pull answers
      FetchLeave before fuel reaches O.

    - [lk_fetch_no_starve]: under root ownership ([zr_root_own]) and
      DECLARATIVE success on the reader's stream, the fetch cannot
      starve.  At a starve point [br_have = 0], so the whole stream is
      the accumulator's [br_bits] bits; the successful [hdecode]'s
      codeword [cw0] therefore fits inside [br_bits], and the pull
      guard's owner codeword [cw] at the same root index strictly
      exceeds [br_bits].  Both spell prefixes of the same root-index
      write, so [cw0] is a proper prefix of [cw] — two distinct
      code-table words in prefix relation, refuted by
      [code_table_prefix_free].

    - [lk_decode_no_leave] / [lk_decode_no_fuel]: the [inf_decode]
      corollaries (root-only tables: the [sub] guard is false at every
      owned entry, so fetch2 never runs).

    PA-EXPORTS: lk_fetch_no_fuel, lk_fetch_no_starve,
    lk_decode_no_leave, lk_decode_no_fuel. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate
  DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6M.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6P.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Fuel: [inf_fetch] never answers FetchFuel.
   ========================================================================== *)

Lemma lk_fetch_go_no_fuel : forall f (t : ztbl) (nb : Z) (b : BR),
  0 <= br_have b -> (Z.to_nat (br_have b) < f)%nat ->
  inf_fetch_go f t nb b <> FetchFuel.
Proof.
  induction f as [|f IH]; intros t nb b Hv Hf; [lia|].
  cbn [inf_fetch_go]. cbv zeta.
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b));
    [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:EP; [|discriminate].
  assert (Hne : br_have b <> 0).
  { intro E0. rewrite (proj2 (br_pullbyte_none b) E0) in EP.
    discriminate. }
  destruct (br_pullbyte_step b b1 EP) as (Hh1 & _ & _ & _).
  apply IH; lia.
Qed.

Lemma lk_fetch_no_fuel : forall (t : ztbl) (nb : Z) (b : BR),
  0 <= br_have b -> inf_fetch t nb b <> FetchFuel.
Proof.
  intros t nb b Hv. unfold inf_fetch.
  apply lk_fetch_go_no_fuel; lia.
Qed.

(* ==========================================================================
   2.  Starvation: declarative success forbids FetchLeave.
   ========================================================================== *)

Lemma lk_fetch_go_no_starve :
  forall (T : ztbl) (root : Z) (lens : list nat) (maxBits : nat)
         (ent : nat -> Code),
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    forall f b (sym0 : nat) (rem0 : list bool) b',
      br_wf b ->
      hdecode (code_table lens maxBits) (br_stream b)
      = Some (sym0, rem0) ->
      inf_fetch_go f T root b <> FetchLeave b'.
Proof.
  intros T root lens maxBits ent Hroot HV Hown.
  induction f as [|f IH]; intros b sym0 rem0 b' Hwf Hdec;
    cbn [inf_fetch_go]; cbv zeta; [discriminate|].
  destruct (Hown (br_bits_of root b)
              (br_bits_of_in_range root b ltac:(lia)))
    as (sym & cw & Hcf & Hcwr & HTi & Hcb & Hpref).
  destruct (Z.leb_spec (c_bits (T (br_bits_of root b))) (br_bits b))
    as [Hle|Hgt]; [discriminate|].
  rewrite HTi, Hcb in Hgt.
  destruct (br_pullbyte b) as [b1|] eqn:EP.
  - (* a successful pull transports everything *)
    assert (Hwf1 : br_wf b1)
      by (apply (br_wf_pullbyte b b1); [exact Hwf | lia | exact EP]).
    pose proof (br_stream_pullbyte b b1 Hwf EP) as HS1.
    apply (IH b1 sym0 rem0 b' Hwf1).
    rewrite HS1. exact Hdec.
  - (* THE STARVE POINT: have = 0, whole stream inside the hold *)
    intros _.
    assert (Hh0 : br_have b = 0)
      by (apply (proj1 (br_pullbyte_none b)); exact EP).
    pose proof (br_stream_length b Hwf) as HL.
    rewrite Hh0 in HL.
    destruct (hdecode_sound nat (code_table lens maxBits)
                (br_stream b) sym0 rem0 Hdec)
      as (cw0 & Hin0 & Hpf0 & Hsplit).
    (* length chain: |cw0| <= bits < |cw| <= root *)
    assert (Hlen0 : (length cw0 <= length (br_stream b))%nat)
      by (rewrite Hsplit, length_app; lia).
    assert (Hcwlt : (length cw0 < length cw)%nat) by lia.
    (* cw0 spells the low bits of the same root index *)
    pose proof (br_index_spells_stream (Z.of_nat (length cw0)) root b
                  ltac:(lia) ltac:(lia)) as Hspell.
    rewrite Nat2Z.id in Hspell.
    rewrite (zr_stream_eq b) in Hspell.
    rewrite (is_prefix_firstn cw0 (br_stream b) Hpf0) in Hspell.
    (* cw0 is a proper prefix of the owner codeword cw *)
    assert (Hsub : firstn (length cw0) cw = cw0).
    { rewrite <- Hpref.
      rewrite firstn_firstn.
      rewrite Nat.min_l by lia.
      rewrite firstn_write_bits by lia.
      exact Hspell. }
    assert (Hpfx : is_prefix cw0 cw = true)
      by (apply is_prefix_of_firstn; exact Hsub).
    (* two distinct code-table words in prefix relation: refuted *)
    assert (Hin : In (cw, sym) (code_table lens maxBits))
      by (apply (proj2 (code_table_In_iff lens maxBits sym cw)); exact Hcf).
    assert (Hne : (cw0, sym0) <> (cw, sym)).
    { intro E. injection E as Ecw _.
      apply (f_equal (@length bool)) in Ecw. lia. }
    pose proof (code_table_prefix_free lens maxBits HV
                  cw0 sym0 cw sym Hin0 Hin Hne) as Hff.
    rewrite Hpfx in Hff. discriminate.
Qed.

Lemma lk_fetch_no_starve :
  forall (T : ztbl) (root : Z) (lens : list nat) (maxBits : nat)
         (ent : nat -> Code) b (sym0 : nat) (rem0 : list bool) b',
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    br_wf b ->
    hdecode (code_table lens maxBits) (br_stream b) = Some (sym0, rem0) ->
    inf_fetch T root b <> FetchLeave b'.
Proof.
  intros T root lens maxBits ent b sym0 rem0 b' Hroot HV Hown Hwf Hdec.
  unfold inf_fetch.
  exact (lk_fetch_go_no_starve T root lens maxBits ent Hroot HV Hown
           _ b sym0 rem0 b' Hwf Hdec).
Qed.

(* ==========================================================================
   3.  The [inf_decode] corollaries (root-only tables).
   ========================================================================== *)

Lemma lk_decode_no_leave :
  forall (sub : Code -> bool) (T : ztbl) (root : Z) (lens : list nat)
         (maxBits : nat) (ent : nat -> Code) b (sym0 : nat)
         (rem0 : list bool) b2,
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    (forall sym cw, code_for lens maxBits sym = Some cw ->
                    sub (ent sym) = false) ->
    br_wf b ->
    hdecode (code_table lens maxBits) (br_stream b) = Some (sym0, rem0) ->
    inf_decode sub T root b <> DecLeave b2.
Proof.
  intros sub T root lens maxBits ent b sym0 rem0 b2
         Hroot HV Hown Hsub Hwf Hdec.
  unfold inf_decode.
  pose proof (zr_fetch_hdecode T root lens maxBits ent b Hroot HV Hown
                Hwf) as HF.
  destruct (inf_fetch T root b) as [h0 b0|b0|] eqn:EF.
  - destruct HF as (sym & cw & Hcf & Hh0 & _).
    rewrite Hh0, (Hsub sym cw Hcf). discriminate.
  - exfalso.
    exact (lk_fetch_no_starve T root lens maxBits ent b sym0 rem0 b0
             Hroot HV Hown Hwf Hdec EF).
  - discriminate.
Qed.

Lemma lk_decode_no_fuel :
  forall (sub : Code -> bool) (T : ztbl) (root : Z) (lens : list nat)
         (maxBits : nat) (ent : nat -> Code) b (sym0 : nat)
         (rem0 : list bool),
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    zr_root_own T root lens maxBits ent ->
    (forall sym cw, code_for lens maxBits sym = Some cw ->
                    sub (ent sym) = false) ->
    br_wf b ->
    hdecode (code_table lens maxBits) (br_stream b) = Some (sym0, rem0) ->
    inf_decode sub T root b <> DecFuel.
Proof.
  intros sub T root lens maxBits ent b sym0 rem0
         Hroot HV Hown Hsub Hwf Hdec.
  unfold inf_decode.
  pose proof (zr_fetch_hdecode T root lens maxBits ent b Hroot HV Hown
                Hwf) as HF.
  destruct (inf_fetch T root b) as [h0 b0|b0|] eqn:EF.
  - destruct HF as (sym & cw & Hcf & Hh0 & _).
    rewrite Hh0, (Hsub sym cw Hcf). discriminate.
  - discriminate.
  - exfalso.
    destruct Hwf as (_ & _ & Hv & _).
    exact (lk_fetch_no_fuel T root b Hv EF).
Qed.

Set Printing Width 2000.
Print Assumptions lk_fetch_no_fuel.
Print Assumptions lk_fetch_no_starve.
Print Assumptions lk_decode_no_leave.
Print Assumptions lk_decode_no_fuel.

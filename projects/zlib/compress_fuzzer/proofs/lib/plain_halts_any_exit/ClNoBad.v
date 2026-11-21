(** * ClNoBad — piece 2 of the header-segment selection walk: the
    CODELENS read loop cannot go ClBad when the declarative
    [read_lengths] succeeds.

    OWNER: an earlier development run lane fork (dynsel parcel).

    The landed [Q6TblChainCore.cl_step_agree]/[cl_loop_agree] pair
    characterizes only the ClDone exit; selection needs the ClBad
    direction: at both machine reject sites ([inflate.c:948-957]'s
    repeat-with-no-previous and [:973-977]'s repeat overrun) the
    DECLARATIVE [read_lengths_fuel] returns None at the same state —
    proof bodies mirror cl_step_agree's sym>=16 arm (Q6TblChainCore
    :617-760) with the divergence at the final comparison.  Also the
    all-zero CL code census ([hdecode_zeros]) for the PreEmpty-CODES
    refutation.

    PA-EXPORTS: cl_step_bad_none, cl_loop_noBad, hdecode_zeros.
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff Inftrees DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A Q6TblChainCore Q6TblChain.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* 0.  The all-zero CL code decodes nothing.                           *)

Lemma code_for_zero_all : forall (cl : list nat) sym,
  (forall x, In x cl -> x = 0%nat) ->
  code_for cl 7%nat sym = None.
Proof.
  intros cl sym Hz. unfold code_for.
  destruct (nth_error cl sym) as [len|] eqn:E; [|reflexivity].
  rewrite (Hz len (nth_error_In cl sym E)).
  reflexivity.
Qed.

Lemma all_codes_zeros_aux : forall (cl : list nat) (L : list nat),
  (forall x, In x cl -> x = 0%nat) ->
  fold_right (code_entry cl 7%nat) [] L = [].
Proof.
  intros cl L Hz. induction L as [|k L IH]; [reflexivity|].
  cbn [fold_right]. unfold code_entry at 1.
  rewrite (code_for_zero_all cl k Hz). exact IH.
Qed.

Lemma hdecode_zeros : forall (cl : list nat) bits,
  (forall x, In x cl -> x = 0%nat) ->
  hdecode (code_table cl 7%nat) bits = (@None (nat * list bool)).
Proof.
  intros cl bits Hz.
  unfold code_table, all_codes.
  rewrite (all_codes_zeros_aux cl _ Hz).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 0b. PreEmpty forces findmax = 0 (lives HERE, outside any Strategy
       wall: the proof unfolds it_pre, so its Qed needs it_pre
       conversion-expandable; the endpoint keeps it_pre opaque and
       consumes this lemma instead). *)

Lemma it_pre_empty_findmax0 : forall ty lens codes root0 t0 t,
  it_pre ty lens codes root0 t0 = PreEmpty t ->
  it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero) = 0.
Proof.
  intros ty lens codes root0 t0 t.
  unfold it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
              (it_count (Z.to_nat codes) 0 lens zzero)) 0) eqn:Emx.
  { intros _. apply Z.eqb_eq in Emx. exact Emx. }
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|intros HE; discriminate HE].
  match goal with
  | |- context [it_incomplete ?a ?b0 ?c1] =>
      destruct (it_incomplete a b0 c1); [intros HE; discriminate HE|]
  end.
  match goal with
  | |- context [it_enough ?a ?b0] =>
      destruct (it_enough a b0); intros HE; discriminate HE
  end.
Qed.

(* ------------------------------------------------------------------ *)
(* 1.  A ClBad step happens strictly inside the count.                 *)

Lemma cl_step_bad_lt : forall T nb tot s s2 m,
  cl_step T nb tot s = ClBad s2 m -> cl_have s < tot.
Proof.
  intros T nb tot s s2 m. unfold cl_step.
  destruct (Z.leb_spec tot (cl_have s)) as [Hle|Hgt];
    [intro H; discriminate H | intros _; exact Hgt].
Qed.

(* ------------------------------------------------------------------ *)
(* 2.  THE SITE ANALYSIS: a ClBad step forces the declarative None.    *)

Lemma cl_step_bad_none :
  forall cl T nb tot s acc s2 m,
    zr_codes_fetch_bridge cl T nb ->
    br_wf (cl_br s) ->
    cl_have s = Z.of_nat (length acc) ->
    arr_eq_on (cl_lens s) (zlens acc) 0 (cl_have s) ->
    cl_step T nb tot s = ClBad s2 m ->
    forall f', read_lengths_fuel (S f') cl (Z.to_nat (tot - cl_have s)) acc
                 (br_stream (cl_br s)) = None.
Proof.
  intros cl T nb tot s acc s2 m HB Hwf Hlen Hwin HE f'.
  revert HE. unfold cl_step.
  destruct (Z.leb_spec tot (cl_have s)) as [Hle|Hgt];
    [intro HE; discriminate HE|].
  pose proof (HB (cl_br s) Hwf) as HF.
  destruct (inf_fetch T nb (cl_br s)) as [h b'|b'|] eqn:EF;
    [| intro HE; discriminate HE | intro HE; discriminate HE].
  destruct HF as (Hsb & Hwfb & Hbits & Hbb & Hval & Hdec).
  destruct (Z.ltb_spec (c_val h) 16) as [Hv16|Hv16];
    [intro HE; discriminate HE|].
  assert (Hval3 : c_val h = 16 \/ c_val h = 17 \/ c_val h = 18) by lia.
  assert (HneedS : Z.to_nat (tot - cl_have s)
                   = S (Z.to_nat (tot - cl_have s - 1))) by lia.
  destruct Hval3 as [Hv|[Hv|Hv]].
  - (* symbol 16 *)
    replace (Z.eqb (c_val h) 16) with true
      by (symmetry; apply Z.eqb_eq; exact Hv).
    rewrite Hv in Hdec.
    cbv beta iota.
    destruct (inf_nb (c_bits h + 2) b') as [b2|b2] eqn:ENB; cbv beta iota;
      [| intro HE; discriminate HE].
    destruct (inf_nb_ok (c_bits h + 2) b' b2 Hwfb ltac:(lia) ENB)
      as (Hs2 & Hwf2 & Hb2).
    destruct (Z.eqb_spec (cl_have s) 0) as [Hz|Hz]; cbv beta iota.
    + (* :948-957 repeat with no previous length *)
      intro HE. clear HE.
      assert (Hacc : acc = [])
        by (apply length_zero_iff_nil; lia).
      subst acc.
      rewrite HneedS. cbn [read_lengths_fuel].
      rewrite <- Hsb, Hdec.
      reflexivity.
    + (* the overrun check *)
      destruct (Z.ltb_spec tot
                  (cl_have s + (3 + br_bits_of 2 (br_dropbits (c_bits h) b2))))
        as [Hover|Hfit]; cbv beta iota;
        [| intro HE; discriminate HE].
      intro HE. clear HE.
      assert (Hacc0 : (0 < length acc)%nat) by lia.
      destruct (window_last (cl_lens s) acc
                  ltac:(rewrite <- Hlen; exact Hwin) Hacc0)
        as (prev & Hll & _ & _).
      assert (Hwfd1 : br_wf (br_dropbits (c_bits h) b2))
        by (apply br_wf_dropbits; [exact Hwf2 | lia]).
      pose proof (br_read_agree (c_bits h) b' Hwfb ltac:(lia)) as HA1.
      pose proof (br_read_agree (c_bits h) b2 Hwf2 ltac:(lia)) as HA2.
      rewrite Hs2 in HA2. rewrite HA1 in HA2.
      injection HA2 as Hbo12 Hst12.
      assert (Hbd1 : br_bits (br_dropbits (c_bits h) b2)
                     = br_bits b2 - c_bits h)
        by apply br_dropbits_bits.
      rewrite HneedS. cbn [read_lengths_fuel].
      rewrite <- Hsb, Hdec.
      cbv beta iota.
      replace (Nat.leb (Z.to_nat 16) 15) with false
        by (symmetry; apply Nat.leb_gt; lia).
      cbv beta iota.
      unfold rl_run.
      replace (Nat.eqb (Z.to_nat 16) 16) with true
        by (symmetry; apply Nat.eqb_eq; lia).
      cbv beta iota.
      rewrite Hll.
      cbv beta iota.
      rewrite Hst12.
      pose proof (br_read_agree 2 (br_dropbits (c_bits h) b2) Hwfd1
                    ltac:(rewrite Hbd1; lia)) as HA3.
      change (Z.to_nat 2) with 2%nat in HA3.
      rewrite HA3.
      cbv beta iota.
      assert (Hh1 : 0 <= br_hold (br_dropbits (c_bits h) b2))
        by (destruct Hwfd1 as (_ & Hh & _); lia).
      pose proof (br_bits_of_range 2 (br_dropbits (c_bits h) b2)
                    ltac:(lia) Hh1) as He2.
      change (Z.shiftl 1 2) with 4 in He2.
      replace (Nat.ltb (S (Z.to_nat (tot - cl_have s - 1)))
                 (Z.to_nat (br_bits_of 2 (br_dropbits (c_bits h) b2)) + 3))
        with true
        by (symmetry; apply Nat.ltb_lt; lia).
      reflexivity.
  - (* symbol 17 *)
    replace (Z.eqb (c_val h) 16) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb (c_val h) 17) with true
      by (symmetry; apply Z.eqb_eq; exact Hv).
    rewrite Hv in Hdec.
    cbv beta iota.
    destruct (inf_nb (c_bits h + 3) b') as [b2|b2] eqn:ENB; cbv beta iota;
      [| intro HE; discriminate HE].
    destruct (inf_nb_ok (c_bits h + 3) b' b2 Hwfb ltac:(lia) ENB)
      as (Hs2 & Hwf2 & Hb2).
    destruct (Z.ltb_spec tot
                (cl_have s + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))))
      as [Hover|Hfit]; cbv beta iota;
      [| intro HE; discriminate HE].
    intro HE. clear HE.
    assert (Hwfd1 : br_wf (br_dropbits (c_bits h) b2))
      by (apply br_wf_dropbits; [exact Hwf2 | lia]).
    pose proof (br_read_agree (c_bits h) b' Hwfb ltac:(lia)) as HA1.
    pose proof (br_read_agree (c_bits h) b2 Hwf2 ltac:(lia)) as HA2.
    rewrite Hs2 in HA2. rewrite HA1 in HA2.
    injection HA2 as Hbo12 Hst12.
    assert (Hbd1 : br_bits (br_dropbits (c_bits h) b2)
                   = br_bits b2 - c_bits h)
      by apply br_dropbits_bits.
    rewrite HneedS. cbn [read_lengths_fuel].
    rewrite <- Hsb, Hdec.
    cbv beta iota.
    replace (Nat.leb (Z.to_nat 17) 15) with false
      by (symmetry; apply Nat.leb_gt; lia).
    cbv beta iota.
    unfold rl_run.
    replace (Nat.eqb (Z.to_nat 17) 16) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb (Z.to_nat 17) 17) with true
      by (symmetry; apply Nat.eqb_eq; lia).
    cbv beta iota.
    rewrite Hst12.
    pose proof (br_read_agree 3 (br_dropbits (c_bits h) b2) Hwfd1
                  ltac:(rewrite Hbd1; lia)) as HA3.
    change (Z.to_nat 3) with 3%nat in HA3.
    rewrite HA3.
    cbv beta iota.
    assert (Hh1 : 0 <= br_hold (br_dropbits (c_bits h) b2))
      by (destruct Hwfd1 as (_ & Hh & _); lia).
    pose proof (br_bits_of_range 3 (br_dropbits (c_bits h) b2)
                  ltac:(lia) Hh1) as He2.
    change (Z.shiftl 1 3) with 8 in He2.
    replace (Nat.ltb (S (Z.to_nat (tot - cl_have s - 1)))
               (Z.to_nat (br_bits_of 3 (br_dropbits (c_bits h) b2)) + 3))
      with true
      by (symmetry; apply Nat.ltb_lt; lia).
    reflexivity.
  - (* symbol 18 *)
    replace (Z.eqb (c_val h) 16) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb (c_val h) 17) with false
      by (symmetry; apply Z.eqb_neq; lia).
    rewrite Hv in Hdec.
    cbv beta iota.
    destruct (inf_nb (c_bits h + 7) b') as [b2|b2] eqn:ENB; cbv beta iota;
      [| intro HE; discriminate HE].
    destruct (inf_nb_ok (c_bits h + 7) b' b2 Hwfb ltac:(lia) ENB)
      as (Hs2 & Hwf2 & Hb2).
    destruct (Z.ltb_spec tot
                (cl_have s + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))))
      as [Hover|Hfit]; cbv beta iota;
      [| intro HE; discriminate HE].
    intro HE. clear HE.
    assert (Hwfd1 : br_wf (br_dropbits (c_bits h) b2))
      by (apply br_wf_dropbits; [exact Hwf2 | lia]).
    pose proof (br_read_agree (c_bits h) b' Hwfb ltac:(lia)) as HA1.
    pose proof (br_read_agree (c_bits h) b2 Hwf2 ltac:(lia)) as HA2.
    rewrite Hs2 in HA2. rewrite HA1 in HA2.
    injection HA2 as Hbo12 Hst12.
    assert (Hbd1 : br_bits (br_dropbits (c_bits h) b2)
                   = br_bits b2 - c_bits h)
      by apply br_dropbits_bits.
    rewrite HneedS. cbn [read_lengths_fuel].
    rewrite <- Hsb, Hdec.
    cbv beta iota.
    replace (Nat.leb (Z.to_nat 18) 15) with false
      by (symmetry; apply Nat.leb_gt; lia).
    cbv beta iota.
    unfold rl_run.
    replace (Nat.eqb (Z.to_nat 18) 16) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb (Z.to_nat 18) 17) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb (Z.to_nat 18) 18) with true
      by (symmetry; apply Nat.eqb_eq; lia).
    cbv beta iota.
    rewrite Hst12.
    pose proof (br_read_agree 7 (br_dropbits (c_bits h) b2) Hwfd1
                  ltac:(rewrite Hbd1; lia)) as HA3.
    change (Z.to_nat 7) with 7%nat in HA3.
    rewrite HA3.
    cbv beta iota.
    assert (Hh1 : 0 <= br_hold (br_dropbits (c_bits h) b2))
      by (destruct Hwfd1 as (_ & Hh & _); lia).
    pose proof (br_bits_of_range 7 (br_dropbits (c_bits h) b2)
                  ltac:(lia) Hh1) as He2.
    change (Z.shiftl 1 7) with 128 in He2.
    replace (Nat.ltb (S (Z.to_nat (tot - cl_have s - 1)))
               (Z.to_nat (br_bits_of 7 (br_dropbits (c_bits h) b2)) + 11))
      with true
      by (symmetry; apply Nat.ltb_lt; lia).
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3.  Lifted along the loop.                                          *)

Lemma cl_loop_noBad :
  forall n cl T nb tot s acc,
    zr_codes_fetch_bridge cl T nb ->
    br_wf (cl_br s) ->
    cl_have s = Z.of_nat (length acc) ->
    (forall x, In x acc -> (x <= 15)%nat) ->
    arr_eq_on (cl_lens s) (zlens acc) 0 (cl_have s) ->
    match cl_loop n T nb tot s with
    | Some (ClBad s2 m) =>
        forall f, (Z.to_nat (tot - cl_have s) <= f)%nat ->
        read_lengths_fuel f cl (Z.to_nat (tot - cl_have s)) acc
          (br_stream (cl_br s)) = None
    | _ => True
    end.
Proof.
  induction n as [|n IH]; intros cl T nb tot s acc HB Hwf Hlen Hbnd Hwin;
    cbn [cl_loop]; [exact I|].
  pose proof (cl_step_agree cl T nb tot s acc HB Hwf Hlen Hbnd Hwin) as HS.
  destruct (cl_step T nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES; try exact I.
  - (* ClCont: transport through one trip *)
    destruct HS as (Hlt & Hwf1 & acc1 & Hlen1 & Hwin1 & Hbnd1 & Hmono
                    & Heqn).
    pose proof (IH cl T nb tot s1 acc1 HB Hwf1 Hlen1 Hbnd1 Hwin1) as HR.
    destruct (cl_loop n T nb tot s1) as [[s2|s2|s2 m2|s2|]|]; try exact I.
    intros f Hf.
    destruct f as [|f0]; [lia|].
    rewrite (Heqn f0).
    apply HR. lia.
  - (* the step itself went ClBad *)
    intros f Hf.
    pose proof (cl_step_bad_lt T nb tot s s1 m1 ES) as Hlt.
    destruct f as [|f0]; [lia|].
    exact (cl_step_bad_none cl T nb tot s acc s1 m1 HB Hwf Hlen Hwin ES f0).
Qed.

Set Printing Width 2000.
Print Assumptions hdecode_zeros.
Print Assumptions it_pre_empty_findmax0.
Print Assumptions cl_step_bad_none.
Print Assumptions cl_loop_noBad.

(** * LkClKill — the header-loop starve/fuel kills (q7-decode
    leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    Three atoms the good-only header chain (LkHdr) bottoms out on:

    - [lk_ll_go_no_starve]: LENLENS's 3-bit read loop cannot starve
      under the strict decoder's [read_3bit_vals] success (K1 at each
      pull, floors from [read_bits_length]).

    - [lk_cl_fetch_no_starve]: the CODELENS fetch at the built CL
      table cannot starve under [read_lengths]' hdecode success.  The
      table carries no ownership pack; instead a SYNTHETIC reader
      (hold = the machine's root index, 4 spare zero bytes) makes the
      fetch stop immediately, and [zr_codes_fetch_bridge] on it
      recovers the index's canonical codeword — longer than the real
      reader's whole stream, so the decodable word is its proper
      prefix, refuting prefix-freeness.

    - [lk_cl_step_no_leave] / [lk_cl_step_no_fuel] /
      [lk_cl_loop_exits]: the step- and loop-level assemblies (repeat
      reads killed by K1 against [rl_run]'s own extra-bit reads; the
      loop exits in ClDone/ClBad within its structural fuel, threading
      [cl_step_agree]'s window invariants).

    PA-EXPORTS: all five. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff Inftrees DeflateSpec Inflate
  DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A Q6TblChainCore.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkNb LkFetch.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  LENLENS: the 3-bit loop cannot starve.
   ========================================================================== *)

Lemma lk_ll_go_no_starve :
  forall f ncode have lens b (vals : list nat) (rest : list bool)
         hv' ls' b',
    br_wf b ->
    0 <= have <= ncode -> ncode <= 19 ->
    read_3bit_vals (Z.to_nat (ncode - have)) (br_stream b)
    = Some (vals, rest) ->
    ll_go f ncode have lens b <> LlLeave hv' ls' b'.
Proof.
  induction f as [|f IH];
    intros ncode have lens b vals rest hv' ls' b' Hwf Hhn Hn19 Hrd;
    cbn [ll_go]; [discriminate|].
  destruct (Z.ltb_spec have ncode) as [Hlt|Hge]; [|discriminate].
  assert (HneedS : Z.to_nat (ncode - have)
                   = S (Z.to_nat (ncode - have - 1))) by lia.
  rewrite HneedS in Hrd. cbn [read_3bit_vals] in Hrd.
  destruct (read_bits 3%nat (br_stream b)) as [[v0 r0]|] eqn:ERB;
    [|discriminate Hrd].
  pose proof (read_bits_length 3%nat (br_stream b) v0 r0 ERB) as HL3.
  destruct (inf_nb 3 b) as [b2|b2] eqn:ENB.
  - (* pull ok: recurse on the dropped reader *)
    destruct (inf_nb_ok 3 b b2 Hwf ltac:(lia) ENB) as (ES & Hwf2 & Hb2).
    assert (Hwfd : br_wf (br_dropbits 3 b2))
      by (apply br_wf_dropbits; [exact Hwf2 | lia]).
    pose proof (br_read_agree 3 b2 Hwf2 ltac:(lia)) as HA.
    change (Z.to_nat 3) with 3%nat in HA.
    rewrite ES in HA.
    rewrite ERB in HA. injection HA as Ev0 Er0.
    destruct (read_3bit_vals (Z.to_nat (ncode - have - 1)) r0)
      as [[vs r']|] eqn:ERV; [|discriminate Hrd].
    apply (IH ncode (have + 1) _ (br_dropbits 3 b2) vs r' hv' ls' b'
             Hwfd ltac:(lia) Hn19).
    replace (Z.to_nat (ncode - (have + 1)))
      with (Z.to_nat (ncode - have - 1)) by lia.
    rewrite <- Er0. exact ERV.
  - (* starve: dead against the 3-bit floor *)
    intros _.
    destruct (k1_nb_starve_short 3 b b2 Hwf ltac:(lia) ENB)
      as (Hshort & _ & _).
    change (Z.to_nat 3) with 3%nat in Hshort. lia.
Qed.

(* ==========================================================================
   2.  The CL fetch: no starve, via the synthetic reader.
   ========================================================================== *)

Lemma lk_cl_fetch_go_no_starve :
  forall (cl : list nat) (T : ztbl) (nb : Z),
    zr_codes_fetch_bridge cl T nb ->
    (forall i, 0 <= i < 2 ^ nb -> 0 <= c_bits (T i) <= nb) ->
    0 < nb <= 15 ->
    ValidLengths cl 7%nat ->
    forall f b (s0 : nat) (r0 : list bool) b',
      br_wf b ->
      hdecode (code_table cl 7%nat) (br_stream b) = Some (s0, r0) ->
      inf_fetch_go f T nb b <> FetchLeave b'.
Proof.
  intros cl T nb HB Hbits Hnb HVcl.
  induction f as [|f IH]; intros b s0 r0 b' Hwf Hdec;
    cbn [inf_fetch_go]; cbv zeta; [discriminate|].
  pose proof (DecodeBridge.br_bits_of_in_range nb b ltac:(lia)) as Hir.
  destruct (Z.leb_spec (c_bits (T (br_bits_of nb b))) (br_bits b))
    as [Hle|Hgt]; [discriminate|].
  destruct (br_pullbyte b) as [b1|] eqn:EP.
  - assert (H31 : br_bits b <= 31).
    { pose proof (Hbits (br_bits_of nb b) Hir). lia. }
    assert (Hwf1 : br_wf b1) by (apply (br_wf_pullbyte b b1 Hwf H31 EP)).
    pose proof (br_stream_pullbyte b b1 Hwf EP) as HS1.
    apply (IH b1 s0 r0 b' Hwf1).
    rewrite HS1. exact Hdec.
  - (* THE STARVE POINT *)
    intros _.
    assert (Hh0 : br_have b = 0)
      by (apply (proj1 (br_pullbyte_none b)); exact EP).
    pose proof (br_stream_length b Hwf) as HL.
    rewrite Hh0 in HL.
    destruct (hdecode_sound nat (code_table cl 7%nat)
                (br_stream b) s0 r0 Hdec)
      as (cw0 & Hin0 & Hpf0 & Hsplit).
    assert (Hlen0 : (length cw0 <= length (br_stream b))%nat)
      by (rewrite Hsplit, length_app; lia).
    pose proof (Hbits (br_bits_of nb b) Hir) as Hcbnb.
    (* the real word spells the low bits of the machine's index *)
    assert (Hspell : write_bits (length cw0) (br_bits_of nb b) = cw0).
    { pose proof (br_index_spells_stream (Z.of_nat (length cw0)) nb b
                    ltac:(lia) ltac:(lia)) as HS.
      change ZBitsBridge.br_stream with br_stream in HS.
      rewrite Nat2Z.id in HS.
      rewrite (is_prefix_firstn cw0 (br_stream b) Hpf0) in HS.
      exact HS. }
    (* the SYNTHETIC reader at the same index *)
    set (bsyn := mkBR (fun _ => 0) 4 0 (br_bits_of nb b) nb).
    assert (Hwfs : br_wf bsyn).
    { unfold bsyn, br_wf; cbn [br_bits br_hold br_have br_in].
      rewrite Z.shiftl_1_l.
      split; [lia|]. split; [lia|]. split; [lia|].
      intros i2. lia. }
    assert (Eidx : br_bits_of nb bsyn = br_bits_of nb b).
    { unfold bsyn. unfold br_bits_of at 1. cbn [br_hold].
      replace (Z.shiftl 1 nb - 1) with (Z.ones nb)
        by (rewrite Z.ones_equiv, Z.shiftl_1_l; lia).
      rewrite Z.land_ones by lia.
      apply Z.mod_small. exact Hir. }
    assert (EFsyn : inf_fetch T nb bsyn
                    = FetchOk (T (br_bits_of nb b)) bsyn).
    { unfold inf_fetch.
      change (br_have bsyn) with 4.
      change (Z.to_nat 4) with 4%nat.
      cbn [inf_fetch_go]. cbv zeta.
      rewrite Eidx.
      change (br_bits bsyn) with nb.
      rewrite (proj2 (Z.leb_le (c_bits (T (br_bits_of nb b))) nb)
                 ltac:(lia)).
      reflexivity. }
    pose proof (HB bsyn Hwfs) as HFsyn.
    rewrite EFsyn in HFsyn.
    destruct HFsyn as (_ & _ & Hcb15 & Hcbb & Hv18 & Hdecs).
    (* the synthetic word: length = the entry's bit count *)
    destruct (hdecode_sound nat (code_table cl 7%nat)
                (br_stream bsyn) _ _ Hdecs)
      as (cw1 & Hin1 & Hpf1 & Hsplit1).
    assert (Hwfd : br_wf (br_dropbits (c_bits (T (br_bits_of nb b)))
                            bsyn)).
    { apply br_wf_dropbits; [exact Hwfs|].
      change (br_bits bsyn) with nb. lia. }
    pose proof (br_stream_length bsyn Hwfs) as HLs.
    change (br_bits bsyn) with nb in HLs.
    change (br_have bsyn) with 4 in HLs.
    pose proof (br_stream_length _ Hwfd) as HLd.
    assert (Ebd : br_bits (br_dropbits (c_bits (T (br_bits_of nb b)))
                             bsyn)
                  = nb - c_bits (T (br_bits_of nb b)))
      by (rewrite br_dropbits_bits; reflexivity).
    assert (Ehd : br_have (br_dropbits (c_bits (T (br_bits_of nb b)))
                             bsyn) = 4)
      by reflexivity.
    rewrite Ebd, Ehd in HLd.
    assert (Hlcw1 : Z.of_nat (length cw1)
                    = c_bits (T (br_bits_of nb b))).
    { apply (f_equal (@length bool)) in Hsplit1.
      rewrite length_app in Hsplit1. lia. }
    (* the real word is a proper prefix of the synthetic one *)
    assert (Hsub : firstn (length cw0) cw1 = cw0).
    { assert (Hspell1 : firstn (length cw0) (br_stream bsyn)
                        = write_bits (length cw0) (br_bits_of nb b)).
      { pose proof (br_index_spells_stream (Z.of_nat (length cw0)) nb
                      bsyn ltac:(change (br_bits bsyn) with nb; lia)
                      ltac:(lia)) as HS.
        change ZBitsBridge.br_stream with br_stream in HS.
        rewrite Nat2Z.id, Eidx in HS.
        symmetry. exact HS. }
      rewrite <- (is_prefix_firstn cw1 (br_stream bsyn) Hpf1).
      rewrite firstn_firstn.
      rewrite Nat.min_l by lia.
      rewrite Hspell1. exact Hspell. }
    assert (Hpfx : is_prefix cw0 cw1 = true)
      by (apply is_prefix_of_firstn; exact Hsub).
    assert (Hne : (cw0, s0) <> (cw1, Z.to_nat (c_val
                                    (T (br_bits_of nb b))))).
    { intro E. injection E as Ecw _.
      apply (f_equal (@length bool)) in Ecw. lia. }
    pose proof (code_table_prefix_free cl 7%nat HVcl
                  cw0 s0 cw1 _ Hin0 Hin1 Hne) as Hff.
    rewrite Hpfx in Hff. discriminate.
Qed.

Lemma lk_cl_fetch_no_starve :
  forall (cl : list nat) (T : ztbl) (nb : Z) b (s0 : nat)
         (r0 : list bool) b',
    zr_codes_fetch_bridge cl T nb ->
    (forall i, 0 <= i < 2 ^ nb -> 0 <= c_bits (T i) <= nb) ->
    0 < nb <= 15 ->
    ValidLengths cl 7%nat ->
    br_wf b ->
    hdecode (code_table cl 7%nat) (br_stream b) = Some (s0, r0) ->
    inf_fetch T nb b <> FetchLeave b'.
Proof.
  intros cl T nb b s0 r0 b' HB Hbits Hnb HVcl Hwf Hdec.
  unfold inf_fetch.
  exact (lk_cl_fetch_go_no_starve cl T nb HB Hbits Hnb HVcl
           _ b s0 r0 b' Hwf Hdec).
Qed.

(* ==========================================================================
   3.  The CODELENS step: no leave, no fuel.
   ========================================================================== *)

Lemma lk_cl_step_no_fuel :
  forall cl T nb tot s,
    zr_codes_fetch_bridge cl T nb ->
    br_wf (cl_br s) ->
    cl_step T nb tot s <> ClFuel.
Proof.
  intros cl T nb tot s HB Hwf.
  unfold cl_step. cbv zeta.
  destruct (Z.leb tot (cl_have s)); [discriminate|].
  destruct (inf_fetch T nb (cl_br s)) as [h b'|b'|] eqn:EF.
  - destruct (Z.ltb (c_val h) 16); [discriminate|].
    destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                      else if Z.eqb (c_val h) 17 then c_bits h + 3
                      else c_bits h + 7) b') as [b2|b2];
      cbv beta iota; [|discriminate].
    destruct (Z.eqb (c_val h) 16); cbv beta iota.
    + destruct (Z.eqb (cl_have s) 0); cbv beta iota; [discriminate|].
      destruct (Z.ltb tot (cl_have s
                  + (3 + br_bits_of 2 (br_dropbits (c_bits h) b2))));
        cbv beta iota; discriminate.
    + destruct (Z.eqb (c_val h) 17); cbv beta iota.
      * destruct (Z.ltb tot (cl_have s
                    + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))));
          cbv beta iota; discriminate.
      * destruct (Z.ltb tot (cl_have s
                    + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))));
          cbv beta iota; discriminate.
  - discriminate.
  - exfalso.
    destruct Hwf as (_ & _ & Hv & _).
    exact (lk_fetch_no_fuel T nb (cl_br s) Hv EF).
Qed.

Lemma lk_cl_step_no_leave :
  forall cl T nb tot s (acc : list nat) f s'',
    zr_codes_fetch_bridge cl T nb ->
    (forall i, 0 <= i < 2 ^ nb -> 0 <= c_bits (T i) <= nb) ->
    0 < nb <= 15 ->
    ValidLengths cl 7%nat ->
    br_wf (cl_br s) ->
    (exists ls rest,
        read_lengths_fuel f cl (Z.to_nat (tot - cl_have s)) acc
          (br_stream (cl_br s)) = Some (ls, rest)) ->
    cl_step T nb tot s <> ClLeave s''.
Proof.
  intros cl T nb tot s acc f s'' HB Hbits Hnb HVcl Hwf
         (ls & rest & Hrlf).
  unfold cl_step. cbv zeta.
  destruct (Z.leb_spec tot (cl_have s)) as [Hle|Hgt]; [discriminate|].
  assert (HneedS : Z.to_nat (tot - cl_have s)
                   = S (Z.to_nat (tot - cl_have s - 1))) by lia.
  rewrite HneedS in Hrlf.
  destruct f as [|f2]; cbn [read_lengths_fuel] in Hrlf;
    [discriminate Hrlf|].
  destruct (hdecode (code_table cl 7%nat) (br_stream (cl_br s)))
    as [[sym r1]|] eqn:EHDCL; [|discriminate Hrlf].
  destruct (inf_fetch T nb (cl_br s)) as [h b'|b'|] eqn:EF.
  - (* fetched: only the repeat-extra NEEDBITS can leave *)
    pose proof (HB (cl_br s) Hwf) as HF.
    rewrite EF in HF.
    destruct HF as (Hsb & Hwfb & Hb15 & Hbb & Hv18 & Hdec).
    rewrite Hsb in Hdec.
    rewrite EHDCL in Hdec. injection Hdec as Esym Er1.
    destruct (Z.ltb_spec (c_val h) 16) as [Hv16|Hv16]; [discriminate|].
    destruct (inf_nb (if Z.eqb (c_val h) 16 then c_bits h + 2
                      else if Z.eqb (c_val h) 17 then c_bits h + 3
                      else c_bits h + 7) b') as [b2|b2] eqn:ENB;
      cbv beta iota.
    + (* NBOk: every outcome Conts or BADs *)
      destruct (Z.eqb (c_val h) 16); cbv beta iota.
      * destruct (Z.eqb (cl_have s) 0); cbv beta iota; [discriminate|].
        destruct (Z.ltb tot (cl_have s
                    + (3 + br_bits_of 2 (br_dropbits (c_bits h) b2))));
          cbv beta iota; discriminate.
      * destruct (Z.eqb (c_val h) 17); cbv beta iota.
        -- destruct (Z.ltb tot (cl_have s
                      + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))));
             cbv beta iota; discriminate.
        -- destruct (Z.ltb tot (cl_have s
                      + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))));
             cbv beta iota; discriminate.
    + (* NBLeave: dead against rl_run's own extra read *)
      intros _.
      assert (Hv3 : c_val h = 16 \/ c_val h = 17 \/ c_val h = 18)
        by lia.
      (* the residual computation's extra read gives the floor *)
      assert (Hlebf : Nat.leb sym 15 = false).
      { apply Nat.leb_gt. rewrite Esym. lia. }
      rewrite Hlebf in Hrlf. cbv beta iota in Hrlf.
      destruct (rl_run sym acc r1) as [[[rep k] r2]|] eqn:ERL;
        [|discriminate Hrlf].
      unfold rl_run in ERL.
      (* stream-length bookkeeping at the fetched reader *)
      assert (Hwfd1 : br_wf (br_dropbits (c_bits h) b'))
        by (apply br_wf_dropbits; [exact Hwfb | lia]).
      pose proof (br_stream_length b' Hwfb) as HLb.
      pose proof (br_stream_length _ Hwfd1) as HLd.
      assert (Ebd : br_bits (br_dropbits (c_bits h) b')
                    = br_bits b' - c_bits h)
        by (rewrite br_dropbits_bits; reflexivity).
      assert (Ehd : br_have (br_dropbits (c_bits h) b') = br_have b')
        by reflexivity.
      rewrite Ebd, Ehd in HLd.
      assert (HlenR1 : Z.of_nat (length r1)
                       = Z.of_nat (length (br_stream b')) - c_bits h)
        by (rewrite Er1; lia).
      destruct Hv3 as [Hv|[Hv|Hv]].
      * (* symbol 16: 2 extra bits *)
        rewrite (proj2 (Z.eqb_eq (c_val h) 16) Hv) in ENB.
        destruct (k1_nb_starve_short (c_bits h + 2) b' b2 Hwfb
                    ltac:(lia) ENB) as (Hshort & _ & _).
        assert (Esym16 : sym = 16%nat) by (rewrite Esym, Hv; reflexivity).
        rewrite Esym16 in ERL. cbn [Nat.eqb] in ERL.
        destruct (last_len acc); [|discriminate ERL].
        destruct (read_bits 2%nat r1) as [[e2 rm2]|] eqn:ERB;
          [|discriminate ERL].
        pose proof (read_bits_length 2%nat r1 e2 rm2 ERB) as HL2.
        lia.
      * (* symbol 17: 3 extra bits *)
        rewrite (proj2 (Z.eqb_neq (c_val h) 16) ltac:(lia)) in ENB.
        rewrite (proj2 (Z.eqb_eq (c_val h) 17) Hv) in ENB.
        destruct (k1_nb_starve_short (c_bits h + 3) b' b2 Hwfb
                    ltac:(lia) ENB) as (Hshort & _ & _).
        assert (Esym17 : sym = 17%nat) by (rewrite Esym, Hv; reflexivity).
        rewrite Esym17 in ERL. cbn [Nat.eqb] in ERL.
        destruct (read_bits 3%nat r1) as [[e3 rm3]|] eqn:ERB;
          [|discriminate ERL].
        pose proof (read_bits_length 3%nat r1 e3 rm3 ERB) as HL3.
        lia.
      * (* symbol 18: 7 extra bits *)
        rewrite (proj2 (Z.eqb_neq (c_val h) 16) ltac:(lia)) in ENB.
        rewrite (proj2 (Z.eqb_neq (c_val h) 17) ltac:(lia)) in ENB.
        destruct (k1_nb_starve_short (c_bits h + 7) b' b2 Hwfb
                    ltac:(lia) ENB) as (Hshort & _ & _).
        assert (Esym18 : sym = 18%nat) by (rewrite Esym, Hv; reflexivity).
        rewrite Esym18 in ERL. cbn [Nat.eqb] in ERL.
        destruct (read_bits 7%nat r1) as [[e7 rm7]|] eqn:ERB;
          [|discriminate ERL].
        pose proof (read_bits_length 7%nat r1 e7 rm7 ERB) as HL7.
        lia.
  - (* fetch starve: dead against the hdecode success *)
    intros _.
    exact (lk_cl_fetch_no_starve cl T nb (cl_br s) sym r1 b'
             HB Hbits Hnb HVcl Hwf EHDCL EF).
  - discriminate.
Qed.

(* ==========================================================================
   4.  The loop exits in ClDone/ClBad.
   ========================================================================== *)

Lemma lk_cl_loop_exits :
  forall n cl T nb tot (s : ClSt) (acc : list nat) f,
    zr_codes_fetch_bridge cl T nb ->
    (forall i, 0 <= i < 2 ^ nb -> 0 <= c_bits (T i) <= nb) ->
    0 < nb <= 15 ->
    ValidLengths cl 7%nat ->
    br_wf (cl_br s) ->
    cl_have s = Z.of_nat (length acc) ->
    (forall x, In x acc -> (x <= 15)%nat) ->
    arr_eq_on (cl_lens s) (zlens acc) 0 (cl_have s) ->
    (exists ls rest,
        read_lengths_fuel f cl (Z.to_nat (tot - cl_have s)) acc
          (br_stream (cl_br s)) = Some (ls, rest)) ->
    (Z.to_nat (tot - cl_have s) < n)%nat ->
    exists r, cl_loop n T nb tot s = Some r
              /\ match r with
                 | ClDone _ => True
                 | ClBad _ _ => True
                 | _ => False
                 end.
Proof.
  induction n as [|n IH];
    intros cl T nb tot s acc f HB Hbits Hnb HVcl Hwf Hlen Hbnd Hwin
           Hres Hn; [lia|].
  pose proof (cl_step_agree cl T nb tot s acc HB Hwf Hlen Hbnd Hwin)
    as HA.
  cbn [cl_loop].
  destruct (cl_step T nb tot s) as [s1|s1|s1 m1|s1|] eqn:ES.
  - (* ClCont: thread the invariants and recurse *)
    destruct HA as (Hlt & Hwf1 & acc1 & Hlen1 & Hwin1 & Hbnd1
                    & Hmono & Htrans).
    destruct Hres as (ls & rest & Hrlf).
    destruct f as [|f2].
    { exfalso.
      assert (HneedS : Z.to_nat (tot - cl_have s)
                       = S (Z.to_nat (tot - cl_have s - 1))) by lia.
      rewrite HneedS in Hrlf. cbn [read_lengths_fuel] in Hrlf.
      discriminate Hrlf. }
    rewrite (Htrans f2) in Hrlf.
    apply (IH cl T nb tot s1 acc1 f2 HB Hbits Hnb HVcl Hwf1 Hlen1
             Hbnd1 Hwin1
             (ex_intro _ ls (ex_intro _ rest Hrlf))
             ltac:(lia)).
  - exists (ClDone s1). split; [reflexivity | exact I].
  - exists (ClBad s1 m1). split; [reflexivity | exact I].
  - exfalso.
    destruct Hres as (ls & rest & Hrlf).
    exact (lk_cl_step_no_leave cl T nb tot s acc f s1 HB Hbits Hnb
             HVcl Hwf (ex_intro _ ls (ex_intro _ rest Hrlf)) ES).
  - exfalso.
    exact (lk_cl_step_no_fuel cl T nb tot s HB Hwf ES).
Qed.

Set Printing Width 2000.
Print Assumptions lk_ll_go_no_starve.
Print Assumptions lk_cl_fetch_no_starve.
Print Assumptions lk_cl_step_no_leave.
Print Assumptions lk_cl_step_no_fuel.
Print Assumptions lk_cl_loop_exits.

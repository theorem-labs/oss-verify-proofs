(** * GtCodesBridge — the ZrCodesFetchRes REDUCTION (dyn round).

    PROVENANCE: q7-decode as ACTING OWNER of the bridge (TL carrier
    precedent #6; model-rt reaped). Statement-level spec review by
    q6-fixedtbl (ALL-CLEAR): CT_CODES is
    SINGLE-LEVEL (population <= 7 = root 7), incomplete CODES have no
    o_ret=0 witness, the bridge is table-level (not walk-shaped).

    THE REDUCTION: ZrCodesFetchRes follows from the landed instruments
    (ZReproQ6M.zr_fetch_hdecode, Q6TblChainCore.accept_valid,
    DynTblOkHolds.it_model_bits_range) plus ONE missing input,
    [zr_codes_own] below — ownership of every root slot of the built
    CODES table by a coded symbol at true length with the canonical
    spelling fact, plus the val-is-the-symbol tie. That input is the
    CT_CODES keystone symbol-class territory (owner: an earlier development run per
    the stage-4 handoff; "CT_CODES instance first, no pointers").
    When it lands, ZrCodesFetchRes closes by one application. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff Inflate Inftrees InftreesBridge
  ZBitsBridge DecodeBridge DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6M
  Q6TblChainCore Q6TblChain.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** THE ONE MISSING INPUT (premise telescope = ZrCodesFetchRes verbatim;
    conclusion = the CODES ownership at maxBits 7 + the val tie).
    Supply shape chosen for the keystone: the ent witness is
    existential, per the round convention (freeze v9). *)
Definition zr_codes_own : Prop :=
  forall (cl : list nat) (lens : zarr) (cs : ztbl) out,
    length cl = 19%nat ->
    arr_eq_on lens (zlens cl) 0 19 ->
    (forall x, In x cl -> (x <= 7)%nat) ->
    it_model CT_CODES lens 19 7 (fun i => cs (0 + i)) = Some out ->
    o_ret out = 0 ->
    (exists c0 st0, it_pre CT_CODES lens 19 7 (fun i => cs (0 + i))
                    = PreGo c0 st0) ->
    exists ent,
      zr_root_own (fun i => codes_wb cs 0 (o_tbl out) (0 + i))
                  (o_bits out) cl 7%nat ent
      /\ (forall sym cw, code_for cl 7%nat sym = Some cw ->
            c_val (ent sym) = Z.of_nat sym).

Theorem zr_codes_fetch_res_from_own :
  zr_codes_own -> ZrCodesFetchRes.
Proof.
  intros HOWN. unfold ZrCodesFetchRes.
  intros cl lens cs out Hlen Hag Hbound Hmod Hret Hpre.
  destruct (HOWN cl lens cs out Hlen Hag Hbound Hmod Hret Hpre)
    as (ent & Hown & Hval).
  assert (Hc19 : 19 = Z.of_nat (length cl)) by (rewrite Hlen; reflexivity).
  assert (Hm7 : (7 <= 15)%nat) by lia.
  assert (HV : ValidLengths cl 7%nat).
  { apply valid_lengths_b_true.
    exact (accept_valid CT_CODES lens cl 19 7
             (fun i => cs (0 + i)) out 7%nat
             Hc19 Hag Hbound Hm7 Hmod Hret). }
  assert (Hroot : 1 <= o_bits out <= 15).
  { apply (it_model_bits_range CT_CODES lens 19 7
             (fun i => cs (0 + i)) out); [lia| |lia|exact Hmod|exact Hret].
    intros i Hi.
    rewrite (Hag i Hi). unfold zlens.
    assert (Hin : In (nth (Z.to_nat i) cl 0%nat) cl).
    { apply nth_In. rewrite Hlen. lia. }
    pose proof (Hbound _ Hin). lia. }
  unfold zr_codes_fetch_bridge.
  intros b Hwf.
  assert (Hr07 : 0 < o_bits out <= 15) by lia.
  pose proof (zr_fetch_hdecode
                (fun i => codes_wb cs 0 (o_tbl out) (0 + i))
                (o_bits out) cl 7%nat ent b
                Hr07 HV Hown Hwf) as HF.
  destruct (inf_fetch (fun i => codes_wb cs 0 (o_tbl out) (0 + i))
              (o_bits out) b) as [h b'|b'|] eqn:E; [|exact I|exact I].
  destruct HF as (sym & cw & Hcf & Hh & Hcb & Hs & Hwf2 & Hle & Hhd).
  pose proof (code_for_inv _ _ _ _ Hcf)
    as (len & Hnth & Hl1 & Hl7 & Hcw).
  assert (Hlcw : length cw = len) by (rewrite Hcw; apply code_bits_length).
  pose proof (code_for_range _ _ _ _ Hcf) as Hs19.
  rewrite Hlen in Hs19.
  pose proof (Hval sym cw Hcf) as Hvs.
  assert (Hvh : c_val h = Z.of_nat sym) by (rewrite Hh; exact Hvs).
  assert (Esym : Z.to_nat (c_val h) = sym)
    by (rewrite Hvh; apply Nat2Z.id).
  split; [exact Hs|].
  split; [exact Hwf2|].
  split; [rewrite Hcb, Hlcw; lia|].
  split; [exact Hle|].
  split; [rewrite Hvh; lia|].
  rewrite Esym. exact Hhd.
Qed.

Print Assumptions zr_codes_fetch_res_from_own.

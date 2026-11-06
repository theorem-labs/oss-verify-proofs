(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  codec_main_inv codec_main_lib codec_main_owehd.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE0 of the walk of LLVMFuzzerTestOneInput in the UBSan image: owe()'s cases FADER,
    BUTTON, TOUCH, VPOT and JOG (fuzz_codec.c:139-173), each from its entry in owe()'s jump table to
    the checks at 0x14a34, through its own range tests (to SPEC_E_RANGE at 0x14a2c-0x14a30) and the
    tails it shares (0x14ab4-0x14abc, 0x146b8-0x146cc, 0x14a04-0x14a08). The null and alignment
    traps on the desk (0x14534, 0x14694, 0x146dc) are dead: these kinds need a desk, so owe()'s
    prologue left a0 = 1 and a non-NULL k.desk, which is SPEC_C24 or SPEC_PC, both 16-aligned. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** ---- words and bytes ---- *)

(** lw of an unsigned field: the sign-extended word. *)
Lemma sx32_u32_o0 : forall x, 0 <= x < 2 ^ 32 ->
  (x < 2 ^ 31 /\ bv_unsigned (sx32 (Z_to_bv 64 x)) = x) \/
  (2 ^ 31 <= x /\ bv_unsigned (sx32 (Z_to_bv 64 x)) = x + (2 ^ 64 - 2 ^ 32)).
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec x (2 ^ 31)); [left | right]; (split; [lia|]); Z.div_mod_to_equations; lia.
Qed.

(** snez of an unsigned field loaded with lw. *)
Lemma snez_sx_o0 : forall c, 0 <= c < 2 ^ 32 -> (0 <? bv_unsigned (sx32 (Z_to_bv 64 c))) = negb (c =? 0).
Proof.
  intros c Hc. destruct (Z.eqb_spec c 0) as [E|E].
  - subst c. vm_compute. reflexivity.
  - cbn [negb]. apply Z.ltb_lt. destruct (sx32_u32_o0 c Hc) as [[_ H]|[_ H]]; rewrite H; lia.
Qed.

(** The window test of JOG and VPOT (addiw t, delta, -0x40; bltu t, -0x80 -> E_RANGE) on the
    sign-extended delta: taken exactly when delta is outside [-64, 63]. *)
Lemma delta_out_o0 : forall x, - 2 ^ 31 <= x < 2 ^ 31 ->
  bv_swrap 32 (x mod 18446744073709551616 + -64) mod 18446744073709551616 < 18446744073709551488 ->
  x < -64 \/ 63 < x.
Proof.
  intros x Hx H. unfold bv_swrap, bv_wrap in H.
  replace (bv_half_modulus 32) with (2 ^ 31) in H by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) in H by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma delta_in_o0 : forall x, - 2 ^ 31 <= x < 2 ^ 31 ->
  18446744073709551488 <= bv_swrap 32 (x mod 18446744073709551616 + -64) mod 18446744073709551616 ->
  -64 <= x <= 63.
Proof.
  intros x Hx H. unfold bv_swrap, bv_wrap in H.
  replace (bv_half_modulus 32) with (2 ^ 31) in H by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) in H by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma byte_eq_o0 : forall x y, x mod 2 ^ 8 = y mod 2 ^ 8 -> Z_to_bv 8 x = b8 y.
Proof. intros x y H. unfold b8. apply Z_to_bv8_mod. exact H. Qed.

(** A stored byte equals the owed one. *)
Ltac byte_tac_o0 :=
  apply byte_eq_o0; unfold u8;
  rewrite ?unsigned_lit_wrap, ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  Z.div_mod_to_equations; lia.
Ltac byte_tac2_o0 := first [ byte_tac_o0 | (rewrite Z.lor_comm; byte_tac_o0) ].

Lemma b8_small_o0 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. exact Hx.
Qed.

(** ---- the desk ---- *)

Lemma desk_range_o0 : forall k, desk_at k -> 0 <= k_p k < 2 ^ 64 /\ 0 <= k_desk k < 2 ^ 64.
Proof.
  intros k [[E1 E2]|[[E1 E2]|[E1 E2]]]; rewrite E1, E2; unfold PERS, SDESK_C24, SDESK_PC; lia.
Qed.

(** A kind that needs a desk got one of the two of the image. *)
Lemma desk_cases_o0 : forall k, desk_at k -> k_desk k <> 0 ->
  (k_desk k = SDESK_C24 /\ od_of k = Some c24) \/ (k_desk k = SDESK_PC /\ od_of k = Some pc).
Proof.
  intros k [[_ E]|[[_ E]|[_ E]]] H; [contradiction | left | right];
    (split; [exact E | unfold od_of; rewrite E; reflexivity]).
Qed.

Lemma desk_of_o0 : forall k, desk_at k -> k_desk k <> 0 ->
  exists d, od_of k = Some d /\ 8 <= d_strips d <= 24 /\
    ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)).
Proof.
  intros k HD HN. destruct (desk_cases_o0 k HD HN) as [[E O]|[E O]].
  - exists c24. split; [exact O|]. split; [cbn; lia | left; split; [exact E | reflexivity]].
  - exists pc. split; [exact O|]. split; [cbn; lia | right; split; [exact E | reflexivity]].
Qed.

(** d->strips (lbu 9(s7)), a RELRO read of SPEC_C24 or SPEC_PC. *)
Lemma desk_strips_o0 : forall m k d, relro_img m ->
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (k_desk k + 9)) 1 = Some [Z_to_bv 8 (d_strips d)].
Proof.
  intros m k d HR [[E ->] | [E ->]]; rewrite E; unfold SDESK_C24, SDESK_PC.
  - pose proof (codec_SPEC_C24_at m HR) as DK. unfold codec_SPEC_C24_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f690 _ 9 (C1 (Z_to_bv 8 0x18)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m HR) as DK. unfold codec_SPEC_PC_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f6a0 _ 9 (C1 (Z_to_bv 8 0x08)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

(** ---- the record ---- *)

Ltac kproj_o0 := cbn [with_want_rc with_want_key set_want k_run with_rc with_out
                      k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc
                      k_want k_want_len k_want_key k_want_display].

(** The encoder's code is owe()'s (codec_agree.agree_all). *)
Lemma enc_owe_rc_o0 : forall k, rec_wf k -> fst (enc_k k) = fst (owe_k k).
Proof.
  intros k (HK & HD & _ & _ & _ & _ & _ & _ & _ & HR).
  pose proof (agree_all (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                HK (od_ok_of k HD) HR) as A.
  unfold agrees in A. revert A. unfold enc_k, owe_k.
  destruct (enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
    as [rc o].
  intros [A _]. cbn [fst]. symmetry. exact A.
Qed.

(** The record owe()'s cases start from, as cells. *)
Lemma kc_run_cells_o0 : forall k,
  k_want_rc k = 0 -> k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
  kcall_cells (k_run k) =
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (fst (enc_k k)));
   CB 32 (k_before k); CB 32 (cmd_out (k_before k) (snd (enc_k k)));
   C4 (Z_to_bv 64 0); CB 24 (k_want k); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros k H1 H2 H3 H4. unfold kcall_cells, k_run, with_rc, with_out. kproj_o0.
  rewrite H1, H2, H3, H4. reflexivity.
Qed.

(** The record of a failing range test: want_rc = SPEC_E_RANGE stored at 0x14a30. *)
Lemma kc_rng_o0 : forall m A k v,
  k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
  rw_cells rsegs m A
    [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
     CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (fst (enc_k k)));
     CB 32 (k_before k); CB 32 (cmd_out (k_before k) (snd (enc_k k)));
     C4 v; CB 24 (k_want k); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  v = Z_to_bv 64 E_RANGE ->
  rw_cells rsegs m A (kcall_cells (with_want_rc (k_run k) E_RANGE)).
Proof.
  intros m A k v H2 H3 H4 H ->. unfold kcall_cells, with_want_rc, k_run, with_rc, with_out. kproj_o0.
  rewrite H2, H3, H4. exact H.
Qed.

(** 0x14a34: hand the record to the checks; leaves chk_wf of the record. *)
Ltac go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV :=
  lazymatch type of FRK with
  | rw_cells _ _ _ (kcall_cells ?K') =>
      eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K');
      [ | eassumption | eassumption | eassumption | eassumption | eassumption
        | exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FRK (conj FIN (conj FPD (conj FTX (conj FPL FSV))))))))
        | eassumption | eassumption | eassumption | eassumption ]
  end.

(** The record of a success: owe()'s bytes W in want, want_len, want_key; want_display stays 0. *)
Definition k_owed (k : kcall) (W : list byte) (wl wk : Z) : kcall :=
  with_want_key (set_want (k_run k) W wl 0) wk.

Lemma kc_owed_o0 : forall m A k W wl wk,
  rw_cells rsegs m A
    ([C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
      CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (fst (enc_k k)));
      CB 32 (k_before k); CB 32 (cmd_out (k_before k) (snd (enc_k k))); C4 (Z_to_bv 64 0)] ++ W ++
     [C8 (Z_to_bv 64 wl); C4 (Z_to_bv 64 wk); C4 (Z_to_bv 64 0)]) ->
  cells_size W = 24%nat -> k_want_rc k = 0 ->
  rw_cells rsegs m A (kcall_cells (k_owed k (cells_bytes W) wl wk)).
Proof.
  intros m A k W wl wk H HS H1.
  apply rw_cells_merge in H. rewrite HS in H.
  unfold kcall_cells, k_owed, with_want_key, set_want, k_run, with_rc, with_out. kproj_o0.
  rewrite H1. exact H.
Qed.

Ltac drop14_o0 l :=
  lazymatch l with _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?r => r end.
Ltac but_last3_o0 l :=
  lazymatch l with
  | [_; _; _] => constr:(@nil cell)
  | ?x :: ?r => let r' := but_last3_o0 r in constr:(x :: r')
  end.

(** The record at 0x14a34 after a success, as kcall_cells of k_owed. *)
Ltac owed_rec_o0 k FK HWRC :=
  lazymatch type of FK with
  | rw_cells _ _ _ ?cs =>
      let r := drop14_o0 cs in
      let W := but_last3_o0 r in
      let FK' := fresh "FRK" in
      pose proof (kc_owed_o0 _ _ k W _ _ FK eq_refl HWRC) as FK'
  end.

(** ---- what the checks need ---- *)

Lemma chk_wf_rng_o0 : forall k, rec_wf k -> fst (owe_k k) = E_RANGE ->
  chk_wf (with_want_rc (k_run k) E_RANGE).
Proof.
  intros k WF OW.
  pose proof WF as (HK & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof (enc_owe_rc_o0 k WF) as EC. rewrite OW in EC.
  assert (E1 : enc_k (with_want_rc (k_run k) E_RANGE) = enc_k k) by reflexivity.
  assert (E2 : owe_k (with_want_rc (k_run k) E_RANGE) = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2, OW. kproj_o0.
  pose proof (desk_range_o0 k HDA) as [Rp Rd].
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj_o0. rewrite EC, HWL0, HWK0, HWD0. unfold E_RANGE. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. unfold E_RANGE. intros H. discriminate H.
Qed.

Lemma chk_wf_succ_o0 : forall k w wk W wl wk', rec_wf k -> owe_k k = (0, (w, wk, 0)) ->
  firstn (length w) W = bz w -> wl = Z.of_nat (length w) -> (length w <= 24)%nat ->
  wk' = wk -> 0 <= wk < 2 ^ 32 ->
  chk_wf (k_owed k W wl wk').
Proof.
  intros k w wk W wl wk' WF OW HW HL H24 HK' HK32. subst wk'.
  pose proof WF as (HK & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof (enc_owe_rc_o0 k WF) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (k_owed k W wl wk) = enc_k k) by reflexivity.
  assert (E2 : owe_k (k_owed k W wl wk) = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2, OW. unfold k_owed. kproj_o0.
  pose proof (desk_range_o0 k HDA) as [Rp Rd].
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj_o0. rewrite EC, HWRC0. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [fst]; exact HWRC0|]. intros _. cbn [snd].
  split; [exact HW|]. split; [exact HL|]. split; [lia|]. split; reflexivity.
Qed.

(** ---- owe() of kinds 0..4 (fuzz_codec.c:139-173) ---- *)

Lemma owe_k0_ok : forall k d, k_kind k = 0 -> od_of k = Some d -> k_a k < d_strips d -> k_b k <= 1023 ->
  owe_k k = (0, ([0xb0; u8 (k_a k); u8 (k_b k / 8); u8 (0x20 + k_a k); u8 ((k_b k mod 8) * 16)],
                 KEY 1 (k_a k), 0)).
Proof.
  intros k d HK HO Ha Hb. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); [lia|]. destruct (Z.ltb_spec 1023 (k_b k)); [lia|].
  reflexivity.
Qed.

Lemma owe_k0_rng : forall k d, k_kind k = 0 -> od_of k = Some d -> d_strips d <= k_a k \/ 1023 < k_b k ->
  fst (owe_k k) = E_RANGE.
Proof.
  intros k d HK HO H. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); destruct (Z.ltb_spec 1023 (k_b k)); try reflexivity; lia.
Qed.

Lemma owe_k1_ok : forall k, k_kind k = 1 -> 0 <= k_a k <= 0x7f -> 0 <= k_b k <= 0x3f ->
  owe_k k = (0, ([0x90; u8 (k_a k); u8 (Z.lor (bit_or_0 (negb (k_c k =? 0)) 0x40) (k_b k))],
                 KEY 2 (Z.lor ((k_a k * 256) mod 2 ^ 32) (k_b k)), 0)).
Proof.
  intros k HK Ha Hb. unfold owe_k. rewrite HK. unfold owe_spec.
  destruct (od_of k); cbv beta iota zeta;
    (destruct (Z.ltb_spec 0x7f (k_a k)); [lia|]); (destruct (Z.ltb_spec 0x3f (k_b k)); [lia|]); reflexivity.
Qed.

Lemma owe_k1_rng : forall k, k_kind k = 1 -> 0x7f < k_a k \/ 0x3f < k_b k -> fst (owe_k k) = E_RANGE.
Proof.
  intros k HK H. unfold owe_k. rewrite HK. unfold owe_spec.
  destruct (od_of k); cbv beta iota zeta;
    destruct (Z.ltb_spec 0x7f (k_a k)); destruct (Z.ltb_spec 0x3f (k_b k)); try reflexivity; lia.
Qed.

Lemma owe_k2_ok : forall k d, k_kind k = 2 -> od_of k = Some d -> k_a k < d_strips d ->
  owe_k k = (0, ([0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (k_c k =? 0)) 0x40) (k_a k))], KEY 8 0, 0)).
Proof.
  intros k d HK HO Ha. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); [lia|]. reflexivity.
Qed.

Lemma owe_k2_rng : forall k d, k_kind k = 2 -> od_of k = Some d -> d_strips d <= k_a k ->
  fst (owe_k k) = E_RANGE.
Proof.
  intros k d HK HO H. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); [reflexivity | lia].
Qed.

Lemma owe_k3_ok : forall k d, k_kind k = 3 -> od_of k = Some d -> k_a k < d_strips d ->
  -64 <= k_delta k <= 63 ->
  owe_k k = (0, ([0xb0; u8 (Z.lor 0x40 (k_a k)); u8 (k_delta k + 64)], KEY 8 0, 0)).
Proof.
  intros k d HK HO Ha Hd. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); [lia|].
  destruct (Z.ltb_spec (k_delta k) (-64)); [lia|]. destruct (Z.ltb_spec 63 (k_delta k)); [lia|].
  reflexivity.
Qed.

Lemma owe_k3_rng : forall k d, k_kind k = 3 -> od_of k = Some d ->
  d_strips d <= k_a k \/ k_delta k < -64 \/ 63 < k_delta k -> fst (owe_k k) = E_RANGE.
Proof.
  intros k d HK HO H. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); destruct (Z.ltb_spec (k_delta k) (-64));
    destruct (Z.ltb_spec 63 (k_delta k)); try reflexivity; lia.
Qed.

Lemma owe_k4_ok : forall k, k_kind k = 4 -> -64 <= k_delta k <= 63 ->
  owe_k k = (0, ([0xb0; 0x5c; u8 (k_delta k + 64)], KEY 8 0, 0)).
Proof.
  intros k HK Hd. unfold owe_k. rewrite HK. unfold owe_spec.
  destruct (od_of k); cbv beta iota zeta;
    (destruct (Z.ltb_spec (k_delta k) (-64)); [lia|]); (destruct (Z.ltb_spec 63 (k_delta k)); [lia|]);
    reflexivity.
Qed.

Lemma owe_k4_rng : forall k, k_kind k = 4 -> k_delta k < -64 \/ 63 < k_delta k -> fst (owe_k k) = E_RANGE.
Proof.
  intros k HK H. unfold owe_k. rewrite HK. unfold owe_spec.
  destruct (od_of k); cbv beta iota zeta;
    destruct (Z.ltb_spec (k_delta k) (-64)); destruct (Z.ltb_spec 63 (k_delta k)); try reflexivity; lia.
Qed.

(** ---- keys and the two spilled halfwords ---- *)

Lemma key_fader_o0 : forall a, 0 <= a < 65536 -> Z.lor a 65536 = KEY 1 a.
Proof.
  intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. rewrite Z.lor_comm. reflexivity.
Qed.

Lemma key_button_o0 : forall a b, 0 <= a <= 127 -> 0 <= b <= 63 ->
  Z.lor (Z.shiftl a 8 mod 2 ^ 64) (Z.lor b 131072) = KEY 2 (Z.lor ((a * 256) mod 2 ^ 32) b).
Proof.
  intros a b Ha Hb. unfold KEY. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (a * 2 ^ 8)) by lia. rewrite (Z.mod_small (a * 256)) by lia.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  assert (L := lor_lt_pow2 (a * 256) b 16 ltac:(lia) ltac:(lia)).
  rewrite (Z.mod_small (Z.lor (a * 256) b)) by lia.
  replace (a * 2 ^ 8) with (a * 256) by lia.
  rewrite Z.lor_assoc, Z.lor_comm. reflexivity.
Qed.

Lemma key8_o0 : KEY 8 0 = 524288.
Proof. reflexivity. Qed.

Lemma le2_0990_o0 : le2 (Z_to_bv 64 2448) = [b8 0x90; b8 0x09].
Proof.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  repeat (apply f_equal2; [ apply byte_eq_o0; reflexivity | ]). reflexivity.
Qed.

Lemma le2_5cb0_o0 : le2 (Z_to_bv 64 23728) = [b8 0xb0; b8 0x5c].
Proof.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  repeat (apply f_equal2; [ apply byte_eq_o0; reflexivity | ]). reflexivity.
Qed.

(** ---- the five cases ---- *)

(** FADER, 0x14528-0x14584 and the tail 0x14ab4-0x14abc. *)
Lemma owe_fader_o0 : forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 0 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (relro_at _ _ ENV MU) as RR.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  destruct (HND ltac:(rewrite EK; reflexivity)) as [-> HDNZ]. clear HND.
  destruct (desk_of_o0 k HDK HDNZ) as (d & OD & HSTR & DKS).
  pose proof (desk_strips_o0 m1 k d RR DKS) as RD9.
  assert (BS : bv_unsigned (Z_to_bv 8 (d_strips d)) = d_strips d) by (apply b8_small_o0; lia).
  pose proof (desk_range_o0 k HDK) as [Rp Rd].
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  pose proof (sx32_u32_o0 (k_a k) Ha) as SXA. pose proof (sx32_u32_o0 (k_b k) Hb) as SXB.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 0) with 0x14528 by reflexivity.
  (* 0x14528-0x14534: the null and alignment trap on d is dead *)
  zstep. zstep. zstep. zstep.
  if_cases T;
    [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
      unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
    | clear T ].
  (* 0x14538-0x14540: a >= d->strips *)
  zstep. zstep. rewrite ?BS. zstep.
  if_cases E1.
  - zify_cond E1. rewrite ?BS in E1.
    zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k0_rng k d EK OD). lia.
  - zify_cond E1. rewrite ?BS in E1.
    assert (Ha' : k_a k < d_strips d) by lia.
    rewrite (sx32_small (k_a k)) by lia.
    (* 0x14544-0x1454c: b > 0x3ff *)
    zstep. zstep. zstep.
    if_cases E2.
    + zify_cond E2.
      zstep. zstep.
      pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply chk_wf_rng_o0; [exact WF|]. apply (owe_k0_rng k d EK OD). lia.
    + zify_cond E2.
      assert (Hb' : k_b k <= 1023) by lia.
      rewrite (sx32_small (k_b k)) by lia.
      (* 0x14550-0x14584, 0x14ab4-0x14abc: want[0..4], want_len = 5, want_key *)
      do 17 zstep.
      owed_rec_o0 k FK HWRC.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply (chk_wf_succ_o0 k [0xb0; u8 (k_a k); u8 (k_b k / 8); u8 (0x20 + k_a k); u8 ((k_b k mod 8) * 16)]
                            (KEY 1 (k_a k))).
      * exact WF.
      * apply (owe_k0_ok k d EK OD); lia.
      * cbn [cells_bytes cbytes app firstn length bz map].
        repeat (apply f_equal2; [ byte_tac2_o0 | ]). reflexivity.
      * reflexivity.
      * cbn [length]. lia.
      * apply key_fader_o0. lia.
      * apply KEY_range. lia.
Qed.

(** BUTTON, 0x14738-0x1478c: no desk. *)
Lemma owe_button_o0 : forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 1 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ _ HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  pose proof (sx32_u32_o0 (k_a k) Ha) as SXA. pose proof (sx32_u32_o0 (k_b k) Hb) as SXB.
  pose proof (snez_sx_o0 (k_c k) Hc) as SN.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 1) with 0x14738 by reflexivity.
  (* 0x14738-0x14740: a > 0x7f *)
  zstep. zstep. zstep.
  if_cases E1.
  - zify_cond E1.
    zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k1_rng k EK). lia.
  - zify_cond E1.
    assert (Ha' : k_a k <= 0x7f) by lia.
    rewrite (sx32_small (k_a k)) by lia.
    (* 0x14744-0x1474c: b > 0x3f *)
    zstep. zstep. zstep.
    if_cases E2.
    + zify_cond E2.
      zstep. zstep.
      pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply chk_wf_rng_o0; [exact WF|]. apply (owe_k1_rng k EK). lia.
    + zify_cond E2.
      assert (Hb' : k_b k <= 0x3f) by lia.
      rewrite (sx32_small (k_b k)) by lia.
      destruct (Z.eqb_spec (k_c k) 0) as [Hc0 | Hc0];
        [ assert (Hceq : (k_c k =? 0) = true) by (apply Z.eqb_eq; exact Hc0)
        | assert (Hceq : (k_c k =? 0) = false) by (apply Z.eqb_neq; exact Hc0) ];
        try rewrite Hceq in SN; cbn [negb] in SN.
      (* 0x14750-0x1478c: the key, want[0..2], want_len = 3, want_key *)
      all: do 6 zstep; rewrite SN; cbn [Z.b2z]; do 10 zstep.
      all: owed_rec_o0 k FK HWRC.
      all: go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      all: apply (chk_wf_succ_o0 k [0x90; u8 (k_a k); u8 (Z.lor (bit_or_0 (negb (k_c k =? 0)) 0x40) (k_b k))]
                                 (KEY 2 (Z.lor ((k_a k * 256) mod 2 ^ 32) (k_b k))));
        [ exact WF
        | apply (owe_k1_ok k EK); lia
        |
        | reflexivity
        | cbn [length]; lia
        | apply key_button_o0; lia
        | apply KEY_range; lia ].
      all: rewrite Hceq; cbn [negb bit_or_0].
      all: cbn [cells_bytes cbytes app firstn length bz map].
      all: repeat (apply f_equal2; [ byte_tac2_o0 | ]); reflexivity.
Qed.

(** TOUCH, 0x14688-0x146b4, then 0x146b8-0x146cc and 0x14a04-0x14a08. *)
Lemma owe_touch_o0 : forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 2 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (relro_at _ _ ENV MU) as RR.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  destruct (HND ltac:(rewrite EK; reflexivity)) as [-> HDNZ]. clear HND.
  destruct (desk_of_o0 k HDK HDNZ) as (d & OD & HSTR & DKS).
  pose proof (desk_strips_o0 m1 k d RR DKS) as RD9.
  assert (BS : bv_unsigned (Z_to_bv 8 (d_strips d)) = d_strips d) by (apply b8_small_o0; lia).
  pose proof (desk_range_o0 k HDK) as [Rp Rd].
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  pose proof (sx32_u32_o0 (k_a k) Ha) as SXA.
  pose proof (snez_sx_o0 (k_c k) Hc) as SN.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 2) with 0x14688 by reflexivity.
  (* 0x14688-0x14694: the null and alignment trap on d is dead *)
  zstep. zstep. zstep. zstep.
  if_cases T;
    [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
      unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
    | clear T ].
  (* 0x14698-0x146a0: a >= d->strips *)
  zstep. zstep. rewrite ?BS. zstep.
  if_cases E1.
  - zify_cond E1. rewrite ?BS in E1.
    zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k2_rng k d EK OD). lia.
  - zify_cond E1. rewrite ?BS in E1.
    assert (Ha' : k_a k < d_strips d) by lia.
    rewrite (sx32_small (k_a k)) by lia.
    destruct (Z.eqb_spec (k_c k) 0) as [Hc0 | Hc0];
      [ assert (Hceq : (k_c k =? 0) = true) by (apply Z.eqb_eq; exact Hc0)
      | assert (Hceq : (k_c k =? 0) = false) by (apply Z.eqb_neq; exact Hc0) ];
      try rewrite Hceq in SN; cbn [negb] in SN.
    (* 0x146a4-0x146cc, 0x14a04-0x14a08: want = 90 09 (c?0x40:0)|a, want_len = 3, want_key *)
    all: do 2 zstep; rewrite SN; cbn [Z.b2z]; do 11 zstep.
    all: owed_rec_o0 k FK HWRC.
    all: go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    all: apply (chk_wf_succ_o0 k [0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (k_c k =? 0)) 0x40) (k_a k))]
                               (KEY 8 0));
      [ exact WF
      | apply (owe_k2_ok k d EK OD); lia
      |
      | reflexivity
      | cbn [length]; lia
      | reflexivity
      | apply KEY_range; lia ].
    all: rewrite Hceq; cbn [negb bit_or_0].
    all: cbn [cells_bytes cbytes app]; rewrite le2_0990_o0; cbn [app firstn length bz map].
    all: repeat (apply f_equal2; [ first [ reflexivity | byte_tac2_o0 ] | ]); reflexivity.
Qed.

(** VPOT, 0x146d0-0x14714, then 0x146c0-0x146cc and 0x14a04-0x14a08. *)
Lemma owe_vpot_o0 : forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 3 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (relro_at _ _ ENV MU) as RR.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  destruct (HND ltac:(rewrite EK; reflexivity)) as [-> HDNZ]. clear HND.
  destruct (desk_of_o0 k HDK HDNZ) as (d & OD & HSTR & DKS).
  pose proof (desk_strips_o0 m1 k d RR DKS) as RD9.
  assert (BS : bv_unsigned (Z_to_bv 8 (d_strips d)) = d_strips d) by (apply b8_small_o0; lia).
  pose proof (desk_range_o0 k HDK) as [Rp Rd].
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  pose proof (sx32_u32_o0 (k_a k) Ha) as SXA.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 3) with 0x146d0 by reflexivity.
  (* 0x146d0-0x146dc: the null and alignment trap on d is dead *)
  zstep. zstep. zstep. zstep.
  if_cases T;
    [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
      unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
    | clear T ].
  (* 0x146e0-0x146e8: a >= d->strips *)
  zstep. zstep. rewrite ?BS. zstep.
  if_cases E1.
  - zify_cond E1. rewrite ?BS in E1.
    zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k3_rng k d EK OD). lia.
  - zify_cond E1. rewrite ?BS in E1.
    assert (Ha' : k_a k < d_strips d) by lia.
    rewrite (sx32_small (k_a k)) by lia.
    (* 0x146ec-0x146f8: the window test of delta *)
    zstep. rewrite (sx32_small (k_delta k)) by lia.
    zstep. zstep. zstep.
    if_cases E2.
    + zify_cond E2. apply delta_out_o0 in E2; [ | lia ].
      zstep. zstep.
      pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply chk_wf_rng_o0; [exact WF|]. apply (owe_k3_rng k d EK OD). lia.
    + zify_cond E2. apply delta_in_o0 in E2; [ | lia ].
      (* 0x146fc-0x14714, 0x146c0-0x146cc, 0x14a04-0x14a08 *)
      do 13 zstep.
      owed_rec_o0 k FK HWRC.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply (chk_wf_succ_o0 k [0xb0; u8 (Z.lor 0x40 (k_a k)); u8 (k_delta k + 64)] (KEY 8 0)).
      * exact WF.
      * apply (owe_k3_ok k d EK OD); lia.
      * cbn [cells_bytes cbytes app firstn length bz map].
        repeat (apply f_equal2; [ byte_tac2_o0 | ]). reflexivity.
      * reflexivity.
      * cbn [length]. lia.
      * reflexivity.
      * apply KEY_range. lia.
Qed.

(** JOG, 0x145b4-0x145cc, then 0x146b8-0x146cc and 0x14a04-0x14a08: no desk. *)
Lemma owe_jog_o0 : forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 4 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ _ HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 4) with 0x145b4 by reflexivity.
  (* 0x145b4-0x145c0: the window test of delta *)
  zstep. rewrite (sx32_small (k_delta k)) by lia.
  zstep. zstep. zstep.
  if_cases E2.
  - zify_cond E2. apply delta_out_o0 in E2; [ | lia ].
    zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k4_rng k EK). lia.
  - zify_cond E2. apply delta_in_o0 in E2; [ | lia ].
    (* 0x145c4-0x145cc, 0x146b8-0x146cc, 0x14a04-0x14a08: want = b0 5c delta+64 *)
    do 11 zstep.
    owed_rec_o0 k FK HWRC.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply (chk_wf_succ_o0 k [0xb0; 0x5c; u8 (k_delta k + 64)] (KEY 8 0)).
    + exact WF.
    + apply (owe_k4_ok k EK); lia.
    + cbn [cells_bytes cbytes app]. rewrite le2_5cb0_o0. cbn [app firstn length bz map].
      repeat (apply f_equal2; [ first [ reflexivity | byte_tac2_o0 ] | ]). reflexivity.
    + reflexivity.
    + cbn [length]. lia.
    + reflexivity.
    + apply KEY_range. lia.
Qed.

(** ---- the segment ---- *)

Lemma codec_main_owe0 : seg_owe0_stmt.
Proof.
  unfold seg_owe0_stmt. intros E n ENV CHK k WF HK4.
  pose proof WF as (HK & _).
  assert (KC : k_kind k = 0 \/ k_kind k = 1 \/ k_kind k = 2 \/ k_kind k = 3 \/ k_kind k = 4) by lia.
  destruct KC as [EK|[EK|[EK|[EK|EK]]]].
  - exact (owe_fader_o0 E n ENV CHK k WF EK).
  - exact (owe_button_o0 E n ENV CHK k WF EK).
  - exact (owe_touch_o0 E n ENV CHK k WF EK).
  - exact (owe_vpot_o0 E n ENV CHK k WF EK).
  - exact (owe_jog_o0 E n ENV CHK k WF EK).
Qed.

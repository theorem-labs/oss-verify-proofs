(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit
  InflateInvFastA InflateInvFastB InflateInvFastC InflateInvArms1 InflateInvArms3 InflateInvArms4.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma DEBT_LEN : forall NI NO WN TOT0 s c r, pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = LEN -> DEBT (mkW s c r).
Proof.
  intros NI NO WN TOT0 s c r PI Hm.
  pose (w := mkW s c r). change (mkW s c r) with w in PI |- *. change s with (w_s w) in Hm. clearbody w. clear s c r.
  dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
  destruct (len_tab _ SIr eq_refl) as (extL & TL & HextL). cbn [is_codes is_lencode is_lenbits] in TL, HextL.
  destruct (tab_ok_root _ _ _ _ TL) as (Rl1 & Rl2 & Rl3).
  pose proof (len_rep _ SIr eq_refl) as LREP. cbn [is_codes is_lencode is_lenbits] in LREP.
  binv_use. destruct BI as [B8 | BP].
  - apply (DEBT_small _ _ _ extL); [| cbn [ir_next]; lia | cbn [ir_bits]; exact B8].
    apply (tab_ok_ext LENS (fun i => cat f_codes f_lencode i)); [intros i Hi; rewrite code_at_cat; reflexivity | exact TL].
  - unfold DEBT. cbn [w_s w_r ir_bits ir_hold ir_next]. intros h' Hh' M.
    enough (G : r_bits < lcons (mkIS LEN f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
              f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
              f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk) h') by lia.
    apply (lcons_pending (cat f_codes f_lencode) f_lenbits extL LREP TL _ r_hold r_bits h');
      [intros; rewrite code_at_cat; reflexivity | reflexivity | lia | lia | exact M | exact BP].
Qed.

Theorem fastok : forall (NI NO WN TOT0 : Z) s c r,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  gFAST (mkW s c r) = true /\ pinv NI NO WN TOT0 (LOAD (inflate_fast (RESTORE (mkW s c r))))
  /\ ir_bits (w_r (LOAD (inflate_fast (RESTORE (mkW s c r))))) < 8.
Proof.
  intros NI NO WN TOT0 s c r PI Hm H6 H258 H8.
  pose proof PI as ([NI32 NO32] & _).
  assert (FC : fastcond ivar_ref (w_r (mkW s c r)) = true).
  { unfold fastcond. cbn [w_r iv_fast ivar_ref].
    rewrite (proj2 (Z.leb_le _ _) H6), (proj2 (Z.leb_le _ _) H258), (proj2 (Z.ltb_lt _ _) H8). reflexivity. }
  destruct (fast_ok ivar_ref NI NO WN TOT0 NO32 (mkW s c r) PI Hm FC (DEBT_LEN NI NO WN TOT0 s c r PI Hm)) as (G & P & B & _).
  split; [exact G|]. split; [exact P | exact B].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 208 of its 228 lines of code are new or changed and 673 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/diginet_strip_leds_encode.v, with its module paths and module names changed; 36 of its 72 lines of code are new or changed and 192 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells leds_encode_c diginet_strip_leds_encode_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma sl_land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sl_b8_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof. intros z H. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma sl_u32_small : forall r v, arg_u32 r v -> v < 2 ^ 31 -> bv_unsigned r = v.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
  apply unsigned_lit. lia.
Qed.

Lemma sl_u32_big : forall r v, arg_u32 r v -> 2 ^ 31 <= v -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned r.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite unsigned_lit_wrap. rewrite <- (Z_mod_plus_full (v - 2 ^ 32) 1).
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac close_fail :=
  cbn [strip_leds_spec cmd_out]; cbn beta iota;
  first [ split; [reflexivity | cbn [cmd_out]; assumption] | reflexivity | assumption ].

Theorem diginet_strip_leds_encode_holds : leds_encode_contract -> diginet_strip_leds_encode_contract.
Proof.
  intros LEDS. unfold leds_encode_contract, leds_encode_pre, LEDS_ENCODE, LEDS_ENCODE_DEPTH in LEDS.
  unfold diginet_strip_leds_encode_contract, diginet_strip_leds_encode_pre, DIGINET_STRIP_LEDS_ENCODE,
    DIGINET_STRIP_LEDS_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd strip bits before (HP & HD1 & HA1 & HA2 & Hnz & HC & HAL & HSO & HMI & ST & LO).
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  assert (Ls1 : strip < 2 ^ 31 -> bv_unsigned a1 = strip) by (apply sl_u32_small; exact HA1).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Lb1 : 2 ^ 31 <= strip -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (apply sl_u32_big; exact HA1).
  destruct pd as [d|].
  2: {
    cbn in HP. subst a0.
    zstep. zstep. if_true. zstep. zstep.
    finish. all: close_fail. }
  pose proof HP as HP0. destruct HP as (Hp0 & Hp8 & Hdk & Hb).
  pose proof (HD1 d eq_refl) as D1. clear HD1.
  pose proof (bytes_at_ov_read rsegs m _ _ 1 1 Hb ltac:(cbn; lia)) as HR.
  cbn [firstn skipn bz map] in HR.
  destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  zstep. zstep. if_cases K0; [exfalso; zify_cond K0; lia |].
  zstep. if_cases K1; [exfalso; zify_cond K1; lia |].
  zstep. zstep. if_cases K2; [exfalso; zify_cond K2; rewrite sl_land7_mod8 in K2; lia |].
  zstep. zstep. if_cases K3.
  - zify_cond K3. rewrite ?sl_b8_unsigned in K3 by lia.
    replace (strip_leds_spec (Some d) strip bits) with (E_RANGE, @None cmd)
      by (unfold strip_leds_spec; replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia);
          reflexivity).
    zstep. zstep. zstep. finish. all: close_fail.
  - zify_cond K3. rewrite ?sl_b8_unsigned in K3 by lia.
    assert (Us : bv_unsigned a1 = strip) by lia.
    assert (Es : a1 = Z_to_bv 64 strip) by (rewrite <- Us; symmetry; apply Z_to_bv_bv_unsigned).
    replace (strip_leds_spec (Some d) strip bits) with (leds_spec d strip bits)
      by (unfold strip_leds_spec; replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
          reflexivity).
    zstep.
    eapply evt_mono; [ eapply LEDS with (lo := lo) (d := d) (addr := strip) (bits := bits) (before := before) | ].
    + refine (conj HP0 (conj D1 (conj _ (conj Es (conj HA2 (conj Hnz (conj HC (conj HAL (conj HSO (conj HMI (conj ST LO))))))))))).
      destruct HA1 as [Bs _]. lia.
    + intros ms' PO. exact PO.
Qed.

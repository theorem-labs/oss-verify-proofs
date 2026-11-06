(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 208 of its 228 lines of code are new or changed and 673 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/diginet_strip_leds_encode.v, with its module paths and module names changed; 36 of its 72 lines of code are new or changed and 192 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/diginet_strip_leds_encode.v, with its module names and numbers changed; 19 of its 48 lines of code are new or changed and 43 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells leds_encode_c diginet_counter_leds_encode_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma cl_land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma cl_b8_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof. intros z H. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Ltac close_fail :=
  cbn [counter_leds_spec cmd_out]; cbn beta iota;
  first [ split; [reflexivity | cbn [cmd_out]; assumption] | reflexivity | assumption ].

Theorem diginet_counter_leds_encode_holds : leds_encode_contract -> diginet_counter_leds_encode_contract.
Proof.
  intros LEDS. unfold leds_encode_contract, leds_encode_pre, LEDS_ENCODE, LEDS_ENCODE_DEPTH in LEDS.
  unfold diginet_counter_leds_encode_contract, diginet_counter_leds_encode_pre, DIGINET_COUNTER_LEDS_ENCODE,
    DIGINET_COUNTER_LEDS_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd bits before (HP & HD1 & HA1 & Hnz & HC & HAL & HSO & HMI & ST & LO).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct pd as [d|].
  2: {
    cbn in HP. subst a0.
    zstep. if_true. zstep. zstep.
    finish. all: close_fail. }
  pose proof HP as HP0. destruct HP as (Hp0 & Hp8 & Hdk & Hb).
  pose proof (HD1 d eq_refl) as D1. clear HD1.
  pose proof (bytes_at_ov_read rsegs m _ _ 3 1 Hb ltac:(cbn; lia)) as HR.
  cbn [firstn skipn bz map] in HR.
  destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  zstep. if_cases K0; [exfalso; zify_cond K0; lia |].
  zstep. zstep. if_cases K1; [exfalso; zify_cond K1; lia |].
  zstep. zstep. zstep. if_cases K2; [exfalso; zify_cond K2; rewrite cl_land7_mod8 in K2; lia |].
  zstep. zstep.
  replace (counter_leds_spec (Some d) bits) with (leds_spec d (d_counter d) bits) by reflexivity.
  eapply evt_mono; [ eapply LEDS with (lo := lo) (d := d) (addr := d_counter d) (bits := bits) (before := before) | ].
  - refine (conj HP0 (conj D1 (conj _ (conj _ (conj HA1 (conj Hnz (conj HC (conj HAL (conj HSO (conj HMI (conj ST LO))))))))))).
    + lia.
    + rewrite cl_b8_unsigned by lia. reflexivity.
  - intros ms' PO. exact PO.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 77 of its 87 lines of code are new or changed and 683 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_enc diginet_fader_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_fader_encode of the plain image (0x15408, 26 instructions, leaf). Paths: p = NULL (rc -1);
    value > 1023 (rc -11, tested before strip); strip >= p->strips (rc -11, after `lbu` of byte 17 of the
    personality); else the five bytes, len = 5 and display = 0 by one `sh`, and key = strip | 0x10000. The
    register a1 / a2 holds strip / value sign-extended from bit 31, so a value or strip >= 2^31 is a huge
    unsigned number and takes the range branches. *)

(* A `sb` of a register v stores the byte v mod 256 as one cell. *)
Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                                 | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Theorem diginet_fader_encode_holds : diginet_fader_encode_contract.
Proof.
  unfold diginet_fader_encode_contract, diginet_fader_encode_pre, DIGINET_FADER_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m pd strip value before (HP & [Bs HA1] & [Bv HA2] & Hnz & HC & HMI).
  pose proof (rw_cells_len32 _ _ _ _ HC) as Hlen.
  pose proof (munch_refl [(bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ls1 : strip < 2 ^ 31 -> bv_unsigned a1 = strip) by (intros; subst a1; apply u32_small; lia).
  assert (Lb1 : 2 ^ 31 <= strip -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (intros; subst a1; apply u32_big; lia).
  assert (Ls2 : value < 2 ^ 31 -> bv_unsigned a2 = value) by (intros; subst a2; apply u32_small; lia).
  assert (Lb2 : 2 ^ 31 <= value -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a2) by (intros; subst a2; apply u32_big; lia).
  clear HA1 HA2.
  destruct pd as [d|].
  2: {
    (* p = NULL: beqz a4 to the return with a0 = -1 *)
    cbn in HP. subst a0.
    replace (fader_spec None strip value) with (E_ARG, @None cmd) by reflexivity.
    zstep. zstep. zstep. if_true. zstep.
    finish. all: close_fail HC. }
  destruct HP as [Hp0 [Hdk Hb]].
  destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  pose proof (bytes_at_ov_read rsegs m _ _ 1 1 Hb ltac:(cbn; lia)) as HR.
  cbn [firstn skipn bz map] in HR.
  zstep. zstep. zstep.
  if_cases K1.
  { exfalso. zify_cond K1. lia. }
  zstep. if_cases K2.
  { exfalso. zify_cond K2. lia. }
  zstep. zstep. zstep.
  if_cases K3.
  - (* bltu a5 (1023), a2: value > 1023 *)
    zify_cond K3.
    replace (fader_spec (Some d) strip value) with (E_RANGE, @None cmd)
      by (unfold fader_spec; replace (1023 <? value) with true by (symmetry; apply Z.ltb_lt; lia);
          rewrite orb_true_r; reflexivity).
    zstep. finish. all: close_fail HC.
  - zify_cond K3.
    assert (Uv : bv_unsigned a2 = value) by lia.
    assert (Bv' : value <= 1023) by lia.
    (* lbu a4, 17(a4): p->strips; bgeu a1, a4 *)
    zstep. zstep. if_cases K4.
    + zify_cond K4. unfold b8 in K4. rewrite b8_unsigned in K4 by lia.
      replace (fader_spec (Some d) strip value) with (E_RANGE, @None cmd)
        by (unfold fader_spec; replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia);
            reflexivity).
      zstep. finish. all: close_fail HC.
    + zify_cond K4. unfold b8 in K4. rewrite b8_unsigned in K4 by lia.
      assert (Us : bv_unsigned a1 = strip) by lia.
      replace (fader_spec (Some d) strip value)
        with (0, Some ([0xb0; u8 strip; u8 (value / 8); u8 (0x20 + strip); u8 ((value mod 8) * 16)], KEY 1 strip, 0))
        by (unfold fader_spec; replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
            replace (1023 <? value) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      (* the stores of bytes[0..4], len / display and key; ret *)
      do 17 zstep.
      finish.
      all: lazymatch goal with
           | |- rw_cells _ _ _ _ => idtac
           | |- _ => reflexivity
           end.
      destruct32 before Hlen.
      eapply rw_cells_rebytes; [exact HC | cbn; split; [reflexivity | exact I] | ].
      cbn -[le4 Z_to_bv bv_unsigned b8 u8 KEY].
      repeat match goal with |- _ :: _ = _ :: _ => f_equal end.
      all: try reflexivity.
      * unfold b8, u8. apply z8_eq. rewrite Us. bf_m strip 256.
      * unfold b8, u8. apply z8_eq. rewrite Uv, unsigned_lit_wrap. bf_m value 1024.
      * unfold b8, u8. apply z8_eq. rewrite Us, unsigned_lit_wrap. bf_m strip 256.
      * unfold b8, u8. apply z8_eq. rewrite Uv, unsigned_lit_wrap. bf_m value 1024.
      * do 3 f_equal. unfold KEY. rewrite Us. bf_e strip 256.
Qed.

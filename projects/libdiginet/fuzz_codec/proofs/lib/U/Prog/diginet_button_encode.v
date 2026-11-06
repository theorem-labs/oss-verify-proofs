(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 68 of its 78 lines of code are new or changed and 683 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_enc.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_button_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_button_encode of the UBSan image (0x15884, 27 instructions, leaf, put3 inlined); its trap (out
    not 4-aligned) is not reached under the contract's premises. Paths: out =
    NULL is excluded by the contract; button > 0x7f or id > 0x3f (rc -11; a value >= 2^31 is
    sign-extended to a huge unsigned number); else `sb` of 0x90, button and (on != 0) << 6 | id, `sh` of 3
    (len 3, display 0) and `sw` of the key button << 8 | id | 0x20000. *)

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

Theorem diginet_button_encode_holds : diginet_button_encode_contract.
Proof.
  unfold diginet_button_encode_contract, diginet_button_encode_pre, DIGINET_BUTTON_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m button id on before ([Bb HA0] & [Bi HA1] & [Bo HA2] & Hnz & HC & Hal & HMI).
  pose proof (rw_cells_len32 _ _ _ _ HC) as Hlen.
  pose proof (munch_refl [(bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ls0 : button < 2 ^ 31 -> bv_unsigned a0 = button) by (intros; subst a0; apply u32_small; lia).
  assert (Lb0 : 2 ^ 31 <= button -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a0) by (intros; subst a0; apply u32_big; lia).
  assert (Ls1 : id < 2 ^ 31 -> bv_unsigned a1 = id) by (intros; subst a1; apply u32_small; lia).
  assert (Lb1 : 2 ^ 31 <= id -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (intros; subst a1; apply u32_big; lia).
  clear HA0 HA1. subst a2.
  zstep. if_cases K1.
  { exfalso. zify_cond K1. lia. }
  zstep. zstep. zstep. zstep.
  if_cases K2.
  - (* bltu a5 (0x7f), a4: button > 0x7f *)
    zify_cond K2.
    replace (button_spec button id on) with (E_RANGE, @None cmd)
      by (unfold button_spec; replace (0x7f <? button) with true by (symmetry; apply Z.ltb_lt; lia);
          reflexivity).
    zstep. finish. all: close_fail HC.
  - zify_cond K2.
    assert (Ub : bv_unsigned a0 = button) by lia.
    zstep. zstep. if_cases K3.
    + (* bltu a5 (0x3f), a1: id > 0x3f *)
      zify_cond K3.
      replace (button_spec button id on) with (E_RANGE, @None cmd)
        by (unfold button_spec; replace (0x3f <? id) with true by (symmetry; apply Z.ltb_lt; lia);
            rewrite orb_true_r; reflexivity).
      zstep. finish. all: close_fail HC.
    + zify_cond K3.
      assert (Ui : bv_unsigned a1 = id) by lia.
      replace (button_spec button id on)
        with (0, Some ([0x90; u8 button; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) id)],
                       KEY 2 (Z.lor ((button * 256) mod 2 ^ 32) id), 0))
        by (unfold button_spec; replace (0x7f <? button) with false by (symmetry; apply Z.ltb_ge; lia);
            replace (0x3f <? id) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      (* andi a0, a3, 3; bnez: out is 4-aligned *)
      zstep. zstep. if_cases K6.
      { exfalso. zify_cond K6. apply K6, land3_aligned, Hal. }
      do 15 zstep.
      finish.
      all: lazymatch goal with
           | |- rw_cells _ _ _ _ => idtac
           | |- _ => first [ reflexivity | f_equal; apply land3_aligned, Hal ]
           end.
      destruct32 before Hlen.
      eapply rw_cells_rebytes; [exact HC | cbn; split; [reflexivity | exact I] | ].
      cbn -[le4 Z_to_bv bv_unsigned b8 u8 KEY].
      repeat match goal with |- _ :: _ = _ :: _ => f_equal end.
      all: try reflexivity.
      * unfold b8, u8. apply z8_eq. rewrite Ub. bf_m button 128.
      * (* snez a2: on != 0 *)
        rewrite snez_s32 by lia. destruct (on =? 0); cbn [negb bit_or_0 Z.b2z].
        all: unfold b8, u8; apply z8_eq; rewrite Ui, unsigned_lit_wrap; bf_m id 64.
      * do 3 f_equal. unfold KEY. rewrite Ub, Ui. bf_e2 button 128 id 64.
Qed.

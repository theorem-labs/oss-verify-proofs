(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 73 of its 83 lines of code are new or changed and 683 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_enc.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_touch_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_touch_encode of the UBSan image (0x158f0, 37 instructions, leaf, button_encode and put3
    inlined); its traps (p not 8-aligned, out not 4-aligned) are not reached under the contract's
    premises. Paths: p = NULL (rc -1); strip >= p->strips (rc -11, after `lbu` of byte 17 of the
    personality; a strip >= 2^31 is sign-extended to a huge unsigned number); strip >= 0x40 below
    p->strips cannot happen (p->strips <= 64), so button_encode's range test passes; then `sh` of 0x0990
    (bytes 0x90, 0x09), `sb` of (on != 0) << 6 | strip, `sh` of 3 (len 3, display 0), `sw` of
    button_encode's key and then `sw` of touch's key 0x80000 over it. *)

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

Theorem diginet_touch_encode_holds : diginet_touch_encode_contract.
Proof.
  unfold diginet_touch_encode_contract, diginet_touch_encode_pre, DIGINET_TOUCH_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m pd strip on before (HP & H64 & [Bs HA1] & [Bo HA2] & Hnz & HC & Hal & HMI).
  pose proof (rw_cells_len32 _ _ _ _ HC) as Hlen.
  pose proof (munch_refl [(bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ls1 : strip < 2 ^ 31 -> bv_unsigned a1 = strip) by (intros; subst a1; apply u32_small; lia).
  assert (Lb1 : 2 ^ 31 <= strip -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (intros; subst a1; apply u32_big; lia).
  clear HA1. subst a2.
  destruct pd as [d|].
  2: {
    (* p = NULL: beqz a4 to the return with a0 = -1 *)
    cbn in HP. subst a0.
    replace (touch_spec None strip on) with (E_ARG, @None cmd) by reflexivity.
    zstep. zstep. zstep. if_true. zstep.
    finish. all: close_fail HC. }
  specialize (H64 d eq_refl).
  destruct HP as [Hp0 [Hpal [Hdk Hb]]].
  destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  pose proof (bytes_at_ov_read rsegs m _ _ 1 1 Hb ltac:(cbn; lia)) as HR.
  cbn [firstn skipn bz map] in HR.
  zstep. zstep. zstep.
  if_cases K1.
  { exfalso. zify_cond K1. lia. }
  zstep. if_cases K2.
  { exfalso. zify_cond K2. lia. }
  (* andi a0, a4, 7; bnez: p is 8-aligned *)
  zstep. zstep. if_cases K5.
  { exfalso. zify_cond K5. apply K5, land7_aligned, Hpal. }
  (* lbu a0, 17(a4): p->strips; bgeu a1, a0 *)
  zstep. zstep. if_cases K3.
  - zify_cond K3. unfold b8 in K3. rewrite b8_unsigned in K3 by lia.
    replace (touch_spec (Some d) strip on) with (E_RANGE, @None cmd)
      by (unfold touch_spec; replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia);
          reflexivity).
    zstep. zstep. finish. all: close_fail HC.
  - zify_cond K3. unfold b8 in K3. rewrite b8_unsigned in K3 by lia.
    assert (Us : bv_unsigned a1 = strip) by lia.
    (* addi a0, 0x40; bltu a1, a0: strip < 0x40 since strip < p->strips <= 64 *)
    zstep. zstep. if_cases K4.
    2: { exfalso. zify_cond K4. lia. }
    replace (touch_spec (Some d) strip on)
      with (0, Some ([0x90; u8 9; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) strip)], KEY 8 0, 0))
      by (unfold touch_spec, button_spec, with_key;
          replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
          replace (0x3f <? strip) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    (* andi a0, a3, 3; bnez: out is 4-aligned *)
    zstep. zstep. if_cases K6.
    { exfalso. zify_cond K6. apply K6, land3_aligned, Hal. }
    (* bytes[0..2], len / display, button_encode's key; li a1, 1; beqz a1 (not taken) *)
    do 15 zstep. if_false.
    (* touch's key; ret *)
    do 3 zstep.
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
    + unfold b8. apply z8_eq. reflexivity.
    + (* snez a2: on != 0 *)
      rewrite snez_s32 by lia. destruct (on =? 0); cbn [negb bit_or_0 Z.b2z].
      all: unfold b8, u8; apply z8_eq; rewrite Us, unsigned_lit_wrap; bf_m strip 64.
Qed.

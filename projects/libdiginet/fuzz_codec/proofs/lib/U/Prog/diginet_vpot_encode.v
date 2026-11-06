(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 81 of its 91 lines of code are new or changed and 683 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_enc.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_vpot_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_vpot_encode of the UBSan image (0x15984, 26 instructions, leaf, delta_byte and put3 inlined);
    its traps (p not 8-aligned, out not 4-aligned) are not reached under the contract's premises.
    Paths: p = NULL (rc -1); delta_byte's test (`addiw a5, a2, -64`, `bltu` against -128) fails unless
    -64 <= delta <= 63 (rc -11); strip >= p->strips (rc -11, after `lbu` of byte 17 of the personality;
    a strip >= 2^31 is sign-extended to a huge unsigned number); else `sb` of 0xb0, strip | 0x40 and
    delta + 64, `sh` of 3 (len 3, display 0) and `sw` of the key 0x80000. *)

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

Theorem diginet_vpot_encode_holds : diginet_vpot_encode_contract.
Proof.
  unfold diginet_vpot_encode_contract, diginet_vpot_encode_pre, DIGINET_VPOT_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m pd strip delta before (HP & [Bs HA1] & [Bd HA2] & Hnz & HC & Hal & HMI).
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
    replace (vpot_spec None strip delta) with (E_ARG, @None cmd) by reflexivity.
    zstep. zstep. zstep. if_true. zstep.
    finish. all: close_fail HC. }
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
  zstep. zstep. zstep. zstep.
  if_cases K3.
  - (* bltu a5, a6: delta out of [-64, 63] *)
    zify_cond K3.
    assert (K3' : delta < -64 \/ 63 < delta).
    { destruct (Z.le_gt_cases (-64) delta); [|lia]. destruct (Z.le_gt_cases delta 63); [|lia].
      exfalso. apply (proj1 (Z.lt_nge _ _) K3). apply (proj2 (delta_range delta ltac:(lia))). lia. }
    replace (vpot_spec (Some d) strip delta) with (E_RANGE, @None cmd)
      by (unfold vpot_spec; destruct K3' as [K|K];
          [ replace (delta <? -64) with true by (symmetry; apply Z.ltb_lt; lia); rewrite orb_true_r
          | replace (63 <? delta) with true by (symmetry; apply Z.ltb_lt; lia); rewrite orb_true_r ];
          reflexivity).
    zstep. finish. all: close_fail HC.
  - zify_cond K3. apply delta_range in K3; [|lia].
    (* lbu a4, 17(a4): p->strips; bgeu a1, a4 *)
    zstep. zstep. if_cases K4.
    + zify_cond K4. unfold b8 in K4. rewrite b8_unsigned in K4 by lia.
      replace (vpot_spec (Some d) strip delta) with (E_RANGE, @None cmd)
        by (unfold vpot_spec; replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia);
            reflexivity).
      zstep. finish. all: close_fail HC.
    + zify_cond K4. unfold b8 in K4. rewrite b8_unsigned in K4 by lia.
      assert (Us : bv_unsigned a1 = strip) by lia.
      replace (vpot_spec (Some d) strip delta)
        with (0, Some ([0xb0; u8 (Z.lor 0x40 strip); u8 (delta + 64)], KEY 8 0, 0))
        by (unfold vpot_spec; replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
            replace (delta <? -64) with false by (symmetry; apply Z.ltb_ge; lia);
            replace (63 <? delta) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      (* bytes[0..2], len / display, key; ret *)
      (* andi a0, a3, 3; bnez: out is 4-aligned *)
      zstep. zstep. if_cases K6.
      { exfalso. zify_cond K6. apply K6, land3_aligned, Hal. }
      do 11 zstep.
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
      * unfold b8, u8. apply z8_eq. rewrite Us, unsigned_lit_wrap. bf_m strip 256.
      * unfold b8, u8. apply z8_eq. rewrite unsigned_lit_wrap. rewrite !Z.mod_small by lia. reflexivity.
Qed.

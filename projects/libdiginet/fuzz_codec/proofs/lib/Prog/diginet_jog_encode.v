(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 50 of its 60 lines of code are new or changed and 683 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_enc diginet_jog_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_jog_encode of the plain image (0x15590, 20 instructions, leaf). Paths: out = NULL is excluded
    by the contract; delta_byte's test (`addiw a0, a0, -64`, then `bgeu` against -128) fails unless
    -64 <= delta <= 63 (rc -11); else `sh` of 0x5cb0 (bytes 0xb0, 0x5c), `sb` of delta + 64, `sh` of 3
    (len 3, display 0) and `sw` of the key 0x80000. *)

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

Theorem diginet_jog_encode_holds : diginet_jog_encode_contract.
Proof.
  unfold diginet_jog_encode_contract, diginet_jog_encode_pre, DIGINET_JOG_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m delta before ([Bd HA0] & Hnz & HC & HMI).
  pose proof (rw_cells_len32 _ _ _ _ HC) as Hlen.
  pose proof (munch_refl [(bv_unsigned a1, bv_unsigned a1 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  subst a0.
  zstep. if_cases K1.
  { exfalso. zify_cond K1. lia. }
  zstep. zstep. zstep. zstep.
  if_cases K2.
  - zify_cond K2. apply delta_range in K2; [|lia].
    replace (jog_spec delta) with (0, Some ([0xb0; 0x5c; u8 (delta + 64)], KEY 8 0, 0))
      by (unfold jog_spec; replace (delta <? -64) with false by (symmetry; apply Z.ltb_ge; lia);
          replace (63 <? delta) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    do 11 zstep.
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
    + unfold b8. apply z8_eq. reflexivity.
    + unfold b8, u8. apply z8_eq. rewrite unsigned_lit_wrap. rewrite !Z.mod_small by lia. reflexivity.
  - zify_cond K2.
    assert (K2' : delta < -64 \/ 63 < delta).
    { destruct (Z.le_gt_cases (-64) delta); [|lia]. destruct (Z.le_gt_cases delta 63); [|lia].
      exfalso. apply (proj1 (Z.lt_nge _ _) K2). apply (proj2 (delta_range delta ltac:(lia))). lia. }
    replace (jog_spec delta) with (E_RANGE, @None cmd)
      by (unfold jog_spec; destruct K2' as [K|K];
          [ replace (delta <? -64) with true by (symmetry; apply Z.ltb_lt; lia)
          | replace (63 <? delta) with true by (symmetry; apply Z.ltb_lt; lia); rewrite orb_true_r ];
          reflexivity).
    zstep. zstep. finish. all: close_fail HC.
Qed.

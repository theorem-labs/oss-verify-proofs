(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 107 of its 117 lines of code are new or changed and 683 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells diginet_meter_encode_c
  diginet_meter_encode_arith.
Import ListNotations.
Open Scope Z_scope.

(** diginet_meter_encode of the plain image (0x15794, 53 instructions), walked with the tactics of
    libreac/fuzz_knock's leaves. The NULL tests and the full unsigned range tests of channel and
    segments return before the frame; then the frame of 16 bytes, the device byte read with `lb` before
    any store, mask = not (-1 << segments) by `sllw`, the payload [mch; mask >> 7; mask & 0x7f] stored at
    sp+0xd..0xf, sysex_encode inlined (the device bit-7 test gives E_ARG, the payload bit-7 loop never
    branches since each payload byte is below 0x80), and the success stores to out. *)

(* A byte store of any register v writes the byte Z_to_bv 8 (bv_unsigned v) (le1 v unfolds to it). *)
#[local] Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

#[local] Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

(* A return on a failing path before any store to out: out unchanged. *)
#[local] Ltac ret_unchanged := finish; try (cbn; split; [reflexivity | assumption]); try reflexivity.

Theorem diginet_meter_encode_holds : diginet_meter_encode_contract.
Proof.
  unfold diginet_meter_encode_contract, diginet_meter_encode_pre, DIGINET_METER_ENCODE, DIGINET_METER_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd channel right segments before
         (HP & [RC HA1] & [RR HA2] & [RS HA3] & HO & OUT & SPO & HMI & ST & LO).
  subst a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a4, bv_unsigned a4 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a4) as Ra4. unfold bv_modulus in Ra4.
  assert (LB : length before = 32%nat) by (destruct OUT as [[[W _] _] _]; exact W).
  destruct pd as [d|].
  2: {
    cbn [pers_arg] in HP. subst a0.
    zstep. zstep. zstep. if_true. zstep.
    ret_unchanged. }
  destruct HP as [HA0 [DOK HPB]].
  destruct DOK as [Hdev _].
  assert (HR : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + 16)) 1 = Some [Z_to_bv 8 (d_dev d)]).
  { pose proof (bytes_at_read rsegs m _ _ 0 1 HPB ltac:(lia) ltac:(cbn; lia)) as R.
    rewrite Z.add_0_r in R. exact R. }
  clear HPB.
  zstep. zstep. zstep. if_false. zstep. if_false.
  zstep. zstep. zstep.
  if_cases K1.
  { zify_cond K1.
    assert (Hc : 32 <= channel)
      by (revert K1; rewrite u_s32 by lia; destruct (Z.ltb_spec channel (2^31)); intros K1; lia).
    rewrite (meter_range_ch d channel right segments Hc).
    zstep. ret_unchanged. }
  zify_cond K1.
  assert (Hc : channel < 32)
    by (revert K1; rewrite u_s32 by lia; destruct (Z.ltb_spec channel (2^31)); intros K1; lia).
  zstep. zstep.
  if_cases K2.
  { zify_cond K2.
    assert (Hs : 14 < segments)
      by (revert K2; rewrite u_s32 by lia; destruct (Z.ltb_spec segments (2^31)); intros K2; lia).
    rewrite (meter_range_seg d channel right segments Hs).
    zstep. ret_unchanged. }
  zify_cond K2.
  assert (Hs : segments <= 14)
    by (revert K2; rewrite u_s32 by lia; destruct (Z.ltb_spec segments (2^31)); intros K2; lia).
  clear K1 K2.
  rewrite (s32_small channel) by lia. rewrite (s32_small segments) by lia.
  pose proof (mch_range channel right ltac:(lia)) as HM.
  pose proof (mask_bytes segments ltac:(lia)) as [HMH HML].
  carve_frame 16%nat ST.
  (* addi sp; addi a0; snez a6, a2; lb a2, 0x10(a5) (the device byte) *)
  zstep. zstep. zstep. zstep.
  clear HR.
  (* sllw; slli; not; or; srli; andi *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (reg_ch channel right) by lia. rewrite (reg_mask segments) by lia.
  (* sb a1, 0xd(sp); sb a5, 0xe(sp); sb a3, 0xf(sp) *)
  zstep. zstep. zstep.
  rewrite !byte_lit in FR.
  rewrite (sxb_z8 (d_dev d)) by lia.
  destruct (Z.ltb_spec (d_dev d) 128) as [Hlo|Hhi].
  2: {
    (* bltz a2: the device byte has bit 7 set: E_ARG *)
    rewrite (meter_dev_hi d channel right segments ltac:(lia) ltac:(lia) ltac:(lia)).
    zstep. if_cases K3; [| exfalso; zify_cond K3; lia].
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    ret_unchanged. }
  rewrite (meter_ok d channel right segments ltac:(lia) ltac:(lia) ltac:(lia)).
  zstep. if_cases K3; [exfalso; zify_cond K3; lia |].
  clear K3.
  (* addi a0, 3; addi a3, sp, 0xd; the three rounds of the payload check: lb; bltz (bit 7 is clear in each
     payload byte, so never taken); addi; addi; bnez *)
  zstep. zstep.
  zstep. rewrite sxb_z8_lo by lia. zstep. if_cases K4; [exfalso; zify_cond K4; lia|]. clear K4.
  zstep. zstep. zstep. if_true.
  zstep. rewrite sxb_z8_lo by lia. zstep. if_cases K4; [exfalso; zify_cond K4; lia|]. clear K4.
  zstep. zstep. zstep. if_true.
  zstep. rewrite sxb_z8_lo by lia. zstep. if_cases K4; [exfalso; zify_cond K4; lia|]. clear K4.
  zstep. zstep. zstep. if_false.
  (* lui; addi; lbu x3 (the payload read back); lui; or (the key); addi; addi *)
  do 9 zstep.
  (* sh 0x13f0; sb device; sb 0x10; sb payload x3 (an addi between); sb 0xf7; sh len 8; sw key *)
  do 10 zstep.
  (* j; addi sp; ret *)
  zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  rewrite (key_eq (mch channel right)) in OUT by lia.
  rewrite !byte_lit, !byte_unsigned, byte_m9 in OUT.
  finish.
  all: try reflexivity.
  do 32 (destruct before as [|?x before]; [discriminate LB|]).
  destruct before; [|discriminate LB].
  eapply rw_cells_rebytes; [exact OUT | split; [reflexivity | exact I] | ].
  cbn [cells_bytes cbytes]. rewrite le2_5104, le2_8.
  cbn [cmd_out bz map app firstn skipn length].
  reflexivity.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 136 of its 147 lines of code are new or changed and 682 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe diginet_meter_encode_arith.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_sysex_encode_c
  diginet_meter_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_meter_encode of the UBSan image (0x15bdc, 46 instructions), walked with the tactics of
    libreac/fuzz_knock's leaves. The frame of 32 bytes (ra, s0, s1 saved first), the NULL tests and the
    full unsigned range tests of channel and segments, the payload [mch; mask >> 7; mask & 0x7f] stored at
    sp+5..7, the `p & 7` trap test (not taken: p mod 8 = 0), the device byte read with `lbu` after the frame
    stores (the personality bytes lie outside the frame), the call of diginet_sysex_encode (its contract is
    the premise) and, on rc = 0, the `out & 3` trap test (not taken: out mod 4 = 0) and the key store. *)

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

(* The three payload bytes the body stores at sp+5..7 of its frame, as the bytes sysex_encode reads. *)
Lemma frame_payload : forall m A j b1 b2 b3 c1 c2 c3,
  rw_cells rsegs m A [CB 5 j; C1 b1; C1 b2; C1 b3; C8 c1; C8 c2; C8 c3] ->
  bytes_at rsegs m (A + 5) [b1; b2; b3].
Proof.
  intros m A j b1 b2 b3 c1 c2 c3 [[Hwf Hb] _].
  destruct Hwf as [Hj _]. cbn [cell_wf] in Hj.
  cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite Hj in Hb.
  assert (E : [b1] ++ [b2] ++ [b3] ++ le8 c1 ++ le8 c2 ++ le8 c3 ++ []
              = [b1; b2; b3] ++ (le8 c1 ++ le8 c2 ++ le8 c3 ++ [])) by reflexivity.
  rewrite E in Hb. apply bytes_at_app in Hb as [Hb _]. exact Hb.
Qed.

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

(* A return on a failing path before any store to out: out unchanged. *)
#[local] Ltac ret_unchanged := finish; try (cbn; split; [reflexivity | assumption]); try reflexivity.

(* From 0x15c78 on a path that has not written out: mv a0, a4; ld ra, s0, s1; addi sp; ret. *)
#[local] Ltac exit_unchanged FR ST sp :=
  zstep; zstep; zstep; zstep;
  release_frame FR ST (bv_unsigned sp);
  zstep; zstep;
  ret_unchanged.

Theorem diginet_meter_encode_holds : diginet_sysex_encode_contract -> diginet_meter_encode_contract.
Proof.
  intros SYSEX.
  unfold diginet_sysex_encode_contract, diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE, DIGINET_SYSEX_ENCODE_DEPTH
    in SYSEX.
  unfold diginet_meter_encode_contract, diginet_meter_encode_pre, DIGINET_METER_ENCODE, DIGINET_METER_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd channel right segments before
         (HP & HD1 & [RC HA1] & [RR HA2] & [RS HA3] & HO & OUT & HA4 & SPO & HMI & ST & LO).
  subst a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a4, bv_unsigned a4 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp.
  pose proof (bv_unsigned_in_range 64 a4) as Ra4. unfold bv_modulus in Ra4.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Ra4.
  assert (LO0 : 0 <= lo) by (destruct ST as [W _]; exact W).
  assert (LB : length before = 32%nat) by (destruct OUT as [[[W _] _] _]; exact W).
  carve_frame 32%nat ST.
  destruct pd as [d|].
  2: {
    cbn [pers_arg] in HP. subst a0. clear HD1.
    do 7 zstep. if_true.
    exit_unchanged FR ST sp. }
  destruct HP as [HA0 [HA08 [DOK HPB]]].
  destruct DOK as [Hdev _].
  specialize (HD1 d eq_refl). unfold disj in HD1.
  change (bz [d_dev d; d_strips d; d_chars d; d_counter d])
    with [b8 (d_dev d); b8 (d_strips d); b8 (d_chars d); b8 (d_counter d)] in HPB.
  do 7 zstep. if_false. zstep. if_false.
  zstep. zstep. zstep.
  if_cases K1.
  { zify_cond K1.
    assert (Hc : 32 <= channel)
      by (revert K1; rewrite u_s32 by lia; destruct (Z.ltb_spec channel (2^31)); intros K1; lia).
    rewrite (meter_range_ch d channel right segments Hc).
    exit_unchanged FR ST sp. }
  zify_cond K1.
  assert (Hc : channel < 32)
    by (revert K1; rewrite u_s32 by lia; destruct (Z.ltb_spec channel (2^31)); intros K1; lia).
  zstep. zstep.
  if_cases K2.
  { zify_cond K2.
    assert (Hs : 14 < segments)
      by (revert K2; rewrite u_s32 by lia; destruct (Z.ltb_spec segments (2^31)); intros K2; lia).
    rewrite (meter_range_seg d channel right segments Hs).
    exit_unchanged FR ST sp. }
  zify_cond K2.
  assert (Hs : segments <= 14)
    by (revert K2; rewrite u_s32 by lia; destruct (Z.ltb_spec segments (2^31)); intros K2; lia).
  clear K1 K2.
  rewrite (s32_small channel) by lia. rewrite (s32_small segments) by lia.
  pose proof (mch_range channel right ltac:(lia)) as HM.
  pose proof (mask_bytes segments ltac:(lia)) as [HMH HML].
  (* addi a4, -1; snez; sllw; andi a4, a0, 7; slli; not; or s1; srli; andi *)
  do 9 zstep.
  rewrite (reg_ch channel right) by lia. rewrite (reg_mask segments) by lia.
  (* sb s1, 5(sp); sb a1, 6(sp); sb a2, 7(sp) *)
  zstep. zstep. zstep.
  rewrite !byte_lit in FR.
  (* bnez a4: the UBSan alignment trap on p (p mod 8 = 0), not taken *)
  zstep. if_cases T1; [exfalso; zify_cond T1; rewrite land7_mod8 in T1; lia |]. clear T1.
  (* lbu a0, 0x10(a0): the device byte, read after the frame stores (D1: p+16..19 lie outside the frame) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HR : ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned a0 + 16)) 1 = Some [Z_to_bv 8 (d_dev d)])
      by (pose proof (bytes_at_read rsegs mm _ _ 0 1 HPB ltac:(lia) ltac:(cbn; lia)) as R;
          rewrite Z.add_0_r in R; exact R)
  end.
  zstep. clear HR.
  cbv beta. rewrite byte_val by lia.
  (* addi a1, 16; addi a2, sp, 5; addi a3, 3; mv a4, s0; jal diginet_sysex_encode *)
  do 5 zstep.
  assert (U32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (U27 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -27)) = bv_unsigned sp + -27) by (apply unsigned_lit; lia).
  pose proof (frame_payload _ _ _ _ _ _ _ _ _ FR) as PL.
  replace (bv_unsigned sp + -32 + 5) with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -27))) in PL by lia.
  rewrite <- U32 in ST.
  call SYSEX.
  { refine (conj (conj _ eq_refl) (conj (conj _ eq_refl) (conj _ (conj PL (conj eq_refl (conj HO (conj OUT
              (conj HA4 (conj _ (conj _ (conj _ (conj HMI (conj ST _))))))))))))).
    all: unfold disj; cbn [length]; lia. }
  rewrite U32 in PC. rename PC into ST.
  cbn [zb map] in POST. rewrite !byte_val in POST by lia.
  destruct (Z.ltb_spec (d_dev d) 128) as [Hlo|Hhi].
  2: {
    (* sysex_encode refuses the device byte (bit 7 set): E_ARG, out unchanged *)
    rewrite sysex_meter_hi in POST by lia. cbv beta iota in POST. destruct POST as [EA OUT2]. subst x2.
    rewrite (meter_dev_hi d channel right segments ltac:(lia) ltac:(lia) ltac:(lia)).
    (* mv a4, a0; bnez a0 (taken) *)
    zstep. zstep. if_true.
    exit_unchanged FR ST sp. }
  rewrite (sysex_meter_ok (d_dev d) channel right segments) in POST by lia.
  cbv beta iota in POST. destruct POST as [EA OUT2]. subst x2.
  rewrite (meter_ok d channel right segments ltac:(lia) ltac:(lia) ltac:(lia)).
  (* mv a4, a0; bnez a0 (rc = 0: not taken) *)
  zstep. zstep. if_false.
  (* andi a0, s0, 3; bnez a0: the UBSan alignment trap on out (out mod 4 = 0), not taken *)
  zstep. zstep. if_cases T2; [exfalso; zify_cond T2; rewrite land3_mod4 in T2; lia |]. clear T2.
  (* lui a0, 0x40; or a0, s1, a0; sw a0, 0x1c(s0): the key *)
  zstep. zstep. zstep.
  (* mv a0, a4; ld ra, s0, s1; addi sp; ret *)
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  rewrite (key_eq (mch channel right)) in OUT2 by lia.
  finish.
  all: try reflexivity.
  do 32 (destruct before as [|?x before]; [discriminate LB|]).
  destruct before; [|discriminate LB].
  eapply rw_cells_rebytes; [exact OUT2 | split; [reflexivity | exact I] | ].
  cbn [cells_bytes cbytes cmd_out bz map app firstn skipn length].
  reflexivity.
Qed.

(** diginet_seg7 (diginet_codec.c:308-335; the leaf at 0x15af4, 12 instructions). 0x15af4-0x15af8 `addi -0x20`,
    `andi 0xff` form i = (c - 0x20) mod 256 from the low byte c of a0 (seg7_idx); 0x15b00 `bltu a1(90), a0` sends
    i > 90 to 0x15b1c `li a0, -1`; else 0x15b04-0x15b14 load the word i of the table at 0x104e0 (.rodata: mem_inv
    gives the image's words, codec_img.v codec_seg7_read) with `lw` and return it (seg7_tab_eq: that table is
    DgnLib.v's seg7_table). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells codec_img diginet_seg7_c.
Import ListNotations.
Open Scope Z_scope.

(* 0x15af4-0x15af8: the index from the low byte of a0 *)
Lemma seg7_idx : forall x, 0 <= x ->
  Z.land ((x + -32) mod 18446744073709551616) 255 = (x mod 256 - 0x20) mod 256.
Proof.
  intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  rewrite (Z.mod_eq (x + -32) 18446744073709551616) by lia.
  rewrite (Z.mod_eq x 256) by lia.
  replace (x + -32 - 18446744073709551616 * ((x + -32) / 18446744073709551616))
    with ((x + -32) + (- ((x + -32) / 18446744073709551616 * 72057594037927936)) * 256) by lia.
  replace (x - 256 * (x / 256) - 0x20) with ((x + -32) + (- (x / 256)) * 256) by lia.
  rewrite !Z.mod_add by lia. reflexivity.
Qed.

(* the image's table is DgnLib.v's *)
Lemma seg7_tab_eq : forall i, 0 <= i <= 90 ->
  nth (Z.to_nat i) codec_seg7_tab 0 = nth (Z.to_nat i) seg7_table (-1).
Proof.
  intros i Hi. replace codec_seg7_tab with seg7_table by (vm_compute; reflexivity).
  apply nth_indep. change (length seg7_table) with 91%nat. lia.
Qed.

Theorem diginet_seg7_holds : diginet_seg7_contract.
Proof.
  unfold diginet_seg7_contract, diginet_seg7_pre, DIGINET_SEG7.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HMI.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
  zstep. zstep. zstep. zstep.
  remember (Z.land ((bv_unsigned a0 + -32) mod 18446744073709551616) 255) as i eqn:Hi.
  assert (Ei : i = (bv_unsigned a0 mod 256 - 0x20) mod 256) by (rewrite Hi; apply seg7_idx; lia).
  assert (Ri : 0 <= i < 256) by (rewrite Ei; apply Z.mod_pos_bound; lia).
  clear Hi.
  if_cases K1.
  - (* i > 90: no glyph *)
    zify_cond K1.
    zstep. zstep.
    replace (seg7_spec (bv_unsigned a0 mod 256)) with (-1)
      by (unfold seg7_spec; cbv zeta; rewrite <- Ei; rewrite (proj2 (Z.leb_gt i 90)) by lia; reflexivity).
    finish.
  - (* i <= 90: the table word *)
    zify_cond K1.
    zstep. zstep. zstep. zstep.
    replace (66784 + i ≪ 2) with (CODEC_SEG7 + 4 * i)
      by (unfold CODEC_SEG7; rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (codec_seg7_read m i HMI ltac:(lia)) as HR.
    zstep.
    rewrite (codec_seg7_sx i ltac:(lia)).
    zstep.
    replace (seg7_spec (bv_unsigned a0 mod 256)) with (nth (Z.to_nat i) codec_seg7_tab 0)
      by (unfold seg7_spec; cbv zeta; rewrite <- Ei; rewrite (proj2 (Z.leb_le i 90)) by lia;
          apply seg7_tab_eq; lia).
    finish.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 208 of its 228 lines of code are new or changed and 673 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells diginet_strip_leds_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** The body (0x15868, 35 instructions, leaf, no frame): a4 = p, a0 = -1; NULL p or out returns -1;
    bits > 0x7f (unsigned compare of the sign-extended u32) returns -11; strip >= p->strips (lbu
    p+17, unsigned compare) returns -11; p->device (lb p+16) negative returns -1; strip > 0x7f
    returns -11; else out gets f0 13 device 20 strip bits f7, len 7, display 0, key strip | 0x50000,
    and a0 = 0. Each early return gives the spec's (rc, None). *)

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

(** lb of a byte x: the register is x sign-extended from bit 7. *)
Lemma sl_signed_b8 : forall x, 0 <= x < 256 -> bv_signed (b8 x) = if x <? 128 then x else x - 256.
Proof.
  intros x H. unfold bv_signed. rewrite sl_b8_unsigned by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  destruct (Z.ltb_spec x 128); cbv beta iota.
  - rewrite Z.mod_small by lia. lia.
  - replace (x + 128) with ((x - 128) + 1 * 256) by lia. rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma sl_sxb_lo : forall x, 0 <= x < 128 -> bv_unsigned (sxb (b8 x)) = x.
Proof.
  intros x H. unfold sxb. rewrite unsigned_lit_wrap, sl_signed_b8 by lia.
  destruct (Z.ltb_spec x 128) as [Hl|Hl]; [|lia]. cbv beta iota. apply Z.mod_small. lia.
Qed.

Lemma sl_sxb_hi : forall x, 128 <= x < 256 -> bv_unsigned (sxb (b8 x)) = x - 256 + 2 ^ 64.
Proof.
  intros x H. unfold sxb. rewrite unsigned_lit_wrap, sl_signed_b8 by lia.
  destruct (Z.ltb_spec x 128) as [Hl|Hl]; [lia|]. cbv beta iota.
  rewrite <- (Z_mod_plus_full (x - 256) 1). rewrite Z.mod_small by lia. lia.
Qed.

Lemma sl_tb7_hi : forall x, 128 <= x < 256 -> Z.testbit x 7 = true.
Proof.
  intros x H. rewrite Z.testbit_true by lia. change (2 ^ 7) with 128.
  assert (E : x / 128 = 1) by (Z.div_mod_to_equations; lia). rewrite E. reflexivity.
Qed.

(** srli (slli bits 8 | strip) 8 = bits. *)
Lemma sl_pack : forall b s, 0 <= b < 128 -> 0 <= s < 256 ->
  Z.shiftr (Z.lor (Z.shiftl b 8 mod 18446744073709551616) s) 8 = b.
Proof.
  intros b s Hb Hs.
  rewrite (Z.mod_small (Z.shiftl b 8)) by (rewrite Z.shiftl_mul_pow2 by lia; cbn; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sl_key : forall s, 0 <= s < 65536 -> Z.lor s 327680 = KEY 5 s.
Proof.
  intros s H. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by first [lia | cbn; lia]. rewrite Z.lor_comm. reflexivity.
Qed.

Lemma sl_leds_ok : forall d a b, 0 <= a < 128 -> 0 <= b < 128 -> 0 <= d_dev d < 128 ->
  leds_spec d a b = (0, Some ([0xf0; 0x13; d_dev d; 0x20; a; b; 0xf7], KEY 5 a, 0)).
Proof.
  intros d a b Ha Hb Hd. unfold leds_spec, sysex_spec, u8.
  replace (0x7f <? b) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0x7f <? d_dev d) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (Z.mod_small a 256), (Z.mod_small b 256) by lia.
  cbn [existsb].
  rewrite (testbit_high_false a 7 7), (testbit_high_false b 7 7) by first [lia | cbn; lia].
  reflexivity.
Qed.

Lemma sl_le2_5104 : le2 (Z_to_bv 64 5104) = [b8 240; b8 19].
Proof.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  apply (f_equal2 cons); [apply bv_eq; reflexivity|].
  apply (f_equal2 cons); [apply bv_eq; reflexivity|reflexivity].
Qed.

Lemma sl_le2_7 : le2 (Z_to_bv 64 7) = [b8 7; b8 0].
Proof.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  apply (f_equal2 cons); [apply bv_eq; reflexivity|].
  apply (f_equal2 cons); [apply bv_eq; reflexivity|reflexivity].
Qed.

Lemma sl_rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Ltac sl_destruct32 l H :=
  do 32 (let x := fresh "x" in destruct l as [|x l]; [cbn in H; lia|]);
  destruct l; [|cbn in H; lia].

(** The 32 bytes of out after the eight stores of the success path are cmd_out of the command. *)
Lemma sl_out_cells : forall m A before dv s b k,
  length before = 32%nat ->
  rw_cells rsegs m A
    [C2 (Z_to_bv 64 5104); C1 (b8 dv); C1 (b8 32); C1 (b8 s); C1 (b8 b); C1 (b8 247);
     CB 17 (firstn 17 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 2 before)))))));
     C2 (Z_to_bv 64 7);
     CB 2 (firstn 2 (skipn 19 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 2 before))))))));
     C4 (Z_to_bv 64 k)] ->
  rw_cells rsegs m A [CB 32 (cmd_out before (Some ([0xf0; 0x13; dv; 0x20; s; b; 0xf7], k, 0)))].
Proof.
  intros m A before dv s b k Hlen HC. sl_destruct32 before Hlen.
  eapply sl_rw_cells_rebytes; [exact HC | cbn; split; [reflexivity | exact I] | ].
  cbn [cells_bytes cbytes cmd_out bz map app firstn skipn length Z.of_nat Pos.of_succ_nat Pos.succ].
  rewrite sl_le2_5104, sl_le2_7. reflexivity.
Qed.

Ltac sl_close_fail HC :=
  cbn beta iota;
  lazymatch goal with
  | |- _ /\ _ => split; [reflexivity | exact HC]
  | |- _ = _ => reflexivity
  | |- _ => exact HC
  end.

Theorem diginet_strip_leds_encode_holds : diginet_strip_leds_encode_contract.
Proof.
  unfold diginet_strip_leds_encode_contract, diginet_strip_leds_encode_pre, DIGINET_STRIP_LEDS_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m pd strip bits before (HP & HA1 & HA2 & Hnz & HC & HMI).
  assert (Hlen : length before = 32%nat) by (destruct HC as [[[Hw _] _] _]; exact Hw).
  pose proof (munch_refl [(bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ls1 : strip < 2 ^ 31 -> bv_unsigned a1 = strip) by (apply sl_u32_small; exact HA1).
  assert (Lb1 : 2 ^ 31 <= strip -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (apply sl_u32_big; exact HA1).
  assert (Ls2 : bits < 2 ^ 31 -> bv_unsigned a2 = bits) by (apply sl_u32_small; exact HA2).
  assert (Lb2 : 2 ^ 31 <= bits -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a2) by (apply sl_u32_big; exact HA2).
  destruct HA1 as [Bs _]. destruct HA2 as [Bb _].
  destruct pd as [d|].
  2: {
    (* p = NULL: beqz a4 at 0x15870 returns a0 = -1 *)
    cbn in HP. subst a0.
    replace (strip_leds_spec None strip bits) with (E_ARG, @None cmd) by reflexivity.
    zstep. zstep. zstep. if_true. zstep.
    finish. all: sl_close_fail HC. }
  destruct HP as [Hp0 [Hdk Hb]].
  destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  pose proof (bytes_at_ov_read rsegs m _ _ 1 1 Hb ltac:(cbn; lia)) as HR1.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 1 Hb ltac:(cbn; lia)) as HR0.
  cbn [firstn skipn bz map] in HR1, HR0.
  clear Hb.
  zstep. zstep. zstep.
  if_cases K1.
  { exfalso. zify_cond K1. lia. }
  zstep. if_cases K2.
  { exfalso. zify_cond K2. lia. }
  zstep. zstep.
  (* 0x1587c bltu 0x7f, bits *)
  if_cases K3.
  { zify_cond K3.
    assert (Hb7 : 127 < bits)
      by (destruct (Z_lt_le_dec bits (2 ^ 31)) as [H|H]; [specialize (Ls2 H); lia | lia]).
    replace (strip_leds_spec (Some d) strip bits) with (E_RANGE, @None cmd)
      by (unfold strip_leds_spec, leds_spec; destruct (d_strips d <=? strip); [reflexivity|];
          replace (0x7f <? bits) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    zstep. zstep. finish. all: sl_close_fail HC. }
  zify_cond K3.
  assert (Ub : bv_unsigned a2 = bits)
    by (destruct (Z_lt_le_dec bits (2 ^ 31)) as [H|H]; [exact (Ls2 H) | specialize (Lb2 H); lia]).
  (* 0x15880 lbu strips; 0x15884 bgeu strip, strips *)
  zstep. zstep.
  if_cases K4.
  { zify_cond K4. rewrite sl_b8_unsigned in K4 by lia.
    assert (Hs : d_strips d <= strip)
      by (destruct (Z_lt_le_dec strip (2 ^ 31)) as [H|H]; [specialize (Ls1 H); lia | lia]).
    replace (strip_leds_spec (Some d) strip bits) with (E_RANGE, @None cmd)
      by (unfold strip_leds_spec; replace (d_strips d <=? strip) with true by (symmetry; apply Z.leb_le; lia);
          reflexivity).
    zstep. zstep. finish. all: sl_close_fail HC. }
  zify_cond K4. rewrite sl_b8_unsigned in K4 by lia.
  assert (Us : bv_unsigned a1 = strip)
    by (destruct (Z_lt_le_dec strip (2 ^ 31)) as [H|H]; [exact (Ls1 H) | specialize (Lb1 H); lia]).
  (* 0x15888 lb device; 0x1588c bltz device *)
  zstep. zstep.
  if_cases K5.
  { zify_cond K5.
    assert (Dh : 128 <= d_dev d)
      by (destruct (Z_lt_le_dec (d_dev d) 128) as [H|H]; [rewrite sl_sxb_lo in K5 by lia; lia | exact H]).
    replace (strip_leds_spec (Some d) strip bits) with (E_ARG, @None cmd)
      by (unfold strip_leds_spec, leds_spec, sysex_spec;
          replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
          replace (0x7f <? bits) with false by (symmetry; apply Z.ltb_ge; lia);
          replace (0x7f <? d_dev d) with true by (symmetry; apply Z.ltb_lt; lia);
          reflexivity).
    zstep. finish. all: sl_close_fail HC. }
  zify_cond K5.
  assert (Dl : d_dev d < 128)
    by (destruct (Z_lt_le_dec (d_dev d) 128) as [H|H]; [exact H | rewrite sl_sxb_hi in K5 by lia; lia]).
  (* 0x15898 bltu 0x7f, strip: the payload byte strip has bit 7 set *)
  zstep. zstep. zstep.
  if_cases K6.
  { zify_cond K6.
    replace (strip_leds_spec (Some d) strip bits) with (E_RANGE, @None cmd)
      by (unfold strip_leds_spec, leds_spec, sysex_spec, u8;
          replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
          replace (0x7f <? bits) with false by (symmetry; apply Z.ltb_ge; lia);
          replace (0x7f <? d_dev d) with false by (symmetry; apply Z.ltb_ge; lia);
          rewrite (Z.mod_small strip 256), (Z.mod_small bits 256) by lia;
          cbn [existsb]; rewrite (sl_tb7_hi strip) by lia; reflexivity).
    zstep. finish. all: sl_close_fail HC. }
  zify_cond K6.
  clear HR0 HR1.
  (* 0x1589c .. 0x158e4: a0 = 0 and the eight stores into out; 0x158e8 ret *)
  do 20 zstep.
  rewrite Ub, Us in HC.
  rewrite (sl_pack bits strip) in HC by lia.
  rewrite (unsigned_lit bits) in HC by lia.
  rewrite (sl_key strip) in HC by lia.
  rewrite (sl_sxb_lo (d_dev d)) in HC by lia.
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-9)))) with (b8 247) in HC by (apply bv_eq; reflexivity).
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 32))) with (b8 32) in HC by (apply bv_eq; reflexivity).
  replace (strip_leds_spec (Some d) strip bits)
    with (0, Some ([0xf0; 0x13; d_dev d; 0x20; strip; bits; 0xf7], KEY 5 strip, 0))
    by (symmetry; unfold strip_leds_spec;
        replace (d_strips d <=? strip) with false by (symmetry; apply Z.leb_gt; lia);
        apply sl_leds_ok; lia).
  finish.
  all: lazymatch goal with
       | |- rw_cells _ _ _ _ => idtac
       | |- _ => reflexivity
       end.
  apply sl_out_cells; [exact Hlen | exact HC].
Qed.

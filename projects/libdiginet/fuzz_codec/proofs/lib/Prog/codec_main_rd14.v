(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c. *)
(* Modified by Theorem Labs: for reac-repacer/fuzz_uci. Sections G / G2 are
   libreac/fuzz_decode's released lib/Prog/crt_glue.v with its module paths changed and its one decode-specific
   import (check_braid_c, for braid_map) dropped. Section Body is the invariant layer of that release's
   lib/Prog/check_round_trip.v `Section Body` (cr_inv, cr_pre, cr_inv_call, cr_inv_A, cr_inv_kept, cr_heap_E,
   cr_free_keep, cr_old_in, cr_frame_call), with the one change that the function's own stack size is the section
   variable K instead of decode's CRT_STACK, and with cr_frame_call generalised from decode's fixed frame cell list
   to any (base, cells): so fuzz_uci's check_no_overread and check_value, whose frames differ, share one copy. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/CheckGlue.v, with its module paths changed; 187 of its 423 lines of code are new or changed and 255 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/cc_glue.v, with its module paths changed; 503 of its 621 lines of code are new or changed and 305 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/KindBGlue.v, with its module names changed; 185 of its 205 lines of code are new or changed and 601 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_text codec_main_inv
  codec_main_rdb_lib check_text_masks_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the composed arguments ---- *)

Lemma lor_low_add : forall a b n, 0 <= n -> 0 <= a -> 0 <= b < 2 ^ n -> a mod 2 ^ n = 0 -> Z.lor b a = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low a n i Hlt), Hm, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite Z.lor_comm. rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma lor_lt : forall n a b, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros n a b Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec, (Z_testbit_high n a k), (Z_testbit_high n b k) by lia. reflexivity.
Qed.

(** fuzz_u32 from its two u16 halves: x | y << 16 through slliw (bit 31 sign-extended) is the unsigned
    value's C int. *)
Lemma compose_u32 : forall x y, 0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 16 ->
  0 <= Z.lor x (Z.shiftl y 16) < 2 ^ 32 /\
  Z_to_bv 64 (Z.lor x (bv_swrap 32 (Z.shiftl y 16) mod 18446744073709551616)) =
  Z_to_bv 64 (s32 (Z.lor x (Z.shiftl y 16))).
Proof.
  intros x y Hx Hy.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 16) with 65536 in *. change 18446744073709551616 with (2 ^ 64).
  rewrite (lor_low_add (y * 65536) x 16) by (try (change (2 ^ 16) with 65536; apply Z.mod_mul); lia).
  rewrite swrap32_s32. rewrite (Z.mod_small (y * 65536) (2 ^ 32)) by lia.
  split; [lia|].
  unfold s32.
  destruct (Z.ltb_spec (y * 65536) (2 ^ 31)) as [Hl | Hl];
  destruct (Z.ltb_spec (y * 65536 + x) (2 ^ 31)) as [Hl' | Hl']; try lia.
  - rewrite (Z.mod_small (y * 65536) (2 ^ 64)) by lia.
    rewrite (lor_low_add (y * 65536) x 16) by (try (change (2 ^ 16) with 65536; apply Z.mod_mul); lia).
    reflexivity.
  - assert (E : (y * 65536 - 2 ^ 32) mod 2 ^ 64 = (y + 2 ^ 48 - 65536) * 65536).
    { rewrite <- (Z.mod_add (y * 65536 - 2 ^ 32) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite E.
    rewrite (lor_low_add ((y + 2 ^ 48 - 65536) * 65536) x 16)
      by (try (change (2 ^ 16) with 65536; apply Z.mod_mul); lia).
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace ((y + 2 ^ 48 - 65536) * 65536 + x) with ((y * 65536 + x - 2 ^ 32) + 1 * 2 ^ 64) by lia.
    apply Z.mod_add. lia.
Qed.

(** fuzz_u16: y | x << 8 (zero-extended). *)
Lemma compose_u16 : forall x y, 0 <= x < 2 ^ 8 -> 0 <= y < 2 ^ 16 ->
  0 <= Z.lor (Z.shiftl x 8) y < 2 ^ 16 /\
  Z_to_bv 64 (Z.lor (Z.shiftl x 8 mod 18446744073709551616) y) = Z_to_bv 64 (Z.lor (Z.shiftl x 8) y).
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (x * 2 ^ 8) 18446744073709551616) by lia.
  split; [apply lor_lt; lia | reflexivity].
Qed.

(** ---- the segment ---- *)

(** 0x14910-0x14930: n and mask composed, check_text_masks(n, mask), bltu s3, s6 -> EXIT, else j LATCH2. *)
Lemma rd14_tail : check_text_masks_contract -> forall e fuel, env_ok e -> latch2_ok e fuel -> exit_ok e ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4w a5w a6' a7' s5w s8' s10' t3' t4' t5' t6' ops inp inn : word)
         (pv dv c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd_cells 14 pv dv inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem ->
    bv_unsigned a0w < 2 ^ 16 -> bv_unsigned a1w < 2 ^ 16 -> bv_unsigned a2w < 2 ^ 16 ->
    bv_unsigned a3w < 2 ^ 16 -> bv_unsigned a4w < 2 ^ 8 -> bv_unsigned a5w < 2 ^ 16 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4w a5w a6' a7' s5w ops s8' s10' t3' t4' t5' t6')
          0x14910 m1).
Proof.
  intros CM e fuel HE L2 EX ra' t0' t1' t2' a0w a1w a2w a3w a4w a5w a6' a7' s5w s8' s10' t3' t4' t5' t6' ops
         inp inn pv dv c rem tl m1 FR HFR HF HC -> -> R0 R1 R2 R3 R4 R5.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 ops) as Rops. unfold bv_modulus in Rops.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  destruct HFR as (SV & ST & MU & WM & HMI).
  pose proof ST as [Hlo0 _].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  unfold rd_cells in FR. cbn [kcall_cells k_rd k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display app] in FR.
  unfold LLVM_CODEC_STACK in *.
  do 6 zstep.
  pose proof (bv_unsigned_in_range 64 a0w) as N0. pose proof (bv_unsigned_in_range 64 a1w) as N1.
  pose proof (bv_unsigned_in_range 64 a2w) as N2. pose proof (bv_unsigned_in_range 64 a3w) as N3.
  pose proof (bv_unsigned_in_range 64 a4w) as N4. pose proof (bv_unsigned_in_range 64 a5w) as N5.
  assert (X : 0 <= Z.lor (bv_unsigned a1w) (bv_unsigned a0w) < 2 ^ 16) by (apply lor_lt; lia).
  assert (Y : 0 <= Z.lor (bv_unsigned a3w) (bv_unsigned a2w) < 2 ^ 16) by (apply lor_lt; lia).
  destruct (compose_u32 _ _ X Y) as [Rn En]. rewrite En.
  destruct (compose_u16 (bv_unsigned a4w) (bv_unsigned a5w) ltac:(lia) ltac:(lia)) as [Rm Em]. rewrite Em.
  set (n := Z.lor (Z.lor (bv_unsigned a1w) (bv_unsigned a0w))
              (Z.shiftl (Z.lor (bv_unsigned a3w) (bv_unsigned a2w)) 16)) in *.
  set (mask := Z.lor (Z.shiftl (bv_unsigned a4w) 8) (bv_unsigned a5w)) in *.
  clearbody n mask. clear En Em X Y.
  zstep.
  unfold check_text_masks_contract, CHECK_TEXT_MASKS, CHECK_TEXT_MASKS_DEPTH in CM.
  call (CM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e_lo e) n mask).
  { unfold check_text_masks_pre, CHECK_TEXT_MASKS_DEPTH. rewrite USP.
    destruct (masks_agree n mask Rn Rm) as (A1 & A2 & A3 & A4).
    split; [split; [exact Rn | reflexivity] |].
    split; [split; [exact Rm | reflexivity] |].
    split; [exact HMI |]. split; [exact ST |]. split; [lia |].
    split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 | exact A4]. }
  rewrite ?USP in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FB : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e (k_rd 14 pv dv) c rem tl))
      by exact FR end.
  clear FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FO : fr_ok e mm)
      by (unfold fr_ok; split; [exact SV|]; split; [assumption|]; split; [exact MU|]; split; [exact WM | exact MI])
  end.
  zstep.
  if_cases EB.
  - zify_cond EB.
    eapply EX; [ apply body_cells_size | exact FB | exact FO ].
  - zify_cond EB. zstep.
    unfold latch2_ok, st, body_regs in L2.
    eapply L2; [ exact HF | lia | exact HC | exact FB | exact FO ].
Qed.

Ltac rd14_range :=
  rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?unsigned_lit by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); lia.

Ltac rd14_close Hcur :=
  first [ reflexivity | (unfold cur_ok; lia) | (rewrite Hcur; f_equal; lia) | (f_equal; lia)
        | (rewrite <- Hcur; symmetry; apply Z_to_bv_bv_unsigned) | rd14_range ].

(** 0x139a8-0x13a20, 0x13b3c-0x13b44, 0x13b88-0x13b8c, 0x148c8-0x1490c: n = fuzz_u32 (four fuzz_u8), mask =
    fuzz_u16 (two fuzz_u8), a missing byte reads 0; in.p / in.n advanced by the bytes taken; then the tail. *)
Lemma codec_main_rd14 : S_rd14.
Proof.
  unfold S_rd14. intros CM e fuel HE L2 EX.
  pose proof (rd14_tail CM e fuel HE L2 EX) as TL. unfold st, body_regs in TL.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  replace (rd_pc 14) with 0x139a8 by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  pose proof (unsigned_lit rem ltac:(lia)) as Urem.
  unfold body_cells in FR. cbn [kcall_cells k_rd k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display app] in FR.
  set (cur := Z_to_bv 64 (bv_unsigned (e_p e) + c)) in FR.
  assert (Hcur : bv_unsigned cur = bv_unsigned (e_p e) + c) by (unfold cur; apply unsigned_lit; lia).
  clearbody cur.
  zstep. zstep.
  if_cases E0.
  { (* rem = 0 *)
    zify_cond E0. do 3 zstep. do 3 zstep. try if_true. zstep. zstep.
    eapply TL with (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
      rd14_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 cur c. zstep. zstep.
  if_cases E1.
  { (* rem = 1 *)
    zify_cond E1. do 4 zstep. try if_true. zstep. zstep.
    eapply TL with (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
      rd14_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte cur c 1. zstep. zstep. zstep.
  if_cases E2.
  { (* rem = 2 *)
    zify_cond E2. do 4 zstep. try if_true. zstep. zstep.
    eapply TL with (c := c + 2) (rem := rem - 2);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
      rd14_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte cur c 2. zstep. zstep.
  if_cases E3.
  { (* rem = 3 *)
    zify_cond E3. do 4 zstep. try if_true. zstep. zstep.
    eapply TL with (c := c + 3) (rem := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
      rd14_close Hcur. }
  zify_cond E3.
  do 4 zstep. in_byte cur c 3. zstep. zstep. zstep.
  if_cases E4.
  { (* rem >= 5 *)
    zify_cond E4.
    do 5 zstep. in_byte cur c 4. zstep. zstep.
    if_cases E5.
    { (* rem = 5 *)
      zify_cond E5. zstep.
      eapply TL with (c := c + 5) (rem := rem - 5);
        [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
        rd14_close Hcur. }
    zify_cond E5.
    do 4 zstep. in_byte cur c 5. zstep. zstep.
    eapply TL with (c := c + 6) (rem := rem - 6);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
      rd14_close Hcur. }
  (* rem = 4 *)
  zify_cond E4. zstep. zstep.
  eapply TL with (c := c + 4) (rem := rem - 4);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | .. ];
    rd14_close Hcur.
Qed.

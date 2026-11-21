(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition cb_S2_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV BV0 : Z) (dist lc code : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s6 s7 s8 s9 s10 w m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp (wz dist) w (wz lc) (wz BV) (wz (code * 4)) (wz code) s6 s7 s8 s9 s10 s11) F (wz 0x1dc7c) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S2 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc dist code V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = arr_get lfc (code + 257) -> l = arr_get ldl (code + 257) ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 256 -> 0 < LT -> LT + 4 * 286 < 2^63 -> LT mod 2 = 0 ->
  0 <= V < 32768 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S2_post L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) BV dist lc code
                ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) s1 (wz lc) s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1da6c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ecode EV El EMH HBB MI LAY RDL Rlc RLT1 RLT2 ALT RV Rl RBV RPD ROOM. unfold ucbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI (code + 257) ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  pose proof (u8ro_read usegs m Z_LENGTH_CODE (av8 length_code_a 256) lc _ (wa (Z_LENGTH_CODE + lc)) (rod_length_code m MI)
                (av8_nth length_code_a 256 lc ltac:(lia)) ltac:(lia) eq_refl) as RDlc. rewrite <- Ecode in RDlc.
  unfold Z_LENGTH_CODE in *.
  ustep CB_TRAP. zs2. zsb. rewrite (bv8_small code) by lia.
  zs2. shl_norm.
  uwalk 0x1da98 CB_TRAP. at_pc 0x1da98.
  zs. rewrite (zx16_small l) by lia. zs2. zs. rewrite (zx16_small V) by lia.
  clear Ecode EV El.
  do 4 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep CB_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2.
      reg_as (BV + l) (BV + l).
    apply evt_done. unfold cb_S2_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    ustep CB_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1db00 CB_TRAP. at_pc 0x1db00.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1db34 CB_TRAP. at_pc 0x1db34.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1db50 CB_TRAP. at_pc 0x1db50.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
      zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S2_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Lemma unsigned_wz_neg : forall z, - 2^63 <= z < 0 -> bv_unsigned (wz z) = z + 2^64.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma cb_range_test : forall code, 0 <= code < 29 -> bv_ltu (wz (code + -28)) (wz (-20)) = negb ((8 <=? code) && (code <=? 27)).
Proof.
  intros code H. unfold bv_ltu. rewrite (unsigned_wz_neg (-20)) by lia.
  destruct (Z.eq_dec code 28) as [->|NE].
  - change (28 + -28) with 0. rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_wz_neg by lia.
    destruct (Z.leb_spec 8 code), (Z.leb_spec code 27); cbn [andb negb]; [apply Z.ltb_ge| | apply Z.ltb_lt| apply Z.ltb_lt]; lia.
Qed.

Definition cb_S3_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (dist : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s2 s4 s5 s6 s7 s8 s9 s10 w m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp (wz dist) w s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1ddc0) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S3 : forall (L : dlay) (s : deflate_state) (LT DT sx lc dist code V l : Z) (X : bool) (PB : arr) (PD BB BV BV0 : Z) (w : word)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = lc - arr_get base_length_a code -> l = arr_get extra_lbits_a code -> X = (8 <=? code) && (code <=? 27) ->
  EM m L s PB PD w (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L -> 0 <= lc < 256 -> 0 <= BV0 < 2^32 ->
  0 <= BV <= 16 -> 0 <= PD -> (X = true -> 16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S3_post L s LT DT sx (if X then sbF_PB PB PD BB BV V l else PB) (if X then sbF_PD PD BV l else PD)
                (if X then sbF_BB BB BV V l else BB) (if X then sbF_BV BV l else BV) dist ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) w (wz lc) (wz BV) (wz (code * 4)) (wz code) s6 s7 s8 s9 s10 s11) F (wz 0x1dc7c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ecode EV El EX EMH HW MI LAY Rlc RBV0 RBV RPD ROOM. unfold ucbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (extra_lbits_facts code Rcode) as (Rex & Rbase & _). rewrite <- El in Rex.
  pose proof (length_base_le lc Rlc) as RVlo. rewrite <- Ecode in RVlo.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zstep.
  lazymatch goal with H : mem_inv usegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u32ro_read mc Z_BASE_LENGTH (av32 base_length_a 29) code _ (wa (Z_BASE_LENGTH + 4 * code)) (rod_base_length mc H)
                (av32_nth base_length_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDb;
    pose proof (u32ro_read mc Z_EXTRA_LBITS (av32 extra_lbits_a 29) code _ (wa (Z_EXTRA_LBITS + 4 * code)) (rod_extra_lbits mc H)
                (av32_nth extra_lbits_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDe end.
  rewrite <- El in RDe. unfold Z_BASE_LENGTH, Z_EXTRA_LBITS in *.
  ustep CB_TRAP. zs2. zstep. rewrite cb_range_test by lia. rewrite <- EX.
  destruct X.
  -
    cbn [negb].
    assert (CX : 8 <= code <= 27) by (symmetry in EX; apply andb_true_iff in EX; rewrite !Z.leb_le in EX; lia).
    uwalk 0x1dcac CB_TRAP. at_pc 0x1dcac.
    zs2. zs2. zs2.
    ustep CB_TRAP. zs2. zs2.
    rewrite <- EV. zs2. zs2. ustep CB_TRAP. zs2. zs2.
    assert (RV : 0 <= V < 256) by lia.
    zs2. rewrite (land16_small V) by lia.
    zs2. zs2. zs2. shl_g0. zs2. zs2. shl_g1.
    clear Ecode EV El.
    zstep. br_cases K.
    +
      ustep CB_TRAP. zs2. zs2. zs2.
      sb_or w1 LO BB ltac:(exact HW).
      zs2. zstep. ustep CB_TRAP. zstep.
      reg_as (BV + l) (BV + l).
      apply evt_done. unfold cb_S3_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| exact LO].
    +
      ustep CB_TRAP. zs. zs. zs. zs.
      sb_or w1 LO BB ltac:(exact HW).
      zs. zs. zstep. zs.
      uwalk 0x1dd30 CB_TRAP. at_pc 0x1dd30.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
      zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
      uwalk 0x1dd64 CB_TRAP. at_pc 0x1dd64.
      pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
      uwalk 0x1dd80 CB_TRAP. at_pc 0x1dd80.
      zs2. rewrite srlw_val16 by lia.
      pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
      zs2. zstep. ustep CB_TRAP. zs2. zs2.
      rewrite swrap32_add_mod64, ?wz_add_mod64. strip32.
      zstep. br_true. zstep.
      reg_as (BV + (l + -16)) (BV + l - 16).
      apply evt_done. unfold cb_S3_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
  -
    cbn [negb].
    apply evt_done. unfold cb_S3_post, ucbR. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact HW].
Qed.

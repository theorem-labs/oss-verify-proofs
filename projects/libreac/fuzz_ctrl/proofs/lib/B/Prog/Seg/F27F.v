(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source: lib/B/Prog/Seg/F27.v seg_F27's two inline stretches (no stated run lemma) at
     a working branch 3803efccea0 (blob a0b51aa2c6b8217fd46ab70c42eab6ef70d0fbf3);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: split stretches, both calls-free.  seg_F27_F re-runs F27.v:340-362 (r = t_rp = 0:
     0x828b4 -> 0x8292c, the port-slot loop head) and seg_F27_rp_F re-runs F27.v:409-426 (r <> 0:
     0x828b4 -> 0x82aa4, the three ports words are -7).  Neither stretch calls anything, so neither is split
     further. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F27.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* The short name PropExec resolves to the UL engine's copy here (the Seg chain loads it last), but StepF steps
   the lib.Lib engine: name its value functions explicitly. *)
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      match goal with
      | H : rng RNG E _ |- _ =>
          eapply rng_acc_litZ; [exact H | reflexivity | lia | split; lia]
      end
  end.

(* F27's branch helpers, over the lib.Lib goal (its own `cbv_concl_iota` comes from the UL engine's Step). *)
Ltac f27f_cbv_iota :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in change_no_check g'.
Ltac f27f_brc v :=
  lazymatch goal with
  | |- context [if ?c then _ else _] => replace c with v by (vm_compute; reflexivity); f27f_cbv_iota
  end.
Ltac f27f_br v pf :=
  lazymatch goal with
  | |- context [if ?c then _ else _] => replace c with v by (symmetry; pf); f27f_cbv_iota
  end.

(* The read facts and value normalisations of F27's runs, over the lib.Lib engine. *)
Lemma f27f_rd4 : forall m a bs, bytes_at rsegs m a bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m (wa a) 4 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 4 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f27f_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f27f_slti0 : forall u, 0 <= u < 2 ^ 63 -> LPE.v_slti (Z_to_bv 64 u) 0 = Z_to_bv 64 0.
Proof.
  intros u Hu. unfold LPE.v_slti, LPE.zsig.
  assert (E : bv_unsigned (Z_to_bv 64 u) = u) by (apply unsigned_lit; lia).
  rewrite (bv_signed_small (Z_to_bv 64 u)) by (rewrite E; lia). rewrite E.
  destruct (Z.ltb_spec u 0); [lia | reflexivity].
Qed.
Lemma f27f_sltiu1 : forall (x : word) imm, bv_unsigned x < bv_wrap 64 imm -> LPE.v_sltiu x imm = Z_to_bv 64 1.
Proof.
  intros x imm H. unfold LPE.v_sltiu. destruct (Z.ltb_spec (bv_unsigned x) (bv_wrap 64 imm)); [reflexivity | lia].
Qed.
Lemma f27f_a6_eq : forall phi, 0 < phi -> phi + 50 <= 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (LPE.v_sltiu
      (Z_to_bv 64 (18446744073709551608 - bv_unsigned (Z_to_bv 64 (phi + 18)))) (-7)))))
    (bv_unsigned (Z_to_bv 64 (18446744073709551608 - bv_unsigned (Z_to_bv 64 (phi + 18))))))
  = Z_to_bv 64 (-8 - (phi + 18)).
Proof.
  intros phi H0 H50.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  rewrite (unsigned_lit (phi + 18)) by lia.
  rewrite (unsigned_lit (18446744073709551608 - (phi + 18))) by lia.
  rewrite f27f_sltiu1
    by (rewrite unsigned_lit by lia; change (bv_wrap 64 (-7)) with 18446744073709551609; lia).
  change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with 18446744073709551615.
  rewrite F27.f27_land_m1 by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  replace (18446744073709551608 - (phi + 18)) with ((-8 - (phi + 18)) + 1 * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* The r = 0 arm of seg_F27's inline stretch, 0x828b4 -> 0x8292c (F27.v:340-362): the port counts agree, the
   ports result r is 0, and the port-slot loop registers are set.  The only access is the block spill
   [A + 312, A + 320) (read twice). *)
Lemma seg_F27_F : forall (RNG : footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9v x10v x11 x12 x13 x14 x15 x16 x17 x18v x19 x20 x21v x22 x23v x24 x25v x26 x27v
   x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi u : Z),
  x9v = Z_to_bv 64 A -> x18v = Z_to_bv 64 phi -> x27v = Z_to_bv 64 (-8) ->
  x25v = Z_to_bv 64 0 -> x23v = Z_to_bv 64 u -> x10v = Z_to_bv 64 u ->
  0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= u < 2 ^ 63 ->
  bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 (phi + 18))) ->
  rng RNG (A + 312) 8 ->
  evtF rsegs RNG
    (fun ms' => exists R : bvmap 5 word,
       ms' = MS R F (Z_to_bv 64 0x8292c) fc None m (seg_rom rsegs) /\
       getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9v /\
       getr R 19 = x19 /\ getr R 26 = x26 /\ getr R 18 = x18v /\ getr R 23 = x23v /\ getr R 27 = x27v /\
       getr R 20 = x20 /\ getr R 21 = x21v /\ getr R 24 = x24 /\
       getr R 10 = Z_to_bv 64 (phi + 26) /\ getr R 14 = Z_to_bv 64 (phi + 26) /\
       getr R 16 = Z_to_bv 64 (-8 - (phi + 18)) /\ getr R 17 = Z_to_bv 64 12 /\
       getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 0 /\
       getr R 15 = Z_to_bv 64 0 /\ getr R 28 = Z_to_bv 64 12)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9v x10v x11 x12 x13 x14 x15 x16 x17 x18v x19 x20 x21v x22 x23v x24 x25v
         x26 x27v x28 x29 x30 x31) F (Z_to_bv 64 0x828b4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9v x10v x11 x12 x13 x14 x15 x16 x17 x18v x19 x20 x21v x22 x23v x24 x25v
    x26 x27v x28 x29 x30 x31 F fc m A phi u -> -> -> -> -> -> Hphi0 Hphi50 Hu63 H312 R312.
  pose proof (f27f_rd8 m _ _ H312 ltac:(apply length_le8)) as RD312.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* 0x828b4 bne a0,s7: both counts are t_unk, not taken *)
  step. f27f_br false ltac:(rewrite bv_eqb_refl; reflexivity).
  (* 0x828b8 seqz a0,s9 ; 0x828bc slti a1,s7,0 *)
  step. step.
  (* 0x828c0 beq a0,a1: seqz r = 1, slti unk = 0, not taken *)
  step. f27f_br false ltac:(rewrite (f27f_slti0 u Hu63); vm_compute; reflexivity).
  (* 0x828c4 beqz s9: r = 0, taken to 0x828f0 *)
  step. f27f_brc true.
  (* 0x828f0 li t3,12 *)
  step.
  (* 0x828f4 ld a0,312(s1) = blk = phi + 18 ; 0x828f8 beqz a0,82fa0 (T55): blk <> 0, not taken *)
  step. step. f27f_br false ltac:(apply F27.f27_eqb0; lia).
  (* 0x828fc-0x82908: li a5,0 ; li a3,0 ; li a1,0 ; li a2,0 *)
  step. step. step. step.
  (* 0x8290c ld a4,312(s1) ; 0x82910 sub a0,s11,a4 ; 0x82914 addi a4,a4,8 ; 0x82918 sltiu a6,a0,-7 ;
     0x8291c neg a6,a6 ; 0x82920 and a6,a6,a0 ; 0x82924 li a7,12 ; 0x82928 mv a0,a4 *)
  step. step. step. step. step. step. step. step.
  finish. all: simp_regs; try reflexivity; try (f_equal; lia).
  exact (f27f_a6_eq phi Hphi0 Hphi50).
Qed.

(* The r <> 0 arm of seg_F27's inline stretch, 0x828b4 -> 0x82aa4 (F27.v:409-426): r = unk = -1 and the three
   ports words at s5 = fr + 128 are -7, so every FAIL branch falls through to the jump at 0x828ec.  The only
   accesses are the three 4-byte words [fr + 128, fr + 140). *)
Lemma seg_F27_rp_F : forall (RNG : footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21v x22 x23v x24 x25v x26 x27
   x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z) (w0 w4 w8 : list byte),
  x21v = Z_to_bv 64 (fr + 128) -> x25v = Z_to_bv 64 (-1) -> x23v = Z_to_bv 64 (-1) -> x10v = Z_to_bv 64 (-1) ->
  bytes_at rsegs m (fr + 128) w0 -> length w0 = 4%nat -> w0 = le4 (Z_to_bv 64 (-7)) ->
  bytes_at rsegs m (fr + 132) w4 -> length w4 = 4%nat -> w4 = le4 (Z_to_bv 64 (-7)) ->
  bytes_at rsegs m (fr + 136) w8 -> length w8 = 4%nat -> w8 = le4 (Z_to_bv 64 (-7)) ->
  rng RNG (fr + 128) 12 ->
  evtF rsegs RNG
    (fun ms' => exists R : bvmap 5 word,
       ms' = MS R F (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs) /\
       getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
       getr R 19 = x19 /\ getr R 26 = x26 /\ getr R 18 = x18 /\ getr R 27 = x27 /\
       getr R 20 = x20 /\ getr R 21 = x21v /\ getr R 24 = x24)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21v x22 x23v x24 x25v
         x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x828b4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21v x22 x23v x24 x25v
    x26 x27 x28 x29 x30 x31 F fc m fr w0 w4 w8 -> -> -> -> P0 L0 E0 P4 L4 E4 P8 L8 E8 R128.
  subst w0 w4 w8.
  pose proof (f27f_rd4 m _ _ P0 ltac:(apply length_le4)) as RD0.
  pose proof (f27f_rd4 m _ _ P4 ltac:(apply length_le4)) as RD4.
  pose proof (f27f_rd4 m _ _ P8 ltac:(apply length_le4)) as RD8.
  (* 0x828b4 bne a0,s7: both -1, not taken *)
  step. f27f_brc false.
  (* seqz a0,s9 = 0 ; slti a1,s7,0 = 1 ; 0x828c0 beq a0,a1 not taken *)
  step. step. step. f27f_brc false.
  (* 0x828c4 beqz s9 (= -1) not taken *)
  step. f27f_brc false.
  (* 0x828c8 lw a0,0(s5) = -7 (s5 = fr + 128) ; li a1,-7 ; 0x828d0 bne a0,a1 not taken *)
  step. step. step. f27f_brc false.
  (* 0x828d4 lw a0,4(s5) ; li a1,-7 ; 0x828dc bne a0,a1 not taken *)
  step. step. step. f27f_brc false.
  (* 0x828e0 lw a0,8(s5) ; li a1,-7 ; 0x828e8 bne a0,a1 not taken *)
  step. step. step. f27f_brc false.
  (* 0x828ec j 82aa4 *)
  step.
  finish. all: simp_regs; try reflexivity; try (f_equal; lia).
Qed.

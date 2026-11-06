(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The plain image's harness body LLVMFuzzerTestOneInput (fuzz_egress.c:157-163), two straight-line evt segments
   between its SR calls:
   - eB_evt, 0x12d58 (malloc returned f in a0) to the call of check_restamp at 0x12da0: the `if (!b) abort();` arm
     of fuzz_dup is not taken (f >= 4096); f kept in s3, slot = head[0] - 2 in s4, the counter in s5; when size >= 54,
     fuzz_dup's memcpy(f, data + 53, n); then check_restamp(f, n, ctr).
   - eD_evt, 0x12db0 (check_mute returned) to the call of check_inject at 0x12dd0: check_gate(f, n, slot) through its
     evt contract, then check_inject(f, n, slot, v) with v = sp + 8. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import memcpy_c check_gate_c lt_head.
Import ListNotations.
Open Scope Z_scope.

Lemma sltiu_ge : forall n, 54 <= n < 2 ^ 64 -> v_sltiu (Z_to_bv 64 n) 54 = Z_to_bv 64 0.
Proof.
  intros n Hn. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 54) with 54.
  destruct (Z.ltb_spec n 54); [lia | reflexivity].
Qed.

(* the state at check_restamp's entry: ra = 0x12da4, a0 = s3 = f, a1 = s2 = n, a2 = s5 = the counter, s4 = slot *)
Definition qB (F : bvmap 5 word) (fc : bv 32) (gp tp x25 x26 x27 : word) (m0 : word -> option byte)
    (Sp res nn slot : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m' (cw : word), ms = MS R F (Z_to_bv 64 0x12e14) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12da4 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 10 = Z_to_bv 64 res /\ reg_get R 11 = Z_to_bv 64 nn /\ reg_get R 12 = cw /\
    reg_get R 18 = Z_to_bv 64 nn /\ reg_get R 19 = Z_to_bv 64 res /\ reg_get R 20 = Z_to_bv 64 slot /\
    reg_get R 25 = x25 /\ reg_get R 26 = x26 /\ reg_get R 27 = x27 /\
    munch [(res, res + nn)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' (Sp + 112) sv.

Lemma eB_evt : memcpy_contract ->
  forall (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (sv : list cell) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp n p res nn : Z) (b0 : byte)
         (src junk : list byte),
    0 <= Sp -> Sp + 192 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> 4096 <= res -> res + nn <= Sp ->
    nn = Z.min (Z.max (n - 53) 0) 1600 -> (54 <= n -> p + n <= Sp) ->
    (54 <= n -> bytes_at rsegs m (p + 53) src) -> length src = Z.to_nat nn ->
    (54 <= n -> rw_cells rsegs m res [CB (Z.to_nat nn) junk]) ->
    (54 <= n -> p + 53 + nn <= res \/ res + nn <= p + 53) ->
    rw_cells rsegs m (Sp + 112) sv -> cells_size sv = 80%nat -> mem_inv rsegs m ->
    evt rsegs (qB F fc x3 x4 x25 x26 x27 m Sp res nn (bv_unsigned b0 + -2) sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 res) x11 x12 x13 x14 x15
               x16 x17 (Z_to_bv 64 nn) x19 (Z_to_bv 64 (bv_unsigned b0)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12d58) fc None m (seg_rom rsegs)).
Proof.
  intros MC x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    sv F fc m Sp n p res nn b0 src junk H0 H63 Hn Hp Hres Hrs Hnn Hpn HBS HLS HJK HDJ RS Hsv MI.
  pose proof (munch_refl [(res, res + nn)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. take false.
  do 7 step.
  destruct (Z_lt_le_dec n 54) as [H54|H54].
  - take true. do 4 step.
    apply evt_done. unfold qB. do 3 eexists.
    split; [reflexivity|]. do 13 qreg.
    split; [exact MU|]. split; [exact WM | exact RS].
  - take false. step. rewrite (sltiu_ge n) by lia. do 6 step.
    pose proof (Hpn H54) as Hpn'.
    eapply evt_cut.
    { eapply (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m src junk).
      - rewrite unsigned_lit by lia. exact (HBS H54).
      - rewrite (unsigned_lit nn) by lia. exact HLS.
      - rewrite !unsigned_lit by lia. exact (HJK H54).
      - rewrite !unsigned_lit by lia. exact (HDJ H54).
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2
      & WM2 & MI2 & RW2 & BS2).
    rewrite !unsigned_lit in MU2 by lia.
    replace (ret_pc (Z_to_bv 64 0x12d94)) with (Z_to_bv 64 0x12d94) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply (rw_cells_transport rsegs [(res, res + nn)] m m2 (Sp + 112) sv) in RS;
      [ | exact MU2 | exact WM2 | cbn [disjoint_from]; rewrite Hsv; split; [lia | exact I] ].
    do 4 step.
    apply evt_done. unfold qB. do 3 eexists.
    split; [reflexivity|]. do 13 qreg.
    split; [exact MU2|]. split; [exact WM2 | exact RS].
Qed.

(* the state at check_inject's entry: ra = 0x12dd4, a0 = f, a1 = n, a2 = slot, a3 = v = sp + 8 *)
Definition qD (F : bvmap 5 word) (fc : bv 32) (gp tp x25 x26 x27 : word) (m0 : word -> option byte)
    (Sp res nn slot : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m', ms = MS R F (Z_to_bv 64 0x13028) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12dd4 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 10 = Z_to_bv 64 res /\ reg_get R 11 = Z_to_bv 64 nn /\ reg_get R 12 = Z_to_bv 64 slot /\
    reg_get R 13 = Z_to_bv 64 (Sp + 8) /\
    reg_get R 18 = Z_to_bv 64 nn /\ reg_get R 19 = Z_to_bv 64 res /\ reg_get R 20 = Z_to_bv 64 slot /\
    reg_get R 25 = x25 /\ reg_get R 26 = x26 /\ reg_get R 27 = x27 /\
    munch [(Sp - 80, Sp)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' (Sp + 112) sv.

Lemma eD_evt : check_gate_contract ->
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (sv : list cell) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp lo res nn slot : Z)
         (bs : list byte),
    0 <= lo -> lo + 80 <= Sp -> Sp + 192 <= 2 ^ 63 -> 4096 <= res -> res + nn <= lo -> 0 <= nn <= 1600 ->
    -2 <= slot <= 253 ->
    stk rsegs m lo Sp -> mem_inv rsegs m -> bytes_at rsegs m res bs -> length bs = Z.to_nat nn ->
    rw_cells rsegs m (Sp + 112) sv -> cells_size sv = 80%nat ->
    evt rsegs (qD F fc x3 x4 x25 x26 x27 m Sp res nn slot sv)
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nn)
               (Z_to_bv 64 res) (Z_to_bv 64 slot) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12db0) fc None m (seg_rom rsegs)).
Proof.
  intros CG x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    sv F fc m Sp lo res nn slot bs Hlo Hlo80 H63 Hres Hrl Hnn Hsl ST MI HBS HLB RS Hsv.
  do 4 step.
  eapply evt_cut.
  { eapply (CG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m bs slot lo).
    - exact MI.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. exact HBS.
    - rewrite unsigned_lit by lia. exact HLB.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. left. lia.
    - reflexivity.
    - lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2
    & WM2 & MI2 & ST2).
  rewrite !unsigned_lit in MU2 by lia.
  replace (ret_pc (Z_to_bv 64 0x12dc0)) with (Z_to_bv 64 0x12dc0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (rw_cells_transport rsegs [(Sp - 80, Sp)] m m2 (Sp + 112) sv) in RS;
    [ | exact MU2 | exact WM2 | cbn [disjoint_from]; rewrite Hsv; split; [lia | exact I] ].
  do 5 step.
  apply evt_done. unfold qD. do 2 eexists.
  split; [reflexivity|]. do 14 qreg.
  split; [exact MU2|]. split; [exact WM2 | exact RS].
Qed.

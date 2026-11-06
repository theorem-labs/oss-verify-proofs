(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_slow_path_double_stmt P_memset_stmt P_parse_mantissa_stmt P_positive_digit_comp_d_stmt P_negative_digit_comp_d_stmt P_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.

Module P_spd_A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_spd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  Hypothesis C_22a9c : K_22a9c c.
  Hypothesis C_221e8 : K_221e8 c.

  (* [comment removed for export] *)
  #[using="PRE C_22a9c C_221e8"] Lemma spd_A :
    evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x23f34) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22a9c C_221e8 : LiaFast.U) => LiaFast.u0).
    unfold K_221e8 in C_221e8. unfold K_22a9c in C_22a9c.
    pre_facts.
    pose proof (pre_ST c PRE) as ST. unfold slow_path_double_need in ST.
    pose proof (pre_TXT c PRE) as TXT. pose proof (pre_VAL c PRE) as VAL.
    pose proof (pre_PR1 c PRE) as PR1. pose proof (pre_PR2 c PRE) as PR2. unfold P_FMIN_D in PR2.
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    pose proof (munch_refl W m0) as MU. cbv delta [slow_path_double_W slow_path_double_need] in MU.
    pose proof (wmono_refl PSEGS m0) as WM.
    carve_frame 688%nat ST.
    do 14 step.   (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT 0%Z RD. rewrite wa_P0 in RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite v_sltiu_b2z.
    lazymatch goal with |- context [Z_to_bv 64 (Z.b2z ?b)] =>
      pose proof (b2z_range b) as NG; set (ng := Z.b2z b) in *; clearbody ng end.
    step. (* [comment removed for export] *)
    rewrite (pre_A5 c PRE).
    step. (* [comment removed for export] *)
    if_true.
    assert (PINV : pinv c (firstn 584 (firstn 592 (firstn 600 (firstn 608 (firstn 616 (firstn 624 (firstn 632 (firstn 640
                   (firstn 648 (firstn 656 (firstn 664 (firstn 672 (firstn 680 junk))))))))))))) m).
    { split; [exact TXT|]. split; [exact FR|]. split; [unfold slow_path_double_need; exact ST|]. split; [exact VAL|].
      split; [exact PR1|]. split; [unfold P_FMIN_D; exact PR2|].
      split; [cbv delta [slow_path_double_W slow_path_double_need]; exact MU | exact WM]. }
    pose proof (txb_range bs 0) as Rb0. unfold txb in Rb0.
    (* [comment removed for export] *)
    assert (SIGN : forall (x12 : word),
      evt PSEGS POST
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 a2 s1 (Z_to_bv 64 ng) a1 x12 a3 a4 (Z_to_bv 64 0) (txb bs 0) a7
                 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x240a8) fc None m (seg_rom PSEGS))).
    { intros x12.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hend.
      - cond_cleanup Hend.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_22a9c. exact PINV.
      - cond_cleanup Hend.
        txt_rd TXT 1%Z RD.
        step. (* [comment removed for export] *)
        clear RD. pose proof (txb_range bs 1) as Rb1. unfold txb in Rb1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hdig.
        + cond_cleanup Hdig.
          goto (eapply C_221e8 with (k2 := 0%Z) (k3 := 1%Z)); [exact PINV | lia | lia | lia | lia | intros; reflexivity].
        + cond_cleanup Hdig.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hdp.
          * goto (eapply C_221e8 with (k2 := 1%Z) (k3 := 1%Z)); [exact PINV | lia | lia | lia | lia | intros; reflexivity].
          * step. (* [comment removed for export] *)
            eapply C_22a9c. exact PINV. }
    step. (* [comment removed for export] *)
    if_cases Hminus.
    - apply SIGN.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hplus.
      + (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply C_221e8 with (k2 := 0%Z) (k3 := 0%Z)); [exact PINV | lia | lia | lia | lia | intros; reflexivity].
      + step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases H43.
        * step. (* [comment removed for export] *)
          goto (eapply C_221e8 with (k2 := 0%Z) (k3 := 0%Z)); [exact PINV | lia | lia | lia | lia | intros; reflexivity].
        * apply SIGN.
  Qed.
End BLK.
End P_spd_A.


Module P_spd_B.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_spd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  Hypothesis C_22460 : K_22460 c.

  #[using="PRE C_22460"] Lemma spd_B_loop : forall (n : nat) (k : Z) (x5 x6 x12 : word) junk m
      (x1 x7 x9 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (ng k3 : Z),
      (L - k <= Z.of_nat n)%Z ->
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3)%Z -> (k3 <= 1)%Z -> (k3 <= k < L)%Z -> digs bs k3 k ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) a1 x12 a3 a4 (Z_to_bv 64 (P + k)) (Z_to_bv 64 10) (Z_to_bv 64 9)
                 x18 (Z_to_bv 64 (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2419c) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22460 : LiaFast.U) => LiaFast.u0).
    unfold K_22460 in C_22460.
    induction n as [|n IH]; intros k x5 x6 x12 junk m x1 x7 x9 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3
      Hn PINV NG K30 K31 HK DG.
    { exfalso. lia. }
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    txt_rd TXT k RD. pose proof (tx_range bs k) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) k.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. clear Hd.
      goto (eapply C_22460 with (k3 := k3) (kI := k)); [exact PINV | lia | lia | lia | lia | exact DG].
    - cond_cleanup Hd. pose proof (dig_yes _ Rk Hd) as D. clear Hd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH (k + 1)%Z) with (k3 := k3)); [lia | exact PINV | lia | lia | lia | lia | apply digs_snoc; assumption].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply C_22460 with (k3 := k3) (kI := (k + 1)%Z)); [exact PINV | lia | lia | lia | lia | apply digs_snoc; assumption].
  Qed.

  #[using="PRE C_22460"] Lemma spd_B : K_221e8 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22460 : LiaFast.U) => LiaFast.u0).
    unfold K_22460 in C_22460.
    unfold K_221e8. intros junk m x1 x5 x6 x7 x9 x12 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k2 k3
      PINV NG K23 K3L K31 X16.
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    pose proof (digs_nil bs k3) as DG0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend.
      step. (* [comment removed for export] *)
      goto (eapply C_22460 with (k3 := k3) (kI := k3)); [exact PINV | lia | lia | lia | lia | exact DG0]. }
    cond_cleanup Hend. rewrite (X16 ltac:(lia)).
    pose proof (tx_range bs k3) as R0. rewrite txb_tx.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd0.
    { cond_cleanup Hd0. clear Hd0.
      goto (eapply C_22460 with (k3 := k3) (kI := k3)); [exact PINV | lia | lia | lia | lia | exact DG0]. }
    cond_cleanup Hd0. pose proof (dig_yes _ R0 Hd0) as D0. clear Hd0.
    pose proof (digs_snoc _ _ _ DG0 D0) as DG1.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He1.
    { cond_cleanup He1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 1)%Z)); [exact PINV | lia | lia | lia | lia | exact DG1]. }
    cond_cleanup He1.
    txt_rd TXT (k3 + 1)%Z RD. pose proof (tx_range bs (k3 + 1)) as R1.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 1)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd1.
    { cond_cleanup Hd1. clear Hd1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 1)%Z)); [exact PINV | lia | lia | lia | lia | exact DG1]. }
    cond_cleanup Hd1. pose proof (dig_yes _ R1 Hd1) as D1. clear Hd1.
    pose proof (digs_snoc _ _ _ DG1 D1) as DG2. replace (k3 + 1 + 1)%Z with (k3 + 2)%Z in DG2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He2.
    { cond_cleanup He2.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 2)%Z)); [exact PINV | lia | lia | lia | lia | exact DG2]. }
    cond_cleanup He2.
    txt_rd TXT (k3 + 2)%Z RD. pose proof (tx_range bs (k3 + 2)) as R2.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 2)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd2.
    { cond_cleanup Hd2. clear Hd2.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 2)%Z)); [exact PINV | lia | lia | lia | lia | exact DG2]. }
    cond_cleanup Hd2. pose proof (dig_yes _ R2 Hd2) as D2. clear Hd2.
    pose proof (digs_snoc _ _ _ DG2 D2) as DG3. replace (k3 + 2 + 1)%Z with (k3 + 3)%Z in DG3 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He3.
    { cond_cleanup He3.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 3)%Z)); [exact PINV | lia | lia | lia | lia | exact DG3]. }
    cond_cleanup He3.
    txt_rd TXT (k3 + 3)%Z RD. pose proof (tx_range bs (k3 + 3)) as R3.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 3)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd3.
    { cond_cleanup Hd3. clear Hd3.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 3)%Z)); [exact PINV | lia | lia | lia | lia | exact DG3]. }
    cond_cleanup Hd3. pose proof (dig_yes _ R3 Hd3) as D3. clear Hd3.
    pose proof (digs_snoc _ _ _ DG3 D3) as DG4. replace (k3 + 3 + 1)%Z with (k3 + 4)%Z in DG4 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He4.
    { cond_cleanup He4.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 4)%Z)); [exact PINV | lia | lia | lia | lia | exact DG4]. }
    cond_cleanup He4.
    txt_rd TXT (k3 + 4)%Z RD. pose proof (tx_range bs (k3 + 4)) as R4.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) (k3 + 4)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd4.
    { cond_cleanup Hd4. clear Hd4.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 4)%Z)); [exact PINV | lia | lia | lia | lia | exact DG4]. }
    cond_cleanup Hd4. pose proof (dig_yes _ R4 Hd4) as D4. clear Hd4.
    pose proof (digs_snoc _ _ _ DG4 D4) as DG5. replace (k3 + 4 + 1)%Z with (k3 + 5)%Z in DG5 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He5.
    { cond_cleanup He5.
      goto (eapply C_22460 with (k3 := k3) (kI := (k3 + 5)%Z)); [exact PINV | lia | lia | lia | lia | exact DG5]. }
    cond_cleanup He5.
    step. (* [comment removed for export] *)
    goto (eapply (spd_B_loop (S (Z.to_nat (L - (k3 + 5)))) (k3 + 5)%Z) with (k3 := k3));
      [lia | exact PINV | lia | lia | lia | lia | exact DG5].
  Qed.
End BLK.
End P_spd_B.


Module P_spd_C.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  Hypothesis C_22598 : K_22598 c.
  Hypothesis C_22a9c : K_22a9c c.

  #[local] Notation Zw z := (Z_to_bv 64 z).

  #[using="Type"] Lemma nz_of_mod : forall x M : Z, (x mod M <> 0)%Z -> x <> 0%Z.
  Proof. LiaFast.lf_pins LiaFast.u0. intros x M H E0. apply H. rewrite E0. apply Zmod_0_l. Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22598 C_22a9c"] Lemma C_22724 : forall junk m (x1 x5 x6 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ng k3 kI kp : Z),
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z ->
      tx bs kI = (bv_unsigned a4 mod 256)%Z -> (kI + 1 <= kp <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kp ->
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 a2 x9 (Zw ng) a1 x12 a3 a4 (Zw (P + kI)) (Zw (kI - k3)) (Zw (P + kI + 1))
                 (Zw (P + kp)) (Zw (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24614) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI kp
      PINV NG K3I K31 KIL DP KP DGI DGF.
    unfold K_22598 in C_22598. unfold K_22a9c in C_22a9c.
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (P + kI + 1)%Z), (unsigned_lit (P + kp)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - cond_cleanup Hnz.
      goto (eapply C_22598 with (k3 := k3) (kI := kI) (fp := (P + kI + 1)%Z) (fL := (kp - (kI + 1))%Z) (kp := kp));
        [exact PINV | lia | lia | lia | lia | lia | exact DGI | | ].
      + right. split; [reflexivity|]. split; [lia|]. split; [exact DP|]. split; [lia|].
        replace (kI + 1 + (kp - (kI + 1)))%Z with kp by lia. exact DGF.
      + Z.div_mod_to_equations. lia.
    - cond_cleanup Hnz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_22a9c). exact PINV.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22598 C_22a9c"] Lemma C_loop1 : forall (n : nat) junk m (x1 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ng k3 kI kc : Z),
      (L - kc <= Z.of_nat n)%Z ->
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z ->
      tx bs kI = (bv_unsigned a4 mod 256)%Z -> (kI + 1 <= kc < L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw 9) (Zw 10) x7 a2 x9 (Zw ng) a1 x12 a3 a4 (Zw (P + kI)) (Zw (kI - k3)) (Zw (P + kI + 1))
                 (Zw (P + kc)) (Zw (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x245f0) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI kc
      Hn PINV NG K3I K31 KIL DP KC DGI DGF.
    { exfalso. lia. }
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    txt_rd TXT kc RD. pose proof (tx_range bs kc) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. clear Hd.
      goto (eapply C_22724 with (kp := kc)); [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | exact DGF].
    - cond_cleanup Hd.
      match type of Hd with (Z.land _ 255 <= 9)%Z => idtac | ?t => idtac "HD-FORM" t end.
      pose proof (dig_yes_m _ Rk Hd) as D. clear Hd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH junk m) with (kc := (kc + 1)%Z));
          [lia | exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | apply digs_snoc; assumption].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        goto (eapply C_22724 with (kp := (kc + 1)%Z));
          [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | apply digs_snoc; assumption].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22598 C_22a9c"] Lemma C_226f4 : forall junk m (x1 x5 x6 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ng k3 kI kc : Z),
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z ->
      tx bs kI = (bv_unsigned a4 mod 256)%Z -> (kI + 1 <= kc <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 a2 x9 (Zw ng) a1 x12 a3 a4 (Zw (P + kI)) (Zw (kI - k3)) (Zw (P + kI + 1))
                 (Zw (P + kc)) (Zw (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x245e4) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI kc
      PINV NG K3I K31 KIL DP KC DGI DGF.
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    step. (* [comment removed for export] *)
    if_cases Hend.
    - cond_cleanup Hend.
      goto (eapply C_22724 with (kp := kc)); [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | exact DGF].
    - cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (C_loop1 (S (Z.to_nat (L - kc))) junk m) with (kc := kc));
        [lia | exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | exact DGF].
  Qed.

  #[using="Type"] Lemma digs_snoc4 : forall lo k, digs bs lo k ->
    isdig (tx bs k) -> isdig (tx bs (k + 1)) -> isdig (tx bs (k + 2)) -> isdig (tx bs (k + 3)) -> digs bs lo (k + 4).
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros lo k H D0 D1 D2 D3.
    replace (k + 4)%Z with (k + 3 + 1)%Z by lia. apply digs_snoc; [|exact D3].
    replace (k + 3)%Z with (k + 2 + 1)%Z by lia. apply digs_snoc; [|exact D2].
    replace (k + 2)%Z with (k + 1 + 1)%Z by lia. apply digs_snoc; [|exact D1].
    apply digs_snoc; [exact H|exact D0].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22598 C_22a9c"] Lemma C_4test : forall junk m (x1 x5 x6 x7 x9 x12 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ng k3 kI kc Vv : Z),
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z ->
      tx bs kI = (bv_unsigned a4 mod 256)%Z -> (kI + 1 <= kc)%Z -> (kc + 4 <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      (0 <= Vv < 2^64)%Z -> (Vv mod 2^32 = v4 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3)))%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 a2 x9 (Zw ng) a1 x12 a3 a4 (Zw (P + kI)) (Zw (kI - k3)) (Zw (P + kI + 1))
                 (Zw (P + kc)) (Zw (P + k3)) x20 x21 (Zw Vv) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24578) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x5 x6 x7 x9 x12 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI kc Vv
      PINV NG K3I K31 KIL DP KC1 KC2 DGI DGF VR VM.
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H4.
    - clear H4.
      goto (eapply C_226f4 with (kc := kc)); [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | exact DGF].
    - rewrite ?(unsigned_lit Vv) in H4 by lia.
      destruct (swar4_dig Vv _ _ _ _ R0 R1 R2 R3 VR VM H4) as (D0 & D1 & D2 & D3). clear H4.
      do 16 step. (* [comment removed for export] *)
      goto (eapply C_226f4 with (kc := (kc + 4)%Z)); [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | ].
      apply digs_snoc4; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22598 C_22a9c"] Lemma C_22658 : forall junk m (x1 x6 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ng k3 kI kc : Z),
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z ->
      tx bs kI = (bv_unsigned a4 mod 256)%Z -> (kI + 1 <= kc <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (L - kc)) x6 x7 a2 x9 (Zw ng) a1 x12 a3 a4 (Zw (P + kI)) (Zw (kI - k3)) (Zw (P + kI + 1))
                 (Zw (P + kc)) (Zw (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24548) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x1 x6 x7 x9 x12 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI kc
      PINV NG K3I K31 KIL DP KC DGI DGF.
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H4.
    - cond_cleanup H4. clear H4.
      goto (eapply C_226f4 with (kc := kc)); [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | exact DGF].
    - cond_cleanup H4. rewrite signed_lit in H4 by lia.
      pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
      pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
      txt_rd TXT (kc + 1)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 1)%Z.
      txt_rd TXT (kc + 0)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 0)%Z. rewrite (Z.add_0_r kc).
      txt_rd TXT (kc + 2)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 2)%Z.
      txt_rd TXT (kc + 3)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 3)%Z.
      do 6 step. (* [comment removed for export] *)
      rewrite (ortree4_eq (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))) by (apply tx_range).
      pose proof (v4_range _ _ _ _ R0 R1 R2 R3) as VR.
      goto (eapply C_4test with (kc := kc) (Vv := v4 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))));
        [exact PINV | lia | lia | lia | lia | exact DP | lia | lia | exact DGI | exact DGF | lia | apply Z.mod_small; lia].
  Qed.

  #[using="Type"] Lemma v8_facts : forall z0 z1 z2 z3 z4 z5 z6 z7,
    (0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
     0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
     0 <= v8 z0 z1 z2 z3 z4 z5 z6 z7 < 2^64 /\ v8 z0 z1 z2 z3 z4 z5 z6 z7 mod 2^32 = v4 z0 z1 z2 z3)%Z.
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros. pose proof (v4_range z0 z1 z2 z3). pose proof (v4_range z4 z5 z6 z7). unfold v8. split; [lia|].
    rewrite (Z.mul_comm (2^32)). rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22598 C_22a9c"] Lemma C_loop8 : forall (n : nat) junk m (x1 x9 x12 x20 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
      (ng k3 kI kc : Z),
      (L - kc <= Z.of_nat n)%Z ->
      pinv c junk m -> (0 <= ng <= 1)%Z -> (0 <= k3 <= kI)%Z -> (k3 <= 1)%Z -> (kI < L)%Z ->
      tx bs kI = (bv_unsigned a4 mod 256)%Z -> (kI + 1 <= kc)%Z -> (kc + 8 <= L)%Z -> digs bs k3 kI -> digs bs (kI + 1) kc ->
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp (Zw (L - kc)) (Zw 14974415777481871312) (Zw 9259542123273814144) a2 x9 (Zw ng) a1 x12 a3 a4
                 (Zw (P + kI)) (Zw (kI - k3)) (Zw (P + kI + 1))
                 (Zw (P + kc)) (Zw (P + k3)) x20 (Zw 7) x22 x23 x24 x25 x26 x27 (Zw 5063812098665367110) x29 x30 x31)
            F (Zw 0x243c4) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x1 x9 x12 x20 x22 x23 x24 x25 x26 x27 x29 x30 x31 ng k3 kI kc
      Hn PINV NG K3I K31 KIL DP KC1 KC8 DGI DGF.
    { exfalso. lia. }
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    pose proof (tx_range bs (kc + 4)) as R4. pose proof (tx_range bs (kc + 5)) as R5.
    pose proof (tx_range bs (kc + 6)) as R6. pose proof (tx_range bs (kc + 7)) as R7.
    txt_rd TXT (kc + 1)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 1)%Z.
    txt_rd TXT (kc + 2)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 2)%Z.
    txt_rd TXT (kc + 3)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 3)%Z.
    txt_rd TXT (kc + 0)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 0)%Z. rewrite (Z.add_0_r kc).
    do 4 step. (* [comment removed for export] *)
    txt_rd TXT (kc + 4)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 4)%Z.
    txt_rd TXT (kc + 5)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 5)%Z.
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 6)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 6)%Z.
    txt_rd TXT (kc + 7)%Z RD. step. clear RD. fold_tx (r_bs c) (kc + 7)%Z.
    do 9 step. (* [comment removed for export] *)
    rewrite (ortree8_eq (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7))) by (apply tx_range).
    destruct (v8_facts _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7) as [VR VM].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsw.
    - clear Hsw.
      goto (eapply C_4test with (kc := kc) (Vv := v8 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7))));
        [exact PINV | lia | lia | lia | lia | exact DP | lia | lia | exact DGI | exact DGF | exact VR | exact VM].
    - rewrite ?(unsigned_lit (v8 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7)))) in Hsw by lia.
      destruct (swar8_dig _ _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7 eq_refl Hsw) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7).
      clear Hsw.
      assert (DGF' : digs bs (kI + 1) (kc + 8)).
      { replace (kc + 8)%Z with (kc + 4 + 4)%Z by lia.
        apply digs_snoc4; [apply digs_snoc4; assumption | exact D4 | | |].
        - replace (kc + 4 + 1)%Z with (kc + 5)%Z by lia. exact D5.
        - replace (kc + 4 + 2)%Z with (kc + 6)%Z by lia. exact D6.
        - replace (kc + 4 + 3)%Z with (kc + 7)%Z by lia. exact D7. }
      do 14 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore. rewrite signed_lit in Hmore by lia.
        goto (eapply (IH junk m) with (kc := (kc + 8)%Z));
          [lia | exact PINV | lia | lia | lia | lia | exact DP | lia | lia | exact DGI | exact DGF'].
      + cond_cleanup Hmore. rewrite signed_lit in Hmore by lia.
        step. (* [comment removed for export] *)
        goto (eapply C_22658 with (kc := (kc + 8)%Z));
          [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DGI | exact DGF'].
  Qed.

  #[using="PRE C_22598 C_22a9c"] Lemma spd_C : K_22460 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22598 C_22a9c : LiaFast.U) => LiaFast.u0).
    unfold K_22598 in C_22598. unfold K_22a9c in C_22a9c.
    unfold K_22460. intros junk m x1 x5 x6 x7 x9 x12 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI
      PINV NG K3I KIL K31 DG.
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (P + kI)%Z), (unsigned_lit (P + k3)%Z) by lia.
    (* [comment removed for export] *)
    assert (NODP : forall x5 x17,
      evt PSEGS POST
        (MS (mkR x1 (Zw SP) gp tp x5 x6 x7 a2 x9 (Zw ng) a1 x12 a3 a4 (Zw (P + kI)) (Zw (P + kI - (P + k3))) x17
                 x18 (Zw (P + k3)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Zw 0x24470) fc None m (seg_rom PSEGS))).
    { intros y5 y17.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply C_22a9c). exact PINV.
      - cond_cleanup Hz.
        goto (eapply C_22598 with (k3 := k3) (kI := kI) (fp := 0%Z) (fL := 0%Z) (kp := kI));
          [exact PINV | lia | lia | lia | lia | lia | exact DG | left; lia | ].
        Z.div_mod_to_equations. lia. }
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend. apply NODP. }
    cond_cleanup Hend.
    txt_rd TXT kI RD. pose proof (tx_range bs kI) as RkI.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kI.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hdp.
    { cond_cleanup Hdp. apply NODP. }
    cond_cleanup Hdp.
    assert (DP : tx bs kI = (bv_unsigned a4 mod 256)%Z).
    { rewrite Hdp. change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    clear Hdp.
    pose proof (digs_nil bs (kI + 1)) as DGF.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (P + kI + 1)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H8.
    - cond_cleanup H8. rewrite signed_lit in H8 by lia.
      step. (* [comment removed for export] *)
      goto (eapply C_22658 with (kc := (kI + 1)%Z));
        [exact PINV | lia | lia | lia | lia | exact DP | lia | exact DG | exact DGF].
    - cond_cleanup H8. rewrite signed_lit in H8 by lia.
      do 7 step. (* [comment removed for export] *)
      step. step. step. (* [comment removed for export] *)
      do 10 step. (* [comment removed for export] *)
      goto (eapply (C_loop8 (S (Z.to_nat (L - (kI + 1)))) junk m) with (kc := (kI + 1)%Z));
        [lia | exact PINV | lia | lia | lia | lia | exact DP | lia | lia | exact DG | exact DGF].
  Qed.
End BLK.
End P_spd_C.


Module P_spd_D.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  Hypothesis C_227c4 : K_227c4 c.
  Hypothesis C_22a9c : K_22a9c c.

  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  Definition dctx (ng k3 kI fp fL kp : Z) junk m : Prop :=
    pinv c junk m /\ (0 <= ng <= 1)%Z /\ (0 <= k3 <= kI)%Z /\ (k3 <= 1)%Z /\ (0 <= fL)%Z /\
    (kI <= kp <= L)%Z /\ digs bs k3 kI /\ spans c k3 kI fp fL kp /\ (0 < (kI - k3) + fL)%Z.

  #[local] Ltac open_dctx DX :=
    destruct DX as (PINV & NG & K3I & K31 & FL0 & KP & DGI & SPANS & DC);
    pre_facts; pose proof PINV as PINV'; open_pinv PINV'.

  Section D.
  Variable x1 : word.

  (* [comment removed for export] *)
  #[local] Notation DST pc x7 x9 x12 x13 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m :=
    (MS (mkR x1 (Zw SP) gp tp (Zw fL) (Zw ((kI - k3) + fL)) x7 a2 x9 (Zw ng) a1 x12 x13 a4
             (Zw (P + kI)) (Zw (kI - k3)) (Zw fp) (Zw (P + kp)) (Zw (P + k3)) x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom PSEGS)) (only parsing).


  (* [comment removed for export] *)
  #[using="PRE C_227c4 C_22a9c"] Lemma D_24664 : forall junk m (x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp,
      dctx ng k3 kI fp fL kp junk m ->
      evt PSEGS POST (DST 0x246a4 x7 x9 x12 a3 (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp DX. open_dctx DX.
    unfold K_227c4 in C_227c4. unfold K_22a9c in C_22a9c.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hfx.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_22a9c). exact PINV.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_227c4 with (k3 := k3) (kI := kI) (fp := fp) (fL := fL) (kp := kp) (kq := kp) (xn := 0%Z));
        [exact PINV | lia | lia | lia | lia | lia | lia | exact DGI | exact SPANS | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4"] Lemma D_24654 : forall junk m (x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp kq xn ngx,
      dctx ng k3 kI fp fL kp junk m -> (kp <= kq <= L)%Z -> (0 <= xn < 2^32)%Z -> (0 <= ngx <= 1)%Z ->
      evt PSEGS POST (DST 0x24694 (Zw ngx) (Zw (P + kq)) x12 (Zw xn) (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 : LiaFast.U) => LiaFast.u0).
    intros junk m x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp kq xn ngx DX KQ XN NGX. open_dctx DX.
    unfold K_227c4 in C_227c4.
    step. (* [comment removed for export] *)
    if_cases Hng.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_227c4 with (k3 := k3) (kI := kI) (fp := fp) (fL := fL) (kp := kp) (kq := kq) (xn := xn));
        [exact PINV | lia | lia | lia | lia | lia | lia | exact DGI | exact SPANS | lia | lia].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_227c4 with (k3 := k3) (kI := kI) (fp := fp) (fL := fL) (kp := kp) (kq := kq) (xn := (- xn)%Z));
        [exact PINV | lia | lia | lia | lia | lia | lia | exact DGI | exact SPANS | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4"] Lemma D_loopx : forall (n : nat) junk m (x12 x21 x22 x23 x24 x25 x26 x27 x31 : word) ng k3 kI fp fL kp kq xn ngx,
      (L - kq <= Z.of_nat n)%Z ->
      dctx ng k3 kI fp fL kp junk m -> (kp <= kq < L)%Z -> (0 <= xn < 2^32)%Z -> (0 <= ngx <= 1)%Z ->
      evt PSEGS POST (DST 0x2466c (Zw ngx) (Zw (P + kq)) x12 (Zw xn) (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27
                          (Zw 9) (Zw 10) (Zw 268435456) x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x12 x21 x22 x23 x24 x25 x26 x27 x31 ng k3 kI fp fL kp kq xn ngx Hn DX KQ XN NGX.
    { exfalso. lia. }
    pose proof DX as DX'. open_dctx DX'.
    txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd.
      goto (eapply D_24654 with (kq := kq) (xn := xn) (ngx := ngx)); [exact DX | lia | lia | lia].
    - clear Hd.
      step. (* [comment removed for export] *)
      if_cases Hcl.
      + cond_cleanup Hcl. rewrite ?signed_lit in Hcl by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore.
          goto (eapply (IH junk m) with (kq := (kq + 1)%Z) (xn := xn) (ngx := ngx)); [lia | exact DX | lia | lia | lia].
        * cond_cleanup Hmore.
          step. (* [comment removed for export] *)
          goto (eapply D_24654 with (kq := (kq + 1)%Z) (xn := xn) (ngx := ngx)); [exact DX | lia | lia | lia].
      + cond_cleanup Hcl. rewrite ?signed_lit in Hcl by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit xn) by lia.
        lazymatch goal with |- context [Zw (xn * 10 + Z.land ?u 255)%Z] =>
          pose proof (land255_range u) as T0; set (xn' := (xn * 10 + Z.land u 255)%Z) in *
        | |- ?g => idtac "ADDFORM"; idtac g end.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore.
          goto (eapply (IH junk m) with (kq := (kq + 1)%Z) (xn := xn') (ngx := ngx)); [lia | exact DX | lia | lia | lia].
        * cond_cleanup Hmore.
          step. (* [comment removed for export] *)
          goto (eapply D_24654 with (kq := (kq + 1)%Z) (xn := xn') (ngx := ngx)); [exact DX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4 C_22a9c"] Lemma D_24610 : forall junk m (x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp kq ngx,
      dctx ng k3 kI fp fL kp junk m -> (kp <= kq < L)%Z -> (0 <= ngx <= 1)%Z ->
      evt PSEGS POST (DST 0x24650 (Zw ngx) (Zw (P + kq)) x12 a3 (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp kq ngx DX KQ NGX.
    pose proof DX as DX'. open_dctx DX'.
    txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd. goto (eapply D_24664). exact DX.
    - clear Hd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (D_loopx (S (Z.to_nat (L - kq))) junk m) with (kq := kq) (xn := 0%Z) (ngx := ngx));
        [lia | exact DX | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4 C_22a9c"] Lemma D_244d0 : forall junk m (x7 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp kq,
      dctx ng k3 kI fp fL kp junk m -> (kp <= kq <= L)%Z ->
      evt PSEGS POST (DST 0x24510 x7 (Zw (P + kq)) x12 a3 (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x7 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp kq DX KQ.
    pose proof DX as DX'. open_dctx DX'.
    step. (* [comment removed for export] *)
    if_cases Hend.
    - cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hx; cond_cleanup Hx; [exfalso; lia|].
      step. (* [comment removed for export] *)
      goto (eapply D_24664). exact DX.
    - cond_cleanup Hend.
      txt_rd TXT kq RD. pose proof (tx_range bs kq) as Rk.
      step. (* [comment removed for export] *)
      clear RD. fold_tx (r_bs c) kq.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hminus.
      + clear Hminus.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite v_sltiu_b2z.
        lazymatch goal with |- context [Zw (Z.b2z ?b)] =>
          pose proof (b2z_range b) as PL; set (pl := Z.b2z b) in *; clearbody pl end.
        step. (* [comment removed for export] *)
        rewrite ?(unsigned_lit (P + kq)%Z), ?(unsigned_lit pl) by lia.
        step. (* [comment removed for export] *)
        if_cases He.
        * clear He. goto (eapply D_24664). exact DX.
        * cond_cleanup He.
          goto (eapply D_24610 with (kq := (kq + pl)%Z) (ngx := 0%Z)); [exact DX | lia | lia].
      + clear Hminus.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He.
        * cond_cleanup He.
          goto (eapply D_24610 with (kq := (kq + 1)%Z) (ngx := 1%Z)); [exact DX | lia | lia].
        * clear He.
          step. (* [comment removed for export] *)
          goto (eapply D_24664). exact DX.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4 C_22a9c"] Lemma D_244a0 : forall junk m (x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp,
      dctx ng k3 kI fp fL kp junk m -> (kp < L)%Z ->
      evt PSEGS POST (DST 0x244e0 (Zw (tx bs kp)) x9 x12 a3 (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp DX KP'.
    pose proof DX as DX'. open_dctx DX'. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs.
    - clear Hs. goto (eapply D_244d0 with (kq := kp)); [exact DX | lia].
    - clear Hs.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hskip.
      + clear Hskip. goto (eapply D_244d0 with (kq := kp)); [exact DX | lia].
      + clear Hskip.
        step. (* [comment removed for export] *)
        goto (eapply D_244d0 with (kq := (kp + 1)%Z)); [exact DX | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4 C_22a9c"] Lemma D_244f0 : forall junk m (x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp,
      dctx ng k3 kI fp fL kp junk m ->
      evt PSEGS POST (DST 0x24530 x7 x9 x12 a3 (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp DX.
    pose proof DX as DX'. open_dctx DX'.
    unfold K_227c4 in C_227c4. unfold K_22a9c in C_22a9c.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsci.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_227c4 with (k3 := k3) (kI := kI) (fp := fp) (fL := fL) (kp := kp) (kq := kp) (xn := 0%Z));
        [exact PINV | lia | lia | lia | lia | lia | lia | exact DGI | exact SPANS | lia | lia].
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply C_22a9c). exact PINV.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_227c4 C_22a9c"] Lemma D_24464 : forall junk m (x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) ng k3 kI fp fL kp,
      dctx ng k3 kI fp fL kp junk m ->
      evt PSEGS POST (DST 0x244a4 x7 x9 x12 a3 (Zw (- fL)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp m).
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    intros junk m x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp DX.
    pose proof DX as DX'. open_dctx DX'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hf; [clear Hf; goto (eapply D_244f0); exact DX|]. clear Hf.
    step. (* [comment removed for export] *)
    if_cases He; [clear He; goto (eapply D_244f0); exact DX|]. cond_cleanup He.
    txt_rd TXT kp RD. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hr; [clear Hr; goto (eapply D_244f0); exact DX|]. clear Hr.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; [clear Hb; goto (eapply D_244f0); exact DX|]. clear Hb.
    goto (eapply D_244a0); [exact DX | lia].
  Qed.

  End D.

  #[using="PRE C_227c4 C_22a9c"] Lemma spd_D : K_22598 c.
  Proof. LiaFast.lf_pins (fun (PRE C_227c4 C_22a9c : LiaFast.U) => LiaFast.u0).
    unfold K_22598. intros junk m x1 x7 x9 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp
      PINV NG K3I K31 FL0 KP DGI SPANS DC.
    assert (DX : dctx ng k3 kI fp fL kp junk m).
    { split; [exact PINV|]. split; [exact NG|]. split; [exact K3I|]. split; [exact K31|]. split; [exact FL0|].
      split; [exact KP|]. split; [exact DGI|]. split; [exact SPANS| exact DC]. }
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs; [clear Hs; goto (eapply D_24464); exact DX|]. clear Hs.
    step. (* [comment removed for export] *)
    if_cases He; [clear He; goto (eapply D_24464); exact DX|]. cond_cleanup He.
    txt_rd TXT kp RD. pose proof (tx_range bs kp) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hee.
    - clear Hee. goto (eapply D_244a0); [exact DX | lia].
    - clear Hee. goto (eapply D_24464); exact DX.
  Qed.
End BLK.
End P_spd_D.


Module P_spd_E.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  Hypothesis C_22cac : K_22cac c.

  #[local] Notation Zw z := (Z_to_bv 64 z).
  Definition C19 : Z := 999999999999999999.

  (* [comment removed for export] *)
  Definition ectx (ng k3 kI fp fL kp kq : Z) junk m : Prop :=
    pinv c junk m /\ (0 <= ng <= 1)%Z /\ (0 <= k3 <= kI)%Z /\ (k3 <= 1)%Z /\ (0 <= fL)%Z /\
    (kI <= kp <= kq)%Z /\ (kq <= L)%Z /\ digs bs k3 kI /\ spans c k3 kI fp fL kp /\ (0 < (kI - k3) + fL)%Z /\
    (kI + fL <= kp)%Z.

  (* [comment removed for export] *)
  Definition NZ (k3 kI fL : Z) : Prop := zeros bs k3 kI -> (fL = 0 \/ zeros bs (kI + 1) (kI + 1 + fL))%Z -> False.

  #[local] Ltac open_ectx EX :=
    destruct EX as (PINV & NG & K3I & K31 & FL0 & KPQ & KQL & DGI & SPANS & DC & FLK);
    pre_facts; pose proof PINV as PINV'; open_pinv PINV'.

  Section E.
  Variables x1 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word.

  #[local] Notation EST pc x6 x7 x11 x12 x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq m :=
    (MS (mkR x1 (Zw SP) gp tp (Zw fL) x6 x7 a2 (Zw (P + kq)) (Zw ng) x11 x12 x13 x14
             x15 (Zw (kI - k3)) (Zw fp) (Zw (P + kp)) (Zw (P + k3)) x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom PSEGS)) (only parsing).

  #[local] Ltac fin266 PINV SPANS tmv :=
    goto (eapply C_22cac with (tm := tmv));
    [ exact PINV | lia | lia | lia | lia | lia
    | destruct SPANS as [(?&?&?)|(?&?&?&?&?)]; [left; lia | right; lia]
    | lia | ].

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_fin1 : forall junk m (x6 x7 x11 x13 x14 x15 x20 x28 x29 : word) ng k3 kI fp fL kp kq wv,
      ectx ng k3 kI fp fL kp kq junk m -> (0 < wv < 2^64 - 1)%Z ->
      evt PSEGS POST (EST 0x24b90 x6 x7 x11 (Zw wv) x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    intros junk m x6 x7 x11 x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq wv EX WV. open_ectx EX.
    unfold K_22cac in C_22cac.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fin266 PINV SPANS 1%Z. intros _. rewrite unsigned_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_fin0 : forall junk m (x6 x7 x11 x12 x13 x14 x15 x20 x28 x29 : word) ng k3 kI fp fL kp kq,
      ectx ng k3 kI fp fL kp kq junk m ->
      evt PSEGS POST (EST 0x2476c x6 x7 x11 x12 x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    intros junk m x6 x7 x11 x12 x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq EX. open_ectx EX.
    unfold K_22cac in C_22cac.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    fin266 PINV SPANS 0%Z. intros; lia.
  Qed.

  #[using="PRE C_22cac"] Lemma E_24b4c : forall junk m (x6 x7 x11 x13 x14 x15 x20 x28 x29 : word) ng k3 kI fp fL kp kq wv,
      ectx ng k3 kI fp fL kp kq junk m -> (0 < wv < 2^64 - 1)%Z ->
      evt PSEGS POST (EST 0x24b8c x6 x7 x11 (Zw wv) x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    intros junk m x6 x7 x11 x13 x14 x15 x20 x28 x29 ng k3 kI fp fL kp kq wv EX WV.
    step. (* [comment removed for export] *)
    goto (eapply E_fin1 with (wv := wv)); [exact EX | exact WV].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_loopF : forall (n : nat) junk m (x7 x13 x20 x28 x29 : word) ng k3 kI fp fL kp kq kf wv,
      (kI + 1 + fL - kf <= Z.of_nat n)%Z ->
      ectx ng k3 kI fp fL kp kq junk m -> NZ k3 kI fL ->
      (fp = P + kI + 1)%Z -> (kI + 1 + fL <= L)%Z -> digs bs (kI + 1) (kI + 1 + fL) ->
      (kI + 1 <= kf < kI + 1 + fL)%Z -> (0 <= wv <= C19)%Z ->
      (wv = 0%Z -> zeros bs k3 kI /\ zeros bs (kI + 1) kf) ->
      evt PSEGS POST (EST 0x24740 (Zw (kI + fL - kf)) x7 (Zw (P + kf)) (Zw wv) x13 (Zw C19) (Zw 10) x20 x28 x29
                          ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x7 x13 x20 x28 x29 ng k3 kI fp fL kp kq kf wv Hn EX NZH FP FEND DGF KF WV ZF.
    { exfalso. lia. }
    pose proof EX as EX'. open_ectx EX'. unfold C19 in *.
    txt_rd TXT kf RD. pose proof (tx_range bs kf) as Rk. pose proof (DGF kf ltac:(lia)) as Dk. unfold isdig in Dk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) kf.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit wv), ?(unsigned_lit (wv * 10)%Z), ?(unsigned_lit (wv * 10 + tx bs kf)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hbig.
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      goto (eapply E_24b4c with (wv := (wv * 10 + tx bs kf + -48)%Z)); [exact EX | lia].
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH junk m) with (kf := (kf + 1)%Z) (wv := (wv * 10 + tx bs kf + -48)%Z));
          [lia | exact EX | exact NZH | lia | lia | exact DGF | | unfold C19; lia | ].
        * Z.div_mod_to_equations. lia.
        * intros Hz. assert (wv = 0%Z) as -> by lia. destruct (ZF eq_refl) as [Z1 Z2].
          split; [exact Z1|]. apply zeros_snoc; [exact Z2 | lia].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        assert (NZW : (wv * 10 + tx bs kf + -48 <> 0)%Z).
        { intros Hz. assert (wv = 0%Z) as -> by lia. destruct (ZF eq_refl) as [Z1 Z2].
          apply (NZH Z1). right. replace (kI + 1 + fL)%Z with (kf + 1)%Z by (Z.div_mod_to_equations; lia).
          apply zeros_snoc; [exact Z2 | lia]. }
        goto (eapply E_24b4c with (wv := (wv * 10 + tx bs kf + -48)%Z)); [exact EX | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_246ec : forall junk m (x6 x7 x11 x13 x15 x20 x28 x29 : word) ng k3 kI fp fL kp kq wv,
      ectx ng k3 kI fp fL kp kq junk m -> NZ k3 kI fL -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> zeros bs k3 kI) ->
      evt PSEGS POST (EST 0x2472c x6 x7 x11 (Zw wv) x13 (Zw 79604) x15 x20 x28 x29 ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    intros junk m x6 x7 x11 x13 x15 x20 x28 x29 ng k3 kI fp fL kp kq wv EX NZH WV ZF.
    pose proof EX as EX'. open_ectx EX'. unfold C19 in *.
    step. (* [comment removed for export] *)
    if_cases Hf0.
    - cond_cleanup Hf0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (NZW : wv <> 0%Z).
      { intros ->. apply (NZH (ZF eq_refl)). left. rewrite ?Z.mod_small in Hf0 by lia. lia. }
      goto (eapply E_fin1 with (wv := wv)); [exact EX | lia].
    - cond_cleanup Hf0.
      destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; [exfalso; lia|].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (E_loopF (S (Z.to_nat fL)) junk m) with (kf := (kI + 1)%Z) (wv := wv));
        [lia | exact EX | exact NZH | exact F1 | lia | exact F5 | lia | unfold C19; lia | ].
      intros Hz. split; [exact (ZF Hz) | apply zeros_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_loopI : forall (n : nat) junk m (x13 x20 x28 x29 : word) ng k3 kI fp fL kp kq ki wv,
      (kI - ki <= Z.of_nat n)%Z ->
      ectx ng k3 kI fp fL kp kq junk m -> NZ k3 kI fL ->
      (k3 <= ki < kI)%Z -> (0 <= wv <= C19)%Z -> (wv = 0%Z -> zeros bs k3 ki) ->
      evt PSEGS POST (EST 0x2470c (Zw C19) (Zw 10) (Zw (P + ki)) (Zw wv) x13 (Zw 79604) (Zw (P + kI)) x20 x28 x29
                          ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x13 x20 x28 x29 ng k3 kI fp fL kp kq ki wv Hn EX NZH KI WV ZF.
    { exfalso. lia. }
    pose proof EX as EX'. open_ectx EX'. unfold C19 in *.
    txt_rd TXT ki RD. pose proof (tx_range bs ki) as Rk. pose proof (DGI ki ltac:(lia)) as Dk. unfold isdig in Dk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) ki.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit wv), ?(unsigned_lit (wv * 10)%Z), ?(unsigned_lit (wv * 10 + tx bs ki)%Z) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hbig.
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      step. (* [comment removed for export] *)
      if_taken.
      goto (eapply E_fin1 with (wv := (wv * 10 + tx bs ki + -48)%Z)); [exact EX | lia].
    - cond_cleanup Hbig. rewrite ?Z.mod_small in Hbig by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH junk m) with (ki := (ki + 1)%Z) (wv := (wv * 10 + tx bs ki + -48)%Z));
          [lia | exact EX | exact NZH | lia | unfold C19; lia | ].
        intros Hz. assert (wv = 0%Z) as -> by lia. apply zeros_snoc; [exact (ZF eq_refl) | lia].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        if_not_taken.
        goto (eapply E_246ec with (wv := (wv * 10 + tx bs ki + -48)%Z));
          [exact EX | exact NZH | unfold C19; lia | ].
        intros Hz. assert (wv = 0%Z) as -> by lia. replace kI with (ki + 1)%Z by lia.
        apply zeros_snoc; [exact (ZF eq_refl) | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_246b4 : forall junk m (x6 x7 x11 x12 x13 x14 x20 x28 x29 : word) ng k3 kI fp fL kp kq,
      ectx ng k3 kI fp fL kp kq junk m -> NZ k3 kI fL ->
      evt PSEGS POST (EST 0x246f4 x6 x7 x11 x12 x13 x14 (Zw (P + kI)) x20 x28 x29 ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    intros junk m x6 x7 x11 x12 x13 x14 x20 x28 x29 ng k3 kI fp fL kp kq EX NZH.
    pose proof EX as EX'. open_ectx EX'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hemp.
    - cond_cleanup Hemp.
      goto (eapply E_246ec with (wv := 0%Z)); [exact EX | exact NZH | unfold C19; lia | ].
      intros _. replace kI with k3 by lia. apply zeros_nil.
    - cond_cleanup Hemp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (E_loopI (S (Z.to_nat (kI - k3))) junk m) with (ki := k3) (wv := 0%Z));
        [lia | exact EX | exact NZH | lia | unfold C19; lia | intros _; apply zeros_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_246ac : forall junk m (x7 x11 x12 x13 x14 x20 x28 x29 : word) ng k3 kI fp fL kp kq ks dpv,
      ectx ng k3 kI fp fL kp kq junk m ->
      dpv = (bv_unsigned a4 mod 256)%Z -> (k3 <= ks <= L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = dpv) ->
      (ks = L \/ (tx bs ks <> 48%Z /\ tx bs ks <> dpv)) ->
      evt PSEGS POST (EST 0x246ec (Zw ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))) x7 x11 x12 x13 x14 (Zw (P + kI)) x20 x28 x29
                          ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    intros junk m x7 x11 x12 x13 x14 x20 x28 x29 ng k3 kI fp fL kp kq ks dpv EX DPV KS SCAN EXIT.
    pose proof EX as EX'. open_ectx EX'.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply E_fin0). exact EX.
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      goto (eapply E_246b4); [exact EX|].
      intros ZI ZF.
      assert (SP' : (fL = 0 \/ (kI < L /\ tx bs kI = dpv /\ kI + 1 + fL <= L /\ zeros bs (kI + 1) (kI + 1 + fL)))%Z).
      { destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; [left; exact F2|].
        destruct ZF as [F0|ZF]; [left; exact F0 | right].
        split; [exact F2|]. split; [rewrite F3, DPV; reflexivity|]. split; [lia | exact ZF]. }
      exact (strip_contra bs L k3 kI fL ks dpv ltac:(lia) ltac:(lia) FL0 KS ZI SP' SCAN EXIT H20).
  Qed.
  #[using="Type"] Lemma seqz_m48 : forall t, (0 <= t < 256)%Z -> t <> 48%Z -> v_sltiu (Zw (t + -48)) 1 = Zw 0.
  Proof. LiaFast.lf_pins LiaFast.u0.
    intros t Ht Hne. rewrite v_sltiu_b2z. rewrite unsigned_lit_wrap.
    replace (bv_wrap 64 1) with 1%Z by reflexivity.
    destruct (Z.ltb_spec0 ((t + -48) mod 2^64) 1) as [Hl|Hl]; [|reflexivity].
    exfalso. destruct (Z_lt_le_dec t 48).
    - rewrite <- (Z.mod_add _ 1) in Hl by lia. rewrite Z.mod_small in Hl by lia. lia.
    - rewrite Z.mod_small in Hl by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_22cac"] Lemma E_loopS : forall (n : nat) junk m (x12 x13 x20 x29 : word) ng k3 kI fp fL kp kq ks dpv t1v,
      (L - ks <= Z.of_nat n)%Z ->
      ectx ng k3 kI fp fL kp kq junk m ->
      dpv = (bv_unsigned a4 mod 256)%Z -> (k3 <= ks < L)%Z ->
      (forall k, (k3 <= k < ks)%Z -> tx bs k = 48%Z \/ tx bs k = dpv) ->
      t1v = ((kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks - k3)))%Z ->
      evt PSEGS POST (EST 0x246cc (Zw t1v) (Zw 48) a1 x12 x13 (Zw dpv) (Zw (P + kI)) x20 (Zw (P + ks)) x29
                          ng k3 kI fp fL kp kq m).
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros junk m x12 x13 x20 x29 ng k3 kI fp fL kp kq ks dpv t1v Hn EX DPV KS SCAN T1V.
    { exfalso. lia. }
    pose proof EX as EX'. open_ectx EX'.
    pose proof (cnt48_range bs k3 (Z.to_nat (ks - k3))) as CR.
    assert (DPR : (0 <= dpv < 256)%Z) by (rewrite DPV; apply Z.mod_pos_bound; lia).
    txt_rd TXT ks RD. pose proof (tx_range bs ks) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx (r_bs c) ks.
    (* [comment removed for export] *)
    assert (TAIL : forall is0 : Z,
      (is0 = (if (tx bs ks =? 48)%Z then 1 else 0))%Z -> (tx bs ks = 48%Z \/ tx bs ks = dpv) ->
      evt PSEGS POST (EST 0x246e0 (Zw t1v) (Zw 48) a1 x12 x13 (Zw dpv) (Zw (P + kI)) x20 (Zw (P + ks)) (Zw is0)
                          ng k3 kI fp fL kp kq m)).
    { intros is0 IS0 HB.
      assert (IS0R : (0 <= is0 <= 1)%Z) by (rewrite IS0; destruct (tx bs ks =? 48)%Z; lia).
      assert (SCAN' : forall k, (k3 <= k < ks + 1)%Z -> tx bs k = 48%Z \/ tx bs k = dpv).
      { intros k Hk. destruct (Z.eq_dec k ks) as [->|]; [exact HB|]. apply SCAN. lia. }
      assert (T1V' : (t1v - is0 = (kI - k3) + fL - cnt48 bs k3 (Z.to_nat (ks + 1 - k3)))%Z).
      { replace (Z.to_nat (ks + 1 - k3)) with (S (Z.to_nat (ks - k3))) by lia.
        rewrite cnt48_step. replace (k3 + Z.of_nat (Z.to_nat (ks - k3)))%Z with ks by lia. rewrite <- IS0. lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      - cond_cleanup Hmore.
        goto (eapply (IH junk m) with (ks := (ks + 1)%Z) (t1v := (t1v - is0)%Z));
          [lia | exact EX | exact DPV | lia | exact SCAN' | exact T1V'].
      - cond_cleanup Hmore.
        goto (eapply E_246ac with (ks := (ks + 1)%Z) (dpv := dpv));
          [exact EX | exact DPV | lia | exact SCAN' | left; lia]. }
    step. (* [comment removed for export] *)
    if_cases H48.
    - cond_cleanup H48.
      rewrite H48.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (TAIL 1%Z)); [rewrite H48; reflexivity | left; exact H48].
    - cond_cleanup H48.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      + cond_cleanup Hdp.
        goto (eapply E_246ac with (ks := ks) (dpv := dpv));
          [exact EX | exact DPV | lia | exact SCAN | right; split; [exact H48 | exact Hdp]].
      + cond_cleanup Hdp.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (seqz_m48 (tx bs ks) Rk H48).
        goto (eapply (TAIL 0%Z)); [rewrite (proj2 (Z.eqb_neq _ _) H48); reflexivity | right; exact Hdp].
  Qed.

  End E.

  #[using="PRE C_22cac"] Lemma spd_E : K_227c4 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22cac : LiaFast.U) => LiaFast.u0).
    unfold K_227c4. intros junk m x1 x7 x12 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ng k3 kI fp fL kp kq xn
      PINV NG K3I K31 FL0 KPQ KQL DGI SPANS DC XN.
    assert (EX : ectx ng k3 kI fp fL kp kq junk m).
    { split; [exact PINV|]. split; [exact NG|]. split; [exact K3I|]. split; [exact K31|]. split; [exact FL0|].
      split; [exact KPQ|]. split; [exact KQL|]. split; [exact DGI|]. split; [exact SPANS|]. split; [exact DC|].
      destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; lia. }
    pre_facts. pose proof PINV as PINV'. open_pinv PINV'.
    assert (FLK : (kI + fL <= kp)%Z) by (destruct SPANS as [(F1 & F2 & F3)|(F1 & F2 & F3 & F4 & F5)]; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H20.
    - clear H20. goto (eapply E_fin0). exact EX.
    - cond_cleanup H20. rewrite signed_lit in H20 by lia.
      step. (* [comment removed for export] *)
      if_cases Hk3.
      { cond_cleanup Hk3. exfalso. lia. }
      cond_cleanup Hk3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (E_loopS x1 x21 x22 x23 x24 x25 x26 x27 x30 x31 (S (Z.to_nat (L - k3))) junk m)
              with (ks := k3) (dpv := (bv_unsigned a4 mod 256)%Z) (t1v := ((kI - k3) + fL)%Z));
        [ | lia | exact EX | reflexivity | lia | intros; lia | ].
      + change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity.
      + replace (Z.to_nat (k3 - k3)) with O by lia. cbn [cnt48]. lia.
  Qed.
End BLK.
End P_spd_E.


Module P_spd_T0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbv beta delta [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  Hypothesis C_22d1c : K_22d1c c.

  (* [comment removed for export] *)
  #[using="PRE C_22d1c"] Lemma spd_T0 : K_22cac c.
  Proof. LiaFast.lf_pins (fun (PRE C_22d1c : LiaFast.U) => LiaFast.u0).
    unfold K_22d1c in C_22d1c.
    unfold K_22cac. intros junk m x1 x6 x7 x11 x14 x15 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 w q ng k3 kI fp fL kq tm
      PINV Hng Hk Hk1 HfL Hkq Hfp Htm Hw.
    pre_facts. open_pinv PINV. cbv delta [frameA] in FR.
    do 12 step.
    rewrite (unsigned_lit ng) in FR by lia. rewrite (unsigned_lit tm) in FR by lia.
    change (bv_unsigned (Z_to_bv 64 1)) with 1%Z in FR.
    eapply C_22d1c.
    - split; [exact TXT|]. split; [cbv beta delta [frameP savesC app]; exact FR|].
      split; [unfold slow_path_double_need; exact ST|]. split; [exact VAL|].
      split; [exact PR1|]. split; [unfold P_FMIN_D; exact PR2|].
      split; [cbv delta [slow_path_double_W slow_path_double_need]; exact MU | exact WM].
    - unfold pnsok. repeat match goal with |- _ /\ _ => split end; try lia.
      all: try (destruct Hfp as [[A B]|[A B]]; [left; lia | right; lia]).
      all: match goal with |- ?g => idtac "LEFT" g end.
  Qed.
End BLK.
End P_spd_T0.


Module P_spd_TD.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbv beta delta [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  Hypothesis C_22ad4 : K_22ad4 c.
  Hypothesis C_22d30 : K_22d30 c.

  #[local] Ltac close_tinv TXT FR ST VAL PR1 PR2 MU WM :=
    split; [exact TXT|]; split; [cbv beta delta [frameP savesC app]; exact FR|];
    split; [unfold slow_path_double_need; exact ST|]; split; [exact VAL|];
    split; [exact PR1|]; split; [unfold P_FMIN_D; exact PR2|];
    split; [cbv delta [slow_path_double_W slow_path_double_need]; exact MU | exact WM].

  (* [comment removed for export] *)
  #[using="PRE C_22ad4 C_22d30"] Lemma spd_TD : K_22d1c c.
  Proof. LiaFast.lf_pins (fun (PRE C_22ad4 C_22d30 : LiaFast.U) => LiaFast.u0).
    unfold K_22ad4 in C_22ad4. unfold K_22d30 in C_22d30.
    unfold K_22d1c. intros m r j5 x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL tm TI PN.
    pre_facts. open_tinv TI. pose proof PN as PN'. open_pnsok PN'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Htm0.
    - cond_cleanup Htm0.
      assert (tm = 1%Z) as -> by lia.
      eapply C_22d30; [close_tinv TXT FR ST VAL PR1 PR2 MU WM | exact PN | right; split; reflexivity].
    - cond_cleanup Htm0.
      assert (tm = 0%Z) as -> by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      + cond_cleanup Hq.
        eapply C_22ad4; [close_tinv TXT FR ST VAL PR1 PR2 MU WM | exact PN | ].
        rewrite ?signed_lit in Hq by lia. lia.
      + cond_cleanup Hq.
        step. (* [comment removed for export] *)
        eapply C_22d30; [close_tinv TXT FR ST VAL PR1 PR2 MU WM | exact PN | left; reflexivity].
  Qed.
End BLK.
End P_spd_TD.


Module P_spd_PK.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbv beta delta [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[using="PRE"] Lemma spd_EPI : K_23350 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_23350. intros m cells F' fc' v' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 FRM' FRl SZ FRh ST VAL MU WM.
    pre_facts. cbv beta delta [savesC] in FRh. cbv beta delta [slow_path_double_W slow_path_double_need] in MU.
    unfold slow_path_double_need in ST.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z in FRh by lia.
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply stk_release in FRl; [ | exact ST | lia ]. rewrite SZ in FRl. clear ST.
    replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z in FRl by lia.
    eapply stk_release in FRh; [ | exact FRl | lia ]. cbn [cells_size csize Nat.add] in FRh. clear FRl.
    replace (bv_unsigned sp + -104 + Z.of_nat 104)%Z with (bv_unsigned sp) in FRh by lia.
    unfold slow_path_double_post. finish.
    all: try (unfold slow_path_double_need; exact FRh).
    all: try exact VAL.
  Qed.

  Hypothesis C_23350 : K_23350 c.

  (* [comment removed for export] *)
  #[using="PRE C_23350"] Lemma spd_PK : K_23318 c.
  Proof. LiaFast.lf_pins (fun (PRE C_23350 : LiaFast.U) => LiaFast.u0).
    unfold K_23350 in C_23350.
    unfold K_23318. intros m cells x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 TXT FRl SZ FRh ST VAL PR1 PR2 MU WM.
    pre_facts. unfold slow_path_double_need in ST. unfold P_FMIN_D in PR2.
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    cbv beta delta [savesC] in FRh.
    do 10 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 3 step. (* [comment removed for export] *)
    eapply C_23350. all: try eassumption. all: cbv beta delta [savesC]; assumption.
  Qed.
End BLK.
End P_spd_PK.


Module P_spd_CL.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbv beta delta [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  Fixpoint image_u64s (A : Z) (n : nat) : list Z :=
    match n with O => [] | S n' =>
      match image_bytes PSEGS A 8 with Some xs => bv_unsigned (le_bytes_to_word xs) | None => 0%Z end :: image_u64s (A + 8) n' end.
  (* [comment removed for export] *)
  Definition TBLD : list Z := Eval vm_compute in (image_u64s 0x15ba8 23).
  #[using="Type"] Lemma TBLD_ok : table_b PSEGS 0x15ba8 8 (fun v => le8 (Z_to_bv 64 v)) TBLD = true.
  Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

  Hypothesis C_22d30 : K_22d30 c.
  Hypothesis C_23350 : K_23350 c.

  (* [comment removed for export] *)
  #[using="PRE C_22d30 C_23350"] Lemma spd_CL : K_22ad4 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22d30 C_23350 : LiaFast.U) => LiaFast.u0).
    unfold K_22d30 in C_22d30. unfold K_23350 in C_23350.
    unfold K_22ad4. intros m r j5 x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL TI PN Hq.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hq22.
    { cond_cleanup Hq22.
      eapply C_22d30; [exact TI | exact PN | left; reflexivity]. }
    cond_cleanup Hq22. rewrite ?signed_lit in Hq22 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw53.
    { cond_cleanup Hw53.
      eapply C_22d30; [exact TI | exact PN | left; reflexivity]. }
    cond_cleanup Hw53.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (feq_s (fadd_s RNE (Z_to_bv 64 18446744069422972928) (Z_to_bv 64 18446744070479937536))
                   (fsub_s RNE (Z_to_bv 64 18446744070479937536) (Z_to_bv 64 18446744069422972928)))
      with true by (vm_compute; reflexivity).
    step. (* [comment removed for export] *)
    if_false.
    (* [comment removed for export] *)
    assert (TAIL : forall (Fq : bvmap 5 word) (fcq : bv 32) (xa1 xa3 xs4 : word), frm0 fcq ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) xa1 w xa3 x14 x15 x16 x17
                 x18 x19 xs4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fq (Z_to_bv 64 0x24a80) fcq None m (seg_rom PSEGS))).
    { intros Fq fcq xa1 xa3 xs4 FRMq.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsgn.
      - chunk_split FR 13%nat FRl FRh.
        eapply C_23350; [exact FRMq | exact FRl | reflexivity | | exact ST | exact VAL | exact MU | exact WM].
        replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh.
      - step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        chunk_split FR 13%nat FRl FRh.
        eapply C_23350; [exact FRMq | exact FRl | reflexivity | | exact ST | exact VAL | exact MU | exact WM].
        replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hneg.
    - cond_cleanup Hneg.
      assert (QS : (bv_signed q = bv_unsigned q - 2^64)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia.
      replace (Z_to_bv 64 (89000 - bv_unsigned (Z_to_bv 64 (bv_unsigned q * 2 ^ 3))))
        with (Z_to_bv 64 (89000 + 8 * (2^64 - bv_unsigned q)))
        by (rewrite unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      pose proof (table_read PSEGS _ _ _ _ m _ _ TBLD_ok PR1 ltac:(lia) ltac:(cbn; lia) (2^64 - bv_unsigned q)%Z ltac:(cbn; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      apply TAIL. assumption.
    - cond_cleanup Hneg.
      assert (QS : (bv_signed q = bv_unsigned q)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia.
      pose proof (table_read PSEGS _ _ _ _ m _ _ TBLD_ok PR1 ltac:(lia) ltac:(cbn; lia) (bv_unsigned q) ltac:(cbn; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply TAIL. assumption.
  Qed.
End BLK.
End P_spd_CL.


Module P_spd_ERR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbv beta delta [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  Fixpoint image_u64s (A : Z) (n : nat) : list Z :=
    match n with O => [] | S n' =>
      match image_bytes PSEGS A 8 with Some xs => bv_unsigned (le_bytes_to_word xs) | None => 0%Z end :: image_u64s (A + 8) n' end.
  Definition TBLD : list Z := Eval vm_compute in (image_u64s 0x15ba8 23).
  #[using="Type"] Lemma TBLD_ok : table_b PSEGS 0x15ba8 8 (fun v => le8 (Z_to_bv 64 v)) TBLD = true.
  Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

  Hypothesis memset_spec : memset_stmt.
  Hypothesis C_23350 : K_23350 c.

  (* [comment removed for export] *)
  #[using="PRE memset_spec C_23350"] Lemma spd_ERR : K_22a9c c.
  Proof. LiaFast.lf_pins (fun (PRE memset_spec C_23350 : LiaFast.U) => LiaFast.u0).
    unfold K_23350 in C_23350.
    unfold K_22a9c. intros junk m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. open_pinv PINV. cbv delta [frameA] in FR.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    assert (LJ : length junk = 584%nat) by exact (proj1 (proj1 (proj1 FR))).
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply (rw_cells_split_CB PSEGS m SP [] 32 _ _ [27; 5]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    chunk_split FR 1%nat FRz FR.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ FRz) as OLD. clear FRz.
    pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as U1.
    pose proof (unsigned_lit 27 ltac:(lia)) as U2.
    step. (* [comment removed for export] *)
    call memset_spec.
    { reflexivity. }
    { rewrite U1. exact OLD. }
    { rewrite U2, !firstn_length, LJ. reflexivity. }
    { rewrite U1. Z.div_mod_to_equations. lia. }
    rewrite -> ?U1, -> ?U2 in *.
    change (Z.to_nat 27) with 27%nat in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      lazymatch goal with M : bytes_at _ m' _ (repeat _ _), Wt : wr_at _ m' _ _ |- _ =>
        pose proof (rw_cells_of_u8arr PSEGS _ _ _ (conj M Wt)) as FRz; clear M Wt end end.
    rewrite repeat_length in FRz.
    chunk_join FRz FR FR2. rename FR2 into FR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    replace (feq_s (fadd_s RNE (Z_to_bv 64 18446744069422972928) (Z_to_bv 64 18446744070479937536))
                   (fsub_s RNE (Z_to_bv 64 18446744070479937536) (Z_to_bv 64 18446744069422972928)))
      with true by (vm_compute; reflexivity).
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_true.
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      let n := eval lazy in (length cs - 13)%nat in chunk_split FR n FRl FRh end.
    lazymatch goal with |- evt _ _ (MS _ _ _ ?fcq None _ _) =>
      lazymatch goal with FQ : frm0 fcq |- _ =>
      eapply C_23350; [exact FQ | exact FRl | reflexivity | | exact ST | exact VAL | exact MU | exact WM] end end.
    replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia. exact FRh.
  Qed.
End BLK.
End P_spd_ERR.


Module P_spd_CF1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_22ef4 : K_22ef4 c.
  Hypothesis C_23318 : K_23318 c.

  (* [comment removed for export] *)
  #[local] Ltac exit18 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -688) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 413152 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 13%nat FRl FRh;
    eapply C_23318; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM];
    replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.

  (* [comment removed for export] *)
  #[using="PRE C_22ef4 C_23318"] Lemma spd_CF1 : K_22d30 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22ef4 C_23318 : LiaFast.U) => LiaFast.u0).
    unfold K_22ef4 in C_22ef4. unfold K_23318 in C_23318.
    unfold K_22d30. intros m r j5 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm ng k3 kI fp fL tm tf TI PN Htf.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw0.
    { cond_cleanup Hw0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Htf1. { cond_cleanup Htf1. exfalso. lia. }
      step. (* [comment removed for export] *)
      exit18. }
    cond_cleanup Hw0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqlo.
    { cond_cleanup Hqlo.
      step. (* [comment removed for export] *)
      if_cases Htf0.
      - exit18.
      - cond_cleanup Htf0. assert (Htm1 : tm = 1%Z) by lia. subst tm.
        eapply C_22ef4; [exact TI | exact PN | intros _; split; reflexivity | intros HH; exfalso; lia]. }
    cond_cleanup Hqlo.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqhi.
    2:{ cond_cleanup Hqhi.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Htf1.
      - cond_cleanup Htf1. assert (Htm1 : tm = 1%Z) by lia. subst tm.
        eapply C_22ef4; [exact TI | exact PN | intros HH; exfalso; lia | intros _; split; reflexivity].
      - step. (* [comment removed for export] *)
        exit18. }
    cond_cleanup Hqhi.
    (* [comment removed for export] *)
    assert (XF4 : tm = 1%Z -> forall (v5 v6 v7 v11 v13 v14 v15 v16 v17 am ap : word),
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 (Z_to_bv 64 ng) v11 w v13 v14 v15 v16 v17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24de4) fc None m (seg_rom PSEGS))).
    { intros Htm1; intros. subst tm. eapply C_22ef4; [exact TI | exact PN | intros HH; exfalso; lia | intros HH; exfalso; lia]. }
    step. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (idx16_cf q) by lia. gen_big.
    pose proof (table_read PSEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * (bv_signed q + 342))%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    pose proof (table_read PSEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * (bv_signed q + 342) + 1)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    do 13 gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J30 : forall v5 v6 v7 v13 v14 v15 v16 v17 : word,
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 (Z_to_bv 64 ng) (Z_to_bv 64 tf) w v13 v14 v15 v16 v17
                 (Z_to_bv 64 0) (Z_to_bv 64 0) q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24d20) fc None m (seg_rom PSEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (J8c : forall u5 u6 u7 u13 u14 u15 u16 u17 : word,
        evt PSEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp u5 u6 u7 a2 x9 (Z_to_bv 64 ng) (Z_to_bv 64 tf) w u13 u14 u15 u16 u17
                   (Z_to_bv 64 0) (Z_to_bv 64 0) q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x24d7c) fc None m (seg_rom PSEGS))).
      { intros.
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hinf.
        - clear Hinf.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htf1.
          + cond_cleanup Htf1. apply XF4. lia.
          + step. (* [comment removed for export] *) exit18.
        - clear Hinf.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htf1.
          + cond_cleanup Htf1. apply XF4. lia.
          + step. (* [comment removed for export] *) exit18. }
      step. (* [comment removed for export] *)
      if_cases Hpos.
      - clear Hpos. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          gstep. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htf1.
          * cond_cleanup Htf1. apply XF4. lia.
          * step. (* [comment removed for export] *) exit18.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Htf0.
          * exit18.
          * cond_cleanup Htf0. apply XF4. lia.
      - clear Hpos.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb1. { clear Hb1. apply J8c. }
        clear Hb1.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb2. { clear Hb2. apply J8c. }
        clear Hb2.
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb3. { clear Hb3. apply J8c. }
        clear Hb3.
        gstep. (* [comment removed for export] *)
        apply J8c. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J30. }
    clear Hlow.
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J30.
  Qed.
End BLK.
End P_spd_CF1.


Module P_spd_CF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_230e8 : K_230e8 c.

  (* [comment removed for export] *)
  #[using="PRE C_230e8"] Lemma spd_CF2 : K_22ef4 c.
  Proof. LiaFast.lf_pins (fun (PRE C_230e8 : LiaFast.U) => LiaFast.u0).
    unfold K_230e8 in C_230e8.
    unfold K_22ef4. intros m r j5 x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ap ng k3 kI fp fL TI PN Hlo Hhi.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw1. { cond_cleanup Hw1. exfalso. Z.div_mod_to_equations. lia. }
    clear Hw1.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqlo.
    { cond_cleanup Hqlo. destruct (Hlo ltac:(lia)) as [Ham Hap]. subst am ap.
      eapply C_230e8; [exact TI | exact PN | intros HH; exfalso; destruct HH as [HH|HH]; apply HH; reflexivity]. }
    cond_cleanup Hqlo.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hqhi.
    2:{ cond_cleanup Hqhi. destruct (Hhi ltac:(lia)) as [Ham Hap]. subst am ap.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply C_230e8; [exact TI | exact PN | intros HH; exfalso; destruct HH as [HH|HH]; apply HH; reflexivity]. }
    cond_cleanup Hqhi. clear Hlo Hhi.
    (* [comment removed for export] *)
    assert (XE8 : forall (v5 v6 v7 v11 v15 v16 v17 bp bm : word),
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 (Z_to_bv 64 ng) v11 w bp bm v15 v16 v17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24fd8) fc None m (seg_rom PSEGS))).
    { intros. eapply C_230e8; [exact TI | exact PN | intros _; lia]. }
    step. (* [comment removed for export] *)
    do 3 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (idx16_cf q) by lia. gen_big.
    pose proof (table_read PSEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * (bv_signed q + 342))%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    pose proof (table_read PSEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * (bv_signed q + 342) + 1)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    do 13 gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 3 step. (* [comment removed for export] *)
    do 4 gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 11 gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (Jf0 : forall v5 v6 v7 v11 v13 v14 v15 v16 v17 : word,
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 (Z_to_bv 64 ng) v11 w v13 v14 v15 v16 v17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24ee0) fc None m (seg_rom PSEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 6 gstep. (* [comment removed for export] *)
      assert (J4c : forall u5 u6 u7 u11 u13 u14 u15 u16 u17 : word,
        evt PSEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp u5 u6 u7 a2 x9 (Z_to_bv 64 ng) u11 w u13 u14 u15 u16 u17
                   am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x24f3c) fc None m (seg_rom PSEGS))).
      { intros.
        do 10 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hinf.
        - clear Hinf.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          apply XE8.
        - clear Hinf.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          apply XE8. }
      step. (* [comment removed for export] *)
      if_cases Hpos.
      - clear Hpos.
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          do 6 gstep. (* [comment removed for export] *)
          apply XE8.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          apply XE8.
      - clear Hpos.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb1. { clear Hb1. apply J4c. }
        clear Hb1.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb2. { clear Hb2. apply J4c. }
        clear Hb2.
        do 5 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb3. { clear Hb3. apply J4c. }
        clear Hb3.
        gstep. (* [comment removed for export] *)
        apply J4c. }
    step. (* [comment removed for export] *)
    if_cases Hlow. { clear Hlow. apply Jf0. }
    clear Hlow.
    step. (* [comment removed for export] *)
    do 4 gstep. (* [comment removed for export] *)
    apply Jf0.
  Qed.
End BLK.
End P_spd_CF2.


Module P_spd_CE.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    end.
  #[local] Ltac gstep := step; gen_big.

  Hypothesis C_23318 : K_23318 c.
  Hypothesis C_23210 : K_23210 c.

  (* [comment removed for export] *)
  #[local] Ltac exit18 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with FR : rw_cells _ m (bv_unsigned sp + -688) _, TXT : bytes_at _ m P _, ST : stk _ m _ _,
                        VAL : rw_cells _ m V _, PR1 : pristine m 65536 139264, PR2 : pristine m 413152 _,
                        MU : munch _ _ m, WM : wmono _ _ m |- _ =>
    let FRl := fresh "FRl" in let FRh := fresh "FRh" in
    chunk_split FR 13%nat FRl FRh;
    eapply C_23318; [exact TXT | exact FRl | reflexivity | | exact ST | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM];
    replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia; exact FRh end end.


  (* [comment removed for export] *)
  #[using="PRE C_23318 C_23210"] Lemma spd_CE : K_230e8 c.
  Proof. LiaFast.lf_pins (fun (PRE C_23318 C_23210 : LiaFast.U) => LiaFast.u0).
    unfold K_23318 in C_23318. unfold K_23210 in C_23210.
    unfold K_230e8. intros m r j5 x1 x5 x6 x7 x9 x11 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ap bm bp ng k3 kI fp fL TI PN Hrng.
    pre_facts. pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    (* [comment removed for export] *)
    assert (CEX : forall x13 x14 : word, (-342 <= bv_signed q <= 308)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w x13 x14 x15 x16 x17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24fe0) fc None m (seg_rom PSEGS))).
    { intros y13 y14 Hq. clear Hrng.
      step. (* [comment removed for export] *)
      if_cases Hw0. { cond_cleanup Hw0. exfalso. lia. }
      clear Hw0.
      step. (* [comment removed for export] *)
      do 4 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      remember (Z_to_bv 64 (bv_unsigned q ≪ 1)) as A1 eqn:HA1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 4 step. (* [comment removed for export] *)
      do 10 gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (idx16_ce q A1 HA1) by lia.
      pose proof (table_read PSEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                    (2 * (bv_signed q + 342))%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
      pose proof (table_read PSEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                    (2 * (bv_signed q + 342) + 1)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
      step. (* [comment removed for export] *)
      do 9 gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (bv_unsigned ?x ≫ 56))] =>
        pose proof (bv_unsigned_in_range 64 x) as Rlz; unfold bv_modulus in Rlz;
        assert (Hlz : (0 <= Z.shiftr (bv_unsigned x) 56 < 256)%Z)
          by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia);
        remember (Z_to_bv 64 (bv_unsigned x ≫ 56)) as LZ eqn:HLZ end.
      assert (Ulz : (0 <= bv_unsigned LZ < 256)%Z) by (subst LZ; rewrite unsigned_lit by lia; exact Hlz).
      clear HLZ Hlz Rlz.
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (Jcc : forall v5 v6 v7 v11 v14 v15 v16 v17 : word,
        evt PSEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 (Z_to_bv 64 ng) v11 w LZ v14 v15 v16 v17
                   am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x250bc) fc None m (seg_rom PSEGS))).
      { intros.
        step. (* [comment removed for export] *)
        pose proof (bv_unsigned_in_range 64 v16) as R16. unfold bv_modulus in R16.
        assert (Hub : (0 <= bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned v16) 63)) <= 1)%Z).
        { rewrite Z.shiftr_div_pow2 by lia. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
          Z.div_mod_to_equations; lia. }
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (ce_A_range q ltac:(lia)) as HA.
        lazymatch goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 (Z.shiftr ?t 16)))] =>
          remember (bv_swrap 32 (Z.shiftr t 16)) as A eqn:HAe end.
        clear HAe.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (ce_X_eq A (bv_unsigned LZ) _ HA Ulz Hub).
        lazymatch goal with |- context [Some (Z_to_bv 64 (A - ?l - 31693 + ?u)%Z)] =>
          remember (A - l - 31693 + u)%Z as X eqn:HX end.
        assert (RX : (-33100 <= X <= -30600)%Z) by lia. clear HX Hub.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hneg.
        - clear Hneg.
          eapply C_23210; [exact TI | exact PN | lia | apply zx32_shifts | exact RX].
        - clear Hneg.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          exit18. }
      step. (* [comment removed for export] *)
      if_cases Hlow. { clear Hlow. apply Jcc. }
      clear Hlow.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (idx16_ce' q A1 HA1) by lia.
      step. (* [comment removed for export] *)
      do 5 gstep. (* [comment removed for export] *)
      apply Jcc. }
    step. (* [comment removed for export] *)
    if_cases Hm.
    - cond_cleanup Hm. apply CEX. apply Hrng. left. intros E; apply Hm. rewrite E. reflexivity.
    - cond_cleanup Hm.
      step. (* [comment removed for export] *)
      if_cases Hp.
      + exit18.
      + cond_cleanup Hp. apply CEX. apply Hrng. right. intros E; apply Hp. rewrite E. reflexivity.
  Qed.
End BLK.
End P_spd_CE.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_DC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_B OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_C OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_D OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_E OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_T0 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_TD OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_PK OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_CL OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_ERR OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_CF1 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_CF2 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double.P_spd_CE OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Main.
  Hypothesis memset_spec : memset_stmt.
  Hypothesis parse_mantissa_spec : parse_mantissa_stmt.
  Hypothesis positive_digit_comp_d_spec : positive_digit_comp_d_stmt.
  Hypothesis negative_digit_comp_d_spec : negative_digit_comp_d_stmt.

  #[using="memset_spec parse_mantissa_spec positive_digit_comp_d_spec negative_digit_comp_d_spec"] Lemma slow_path_double_spec : slow_path_double_stmt.
  Proof. LiaFast.lf_pins (fun (memset_spec parse_mantissa_spec positive_digit_comp_d_spec negative_digit_comp_d_spec : LiaFast.U) => LiaFast.u0).
    unfold slow_path_double_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v.
    intros TXT LEN RANGE ENW A5 VAL VAL8 ST AL LO P0 V0 VLO PR1 PR2 FRM SEP1 SEP2 SEP3.
    set (c := SPF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v).
    assert (PRE : spd_pre c).
    { constructor; cbn; try assumption; try lia. }
    pose proof (spd_EPI c PRE) as EPI.
    pose proof (spd_PK c PRE EPI) as PK.
    pose proof (spd_ERR c PRE memset_spec EPI) as ERR.
    pose proof (spd_DC c PRE memset_spec parse_mantissa_spec positive_digit_comp_d_spec negative_digit_comp_d_spec PK) as DC.
    pose proof (spd_CE c PRE PK DC) as CE.
    pose proof (spd_CF2 c PRE CE) as CF2.
    pose proof (spd_CF1 c PRE CF2 PK) as CF1.
    pose proof (spd_CL c PRE CF1 EPI) as CL.
    pose proof (spd_TD c PRE CL CF1) as TD.
    pose proof (spd_T0 c PRE TD) as T0.
    pose proof (spd_E c PRE T0) as BE.
    pose proof (spd_D c PRE BE ERR) as BD.
    pose proof (spd_C c PRE BD ERR) as BC.
    pose proof (spd_B c PRE BC) as BB.
    exact (spd_A c PRE ERR BB).
  Qed.
End Main.

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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_from_chars_double_stmt.

Module P_parse_infnan_d_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition parse_infnan_d_entry : Z := 0x23d80.

(* [comment removed for export] *)
Definition parse_infnan_d_W (v : word) : list ivl := [(bv_unsigned v, bv_unsigned v + 8)]%Z.

Definition parse_infnan_d_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (v : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (v' : word)
                    (F' : bvmap 5 word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (parse_infnan_d_W v) m m'
    /\ wmono PSEGS m m'
    /\ rw_cells PSEGS m' (bv_unsigned v) [C8 v'].

Definition parse_infnan_d_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (vold : word),
    (* [comment removed for export] *)
    bytes_at PSEGS m (bv_unsigned a0) bs ->
    (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z ->
    (bv_unsigned a0 < bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    rw_cells PSEGS m (bv_unsigned a2) [C8 vold] ->
    (* [comment removed for export] *)
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z ->
    (bv_unsigned a2 + 8 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z ->
    evt PSEGS (parse_infnan_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc a2 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x23d80) fc None m (seg_rom PSEGS)).
End P_parse_infnan_d_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_slow_path_double_stmt P_fcd_common.

Module P_fcd_commonT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export P_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CTX.
  Variable c : spf_ctx.
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation sp := (r_sp c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).

  (* [comment removed for export] *)
  Definition K_21b4c : Prop :=
    forall junk m (x1 x5 x6 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (q : word),
      pinv c junk m -> (-342 <= bv_signed q <= 308)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 q x8 x9 x10 x11 a2 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x23a4c) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_21d8c : Prop :=
    forall junk m (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      pinv c junk m ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x23c8c) fc None m (seg_rom PSEGS)).
End CTX.
End P_fcd_commonT.


Module P_fcd_A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac P_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_212dc : K_212dc c.
  Hypothesis C_2151c : K_2151c c.
  Hypothesis C_21a44 : K_21a44 c.

  (* [comment removed for export] *)
  #[using="PRE C_212dc C_21a44"] Lemma fcd_A :
    evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x22ffc) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_212dc C_21a44 : LiaFast.U) => LiaFast.u0).
    unfold K_212dc in C_212dc. unfold K_21a44 in C_21a44.
    pre_facts.
    pose proof (pre_ST c PRE) as ST. unfold from_chars_double_need in ST.
    pose proof (pre_TXT c PRE) as TXT. pose proof (pre_VAL c PRE) as VAL.
    pose proof (pre_PR1 c PRE) as PR1. pose proof (pre_PR2 c PRE) as PR2. unfold P_FMIN in PR2.
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    pose proof (munch_refl W m0) as MU. cbv delta [from_chars_double_W from_chars_double_need] in MU.
    pose proof (wmono_refl PSEGS m0) as WM.
    carve_frame 112%nat ST.
    do 14 step.   (* [comment removed for export] *)
    assert (PINV : pinv c (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64
                   (firstn 72 (firstn 80 (firstn 88 (firstn 96 (firstn 104 junk))))))))))))) m).
    { split; [exact TXT|]. split; [exact FR|]. split; [unfold from_chars_double_need; exact ST|]. split; [exact VAL|].
      split; [exact PR1|]. split; [unfold P_FMIN; exact PR2|].
      split; [cbv delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]. }
    step. (* [comment removed for export] *) rewrite F256.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_true.
    step. (* [comment removed for export] *)
    if_cases Hemp.
    { (* [comment removed for export] *)
      cond_cleanup Hemp.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 13 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      unfold from_chars_double_post. finish. all: try exact VAL. all: try exact FRM.
      all: match goal with |- ?g => idtac "REMAIN" g end. }
    cond_cleanup Hemp.
    rd 0%Z. (* [comment removed for export] *)
    pose proof (tx_range bs 0) as Rb0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite F32.
    step. (* [comment removed for export] *) if_true.
    step. (* [comment removed for export] *)
    if_cases Hminus.
    - (* [comment removed for export] *)
      clear Hminus.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hend.
      { cond_cleanup Hend. goto (eapply C_21a44); [exact PINV | lia]. }
      cond_cleanup Hend.
      rd 1%Z. (* [comment removed for export] *)
      pose proof (tx_range bs 1) as Rb1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hdig.
      + clear Hdig. goto (eapply C_212dc with (k1 := 1%Z)); [exact PINV | lia | lia].
      + clear Hdig. step. (* [comment removed for export] *) dp46.
        step. (* [comment removed for export] *)
        if_cases Hdp.
        * clear Hdp. goto (eapply C_21a44); [exact PINV | lia].
        * clear Hdp. goto (eapply C_212dc with (k1 := 1%Z)); [exact PINV | lia | lia].
    - clear Hminus.
      step. (* [comment removed for export] *) rewrite F128.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_true.
      goto (eapply C_212dc with (k1 := 0%Z)); [exact PINV | lia | lia].
  Qed.
End BLK.
End P_fcd_A.


Module P_fcd_A2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac P_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_2151c : K_2151c c.

  (* [comment removed for export] *)
  #[using="PRE C_2151c"] Lemma fcd_A2 : K_212dc c.
  Proof. LiaFast.lf_pins (fun (PRE C_2151c : LiaFast.U) => LiaFast.u0).
    unfold K_212dc. unfold K_2151c in C_2151c.
    intros junk m x7 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 k1 PINV Hk1 Hk1L.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (LOOP : forall (n : nat) (k : Z) (x17 x29 x30 : word),
      (Z.to_nat (L - k) <= n)%nat -> (k1 <= k < L)%Z ->
      evt PSEGS POST
        (MS (mkR ra (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 10) x8 x9 (Z_to_bv 64 (P + k)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 9) x29 x30 x31)
            F (Z_to_bv 64 0x232a0) fc None m (seg_rom PSEGS))).
    { induction n as [|n IH]; intros k y17 y29 y30 Hn Hk. { exfalso. lia. }
      rd k. (* [comment removed for export] *) pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hd.
      { clear Hd. goto (eapply C_2151c with (k1 := k1) (kI := k)); [exact PINV0 | lia | lia | lia]. }
      clear Hd.
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *) gen_reg (17:reg).
      step. (* [comment removed for export] *)
      if_cases Hm.
      - cond_cleanup Hm. goto (eapply (IH (k + 1)%Z)); lia.
      - cond_cleanup Hm. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply C_2151c with (k1 := k1) (kI := L)); [exact PINV0 | lia | lia | lia]. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He.
    { cond_cleanup He. exfalso. lia. }
    cond_cleanup He.
    pose proof (tx_range bs k1) as R0. rewrite (txb_tx bs k1).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd0.
    { clear Hd0. goto (eapply C_2151c with (k1 := k1) (kI := k1)); [exact PINV0 | lia | lia | lia]. }
    clear Hd0.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He1.
    { cond_cleanup He1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 1)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He1.
    rd (k1 + 1)%Z. pose proof (tx_range bs (k1 + 1)) as R1.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd1.
    { clear Hd1. step. step. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 1)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd1.
    step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (17:reg).
    step. (* [comment removed for export] *)
    if_cases He2.
    { cond_cleanup He2. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 2)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He2.
    (* [comment removed for export] *)
    rd (k1 + 2)%Z. pose proof (tx_range bs (k1 + 2)) as R2.
    step. step. step. (* [comment removed for export] *)
    if_cases Hd2.
    { clear Hd2. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 2)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd2.
    step. gstep. gstep. step. (* [comment removed for export] *) gstep. gen_reg (17:reg).
    step. (* [comment removed for export] *)
    if_cases He3.
    { cond_cleanup He3. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 3)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He3.
    (* [comment removed for export] *)
    rd (k1 + 3)%Z. pose proof (tx_range bs (k1 + 3)) as R3.
    step. step. step.
    if_cases Hd3.
    { clear Hd3. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 3)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd3.
    step. gstep. gstep. step. (* [comment removed for export] *) gstep. gen_reg (17:reg).
    step. (* [comment removed for export] *)
    if_cases He4.
    { cond_cleanup He4. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 4)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He4.
    (* [comment removed for export] *)
    rd (k1 + 4)%Z. pose proof (tx_range bs (k1 + 4)) as R4.
    step. step. step.
    if_cases Hd4.
    { clear Hd4. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 4)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd4.
    step. (* [comment removed for export] *) gstep. gstep. step. (* [comment removed for export] *) gstep. gen_reg (17:reg).
    step. (* [comment removed for export] *)
    if_cases He5.
    { cond_cleanup He5. goto (eapply C_2151c with (k1 := k1) (kI := (k1 + 5)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He5.
    step. (* [comment removed for export] *)
    goto (eapply (LOOP (Z.to_nat (L - (k1 + 5))) (k1 + 5)%Z)); lia.
  Qed.
End BLK.
End P_fcd_A2.


Module P_fcd_B.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac P_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_21724 : K_21724 c.
  Hypothesis C_21a44 : K_21a44 c.

  (* [comment removed for export] *)
  #[using="PRE C_21724 C_21a44"] Lemma fcd_B : K_2151c c.
  Proof. LiaFast.lf_pins (fun (PRE C_21724 C_21a44 : LiaFast.U) => LiaFast.u0).
    unfold K_2151c. unfold K_21724 in C_21724. unfold K_21a44 in C_21a44.
    intros junk m x7 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 k1 kI PINV HL1 Hk1 HkI.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (J718 : forall (kp : Z) (x1 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
      (kI + 1 <= kp <= L)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 (P + kI + 1)) x8 x9 (Z_to_bv 64 (P + kp)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (kI - k1)) x29 x30 x31)
            F (Z_to_bv 64 0x23618) fc None m (seg_rom PSEGS))).
    { intros kp y1 y8 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 Hkp.
      step. (* [comment removed for export] *) rewrite word_sub_lit2.
      replace (P + kI + 1 - (P + kp))%Z with (kI + 1 - kp)%Z by lia.
      step. (* [comment removed for export] *) rewrite word_sub_lit2.
      replace (kI - k1 - (kI + 1 - kp))%Z with (kp - k1 - 1)%Z by lia.
      step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz. goto (eapply C_21a44); [exact PINV0 | lia].
      - cond_cleanup Hz. goto (eapply C_21724 with (k1 := k1) (kp := kp) (ex := (kI + 1 - kp)%Z) (dc := (kp - k1 - 1)%Z));
          [exact PINV0 | lia | lia | lia | lia | lia]. }
    (* [comment removed for export] *)
    assert (JE8 : forall (q : Z) (x1 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
      (kI + 1 <= q <= L)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 (P + kI + 1)) x8 x9 (Z_to_bv 64 (P + q)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (kI - k1)) x29 x30 x31)
            F (Z_to_bv 64 0x235e8) fc None m (seg_rom PSEGS))).
    { intros q y1 y8 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 Hq.
      assert (LOOP : forall (n : nat) (q' : Z) (z17 z31 : word), (Z.to_nat (L - q') <= n)%nat -> (kI + 1 <= q' < L)%Z ->
        evt PSEGS POST
          (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 (P + kI + 1)) y8 y9 (Z_to_bv 64 (P + q')) a1 a2 a3 a4
                   (txb bs 0) a0 z17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 (kI - k1)) (Z_to_bv 64 9) (Z_to_bv 64 10) z31)
              F (Z_to_bv 64 0x235f4) fc None m (seg_rom PSEGS))).
      { induction n as [|n IH]; intros q' z17 z31 Hn Hq'. { exfalso. lia. }
        rd q'. (* [comment removed for export] *) pose proof (tx_range bs q') as Rq.
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hd.
        { clear Hd. goto (eapply (J718 q')); lia. }
        clear Hd.
        step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (17:reg).
        step. (* [comment removed for export] *)
        if_cases Hm.
        - cond_cleanup Hm. goto (eapply (IH (q' + 1)%Z)); lia.
        - cond_cleanup Hm. step. (* [comment removed for export] *) goto (eapply (J718 L)); lia. }
      step. (* [comment removed for export] *)
      if_cases He.
      - cond_cleanup He. goto (eapply (J718 q)); lia.
      - cond_cleanup He. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply (LOOP (Z.to_nat (L - q)) q)); lia. }
    (* [comment removed for export] *)
    assert (J67c : forall (q : Z) (x1 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
      (kI + 1 <= q)%Z -> (q + 4 <= L)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 (P + kI + 1)) x8 x9 (Z_to_bv 64 (P + q)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (kI - k1)) x29 x30 x31)
            F (Z_to_bv 64 0x2357c) fc None m (seg_rom PSEGS))).
    { intros q y1 y8 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 Hq1 Hq2.
      do 4 step. (* [comment removed for export] *) do 2 gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc.
      - clear Hc. goto (eapply (JE8 q)); lia.
      - clear Hc. step. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. gstep. gstep. (* [comment removed for export] *)
        step. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (17:reg).
        step. (* [comment removed for export] *)
        goto (eapply (JE8 (q + 4)%Z)); lia. }
    (* [comment removed for export] *)
    assert (J64c : forall (q R : Z) (x1 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word),
      (kI + 1 <= q <= L)%Z -> (R = L - q)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 (P + kI + 1)) x8 x9 (Z_to_bv 64 (P + q)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (kI - k1)) (Z_to_bv 64 R) x30 x31)
            F (Z_to_bv 64 0x2354c) fc None m (seg_rom PSEGS))).
    { intros q R y1 y8 y9 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y30 y31 Hq HR.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hs.
      - clear Hs. goto (eapply (JE8 q)); lia.
      - cond_cleanup Hs. rewrite ?signed_lit in Hs by lia.
        rd (q + 1)%Z. rd q. rd (q + 2)%Z. rd (q + 3)%Z.
        do 6 gstep. (* [comment removed for export] *)
        goto (eapply (J67c q)); lia. }
    (* [comment removed for export] *)
    assert (SW : forall (n : nat) (q R : Z) (x1 x17 x23 x24 x25 x26 x27 : word),
      (Z.to_nat (L - q) <= n)%nat -> (kI + 1 <= q)%Z -> (R = L - q)%Z -> (8 <= R)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 (P + kI + 1))
                 (Z_to_bv 64 5063812098665367110) (Z_to_bv 64 4294967296000100) (Z_to_bv 64 (P + q)) a1 a2 a3 a4 (txb bs 0) a0 x17
                 (Z_to_bv 64 42949672960001) (Z_to_bv 64 1095216660735) (Z_to_bv 64 100000000)
                 (Z_to_bv 64 10) (Z_to_bv 64 7) x23 x24 x25 x26 x27
                 (Z_to_bv 64 (kI - k1)) (Z_to_bv 64 R) (Z_to_bv 64 14974415777481871312) (Z_to_bv 64 9259542123273814144))
            F (Z_to_bv 64 0x23490) fc None m (seg_rom PSEGS))).
    { induction n as [|n IH]; intros q R y1 y17 y23 y24 y25 y26 y27 Hn Hq HR H8. { exfalso. lia. }
      rd (q + 1)%Z. rd (q + 2)%Z. rd (q + 3)%Z. rd q.
      do 4 gstep. (* [comment removed for export] *)
      rd (q + 4)%Z. rd (q + 5)%Z.
      gstep. (* [comment removed for export] *)
      rd (q + 6)%Z. rd (q + 7)%Z.
      do 12 gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc.
      { clear Hc. goto (eapply (J67c q)); lia. }
      clear Hc.
      do 3 gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 9 gstep. (* [comment removed for export] *) gen_reg (17:reg).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      - cond_cleanup Hb. rewrite ?signed_lit in Hb by lia.
        goto (eapply (IH (q + 8)%Z)); lia.
      - cond_cleanup Hb. rewrite ?signed_lit in Hb by lia. step. (* [comment removed for export] *)
        goto (eapply (J64c (q + 8)%Z (R + -8)%Z)); lia. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite word_sub_lit2. replace (P + kI - (P + k1))%Z with (kI - k1)%Z by lia.
    step. (* [comment removed for export] *)
    if_cases He.
    { cond_cleanup He. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz. goto (eapply C_21724 with (k1 := k1) (kp := kI) (ex := 0%Z) (dc := (kI - k1)%Z)); [exact PINV0 | lia | lia | lia | lia | lia].
      - cond_cleanup Hz. step. (* [comment removed for export] *) goto (eapply C_21a44); [exact PINV0 | lia]. }
    cond_cleanup He.
    rd kI. pose proof (tx_range bs kI) as RkI.
    step. (* [comment removed for export] *) dp46.
    step. (* [comment removed for export] *)
    if_cases Hdp.
    { clear Hdp. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz. goto (eapply C_21724 with (k1 := k1) (kp := kI) (ex := 0%Z) (dc := (kI - k1)%Z)); [exact PINV0 | lia | lia | lia | lia | lia].
      - cond_cleanup Hz. step. (* [comment removed for export] *) goto (eapply C_21a44); [exact PINV0 | lia]. }
    clear Hdp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit.
    lazymatch goal with |- context [Some (Z_to_bv 64 (E - ?u))] => replace (E - u)%Z with (L - (kI + 1))%Z by lia end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs8.
    - clear Hs8. step. (* [comment removed for export] *) goto (eapply (J64c (kI + 1)%Z)); lia.
    - cond_cleanup Hs8. rewrite ?signed_lit in Hs8 by lia.
      do 19 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (eapply (SW (Z.to_nat (L - (kI + 1))) (kI + 1)%Z (L - (kI + 1))%Z)); lia.
  Qed.
End BLK.
End P_fcd_B.


Module P_fcd_C.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac P_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_21a80 : K_21a80 c.
  Hypothesis C_21a44 : K_21a44 c.

  (* [comment removed for export] *)
  #[using="PRE C_21a80 C_21a44"] Lemma fcd_C : K_21724 c.
  Proof. LiaFast.lf_pins (fun (PRE C_21a80 C_21a44 : LiaFast.U) => LiaFast.u0).
    unfold K_21724. unfold K_21a80 in C_21a80. unfold K_21a44 in C_21a44.
    intros junk m x1 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 k1 kp ex dc PINV HL1 Hk1 Hkp Hex Hdc.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (JC8 : forall (y7 y10 y29 y30 y31 : word),
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) y7 x8 x9 y10 a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 dc) y29 y30 y31)
            F (Z_to_bv 64 0x236c8) fc None m (seg_rom PSEGS))).
    { intros. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hs.
      - clear Hs. goto (eapply C_21a44); [exact PINV0 | lia].
      - clear Hs. step. (* [comment removed for export] *) goto (eapply C_21a80 with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia]. }
    (* [comment removed for export] *)
    assert (J74 : forall (en sg : Z) (y8 y9 y10 y18 y29 : word), (0 <= en < 2^32)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 ex) y8 y9 y10 a1 a2 a3 a4
                 (txb bs 0) a0 x17 y18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 dc) y29 (Z_to_bv 64 sg) (Z_to_bv 64 en))
            F (Z_to_bv 64 0x23974) fc None m (seg_rom PSEGS))).
    { intros en sg y8 y9 y10 y18 y29 Hen.
      step. (* [comment removed for export] *)
      if_cases Hsg.
      - clear Hsg. step. (* [comment removed for export] *)
        goto (eapply C_21a80 with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia].
      - clear Hsg. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply C_21a80 with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia]. }
    (* [comment removed for export] *)
    assert (LOOP : forall (n : nat) (k en sg : Z) (y18 : word),
      (Z.to_nat (L - k) <= n)%nat -> (kp <= k < L)%Z -> (0 <= en < 2^32)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 ex) (Z_to_bv 64 9) (Z_to_bv 64 268435456)
                 (Z_to_bv 64 10) a1 a2 a3 a4
                 (txb bs 0) a0 x17 y18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 dc) (Z_to_bv 64 (P + k)) (Z_to_bv 64 sg) (Z_to_bv 64 en))
            F (Z_to_bv 64 0x23710) fc None m (seg_rom PSEGS))).
    { induction n as [|n IH]; intros k en sg y18 Hn Hk Hen. { exfalso. lia. }
      rd k. (* [comment removed for export] *) pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (Z.land ?u 255))] =>
        pose proof (land_range_r u 255 ltac:(lia)) as Hd; set (dg := Z.land u 255) in * end.
      step. (* [comment removed for export] *)
      if_cases Hnd.
      { clear Hnd. step. (* [comment removed for export] *) goto (eapply (J74 en sg)); lia. }
      cond_cleanup Hnd.
      step. (* [comment removed for export] *)
      if_cases Hbig.
      - cond_cleanup Hbig. rewrite ?signed_lit in Hbig by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hm.
        + cond_cleanup Hm. goto (eapply (IH (k + 1)%Z en sg)); lia.
        + cond_cleanup Hm. step. (* [comment removed for export] *) step. (* [comment removed for export] *) goto (eapply (J74 en sg)); lia.
      - cond_cleanup Hbig. rewrite ?signed_lit in Hbig by lia.
        step. (* [comment removed for export] *) rewrite ?unsigned_lit by lia.
        step. (* [comment removed for export] *) rewrite ?unsigned_lit by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hm.
        + cond_cleanup Hm. goto (eapply (IH (k + 1)%Z (en * 10 + dg)%Z sg)); lia.
        + cond_cleanup Hm. step. (* [comment removed for export] *) step. (* [comment removed for export] *) goto (eapply (J74 (en * 10 + dg)%Z sg)); lia. }
    (* [comment removed for export] *)
    assert (JF0 : forall (k sg : Z) (y31 : word), (kp <= k <= L)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 ex) x8 x9 (Z_to_bv 64 (P + kp)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 dc) (Z_to_bv 64 (P + k)) (Z_to_bv 64 sg) y31)
            F (Z_to_bv 64 0x236f0) fc None m (seg_rom PSEGS))).
    { intros k sg y31 Hk.
      step. (* [comment removed for export] *)
      if_cases He.
      { cond_cleanup He. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        if_cases Hf.
        - clear Hf. goto (eapply C_21a44); [exact PINV0 | lia].
        - clear Hf. step. (* [comment removed for export] *) goto (eapply C_21a80 with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia]. }
      cond_cleanup He.
      rd k. pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnd.
      { clear Hnd. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        if_cases Hf.
        - clear Hf. goto (eapply C_21a44); [exact PINV0 | lia].
        - clear Hf. step. (* [comment removed for export] *) goto (eapply C_21a80 with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia]. }
      clear Hnd.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      goto (eapply (LOOP (Z.to_nat (L - k)) k 0%Z sg)); lia. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsci.
    { clear Hsci. step. (* [comment removed for export] *) rewrite F64. step. (* [comment removed for export] *) if_true. apply JC8. }
    clear Hsci.
    step. (* [comment removed for export] *)
    if_cases He.
    { clear He. step. rewrite F64. step. if_true. apply JC8. }
    cond_cleanup He.
    rd kp. pose proof (tx_range bs kp) as Rkp.
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hee.
    2:{ clear Hee. step. rewrite F64. step. if_true. apply JC8. }
    clear Hee.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    assert (JAC : forall (d : Z) (y30 y31 : word), (0 <= d <= 1)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 ex) x8 x9 (Z_to_bv 64 (P + kp)) a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 dc) (Z_to_bv 64 (P + kp + d)) y30 y31)
            F (Z_to_bv 64 0x236ac) fc None m (seg_rom PSEGS))).
    { intros d y30 y31 Hd.
      step. (* [comment removed for export] *)
      if_cases He2.
      { cond_cleanup He2. step. (* [comment removed for export] *) step. (* [comment removed for export] *) goto (eapply (JF0 (kp + d)%Z 0%Z)); lia. }
      cond_cleanup He2.
      rd (kp + d)%Z. pose proof (tx_range bs (kp + d)) as Rk2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmi.
      - clear Hmi. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) rewrite v_sltiu_b2z.
        lazymatch goal with |- context [Z_to_bv 64 (Z.b2z ?b)] =>
          pose proof (b2z_range b) as Hpl; set (pl := Z.b2z b) in * end.
        step. (* [comment removed for export] *) rewrite ?unsigned_lit by lia.
        goto (eapply (JF0 (kp + d + pl)%Z 0%Z)); lia.
      - clear Hmi. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply (JF0 (kp + d + 1)%Z 1%Z)); lia. }
    if_cases Hlt.
    { clear Hlt. goto (eapply (JAC 0%Z)); lia. }
    clear Hlt. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - clear Hz. goto (eapply (JAC 0%Z)); lia.
    - clear Hz. step. (* [comment removed for export] *) goto (eapply (JAC 1%Z)); lia.
  Qed.
End BLK.
End P_fcd_C.


Module P_fcd_D.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac P_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_21b0c : K_21b0c c.
  Hypothesis C_21e70 : K_21e70 c.

  (* [comment removed for export] *)
  #[using="PRE C_21b0c C_21e70"] Lemma fcd_D : K_21a80 c.
  Proof. LiaFast.lf_pins (fun (PRE C_21b0c C_21e70 : LiaFast.U) => LiaFast.u0).
    unfold K_21a80. unfold K_21b0c in C_21b0c. unfold K_21e70 in C_21e70.
    intros junk m x1 x7 x8 x9 x10 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 k1 dc PINV HL1 Hk1 Hdc.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (LOOP : forall (n : nat) (k d : Z) (y31 : word),
      (Z.to_nat (L - k) <= n)%nat -> (0 <= k < L)%Z -> (dc - k <= d <= dc)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k)) x7 x8 x9 x10 a1 a2 a3 a4
                 (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 d) (Z_to_bv 64 46) (Z_to_bv 64 48) y31)
            F (Z_to_bv 64 0x23994) fc None m (seg_rom PSEGS))).
    { induction n as [|n IH]; intros k d y31 Hn Hk Hd. { exfalso. lia. }
      assert (JA0 :
        evt PSEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + k)) x7 x8 x9 x10 a1 a2 a3 a4
                   (txb bs 0) a0 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 d) (Z_to_bv 64 46) (Z_to_bv 64 48) (Z_to_bv 64 (tx bs k)))
              F (Z_to_bv 64 0x239a0) fc None m (seg_rom PSEGS))).
      { pose proof (tx_range bs k) as Rk.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) rewrite v_sltiu_b2z.
        lazymatch goal with |- context [Z_to_bv 64 (Z.b2z ?b)] =>
          pose proof (b2z_range b) as Hz; set (z := Z.b2z b) in * end.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) rewrite word_sub_lit2.
        step. (* [comment removed for export] *)
        if_cases Hm.
        - cond_cleanup Hm. goto (eapply (IH (k + 1)%Z (d - z)%Z)); lia.
        - cond_cleanup Hm. step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hs.
          + clear Hs. eapply C_21b0c. exact PINV0.
          + clear Hs. step. (* [comment removed for export] *) eapply C_21e70; [exact PINV0 | lia]. }
      rd k. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H48.
      { clear H48. apply JA0. }
      clear H48.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      - clear Hdp. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hs.
        + clear Hs. eapply C_21b0c. exact PINV0.
        + clear Hs. step. (* [comment removed for export] *) eapply C_21e70; [exact PINV0 | lia].
      - clear Hdp. apply JA0. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs.
    { clear Hs. eapply C_21b0c. exact PINV0. }
    cond_cleanup Hs. rewrite ?signed_lit in Hs by lia.
    step. (* [comment removed for export] *)
    if_cases He.
    { clear He. eapply C_21e70; [exact PINV0 | lia]. }
    cond_cleanup He.
    step. (* [comment removed for export] *) dp46.
    step. (* [comment removed for export] *)
    goto (eapply (LOOP (Z.to_nat (L - k1)) k1 dc)); lia.
  Qed.
End BLK.
End P_fcd_D.


Module P_fcd_X.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac P_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_slow_path_double_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_parse_infnan_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2; unfold frameA in FR;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis parse_infnan_d_spec : parse_infnan_d_stmt.
  Hypothesis slow_path_double_spec : slow_path_double_stmt.

  (* [comment removed for export] *)
  #[local] Ltac post_call segs m ::=
    let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO;
    destruct_exs PO;
    let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
    destruct PO as [E [MUc [WMc PO]]];
    lazymatch type of PO with
    | _ /\ _ => destruct PO as [MIc PO]
    | _ => rename PO into MIc
    end;
    subst ms';
    lazymatch type of MUc with
    | munch ?W m ?m' =>
        let W' := eval hnf in W in change (munch W' m m') in MUc;
        cbv delta [slow_path_double_need] in MUc;
        transport_after_call segs m m' MUc WMc;
        clear MUc WMc;
        try match goal with H : mem_inv segs m |- _ => clear H end;
        try clear m
    end;
    try destruct_ands PO;
    try (lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end).

  (* [comment removed for export] *)
  #[using="PRE"] Lemma fcd_EPI : K_21dd0 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_21dd0. intros junk m F' fc' v' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      FRM' FR ST VAL MU WM.
    pre_facts. unfold from_chars_double_need in ST. cbv delta [from_chars_double_W from_chars_double_need] in MU.
    unfold frameA in FR.
    gstep. gstep. gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold from_chars_double_post. finish.
    all: try exact VAL. all: try exact FRM'.
  Qed.

  Hypothesis C_21dd0 : K_21dd0 c.

  (* [comment removed for export] *)
  #[using="PRE parse_infnan_d_spec C_21dd0"] Lemma fcd_INF : K_21a44 c.
  Proof. LiaFast.lf_pins (fun (PRE parse_infnan_d_spec C_21dd0 : LiaFast.U) => LiaFast.u0).
    unfold K_21a44. unfold K_21dd0 in C_21dd0.
    intros junk m x1 x5 x6 x7 x8 x9 x10 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PINV HL1.
    pre_facts. open_pinv PINV. unfold frameA in FR.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *) rewrite F16.
    step. (* [comment removed for export] *) if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call parse_infnan_d_spec.
    { exact TXT. } { exact LEN. } { lia. } { exact VAL. } { exact PR1. } { lia. } { lia. }
    rename MI into VAL'.
    gstep. gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply C_21dd0; [exact FRM | exact FR | exact ST | exact VAL' | exact MU | exact WM].
  Qed.

  (* [comment removed for export] *)
  #[using="PRE slow_path_double_spec C_21dd0"] Lemma fcd_SLOW : K_21e70 c.
  Proof. LiaFast.lf_pins (fun (PRE slow_path_double_spec C_21dd0 : LiaFast.U) => LiaFast.u0).
    unfold K_21e70. unfold K_21dd0 in C_21dd0.
    intros junk m x1 x6 x7 x8 x9 x10 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PINV HL1.
    pre_facts. open_pinv PINV. unfold frameA in FR.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *) setcmp. change (Z.b2z (0 <? 0)%Z) with 0%Z.
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -112) ltac:(lia)) as USP.
    step. (* [comment removed for export] *)
    call slow_path_double_spec.
    { exact TXT. } { exact LEN. } { lia. } { lia. } { reflexivity. } { exact VAL. } { exact VAL8. }
    { rewrite USP. unfold slow_path_double_need. replace (bv_unsigned sp + -112 - (688 + 1808))%Z with (bv_unsigned sp - 2608)%Z by lia. exact ST. }
    { rewrite USP. Z.div_mod_to_equations. lia. }
    { rewrite USP. unfold slow_path_double_need. lia. }
    { lia. } { lia. } { lia. } { exact PR1. } { unfold P_FMIN_D. exact PR2. } { exact FRM. }
    { rewrite USP. unfold slow_path_double_need. lia. }
    { rewrite USP. unfold slow_path_double_need. lia. }
    { lia. }
    rewrite ?USP in *.
    match goal with |- _ => idtac end.
    lazymatch goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM' end.
    lazymatch goal with H : stk _ ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST' end.
    lazymatch goal with H : rw_cells _ ?mm V _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into VAL' end.
    unfold slow_path_double_need in ST'. replace (bv_unsigned sp + -112 - (688 + 1808))%Z with (bv_unsigned sp - 2608)%Z in ST' by lia.
    step. (* [comment removed for export] *)
    gstep. gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply C_21dd0; [exact FRM' | exact FR | exact ST' | exact VAL' | exact MU | exact WM].
  Qed.
End BLK.
End P_fcd_X.


Module P_fcd_CL.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac P_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2; unfold frameA in FR;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_21b4c : K_21b4c c.
  Hypothesis C_21d8c : K_21d8c c.
  Hypothesis C_21dd0 : K_21dd0 c.

  (* [comment removed for export] *)
  #[using="PRE C_21b4c C_21d8c C_21dd0"] Lemma fcd_CL : K_21b0c c.
  Proof. LiaFast.lf_pins (fun (PRE C_21b4c C_21d8c C_21dd0 : LiaFast.U) => LiaFast.u0).
    unfold K_21b4c in C_21b4c. unfold K_21d8c in C_21d8c. unfold K_21dd0 in C_21dd0.
    unfold K_21b0c. intros junk m x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. pose proof PINV as PI. open_pinv PI.
    pose proof (bv_unsigned_in_range 64 x7) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed x7) as SQ.
    pose proof (bv_unsigned_in_range 64 x17) as Rw. unfold bv_modulus in Rw.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    assert (PK : forall x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word,
      evt PSEGS POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x23c8c) fc None m (seg_rom PSEGS))).
    { intros. eapply C_21d8c. exact PINV. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hfp.
    2:{ (* [comment removed for export] *)
      clear Hfp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hw0.
      { clear Hw0. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply PK. }
      clear Hw0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hqlo.
      { clear Hqlo. apply PK. }
      cond_cleanup Hqlo. rewrite ?signed_lit in Hqlo by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hqhi.
      { cond_cleanup Hqhi. rewrite ?signed_lit in Hqhi by lia.
        eapply C_21b4c; [exact PINV | lia]. }
      clear Hqhi.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply PK. }
    cond_cleanup Hfp.
    assert (Q22 : (-22 <= bv_signed x7 <= 22)%Z).
    { rewrite SQ. rewrite ?unsigned_lit_wrap in Hfp.
      destruct (Z.ltb_spec0 (bv_unsigned x7) (2^63)); Z.div_mod_to_equations; lia. }
    clear Hfp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw53.
    2:{ clear Hw53. eapply C_21b4c; [exact PINV | lia]. }
    clear Hw53.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [feq_s ?a ?b] => replace (feq_s a b) with true by (vm_compute; reflexivity) end.
    step. (* [comment removed for export] *)
    if_false.
    (* [comment removed for export] *)
    assert (TAIL : forall (Fq : bvmap 5 word) (fcq : bv 32) (xa1 xt2 : word), frm0 fcq ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 xt2 x8 x9 x10 xa1 a2 (Z_to_bv 64 (-45)) x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fq (Z_to_bv 64 0x23d34) fcq None m (seg_rom PSEGS))).
    { intros Fq fcq xa1 xt2 FRMq.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsgn.
      - clear Hsgn.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_21dd0; [exact FRMq | exact FR | exact ST | | exact MU | exact WM].
        match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => first [exact H | replace a with V in H by lia; exact H] end.
      - clear Hsgn.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_21dd0; [exact FRMq | exact FR | exact ST | | exact MU | exact WM].
        match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => first [exact H | replace a with V in H by lia; exact H] end. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hneg.
    - cond_cleanup Hneg. rewrite ?signed_lit in Hneg by lia.
      assert (QS : (bv_signed x7 = bv_unsigned x7 - 2^64)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned x7) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      lazymatch goal with |- context [Some (Z_to_bv 64 (89000 - ?e)%Z)] =>
        replace (Z_to_bv 64 (89000 - e)%Z) with (Z_to_bv 64 (89000 + 8 * (2^64 - bv_unsigned x7)))
          by (rewrite ?unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) end.
      pose proof (table_read PSEGS _ _ _ _ m _ _ TBLD_ok PR1 ltac:(lia) ltac:(cbn; lia) (2^64 - bv_unsigned x7)%Z ltac:(cbn; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      apply TAIL. assumption.
    - cond_cleanup Hneg. rewrite ?signed_lit in Hneg by lia.
      assert (QS : (bv_signed x7 = bv_unsigned x7)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned x7) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      pose proof (table_read PSEGS _ _ _ _ m _ _ TBLD_ok PR1 ltac:(lia) ltac:(cbn; lia) (bv_unsigned x7) ltac:(cbn; lia)) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply TAIL. assumption.
  Qed.
End BLK.
End P_fcd_CL.


Module P_fcd_CF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac P_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2; unfold frameA in FR;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_21d8c : K_21d8c c.

  (* [comment removed for export] *)
  #[using="PRE C_21d8c"] Lemma fcd_CF : K_21b4c c.
  Proof. LiaFast.lf_pins (fun (PRE C_21d8c : LiaFast.U) => LiaFast.u0).
    unfold K_21d8c in C_21d8c.
    unfold K_21b4c. intros junk m x1 x5 x6 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 q PINV Hq.
    pre_facts. pose proof PINV as PI. open_pinv PI.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (bv_unsigned_in_range 64 x17) as Rw. unfold bv_modulus in Rw.
    assert (PK : forall x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word,
      evt PSEGS POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x23c8c) fc None m (seg_rom PSEGS))).
    { intros. eapply C_21d8c. exact PINV. }
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
    assert (J14 : forall v5 v6 v10 v11 v13 v14 v16 v28 v29 : word,
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp v5 v6 q x8 x9 v10 v11 a2 v13 v14 x15 v16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 v28 v29 x30 x31)
            F (Z_to_bv 64 0x23b14) fc None m (seg_rom PSEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *) gen_reg (11:reg).
      gstep. (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (J70 : forall u5 u6 u7 u10 u11 u13 u14 u16 u28 u29 : word,
        evt PSEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp u5 u6 u7 x8 x9 u10 u11 a2 u13 u14 x15 u16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u28 u29 x30 x31)
              F (Z_to_bv 64 0x23b70) fc None m (seg_rom PSEGS))).
      { intros.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        do 10 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hinf.
        - clear Hinf. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply PK.
        - clear Hinf. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply PK. }
      step. (* [comment removed for export] *)
      if_cases Hpos.
      - clear Hpos. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh. do 6 gstep. (* [comment removed for export] *) apply PK.
        + clear Hsh. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply PK.
      - clear Hpos.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hlo.
        { clear Hlo. apply J70. }
        clear Hlo.
        gstep. (* [comment removed for export] *) gen_reg (7:reg).
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hq2.
        { clear Hq2. apply J70. }
        clear Hq2.
        do 5 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hz.
        { clear Hz. apply J70. }
        clear Hz. gstep. (* [comment removed for export] *) apply J70. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    - clear Hlow. apply J14.
    - clear Hlow.
      step. (* [comment removed for export] *)
      do 4 gstep. (* [comment removed for export] *)
      apply J14.
  Qed.
End BLK.
End P_fcd_CF.


Module P_fcd_PK.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac P_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : fcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -112)%Z.
  #[local] Notation NEED := from_chars_double_need.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (from_chars_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL8;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM; pose proof (pre_A4 c PRE) as A4;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold from_chars_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    pose proof (fmt_tests c PRE) as FT; unfold fmt in FT; destruct FT as (F256 & F32 & F128 & F16 & F64);
    pose proof (pre_FMT c PRE) as FMT; unfold fmt in FMT;
    unfold from_chars_double_need in LO, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold from_chars_double_need in ST; unfold P_FMIN in PR2; unfold frameA in FR;
    cbv delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.
  Hypothesis C_21dd0 : K_21dd0 c.

  (* [comment removed for export] *)
  #[using="PRE C_21dd0"] Lemma fcd_PK : K_21d8c c.
  Proof. LiaFast.lf_pins (fun (PRE C_21dd0 : LiaFast.U) => LiaFast.u0).
    unfold K_21d8c. unfold K_21dd0 in C_21dd0.
    intros junk m x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. open_pinv PINV.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *)
    do 13 gstep. (* [comment removed for export] *) gen_reg (15:reg).
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
    eapply C_21dd0; [exact FRM | exact FR | exact ST | exact VAL | exact MU | exact WM].
  Qed.
End BLK.
End P_fcd_PK.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_parse_infnan_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_slow_path_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_A2 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_B OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_C OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_D OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_X OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_CL OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_CF OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_fcd_PK.
Import ListNotations.

Module P_parse_infnan_d.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_from_chars_double.P_parse_infnan_d_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma zxb_off_eqz : forall (c : byte) (k : Z), (bv_unsigned c + k = 0)%Z ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + k)) 1 = Z_to_bv 64 1.
Proof.
  intros c k Hc. rewrite v_sltiu_b2z. unfold zxb.
  pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
  rewrite (unsigned_lit (bv_unsigned c)) by lia.
  rewrite Hc. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  change (bv_wrap 64 1) with 1%Z. reflexivity.
Qed.

Lemma zxb_off_nez : forall (c : byte) (k : Z), (-256 < k <= 0)%Z -> (bv_unsigned c + k <> 0)%Z ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + k)) 1 = Z_to_bv 64 0.
Proof.
  intros c k Hk Hc. rewrite v_sltiu_b2z. unfold zxb.
  pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
  rewrite (unsigned_lit (bv_unsigned c)) by lia.
  rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.lt_ge_cases (bv_unsigned c + k) 0).
  - rewrite <- (Z.mod_unique_pos _ (2^64) (-1) (bv_unsigned c + k + 2^64)) by lia.
    replace (_ <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - rewrite Z.mod_small by lia.
    replace (_ <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Section Proof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (fc : bv 32) (m : word -> option byte) (bs : list byte) (vold : word).
  Hypothesis LEN : (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z.
  Hypothesis LT : (bv_unsigned a0 < bv_unsigned a1)%Z.
  Hypothesis SEP : (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z.
  Hypothesis RO2 : (bv_unsigned a2 + 8 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z.
  Hypothesis Ra1 : (bv_unsigned a1 < 2^64)%Z.

  Notation W := (parse_infnan_d_W a2).
  Ltac fin := finish; match goal with H : rw_cells _ _ _ [C8 _] |- rw_cells _ _ _ _ => exact H end.
  Notation POST := (parse_infnan_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc a2 m).

  Definition nan_loop_ok (j : nat) : Prop :=
    forall (i q : Z) (c : byte) (x5 x6 x10 x16 x17 : word) (F' : bvmap 5 word) (m' : word -> option byte) (v' : word),
      (Z.to_nat (bv_unsigned a1 - q) <= j)%nat ->
      (q = bv_unsigned a0 + i)%Z ->
      nth_error bs (Z.to_nat i) = Some c -> (0 <= i)%Z ->
      (bv_unsigned c <> 41)%Z ->
      bytes_at PSEGS m' (bv_unsigned a0) bs ->
      rw_cells PSEGS m' (bv_unsigned a2) [C8 v'] ->
      munch W m m' -> wmono PSEGS m m' ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 (Z_to_bv 64 41) (Z_to_bv 64 26) (Z_to_bv 64 q) (zxb c) x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x23e48) fc None m' (seg_rom PSEGS)).

  (* [comment removed for export] *)
  #[using="LEN SEP RO2 Ra1"] Lemma nan_adv : forall j, nan_loop_ok j ->
    forall (i q : Z) (x5 x6 x10 x15 x16 x17 : word) (F' : bvmap 5 word) (m' : word -> option byte) (v' : word),
      (Z.to_nat (bv_unsigned a1 - (q + 1)) <= j)%nat ->
      (q = bv_unsigned a0 + i)%Z -> (0 <= i)%Z -> (q < bv_unsigned a1)%Z ->
      bytes_at PSEGS m' (bv_unsigned a0) bs ->
      rw_cells PSEGS m' (bv_unsigned a2) [C8 v'] ->
      munch W m m' -> wmono PSEGS m m' ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 (Z_to_bv 64 41) (Z_to_bv 64 26) (Z_to_bv 64 q) x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x23e6c) fc None m' (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (LEN SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    intros j IH i q x5 x6 x10 x15 x16 x17 F' m' v' MEAS Hq Hi Hlt DATA OBJ MU WM.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He.
    - cond_cleanup He.
      step. step. step. step. (* [comment removed for export] *)
      fin.
    - cond_cleanup He.
      destruct (nth_error bs (Z.to_nat (i + 1))) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      pose proof (u8ro_read PSEGS m' (bv_unsigned a0) bs (i + 1) c _ DATA Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_cases Hp.
      + cond_cleanup Hp.
        eapply (IH (i + 1)%Z (q + 1)%Z c); try eassumption; try lia.
      + cond_cleanup Hp.
        step. step. step. step. step. (* [comment removed for export] *)
        fin.
  Qed.

  #[using="LEN SEP RO2 Ra1"] Lemma nan_loop : forall j, nan_loop_ok j.
  Proof. LiaFast.lf_pins (fun (LEN SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold nan_loop_ok; intros i q c x5 x6 x10 x16 x17 F' m' v' MEAS Hq Hc Hi NPAR DATA OBJ MU WM.
    - exfalso. pose proof (nth_error_lt _ _ _ Hc). lia.
    - pose proof (nth_error_lt _ _ _ Hc) as Hlt.
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H1.
      + clear H1. eapply (nan_adv j IH i q); try eassumption; try lia.
      + clear H1.
        step. step. step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases H2.
        * clear H2. step. step. step. step. fin.
        * clear H2. eapply (nan_adv j IH i q); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LEN SEP RO2 Ra1"] Lemma nan_tail : forall (c0 : byte) (p x5 x6 x10 x13 x16 x17 : word) (d : Z) (F' : bvmap 5 word),
      (d = 0 \/ d = 1)%Z -> (bv_unsigned p = bv_unsigned a0 + d)%Z -> (3 <= bv_unsigned a1 - bv_unsigned p)%Z ->
      bytes_at PSEGS m (bv_unsigned a0) bs -> rw_cells PSEGS m (bv_unsigned a2) [C8 vold] ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 a2 x13 p (zxb c0) x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x23e14) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (LEN SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    intros c0 p x5 x6 x10 x13 x16 x17 d F' Hd Hp H3 DATA OBJ.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl PSEGS m) as WM.
    unfold parse_infnan_d_W in MU.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E3.
    { clear E3. step. step. step. step. fin. }
    cond_cleanup E3.
    destruct (nth_error bs (Z.to_nat (d + 3))) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
    pose proof (u8ro_read PSEGS _ (bv_unsigned a0) bs (d + 3) b3 _ DATA Hb3 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E4.
    { clear E4. step. step. fin. }
    clear E4.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E5.
    { clear E5. step. step. fin. }
    cond_cleanup E5.
    destruct (nth_error bs (Z.to_nat (d + 4))) as [b4|] eqn:Hb4. 2:{ exfalso. apply nth_error_None in Hb4. lia. }
    pose proof (bv_unsigned_in_range 8 b4) as Rb4. unfold bv_modulus in Rb4. cbn in Rb4.
    pose proof (u8ro_read PSEGS _ (bv_unsigned a0) bs (d + 4) b4 _ DATA Hb4 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E6.
    { clear E6. step. step. step. step. step. fin. }
    cond_cleanup E6.
    step. (* [comment removed for export] *)
    eapply (nan_loop _ (d + 4)%Z (bv_unsigned p + 4)%Z b4); try eassumption; try lia. apply Nat.le_refl.
  Qed.

  (* [comment removed for export] *)
  #[using="a1 LEN SEP RO2"] Lemma inf_tail : forall (c0 : byte) (p x5 x6 x10 x11 x13 x16 x17 : word) (d : Z) (F' : bvmap 5 word),
      (d = 0 \/ d = 1)%Z -> (bv_unsigned p = bv_unsigned a0 + d)%Z ->
      bytes_at PSEGS m (bv_unsigned a0) bs -> rw_cells PSEGS m (bv_unsigned a2) [C8 vold] -> pristine m 0x10000 0x22000 ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 x11 a2 x13 p (zxb c0) x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x23ef0) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (a1 LEN SEP RO2 : LiaFast.U) => LiaFast.u0).
    intros c0 p x5 x6 x10 x11 x13 x16 x17 d F' Hd Hp DATA OBJ PR.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl PSEGS m) as WM.
    unfold parse_infnan_d_W in MU.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    pose proof (bv_unsigned_in_range 8 c0) as Rc0. unfold bv_modulus in Rc0. cbn in Rc0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    destruct (Z.eq_dec (bv_unsigned c0) 45) as [Hm|Hm].
    - step. (* [comment removed for export] *)
      rewrite (zxb_off_eqz c0 (-45)) by lia.
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ (bvmap_set 15 ?v _) _ _ _ _ _) => remember v as fv eqn:Hfv; clear Hfv end.
      step. (* [comment removed for export] *)
      step. step. step. fin.
    - step. (* [comment removed for export] *)
      rewrite (zxb_off_nez c0 (-45)) by lia.
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ (bvmap_set 15 ?v _) _ _ _ _ _) => remember v as fv eqn:Hfv; clear Hfv end.
      step. (* [comment removed for export] *)
      step. step. step. fin.
  Qed.

  (* [comment removed for export] *)
  #[using="LEN LT SEP RO2 Ra1"] Lemma pinf_main : forall (c0 : byte) (p x13 : word) (d : Z) (F : bvmap 5 word),
      (d = 0 \/ d = 1)%Z -> (bv_unsigned p = bv_unsigned a0 + d)%Z -> (bv_unsigned p <= bv_unsigned a1)%Z ->
      bytes_at PSEGS m (bv_unsigned a0) bs -> rw_cells PSEGS m (bv_unsigned a2) [C8 vold] -> pristine m 0x10000 0x22000 ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 x13 p (zxb c0) a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x23da8) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (LEN LT SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    intros c0 p x13 d F Hd Hp Hple DATA OBJ PR.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl PSEGS m) as WM.
    unfold parse_infnan_d_W in MU.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    pose proof (bv_unsigned_in_range 8 c0) as Rc0. unfold bv_modulus in Rc0. cbn in Rc0.
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs.
    { clear Hs. step. step. fin. }
    cond_cleanup Hs.
    assert (H3 : (3 <= bv_unsigned a1 - bv_unsigned p)%Z).
    { eapply Z.le_trans; [exact Hs|]. rewrite zb_signed, unsigned_lit by lia.
      destruct (Z.ltb _ _); lia. }
    clear Hs.
    destruct (nth_error bs (Z.to_nat d)) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
    destruct (nth_error bs (Z.to_nat (d + 1))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
    destruct (nth_error bs (Z.to_nat (d + 2))) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. lia. }
    pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 1) b1 _ DATA Hb1 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs d b0 _ DATA Hb0 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 2) b2 _ DATA Hb2 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    do 9 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E1.
    { clear E1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases E7.
      { clear E7. step. (* [comment removed for export] *) eapply (inf_tail c0 p); try eassumption; lia. }
      cond_cleanup E7.
      destruct (nth_error bs (Z.to_nat (d + 3))) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
      destruct (nth_error bs (Z.to_nat (d + 4))) as [b4|] eqn:Hb4. 2:{ exfalso. apply nth_error_None in Hb4. lia. }
      destruct (nth_error bs (Z.to_nat (d + 5))) as [b5|] eqn:Hb5. 2:{ exfalso. apply nth_error_None in Hb5. lia. }
      destruct (nth_error bs (Z.to_nat (d + 6))) as [b6|] eqn:Hb6. 2:{ exfalso. apply nth_error_None in Hb6. lia. }
      destruct (nth_error bs (Z.to_nat (d + 7))) as [b7|] eqn:Hb7. 2:{ exfalso. apply nth_error_None in Hb7. lia. }
      pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 4) b4 _ DATA Hb4 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 3) b3 _ DATA Hb3 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 5) b5 _ DATA Hb5 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 6) b6 _ DATA Hb6 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      step. step. (* [comment removed for export] *)
      pose proof (u8ro_read PSEGS m (bv_unsigned a0) bs (d + 7) b7 _ DATA Hb7 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      do 15 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases E8.
      { clear E8. eapply (inf_tail c0 p); try eassumption; lia. }
      clear E8. step. (* [comment removed for export] *) eapply (inf_tail c0 p); try eassumption; lia. }
    clear E1. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E2.
    { clear E2. step. step. fin. }
    clear E2.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    destruct (Z.eq_dec (bv_unsigned c0) 45) as [Hm|Hm].
    - step. (* [comment removed for export] *)
      rewrite (zxb_off_eqz c0 (-45)) by lia.
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (nan_tail c0 p); try eassumption; lia.
    - step. (* [comment removed for export] *)
      rewrite (zxb_off_nez c0 (-45)) by lia.
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (nan_tail c0 p); try eassumption; lia.
  Qed.
End Proof.


Lemma parse_infnan_d_spec : parse_infnan_d_stmt.
Proof.
  unfold parse_infnan_d_stmt. intros until vold. intros DATA LEN LT OBJ PR SEP RO2.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
  destruct bs as [|c0 bs0]. { cbn [length] in LEN. lia. }
  pose proof (bv_unsigned_in_range 8 c0) as Rc0. unfold bv_modulus in Rc0. cbn in Rc0.
  pose proof (u8ro_read PSEGS m (bv_unsigned a0) (c0 :: bs0) 0 c0 _ DATA eq_refl ltac:(lia) eq_refl) as RD.
  step. (* [comment removed for export] *)
  clear RD.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hc.
  - clear Hc. step. (* [comment removed for export] *)
    eapply pinf_main; [exact LEN | exact LT | exact SEP | exact RO2 | lia | right; reflexivity
                      | apply unsigned_lit; lia | rewrite unsigned_lit by lia; lia | exact DATA | exact OBJ | exact PR].
  - clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hf.
    + clear Hf.
      eapply pinf_main; [exact LEN | exact LT | exact SEP | exact RO2 | lia | left; reflexivity
                        | lia | lia | exact DATA | exact OBJ | exact PR].
    + clear Hf.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hpl.
      * clear Hpl.
        eapply pinf_main; [exact LEN | exact LT | exact SEP | exact RO2 | lia | left; reflexivity
                          | lia | lia | exact DATA | exact OBJ | exact PR].
      * clear Hpl. step. (* [comment removed for export] *)
        eapply pinf_main; [exact LEN | exact LT | exact SEP | exact RO2 | lia | right; reflexivity
                          | apply unsigned_lit; lia | rewrite unsigned_lit by lia; lia | exact DATA | exact OBJ | exact PR].
Qed.
End P_parse_infnan_d.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem from_chars_double_spec : parse_infnan_d_stmt -> slow_path_double_stmt -> from_chars_double_stmt.
Proof.
  intros PINF SLOW. unfold from_chars_double_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v fmt
         Ha3 Hfmt Ha4 TXT LEN RANGE ENW VAL VAL8 ST AL LO P0 V0 VLO PR1 PR2 FRM SEP1 SEP2 SEP3.
  subst a3 a4.
  set (c := SPF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 fmt) (Z_to_bv 64 FCD_OPT2) a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs v).
  assert (PRE : fcd_pre c).
  { constructor; cbn; try assumption; try reflexivity.
    unfold P_fcd_common.fmt. cbn. rewrite unsigned_lit by lia. exact Hfmt. }
  pose proof (fcd_EPI c PRE) as KDD0.
  pose proof (fcd_INF c PRE PINF KDD0) as KA44.
  pose proof (fcd_SLOW c PRE SLOW KDD0) as KE70.
  pose proof (fcd_PK c PRE KDD0) as KD8C.
  pose proof (fcd_CF c PRE KD8C) as KB4C.
  pose proof (fcd_CL c PRE KB4C KD8C KDD0) as KB0C.
  pose proof (fcd_D c PRE KB0C KE70) as KA80.
  pose proof (fcd_C c PRE KA80 KA44) as K724.
  pose proof (fcd_B c PRE K724 KA44) as K51C.
  pose proof (fcd_A2 c PRE K51C) as K2DC.
  exact (fcd_A c PRE K2DC KA44).
Qed.

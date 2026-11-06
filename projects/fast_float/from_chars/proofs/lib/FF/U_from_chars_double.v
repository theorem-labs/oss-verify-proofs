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
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_from_chars_double_stmt.

Module U_parse_infnan_d_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition parse_infnan_d_entry : Z := 0x243ac.

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
             F' (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (parse_infnan_d_W v) m m'
    /\ wmono USEGS m m'
    /\ rw_cells USEGS m' (bv_unsigned v) [C8 v'].

Definition parse_infnan_d_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (vold : word),
    (* [comment removed for export] *)
    bytes_at USEGS m (bv_unsigned a0) bs ->
    (0 < bv_unsigned a0)%Z ->
    (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z ->
    (bv_unsigned a0 < bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a2) [C8 vold] ->
    (* [comment removed for export] *)
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z ->
    (bv_unsigned a2 + 8 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z ->
    evt USEGS (parse_infnan_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc a2 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x243ac) fc None m (seg_rom USEGS)).
End U_parse_infnan_d_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_slow_path_double_stmt U_fcd_common.

Module U_fcd_commonT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export U_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CTX.
  Variable c : spf_ctx.
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation sp := (r_sp c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
  #[local] Notation POST := (from_chars_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).

  (* [comment removed for export] *)
  Definition K_22040 : Prop :=
    forall lo m (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (q : word),
      pinv c lo m -> (-342 <= bv_signed q <= 308)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 q x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24004) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  Definition K_22280 : Prop :=
    forall lo m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      pinv c lo m ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24244) fc None m (seg_rom USEGS)).
End CTX.
End U_fcd_commonT.


Module U_fcd_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_21610 : K_21610 c.
  Hypothesis C_21f40 : K_21f40 c.
  Hypothesis C_222b8 : K_222b8 c.

  (* [comment removed for export] *)
  #[using="PRE C_21610 C_21f40 C_222b8"] Lemma ufcd_A :
    evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x23380) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_21610 C_21f40 C_222b8 : LiaFast.U) => LiaFast.u0).
    unfold K_21610 in C_21610. unfold K_21f40 in C_21f40. unfold K_222b8 in C_222b8.
    pre_facts.
    pose proof (pre_ST c PRE) as ST. unfold from_chars_double_need in ST.
    pose proof (pre_TXT c PRE) as TXT. pose proof (pre_VAL c PRE) as VAL.
    pose proof (pre_PR1 c PRE) as PR1. pose proof (pre_PR2 c PRE) as PR2. unfold U_FMIN in PR2.
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    pose proof (munch_refl W m0) as MU. cbv beta delta [from_chars_double_W from_chars_double_need] in MU.
    pose proof (wmono_refl USEGS m0) as WM.
    carve_frame 128%nat ST.
    do 14 step.   (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells USEGS ?m1 (bv_unsigned sp + -128)%Z ?cs |- _ =>
      chunk_split FR 1%nat FRL FRH end.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => rename m1 into m end.
    assert (PINV : pinv c [CB 24 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 (firstn 80
                   (firstn 88 (firstn 96 (firstn 104 (firstn 112 (firstn 120 junk)))))))))))))] m).
    { mk_pinv. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite F256.
    step. (* [comment removed for export] *) if_true.
    step. (* [comment removed for export] *)
    if_cases Hemp.
    { (* [comment removed for export] *)
      cond_cleanup Hemp.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      eapply C_222b8; [exact FRM | exact FRL | reflexivity | exact FRH | unfold from_chars_double_need; exact ST | exact VAL
                     | cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]. }
    cond_cleanup Hemp.
    step. (* [comment removed for export] *) rewrite F32.
    step. (* [comment removed for export] *) dp46.
    step. (* [comment removed for export] *) if_true.
    step. (* [comment removed for export] *) notrap.
    rd 0%Z. (* [comment removed for export] *)
    pose proof (tx_range bs 0) as Rb0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hminus.
    - (* [comment removed for export] *)
      clear Hminus.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) notrap.
      step. (* [comment removed for export] *)
      if_cases Hend.
      { cond_cleanup Hend. goto (eapply C_21f40); [exact PINV | lia]. }
      cond_cleanup Hend.
      rd 1%Z. (* [comment removed for export] *)
      pose proof (tx_range bs 1) as Rb1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hdig.
      { clear Hdig. goto (eapply C_21610 with (k1 := 1%Z)); [exact PINV | lia | lia]. }
      clear Hdig.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      { clear Hdp. goto (eapply C_21f40); [exact PINV | lia]. }
      clear Hdp. goto (eapply C_21610 with (k1 := 1%Z)); [exact PINV | lia | lia].
    - clear Hminus.
      step. (* [comment removed for export] *) rewrite F128.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_true.
      goto (eapply C_21610 with (k1 := 0%Z)); [exact PINV | lia | lia].
  Qed.
End BLK.
End U_fcd_A.


Module U_fcd_A2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_218ac : K_218ac c.

  (* [comment removed for export] *)
  #[using="PRE C_218ac"] Lemma ufcd_A2 : K_21610 c.
  Proof. LiaFast.lf_pins (fun (PRE C_218ac : LiaFast.U) => LiaFast.u0).
    unfold K_21610. unfold K_218ac in C_218ac.
    intros junk m x1 x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x29 x30 x31 k1 PINV Hk1 Hk1L.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (LOOP : forall (n : nat) (k : Z) (x8 x12 x16 : word),
      (Z.to_nat (L - k) <= n)%nat -> (k1 <= k <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 (Z_to_bv 64 (P + k)) x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 10)
                 (Z_to_bv 64 (P + k)) (Z_to_bv 64 9))
            F (Z_to_bv 64 0x236d0) fc None m (seg_rom USEGS))).
    { induction n as [|n IH]; intros k y8 y12 y16 Hn Hk.
      { step. (* [comment removed for export] *)
        if_cases He; cond_cleanup He; [|exfalso; lia].
        step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply C_218ac with (k1 := k1) (kI := L)); [exact PINV0 | lia | lia | lia]. }
      step. (* [comment removed for export] *)
      if_cases He.
      { cond_cleanup He. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply C_218ac with (k1 := k1) (kI := L)); [exact PINV0 | lia | lia | lia]. }
      cond_cleanup He.
      rd k. (* [comment removed for export] *) pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hd.
      { clear Hd. goto (eapply C_218ac with (k1 := k1) (kI := k)); [exact PINV0 | lia | lia | lia]. }
      clear Hd.
      gstep. (* [comment removed for export] *)
      step.  (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *) gen_reg (16:reg).
      step.  (* [comment removed for export] *)
      step.  (* [comment removed for export] *) notrap.
      step.  (* [comment removed for export] *)
      goto (eapply (IH (k + 1)%Z)); lia. }
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
    { clear Hd0. goto (eapply C_218ac with (k1 := k1) (kI := k1)); [exact PINV0 | lia | lia | lia]. }
    clear Hd0.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) notrap.
    step. (* [comment removed for export] *)
    if_cases He1.
    { cond_cleanup He1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 1)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He1.
    rd (k1 + 1)%Z. pose proof (tx_range bs (k1 + 1)) as R1.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd1.
    { clear Hd1. step. step. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 1)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd1.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) notrap.
    step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (16:reg).
    step. (* [comment removed for export] *)
    if_cases He2.
    { cond_cleanup He2. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 2)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He2.
    (* [comment removed for export] *)
    rd (k1 + 2)%Z. pose proof (tx_range bs (k1 + 2)) as R2.
    step. step. step. (* [comment removed for export] *)
    if_cases Hd2.
    { clear Hd2. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 2)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd2.
    step. step. step. (* [comment removed for export] *) notrap.
    step. gstep. gstep. step. (* [comment removed for export] *) gstep. gen_reg (16:reg).
    step. (* [comment removed for export] *)
    if_cases He3.
    { cond_cleanup He3. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 3)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He3.
    (* [comment removed for export] *)
    rd (k1 + 3)%Z. pose proof (tx_range bs (k1 + 3)) as R3.
    step. step. step.
    if_cases Hd3.
    { clear Hd3. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 3)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd3.
    step. step. step. notrap.
    step. gstep. gstep. step. (* [comment removed for export] *) gstep. gen_reg (16:reg).
    step. (* [comment removed for export] *)
    if_cases He4.
    { cond_cleanup He4. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 4)%Z)); [exact PINV0 | lia | lia | lia]. }
    cond_cleanup He4.
    (* [comment removed for export] *)
    rd (k1 + 4)%Z. pose proof (tx_range bs (k1 + 4)) as R4.
    step. step. step. (* [comment removed for export] *)
    if_cases Hd4.
    { clear Hd4. goto (eapply C_218ac with (k1 := k1) (kI := (k1 + 4)%Z)); [exact PINV0 | lia | lia | lia]. }
    clear Hd4.
    step. step. step. notrap. (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    gstep. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (16:reg).
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    goto (eapply (LOOP (Z.to_nat (L - (k1 + 5))) (k1 + 5)%Z)); lia.
  Qed.
End BLK.
End U_fcd_A2.


Module U_fcd_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac kill_chk :=
    let H := fresh "Hc" in if_cases H;
    [ exfalso; cond_cleanup H; unsign_chk H; rewrite ?signed_lit in H by lia;
      repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
      first [lia | Z.div_mod_to_equations; lia]
    | clear H ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_21b04 : K_21b04 c.
  Hypothesis C_21f40 : K_21f40 c.

  #[local] Notation LO3 := [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 46); C8 (r_a2 c)].

  (* [comment removed for export] *)
  #[using="PRE C_21b04 C_21f40"] Lemma ufcd_B2 : forall m (k1 kI : Z) (x1 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 : word),
      pinv c LO3 m -> (1 <= L)%Z -> (0 <= k1 <= 1)%Z -> (k1 <= kI)%Z -> (kI < L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 (Z_to_bv 64 (P + kI)) x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 (kI - k1)) x30 x31)
            F (Z_to_bv 64 0x23898) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (PRE C_21b04 C_21f40 : LiaFast.U) => LiaFast.u0).
    unfold K_21b04 in C_21b04. unfold K_21f40 in C_21f40.
    intros m k1 kI x1 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 PINV HL1 Hk1 HkI HkIL.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (J530 : forall (kp : Z) (x1 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 : word),
      (kI + 1 <= kp <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 x12 a3 a4
                 (Z_to_bv 64 (P + kp)) x16 x17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 (kI - k1)) x30 x31)
            F (Z_to_bv 64 0x23aac) fc None m (seg_rom USEGS))).
    { intros kp y1 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y25 y26 y27 y30 y31 Hkp.
      step. (* [comment removed for export] *) rewrite word_sub_lit2.
      replace (P + kI + 1 - (P + kp))%Z with (kI + 1 - kp)%Z by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) rewrite word_sub_lit2.
      replace (kI - k1 - (kI + 1 - kp))%Z with (kp - k1 - 1)%Z by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) kill_chk.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz. goto (eapply C_21f40); [exact PINV0 | lia].
      - cond_cleanup Hz. goto (eapply C_21b04 with (k1 := k1) (kp := kp) (ex := (kI + 1 - kp)%Z) (dc := (kp - k1 - 1)%Z));
          [exact PINV0 | lia | lia | lia | lia | lia]. }
    (* [comment removed for export] *)
    assert (JL : forall (n : nat) (q : Z) (y1 y9 y12 y16 y17 y18 y19 y20 y21 y22 y25 y26 y27 : word),
      (Z.to_nat (L - q) <= n)%nat -> (kI + 1 <= q < L)%Z ->
      evt USEGS POST
        (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 10) y9 a0 a1 y12 a3 a4
                 (Z_to_bv 64 (P + q)) y16 y17 y18 y19 y20 y21 y22 a2 (Z_to_bv 64 46) y25 y26 y27 (txb bs 0) (Z_to_bv 64 (kI - k1))
                 (Z_to_bv 64 9) (Z_to_bv 64 (-1)))
            F (Z_to_bv 64 0x23a84) fc None m (seg_rom USEGS))).
    { induction n as [|n IH]; intros q y1 y9 y12 y16 y17 y18 y19 y20 y21 y22 y25 y26 y27 Hn Hq. { exfalso. lia. }
      rd q. (* [comment removed for export] *) pose proof (tx_range bs q) as Rq.
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hd.
      { clear Hd. goto (eapply (J530 q)); lia. }
      clear Hd.
      step. (* [comment removed for export] *) notrap.
      step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (16:reg).
      step. (* [comment removed for export] *)
      if_cases Hm.
      - cond_cleanup Hm. goto (eapply (IH (q + 1)%Z)); lia.
      - cond_cleanup Hm. step. (* [comment removed for export] *) goto (eapply (J530 L)); lia. }
    (* [comment removed for export] *)
    assert (J4ec : forall (q : Z) (y1 y5 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y30 y31 : word),
      (kI + 1 <= q <= L)%Z ->
      evt USEGS POST
        (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) y8 y9 a0 a1 y12 a3 a4
                 (Z_to_bv 64 (P + q)) y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (txb bs 0) (Z_to_bv 64 (kI - k1)) y30 y31)
            F (Z_to_bv 64 0x23a68) fc None m (seg_rom USEGS))).
    { intros q y1 y5 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y30 y31 Hq.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He.
      - cond_cleanup He. goto (eapply (J530 q)); lia.
      - cond_cleanup He. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        goto (eapply (JL (Z.to_nat (L - q)) q)); lia. }
    (* [comment removed for export] *)
    assert (J474 : forall (q : Z) (y1 y5 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 : word),
      (kI + 1 <= q)%Z -> (q + 4 <= L)%Z ->
      evt USEGS POST
        (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) y8 y9 a0 a1 y12 a3 a4
                 (Z_to_bv 64 (P + q)) y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (txb bs 0) (Z_to_bv 64 (kI - k1))
                 (Z_to_bv 64 (P + q)) y31)
            F (Z_to_bv 64 0x239f0) fc None m (seg_rom USEGS))).
    { intros q y1 y5 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31 Hq1 Hq2.
      do 4 step. (* [comment removed for export] *) do 2 gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc.
      - clear Hc. goto (eapply (J4ec q)); lia.
      - clear Hc.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) notrap.
        step. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. gstep. gstep. (* [comment removed for export] *)
        step. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (16:reg).
        step. (* [comment removed for export] *)
        goto (eapply (J4ec (q + 4)%Z)); lia. }
    (* [comment removed for export] *)
    assert (J444 : forall (q R : Z) (y1 y5 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 : word),
      (kI + 1 <= q <= L)%Z -> (R = L - q)%Z ->
      evt USEGS POST
        (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) y8 y9 a0 a1 y12 a3 a4
                 (Z_to_bv 64 (P + q)) y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (txb bs 0) (Z_to_bv 64 (kI - k1))
                 (Z_to_bv 64 (P + q)) (Z_to_bv 64 R))
            F (Z_to_bv 64 0x239c0) fc None m (seg_rom USEGS))).
    { intros q R y1 y5 y8 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 Hq HR.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hs.
      - clear Hs. goto (eapply (J4ec q)); lia.
      - cond_cleanup Hs. rewrite ?signed_lit in Hs by lia.
        rd (q + 1)%Z. rd q. rd (q + 2)%Z. rd (q + 3)%Z.
        do 6 gstep. (* [comment removed for export] *)
        goto (eapply (J474 q)); lia. }
    (* [comment removed for export] *)
    assert (SW : forall (n : nat) (q R : Z) (y1 y5 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y26 y27 : word),
      (Z.to_nat (L - q) <= n)%nat -> (kI + 1 <= q)%Z -> (R = L - q)%Z -> (8 <= R)%Z ->
      evt USEGS POST
        (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 (Z_to_bv 64 (P + kI + 1)) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 8) y9 a0 a1 y12 a3 a4
                 (Z_to_bv 64 (P + q)) y16 y17 y18 y19 y20 y21 y22 y23 y24 (Z_to_bv 64 7) y26 y27 (txb bs 0) (Z_to_bv 64 (kI - k1))
                 (Z_to_bv 64 (P + q)) (Z_to_bv 64 R))
            F (Z_to_bv 64 0x238f8) fc None m (seg_rom USEGS))).
    { induction n as [|n IH]; intros q R y1 y5 y9 y12 y16 y17 y18 y19 y20 y21 y22 y23 y24 y26 y27 Hn Hq HR H8. { exfalso. lia. }
      rd (q + 1)%Z. rd (q + 2)%Z. rd (q + 3)%Z. rd q.
      do 4 gstep. (* [comment removed for export] *)
      rd (q + 4)%Z. rd (q + 5)%Z.
      gstep. (* [comment removed for export] *)
      rd (q + 6)%Z. rd (q + 7)%Z.
      do 12 gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc.
      { clear Hc. goto (eapply (J474 q)); lia. }
      clear Hc.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) notrap.
      do 3 gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      do 9 gstep. (* [comment removed for export] *) gen_reg (16:reg).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      - cond_cleanup Hb. rewrite ?signed_lit in Hb by lia.
        goto (eapply (IH (q + 8)%Z)); lia.
      - cond_cleanup Hb. rewrite ?signed_lit in Hb by lia. step. (* [comment removed for export] *)
        goto (eapply (J444 (q + 8)%Z (R + -8)%Z)); lia. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit.
    lazymatch goal with |- context [Some (Z_to_bv 64 (E - ?u))] => replace (E - u)%Z with (L - (kI + 1))%Z by lia end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs8.
    - clear Hs8. step. (* [comment removed for export] *) step. (* [comment removed for export] *) goto (eapply (J444 (kI + 1)%Z)); lia.
    - cond_cleanup Hs8. rewrite ?signed_lit in Hs8 by lia.
      do 19 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      goto (eapply (SW (Z.to_nat (L - (kI + 1))) (kI + 1)%Z (L - (kI + 1))%Z)); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE C_21b04 C_21f40"] Lemma ufcd_B : K_218ac c.
  Proof. LiaFast.lf_pins (fun (PRE C_21b04 C_21f40 : LiaFast.U) => LiaFast.u0).
    unfold K_218ac. unfold K_21b04 in C_21b04. unfold K_21f40 in C_21f40.
    intros junk m x1 x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x29 x30 x31 k1 kI PINV HL1 Hk1 HkI.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    step. (* [comment removed for export] *) rewrite word_sub_lit2. replace (P + kI - (P + k1))%Z with (kI - k1)%Z by lia.
    step. (* [comment removed for export] *)
    if_cases He.
    { cond_cleanup He. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz. goto (eapply C_21b04 with (k1 := k1) (kp := kI) (ex := 0%Z) (dc := (kI - k1)%Z)); [exact PINV0 | lia | lia | lia | lia | lia].
      - cond_cleanup Hz. step. (* [comment removed for export] *) goto (eapply C_21f40); [exact PINV0 | lia]. }
    cond_cleanup He.
    rd kI. pose proof (tx_range bs kI) as RkI.
    step. (* [comment removed for export] *)
    if_cases Hdp.
    { clear Hdp. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases Hz.
      - cond_cleanup Hz. goto (eapply C_21b04 with (k1 := k1) (kp := kI) (ex := 0%Z) (dc := (kI - k1)%Z)); [exact PINV0 | lia | lia | lia | lia | lia].
      - cond_cleanup Hz. step. (* [comment removed for export] *) goto (eapply C_21f40); [exact PINV0 | lia]. }
    clear Hdp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) notrap.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => rename m1 into m' end.
    assert (PINV1 : pinv c LO3 m'). { mk_pinv. }
    goto (eapply (ufcd_B2 m' k1 kI)); first [exact PINV1 | lia].
  Qed.
End BLK.
End U_fcd_B.


Module U_fcd_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac kill_chk :=
    let H := fresh "Hc" in if_cases H;
    [ exfalso; cond_cleanup H; unsign_chk H; rewrite ?signed_lit in H by lia;
      repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
      first [lia | Z.div_mod_to_equations; lia]
    | clear H ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_21e6c : K_21e6c c.
  Hypothesis C_21f40 : K_21f40 c.

  (* [comment removed for export] *)
  #[using="PRE C_21e6c C_21f40"] Lemma ufcd_C : K_21b04 c.
  Proof. LiaFast.lf_pins (fun (PRE C_21e6c C_21f40 : LiaFast.U) => LiaFast.u0).
    unfold K_21b04. unfold K_21e6c in C_21e6c. unfold K_21f40 in C_21f40.
    intros lo m x1 x8 x9 x12 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 k1 kp ex dc PINV HL1 Hk1 Hkp Hex Hdc.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (JC : forall (y12 y15 y17 y30 y31 : word),
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 y12 a3 a4
                 y15 x16 y17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc) y30 y31)
            F (Z_to_bv 64 0x23b88) fc None m (seg_rom USEGS))).
    { intros. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hs.
      - clear Hs. goto (eapply C_21e6c with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia].
      - clear Hs. step. (* [comment removed for export] *) goto (eapply C_21f40); [exact PINV0 | lia]. }
    (* [comment removed for export] *)
    assert (JA4 : forall (y8 y9 y12 y15 y17 y30 y31 : word),
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) y8 y9 a0 a1 y12 a3 a4
                 y15 x16 y17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc) y30 y31)
            F (Z_to_bv 64 0x23c20) fc None m (seg_rom USEGS))).
    { intros. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hf.
      - clear Hf. goto (eapply C_21e6c with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia].
      - clear Hf. step. (* [comment removed for export] *) goto (eapply C_21f40); [exact PINV0 | lia]. }
    (* [comment removed for export] *)
    assert (J98 : forall (en sg : Z) (y9 y12 y15 y17 y18 y19 y20 y21 y30 : word), (0 <= en < 2^32)%Z -> (0 <= sg <= 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 en) y9 a0 a1 y12 a3 a4
                 y15 x16 y17 y18 y19 y20 y21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc) y30 (Z_to_bv 64 sg))
            F (Z_to_bv 64 0x23e14) fc None m (seg_rom USEGS))).
    { intros en sg y9 y12 y15 y17 y18 y19 y20 y21 y30 Hen Hsg.
      step. (* [comment removed for export] *)
      if_cases Hs0.
      - clear Hs0.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) kill_chk.
        step. (* [comment removed for export] *)
        goto (eapply C_21e6c with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia].
      - clear Hs0. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) kill_chk.
        step. (* [comment removed for export] *)
        goto (eapply C_21e6c with (k1 := k1) (dc := dc)); [exact PINV0 | lia | lia | lia]. }
    (* [comment removed for export] *)
    assert (LOOP : forall (n : nat) (k en sg : Z) (y12 y17 y21 : word),
      (Z.to_nat (L - k) <= n)%nat -> (kp <= k < L)%Z -> (0 <= en < 2^32)%Z -> (0 <= sg <= 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) (Z_to_bv 64 en) (Z_to_bv 64 9)
                 a0 a1 y12 a3 a4
                 (Z_to_bv 64 10) x16 y17 (Z_to_bv 64 268435455) (Z_to_bv 64 2) (Z_to_bv 64 (P + k)) y21 x22 a2 (Z_to_bv 64 46) x25 x26 x27
                 (txb bs 0) (Z_to_bv 64 dc) (Z_to_bv 64 (P + k)) (Z_to_bv 64 sg))
            F (Z_to_bv 64 0x23be0) fc None m (seg_rom USEGS))).
    { induction n as [|n IH]; intros k en sg y12 y17 y21 Hn Hk Hen Hsg. { exfalso. lia. }
      rd k. (* [comment removed for export] *) pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (Z.land ?u 255))] =>
        pose proof (land_range_r u 255 ltac:(lia)) as Hd; set (dg := Z.land u 255) in * end.
      step. (* [comment removed for export] *)
      if_cases Hnd.
      { clear Hnd. step. (* [comment removed for export] *) goto (eapply (J98 en sg)); lia. }
      cond_cleanup Hnd.
      step. (* [comment removed for export] *)
      if_cases Hbig.
      - cond_cleanup Hbig. rewrite ?signed_lit in Hbig by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) notrap.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hm.
        + cond_cleanup Hm. goto (eapply (IH (k + 1)%Z en sg)); lia.
        + cond_cleanup Hm. step. (* [comment removed for export] *) step. (* [comment removed for export] *) goto (eapply (J98 en sg)); lia.
      - cond_cleanup Hbig. rewrite ?signed_lit in Hbig by lia.
        step. (* [comment removed for export] *) rewrite ?signed_lit by lia.
        rewrite (Z.shiftr_div_pow2 (en * 10)) by lia. rewrite (Z.div_small (en * 10)) by lia.
        step. (* [comment removed for export] *) rewrite ?unsigned_lit by lia.
        step. (* [comment removed for export] *) rewrite ?signed_lit by lia.
        rewrite (Z.shiftr_div_pow2 (en * 10)) by lia. rewrite (Z.div_small (en * 10)) by lia.
        step. (* [comment removed for export] *) notrap.
        step. (* [comment removed for export] *) rewrite ?unsigned_lit by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *) notrap.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hm.
        + cond_cleanup Hm. goto (eapply (IH (k + 1)%Z (en * 10 + dg)%Z sg)); lia.
        + cond_cleanup Hm. step. (* [comment removed for export] *) step. (* [comment removed for export] *) goto (eapply (J98 (en * 10 + dg)%Z sg)); lia. }
    (* [comment removed for export] *)
    assert (JF : forall (k sg : Z) (y12r y17 : word), (kp <= k < L)%Z -> (0 <= sg <= 1)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 y12r a3 a4
                 (Z_to_bv 64 (P + kp)) x16 y17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc)
                 (Z_to_bv 64 (P + k)) (Z_to_bv 64 sg))
            F (Z_to_bv 64 0x23bb8) fc None m (seg_rom USEGS))).
    { intros k sg y12r y17 Hk Hsg.
      rd k. pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnd.
      { clear Hnd. apply JA4. }
      clear Hnd.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      goto (eapply (LOOP (Z.to_nat (L - k)) k 0%Z sg)); lia. }
    (* [comment removed for export] *)
    assert (JAC : forall (d : Z) (y12 y17 y31 : word), (0 <= d <= 1)%Z -> (kp + d <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) (Z_to_bv 64 ex) (Z_to_bv 64 (P + k1)) x8 x9 a0 a1 y12 a3 a4
                 (Z_to_bv 64 (P + kp)) x16 y17 x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 (txb bs 0) (Z_to_bv 64 dc)
                 (Z_to_bv 64 (P + kp + d)) y31)
            F (Z_to_bv 64 0x23b58) fc None m (seg_rom USEGS))).
    { intros d y12 y17 y31 Hd HdL.
      step. (* [comment removed for export] *)
      if_cases He2.
      { cond_cleanup He2. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        if_cases Hx; cond_cleanup Hx; [exfalso; lia|]. step. (* [comment removed for export] *) apply JA4. }
      cond_cleanup He2.
      rd (kp + d)%Z. pose proof (tx_range bs (kp + d)) as Rk2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hpl.
      { clear Hpl. step. (* [comment removed for export] *) step. (* [comment removed for export] *) notrap.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases He3.
        - clear He3. apply JA4.
        - cond_cleanup He3. goto (eapply (JF (kp + d + 1)%Z 0%Z)); lia. }
      clear Hpl.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmi.
      { clear Hmi. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        if_cases Hx.
        - cond_cleanup Hx. goto (eapply (JF (kp + d)%Z 0%Z)); lia.
        - cond_cleanup Hx. step. (* [comment removed for export] *) apply JA4. }
      clear Hmi.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) notrap.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hx.
      - cond_cleanup Hx. goto (eapply (JF (kp + d + 1)%Z 1%Z)); lia.
      - cond_cleanup Hx. step. (* [comment removed for export] *) apply JA4. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsci.
    { clear Hsci. step. (* [comment removed for export] *) rewrite F64. step. (* [comment removed for export] *) if_true. apply JC. }
    clear Hsci.
    step. (* [comment removed for export] *)
    if_cases He.
    { clear He. step. rewrite F64. step. if_true. apply JC. }
    cond_cleanup He.
    rd kp. pose proof (tx_range bs kp) as Rkp.
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hee.
    2:{ clear Hee. step. rewrite F64. step. if_true. apply JC. }
    clear Hee.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hlt.
    { clear Hlt. goto (eapply (JAC 0%Z)); lia. }
    clear Hlt. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - clear Hz. goto (eapply (JAC 0%Z)); lia.
    - clear Hz. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *) notrap.
      goto (eapply (JAC 1%Z)); lia.
  Qed.
End BLK.
End U_fcd_C.


Module U_fcd_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac kill_chk :=
    let H := fresh "Hc" in if_cases H;
    [ exfalso; cond_cleanup H; unsign_chk H; rewrite ?signed_lit in H by lia;
      repeat match type of H with context [if (?a <? ?b)%Z then _ else _] => destruct (Z.ltb_spec0 a b) end;
      first [lia | Z.div_mod_to_equations; lia]
    | clear H ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_22000 : K_22000 c.
  Hypothesis C_223a0 : K_223a0 c.

  (* [comment removed for export] *)
  #[using="PRE C_22000 C_223a0"] Lemma ufcd_D : K_21e6c c.
  Proof. LiaFast.lf_pins (fun (PRE C_22000 C_223a0 : LiaFast.U) => LiaFast.u0).
    unfold K_21e6c. unfold K_22000 in C_22000. unfold K_223a0 in C_223a0.
    intros lo m x1 x6 x8 x9 x12 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x30 x31 k1 dc PINV HL1 Hk1 Hdc.
    pre_facts. pose proof PINV as PINV0. open_pinv PINV.
    (* [comment removed for export] *)
    assert (LOOP : forall (n : nat) (k d : Z) (y8 y12 y28 : word),
      (Z.to_nat (L - k) <= n)%nat -> (0 <= k < L)%Z -> (dc - k <= d <= dc)%Z ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 (Z_to_bv 64 (P + k)) y8 x9 a0 a1 y12 a3 a4
                 x15 x16 (Z_to_bv 64 20) x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 y28 (Z_to_bv 64 d)
                 (Z_to_bv 64 48) (Z_to_bv 64 (-1)))
            F (Z_to_bv 64 0x23e4c) fc None m (seg_rom USEGS))).
    { induction n as [|n IH]; intros k d y8 y12 y28 Hn Hk Hd. { exfalso. lia. }
      (* [comment removed for export] *)
      assert (JEC : forall (d' : Z) (z8 : word), (d - 1 <= d' <= d)%Z ->
        evt USEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 (Z_to_bv 64 (P + k)) z8 x9 a0 a1 y12 a3 a4
                   x15 x16 (Z_to_bv 64 20) x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 y28 (Z_to_bv 64 d')
                   (Z_to_bv 64 48) (Z_to_bv 64 (-1)))
              F (Z_to_bv 64 0x23e68) fc None m (seg_rom USEGS))).
      { intros d' z8 Hd'.
        step. (* [comment removed for export] *) notrap.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hm.
        - cond_cleanup Hm. goto (eapply (IH (k + 1)%Z d')); lia.
        - cond_cleanup Hm. step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hs.
          + clear Hs. eapply C_22000. exact PINV0.
          + clear Hs. step. (* [comment removed for export] *) eapply C_223a0; [exact PINV0 | lia]. }
      (* [comment removed for export] *)
      assert (JDC : forall (ch : Z), (0 <= ch < 256)%Z ->
        evt USEGS POST
          (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 0) x6 (Z_to_bv 64 (P + k)) (Z_to_bv 64 ch) x9 a0 a1 y12 a3 a4
                   x15 x16 (Z_to_bv 64 20) x18 x19 x20 x21 x22 a2 (Z_to_bv 64 46) x25 x26 x27 y28 (Z_to_bv 64 d)
                   (Z_to_bv 64 48) (Z_to_bv 64 (-1)))
              F (Z_to_bv 64 0x23e58) fc None m (seg_rom USEGS))).
      { intros ch Hch.
        step. (* [comment removed for export] *)
        if_cases H48.
        - clear H48. apply (JEC d). lia.
        - clear H48. step. (* [comment removed for export] *)
          step. (* [comment removed for export] *) notrap.
          step. (* [comment removed for export] *)
          goto (eapply (JEC (d - 1)%Z)); lia. }
      rd k. (* [comment removed for export] *) pose proof (tx_range bs k) as Rk.
      step. (* [comment removed for export] *)
      if_cases H48.
      { clear H48. apply JDC. lia. }
      clear H48.
      step. (* [comment removed for export] *)
      if_cases Hdp.
      - clear Hdp. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hs.
        + clear Hs. eapply C_22000. exact PINV0.
        + clear Hs. step. (* [comment removed for export] *) eapply C_223a0; [exact PINV0 | lia].
      - clear Hdp. apply JDC. lia. }
    pose proof (tx_range bs 0) as R0. rewrite (txb_tx bs 0).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hs.
    { clear Hs. eapply C_22000. exact PINV0. }
    cond_cleanup Hs. rewrite ?signed_lit in Hs by lia.
    step. (* [comment removed for export] *)
    if_cases He.
    { clear He. eapply C_223a0; [exact PINV0 | lia]. }
    cond_cleanup He.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    goto (eapply (LOOP (Z.to_nat (L - k1)) k1 dc)); lia.
  Qed.
End BLK.
End U_fcd_D.


Module U_fcd_X.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_slow_path_double_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_parse_infnan_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

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
    try destruct_ands PO.

  (* [comment removed for export] *)
  #[using="PRE"] Lemma ufcd_EPI : K_222b8 c.
  Proof. LiaFast.lf_pins (fun (PRE : LiaFast.U) => LiaFast.u0).
    unfold K_222b8. intros lo m F' fc' v' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      FRM' FRL LOSZ FRH ST VAL MU WM.
    pre_facts. unfold from_chars_double_need in ST. cbv delta [from_chars_double_W from_chars_double_need] in MU.
    unfold savesU in FRH.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FRL ST (bv_unsigned sp + -104)%Z. release_frame FRH ST (bv_unsigned sp).
    unfold from_chars_double_post. finish.
    all: try exact VAL. all: try exact FRM'.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE parse_infnan_d_spec"] Lemma ufcd_INF : K_21f40 c.
  Proof. LiaFast.lf_pins (fun (PRE parse_infnan_d_spec : LiaFast.U) => LiaFast.u0).
    unfold K_21f40.
    intros lo m x1 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV HL1.
    pre_facts. open_pinv PINV.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *) rewrite F16.
    step. (* [comment removed for export] *) if_false.
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FRL ST (bv_unsigned sp + -104)%Z. release_frame FRH ST (bv_unsigned sp).
    step. (* [comment removed for export] *)
    call parse_infnan_d_spec.
    { exact TXT. } { lia. } { exact LEN. } { lia. } { exact VAL. } { exact PR1. } { lia. } { lia. }
    rename MI into VAL'.
    unfold from_chars_double_post. finish.
    all: try exact VAL'. all: try exact FRM.
  Qed.

  (* [comment removed for export] *)
  #[using="PRE slow_path_double_spec"] Lemma ufcd_SLOW : K_223a0 c.
  Proof. LiaFast.lf_pins (fun (PRE slow_path_double_spec : LiaFast.U) => LiaFast.u0).
    unfold K_223a0.
    intros lo m x1 x6 x7 x8 x9 x12 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV HL1.
    pre_facts. open_pinv PINV.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    step. (* [comment removed for export] *) setcmp. change (Z.b2z (0 <? 0)%Z) with 0%Z.
    step. (* [comment removed for export] *)
    do 13 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FRL ST (bv_unsigned sp + -104)%Z. release_frame FRH ST (bv_unsigned sp).
    destruct (stk_split _ _ _ (bv_unsigned sp - 2576)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    step. (* [comment removed for export] *)
    call slow_path_double_spec.
    { exact TXT. } { exact LEN. } { lia. } { lia. } { reflexivity. } { exact VAL. } { exact VAL8. }
    { unfold slow_path_double_need. replace (bv_unsigned sp - (704 + 1872))%Z with (bv_unsigned sp - 2576)%Z by lia. exact SThi. }
    { exact AL. }
    { unfold slow_path_double_need. lia. }
    { lia. } { lia. } { lia. } { exact PR1. } { unfold U_FMIN_D. exact PR2. } { exact FRM. }
    { unfold slow_path_double_need. lia. }
    { unfold slow_path_double_need. lia. }
    { lia. }
    match goal with |- _ => idtac end.
    lazymatch goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM' end.
    lazymatch goal with H : stk _ ?mm (bv_unsigned (r_sp c) - slow_path_double_need)%Z _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST' end.
    lazymatch goal with H : rw_cells _ ?mm V _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into VAL' end.
    unfold slow_path_double_need in ST'. replace (bv_unsigned sp - (704 + 1872))%Z with (bv_unsigned sp - 2576)%Z in ST' by lia.
    pose proof (stk_merge _ _ _ _ _ STlo ST' ltac:(lia)) as ST2.
    unfold from_chars_double_post. finish.
    all: try exact VAL'. all: try exact FRM'. all: try exact ST2.
  Qed.
End BLK.
End U_fcd_X.


Module U_fcd_CL.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_22040 : K_22040 c.
  Hypothesis C_22280 : K_22280 c.
  Hypothesis C_222b8 : K_222b8 c.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[using="PRE C_22040 C_22280 C_222b8"] Lemma ufcd_CL : K_22000 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22040 C_22280 C_222b8 : LiaFast.U) => LiaFast.u0).
    unfold K_22040 in C_22040. unfold K_22280 in C_22280. unfold K_222b8 in C_222b8.
    unfold K_22000. intros lo m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. pose proof PINV as PI. open_pinv PI.
    pose proof (bv_unsigned_in_range 64 x6) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed x6) as SQ.
    pose proof (bv_unsigned_in_range 64 x16) as Rw. unfold bv_modulus in Rw.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    assert (PK : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word,
      evt USEGS POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x24244) fc None m (seg_rom USEGS))).
    { intros. eapply C_22280. exact PINV. }
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
        eapply C_22040; [exact PINV | lia]. }
      clear Hqhi.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply PK. }
    cond_cleanup Hfp.
    assert (Q22 : (-22 <= bv_signed x6 <= 22)%Z).
    { rewrite SQ. rewrite ?unsigned_lit_wrap in Hfp.
      destruct (Z.ltb_spec0 (bv_unsigned x6) (2^63)); Z.div_mod_to_equations; lia. }
    clear Hfp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hw53.
    2:{ clear Hw53. eapply C_22040; [exact PINV | lia]. }
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
    assert (TAIL : forall (m' : word -> option byte) (v' : word) (Fq : bvmap 5 word) (fcq : bv 32) (y6 y10 y11 y12 : word),
      frm0 fcq -> rw_cells USEGS m' SP lo -> rw_cells USEGS m' (bv_unsigned sp + -104)%Z (savesU c) ->
      stk USEGS m' (bv_unsigned sp - NEED) SP ->
      rw_cells USEGS m' V [C8 v'] -> munch W m0 m' -> wmono USEGS m0 m' ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 y6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31)
            Fq (Z_to_bv 64 0x24330) fcq None m' (seg_rom USEGS))).
    { intros m' v' Fq fcq y6 y10 y11 y12 FRMq FRL' FRH' ST' VAL' MU' WM'.
      unfold from_chars_double_need in ST'. unfold savesU in FRH'.
      cbv delta [from_chars_double_W from_chars_double_need] in MU'.
      pose proof (rw_cells_bound _ _ _ _ VAL') as Bval'. cbn [cells_size csize Nat.add] in Bval'.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hsgn.
      - clear Hsgn.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_222b8; [exact FRMq | exact FRL' | exact LOSZ | exact FRH' | exact ST' | | exact MU' | exact WM'].
        match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => first [exact H | replace a with V in H by lia; exact H] end.
      - clear Hsgn.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply C_222b8; [exact FRMq | exact FRL' | exact LOSZ | exact FRH' | exact ST' | | exact MU' | exact WM'].
        match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => first [exact H | replace a with V in H by lia; exact H] end. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hneg.
    - cond_cleanup Hneg. rewrite ?signed_lit in Hneg by lia.
      assert (QS : (bv_signed x6 = bv_unsigned x6 - 2^64)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned x6) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.shiftl_mul_pow2 in Hov by lia; rewrite ?unsigned_lit_wrap in Hov; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      lazymatch goal with |- context [Some (Z_to_bv 64 (89008 + ?e)%Z)] =>
        replace (Z_to_bv 64 (89008 + e)%Z) with (Z_to_bv 64 (89008 + 8 * (2^64 - bv_unsigned x6)))
          by (rewrite ?unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) end.
      lazymatch goal with H : pristine _ 65536 139264 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (table_read USEGS _ _ _ _ mm _ _ TBLDU_ok H ltac:(lia) ltac:(cbn; lia) (2^64 - bv_unsigned x6)%Z ltac:(cbn; lia)) as RD end.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      eapply TAIL; [exact FRM | exact FRL | exact FRH | exact ST | | exact MU | exact WM].
      match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => first [exact H | replace a with V in H by lia; exact H] end.
    - cond_cleanup Hneg. rewrite ?signed_lit in Hneg by lia.
      assert (QS : (bv_signed x6 = bv_unsigned x6)%Z) by (rewrite SQ; destruct (Z.ltb_spec0 (bv_unsigned x6) (2^63)); lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.shiftl_mul_pow2 in Hov by lia; rewrite ?unsigned_lit_wrap in Hov; Z.div_mod_to_equations; lia|]. clear Hov.
      step. (* [comment removed for export] *)
      rewrite ?Z.shiftl_mul_pow2 by lia.
      lazymatch goal with |- context [Some (Z_to_bv 64 (89008 + ?e)%Z)] =>
        replace (Z_to_bv 64 (89008 + e)%Z) with (Z_to_bv 64 (89008 + 8 * bv_unsigned x6))
          by (rewrite ?unsigned_lit_wrap; apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) end.
      lazymatch goal with H : pristine _ 65536 139264 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (table_read USEGS _ _ _ _ mm _ _ TBLDU_ok H ltac:(lia) ltac:(cbn; lia) (bv_unsigned x6) ltac:(cbn; lia)) as RD end.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply TAIL; [exact FRM | exact FRL | exact FRH | exact ST | | exact MU | exact WM].
      match goal with H : rw_cells _ _ ?a [C8 _] |- rw_cells _ _ _ [C8 _] => first [exact H | replace a with V in H by lia; exact H] end.
  Qed.
End BLK.
End U_fcd_CL.


Module U_fcd_CF.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_spd_tbl.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_22280 : K_22280 c.
  #[local] Notation Zw z := (Z_to_bv 64 z).

  (* [comment removed for export] *)
  #[using="PRE C_22280"] Lemma ufcd_CF : K_22040 c.
  Proof. LiaFast.lf_pins (fun (PRE C_22280 : LiaFast.U) => LiaFast.u0).
    unfold K_22280 in C_22280.
    unfold K_22040. intros lo m x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 q PINV Hq.
    pre_facts. pose proof PINV as PI. open_pinv PI.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ.
    pose proof (bv_unsigned_in_range 64 x16) as Rw. unfold bv_modulus in Rw.
    assert (PK : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word,
      evt USEGS POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x24244) fc None m (seg_rom USEGS))).
    { intros. eapply C_22280. exact PINV. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (ucf_idx q) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 684) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5472)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    gstep. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 10 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    step. step. step. (* [comment removed for export] *)
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 684)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD1.
    step. (* [comment removed for export] *)
    clear RD1.
    do 9 gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J128 : forall v5 v7 v10 v11 v12 v13 v14 v17 v29 v30 v31 : word,
      evt USEGS POST
        (MS (mkR x1 (Zw SP) gp tp v5 q v7 x8 x9 v10 v11 v12 v13 v14 x15 x16 v17
                 x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 v29 v30 v31)
            F (Zw 0x240ec) fc None m (seg_rom USEGS))).
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
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hnorm.
      - clear Hnorm. (* [comment removed for export] *)
        do 12 gstep. (* [comment removed for export] *)
        (* [comment removed for export] *)
        assert (J200 : forall u6 u10 u11 u12 u13 u14 u17 : word,
          evt USEGS POST
            (MS (mkR x1 (Zw SP) gp tp v5 u6 v7 x8 x9 u10 u11 u12 u13 u14 x15 x16 u17
                     x18 x19 x20 x21 x22 a2 x24 x25 x26 x27 x28 v29 v30 v31)
                F (Zw 0x241c4) fc None m (seg_rom USEGS))).
        { intros.
          do 13 gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hinf.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            apply PK.
          - clear Hinf.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            apply PK. }
        step. (* [comment removed for export] *)
        if_cases Hre.
        + clear Hre. apply J200.
        + clear Hre.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          gstep. (* [comment removed for export] *)
          apply J200.
      - clear Hnorm. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hsh.
        + clear Hsh.
          step. (* [comment removed for export] *)
          do 7 gstep. (* [comment removed for export] *)
          apply PK.
        + clear Hsh.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          apply PK. }
    step. (* [comment removed for export] *)
    if_cases Hlow.
    { clear Hlow. apply J128. }
    clear Hlow.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5472)%Z) by lia.
    replace (Z.lor (16 * bv_signed q + 5472) 8) with (16 * bv_signed q + 5480)%Z
      by (replace (16 * bv_signed q + 5472)%Z with (16 * (bv_signed q + 342))%Z by lia; rewrite lor_16k_8 by lia; lia).
    step. (* [comment removed for export] *)
    if_cases Hov; [cond_cleanup Hov; exfalso; rewrite ?Z.mod_small in Hov by lia; lia|]. clear Hov.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 684)%Z) by lia.
    replace (Z.lor (2 * bv_signed q + 684) 1) with (2 * bv_signed q + 685)%Z
      by (replace (2 * bv_signed q + 684)%Z with (2 * (bv_signed q + 342))%Z by lia; rewrite lor_2k_1 by lia; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (2 * bv_signed q + 685)%Z) by lia. rewrite ?(Z.shiftl_mul_pow2 _ 3) by lia.
    replace (Zw ((2 * bv_signed q + 685) * 2 ^ 3)) with (Zw (16 * bv_signed q + 5480)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (16 * bv_signed q + 5480)%Z) by lia.
    pose proof (table_read USEGS _ _ _ _ m _ _ TBL5_ok PR1 ltac:(lia) ltac:(rewrite TBL5_length; cbn; lia)
                  (2 * bv_signed q + 685)%Z ltac:(rewrite TBL5_length; cbn; lia)) as RD2.
    step. (* [comment removed for export] *)
    clear RD2.
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    apply J128.
  Qed.
End BLK.
End U_fcd_CF.


Module U_fcd_PK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac Wdc_tac Ubsan_chk U_fcd_common.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_commonT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : ufcd_pre c.
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
  #[local] Notation SP := (bv_unsigned (r_sp c) + -128)%Z.
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
    destruct H as (TXT & FRL & LOSZ & FRH & ST & VAL & PR1 & PR2 & MU & WM); unfold savesU in FRH;
    unfold from_chars_double_need in ST; unfold U_FMIN in PR2;
    cbv beta delta [from_chars_double_W from_chars_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac mk_pinv :=
    lazymatch goal with |- pinv _ ?lo ?m =>
    lazymatch goal with TXT : bytes_at _ m _ _, FRL : rw_cells _ m (bv_unsigned (r_sp c) + -128)%Z lo,
                        FRH : rw_cells _ m (bv_unsigned (r_sp c) + -104)%Z _, ST : stk _ m _ _,
                        VAL : rw_cells _ m (bv_unsigned (r_a2 c)) _, PR1 : pristine m 65536 139264,
                        PR2 : pristine m _ _, MU : munch _ _ m, WM : wmono _ _ m |- _ =>
      split; [exact TXT|]; split; [exact FRL|]; split; [reflexivity|]; split; [exact FRH|];
      split; [unfold from_chars_double_need; exact ST|]; split; [exact VAL|]; split; [exact PR1|];
      split; [unfold U_FMIN; exact PR2|]; split; [cbv beta delta [from_chars_double_W from_chars_double_need]; exact MU | exact WM]
    end end.

  (* [comment removed for export] *)
  #[local] Ltac notrap :=
    let Hc := fresh "Hc" in if_cases Hc;
    [ exfalso; cond_cleanup Hc; rewrite ?unsigned_lit_wrap in Hc; repeat (rewrite Z.mod_small in Hc by lia);
      rewrite ?signed_lit in Hc by lia; first [lia | Z.div_mod_to_equations; lia]
    | clear Hc ].

  (* [comment removed for export] *)
  #[local] Ltac dp46 := replace (Z.land (bv_unsigned (r_a4 c)) 255) with 46%Z by (rewrite (pre_A4 c PRE); reflexivity).

  (* [comment removed for export] *)
  #[local] Ltac rd k :=
    let RD := fresh "RD" in
    lazymatch goal with H : bytes_at _ _ (bv_unsigned (r_a0 c)) _ |- _ => txt_rd H k RD end;
    step; clear RD; try fold_tx (r_bs c) k.

  Hypothesis C_222b8 : K_222b8 c.

  (* [comment removed for export] *)
  #[using="PRE C_222b8"] Lemma ufcd_PK : K_22280 c.
  Proof. LiaFast.lf_pins (fun (PRE C_222b8 : LiaFast.U) => LiaFast.u0).
    unfold K_22280. unfold K_222b8 in C_222b8.
    intros lo m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 PINV.
    pre_facts. open_pinv PINV.
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    do 10 gstep. (* [comment removed for export] *) gen_reg (11:reg).
    step. (* [comment removed for export] *)
    do 3 gstep. (* [comment removed for export] *)
    eapply C_222b8; [exact FRM | exact FRL | exact LOSZ | exact FRH | exact ST | exact VAL | exact MU | exact WM].
  Qed.
End BLK.
End U_fcd_PK.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_parse_infnan_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_slow_path_double_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_fcd_common OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_A2 OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_B OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_C OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_D OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_X OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_CL OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_CF OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_fcd_PK.
Import ListNotations.

Module U_parse_infnan_d.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Wbig_tac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_from_chars_double.U_parse_infnan_d_stmt.
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

  (* [comment removed for export] *)
  Definition nan_loop_ok (j : nat) : Prop :=
    forall (i q : Z) (x5 x6 x10 : word) (F' : bvmap 5 word) (m' : word -> option byte) (v' : word),
      (Z.to_nat (bv_unsigned a1 - q) <= j)%nat ->
      (q = bv_unsigned a0 + i)%Z -> (0 <= i)%Z -> (q < bv_unsigned a1)%Z ->
      bytes_at USEGS m' (bv_unsigned a0) bs ->
      rw_cells USEGS m' (bv_unsigned a2) [C8 v'] ->
      munch W m m' -> wmono USEGS m m' ->
      evt USEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 (Z_to_bv 64 41) (Z_to_bv 64 26) (Z_to_bv 64 (-1)) (Z_to_bv 64 q)
                 (Z_to_bv 64 95) (Z_to_bv 64 9)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x24490) fc None m' (seg_rom USEGS)).

  (* [comment removed for export] *)
  #[using="SEP RO2 Ra1"] Lemma nan_adv : forall j, nan_loop_ok j ->
    forall (i q : Z) (x5 x6 x10 : word) (F' : bvmap 5 word) (m' : word -> option byte) (v' : word),
      (Z.to_nat (bv_unsigned a1 - (q + 1)) <= j)%nat ->
      (q = bv_unsigned a0 + i)%Z -> (0 <= i)%Z -> (q < bv_unsigned a1)%Z ->
      bytes_at USEGS m' (bv_unsigned a0) bs ->
      rw_cells USEGS m' (bv_unsigned a2) [C8 v'] ->
      munch W m m' -> wmono USEGS m m' ->
      evt USEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 (Z_to_bv 64 41) (Z_to_bv 64 26) (Z_to_bv 64 (-1)) (Z_to_bv 64 q)
                 (Z_to_bv 64 95) (Z_to_bv 64 9)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x244b0) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    intros j IH i q x5 x6 x10 F' m' v' MEAS Hq Hi Hlt DATA OBJ MU WM.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He.
    - cond_cleanup He.
      eapply (IH (i + 1)%Z (q + 1)%Z); try eassumption; try lia.
    - cond_cleanup He.
      step. step. step. step. (* [comment removed for export] *)
      fin.
  Qed.

  #[using="LEN LT SEP RO2 Ra1"] Lemma nan_loop : forall j, nan_loop_ok j.
  Proof. LiaFast.lf_pins (fun (LEN LT SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold nan_loop_ok; intros i q x5 x6 x10 F' m' v' MEAS Hq Hi Hlt DATA OBJ MU WM.
    - exfalso. lia.
    - pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
      destruct (nth_error bs (Z.to_nat i)) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      pose proof (u8ro_read USEGS m' (bv_unsigned a0) bs i c _ DATA Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_cases Hp.
      { clear Hp.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        step. step. step. step. step. (* [comment removed for export] *)
        fin. }
      clear Hp.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H1.
      { clear H1. eapply (nan_adv j IH i q); try eassumption; try lia. }
      clear H1.
      step. (* [comment removed for export] *)
      if_cases H2.
      { clear H2. eapply (nan_adv j IH i q); try eassumption; try lia. }
      clear H2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H4.
      { clear H4. step. step. step. step. fin. }
      clear H4. eapply (nan_adv j IH i q); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LEN LT SEP RO2 Ra1"] Lemma nan_tail : forall (c0 : byte) (p x5 x6 x10 x13 x16 x17 : word) (d : Z) (F' : bvmap 5 word),
      (d = 0 \/ d = 1)%Z -> (bv_unsigned p = bv_unsigned a0 + d)%Z -> (3 <= bv_unsigned a1 - bv_unsigned p)%Z ->
      bytes_at USEGS m (bv_unsigned a0) bs -> rw_cells USEGS m (bv_unsigned a2) [C8 vold] ->
      evt USEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 a2 x13 (zxb c0) p x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x24454) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN LT SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    intros c0 p x5 x6 x10 x13 x16 x17 d F' Hd Hp H3 DATA OBJ.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl USEGS m) as WM.
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
    pose proof (u8ro_read USEGS _ (bv_unsigned a0) bs (d + 3) b3 _ DATA Hb3 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E4.
    { clear E4. step. step. step. step. fin. }
    clear E4.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E5.
    { clear E5. step. step. step. step. fin. }
    cond_cleanup E5.
    step. step. step. step. step. (* [comment removed for export] *)
    eapply (nan_loop _ (d + 4)%Z (bv_unsigned p + 4)%Z); try eassumption; try lia. apply Nat.le_refl.
  Qed.

  (* [comment removed for export] *)
  #[using="a1 LEN SEP RO2"] Lemma inf_tail : forall (c0 : byte) (p x5 x6 x10 x11 x13 x16 x17 : word) (d : Z) (F' : bvmap 5 word),
      (d = 0 \/ d = 1)%Z -> (bv_unsigned p = bv_unsigned a0 + d)%Z ->
      bytes_at USEGS m (bv_unsigned a0) bs -> rw_cells USEGS m (bv_unsigned a2) [C8 vold] -> pristine m 0x10000 0x22000 ->
      evt USEGS POST
        (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 x11 a2 x13 (zxb c0) p x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 0x2455c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (a1 LEN SEP RO2 : LiaFast.U) => LiaFast.u0).
    intros c0 p x5 x6 x10 x11 x13 x16 x17 d F' Hd Hp DATA OBJ PR.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl USEGS m) as WM.
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
      lazymatch goal with |- evt _ _ (MS _ (bvmap_set 15 ?v _) _ _ _ _ _) => remember v as fv eqn:Hfv; clear Hfv end.
      step. (* [comment removed for export] *)
      step. step. step. fin.
    - step. (* [comment removed for export] *)
      rewrite (zxb_off_nez c0 (-45)) by lia.
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ (bvmap_set 15 ?v _) _ _ _ _ _) => remember v as fv eqn:Hfv; clear Hfv end.
      step. (* [comment removed for export] *)
      step. step. step. fin.
  Qed.

  (* [comment removed for export] *)
  #[using="LEN LT SEP RO2 Ra1"] Lemma pinf_main : forall (c0 : byte) (p x13 : word) (d : Z) (F : bvmap 5 word),
      (d = 0 \/ d = 1)%Z -> (bv_unsigned p = bv_unsigned a0 + d)%Z -> (bv_unsigned p <= bv_unsigned a1)%Z ->
      bytes_at USEGS m (bv_unsigned a0) bs -> rw_cells USEGS m (bv_unsigned a2) [C8 vold] -> pristine m 0x10000 0x22000 ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 x13 (zxb c0) p a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x243e0) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN LT SEP RO2 Ra1 : LiaFast.U) => LiaFast.u0).
    intros c0 p x13 d F Hd Hp Hple DATA OBJ PR.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl USEGS m) as WM.
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
    pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 1) b1 _ DATA Hb1 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    pose proof (u8ro_read USEGS m (bv_unsigned a0) bs d b0 _ DATA Hb0 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 2) b2 _ DATA Hb2 ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *) clear RD.
    do 9 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E1.
    { clear E1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases E7.
      { clear E7. step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *) eapply (inf_tail c0 p); try eassumption; lia. }
      cond_cleanup E7.
      step. step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_not_taken.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
      destruct (nth_error bs (Z.to_nat (d + 3))) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
      destruct (nth_error bs (Z.to_nat (d + 4))) as [b4|] eqn:Hb4. 2:{ exfalso. apply nth_error_None in Hb4. lia. }
      destruct (nth_error bs (Z.to_nat (d + 5))) as [b5|] eqn:Hb5. 2:{ exfalso. apply nth_error_None in Hb5. lia. }
      destruct (nth_error bs (Z.to_nat (d + 6))) as [b6|] eqn:Hb6. 2:{ exfalso. apply nth_error_None in Hb6. lia. }
      destruct (nth_error bs (Z.to_nat (d + 7))) as [b7|] eqn:Hb7. 2:{ exfalso. apply nth_error_None in Hb7. lia. }
      pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 4) b4 _ DATA Hb4 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 3) b3 _ DATA Hb3 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 5) b5 _ DATA Hb5 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 6) b6 _ DATA Hb6 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      step. step. (* [comment removed for export] *)
      pose proof (u8ro_read USEGS m (bv_unsigned a0) bs (d + 7) b7 _ DATA Hb7 ltac:(lia) eq_refl) as RD.
      step. clear RD.
      do 15 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases E8.
      { clear E8. step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *) eapply (inf_tail c0 p); try eassumption; lia. }
      clear E8. step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      eapply (inf_tail c0 p); try eassumption; lia. }
    clear E1. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases E2.
    { clear E2. step. step. fin. }
    clear E2.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
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
  unfold parse_infnan_d_stmt. intros until vold. intros DATA NZ LEN LT OBJ PR SEP RO2.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
  destruct bs as [|c0 bs0]. { cbn [length] in LEN. lia. }
  pose proof (bv_unsigned_in_range 8 c0) as Rc0. unfold bv_modulus in Rc0. cbn in Rc0.
  step. (* [comment removed for export] *)
  if_not_taken.
  pose proof (u8ro_read USEGS m (bv_unsigned a0) (c0 :: bs0) 0 c0 _ DATA eq_refl ltac:(lia) eq_refl) as RD.
  step. (* [comment removed for export] *)
  clear RD.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hc.
  - clear Hc. step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *)
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
      * clear Hpl. step. (* [comment removed for export] *) step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *)
        eapply pinf_main; [exact LEN | exact LT | exact SEP | exact RO2 | lia | right; reflexivity
                          | apply unsigned_lit; lia | rewrite unsigned_lit by lia; lia | exact DATA | exact OBJ | exact PR].
Qed.
End U_parse_infnan_d.

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
  assert (PRE : ufcd_pre c).
  { constructor; cbn; try assumption; try reflexivity.
    unfold U_fcd_common.fmt. cbn. rewrite unsigned_lit by lia. exact Hfmt. }
  pose proof (ufcd_EPI c PRE) as K2B8.
  pose proof (ufcd_INF c PRE PINF) as KF40.
  pose proof (ufcd_SLOW c PRE SLOW) as K3A0.
  pose proof (ufcd_PK c PRE K2B8) as K280.
  pose proof (ufcd_CF c PRE K280) as K040.
  pose proof (ufcd_CL c PRE K040 K280 K2B8) as K000.
  pose proof (ufcd_D c PRE K000 K3A0) as KE6C.
  pose proof (ufcd_C c PRE KE6C KF40) as KB04.
  pose proof (ufcd_B c PRE KB04 KF40) as K8AC.
  pose proof (ufcd_A2 c PRE K8AC) as K610.
  exact (ufcd_A c PRE K610 KF40 K2B8).
Qed.

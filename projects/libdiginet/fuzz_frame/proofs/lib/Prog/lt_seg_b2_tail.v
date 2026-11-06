(* The two tails of the walk of fuzz_frame's LLVMFuzzerTestOneInput from 0x12d04 (lt_seg_b2.v):
   - 0x12e6c: a refused frame. The code is stored at w (sw a1, 0(sp)), then check_parse_refusal (r, w),
     then mv a0, s0 and jal free;
   - 0x12e30: a frame read as SPEC_OK. The body sum is stored at w + 72, then check_parse_refusal (r, w),
     check_parse_fields (buf, f, w), and mv a0, sp; jal check_round_trip.
   check_parse_refusal and check_parse_fields are taken through their contracts (Section hypotheses).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_parse_c check_parse_refusal_c
  check_parse_fields_c FrameBytes lt_seg_b2_lib.
Import ListNotations.
Open Scope Z_scope.

Section Tail.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.

(* check_parse_refusal, with its arguments given by equations. *)
Lemma cpr_at : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w lo : Z) (b : list byte),
    a0 = Z_to_bv 64 (fr_code b) -> a1 = Z_to_bv 64 w ->
    ro_cells rsegs m w [C4 (Z_to_bv 64 (fr_code b))] ->
    w + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= w ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ea4) fc None m (seg_rom rsegs)).
Proof.
  intros. subst. pose proof CPR as C. unfold check_parse_refusal_contract, CHECK_PARSE_REFUSAL, CPR_STACK in C.
  apply C; assumption.
Qed.

(* check_parse_fields, with its arguments given by equations. *)
Lemma cpf_at : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f w lo : Z) (b fj : list byte),
    a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 w ->
    fr_code b = 0 -> f <> 0 ->
    bytes_at rsegs m buf b ->
    ro_cells rsegs m f (parse_cells buf b fj) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    buf + Z.of_nat (length b) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= buf ->
    f + 64 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= f ->
    w + 80 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= w ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12eec) fc None m (seg_rom rsegs)).
Proof.
  intros. subst. pose proof CPF as C. unfold check_parse_fields_contract, CHECK_PARSE_FIELDS, CPF_STACK in C.
  eapply C; eassumption.
Qed.

(* 0x12e6c: the refused frame. *)
Lemma b2_refuse :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 x : word) (cs : list cell),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    mem_inv rsegs m -> munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (bv_unsigned sp) (C4 x :: cs) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    a1 = Z_to_bv 64 (fr_code b) ->
    evt rsegs (b2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf b x1 x2 x3 x4)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code b)) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lo buf b
    x1 x2 x3 x4 x cs ST LO SPB MI MU WM W SV ->.
  pose proof (u64_range sp) as Rsp.
  (* sw a1, 0(sp): w->code *)
  pose proof (rw_cells_store_ok_at rsegs m (bv_unsigned sp) _ 0 (C4 x) 4 sp W eq_refl eq_refl
    ltac:(unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self)) as HS.
  step. clear HS. sp_store_fix.
  (* check_parse_refusal (r, w) *)
  do 3 step.
  b2_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply cpr_at with (w := bv_unsigned sp) (b := b) (lo := lo); try prem | post_call rsegs mm ]).
  all: try (eapply rw_hd; eassumption).
  (* free (buf) *)
  do 2 step.
  apply evt_done. unfold b2_post. right. do 17 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ _))); eassumption.
Qed.

(* 0x12e30: the frame read as SPEC_OK, with the fields at w and the body sum in a2. *)
Lemma b2_ok :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 : word),
    fr_code b = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    mem_inv rsegs m -> munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m0 m -> wmono rsegs m0 m ->
    0 <= buf -> buf + Z.of_nat (length b) <= lo ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m (bv_unsigned sp) (w_cells buf b (Z_to_bv 64 0)) ->
    rw_cells rsegs m (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    a2 = Z_to_bv 64 (sum_bytes (fr_body b)) ->
    evt rsegs (b2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf b x1 x2 x3 x4)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code b)) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e30) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lo buf b
    x1 x2 x3 x4 C0 ST LO SPB MI MU WM BUF BL BB W PF SV ->.
  pose proof (u64_range sp) as Rsp.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  unfold w_cells in W.
  (* sh a2, 0x48(sp): w->body_sum *)
  step.
  (* check_parse_refusal (r, w) *)
  do 3 step.
  b2_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply cpr_at with (w := bv_unsigned sp) (b := b) (lo := lo); try prem | post_call rsegs mm ]).
  all: try (rewrite C0; eapply rw_hd; eassumption).
  (* check_parse_fields (buf, f, w) *)
  do 4 step.
  b2_curmem ltac:(fun mm => pose proof (spec_of_w mm _ buf b W) as WS).
  b2_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply cpf_at with (buf := buf) (f := bv_unsigned sp + 80) (w := bv_unsigned sp) (b := b)
        (fj := repeat (b8 0) 64) (lo := lo); try prem | post_call rsegs mm ]).
  (* mv a0, sp; jal check_round_trip *)
  do 2 step.
  apply evt_done. unfold b2_post. left. split; [exact C0|].
  do 17 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); prem.
Qed.

End Tail.

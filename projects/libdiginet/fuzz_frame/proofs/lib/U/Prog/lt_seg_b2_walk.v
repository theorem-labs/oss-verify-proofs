(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_top.v, with its module paths changed; 465 of its 529 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/Prog/LLVMFuzzerTestOneInput.v, with its module names and addresses changed; 23 of its 51 lines of code are new or changed and 501 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/U/Prog/lt_seg_b2.v; 296 of its 325 lines of code are new or changed and 22 lines of the source are left out. *)
(* the walk of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.ubsan from the return of the second memset to the call of check_round_trip or of free, on Exec.evt. *)
(* LLVMFuzzerTestOneInput in fuzz_frame.ubsan, 0x12dc8-0x13004: the inlined spec_read_frame (fuzz/spec.h:199-223)
   of the frame bytes b at buf into the struct spec_frame w at sp, then check_parse_refusal (r, w) (0x12fa4), the
   test of w.code (0x12fac), and on SPEC_OK check_parse_fields (buf, f, w) (0x12fbc) and the call of
   check_round_trip (0x12fc4); else the call of free (0x12fd8). The two checks are taken through their contracts
   (Section hypotheses). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_parse_c check_parse_refusal_c
  check_parse_fields_c CheckStackU FrameBytes lt_seg_b2_lib.
Import ListNotations.
Open Scope Z_scope.

(* The post of lt_b2, as a name. *)
Definition b2_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (buf : Z) (b : list byte) (x1 x2 x3 x4 : word) : machine_state -> Prop :=
  fun ms' =>
         (fr_code b = 0 /\
          exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12fc8) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' sp a1' a2' a3' a4' a5' a6'
                          a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x131e4) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            bytes_at rsegs m' buf b /\
            ro_cells rsegs m' (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) /\
            ro_cells rsegs m' (bv_unsigned sp) (spec_cells buf b) /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]) \/
         (exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12fdc) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' (Z_to_bv 64 buf) a1' a2' a3'
                          a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x14dec) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]).

(* A store at sp itself (sw a1, 0(sp)): the step leaves the address as the word sp. *)
Ltac b2_st_sp W :=
  lazymatch type of W with
  | rw_cells _ ?mm (bv_unsigned ?sp) (?c :: _) =>
      let HS := fresh "HS" in
      pose proof (rw_cells_store_ok_at rsegs mm (bv_unsigned sp) _ 0 c 4 sp W eq_refl eq_refl
        ltac:(unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self)) as HS;
      step; clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
          replace (write_to_mem m a bs) with (write_to_mem m (wa (bv_unsigned a + Z.of_nat 0)) bs)
            by (f_equal; unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; apply Z_to_bv_lit_self);
          mem_after_store
      end
  end.

(* A load at sp itself (lw a0, 0(sp)). *)
Ltac b2_ld_sp W :=
  lazymatch type of W with
  | rw_cells _ ?mm (bv_unsigned ?sp) (?c :: _) =>
      let HR := fresh "HRsp" in
      pose proof (rw_cells_read_at rsegs mm (bv_unsigned sp) _ 0 c 4 sp W eq_refl eq_refl
        ltac:(unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self)) as HR;
      step; clear HR
  end.

Section B2.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.

(* 0x12f98-0x12fa4: sw a1, 0(sp) (w.code), then check_parse_refusal (s1, sp); back at 0x12fa8. *)
Lemma b2_cpr :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo buf : Z) (b : list byte)
         (x : word) (cs : list cell),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 -> mem_inv rsegs m ->
    rw_cells rsegs m (bv_unsigned sp) (C4 x :: cs) ->
    a1 = Z_to_bv 64 (fr_code b) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12fa8) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code b)) a0' a1'
                       a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x12fa8) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (bv_unsigned sp) (C4 (Z_to_bv 64 (fr_code b)) :: cs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code b)) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f98) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo buf b
    x cs ST LO SPB SPA MI W ->.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  b2_st_sp W.
  step. step. step.
  eapply evt_cut.
  { eapply evt_eq; [ | eapply CPR with (w := bv_unsigned sp) (b := b) (lo := lo) ].
    1: (rewrite (Z_to_bv_lit_self sp); reflexivity).
    - apply b2_mod16_8. exact SPA.
    - eapply b2_rw_hd. exact W.
    - unfold U_CPR_STACK. lia.
    - exact ST.
    - unfold U_CPR_STACK. lia.
    - exact MI. }
  lazymatch goal with H : mem_inv rsegs ?mm |- _ => unfold U_CPR_STACK; post_call rsegs mm end.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.

(* 0x12f98: a refused frame (w.code is -2, -3 or -4): check_parse_refusal, lw a0, 0(sp); bnez (0x12fac) to
   0x12fd4, mv a0, s0; jal free. *)
Lemma b2_bad :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 x : word) (cs : list cell),
    fr_code b <> 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (bv_unsigned sp) (C4 x :: cs) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    a1 = Z_to_bv 64 (fr_code b) ->
    evt rsegs (b2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf b x1 x2 x3 x4)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code b)) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f98) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lo buf b
    x1 x2 x3 x4 x cs NZ ST LO SPB SPA MI MU WM W SV E1.
  pose proof (u64_range sp) as Rsp.
  eapply evt_cut; [ eapply b2_cpr; [exact ST | exact LO | exact SPB | exact SPA | exact MI | exact W | exact E1]
                  | post_call rsegs m ].
  rename POST into W.
  destruct (fr_code_cases b) as [C|[C|[C|C]]]; [contradiction | ..]; rewrite C in W.
  all: b2_ld_sp W; step; b2_br_vm true; step; step.
  all: apply evt_done; unfold b2_post; right; do 17 eexists; split; [reflexivity|].
  all: refine (conj _ (conj _ (conj _ _))); eassumption.
Qed.

(* 0x12f98: a frame with w.code SPEC_OK: check_parse_refusal, lw a0, 0(sp); bnez (not taken), then
   check_parse_fields (buf, sp + 0x50, sp) (0x12fbc), mv a0, sp; jal check_round_trip. *)
Lemma b2_ok :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 x : word),
    fr_code b = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m0 m -> wmono rsegs m0 m ->
    0 <= buf -> buf + Z.of_nat (length b) <= lo ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m (bv_unsigned sp) (C4 x :: tl (spec_cells buf b)) ->
    rw_cells rsegs m (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    a1 = Z_to_bv 64 (fr_code b) ->
    evt rsegs (b2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf b x1 x2 x3 x4)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code b)) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f98) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lo buf b
    x1 x2 x3 x4 x C0 ST LO SPB SPA MI MU WM B0 BL BB W PF SV E1.
  pose proof (u64_range sp) as Rsp.
  eapply evt_cut; [ eapply b2_cpr; [exact ST | exact LO | exact SPB | exact SPA | exact MI | exact W | exact E1]
                  | post_call rsegs m ].
  rename POST into W. rewrite C0 in W.
  b2_ld_sp W. step. b2_br_vm false.
  step. step. step. step.
  eapply evt_cut.
  { eapply evt_eq; [ | eapply CPF with (f := bv_unsigned sp + 80) (w := bv_unsigned sp) (buf := buf) (b := b)
                                       (fj := repeat (b8 0) 64) (lo := lo) ].
    1: (rewrite (Z_to_bv_lit_self sp); reflexivity).
    - exact C0.
    - lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - apply b2_mod16_8. exact SPA.
    - exact BB.
    - apply b2_rw_ro. exact PF.
    - exact (b2_rw_ro _ _ _ W).
    - eassumption.
    - unfold U_CPF_STACK. lia.
    - unfold U_CPF_STACK. lia.
    - unfold U_CPF_STACK. lia.
    - unfold U_CPF_STACK. lia.
    - assumption. }
  lazymatch goal with H : mem_inv rsegs ?mm |- _ => unfold U_CPF_STACK; post_call rsegs mm end.
  step. step.
  apply evt_done. unfold b2_post. left. split; [exact C0|]. do 17 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); try eassumption.
  - apply b2_rw_ro. exact PF.
  - exact (b2_rw_ro _ _ _ W).
Qed.

(* The 80 zero bytes at w, cut at the fields of struct spec_frame. *)
Definition b2_w0 : list cell :=
  [ C4 (Z_to_bv 64 0); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
    C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0);
    C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (b8 0); C1 (b8 0); CB 6 (repeat (b8 0) 6);
    C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 6 (repeat (b8 0) 6) ].

Lemma b2_w0_shape : forall m A, rw_cells rsegs m A [CB 80 (repeat (b8 0) 80)] -> rw_cells rsegs m A b2_w0.
Proof.
  intros m A W. eapply b2_rw_same; [exact W | vm_compute; repeat split | vm_compute; reflexivity | reflexivity].
Qed.

(* The cells the walk leaves at w, with the 64-bit body sum s at offset 72: spec_cells, since the sh at 0x13000
   stores the low 16 bits of s. *)
Lemma b2_spec_tail : forall m A x buf b s,
  rw_cells rsegs m A
    [C4 x; CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (buf + 6));
     C2 (Z_to_bv 64 (fr_ethertype b)); C2 (Z_to_bv 64 (fr_numbytes b)); C2 (Z_to_bv 64 (fr_sum b));
     C2 (Z_to_bv 64 (fr_retry b)); C4 (Z_to_bv 64 (fr_send b)); C4 (Z_to_bv 64 (fr_ack b));
     C1 (nth 28 b (b8 0)); C1 (nth 29 b (b8 0)); CB 6 (repeat (b8 0) 6); C8 (Z_to_bv 64 (buf + 30));
     C8 (Z_to_bv 64 (fr_body_len b)); C8 (Z_to_bv 64 (fr_pad_len b)); C2 (Z_to_bv 64 s);
     CB 6 (repeat (b8 0) 6)] ->
  0 <= s < 2 ^ 64 -> s mod 2 ^ 16 = fr_body_sum b ->
  rw_cells rsegs m A (C4 x :: tl (spec_cells buf b)).
Proof.
  intros m A x buf b s W Hs Hm. eapply b2_rw_same; [exact W | | | reflexivity].
  - cbn [cells_wf cell_wf tl spec_cells]. rewrite !repeat_length. tauto.
  - cbn [cells_bytes cbytes tl spec_cells]. rewrite <- Hm. rewrite (b2_le2_mod s Hs).
    unfold fr_cmd, fr_ncmds, at8. rewrite !b8_bz. reflexivity.
Qed.

Lemma b2_main :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv rsegs m ->
    s0 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 (fr_code b) -> s2 = Z_to_bv 64 (Z.of_nat (length b)) ->
    Z.of_nat (length b) < 2 ^ 26 -> 4096 <= buf -> buf + Z.of_nat (length b) <= lo ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 (repeat (b8 0) 80)] ->
    rw_cells rsegs m (bv_unsigned sp + 80)
      (if fr_code b =? 0 then parse_cells buf b (repeat (b8 0) 64) else [CB 64 (repeat (b8 0) 64)]) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    evt rsegs (b2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m buf b x1 x2 x3 x4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12dc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo buf b
    x1 x2 x3 x4 ST LO SPB SPA MI -> -> -> NL BUF4 BL BB W PF SV.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply b2_w0_shape in W. unfold b2_w0 in W.
  step. step.
  destruct (Nat.ltb_spec (length b) 30) as [L30|L30].
  { b2_br false. step. step.
    eapply b2_bad; try eassumption.
    - rewrite (b2_code_short b L30). lia.
    - rewrite (b2_code_short b L30). reflexivity. }
  b2_br true.
  step. step. b2_br false. step. step. b2_br false.
  b2_rdb BB 12. step. clear HR. b2_rdb BB 13. step. clear HR.
  step. step.
  rewrite (b2_r16 b 12). change (be16 b 12) with (fr_ethertype b).
  assert (RE : 0 <= fr_ethertype b < 2 ^ 16) by apply be16_range.
  step. step. step. step.
  destruct (Z.eqb_spec (fr_ethertype b) 0x885f) as [EE|EE].
  2: { b2_br true. step.
       eapply b2_bad; try eassumption.
       - rewrite (b2_code_eth b L30 EE). lia.
       - rewrite (b2_code_eth b L30 EE). reflexivity. }
  b2_br false.
  step. step. b2_br false. step. b2_br false.
  b2_rdb BB 14. step. clear HR. b2_rdb BB 15. step. clear HR.
  step. step. step.
  rewrite (b2_r16 b 14). change (be16 b 14) with (fr_numbytes b).
  assert (RN : 0 <= fr_numbytes b < 2 ^ 16) by apply be16_range.
  step. step. step.
  destruct (Z.ltb_spec (fr_numbytes b) 16) as [N16|N16].
  { b2_br true.
    eapply b2_bad; try eassumption.
    - rewrite (b2_code_len b L30 EE (or_introl N16)). lia.
    - rewrite (b2_code_len b L30 EE (or_introl N16)). reflexivity. }
  b2_br false.
  step. step.
  destruct (Z.ltb_spec (Z.of_nat (length b) - 14) (fr_numbytes b)) as [NL2|NL2].
  { b2_br true.
    eapply b2_bad; try eassumption.
    - rewrite (b2_code_len b L30 EE (or_intror NL2)). lia.
    - rewrite (b2_code_len b L30 EE (or_intror NL2)). reflexivity. }
  b2_br false.
  assert (C0 : fr_code b = 0) by (apply b2_code_zero; lia).
  replace (fr_code b =? 0) with true in PF by (rewrite C0; reflexivity). cbv iota in PF.
  (* dst, src *)
  step. step. step. b2_br false.
  step. step. step. step. b2_br false. step. b2_br false.
  (* sum *)
  b2_rdb BB 16. step. clear HR. b2_rdb BB 17. step. clear HR.
  step. step.
  rewrite (b2_r16 b 16). change (be16 b 16) with (fr_sum b).
  assert (RS : 0 <= fr_sum b < 2 ^ 16) by apply be16_range.
  step. step. step. b2_br false.
  step. step. step. b2_br false. step. step. step. b2_br false.
  (* send *)
  b2_rdb BB 19. step. clear HR. b2_rdb BB 18. step. clear HR.
  b2_rdb BB 20. step. clear HR. b2_rdb BB 21. step. clear HR.
  step. step. step. step. step. step.
  rewrite (b2_r32 b 18). change (be32 b 18) with (fr_send b).
  assert (RSd : 0 <= fr_send b < 2 ^ 32) by apply be32_range.
  step. step. step. b2_br false.
  step. step. step. b2_br false. step. step. step. b2_br false.
  (* ack *)
  b2_rdb BB 23. step. clear HR. b2_rdb BB 22. step. clear HR.
  b2_rdb BB 24. step. clear HR. b2_rdb BB 25. step. clear HR.
  step. step. step. step. step. step.
  rewrite (b2_r32 b 22). change (be32 b 22) with (fr_ack b).
  assert (RA : 0 <= fr_ack b < 2 ^ 32) by apply be32_range.
  step. step. step. b2_br false. step. b2_br false.
  (* retry *)
  b2_rdb BB 26. step. clear HR. b2_rdb BB 27. step. clear HR.
  step. step.
  rewrite (b2_r16 b 26). change (be16 b 26) with (fr_retry b).
  assert (RR : 0 <= fr_retry b < 2 ^ 16) by apply be16_range.
  step. step. step. b2_br false.
  (* cmd, ncmds *)
  b2_rdb BB 28. step. clear HR. step. step. rewrite le1_zxb. mem_after_store. step. b2_br false.
  b2_rdb BB 29. step. clear HR. step. step. rewrite le1_zxb. mem_after_store. step. b2_br false.
  (* body, body_len, pad_len *)
  step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length b) + -14)) by lia. rewrite (unsigned_lit (fr_numbytes b)) by lia.
  replace (Z.of_nat (length b) + -14 - fr_numbytes b) with (fr_pad_len b) by (unfold fr_pad_len, fr_body_len; lia).
  change (fr_numbytes b + -16) with (fr_body_len b).
  assert (RBL : 0 <= fr_body_len b <= Z.of_nat (length b) - 30) by (unfold fr_body_len; lia).
  assert (LBL : Z.of_nat (length (fr_body b)) = fr_body_len b)
    by (rewrite (length_fr_body b C0); rewrite Z2Nat.id by lia; reflexivity).
  pose proof (sum_bytes_range (fr_body b)) as SBR.
  step. step. step. step.
  destruct (Z.eqb_spec (fr_body_len b) 0) as [BZ|BZ].
  - (* empty body: 0x12ff8 *)
    b2_br true. step. step. step. step.
    eapply b2_ok; try eassumption.
    + lia.
    + eapply b2_spec_tail; [exact W | lia |].
      unfold fr_body_sum, fr_body. rewrite BZ. reflexivity.
    + rewrite C0. reflexivity.
  - (* the loop *)
    b2_br false. step. step. step.
    eapply b2_loop with (A := buf + 30) (n := fr_body_len b) (l := fr_body b)
      (i := 0%nat) (r := Nat.pred (length (fr_body b))).
    + exact (b2_bytes_sub _ buf b 30 (Z.to_nat (fr_body_len b)) BB ltac:(lia)).
    + lia.
    + rewrite (unsigned_lit (buf + 30)) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia.
    + lia.
    + lia.
    + intros a5'. step. step. step. step.
      eapply b2_ok; try eassumption.
      * lia.
      * eapply b2_spec_tail; [exact W | lia | reflexivity].
      * rewrite C0. reflexivity.
Qed.

End B2.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the entry of LLVMFuzzerTestOneInput (plain image, 0x12cd4) for 1 <= size < 2^26
   up to the call of malloc in the inlined fuzz_dup: the 0x1c0-byte frame and its 13 saved registers, the size
   test (not taken), s3 = data, s4 = lb data[0], s2 = n = size - 1, a0 = n ? n : 1 (seqz / add), jal malloc. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_seg2.
Import ListNotations.
Open Scope Z_scope.

Lemma rd0 : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. clear H. revert i Hi. induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma e_cond_small : forall u, 1 <= u < 2 ^ 26 ->
  bv_ltu (Z_to_bv 64 (u + -67108864)) (Z_to_bv 64 (-67108863)) = false.
Proof.
  intros u Hu. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.ltb_ge. Z.div_mod_to_equations; lia.
Qed.

Definition q_mal (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp lo p n : Z) (pl : list byte) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m' j, ms = MS R F (Z_to_bv 64 0x14e30) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12d38 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 n /\ reg_get R 10 = Z_to_bv 64 (dup_size (n - 1)) /\
    reg_get R 18 = Z_to_bv 64 (n - 1) /\ reg_get R 19 = Z_to_bv 64 p /\
    reg_get R 20 = sxb (nth 0 pl (Z_to_bv 8 0)) /\
    munch [(Sp, Sp + 448)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rw_cells rsegs m' Sp (CB 344 j :: sv).

Lemma e_a0 : forall n, 1 <= n < 2 ^ 26 ->
  Z_to_bv 64 (n + -1 + bv_unsigned (v_sltiu (Z_to_bv 64 (n + -1)) 1)) = Z_to_bv 64 (dup_size (n - 1)).
Proof.
  intros n Hn. unfold v_sltiu. rewrite (unsigned_lit (n + -1)) by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  unfold dup_size. destruct (n + -1 <? 1) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
    rewrite unsigned_lit by lia; destruct (Z.eqb_spec (n - 1) 0); f_equal; lia.
Qed.

Lemma e_entry :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p n : Z) (pl : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 448 <= bv_unsigned sp -> mem_inv rsegs m -> bv_unsigned sp < 2 ^ 63 ->
    1 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> n = Z.of_nat (length pl) ->
    bytes_at rsegs m p pl -> p + n <= lo ->
    evt rsegs (q_mal F fc gp tp m (bv_unsigned sp - 448) lo p n pl
                 [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12cd4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p n pl ST LO MI H63 Hn Hp Hlen HP HPL.
  pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  carve_frame 448%nat ST.
  do 19 step.
  if_false_by (e_cond_small n ltac:(lia)).
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (R0 : ov_read_bytes rsegs mm (Z_to_bv 64 (p + Z.of_nat 0)) 1 = Some [nth 0 pl (Z_to_bv 8 0)]) end.
  { apply rd0; [exact HP | lia]. }
  rewrite Z.add_0_r in R0.
  do 6 step.
  rewrite (e_a0 n Hn).
  apply evt_done. unfold q_mal. do 3 eexists.
  split; [reflexivity|].
  do 9 (split; [first [reflexivity | (simp_regs; f_equal; lia)] |]).
  replace (bv_unsigned sp + -448 + 448) with (bv_unsigned sp) by lia.
  replace (bv_unsigned sp + -448) with (bv_unsigned sp - 448) by lia.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
Qed.

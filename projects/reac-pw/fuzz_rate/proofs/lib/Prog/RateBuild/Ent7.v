(** ent_build's kind 7 (pod.h:350-357): type t % 21, size s % 12, the body the next size input bytes (zeros past
    the end), t and s = fuzz_u8. From the jump table's target 0x13848 to the join 0x13ce0 (through 0x13a2c when no
    byte is left, 0x13c10 when s is read, 0x13c38, and Ent6.v's tail from 0x13c80 with memcpy at 0x13ca4). Ported from
    reac-pw/fuzz_role's Prog/RoleBuild/Ent7.v (role 0x13700 / 0x138e0 /
    0x13ae4 / 0x13b0c / 0x13b54 = rate 0x13848 / 0x13a2c / 0x13c10 / 0x13c38 / 0x13c80) at rate's registers (role s3 s4
    s5 s6 s11 = rate s5 s6 s7 s8 s1) and frame cells (e 0xb8). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntCut EntFacts Ent6.
Import ListNotations.
Open Scope Z_scope.

(** Name the current MemC hypothesis MC. *)
Local Ltac mcname :=
  lazymatch goal with H : MemC _ _ _ _ _ _ _ _ |- _ => let X := fresh "X" in rename H into X; rename X into MC end.

Section Case7.
Variables (sp gp tp s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Lemma case7_ok : case_at sp gp tp s2 s9 F fc m r src pp lo 7 0x13848.
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 b rest m1 Er Hk KS -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R. clear KS.
  pose proof (tail_13c80 sp gp tp s2 s9 F fc m r src pp lo HE MCPY) as T.
  (* 0x13848 beqz s7 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: t = s = 0, type 0 (e's zeros), size 0 *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    (* 0x13a2c mv s5,zero; mv a0,zero; mv a1,zero; ld s1,0x80(sp); j 0x13c38; lui s7,4; andi s6,a1,0xff; j 0x13c80 *)
    mcells. do 8 step.
    eapply (T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%nat 0 0).
    + lia.
    + lia.
    + lia.
    + rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
    + f_equal; rewrite Lr; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply MemC_e_ext; [eassumption|]. vm_compute. reflexivity.
  - (* t = the byte after kind; 0x1384c lbu a0,1(s8); t % 21 (0x13850 .. 0x13880) *)
    assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    do 13 step.
    match goal with |- context [Z.land ?E 255] =>
      replace (Z.land E 255) with (bv_unsigned v mod 21) by (clear - v; revert v; byte_eq) end.
    pose proof (Z.mod_pos_bound (bv_unsigned v) 21 ltac:(lia)) as Hm.
    (* 0x13884 sw s5,0xb8(sp) *)
    pre_store HE (bv_unsigned sp + 184) 4%nat. step. mstore_e HE 0.
    (* ld s1,0x80(sp); addi a0,zero,2; bne s6,a0 *)
    mcells. do 3 step.
    unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
    destruct rest as [|w rest]; cbn [length] in Lr.
    + (* no byte for s: s = 0, size 0; mv a0,zero; mv a1,zero; addi a5,s8,2; j 0x13c38; lui s7,4; andi s6,a1,0xff;
         j 0x13c80 *)
      if_false.
      do 7 step.
      eapply (T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (bv_unsigned v mod 21) 0).
      * lia.
      * lia.
      * lia.
      * rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
      * f_equal; rewrite Lr; reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply MemC_e_ext; [eassumption|]. rewrite le4_any. reflexivity.
    + (* s = the next byte; 0x13c10 lbu a1,2(s8); addi a0,s6,-3; addi a5,s8,3; s % 12 (0x13c1c .. 0x13c34);
         0x13c38 lui s7,4; andi s6,a1,0xff; j 0x13c80 *)
      if_true.
      mcname.
      lazymatch goal with MC : MemC _ _ _ _ _ _ ?mc _ |- _ =>
        assert (HR : ov_read_bytes rsegs mc (wa (src + Z.of_nat 2)) 1 = Some [w])
          by (rewrite (MemC_in_byte sp m r src pp lo _ _ 2 MC) by lia; rewrite Er; reflexivity) end.
      step. clear HR.
      do 12 step.
      match goal with |- context [Z.land ?E 255] =>
        replace (Z.land E 255) with (bv_unsigned w mod 12) by (clear - w; revert w; byte_eq) end.
      pose proof (Z.mod_pos_bound (bv_unsigned w) 12 ltac:(lia)) as Hm'.
      eapply (T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3%nat (bv_unsigned v mod 21) (bv_unsigned w mod 12)).
      * lia.
      * lia.
      * lia.
      * rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
      * f_equal; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply MemC_e_ext; [eassumption|]. rewrite le4_any. reflexivity.
Qed.

End Case7.

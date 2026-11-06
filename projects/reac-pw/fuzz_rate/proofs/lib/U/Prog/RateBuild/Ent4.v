(** ent_build's kind 4 in the UBSan image (pod.h:326-332): a Bool of v % 3, v = fuzz_u8. From the jump table's
    target 0x13610 to the join 0x13ee4 (through 0x138f4 when no byte is left, 0x13904 and 0x13ee0). The form is
    reac-pw/fuzz_role's U/Prog/RoleBuild/Ent4.v re-walked at rate's
    registers: s8 and s11 reloaded from the cells sp + 0xd8 /
    sp + 0xc8 on both paths. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Case4.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma case4_ok_sec : case_at sp gp tp s3 F fc m r src pp lo 4 0x13610.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct rest as [|c rest].
  - (* no byte for v: v = 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13610 beqz s8 (taken) *)
    step. brt.
    (* 0x138f4 mv t1,zero; mv a0,zero; ld s8,0xd8(sp); ld s11,0xc8(sp) *)
    do 2 step.
    pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as Rd8. step.
    pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8. step.
    clear Rd8 Rc8.
    (* 0x13904 addi a1,zero,2; sw a1,0xe8(sp); sw s1,0xec(sp); sw a0,0xf0(sp) *)
    step. est_t HE MC. est_sz HE MC. est_bd HE MC (bv_unsigned sp + 240) 0%nat 4%nat.
    (* 0x13914 j 0x13ee0; 0x13ee0 mv s9,s7 *)
    do 2 step.
    eapply join_13ee4; [eb_tac Er Hk | | | exact MC | | | ].
    + reflexivity.
    + f_equal. rewrite L. cbn [length]. lia.
    + apply le4_le32.
    + apply le4_le32.
    + vm_compute. reflexivity.
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x13610 beqz s8 (not taken); addi s7,s7,1; ld s11,0xc8(sp); addi a0,zero,1; bltu a0,s7 (taken, past the
       trap at 0x13624) *)
    step. brf. step.
    pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8. step. clear Rc8.
    step. step. brt.
    (* 0x13628 lbu a0,1(s9) *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    step.
    (* 0x1362c addi t1,t1,-2; addi s7,s9,2; v % 3 (0x13634-0x1364c) *)
    do 9 step.
    (* 0x13650 ld s8,0xd8(sp); j 0x13904 *)
    pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as Rd8. step. clear Rd8.
    step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned c mod 3) by (symmetry; byte_eq c) end.
    (* 0x13904 addi a1,zero,2; sw a1,0xe8(sp); sw s1,0xec(sp); sw a0,0xf0(sp) *)
    step. est_t HE MC. est_sz HE MC. est_bd HE MC (bv_unsigned sp + 240) 0%nat 4%nat.
    (* 0x13914 j 0x13ee0; 0x13ee0 mv s9,s7 *)
    do 2 step.
    eapply join_13ee4; [eb_tac Er Hk | | | exact MC | | | ].
    + f_equal. rewrite L. lia.
    + f_equal. rewrite L. lia.
    + apply le4_le32.
    + apply le4_le32.
    + cbn [e_body]. rewrite le4_le32, length_le32. apply upd_zeros0. rewrite length_le32. lia.
Qed.

End Case4.

Theorem case4_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> case_at sp gp tp s3 F fc m r src pp lo 4 0x13610.
Proof. intros. apply case4_ok_sec; assumption. Qed.

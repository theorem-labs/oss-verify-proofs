(** ent_build's kind 9 (pod.h:370-376): a Struct of 24 bytes holding one String pod "reac.cfg.rate". From 0x1396c
    (the branch for kind % 10 > 8) through memcpy(e.body + 8, "reac.cfg.rate", 14) and `sd s7,0xa8(sp)` to the join
    0x13764. Ported from reac-pw/fuzz_role's Prog/RoleBuild/Ent9.v at
    rate's registers, frame cells and pcs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** Name the current MemC hypothesis MC. *)
Local Ltac mcname :=
  lazymatch goal with H : MemC _ _ _ _ _ _ _ _ |- _ => let X := fresh "X" in rename H into X; rename X into MC end.

Section Case9.
Variables (sp gp tp s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Lemma case9_ok : case9_at sp gp tp s2 s9 F fc m r src pp lo.
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 b rest m1 Er Hk -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (Lr : length r = S (length rest)) by (rewrite Er; reflexivity).
  (* 0x1396c addi s5,zero,14; sw s5,0xb8(sp); sw s5,0xc0(sp); addi a0,zero,8; sw a0,0xc4(sp) *)
  step.
  pre_store HE (bv_unsigned sp + 184) 4%nat. step. mstore_e HE 0.
  pre_store HE (bv_unsigned sp + 192) 4%nat. step. mstore_e HE 8.
  step.
  pre_store HE (bv_unsigned sp + 196) 4%nat. step. mstore_e HE 12.
  (* auipc a0; addi a1,a0,-0x522 (0x1045e); addi a2,zero,14; addi a0,sp,0xc8; mv s8,a5; jal memcpy *)
  do 6 step.
  mcname.
  lazymatch goal with MC : MemC _ _ _ _ _ _ ?mc ?eb |- _ =>
    destruct (MemC_cells sp m r src pp lo HE mc eb (bv_unsigned sp + 200) 14 MC ltac:(lia)
                ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ) end.
  pose proof (img_apart sp m r src pp lo HE 0x1045e 14 ltac:(vm_compute; reflexivity) ltac:(lia)) as IA.
  eapply evt_cut.
  { eapply MCPY with (src := S9 ++ [NUL]) (junk := junk).
    - rewrite !unsigned_lit by lia. apply image_bytes_at.
      + exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC).
      + vm_compute. reflexivity.
      + lia.
      + replace (Z.of_nat (length (S9 ++ [NUL]))) with 14 by reflexivity. lia.
    - vm_compute. reflexivity.
    - rewrite !unsigned_lit by lia. exact CJ.
    - rewrite !unsigned_lit by lia. unfold FRAME_LOCALS in IA. lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & RC2 & _).
  subst ms'. rewrite !unsigned_lit in MU2, RC2 by lia.
  apply rw_CB_bytes in RC2 as [B2 L2].
  pose proof (MemC_call_e sp m r src pp lo HE _ m2 _ _ 14 _ MC MU2 WM2 MI2 B2
                ltac:(rewrite L2; reflexivity) ltac:(lia) ltac:(lia)) as MC2.
  replace (bv_unsigned sp + 200 - (bv_unsigned sp + 184)) with 16 in MC2 by lia.
  clear MU2 WM2 MI2 B2 L2 MC CJ Lj junk IA.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13998 addi s6,zero,24; sw s6,0xbc(sp) *)
  step.
  pre_store HE (bv_unsigned sp + 188) 4%nat. step. mstore_e HE 4.
  (* 0x139a0 sd s7,0xa8(sp); j 0x13764 *)
  pre_store HE (bv_unsigned sp + 168) 8%nat. step. mstore_out HE.
  step.
  eapply join_13764.
  - rewrite Er. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. rewrite Lr. lia.
  - reflexivity.
  - eapply MemC_e_ext; [eassumption|]. rewrite !le4_any. vm_compute. reflexivity.
  - replace (Z.of_nat (length rest)) with (Z.of_nat (length r) - 1) by (rewrite Lr; lia). exact HW.
Qed.

End Case9.

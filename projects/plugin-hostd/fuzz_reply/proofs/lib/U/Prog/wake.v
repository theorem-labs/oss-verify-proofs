From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import wake_c.
Open Scope Z_scope.

Theorem wake_holds : wake_contract.
Proof.
  unfold wake_contract, WAKE, WAKE_FRAME, G_WAKE1.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO HW DW.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  carve_frame 16%nat ST.
  step. step. step. step. step. step.
  change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))).
  mem_after_store.
  step. if_false.
  match goal with
  | H : bytes_at rsegs ?mm 0x2162c _ |- _ =>
      assert (RD : ov_read_bytes rsegs mm (wa 0x2162c) 4 = Some (le4 (Z_to_bv 64 (-1))));
      [ replace (wa 0x2162c) with (wa (0x2162c + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 0x2162c (le4 (Z_to_bv 64 (-1))) 0 4 H ltac:(lia))
          by (rewrite length_le4; lia);
        reflexivity
      | ]
  end.
  step. step. if_true.
  step. step. step.
  match goal with
  | H : rw_cells rsegs ?mm _ ?cs |- _ =>
      pose proof (stk_release rsegs mm lo _ _ ST H ltac:(lia)) as STR;
      change (cells_size cs) with 16%nat in STR
  end.
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in STR by lia.
  apply evt_done. do 3 eexists.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [exact STR|eassumption].
Qed.

(* check_latest_submit, entry 0x161c4: bne a0,a1,0x161cc; ret; then the abort path (addi sp,sp,-16; sd ra,8(sp);
   jal abort). The model premise gives rc = want, so the bne falls through to the ret and the abort path is closed by
   exfalso. No load, no store, no call: the memory is unchanged, so munch, wmono, mem_inv, stk and wmem hold of m. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem check_latest_submit_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_latest_submit_holds : check_latest_submit_contract.
Proof.
  unfold check_latest_submit_contract, check_latest_submit_ENTRY, check_latest_submit_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' rc want -> -> Hrc Hwant WM HM Hsp ST LO WS MI.
  (* the model: rc = want, B' = B (fuzz_transport.c:674-675) *)
  unfold check_latest_submit_m in HM.
  destruct (rc =? want) eqn:E; cbn [negb] in HM; [|discriminate HM].
  injection HM as <-. apply Z.eqb_eq in E. subst want.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  step.                                   (* 0x161c4 bne a0, a1, 0x161cc *)
  (* the taken branch (to the abort path) needs rc <> rc: closed by exfalso *)
  if_cases K; zify_cond K; try (exfalso; first [ exact (K eq_refl) | lia | (Z.div_mod_to_equations; lia) ]).
  step.                                   (* 0x161c8 ret *)
  apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|]. split; [reflexivity|exact WM].
Qed.

Print Assumptions check_latest_submit_holds.

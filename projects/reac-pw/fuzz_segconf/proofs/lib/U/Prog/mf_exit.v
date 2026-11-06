(** m_file (UBSan build, image 1696d6c34ffd): the piece S_MF_EXIT of U/Prog/m_file_c.v (family F3).
    The epilogue 0x14980-0x149b8: ra, s0 .. s11 from sp + 0x108 .. sp + 0xa8, sp += 0x110, ret. It writes nothing:
    the post holds of the memory it starts from. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c.
Import ListNotations.
Open Scope Z_scope.

Lemma mf_exit_holds : S_MF_EXIT.
Proof.
  unfold S_MF_EXIT, H_MF_EXIT, M_FILE_EXIT, M_FILE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 W Q Hsp HS HF MI TM ST HQ.
  unfold saved_at, M_FILE_SAVE in HS.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range sp0) as Rsp0.
  assert (RC : ro_cells rsegs m (bv_unsigned sp + 168)
                 [C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 ra0]).
  { split; [cbn; repeat split | exact HS]. }
  clear HS.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self sp0) as Esp0.
  set (Sp := bv_unsigned sp) in *. set (Sp0 := bv_unsigned sp0) in *.
  rewrite <- Esp. clearbody Sp Sp0. subst sp0. subst Sp0.
  do 15 step.
  apply evt_done. unfold ret_void_fp.
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m.
  split; [unfold mkR; repeat f_equal; lia|].
  split; [exact HF|]. split; [intros; reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [exact MI|]. split; [exact TM|]. split; [|exact HQ].
  rewrite unsigned_lit by lia. exact ST.
Qed.

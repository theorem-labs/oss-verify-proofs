From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c io_now_c io_now_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of io_now_contract_F (image A, entry 0x8356c, no frame), with StepF's step: the one load's access side goal
   is closed from the rng fact for g_now's payload.

   The walk (3 words):
     0x8356c          auipc a0: a0 = pc + 0x55c000.
     0x83570          ld a0,-1132(a0): a0 = the 8-byte load at 0x5df100 = g_now's payload.
     0x83574          ret.
   By the world relation the 8 bytes at 0x5df100 are sub Bw OFF_g_now 8 (TWorldG.v tw_bytes_at at the row of g_now),
   so the loaded value is Z_to_bv 64 (u_at Bw OFF_g_now 8) = Z_to_bv 64 (io_now_m Bw) (TWorldG.v ld_world). The run
   stores nothing, so the memory, the stack and the world relation are the entry's. *)

Theorem io_now_holds_F : io_now_contract_F.
Proof.
  unfold io_now_contract_F, IO_NOW, IO_NOW_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw HW ST HLO RG.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  rewrite io_now_g_now_at in RG.
  (* the 8 bytes of g_now, as raw memory *)
  assert (L8 : length (TW.sub Bw TW.OFF_g_now 8) = 8%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_g_now; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.OFF_g_now, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok HW TMAP_A_g_now
    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as BF.
  change (TA_g_now + 0) with 6156544 in BF. change (TW.OFF_g_now + 0) with TW.OFF_g_now in BF.
  assert (RDG : ov_read_bytes rsegs m (wa 6156544) 8 = Some (TW.sub Bw TW.OFF_g_now 8)).
  { replace (wa 6156544) with (wa (6156544 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 6156544 _ 0 8 BF ltac:(lia)) by (rewrite L8; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L8. lia. }
  clear BF.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x8356c-0x83570: a0 = g_now *)
  step. step.
  rewrite ld_world.
  (* 0x83574: ret *)
  step.
  apply evtF_done. exists m. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split; [exact ST | exact HW].
Qed.

Print Assumptions io_now_holds_F.

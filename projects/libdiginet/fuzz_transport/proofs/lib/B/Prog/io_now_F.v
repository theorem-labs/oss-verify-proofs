From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_c io_now_c io_now_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of io_now_contract_F (image B, entry 0x83410, no frame), with StepF's step: the one load's access side goal
   is closed from the rng fact for g_now's payload.

   The walk (3 words):
     0x83410          auipc a0: a0 = pc + 0x55c000.
     0x83414          ld a0,-1680(a0): a0 = the 8-byte load at 0x5ded80 = g_now's payload (TB_g_now).
     0x83418          ret.
   By the world relation the 8 bytes at 0x5ded80 are sub Bw OFF_g_now 8 (TWorldG.v tw_bytes_at at TMAP_B's row of
   g_now), so the loaded value is Z_to_bv 64 (u_at Bw OFF_g_now 8) = Z_to_bv 64 (io_now_m Bw) (TWorldG.v ld_world).
   The function has no UBSan check of its own (no trap word). The run stores nothing, so the memory, the stack and
   the world relation are the entry's. *)

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
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.OFF_g_now, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok HW TMAP_B_g_now
    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as BF.
  change (TB_g_now + 0) with 6155648 in BF. change (TW.OFF_g_now + 0) with TW.OFF_g_now in BF.
  assert (RDG : ov_read_bytes rsegs m (wa 6155648) 8 = Some (TW.sub Bw TW.OFF_g_now 8)).
  { replace (wa 6155648) with (wa (6155648 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 6155648 _ 0 8 BF ltac:(lia)) by (rewrite L8; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L8. lia. }
  clear BF.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x83410-0x83414: a0 = g_now *)
  step. step.
  rewrite ld_world.
  (* 0x83418: ret *)
  step.
  apply evtF_done. exists m. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split; [exact ST | exact HW].
Qed.

Print Assumptions io_now_holds_F.

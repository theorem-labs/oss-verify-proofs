From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c check_state_wake_F_c TWorldAKept.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_state_wake_contract_F (image A, entry 0x84370, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportList.v, slots 3139-3148):
     0x84370-0x84374  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x84378-0x8437c  auipc a0; lw a0,..(a0): a0 = the 4-byte load at 0x5df178 = M.foreign, sign-extended.
     0x84380          bnez a0, 0x84390.
     0x84384-0x8438c  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x84390 / 0x84394 (__asan_handle_no_return, abort) is never reached: the model premise
   check_state_wake_m Bw = Some (Bw', tt) gives M_foreign Bw = 0 and Bw' = Bw, and by the world relation the four
   bytes at 0x5df178 are sub Bw A_M_foreign 4, so the loaded value is Z_to_bv 64 (M_foreign Bw) = 0 (TWorldG.v
   lw_world).

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (TWorldAKept.v csw_kept). *)

Theorem check_state_wake_holds_F : check_state_wake_contract_F.
Proof.
  unfold check_state_wake_contract_F, CHECK_STATE_WAKE, CHECK_STATE_WAKE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RFO.
  (* the model: M.foreign = 0 and Bw' = Bw *)
  assert (HF : TW.M_foreign Bw = 0 /\ Bw' = Bw).
  { unfold TC.check_state_wake_m, TC.truth in HM.
    destruct (Z.eqb_spec (TW.M_foreign Bw) 0) as [E|E]; cbn [negb] in HM; [|discriminate HM].
    split; [exact E|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HF as [HF ->]. clear HM.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  rewrite check_state_wake_foreign_at in RFO.
  (* the 4 bytes of M.foreign, as raw memory *)
  assert (L4 : length (TW.sub Bw TW.A_M_foreign 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_foreign, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.A_M_foreign, TW.OFF_M, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 24 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF.
  change (TA_M + 24) with 6156664 in BF. change (TW.OFF_M + 24) with TW.A_M_foreign in BF.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj BF I) as BFC. clear BF.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x84370-0x84374: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as [BF _].
  pose proof (bytes_tp m m0 _ _ 6156664 (TW.sub Bw TW.A_M_foreign 4) MU1 ltac:(rewrite L4; lia) BF) as BF0.
  assert (RDF : ov_read_bytes rsegs m0 (wa 6156664) 4 = Some (TW.sub Bw TW.A_M_foreign 4)).
  { replace (wa 6156664) with (wa (6156664 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156664 _ 0 4 BF0 ltac:(lia)) by (rewrite L4; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L4. lia. }
  clear BF BF0.
  (* 0x84378-0x8437c: a0 = M.foreign = 0 *)
  step. step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_foreign) with (TW.M_foreign Bw). rewrite HF.
  (* 0x84380: bnez a0 falls through *)
  step. if_false.
  (* 0x84384-0x8438c: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 2 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (csw_kept m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

Print Assumptions check_state_wake_holds_F.

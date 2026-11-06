From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_ack_settle_c check_ack_settle_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_ack_settle_contract_F (image A, entry 0x85b04, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportList.v, slots 4648-4659):
     0x85b04-0x85b08  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85b0c-0x85b10  auipc a0; auipc a1.
     0x85b14          lw a0: a0 = the 4-byte load at 0x5e53ac = GOT.acks, sign-extended.
     0x85b18          lw a1: a1 = the 4-byte load at 0x5f312c = OW.acks, sign-extended.
     0x85b1c          bne a0,a1, 0x85b2c.
     0x85b20-0x85b28  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x85b2c / 0x85b30 (__asan_handle_no_return, abort) is never reached: the model premise
   check_ack_settle_m Bw = Some (Bw', tt) gives GOT_acks Bw = OW_acks Bw and Bw' = Bw, and by the world relation the
   four bytes at 0x5e53ac are sub Bw A_GOT_acks 4 and the four bytes at 0x5f312c are sub Bw A_OW_acks 4, so the two
   loaded values are Z_to_bv 64 (GOT_acks Bw) and Z_to_bv 64 (OW_acks Bw) (lw_world), which are equal.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (off_stk premise), so every payload byte reads the same
   (TMAP_A_kept) and tw_at holds of the same Bw. *)

Theorem check_ack_settle_holds_F : check_ack_settle_contract_F.
Proof.
  unfold check_ack_settle_contract_F, CHECK_ACK_SETTLE, CHECK_ACK_SETTLE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RGA ROA.
  (* the model: GOT.acks = OW.acks and Bw' = Bw *)
  assert (HF : TW.GOT_acks Bw = TW.OW_acks Bw /\ Bw' = Bw).
  { unfold TC.check_ack_settle_m in HM.
    destruct (Z.eqb_spec (TW.GOT_acks Bw) (TW.OW_acks Bw)) as [E|E]; cbn [negb] in HM; [|discriminate HM].
    split; [exact E|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HF as [HF ->]. clear HM.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  rewrite check_ack_settle_got_acks_at in RGA.
  rewrite check_ack_settle_ow_acks_at in ROA.
  (* the 4 bytes of GOT.acks and the 4 bytes of OW.acks, as raw memory *)
  assert (LG : length (TW.sub Bw TW.A_GOT_acks 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_GOT_acks, TW.OFF_GOT; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.A_GOT_acks, TW.OFF_GOT, TW.W_LEN. lia. }
  assert (LO : length (TW.sub Bw TW.A_OW_acks 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_OW_acks, TW.OFF_OW; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.A_OW_acks, TW.OFF_OW, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 204 4 TMAP_A_ok HW TMAP_A_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as BG.
  change (TA_GOT + 204) with 6181804 in BG. change (TW.OFF_GOT + 204) with TW.A_GOT_acks in BG.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 204 4 TMAP_A_ok HW TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BO.
  change (TA_OW + 204) with 6238508 in BO. change (TW.OFF_OW + 204) with TW.A_OW_acks in BO.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj (conj BG BO) I) as BFC. clear BG BO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x85b04-0x85b08: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as [[BG BO] _].
  pose proof (bytes_tp m m0 _ _ 6181804 (TW.sub Bw TW.A_GOT_acks 4) MU1 ltac:(rewrite LG; lia) BG) as BG0.
  pose proof (bytes_tp m m0 _ _ 6238508 (TW.sub Bw TW.A_OW_acks 4) MU1 ltac:(rewrite LO; lia) BO) as BO0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 6181804) 4 = Some (TW.sub Bw TW.A_GOT_acks 4)).
  { replace (wa 6181804) with (wa (6181804 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6181804 _ 0 4 BG0 ltac:(lia)) by (rewrite LG; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite LG. lia. }
  assert (RDO : ov_read_bytes rsegs m0 (wa 6238508) 4 = Some (TW.sub Bw TW.A_OW_acks 4)).
  { replace (wa 6238508) with (wa (6238508 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6238508 _ 0 4 BO0 ltac:(lia)) by (rewrite LO; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite LO. lia. }
  clear BG BO BG0 BO0.
  (* 0x85b0c-0x85b18: a0 = GOT.acks, a1 = OW.acks *)
  step. step. step. step.
  rewrite !lw_world.
  change (TW.s32_at Bw TW.A_GOT_acks) with (TW.GOT_acks Bw).
  change (TW.s32_at Bw TW.A_OW_acks) with (TW.OW_acks Bw).
  rewrite HF.
  (* 0x85b1c: bne a0,a1 falls through *)
  step. if_false.
  (* 0x85b20-0x85b28: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU1|].
  split; [match goal with W : wmono _ m m0 |- _ => exact W end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (TMAP_A_kept (segs := rsegs) m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

Print Assumptions check_ack_settle_holds_F.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_ack_settle_c check_ack_settle_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_ack_settle_contract_F (image B, entry 0x85d88, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportBList.v, slots 4794-4806, AF_check_ack_settle = 0x4ae8):
     0x85d88-0x85d8c  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85d90-0x85d94  auipc a0; auipc a1.
     0x85d98          lw a0: a0 = the 4-byte load at 0x5e502c = GOT.acks, sign-extended.
     0x85d9c          lw a1: a1 = the 4-byte load at 0x5f2dac = OW.acks, sign-extended.
     0x85da0          bne a0,a1, 0x85db0.
     0x85da4-0x85dac  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x85db0 / 0x85db4 / 0x85db8 (TB___asan_handle_no_return, TB_abort, then the unimp word 0xc0001073)
   is never reached: the model premise check_ack_settle_m Bw = Some (Bw', tt) gives GOT_acks Bw = OW_acks Bw and
   Bw' = Bw; by the world relation the four bytes at 0x5e502c are sub Bw A_GOT_acks 4 and those at 0x5f2dac are
   sub Bw A_OW_acks 4 (tw_bytes_at), so the two loaded values are Z_to_bv 64 (GOT_acks Bw) and
   Z_to_bv 64 (OW_acks Bw) (lw_world), which are equal, and bne falls through. The unimp word at 0x85db8 is reached
   only from the abort call at 0x85db4, so the same fact rules it out. The function has no UBSan check of its own,
   and the statement has no alignment or range premise.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (TMAP_B_kept). *)

(* A world bytes_at fact survives a munch of a range it does not meet (image B's rsegs). *)
Lemma cas_bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Theorem check_ack_settle_holds_F : check_ack_settle_contract_F.
Proof.
  unfold check_ack_settle_contract_F, CHECK_ACK_SETTLE, CHECK_ACK_SETTLE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RGA ROA.
  (* the model: GOT.acks = OW.acks and Bw' = Bw (fuzz_transport.c:686-687) *)
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
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  rewrite check_ack_settle_got_acks_at in RGA.
  rewrite check_ack_settle_ow_acks_at in ROA.
  (* the 4 bytes of GOT.acks and the 4 bytes of OW.acks, as raw memory *)
  assert (LG : length (TW.sub Bw TW.A_GOT_acks 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_GOT_acks, TW.OFF_GOT; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_GOT_acks, TW.OFF_GOT, TW.W_LEN. lia. }
  assert (LO : length (TW.sub Bw TW.A_OW_acks 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_OW_acks, TW.OFF_OW; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_OW_acks, TW.OFF_OW, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 204 4 TMAP_B_ok HW TMAP_B_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as BG.
  change (TB_GOT + 204) with 6180908 in BG. change (TW.OFF_GOT + 204) with TW.A_GOT_acks in BG.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 204 4 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BO.
  change (TB_OW + 204) with 6237612 in BO. change (TW.OFF_OW + 204) with TW.A_OW_acks in BO.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj (conj BG BO) I) as BFC. clear BG BO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x85d88-0x85d8c: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as [[BG BO] _].
  pose proof (cas_bytes_tp m m0 _ _ 6180908 (TW.sub Bw TW.A_GOT_acks 4) MU1 ltac:(rewrite LG; lia) BG) as BG0.
  pose proof (cas_bytes_tp m m0 _ _ 6237612 (TW.sub Bw TW.A_OW_acks 4) MU1 ltac:(rewrite LO; lia) BO) as BO0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 6180908) 4 = Some (TW.sub Bw TW.A_GOT_acks 4)).
  { replace (wa 6180908) with (wa (6180908 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6180908 _ 0 4 BG0 ltac:(lia)) by (rewrite LG; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite LG. lia. }
  assert (RDO : ov_read_bytes rsegs m0 (wa 6237612) 4 = Some (TW.sub Bw TW.A_OW_acks 4)).
  { replace (wa 6237612) with (wa (6237612 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6237612 _ 0 4 BO0 ltac:(lia)) by (rewrite LO; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite LO. lia. }
  clear BG BO BG0 BO0.
  (* 0x85d90-0x85d9c: a0 = GOT.acks, a1 = OW.acks *)
  step. step. step. step.
  rewrite !lw_world.
  change (TW.s32_at Bw TW.A_GOT_acks) with (TW.GOT_acks Bw).
  change (TW.s32_at Bw TW.A_OW_acks) with (TW.OW_acks Bw).
  rewrite HF.
  (* 0x85da0: bne a0,a1 falls through *)
  step. if_false.
  (* 0x85da4-0x85dac: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU1|].
  split; [match goal with W : wmono _ m m0 |- _ => exact W end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
Qed.

Print Assumptions check_ack_settle_holds_F.

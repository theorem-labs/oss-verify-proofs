From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_code_c check_state_wake_code_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_state_wake_code_contract_F (image B, entry 0x8399c, frame 16 bytes), with StepF's step: each
   access side goal is closed from the rng fact of the frame, the one range the code touches. Image A's walk
   (lib/A/Prog/check_state_wake_code_F.v) at image B's entry, world table TMAP_B and hull.

   The walk (listing DgnTransportBList.v, slots 2495-2503, AF_check_state_wake_code = 0x26fc):
     0x8399c-0x839a0  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x839a4          bne a0,a1,0x839b4.
     0x839a8-0x839b0  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x839b4 / 0x839b8 / 0x839bc (TB___asan_handle_no_return, TB_abort, then the unimp word 0xc0001073)
   is never reached: the model premise check_state_wake_code_m Bw rc want = Some (Bw', tt) gives rc = want and
   Bw' = Bw, so a0 = Z_to_bv 64 rc and a1 = Z_to_bv 64 want are the same register value and the branch falls
   through. The unimp word is reached only from the abort call, so the same fact rules it out. The function has no
   UBSan check of its own.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (cswc_kept below). *)

(* The world relation kept at the leaf form's view csw_view (image B): TWorldB.v's TMAP_B_kept at segs := rsegs, as
   image A's TWorldAKept.csw_kept. *)
Lemma cswc_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_B (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_B_LO \/ TG.G_HARNESS_B_HI <= lo) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof. intros m m' lo hi Bw. unfold csw_view. exact (@TMAP_B_kept rsegs m m' lo hi Bw). Qed.

Theorem check_state_wake_code_holds_F : check_state_wake_code_contract_F.
Proof.
  unfold check_state_wake_code_contract_F, CHECK_STATE_WAKE_CODE, CHECK_STATE_WAKE_CODE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' rc want HA0 HA1 HRC HWT HW HM ST HLO HOFF RFR.
  (* the model: rc = want and Bw' = Bw *)
  assert (HF : rc = want /\ Bw' = Bw).
  { unfold TC.check_state_wake_code_m in HM.
    destruct (Z.eqb_spec rc want) as [E|E]; cbn [negb] in HM; [|discriminate HM].
    split; [exact E|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HF as [<- ->]. clear HM.
  (* a1 is the same register value as a0: the branch at 0x839a4 compares a register with itself *)
  assert (E01 : a1 = a0) by (rewrite HA0, HA1; reflexivity).
  clear HA0 HA1 HRC HWT. subst a1.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x8399c-0x839a0: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  match goal with WM' : wmono rsegs m m0 |- _ => rename WM' into WM1 end.
  (* 0x839a4: bne a0,a0 falls through *)
  step. if_false.
  (* 0x839a8-0x839b0: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. eexists. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (cswc_kept m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
Qed.

Print Assumptions check_state_wake_code_holds_F.

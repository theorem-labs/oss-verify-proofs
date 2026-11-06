From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c check_latest_submit_c check_latest_submit_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_latest_submit_contract_F (image A, entry 0x86230, frame 16 bytes), with StepF's step: each access
   side goal is closed from the rng fact of the frame.

   The walk (listing DgnTransportList.v, 8 words):
     0x86230-0x86234  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x86238          bne a0,a1, 0x86248.
     0x8623c-0x86244  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x86248 / 0x8624c (__asan_handle_no_return, abort) is never reached: the model premise
   check_latest_submit_m Bw rc want = Some (Bw', tt) gives rc = want and Bw' = Bw, so a0 = a1 and the branch falls
   through.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (off_stk premise; TWorldA.TMAP_A_hull), so every payload
   byte reads the same and tw_at holds of the same Bw. *)

(* A run that writes only [lo, hi), outside the hull, keeps the world relation with the same world (the script of
   check_state_wake_F.v's csw_kept, over TWorldA's TMAP_A_hull). *)
Lemma cls_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_LO \/ TG.G_HARNESS_HI <= lo) ->
  tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. apply (tw_kept TMAP_A (csw_view m)); [exact H|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold csw_view, mrd.
  rewrite MU; [reflexivity|].
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in *.
  rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Theorem check_latest_submit_holds_F : check_latest_submit_contract_F.
Proof.
  unfold check_latest_submit_contract_F, CHECK_LATEST_SUBMIT, CHECK_LATEST_SUBMIT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' rc want HA0 HA1 HRC HWANT HW HM ST HLO HOFF RFR.
  (* the model: rc = want and Bw' = Bw *)
  assert (HF : rc = want /\ Bw' = Bw).
  { unfold TC.check_latest_submit_m in HM.
    destruct (Z.eqb_spec rc want) as [E|E]; cbn [negb] in HM; [|discriminate HM].
    split; [exact E|].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  destruct HF as [<- ->]. clear HM. subst a0 a1.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x86230-0x86234: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* 0x86238: bne a0,a1 falls through (a0 = a1 = Z_to_bv 64 rc) *)
  step. if_false.
  (* 0x8623c-0x86244: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (cls_kept m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

Print Assumptions check_latest_submit_holds_F.

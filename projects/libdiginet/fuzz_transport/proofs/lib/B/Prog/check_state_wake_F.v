From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_c check_state_wake_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_state_wake_contract_F (image B, entry 0x84628, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportBList.v, slots 3298-3308, AF_check_state_wake = 0x3388; 11 words, image A's 10 and
   the unimp word at 0x84650):
     0x84628-0x8462c  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x84630-0x84634  auipc a0; lw a0,..(a0): a0 = the 4-byte load at 0x5dedf8 = M.foreign (listing A_OBJ 47),
                      sign-extended.
     0x84638          bnez a0, 0x84648.
     0x8463c-0x84644  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x84648 / 0x8464c / 0x84650 (TB___asan_handle_no_return, TB_abort, then the unimp word 0xc0001073)
   is never reached: the model premise check_state_wake_m Bw = Some (Bw', tt) gives M_foreign Bw = 0 and Bw' = Bw,
   and by the world relation the four bytes at 0x5dedf8 are sub Bw A_M_foreign 4 (tw_bytes_at), so the loaded value
   is Z_to_bv 64 (M_foreign Bw) = 0 (TWorldG.v lw_world) and bnez falls through. The unimp word at 0x84650 is reached
   only from the abort call at 0x8464c, so the same fact rules it out. The function has no UBSan check of its own,
   and the statement has no alignment or range premise.

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise), so tw_at holds of the same Bw
   (csw_kept_B below). *)

(* Image-B local copies of two image-A kit lemmas, with the same statements over image B's rsegs and TMAP_B. Image B
   has no lib/B/Prog/AsanKAProof.v and no lib/B/Prog/TWorldBKept.v yet; when they land, a dedupe pass replaces
   bytes_tp_B by AsanKAProof.bytes_tp and csw_kept_B by TWorldBKept.csw_kept. *)

(* lib/A/Prog/AsanKAProof.v bytes_tp: a bytes_at fact survives a munch of a range it does not meet. *)
Lemma bytes_tp_B : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* lib/A/Prog/TWorldAKept.v csw_kept: a run that writes only [lo, hi), outside the hull of the 18 harness globals,
   keeps tw_at at the leaf form's view csw_view with the same world; TWorldB.v's TMAP_B_kept at segs := rsegs. *)
Lemma csw_kept_B : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_B (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_B_LO \/ TG.G_HARNESS_B_HI <= lo) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof. intros m m' lo hi Bw. unfold csw_view. exact (@TMAP_B_kept rsegs m m' lo hi Bw). Qed.

Theorem check_state_wake_holds_F : check_state_wake_contract_F.
Proof.
  unfold check_state_wake_contract_F, CHECK_STATE_WAKE, CHECK_STATE_WAKE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RFO.
  (* the model: M.foreign = 0 and Bw' = Bw (fuzz_transport.c:507-515, TCb.v check_state_wake_m) *)
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
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  rewrite check_state_wake_foreign_at in RFO.
  (* the 4 bytes of M.foreign, as raw memory *)
  assert (L4 : length (TW.sub Bw TW.A_M_foreign 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_M_foreign, TW.OFF_M; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_M_foreign, TW.OFF_M, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 24 4 TMAP_B_ok HW TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF.
  change (TB_M + 24) with 6155768 in BF. change (TW.OFF_M + 24) with TW.A_M_foreign in BF.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj BF I) as BFC. clear BF.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x84628-0x8462c: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as [BF _].
  pose proof (bytes_tp_B m m0 _ _ 6155768 (TW.sub Bw TW.A_M_foreign 4) MU1 ltac:(rewrite L4; lia) BF) as BF0.
  assert (RDF : ov_read_bytes rsegs m0 (wa 6155768) 4 = Some (TW.sub Bw TW.A_M_foreign 4)).
  { replace (wa 6155768) with (wa (6155768 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6155768 _ 0 4 BF0 ltac:(lia)) by (rewrite L4; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L4. lia. }
  clear BF BF0.
  (* 0x84630-0x84634: a0 = M.foreign = 0 *)
  step. step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_foreign) with (TW.M_foreign Bw). rewrite HF.
  clear RDF.
  (* 0x84638: bnez a0 falls through; the branch to the trap path needs M.foreign <> 0 *)
  step. if_false.
  (* 0x8463c-0x84644: ld ra; addi sp; ret *)
  step. step. step.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU1|].
  split; [match goal with WM' : wmono rsegs m m0 |- _ => exact WM' end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (csw_kept_B m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
Qed.

Print Assumptions check_state_wake_holds_F.

(* check_state_desk_seg_runs: the first footprint run of check_state_desk in image A (fuzz_transport.asan): the
   prologue (check_state_desk_seg_kit.v csd_pro_F), the head (check_state_desk_seg_head.v csd_head_F), the two
   inlined spec_strz_len loops (check_state_desk_seg_loops.v csd_loops_F) and the set-up of the first bcmp call
   (check_state_desk_seg_tail.v csd_call1_F), from the entry 0x8538c to the call at 0x85540. The runs after each
   call are csd_mid_F and csd_ret_F of check_state_desk_seg_tail.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_desk_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_desk_seg_head.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_desk_seg_loops.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_desk_seg_tail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Local Notation AN NB := (TW.u_at NB 24 8).
Local Notation DB Bw := (TW.u_at Bw TW.A_OW_desk_body 8).

Lemma csd_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (p : Z) (NB Bw : list byte) (fr : TI.tframe) (vn nn : nat),
    csd_mem m p NB Bw fr vn nn -> csd_rng RNG (bv_unsigned sp) p NB fr vn nn -> csd_bnd p NB Bw fr ->
    csd_sep (bv_unsigned sp) p NB fr vn nn ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    (TW.s32_at Bw TW.A_OW_desk <? TW.s32_at Bw TW.A_GOT_desk) = false ->
    TW.s32_at NB 40 = TW.s32_at Bw TW.A_OW_desk_off ->
    (TW.u_at NB 32 8 =? 0) = (TW.u_at Bw TW.A_OW_desk_p 8 =? 0) ->
    (TW.u_at NB 32 8 = 0 \/ (TW.u_at NB 32 8 = CSD_PERS0 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_C24) \/
     (TW.u_at NB 32 8 = CSD_PERS1 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_PC)) ->
    TC.frame_strz_len (Some fr) (DB Bw + 15) = Some vn ->
    TC.frame_strz_len (Some fr) (DB Bw + 24) = Some nn ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (y13 y14 y15 y16 y17 : word),
         ms' = MS (mkR (Z_to_bv 64 CSD_RET1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                       (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 24))
                       (Z_to_bv 64 (AN NB)) (Z_to_bv 64 (DB Bw + 15)) (Z_to_bv 64 (Z.of_nat vn))
                       y13 y14 y15 y16 y17
                       (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K)
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CSD_BCMP) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (csd_fr s4 s3 s2 s1 s0 ra) /\
         csd_mem m1 p NB Bw fr vn nn)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
               s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSD_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    p NB Bw fr vn nn MEM RNGH BND SEP ST HLO C1 C2 C3 CP HVN HNN.
  pose proof RNGH as (RFR & _).
  eapply ExecF.evtF_cut.
  { eapply csd_pro_F; [exact ST | lia | exact RFR]. }
  intros ms0 (m1 & -> & MU & WM & ST1 & FR).
  pose proof (csd_mem_frame (bv_unsigned sp) m m1 p NB Bw fr vn nn SEP MU MEM) as MEM1.
  eapply csd_head_F with (p := p) (Bw := Bw) (fr := fr) (vn := vn) (nn := nn);
    [exact MEM1 | exact RNGH | exact BND | exact C1 | exact C2 | exact C3 | exact CP |].
  intros x10 x11 x12 x14 x15 x16 x17.
  eapply csd_loops_F with (p := p) (fr := fr) (vn := vn) (nn := nn);
    [exact MEM1 | exact RNGH | exact BND | exact HVN | exact HNN |].
  intros y12 y13 y14 y15.
  eapply ExecF.evtF_mono; [eapply csd_call1_F|].
  intros ms' ->.
  exists m1. do 5 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|].
  split; [exact FR | exact MEM1].
Qed.

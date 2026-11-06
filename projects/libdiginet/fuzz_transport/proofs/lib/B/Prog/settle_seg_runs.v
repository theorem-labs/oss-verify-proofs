(* settle_seg_runs: the footprint runs (lib/Lib/ExecF.v evtF, stepped with lib/Lib/StepF.v) that the image-B
   caller-journal walk of settle (lib/B/Prog/settle_cgW.v) carries into SRr. Image B = fuzz_transport.asan-ubsan
   41113a03c82f, entry 0x838c0, 21 words; listing lib/B/Prog/DgnTransportBList.v (the words after AF_settle). Image
   A's runs (lib/A/Prog/settle_seg_runs.v) at image B's addresses, world table TMAP_B and hull; the model facts and
   the tactics taken from that file (SA.settle_model, SA.settle_rdf, SA.settle_br) name no image.

   - settle_run1_F, from the entry to the entry of check_ack_settle:
       0x838c0 - 0x838c8  sp = sp - 16; the 8-byte stores of ra and s0 at sp + 8 and sp + 0 (the frame);
       0x838cc            s0 = a0 (ticked);
       0x838d0            jal check_ack_settle (ra = 0x838d4).
     The two stores write only the frame; the frame lies above the hull of the harness globals, so the world relation
     holds at the new memory with the same Bw (TWorldB.v TMAP_B_kept).
   - settle_jal2_F, settle_jal3_F, settle_jal4_F: the calls at 0x838d4 (check_state_settle, ra = 0x838d8), 0x838d8
     (check_inflight_settle, ra = 0x838dc) and 0x838dc (check_keepalive_settle, ra = 0x838e0). Each changes ra only.
   - settle_run5_F, from 0x838e0: a0 = the 4-byte signed load of g_raw (pc-relative, 0x5ded60; no instrumented
     check); g_raw <> 0: ra and s0 loaded back from the frame, sp = sp + 16, ret; g_raw = 0: jal check_latest_queue
     (0x838fc, ra = 0x83900).
   - settle_run6_F, from 0x83900: beqz s0 (s0 = ticked); ticked = 0: the return of 0x838ec - 0x838f8; else ra and s0
     loaded back, sp = sp + 16, j check_latest_drain (0x83910, no link): the state at check_latest_drain's entry is
     settle's own entry state (ra, sp, s0) with the other registers as the run leaves them.
   None of runs 2 - 6 stores a byte. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require settle_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module SA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.settle_seg_runs.

(* The entry, the return addresses of the five calls, and the entries of the six callees (the tail jump's target
   last). *)
Definition SETTLE_ENTRY : Z := 0x838c0.
Definition SETTLE_R1 : Z := 0x838d4.
Definition SETTLE_R2 : Z := 0x838d8.
Definition SETTLE_R3 : Z := 0x838dc.
Definition SETTLE_R4 : Z := 0x838e0.
Definition SETTLE_R5 : Z := 0x83900.
Definition SETTLE_CAS : Z := 0x85d88.
Definition SETTLE_CSS : Z := 0x85dbc.
Definition SETTLE_CIS : Z := 0x85fdc.
Definition SETTLE_CKS : Z := 0x860a4.
Definition SETTLE_CLQ : Z := 0x86104.
Definition SETTLE_CLD : Z := 0x862b8.

(* The load of g_raw (0x5ded60) at a memory m that holds the world. *)
Lemma settle_raw_read : forall (m : word -> option byte) Bw,
  tw_at TMAP_B (csw_view m) Bw ->
  ov_read_bytes rsegs m (wa 6155616) 4 = Some (TW.sub Bw TW.OFF_g_raw 4).
Proof.
  intros m Bw HW. unfold csw_view in HW.
  exact (SA.settle_rdf rsegs TMAP_B m Bw TW.OFF_g_raw TB_g_raw TW.SZ_g_raw 0 4 TMAP_B_ok HW TMAP_B_g_raw
           ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)).
Qed.

(* ---- run 1: from the entry to the entry of check_ack_settle ---- *)

(* What the run leaves at check_ack_settle's entry: ra = 0x838d4, sp the entry sp less 16, s0 = a0, every other
   register the entry's; the frame written with s0 and ra (in address order); every byte outside the frame
   unchanged; the world relation at the new memory. *)
Definition settle_post1 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (ms' : machine_state) : Prop :=
  exists (s0' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 SETTLE_R1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 SETTLE_CAS) fc None m' (seg_rom rsegs) /\
    s0' = a0 /\
    munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\
    tw_at TMAP_B (csw_view m') Bw.

Lemma settle_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    TG.G_HARNESS_B_HI <= bv_unsigned sp - 16 ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
    ExecF.evtF rsegs RNG
      (settle_post1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw HW ST HLO HOFF RFR.
  unfold SETTLE_ENTRY.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold TG.G_HARNESS_B_HI in HOFF.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x838c0 - 0x838c8: the frame and the two saves; 0x838cc: s0 = a0; 0x838d0: the call *)
  step. step. step. step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  apply evtF_done. unfold settle_post1. eexists. exists m0.
  split; [reflexivity|].
  split; [first [reflexivity | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned]|].
  split; [exact MU1|]. split; [exact WM|]. split; [exact FR|].
  apply (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
Qed.

(* ---- runs 2 - 4: the calls of check_state_settle, check_inflight_settle and check_keepalive_settle ---- *)

Lemma settle_jal2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 SETTLE_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 SETTLE_CSS) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R1) fc None m (seg_rom rsegs)).
Proof. intros. unfold SETTLE_R1. step. apply evtF_done. reflexivity. Qed.

Lemma settle_jal3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 SETTLE_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 SETTLE_CIS) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R2) fc None m (seg_rom rsegs)).
Proof. intros. unfold SETTLE_R2. step. apply evtF_done. reflexivity. Qed.

Lemma settle_jal4_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 SETTLE_R4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 SETTLE_CKS) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R3) fc None m (seg_rom rsegs)).
Proof. intros. unfold SETTLE_R3. step. apply evtF_done. reflexivity. Qed.

(* ---- run 5: g_raw, then the return or the call of check_latest_queue ---- *)

Lemma settle_run5_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (vra vs0 : word),
    tw_at TMAP_B (csw_view m) Bw ->
    0 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 vs0; C8 vra] ->
    ExecF.rng RNG (bv_unsigned sp) 16 -> ExecF.rng RNG 6155616 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (TW.g_raw Bw <> 0 /\ exists a0' : word,
            ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 vs0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc vra) fc None m (seg_rom rsegs)) \/
         (TW.g_raw Bw = 0 /\ exists a0' : word,
            ms' = MS (mkR (Z_to_bv 64 SETTLE_R5) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 SETTLE_CLQ) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Bw vra vs0 HW Hsp0 Hsp1 FR RFR RRAW.
  unfold SETTLE_R4.
  pose proof (settle_raw_read m Bw HW) as RD.
  pose proof (TWorldLemmas.s32_range Bw TW.OFF_g_raw) as RG.
  (* 0x838e0 - 0x838e4: a0 = g_raw *)
  step. step.
  rewrite ?lw_world. change (TW.s32_at Bw TW.OFF_g_raw) with (TW.g_raw Bw) in *.
  (* 0x838e8: beqz a0 *)
  step.
  destruct (Z.eq_dec (TW.g_raw Bw) 0) as [G0|G0].
  - SA.settle_br true.
    (* 0x838fc: the call of check_latest_queue *)
    step.
    apply evtF_done. right. split; [exact G0|]. eexists. reflexivity.
  - SA.settle_br false.
    (* 0x838ec - 0x838f8: ra and s0 loaded back, sp = sp + 16, ret *)
    step. step. step. step.
    apply evtF_done. left. split; [exact G0|]. eexists. reflexivity.
Qed.

(* ---- run 6: s0 = ticked, then the return or the tail jump to check_latest_drain ---- *)

Lemma settle_run6_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ticked : Z) (vra vs0 : word),
    -2 ^ 31 <= ticked < 2 ^ 31 ->
    0 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 vs0; C8 vra] ->
    ExecF.rng RNG (bv_unsigned sp) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (ticked = 0 /\
          ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 vs0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc vra) fc None m (seg_rom rsegs)) \/
         (ticked <> 0 /\
          ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 vs0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 SETTLE_CLD) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ticked) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R5) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ticked vra vs0 Htk Hsp0 Hsp1 FR RFR.
  unfold SETTLE_R5.
  (* 0x83900: beqz s0 *)
  step.
  destruct (Z.eq_dec ticked 0) as [K0|K0].
  - SA.settle_br true.
    (* 0x838ec - 0x838f8: ra and s0 loaded back, sp = sp + 16, ret *)
    step. step. step. step.
    apply evtF_done. left. split; [exact K0 | reflexivity].
  - SA.settle_br false.
    (* 0x83904 - 0x83910: ra and s0 loaded back, sp = sp + 16, j check_latest_drain *)
    step. step. step. step.
    apply evtF_done. right. split; [exact K0 | reflexivity].
Qed.

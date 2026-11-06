(* check_inflight_settle_seg_runs: the two footprint runs (lib/Lib/ExecF.v evtF, stepped with lib/Lib/StepF.v) that
   the image-B caller-journal walk of check_inflight_settle (lib/B/Prog/check_inflight_settle_cgW.v) carries into SRr.
   Image B = fuzz_transport.asan-ubsan 41113a03c82f, entry 0x85fdc, 50 words; listing lib/B/Prog/DgnTransportBList.v
   (the words after AF_check_inflight_settle). Image A's runs (lib/A/Prog/check_inflight_settle_seg_runs.v) at image
   B's addresses, world table TMAP_B and hull; the lemmas and tactics taken from that file (CISA.cis_model, cis_rdf,
   cis_ranges, cis_br, cis_fields) name no image.

   - cis_run1_F, from the entry to the entry of diginet_session_deadline:
       0x85fdc - 0x85fec  sp = sp - 32; the 8-byte stores of ra, s0, s1, s2 at sp + 24, 16, 8, 0 (the frame);
       0x85ff0 - 0x86000  a0 = GOT.acked, a1 = OW.acked (4-byte loads); bne a0, a1 to the trap: not taken;
       0x86004 - 0x86018  s0 = &M; a0 = M.fly_on; s2 = g_now + 0x290, s1 = g_cfg + 0x314; beqz a0 to 0x86038;
       0x8601c - 0x86034  a0 = g_now - M.fly_sent, a1 = ack_timeout_ms * 1000; bgeu a0, a1 to the trap: not taken;
       0x86038 - 0x86044  a1 = g_now, a0 = &g_s, jal diginet_session_deadline (ra = 0x86048).
     The four stores write only the frame; the frame lies above the hull of the harness globals, so the world relation
     holds at every memory of the run with the same Bw (TWorldB.v TMAP_B_kept).
   - cis_run2_F, from the return address 0x86048 to the `ret`:
       0x86048 - 0x8605c  a1 = g_now; bltu a0, a1 to the trap: not taken (g_now <= d); a2 = 1000000;
                          a1 = g_now + 1000000; bltu a1, a0 to the trap: not taken;
       0x86060 - 0x86064  a1 = M.fly_on; beqz a1 to 0x86080;
       0x86068 - 0x8607c  a1 = ack_timeout_ms * 1000 + M.fly_sent; bltu a1, a0 to the trap: not taken;
       0x86080 - 0x86094  ra, s0, s1, s2 loaded back from the frame; sp = sp + 32; ret.
     It stores nothing.
   The trap block (0x86098, 0x8609c) and the unimp word at 0x860a0 after it are never reached: every branch to the trap
   block is decided by the model facts, and no branch targets 0x860a0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_inflight_settle_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module CISA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_settle_seg_runs.

(* The entry, the return address of the call, the callee's entry, and the values the run leaves in s0, s1, s2 (the
   base of M; g_cfg + 0x314 and g_now + 0x290, the auipc results the loads at -0x2f8 / -0x290 use) and in a0 at the
   call (the base of g_s). *)
Definition CIS_ENTRY : Z := 0x85fdc.
Definition CIS_RET : Z := 0x86048.
Definition CIS_CALLEE : Z := 0x8a6c0.
Definition CIS_M : Z := 0x5dede0.
Definition CIS_S1 : Z := 0x5df014.
Definition CIS_S2 : Z := 0x5df010.
Definition CIS_GS : Z := 0x5df640.

(* The six world fields the code reads, as the load steps' read facts at a memory m that holds the world. *)
Lemma cis_reads : forall (m : word -> option byte) Bw,
  tw_at TMAP_B (csw_view m) Bw ->
  ov_read_bytes rsegs m (wa 6180920) 4 = Some (TW.sub Bw TW.A_GOT_acked 4) /\
  ov_read_bytes rsegs m (wa 6237624) 4 = Some (TW.sub Bw TW.A_OW_acked 4) /\
  ov_read_bytes rsegs m (wa 6155840) 4 = Some (TW.sub Bw TW.A_M_fly_on 4) /\
  ov_read_bytes rsegs m (wa 6155648) 8 = Some (TW.sub Bw TW.OFF_g_now 8) /\
  ov_read_bytes rsegs m (wa 6155856) 8 = Some (TW.sub Bw TW.A_M_fly_sent 8) /\
  ov_read_bytes rsegs m (wa 6155548) 4 = Some (TW.sub Bw TW.A_Cfg_ack_timeout_ms 4).
Proof.
  intros m Bw HW. unfold csw_view in HW.
  split; [exact (CISA.cis_rdf rsegs TMAP_B m Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 216 4 TMAP_B_ok HW TMAP_B_GOT
                   ltac:(lia) ltac:(unfold TW.SZ_GOT; lia))|].
  split; [exact (CISA.cis_rdf rsegs TMAP_B m Bw TW.OFF_OW TB_OW TW.SZ_OW 216 4 TMAP_B_ok HW TMAP_B_OW
                   ltac:(lia) ltac:(unfold TW.SZ_OW; lia))|].
  split; [exact (CISA.cis_rdf rsegs TMAP_B m Bw TW.OFF_M TB_M TW.SZ_M 96 4 TMAP_B_ok HW TMAP_B_M
                   ltac:(lia) ltac:(unfold TW.SZ_M; lia))|].
  split; [exact (CISA.cis_rdf rsegs TMAP_B m Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok HW TMAP_B_g_now
                   ltac:(lia) ltac:(unfold TW.SZ_g_now; lia))|].
  split; [exact (CISA.cis_rdf rsegs TMAP_B m Bw TW.OFF_M TB_M TW.SZ_M 112 8 TMAP_B_ok HW TMAP_B_M
                   ltac:(lia) ltac:(unfold TW.SZ_M; lia))|].
  exact (CISA.cis_rdf rsegs TMAP_B m Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 28 4 TMAP_B_ok HW TMAP_B_g_cfg
           ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
Qed.

(* ---- the run from the entry to the call ---- *)

(* What the run leaves at the callee's entry (image A's cis_post1 at image B's addresses and world table). *)
Definition cis_post1 (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (ms' : machine_state) : Prop :=
  exists (a2' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 CIS_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2
                  (Z_to_bv 64 CIS_M) (Z_to_bv 64 CIS_S1) (Z_to_bv 64 CIS_GS) (Z_to_bv 64 (TW.g_now Bw))
                  a2' a3 a4 a5 a6 a7 (Z_to_bv 64 CIS_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CIS_CALLEE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
    tw_at TMAP_B (csw_view m') Bw.

Lemma cis_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    TG.G_HARNESS_B_HI <= bv_unsigned sp - 32 ->
    TW.GOT_acked Bw = TW.OW_acked Bw ->
    (TW.M_fly_on Bw <> 0 ->
     (TW.g_now Bw - TW.M_fly_sent Bw) mod 2 ^ 64 < (TW.Cfg_ack_timeout_ms Bw * 1000) mod 2 ^ 64) ->
    ExecF.rng RNG (bv_unsigned sp - 32) 32 ->
    ExecF.rng RNG 6180920 4 -> ExecF.rng RNG 6237624 4 -> ExecF.rng RNG 6155840 4 ->
    ExecF.rng RNG 6155648 8 -> ExecF.rng RNG 6155856 8 -> ExecF.rng RNG 6155548 4 ->
    ExecF.evtF rsegs RNG
      (cis_post1 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIS_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw HW ST HLO HOFF EA FLY1 RFR RGOT ROW RFO RNOW RFS RACK.
  unfold CIS_ENTRY.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (CISA.cis_ranges Bw) as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6).
  unfold TG.G_HARNESS_B_HI in HOFF.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* 0x85fdc - 0x85fec: the frame and the four saves *)
  step. step. step. step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  assert (HW0 : tw_at TMAP_B (csw_view m0) Bw)
    by (apply (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1); unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia).
  destruct (cis_reads m0 Bw HW0) as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6).
  (* 0x85ff0 - 0x86000: GOT.acked and OW.acked; bne not taken *)
  step. step. step. step. CISA.cis_fields Bw. rewrite EA.
  step. rewrite bv_eqb_refl. cbn [negb].
  (* 0x86004 - 0x86014: s0 = &M, a0 = M.fly_on, s2, s1 *)
  step. step. step. step. step. CISA.cis_fields Bw.
  (* 0x86038 - 0x86044: a1 = g_now, a0 = &g_s, the call *)
  assert (TAIL : forall x10 x11 x12 : word,
    ExecF.evtF rsegs RNG
      (cis_post1 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Bw)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 6155744) (Z_to_bv 64 6156308)
               x10 x11 x12 a3 a4 a5 a6 a7 (Z_to_bv 64 6156304) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 548920) fc None m0 (seg_rom rsegs))).
  { intros x10 x11 x12.
    step. step. step. step. CISA.cis_fields Bw.
    apply evtF_done. unfold cis_post1. exists x12, m0.
    split; [reflexivity|]. split; [exact MU1|]. split; [exact WM|]. split; [exact FR | exact HW0]. }
  (* 0x86018: beqz M.fly_on *)
  step.
  destruct (Z.eq_dec (TW.M_fly_on Bw) 0) as [F0|F0].
  { CISA.cis_br true. apply TAIL. }
  CISA.cis_br false.
  specialize (FLY1 F0).
  (* 0x8601c - 0x86034: g_now - M.fly_sent against ack_timeout_ms * 1000; bgeu not taken *)
  step. step. step. CISA.cis_fields Bw. step. step. step.
  step. CISA.cis_br false.
  apply TAIL.
Qed.

(* ---- the run from the callee's return to the return to the caller ---- *)

Lemma cis_run2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (d : Z) (vra vs0 vs1 vs2 : word),
    tw_at TMAP_B (csw_view m) Bw ->
    0 <= d < 2 ^ 64 ->
    TW.g_now Bw <= d -> d <= (TW.g_now Bw + 1000000) mod 2 ^ 64 ->
    (TW.M_fly_on Bw <> 0 ->
     d <= (TW.M_fly_sent Bw + (TW.Cfg_ack_timeout_ms Bw * 1000) mod 2 ^ 64) mod 2 ^ 64) ->
    0 <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
    ExecF.rng RNG (bv_unsigned sp) 32 ->
    ExecF.rng RNG 6155648 8 -> ExecF.rng RNG 6155840 4 -> ExecF.rng RNG 6155856 8 -> ExecF.rng RNG 6155548 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 vs0 vs1 (Z_to_bv 64 d) a1' a2' a3'
                       a4 a5 a6 a7 vs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 CIS_M) (Z_to_bv 64 CIS_S1) (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 CIS_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIS_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Bw d vra vs0 vs1 vs2 HW Rd D1 D2 FLY2 Hsp0 Hsp1 FR RFR RNOW RFO RFS RACK.
  unfold CIS_M, CIS_S1, CIS_S2, CIS_RET.
  pose proof (CISA.cis_ranges Bw) as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6).
  destruct (cis_reads m Bw HW) as (_ & _ & RD3 & RD4 & RD5 & RD6).
  (* 0x86048 - 0x8604c: a1 = g_now; bltu d, g_now not taken *)
  step. CISA.cis_fields Bw.
  step. CISA.cis_br false.
  (* 0x86050 - 0x8605c: a1 = g_now + 1000000; bltu a1, d not taken *)
  step. step. step.
  step. CISA.cis_br false.
  (* 0x86060 - 0x86064: a1 = M.fly_on; beqz to the epilogue *)
  step. CISA.cis_fields Bw.
  step.
  assert (EPI : forall x11 x12 x13 : word,
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 vs0 vs1 (Z_to_bv 64 d) a1' a2' a3'
                       a4 a5 a6 a7 vs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 6155744) (Z_to_bv 64 6156308) (Z_to_bv 64 d) x11 x12 x13
               a4 a5 a6 a7 (Z_to_bv 64 6156304) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 548992) fc None m (seg_rom rsegs))).
  { intros x11 x12 x13.
    step. step. step. step. step. step.
    apply evtF_done. exists x11, x12, x13. reflexivity. }
  destruct (Z.eq_dec (TW.M_fly_on Bw) 0) as [F0|F0].
  { CISA.cis_br true. apply EPI. }
  CISA.cis_br false.
  specialize (FLY2 F0).
  (* 0x86068 - 0x8607c: ack_timeout_ms * 1000 + M.fly_sent; bltu not taken *)
  step. step. CISA.cis_fields Bw. step. step. step.
  step. CISA.cis_br false.
  apply EPI.
Qed.

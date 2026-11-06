(* check_latest_queue_seg_runs: the four footprint runs (lib/Lib/ExecF.v evtF) of the image-A walk of
   check_latest_queue (lib/A/Prog/check_latest_queue_cgW.v), between the cuts the bcmp call makes:

     clq_run_entry   CLQ_ENTRY (+0x00) -> CLQ_HEAD (+0x80): the 80-byte frame and the nine saves, the test of
                     g_s.queued against g_nq (the trap is refuted by the model's S_queued = g_nq), the two pointers
                     into g_s.queue, the loop counter queued + 1, the shadow base read through the runtime cells,
                     and the bases g_q, g_cmd and the stride 40;
     clq_run_exit    CLQ_HEAD -> the return: the counter reaches 0 (i = queued), so the epilogue reloads ra and
                     s0 .. s7 and gives the frame back;
     clq_run_body    CLQ_HEAD -> CLQ_BCMP (+0xe8, the call of the bcmp wrapper): one turn of the loop, with the
                     three instrumented checks falling through (the shadow byte of each payload is 0, so no
                     __asan_report_* entry is reached) and the length test refuted by the model;
     clq_run_ret     CLQ_BCMP_RET (+0xec) -> CLQ_HEAD at i + 1: the bcmp result, which the model makes 0, so the
                     trap at +0xf8 is not reached.

   The loop body writes no memory, so clq_run_body and clq_run_ret leave the memory they were given; only the
   prologue of clq_run_entry stores, and only into its own frame. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c check_latest_queue_seg_facts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The addresses of the walk's cuts, and the frame. *)
Definition CLQ_ENTRY : Z := 0x85e70.
Definition CLQ_HEAD : Z := 0x85ef0.
Definition CLQ_BCMP : Z := 0x42cf8.
Definition CLQ_BCMP_RET : Z := 0x85f5c.
Definition CLQ_FR : Z := 80.

(* What the nine saves left in the frame, in address order from sp - 80. *)
Definition clq_frame_cells (junk : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : list cell :=
  [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The register map at CLQ_HEAD of turn i, with the counter cnt (queued + 1 - i): the four live pointers, the
   shadow base, the two bases and the stride; ra, the temporaries and a1 .. a7 are whatever the last bcmp call
   left. *)
Definition clq_head_regs (sp0 cnt i : Z) (gp tp s8 s9 s10 s11 : word)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) : bvmap 5 word :=
  mkR ra' (Z_to_bv 64 (sp0 + -80)) gp tp t0' t1' t2'
      (Z_to_bv 64 (6160568 + 32 * i)) (Z_to_bv 64 (6233088 + 4 * i)) (Z_to_bv 64 (6160544 + 32 * i))
      a1' a2' a3' a4' a5' a6' a7'
      (Z_to_bv 64 cnt) (Z_to_bv 64 2147450880) (Z_to_bv 64 (6233088 + 4 * i))
      (Z_to_bv 64 40) (Z_to_bv 64 6181888) s7' s8 s9 s10 s11 t3' t4' t5' t6'.

(* ============================================================================
   clq_run_entry
   ============================================================================ *)

Definition clq_post_entry (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (queued : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
         (junk : list byte) (m' : word -> option byte),
    ms' = MS (clq_head_regs (bv_unsigned sp) (queued + 1) 0 gp tp s8 s9 s10 s11
                ra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7 t3' t4' t5' t6')
             F (Z_to_bv 64 CLQ_HEAD) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -80) (clq_frame_cells junk ra s0 s1 s2 s3 s4 s5 s6 s7).

Lemma clq_run_entry :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    TW.S_queued Bw = TW.g_nq Bw ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CLQ_FR <= bv_unsigned sp -> 2 ^ 46 <= bv_unsigned sp <= 2 ^ 47 ->
    asan_cells m ->
    ExecF.rng RNG (bv_unsigned sp - CLQ_FR) CLQ_FR ->
    ExecF.rng RNG 671888 8 -> ExecF.rng RNG 707064 8 ->
    ExecF.rng RNG 6176928 4 -> ExecF.rng RNG 6158688 4 ->
    ExecF.evtF rsegs RNG
      (clq_post_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (TW.g_nq Bw))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLQ_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw HW HEQ ST HLO HSP CELLS RFR RGOT RCELL RQD RNQ.
  unfold CLQ_FR, CLQ_ENTRY in *.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (clq_rngs4 Bw TW.A_S_queued) as Rqd.
  pose proof (clq_rngs4 Bw TW.OFF_g_nq) as Rnq.
  pose proof (clq_rng4 Bw TW.A_S_queued) as Uqd.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  (* +0x00 .. +0x24: the frame and the nine saves *)
  do 10 step.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -80) _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF (bv_unsigned sp + -80) ?cs |- _ => rename H into FR end.
  (* the world and the runtime cells, after the stores *)
  assert (HWF : tw_at TMAP_A (csw_view mF) Bw).
  { apply (clq_kept m mF (bv_unsigned sp - 80) (bv_unsigned sp) Bw HW MU).
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia. }
  destruct CELLS as (HCK & HGC & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in HCK, HGC.
  assert (CK0 : bytes_at rsegs mF 707064 (le8 (wa 2147450880)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact HCK]).
  assert (GCK0 : bytes_at rsegs mF 671888 (le8 (wa 707064)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact HGC]).
  clear HCK HGC.
  assert (RDG : ov_read_bytes rsegs mF (wa 671888) 8 = Some (le8 (wa 707064))).
  { replace (wa 671888) with (wa (671888 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs mF 671888 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  assert (RDC : ov_read_bytes rsegs mF (wa 707064) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 707064) with (wa (707064 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs mF 707064 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  (* the two world loads of the test *)
  pose proof (clq_rd mF Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 18144 4 HWF TMAP_A_g_s ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia)) as RDqd.
  unfold TA_g_s in RDqd. change (TW.OFF_g_s + 18144) with TW.A_S_queued in RDqd.
  pose proof (clq_rd mF Bw TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4 HWF TMAP_A_g_nq ltac:(lia)
    ltac:(unfold TW.SZ_g_nq; lia)) as RDnq.
  unfold TA_g_nq in RDnq. rewrite Z.add_0_r in RDnq.
  replace (TW.OFF_g_nq + 0) with TW.OFF_g_nq in RDnq by lia.
  (* +0x28 .. +0x38: a0 = g_s + 0x4000 *)
  do 5 step.
  (* +0x3c: a0 = g_s.queued *)
  step. rewrite lw_world.
  (* +0x40: a2 = g_nq *)
  step. rewrite lw_world.
  (* +0x44: bne a0, a2 would trap; the model makes them equal *)
  step.
  rewrite clq_eqb_lit by lia.
  rewrite clq_s32_eq.
  change (TW.u_at Bw TW.A_S_queued 4) with (TW.S_queued Bw).
  change (TW.u_at Bw TW.OFF_g_nq 4) with (TW.g_nq Bw).
  replace (TW.S_queued Bw =? TW.g_nq Bw) with true by (symmetry; apply Z.eqb_eq; exact HEQ).
  cbn [negb]. cbv iota.
  (* +0x48 .. +0x7c: the pointers, the counter, the shadow base and the bases *)
  do 14 step.
  rewrite (clq_slsr (TW.s32_at Bw TW.A_S_queued) (TW.u_at Bw TW.A_S_queued 4)
             (clq_rng4 Bw TW.A_S_queued) (clq_s32_mod Bw TW.A_S_queued)).
  change (TW.u_at Bw TW.A_S_queued 4) with (TW.S_queued Bw).
  rewrite HEQ.
  apply evtF_done. unfold clq_post_entry, clq_head_regs.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact FR].
Qed.

(* ============================================================================
   clq_run_exit
   ============================================================================ *)

Definition clq_post_exit (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom rsegs).

Lemma clq_run_exit :
  forall (RNG : ExecF.footprint) (sp0 : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (ra0 r0 r1 r2 r3 r4 r5 r6 r7 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    2 ^ 46 <= sp0 <= 2 ^ 47 ->
    sp = Z_to_bv 64 (sp0 + -80) -> s2 = Z_to_bv 64 1 ->
    rw_cells rsegs m (sp0 + -80) (clq_frame_cells junk ra0 r0 r1 r2 r3 r4 r5 r6 r7) ->
    ExecF.rng RNG (sp0 + -80) 80 ->
    ExecF.evtF rsegs RNG
      (clq_post_exit ra0 (Z_to_bv 64 sp0) gp tp r0 r1 r2 r3 r4 r5 r6 r7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLQ_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros RNG sp0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 r0 r1 r2 r3 r4 r5 r6 r7 F fc m junk HSP HSPE HS2 FR RFR.
  subst sp s2.
  unfold clq_frame_cells, CLQ_HEAD in *.
  (* +0x80: the counter reaches 0 *)
  step.
  (* +0x84: beq s2, zero is taken *)
  step.
  rewrite clq_eqb0 by lia.
  cbn [Z.eqb]. cbv iota.
  (* +0x128 .. +0x150: the epilogue *)
  do 11 step.
  apply evtF_done. unfold clq_post_exit.
  replace (Z_to_bv 64 (sp0 + -80 + 80)) with (Z_to_bv 64 sp0) by (f_equal; lia).
  do 15 eexists. reflexivity.
Qed.

(* ============================================================================
   clq_run_body
   ============================================================================ *)

Definition clq_post_body (sp0 cnt i : Z) (gp tp s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q len : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR (Z_to_bv 64 CLQ_BCMP_RET) (Z_to_bv 64 (sp0 + -80)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (6160568 + 32 * (i + 1))) (Z_to_bv 64 (6233088 + 4 * (i + 1)))
                  (Z_to_bv 64 (6160544 + 32 * i)) (Z_to_bv 64 (6181888 + q * 40 + 12))
                  (Z_to_bv 64 len) a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (cnt + -1)) (Z_to_bv 64 2147450880)
                  (Z_to_bv 64 (6233088 + 4 * (i + 1))) (Z_to_bv 64 40) (Z_to_bv 64 6181888)
                  (Z_to_bv 64 (6160544 + 32 * (i + 1))) s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 CLQ_BCMP) fc None m (seg_rom rsegs).

Lemma clq_run_body :
  forall (RNG : ExecF.footprint) (sp0 cnt i : Z) (Bw : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    sp = Z_to_bv 64 (sp0 + -80) ->
    s0 = Z_to_bv 64 (6160568 + 32 * i) -> s1 = Z_to_bv 64 (6233088 + 4 * i) ->
    a0 = Z_to_bv 64 (6160544 + 32 * i) -> s2 = Z_to_bv 64 cnt ->
    s3 = Z_to_bv 64 2147450880 -> s4 = Z_to_bv 64 (6233088 + 4 * i) ->
    s5 = Z_to_bv 64 40 -> s6 = Z_to_bv 64 6181888 ->
    tw_at TMAP_A (csw_view m) Bw ->
    clq_zsh m 6233088 4096 -> clq_zsh m 6158784 18264 -> clq_zsh m 6181888 40960 ->
    2 <= cnt <= 2 ^ 32 ->
    0 <= i -> i < 1024 -> i < 512 -> TW.Q_at Bw i < 1024 ->
    TW.S_queue_len Bw i = TW.Cmd_len Bw (TW.Q_at Bw i) ->
    ExecF.rng RNG 6233088 4096 -> ExecF.rng RNG 2148230016 512 ->
    ExecF.rng RNG 6158784 18264 -> ExecF.rng RNG 2148220728 2283 ->
    ExecF.rng RNG 6181888 40960 -> ExecF.rng RNG 2148223616 5120 ->
    ExecF.evtF rsegs RNG
      (clq_post_body sp0 cnt i gp tp s8 s9 s10 s11 F fc m (TW.Q_at Bw i) (TW.S_queue_len Bw i))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLQ_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros RNG sp0 cnt i Bw
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Esp Es0 Es1 Ea0 Es2 Es3 Es4 Es5 Es6
    HW ZQ ZS ZC Hcnt Hi0 Hi1 Hi2 Hq HLEN RQ RSQ RS RSS RC RSC.
  subst sp s0 s1 a0 s2 s3 s4 s5 s6.
  unfold CLQ_HEAD in *.
  assert (Hqz : 0 <= TW.Q_at Bw i) by (unfold TW.Q_at; apply TWorldLemmas.u_at_range).
  pose proof (clq_rng1 Bw (TW.A_S_queue_len i)) as Rln.
  pose proof (clq_rng1 Bw (TW.A_Cmd_len (TW.Q_at Bw i))) as Rcl.
  (* the three shadow bytes the checks read *)
  pose proof (clq_zsh_rd m 6233088 4096 (6233088 + 4 * i) ZQ ltac:(lia)) as SH1.
  pose proof (clq_zsh_rd m 6158784 18264 (6160568 + 32 * i) ZS ltac:(lia)) as SH2.
  pose proof (clq_zsh_rd m 6181888 40960 (6181888 + TW.Q_at Bw i * 40 + 36) ZC ltac:(lia)) as SH3.
  unfold ASAN_K in SH1, SH2, SH3.
  (* the three world loads *)
  pose proof (clq_rd m Bw TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * i) 4 HW TMAP_A_g_q ltac:(lia)
    ltac:(unfold TW.SZ_g_q; lia)) as RDq.
  unfold TA_g_q in RDq.
  pose proof (clq_rd m Bw TW.OFF_g_s TA_g_s TW.SZ_g_s (1784 + 32 * i) 1 HW TMAP_A_g_s ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia)) as RDln.
  unfold TA_g_s in RDln.
  replace (6158784 + (1784 + 32 * i)) with (6160568 + 32 * i) in RDln by lia.
  replace (TW.OFF_g_s + (1784 + 32 * i)) with (TW.A_S_queue_len i) in RDln
    by (unfold TW.A_S_queue_len; lia).
  pose proof (clq_rd m Bw TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * TW.Q_at Bw i + 36) 1 HW TMAP_A_g_cmd
    ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)) as RDcl.
  unfold TA_g_cmd in RDcl.
  replace (6181888 + (40 * TW.Q_at Bw i + 36)) with (6181888 + TW.Q_at Bw i * 40 + 36) in RDcl by lia.
  replace (TW.OFF_g_cmd + (40 * TW.Q_at Bw i + 36)) with (TW.A_Cmd_len (TW.Q_at Bw i)) in RDcl
    by (unfold TW.A_Cmd_len; lia).
  (* +0x80, +0x84: the counter is not 0 *)
  step. step.
  rewrite clq_eqb0 by lia.
  replace ((cnt + -1) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb]. cbv iota.
  (* +0x88 .. +0x94: the check of the load of g_q[i] *)
  step. rewrite (unsigned_lit (6233088 + 4 * i)) by lia. rewrite clq_shr3. step. step.
  step. rewrite sxb_eq0, clq_sxb0. cbn [Z.eqb]. cbn [negb]. cbv iota.
  (* +0x98 .. +0xa8: the check of the load of g_s.queue[i].len, and q *)
  step. rewrite (unsigned_lit (6160568 + 32 * i)) by lia. rewrite clq_shr3. step. step.
  step. rewrite lwu_world.
  change (TW.u_at Bw (TW.OFF_g_q + 4 * i) 4) with (TW.Q_at Bw i).
  step. rewrite sxb_eq0, clq_sxb0. cbn [Z.eqb]. cbn [negb]. cbv iota.
  (* +0xac .. +0xc8: the address of g_cmd[q].len, its check, and the queue entry's length *)
  step. rewrite ?(unsigned_lit (TW.Q_at Bw i)) by lia.
  step. step.
  step. rewrite (unsigned_lit (6181888 + TW.Q_at Bw i * 40 + 36)) by lia. rewrite clq_shr3. step. step.
  step. rewrite lbu_world.
  step. rewrite sxb_eq0, clq_sxb0. cbn [Z.eqb]. cbn [negb]. cbv iota.
  (* +0xcc, +0xd0: the two lengths agree, so the trap is not reached *)
  step. rewrite lbu_world.
  step. rewrite clq_eqb_lit by lia.
  change (TW.u_at Bw (TW.A_S_queue_len i) 1) with (TW.S_queue_len Bw i).
  change (TW.u_at Bw (TW.A_Cmd_len (TW.Q_at Bw i)) 1) with (TW.Cmd_len Bw (TW.Q_at Bw i)).
  replace (TW.S_queue_len Bw i =? TW.Cmd_len Bw (TW.Q_at Bw i)) with true
    by (symmetry; apply Z.eqb_eq; exact HLEN).
  cbn [negb]. cbv iota.
  (* +0xd4 .. +0xe8: the four pointers and the call *)
  do 6 step.
  apply evtF_done. unfold clq_post_body, CLQ_BCMP_RET.
  replace (6160568 + 32 * i + 32) with (6160568 + 32 * (i + 1)) by lia.
  replace (6233088 + 4 * i + 4) with (6233088 + 4 * (i + 1)) by lia.
  replace (6160544 + 32 * i + 32) with (6160544 + 32 * (i + 1)) by lia.
  do 12 eexists. reflexivity.
Qed.

(* ============================================================================
   clq_run_ret
   ============================================================================ *)

Lemma clq_run_ret :
  forall (RNG : ExecF.footprint) (sp0 cnt i : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    sp = Z_to_bv 64 (sp0 + -80) -> a0 = Z_to_bv 64 0 ->
    s0 = Z_to_bv 64 (6160568 + 32 * (i + 1)) -> s1 = Z_to_bv 64 (6233088 + 4 * (i + 1)) ->
    s2 = Z_to_bv 64 (cnt + -1) -> s3 = Z_to_bv 64 2147450880 ->
    s4 = Z_to_bv 64 (6233088 + 4 * (i + 1)) -> s5 = Z_to_bv 64 40 -> s6 = Z_to_bv 64 6181888 ->
    s7 = Z_to_bv 64 (6160544 + 32 * (i + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (b1' : word),
         ms' = MS (clq_head_regs sp0 (cnt + -1) (i + 1) gp tp s8 s9 s10 s11
                     ra t0 t1 t2 b1' a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 (6160544 + 32 * (i + 1))) t3 t4 t5 t6)
                  F (Z_to_bv 64 CLQ_HEAD) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLQ_BCMP_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG sp0 cnt i
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Esp Ea0 Es0 Es1 Es2 Es3 Es4 Es5 Es6 Es7.
  subst sp a0 s0 s1 s2 s3 s4 s5 s6 s7.
  unfold CLQ_BCMP_RET in *.
  (* +0xec, +0xf0: a1 = the result, a0 = s7 *)
  step. step.
  (* +0xf4: beq a1, zero is taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  apply evtF_done. unfold clq_head_regs, CLQ_HEAD. eexists. reflexivity.
Qed.

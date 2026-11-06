From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_keepalive_settle_c check_keepalive_settle_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_keepalive_settle_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module KA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_settle_F.

(* Proof of check_keepalive_settle_contract_F (image B, entry 0x860a4, frame 16 bytes), with StepF's step: image A's
   walk (lib/A/Prog/check_keepalive_settle_F.v) at image B's addresses, world table TMAP_B and hull. The lemmas it
   takes from that file (KA.ckk_model, ckk_eqb, ckk_ltu, ckk_rdf) name no image.

   The walk (statement comment, check_keepalive_settle_c.v:21-44):
     0x860a4-0x860a8  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x860ac-0x860b0  a0 = g_raw (4-byte load at 0x5ded60); 0x860b4 bnez a0 -> the return 0x860ec.
     0x860b8-0x860bc  a0 = 0x5dede0 (M); 0x860c0 a1 = M.state; 0x860c4 a2 = 2; 0x860c8 bne a1,a2 -> 0x860ec.
     0x860cc          a1 = M.fly.on; 0x860d0 bnez a1 -> 0x860ec.
     0x860d4-0x860d8  a1 = g_now (8 bytes at 0x5ded80); 0x860dc a2 = M.backoff_until; 0x860e0 bltu a1,a2 -> 0x860ec.
     0x860e4          a0 = M.next_ka; 0x860e8 bgeu a1,a0 -> the trap path 0x860f8.
     0x860ec-0x860f4  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path (0x860f8 __asan_handle_no_return, 0x860fc abort, then the unimp word 0xc0001073 at 0x86100) is
   reached only through the bgeu at 0x860e8, which the model premise rules out (KA.ckk_model): when the four tests
   before it fall through, g_now < M.next_ka. The function has no UBSan check of its own. After the ra store every
   load reads the world at the new memory (TMAP_B_kept), as sub Bw (offset) n (KA.ckk_rdf). *)

(* the return at 0x860ec: ld ra; addi sp; ret, and the post *)
Ltac ckkb_ret FR ST sp HW0 :=
  step; step; step;
  apply evtF_done; do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  split; [release_frame FR ST (bv_unsigned sp); exact ST|];
  split; [reflexivity | exact HW0].

Theorem check_keepalive_settle_holds_F : check_keepalive_settle_contract_F.
Proof.
  unfold check_keepalive_settle_contract_F, CHECK_KEEPALIVE_SETTLE, CHECK_KEEPALIVE_SETTLE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RRAW RST RFLY RNOW RBO RKA.
  destruct (KA.ckk_model Bw Bw' HM) as (-> & DUE). clear HM.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  rewrite check_keepalive_settle_raw_at in RRAW. rewrite check_keepalive_settle_state_at in RST.
  rewrite check_keepalive_settle_fly_on_at in RFLY. rewrite check_keepalive_settle_now_at in RNOW.
  rewrite check_keepalive_settle_backoff_at in RBO. rewrite check_keepalive_settle_next_ka_at in RKA.
  pose proof (TWorldLemmas.s32_range Bw TW.OFF_g_raw) as V1.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_state) as V2.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_fly_on) as V3.
  pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8) as V4.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_backoff_until 8) as V5.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_next_ka 8) as V6.
  change (8 * Z.of_nat 8) with 64 in V4, V5, V6.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x860a4-0x860a8: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the world relation at the new memory, and the six world loads as read facts there *)
  assert (HW0 : tw_at TMAP_B (csw_view m0) Bw)
    by (apply (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1); unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia).
  pose proof (KA.ckk_rdf rsegs TMAP_B m0 Bw TW.OFF_g_raw TB_g_raw TW.SZ_g_raw 0 4 TMAP_B_ok HW0 TMAP_B_g_raw
    ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)) as RD1.
  change (TB_g_raw + 0) with 6155616 in RD1. change (TW.OFF_g_raw + 0) with TW.OFF_g_raw in RD1.
  pose proof (KA.ckk_rdf rsegs TMAP_B m0 Bw TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok HW0 TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD2.
  change (TB_M + 12) with 6155756 in RD2. change (TW.OFF_M + 12) with TW.A_M_state in RD2.
  pose proof (KA.ckk_rdf rsegs TMAP_B m0 Bw TW.OFF_M TB_M TW.SZ_M 96 4 TMAP_B_ok HW0 TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD3.
  change (TB_M + 96) with 6155840 in RD3. change (TW.OFF_M + 96) with TW.A_M_fly_on in RD3.
  pose proof (KA.ckk_rdf rsegs TMAP_B m0 Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok HW0 TMAP_B_g_now
    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as RD4.
  change (TB_g_now + 0) with 6155648 in RD4. change (TW.OFF_g_now + 0) with TW.OFF_g_now in RD4.
  pose proof (KA.ckk_rdf rsegs TMAP_B m0 Bw TW.OFF_M TB_M TW.SZ_M 56 8 TMAP_B_ok HW0 TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD5.
  change (TB_M + 56) with 6155800 in RD5. change (TW.OFF_M + 56) with TW.A_M_backoff_until in RD5.
  pose proof (KA.ckk_rdf rsegs TMAP_B m0 Bw TW.OFF_M TB_M TW.SZ_M 48 8 TMAP_B_ok HW0 TMAP_B_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD6.
  change (TB_M + 48) with 6155792 in RD6. change (TW.OFF_M + 48) with TW.A_M_next_ka in RD6.
  (* 0x860ac-0x860b0: a0 = g_raw; 0x860b4 bnez a0 *)
  step. step. rewrite lw_world.
  step. rewrite KA.ckk_eqb by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw TW.OFF_g_raw) 0) as [E1|E1]; cbn [negb]; [ | ckkb_ret FR ST sp HW0].
  (* 0x860b8-0x860bc: a0 = M; 0x860c0 a1 = M.state; 0x860c4 a2 = 2; 0x860c8 bne a1,a2 *)
  step. step. step. rewrite lw_world. step.
  step. rewrite KA.ckk_eqb by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw TW.A_M_state) 2) as [E2|E2]; cbn [negb]; [ | ckkb_ret FR ST sp HW0].
  (* 0x860cc: a1 = M.fly.on; 0x860d0 bnez a1 *)
  step. rewrite lw_world.
  step. rewrite KA.ckk_eqb by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw TW.A_M_fly_on) 0) as [E3|E3]; cbn [negb]; [ | ckkb_ret FR ST sp HW0].
  (* 0x860d4-0x860d8: a1 = g_now; 0x860dc a2 = M.backoff_until; 0x860e0 bltu a1,a2 *)
  step. step. rewrite ld_world. step. rewrite ld_world.
  step. rewrite KA.ckk_ltu by lia.
  destruct (Z.ltb_spec (TW.u_at Bw TW.OFF_g_now 8) (TW.u_at Bw TW.A_M_backoff_until 8)) as [E4|E4]; cbn [negb];
    [ckkb_ret FR ST sp HW0 | ].
  (* 0x860e4: a0 = M.next_ka; 0x860e8 bgeu a1,a0: not taken, by the model premise *)
  step. rewrite ld_world.
  step. rewrite KA.ckk_ltu by lia.
  destruct (Z.ltb_spec (TW.u_at Bw TW.OFF_g_now 8) (TW.u_at Bw TW.A_M_next_ka 8)) as [E5|E5]; cbn [negb];
    [ckkb_ret FR ST sp HW0 | exfalso; specialize (DUE E1 E2 E3 E4); lia].
Qed.

Print Assumptions check_keepalive_settle_holds_F.

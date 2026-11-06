(* The walk of maybe_online (transport/src/diginet_session.c:176-182) in the ubsan image, 0x17f10, ms inlined: the
   alignment check of s, the three tests of :178, the next keepalive of :179 and the tail call of set_state (:180,
   j at 0x17f54) with no frame of its own. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC WalkNotify set_state_c maybe_online_c.
Import ListNotations.
Open Scope Z_scope.

Theorem maybe_online_holds : set_state_contract -> maybe_online_contract.
Proof.
  intros SETS. unfold maybe_online_contract, maybe_online_ENTRY, maybe_online_FRAME.
  unfold set_state_contract, set_state_ENTRY, set_state_FRAME in SETS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' TF -> WM GF HM TFA RR S16 ST LO WOS MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold w_off_stack in WOS.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  cbv beta zeta delta [maybe_online_m] in HM.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  set (B2 := set_S_next_keepalive_us B (u64 (S_last_rx_us B + ms_m (S_cfg_keepalive_ms B)))) in HM.
  assert (LB2 : length B2 = Z.to_nat W_LEN) by (unfold B2, set_S_next_keepalive_us; wlen).
  assert (GB2 : g_fail_next B2 = g_fail_next B)
    by (unfold B2, g_fail_next, set_S_next_keepalive_us; rewrite !rd_upd_W by wside; reflexivity).
  step. step. try if_false.                    (* andi a1, a0, 7; bnez: s is 8-aligned *)
  (* the exits of :178: ret with the world unchanged *)
  assert (EXIT : forall x11 x12,
    B' = B ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 384, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) x11 x12 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17f58) fc None m (seg_rom rsegs))).
  { intros x11 x12 ->.
    step.                                      (* ret *)
    apply evt_done. do 16 eexists. split; [reflexivity |].
    refine (conj MU (conj WMo (conj MI (conj ST (conj WM GF))))). }
  step. step.                                  (* lw a1, 112(a0): s->state; li a2, 1 *)
  destruct (Z.eqb_spec (S_state B) DIGINET_S_WAKING) as [E1 | E1].
  2: { cbv beta iota delta [andb] in HM. injection HM as <-.
       assert (NE : bv_unsigned (Z_to_bv 64 (s32_at B 1760)) <> 1).
       { pose proof (bv_unsigned_ne (s32_at B 1760) 1 ltac:(pose proof (s32_range B 1760); lia) ltac:(lia) E1) as X.
         rewrite (unsigned_lit 1) in X by lia. exact X. }
       step. if_true. apply EXIT. reflexivity. }
  assert (E1' : s32_at B 1760 = 1) by exact E1. rewrite E1'.
  step. if_false.
  step.                                        (* lw a1, 144(a0): s->wake_acked *)
  destruct (Z.eqb_spec (S_wake_acked B) 0) as [E2 | E2].
  { cbv beta iota delta [andb negb] in HM. injection HM as <-.
    assert (E2' : s32_at B 1792 = 0) by exact E2. rewrite E2'.
    step. if_true. apply EXIT. reflexivity. }
  assert (NZ2 : bv_unsigned (Z_to_bv 64 (s32_at B 1792)) <> 0)
    by (apply bv_unsigned_nz; [pose proof (s32_range B 1792); lia | exact E2]).
  step. if_false.
  step.                                        (* lw a1, 140(a0): s->e1_named_us *)
  destruct (Z.eqb_spec (S_e1_named_us B) 0) as [E3 | E3].
  { cbv beta iota delta [andb negb] in HM. injection HM as <-.
    assert (E3' : s32_at B 1788 = 0) by exact E3. rewrite E3'.
    step. if_true. apply EXIT. reflexivity. }
  assert (NZ3 : bv_unsigned (Z_to_bv 64 (s32_at B 1788)) <> 0)
    by (apply bv_unsigned_nz; [pose proof (s32_range B 1788); lia | exact E3]).
  step. if_false.
  cbv beta iota delta [andb negb] in HM.
  step. step.                                  (* lwu a1, 24(a0): cfg.keepalive_ms; ld a2, 176(a0): last_rx_us *)
  step. step. step. step. step.                (* li a3, 1000; mul; li a1, 2; add; li a2, 2 *)
  step.                                        (* sd a3, 184(a0): next_keepalive_us (:179) *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
    replace X with B2 in H; [try rename H into WM |] end.
  2: { unfold B2, set_S_next_keepalive_us, A_S_next_keepalive_us, ms_m, u64.
       change (S_last_rx_us B) with (u_at B 1824 8). change (S_cfg_keepalive_ms B) with (u_at B 1672 4).
       pose proof (u_at_range B 1672 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
       rewrite (unsigned_lit (u_at B 1672 4)) by lia.
       f_equal. apply put8_mod_eq. rewrite ?Z.mod_mod by lia. rewrite ?Z.add_mod_idemp_r by lia. f_equal. lia. }
  step.                                        (* j set_state: the tail call of :180 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
  eapply evt_cut.
  { eapply (SETS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mS lo 2 2 B2 B' TF).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - exact WM.
    - rewrite GB2. exact GF.
    - exact HM.
    - eapply tframe_at_move; [ exact TFA | exact MU | lia | lia ].
    - eapply relro_img_move; [ exact RR | exact MU | lia ].
    - exact S16.
    - exact ST.
    - exact LO.
    - exact WOS.
    - exact MI. }
  intros ms' PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & STc & WMc' & GFc). subst ms'.
  apply evt_done. do 16 eexists. split; [reflexivity |].
  refine (conj (munch_trans _ _ _ _ MU MUc) (conj (wmono_trans _ _ _ _ WMo WMc) (conj MIc (conj STc (conj WMc' GFc))))).
Qed.

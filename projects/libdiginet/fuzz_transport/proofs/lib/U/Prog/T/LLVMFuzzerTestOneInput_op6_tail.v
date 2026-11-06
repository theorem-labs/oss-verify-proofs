(* Case 6 of LLVMFuzzerTestOneInput (ubsan), 0x13c20-0x13c40 and the shared tail 0x1456c-0x14570: the end of the
   inlined m_close (fuzz_transport.c:384-385: M.fly.on = 0, m_set(S_CLOSED, R_CLOSED), here called out of line at
   0x13c2c), diginet_session_close(&g_s, g_now) (:1203), then settle(0) (:1204) and the latch 0x14574. Each call
   through its contract and llvm_mem_after_call. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  m_set_c diginet_session_close_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op6_lib.
Import ListNotations.
Open Scope Z_scope.

Section OP6T.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

Lemma op6_tail : m_set_contract -> diginet_session_close_contract -> settle_contract ->
  forall m0 Sp lo ops c X B2 B3 r B4 m j10 jio j60
         (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word) F fc,
  0 <= ops < OPS_MAX -> llvm_cursor D c ->
  llvm_mem data D regs0 m0 Sp lo X m j10 jio j60 ->
  m_set_m (set_M_fly_on X 0) S_CLOSED R_CLOSED = Some (B2, tt) ->
  diginet_session_close_m timg_ubsan None B2 (g_now B2) = Some (B3, r) ->
  settle_m B3 0 = Some (B4, tt) ->
  evt rsegs (llvm_latch data D regs0 m0 Sp lo ops c B4 F fc)
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c)) (Z_to_bv 64 7) s5 (Z_to_bv 64 (fi_n c)) s7
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c20) fc None m (seg_rom rsegs)).
Proof.
  intros MSC DSC STC.
  pose proof MSC as MSC0. unfold m_set_contract, m_set_ENTRY, m_set_FRAME in MSC0.
  pose proof DSC as DSC0.
  unfold diginet_session_close_contract, diginet_session_close_ENTRY, diginet_session_close_FRAME in DSC0.
  pose proof STC as STC0. unfold settle_contract, settle_ENTRY, settle_FRAME in STC0.
  intros m0 Sp lo ops c X B2 B3 r B4 m j10 jio j60 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 F fc
    HOPS HC HM HB2 HB3 HB4.
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) with (Z_to_bv 64 209664).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) with (Z_to_bv 64 274632).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) with (Z_to_bv 64 211312).
  pose proof HM as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & HSP & ST & HLO & HSP2 & HWL & MI & _ & WM & GF & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m X WM) as LX.
  unfold LH_K, LH_FRAME in HLO, HSP2.
  wk_facts.
  assert (USp : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MUs.
  pose proof (wmono_refl rsegs m) as WMOs.
  (* 0x13c20 sw zero, 0x60(s8): M.fly.on = 0 *)
  step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ (upd X 96 (put 4 0))] |- _ =>
    change (upd X 96 (put 4 0)) with (set_M_fly_on X 0) in H; rename H into WM1 end.
  assert (LX1 : length (set_M_fly_on X 0) = Z.to_nat W_LEN)
    by (unfold set_M_fly_on, A_M_fly_on, OFF_M; op6_lenp LX).
  assert (GF1 : g_fail_next (set_M_fly_on X 0) <= 1).
  { unfold set_M_fly_on, A_M_fly_on, OFF_M.
    rewrite (op6_gf_put X (0 + 96 + 0) 4 0 LX) by (unfold W_LEN, OFF_g_fail_next; lia). exact GF. }
  lazymatch goal with H : rw_cells rsegs ?m1 W_BASE_UBSAN [CB _ (set_M_fly_on X 0)] |- _ =>
    pose proof (llvm_mem_after_call data D regs0 m0 Sp lo 0 X (set_M_fly_on X 0) m m1 j10 jio j60 HM
                  ltac:(unfold LH_K; lia) MUs WMOs MI ST H GF1) as HM1 end.
  clear MUs WMOs MI ST WM1 GF GF1 HM.
  pose proof HM1 as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & ST & _ & _ & _ & MI & _ & WM & _ & _).
  (* 0x13c24 li a0, 3; 0x13c28 li a1, 8; 0x13c2c jal m_set *)
  step. step. step.
  eapply evt_cut.
  { eapply MSC0 with (st := 3) (why := 8) (lo := lo) (B := set_M_fly_on X 0) (B' := B2);
      [ reflexivity | reflexivity | lia | lia | rewrite USp; exact HSP | rewrite USp; exact ST
      | rewrite USp; lia | unfold w_off_stack; rewrite USp; lia | exact MI | exact WM | exact HB2 ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WMO2 & MI2 & ST2 & WM2).
  subst ms'. rewrite USp in MU2, ST2.
  assert (GF2 : g_fail_next B2 <= 1).
  { rewrite (op6_mset_gf (set_M_fly_on X 0) B2 S_CLOSED R_CLOSED LX1 HB2).
    pose proof HM1 as HM'. unfold llvm_mem in HM'.
    destruct HM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GFx & _). exact GFx. }
  pose proof (llvm_mem_after_call data D regs0 m0 Sp lo 0 (set_M_fly_on X 0) B2 _ m2 j10 jio j60 HM1
                ltac:(unfold LH_K; lia) MU2 WMO2 MI2 ST2 WM2 GF2) as HM2.
  clear ST MI WM MU2 WMO2 MI2 ST2 WM2 HM1.
  rewrite (ret_pc_even 80944) by (first [lia | reflexivity]).
  pose proof HM2 as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & ST & _ & _ & _ & MI & RO & WM & GF3 & _).
  assert (NOW : 0 <= g_now B2 < 2 ^ 64).
  { unfold g_now. pose proof (u_at_range B2 OFF_g_now 8) as R.
    change (8 * Z.of_nat 8) with 64 in R. exact R. }
  (* 0x13c30 ld a1, 0x20(s9): g_now; 0x13c34 auipc a0; 0x13c38 addi a0 (&g_s); 0x13c3c jal diginet_session_close *)
  step. step. step. step.
  eapply evt_cut.
  { eapply DSC0 with (B := B2) (TF := None) (lo := lo) (now := g_now B2) (r := r) (B' := B3);
      [ reflexivity | reflexivity | exact NOW | exact WM | exact GF3 | exact HB3 | exact I | exact RO
      | rewrite USp; exact HSP | rewrite USp; exact ST | rewrite USp; lia
      | unfold w_off_stack; rewrite USp; lia | exact MI ]. }
  intros ms' PO.
  destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                  m3 & E & MU3 & WMO3 & MI3 & ST3 & WM3 & GF4).
  subst ms'. rewrite USp in MU3, ST3.
  pose proof (llvm_mem_after_call data D regs0 m0 Sp lo 672 B2 B3 _ m3 j10 jio j60 HM2
                ltac:(unfold LH_K; lia) MU3 WMO3 MI3 ST3 WM3 GF4) as HM3.
  clear ST MI RO WM GF3 MU3 WMO3 MI3 ST3 WM3 HM2.
  rewrite (ret_pc_even 80960) by (first [lia | reflexivity]).
  pose proof HM3 as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & ST & _ & _ & _ & MI & _ & WM & _ & _).
  (* 0x13c40 j 0x1456c; 0x1456c mv a0, zero; 0x14570 jal settle *)
  step. step. step.
  eapply evt_cut.
  { eapply STC0 with (ticked := 0) (lo := lo) (B := B3) (B' := B4);
      [ reflexivity | lia | exact WM | exact HB4 | rewrite USp; exact HSP | rewrite USp; exact ST
      | rewrite USp; lia | unfold w_off_stack; rewrite USp; lia | exact MI ]. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 &
                  m4 & E & MU4 & WMO4 & MI4 & ST4 & EB & WM4).
  subst ms'. rewrite USp in MU4, ST4. subst B4.
  pose proof (llvm_mem_after_call data D regs0 m0 Sp lo 96 B3 B3 _ m4 j10 jio j60 HM3
                ltac:(unfold LH_K; lia) (lh_munch_add_world _ _ _ _ MU4) WMO4 MI4 ST4 WM4 GF4) as HM4.
  rewrite (ret_pc_even 83316) by (first [lia | reflexivity]).
  apply evt_done. unfold llvm_latch.
  do 23 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC|]. exact HM4.
Qed.

End OP6T.

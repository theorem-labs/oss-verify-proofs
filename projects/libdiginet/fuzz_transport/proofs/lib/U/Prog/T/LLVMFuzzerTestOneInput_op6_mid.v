(* Case 6 of LLVMFuzzerTestOneInput (ubsan), 0x13bec-0x13c1c: op_begin's last two writes (fuzz_transport.c:392-393;
   the machine writes M.fail before OW.desk_off, op6_bb_eq commutes them), then the inlined m_close's test (:380:
   M.desk_known, read before those writes, M.foreign, M.state against S_CLOSED; every failing test branches to
   0x13c20) and its then arm (:381-382: OW.e3 = 1, the increment folded since op_begin zeroed OW, and M.fail = 0).
   Each arm ends at 0x13c20 with the world op6_x B that m_close hands to its M.fly.on store and m_set. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op6_lib.
Import ListNotations.
Open Scope Z_scope.

Section OP6M.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

Lemma op6_mid : forall m0 Sp lo B m j10 jio j60
         (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) F fc
         (Q : machine_state -> Prop),
  length B = Z.to_nat W_LEN ->
  llvm_mem data D regs0 m0 Sp lo (op6_bg B) m j10 jio j60 ->
  (forall (a0' a1' : word) m',
     llvm_mem data D regs0 m0 Sp lo (op6_x B) m' j10 jio j60 ->
     evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                      a0' a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x39) s3 (Z_to_bv 64 7) s5 s6 s7
                      (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                      (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c20) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x39) s3 (Z_to_bv 64 7) s5 s6 s7
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13bec) fc None m (seg_rom rsegs)).
Proof.
  intros m0 Sp lo B m j10 jio j60 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 F fc Q LB HM HK.
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) with (Z_to_bv 64 209664).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) with (Z_to_bv 64 274632).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) with (Z_to_bv 64 211312).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) with (Z_to_bv 64 209664) in HK.
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) with (Z_to_bv 64 274632) in HK.
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) with (Z_to_bv 64 211312) in HK.
  pose proof HM as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & ST & HLO & _ & HWL & MI & _ & WM & GF & _).
  pose proof (op6_bg_len B LB) as Lg.
  pose proof (op6_bb_len B LB) as Lb.
  assert (GFb : g_fail_next (op6_bb B) <= 1)
    by (rewrite (op6_bb_gf B LB), <- (op6_bg_gf B LB); exact GF).
  unfold LH_K in HLO.
  wk_facts.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MUs.
  pose proof (wmono_refl rsegs m) as WMOs.
  (* 0x13bec lbu a0, 0(s9): g_fail_next; 0x13bf0 lw a1, 0(s8): M.desk_known; 0x13bf4 sw a0, 0x58(s8): M.fail;
     0x13bf8 li a0, -1; 0x13bfc sw a0, 0x240(s9): OW.desk_off *)
  step. step. step. step. step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?BW] |- _ =>
    assert (EBW : BW = op6_bb B);
    [ rewrite <- (op6_bb_eq B LB); f_equal; try reflexivity; apply bytes_eq_of_zs; vm_compute; reflexivity
    | rewrite EBW in H; clear EBW; rename H into WMb ]
  end.
  (* 0x13c00 beqz a1, 0x13c20: M.desk_known = 0 fails m_close's test *)
  step.
  pose proof (s32_range (op6_bg B) 0) as RDK.
  if_cases K1; zify_cond K1.
  { assert (EZ : M_desk_known (op6_bb B) = 0).
    { rewrite (op6_dk B LB). apply (proj1 (op6_s32_eq _ 0 RDK ltac:(lia))). exact K1. }
    assert (EC : op6_cond (op6_bb B) = false) by (unfold op6_cond, truth; rewrite EZ; reflexivity).
    eapply HK. unfold op6_x. rewrite EC. cbv beta iota.
    eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 (op6_bg B) (op6_bb B) m _ j10 jio j60 HM);
      [ unfold LH_K; lia | exact MUs | exact WMOs | exact MI | exact ST | exact WMb | exact GFb ]. }
  assert (NZ : M_desk_known (op6_bb B) <> 0).
  { rewrite (op6_dk B LB). intros E. apply K1. rewrite E. reflexivity. }
  (* 0x13c04 lw a0, 0x18(s8): M.foreign; 0x13c08 bnez a0, 0x13c20 *)
  step. step.
  pose proof (s32_range (op6_bb B) 24) as RFO.
  if_cases K2; zify_cond K2.
  { assert (NF : M_foreign (op6_bb B) <> 0).
    { change (M_foreign (op6_bb B)) with (s32_at (op6_bb B) 24). intros E. apply K2. rewrite E. reflexivity. }
    assert (EC : op6_cond (op6_bb B) = false).
    { unfold op6_cond, truth. rewrite (proj2 (Z.eqb_neq _ 0) NF). rewrite andb_false_r. reflexivity. }
    eapply HK. unfold op6_x. rewrite EC. cbv beta iota.
    eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 (op6_bg B) (op6_bb B) m _ j10 jio j60 HM);
      [ unfold LH_K; lia | exact MUs | exact WMOs | exact MI | exact ST | exact WMb | exact GFb ]. }
  assert (ZF : M_foreign (op6_bb B) = 0).
  { change (M_foreign (op6_bb B)) with (s32_at (op6_bb B) 24).
    apply (proj1 (op6_s32_eq _ 0 RFO ltac:(lia))). exact K2. }
  (* 0x13c0c lw a0, 0xc(s8): M.state; 0x13c10 li a1, 3; 0x13c14 beq a0, a1, 0x13c20 *)
  step. step. step.
  pose proof (s32_range (op6_bb B) 12) as RST.
  if_cases K3; zify_cond K3.
  { assert (E3 : M_state (op6_bb B) = S_CLOSED).
    { change (M_state (op6_bb B)) with (s32_at (op6_bb B) 12).
      apply (proj1 (op6_s32_eq _ 3 RST ltac:(lia))). exact K3. }
    assert (EC : op6_cond (op6_bb B) = false).
    { unfold op6_cond. rewrite E3, Z.eqb_refl. rewrite andb_false_r. reflexivity. }
    eapply HK. unfold op6_x. rewrite EC. cbv beta iota.
    eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 (op6_bg B) (op6_bb B) m _ j10 jio j60 HM);
      [ unfold LH_K; lia | exact MUs | exact WMOs | exact MI | exact ST | exact WMb | exact GFb ]. }
  assert (N3 : M_state (op6_bb B) <> S_CLOSED).
  { change (M_state (op6_bb B)) with (s32_at (op6_bb B) 12).
    intros E. apply K3. rewrite E. reflexivity. }
  assert (EC : op6_cond (op6_bb B) = true).
  { unfold op6_cond, truth. rewrite ZF, (proj2 (Z.eqb_neq _ 0) NZ), (proj2 (Z.eqb_neq _ S_CLOSED) N3).
    reflexivity. }
  (* 0x13c18 sw s1, 0x220(s9): OW.e3 = 1; 0x13c1c sw zero, 0x58(s8): M.fail = 0 *)
  step. step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ (upd (upd (op6_bb B) 65512 (put 4 1)) 88 (put 4 0))]
    |- _ => change (upd (upd (op6_bb B) 65512 (put 4 1)) 88 (put 4 0))
              with (set_M_fail (set_OW_e3 (op6_bb B) 1) 0) in H; rename H into WMt end.
  eapply HK. unfold op6_x. rewrite EC. cbv beta iota.
  eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 (op6_bg B) (set_M_fail (set_OW_e3 (op6_bb B) 1) 0) m _
            j10 jio j60 HM);
    [ unfold LH_K; lia | exact MUs | exact WMOs | exact MI | exact ST | exact WMt
    | rewrite (op6_then_gf B LB), <- (op6_bg_gf B LB); exact GF ].
Qed.

End OP6M.

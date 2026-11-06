(* Case 6 of LLVMFuzzerTestOneInput (ubsan), 0x13bcc-0x13be8: op_begin's two memsets (fuzz_transport.c:390-391),
   memset(&OW, 0, 0x130) and memset(&GOT, 0, 0xe0), through memset_contract and llvm_mem_after_fill. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op6_lib.
Import ListNotations.
Open Scope Z_scope.

Section OP6H.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

Lemma op6_head : memset_contract ->
  forall m0 Sp lo B m j10 jio j60
         (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) F fc
         (Q : machine_state -> Prop),
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     llvm_mem data D regs0 m0 Sp lo (op6_bg B) m' j10 jio j60 ->
     evt rsegs Q (MS (mkR ra' (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0' t1' t2' s0 (Z_to_bv 64 1)
                      a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 0x39) s3 (Z_to_bv 64 7) s5 s6 s7
                      (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                      (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13bec) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x39) s3 (Z_to_bv 64 7) s5 s6 s7
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)).
Proof.
  intros MSC. pose proof MSC as MSC0. unfold memset_contract, MEMSET in MSC0.
  intros m0 Sp lo B m j10 jio j60 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 F fc Q HM HK.
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) with (Z_to_bv 64 209664).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) with (Z_to_bv 64 274632).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) with (Z_to_bv 64 211312).
  (* 0x13bcc addi a0, s9, 0x158 (&OW); li a2, 0x130; mv a1, zero; jal memset *)
  step. step. step. step.
  pose proof HM as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & WM & GF0 & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LB.
  wk_facts.
  assert (U1 : bv_unsigned (Z_to_bv 64 274976) = 274976) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 304) = 304) by (apply unsigned_lit; lia).
  pose proof (wm_piece rsegs W_BASE_UBSAN m B 65312 (bv_unsigned (Z_to_bv 64 304))
                (bv_unsigned (Z_to_bv 64 274976)) WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST.
  eapply evt_cut; [eapply MSC0; [exact DST | exact MI] |].
  intros ms' PO. unfold memset_post in PO. destruct_exs PO.
  destruct PO as (E & MUc & WMc & MIc & CZ). subst ms'.
  clear DST WM MI U1 U2.
  pose proof (llvm_mem_after_fill data D regs0 m0 Sp lo B m _ OFF_OW SZ_OW (repeat (b8 0) (Z.to_nat SZ_OW))
                j10 jio j60 HM MUc WMc MIc CZ) as HM1.
  assert (GF1 : g_fail_next (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) <= 1).
  { unfold g_fail_next.
    rewrite op6_uo; [exact GF0 | exact LB | unfold OFF_OW; lia | unfold OFF_g_fail_next; lia
                    | rewrite repeat_length; unfold OFF_OW, SZ_OW, W_LEN; lia
                    | rewrite repeat_length; unfold OFF_OW, SZ_OW, OFF_g_fail_next; lia]. }
  specialize (HM1 ltac:(unfold OFF_OW; lia) ltac:(unfold SZ_OW; lia) ltac:(unfold OFF_OW, SZ_OW, W_LEN; lia) GF1).
  clear HM MUc WMc MIc CZ GF1.
  rewrite (ret_pc_even 80860) by (first [lia | reflexivity]).
  (* 0x13bdc addi a0, s9, 0x74 (&GOT); li a2, 0xe0; mv a1, zero; jal memset *)
  step. step. step. step.
  pose proof HM1 as HM'. unfold llvm_mem in HM'.
  destruct HM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & WM & _ & _).
  assert (U3 : bv_unsigned (Z_to_bv 64 274748) = 274748) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 224) = 224) by (apply unsigned_lit; lia).
  pose proof (wm_piece rsegs W_BASE_UBSAN _ _ 65084 (bv_unsigned (Z_to_bv 64 224))
                (bv_unsigned (Z_to_bv 64 274748)) WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST.
  eapply evt_cut; [eapply MSC0; [exact DST | exact MI] |].
  intros ms' PO. unfold memset_post in PO. destruct_exs PO.
  destruct PO as (E & MUc & WMc & MIc & CZ). subst ms'.
  clear DST WM MI U3 U4.
  pose proof (llvm_mem_after_fill data D regs0 m0 Sp lo _ _ _ OFF_GOT SZ_GOT (repeat (b8 0) (Z.to_nat SZ_GOT))
                j10 jio j60 HM1 MUc WMc MIc CZ) as HM2.
  assert (GF2 : g_fail_next (op6_bg B) <= 1) by (rewrite (op6_bg_gf B LB); exact GF0).
  specialize (HM2 ltac:(unfold OFF_GOT; lia) ltac:(unfold SZ_GOT; lia) ltac:(unfold OFF_GOT, SZ_GOT, W_LEN; lia) GF2).
  rewrite (ret_pc_even 80876) by (first [lia | reflexivity]).
  eapply HK. exact HM2.
Qed.

End OP6H.

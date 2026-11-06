(* Case 7 of the op loop in the ubsan image, 0x13b30-0x13b34 (fuzz_transport.c:1206-1208
   `case 7: g_fail_next = 1; break;`): sb s1, 0(s9) stores s1 = 1 at s9 = &g_fail_next (inside the world), then
   j 0x14574 (the latch). The model's case 7 is Some (set_g_fail_next B 1, (c1, k)) (op7_model), and
   set_g_fail_next B 1 = upd B OFF_g_fail_next (put 1 1) is the world the kit's store hook leaves. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* the model's result, by name (never injection on the world-carrying option itself) *)
Lemma op7_some_inv : forall (X B1 : list byte) (y c2 : fuzz_in) (k k1 : nat),
  Some (X, (y, k)) = Some (B1, (c2, k1)) -> X = B1 /\ y = c2.
Proof. intros X B1 y c2 k k1 H. injection H as E1 E2 E3. split; [exact E1 | exact E2]. Qed.

(* op = 7: the model's op is Some (set_g_fail_next B 1, (c1, k)) *)
Lemma op7_model : forall I B A D c k B1 c2 k1,
  snd (fuzz_u8_m D c) mod 9 = 7 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B1, (c2, k1)) ->
  B1 = set_g_fail_next B 1 /\ c2 = fst (fuzz_u8_m D c).
Proof.
  intros I B A D c k B1 c2 k1. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [x b]. cbn [fst snd]. intros H7 H.
  cbv beta iota zeta in H. rewrite H7 in H. cbn [Z.eqb Pos.eqb] in H.
  apply op7_some_inv in H. destruct H as [E1 E2]. split; [symmetry; exact E1 | symmetry; exact E2].
Qed.

Theorem llvm_op7_holds : llvm_op_stmt 7.
Proof.
  unfold llvm_op_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms A k B1 c2 k1 H HOP.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                 m & j10 & jio & j60 & -> & HOPS & HN & HC & HC1 & H7 & HM).
  destruct (op7_model timg_ubsan B A D c k B1 c2 k1 H7 HOP) as [EB EC].
  rewrite <- HC1 in EC. subst B1 c2.
  unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  pose proof (munch_refl [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof HC as HC0. unfold llvm_cursor in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  unfold off_world in HOW.
  unfold LH_K, LH_FRAME in *.
  unfold llvm_frame, llvm_saved in HRW. cbn [app] in HRW.
  wk_facts. wk_eq_fact OFF_g_fail_next.
  change (Z_to_bv 64 (LH_CASE 7)) with (Z_to_bv 64 0x13b30).
  step.                                        (* 0x13b30 sb s1, 0(s9): g_fail_next = 1 *)
  step.                                        (* 0x13b34 j 0x14574 *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
    replace X with (set_g_fail_next B 1) in H by reflexivity; rename H into HWM' end.
  apply evt_done. unfold llvm_latch. do 23 eexists. split; [reflexivity|].
  split; [exact HOPS|].
  split; [rewrite HC1; unfold llvm_cursor, fuzz_u8_m; destruct (Z.eqb_spec (fi_n c) 0); cbn [fi_off fi_n fst]; lia|].
  unfold llvm_mem.
  split; [exact HD0|]. split; [exact HDL|]. split; [unfold off_world; exact HOW|].
  split; [exact HD|]. split; [exact HSP|]. split; [exact HSTK|].
  split; [unfold LH_K; exact HLO|]. split; [unfold LH_FRAME; exact HSP2|]. split; [exact HWL|].
  split; [exact HMI|].
  split; [exact (lh_relro_munch _ _ _ _ HRO MU HWL)|].
  split; [exact HWM'|].
  split; [unfold set_g_fail_next, g_fail_next;
          rewrite u_at_upd_put; [apply Z.leb_le; reflexivity | unfold OFF_g_fail_next; lia |
            rewrite LB; unfold OFF_g_fail_next, W_LEN; lia]|].
  split; [unfold LH_FRAME; exact HMU|]. split; [exact HWMO|].
  split; [exact HJ1|]. split; [exact HJ2|]. split; [exact HJ3|].
  exact HRW.
Qed.

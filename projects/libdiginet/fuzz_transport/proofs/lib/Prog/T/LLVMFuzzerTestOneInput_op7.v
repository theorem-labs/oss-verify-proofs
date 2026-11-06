(* Case 7 of the op loop, 0x139e4-0x139e8 (fuzz_transport.c:1203-1205 `case 7: g_fail_next = 1; break;`):
   one byte store into the world, then the jump to the latch. The model's case 7 is
   Some (set_g_fail_next B 1, (c1, k)), and set_g_fail_next B 1 is upd B OFF_g_fail_next (put 1 1), which is
   what the kit's world hook leaves after the store. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* RELRO (0x213c8 + 0x98) lies below the world (0x32790), so a write inside the world keeps relro_img.
   The footprint list is written out: [inside] and [disjoint_from] are fixpoints on it, and the kit's store
   tactic reduces them with [cbn], which a named list would block. *)
Lemma relro_munch : forall m m', relro_img m ->
  munch [(W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' -> relro_img m'.
Proof.
  intros m m' HR HM i Hi.
  unfold mrd. rewrite (HM (wa (RELRO_BASE + i))).
  - exact (HR i Hi).
  - cbn [outside]. unfold wa. rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    split; [unfold RELRO_BASE, RELRO_LEN, W_BASE_PLAIN, W_LEN in *; lia | exact I].
Qed.

Section OP7.
Context (data : Z) (D : list byte).

Lemma llvm_op7 : forall Sp lo ops c c1 B m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  llvm_case data D m0 gp tp 7 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c1 (set_g_fail_next B 1)
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 B m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q H HK.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HN & HC & HC1 & HM).
  unfold llvm_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  pose proof (munch_refl [(W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  unfold llvm_cursor in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  unfold off_world in HOW. unfold off_window in HOWIN.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  unfold llvm_frame_consts, llvm_saved in HRW. cbn [app] in HRW.
  wk_facts. wk_eq_fact OFF_g_fail_next.
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb].
  unfold LLVM_FP in HMU0.
  (* 0x139e4 sb s8, 0(s9): g_fail_next = 1; 0x139e8 j 0x1428c *)
  do 2 zstep.
  apply HK. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|].
  split; [rewrite HC1; unfold llvm_cursor, fuzz_u8_m; destruct (Z.eqb_spec (fi_n c) 0); cbn; lia|].
  unfold llvm_mem.
  split; [exact HMU0|]. split; [exact HWMO0|].
  split; [assumption|].
  split; [exact HSP|].
  split; [assumption|].
  split; [exact HLO|]. split; [exact HSP2|]. split; [exact HWOS|]. split; [exact HOWS|].
  split; [exact HOW|]. split; [exact HOWIN|].
  split; [assumption|].
  split; [eapply relro_munch; [exact HRO | exact MU]|].
  split; [assumption|].
  split; [unfold set_g_fail_next, g_fail_next;
          rewrite u_at_upd_put; [reflexivity | unfold OFF_g_fail_next; lia |
            rewrite LB; unfold OFF_g_fail_next, W_LEN; lia]|].
  split; [exact HJ1|]. split; [exact HJ2|].
  assumption.
Qed.

End OP7.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths changed; 522 of its 775 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/T/TSRGlue.v, with its module paths changed; 922 of its 1003 lines of code are new or changed and 694 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/U/Prog/T/LLVMFuzzerTestOneInput_glue.v, with its module paths and module names changed; 531 of its 618 lines of code are new or changed and 916 lines of the source are left out. *)
(* The final wiring of the plain walk of LLVMFuzzerTestOneInput (fuzz/fuzz_transport.c:1124-1218): the walk
   contract (LLVMFuzzerTestOneInput_c.v LLVMFuzzerTestOneInput_walk_contract, at the frame's allocator and sink words)
   from the contracts of its callees. LLVMFuzzerTestOneInput_holds has the type of WalkAll.v
   LLVMFuzzerTestOneInput_walk, written out here so that WalkAll.v can import this file. The chain:
     the entry, 0x13664 to the first loop head, or at the early exits (0x136cc size >= 2^26, 0x13870 an empty cursor)
       through the epilogue to the return: one evt segment, crossed into SR with TSRGlue.v g_run from sr_fr of the
       entry state (the window [S - LLVM_K, S) below the entry sp S);
     the loop, _loopsr.v llvm_loop_sr, its llvm_pass_sr from the nine cases split on the op byte: 0 and 8 (_op08.v),
       1 (_op1.v) and 2 (llvm_op2_sr) at the SR level, and the evt cases 3, 4, 5, 6, 7 (_op3/_op5/_op6/_op7.v,
       llvm_op4) through _lift.v llvm_case_sr_of_evt, each at the model's op taken at the stream with index k set to 1
       (these ops read no address of the stream);
     the exit, _exit.v llvm_exit, crossed with _lift.v llvm_sr_seg;
     the end: lib_post from sr_fr (the contract's own window stk >= LLVM_K holds sr_fr's), sink_none kept because its
       words lie in the image apart from the allocator, ctx, errno and the world (sr_fr's image clause), the input bytes
       kept as an entry block, ro_agree from sr_fr, GI = True (GI.v).
   The Section hypotheses are the pieces not yet in the tree, each stated as its file states it:
     llvm_op2_sr  case 2 at the SR level: _op1.v llvm_op1_sr's shape, with the contracts of op_announce's calls
                  (memset, memcpy, strlen) besides build_and_receive's;
     llvm_op4     case 4 at the evt level: _op6.v llvm_op6's shape, the model as op_submit_m whole, with the contracts of
                  its calls (memset, memcpy, diginet_session_submit, check_refusal_submit, check_latest_submit, settle);
     llvm_entry   the entry: the ubsan image's llvm_entry_stmt shape (U/Prog/T/LLVMFuzzerTestOneInput_lh.v), with the
                  contracts of its calls; the early exits end after the epilogue (the frame's other cells are not
                  written there, so _lh.v llvm_out does not hold). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i YH02 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 AllocSlots AllocRoom MemNorm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require FrameAPI ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess
  TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memcpy_c memset_c strlen_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract GI receive_c
  build_and_receive_c TSRGlue diginet_session_config_default_c diginet_session_init_c m_wake_c
  diginet_session_wake_c check_state_wake_code_c diginet_session_close_c m_tick_c diginet_session_tick_c settle_c
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_sr LLVMFuzzerTestOneInput_lift
  LLVMFuzzerTestOneInput_loopsr LLVMFuzzerTestOneInput_op08 LLVMFuzzerTestOneInput_op1 LLVMFuzzerTestOneInput_op3
  LLVMFuzzerTestOneInput_op5 LLVMFuzzerTestOneInput_op6 LLVMFuzzerTestOneInput_op7.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- small facts *)

Lemma lp_some3 : forall (T1 T2 T3 : Type) (x x' : T1) (y y' : T2) (z z' : T3),
  Some (x, (y, z)) = Some (x', (y', z')) -> x = x' /\ y = y' /\ z = z'.
Proof. intros T1 T2 T3 x x' y y' z z' H. injection H as E1 E2 E3. auto. Qed.

Lemma lp_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

Lemma lp_fds_vm : forall vm md, m_fds (with_vmmaps vm md) = m_fds md.
Proof. intros vm md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma lp_blk_bytes : forall (B : malloc_syms) m A bs, ms_segs B = rsegs -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

(* .data.rel.ro's block of TContract.v [0x213c8, 0x21460) lies inside frame_RELRO's first block [0x213b8, 0x214e0). *)
Lemma lp_relro_of_G : forall (B : malloc_syms) mem, ms_segs B = rsegs ->
  G_img_c B LLVMFuzzerTestOneInput_c.llvm_RELRO mem -> relro_img mem.
Proof.
  intros B mem HS H i Hi. specialize (H (RELRO_BASE + i)).
  change (mbyte rsegs mem (RELRO_BASE + i) = seg_rom rsegs (Mem.wa (RELRO_BASE + i))).
  rewrite <- HS. apply H. exists 0x213b8, 296. split.
  - unfold LLVMFuzzerTestOneInput_c.llvm_RELRO, FrameAPI.frame_RELRO. left. reflexivity.
  - unfold RELRO_BASE, RELRO_LEN in *. lia.
Qed.

(* ---------------------------------------------------------------- the end points' facts *)

Section PTS.
Context (data : Z) (D : list byte).

Lemma lp_out_pt : forall m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro,
  llvm_out data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc0 fc0 None m ro) ->
  YK11.getr R 4 = tp /\ Sp < 2 ^ 63.
Proof.
  intros m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                 r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HM).
  unfold llvm_mem in HM. destruct HM as (_ & _ & _ & _ & _ & _ & HSP2 & _).
  split; [|unfold LLVM_FRAME in HSP2; lia].
  apply (f_equal (fun ms => YK11.getr (ms_regs ms) 4)) in EMS. exact EMS.
Qed.

Lemma lp_ret_qf : forall m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_ret data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  exists R pc' m, ms = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\
    YK11.getr R 4 = tp /\
    (forall regs, Regs6ss.xregs_eqv R regs -> Regs6ss.mkR_of regs = R) /\
    munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m.
Proof.
  intros m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms H.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HM).
  unfold llvm_mem in HM. destruct HM as (MU & WM & _).
  exists (mkR ra (Z_to_bv 64 (Sp + LLVM_FRAME)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6), (bv_unsigned (ret_pc ra)), m.
  rewrite MState.Z_to_bv_bv_unsigned.
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros regs Hx; apply llvm_mkR_of_eqv; exact Hx|].
  split; [exact MU | exact WM].
Qed.

Lemma lp_ret_ext : forall gp tp m0 Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro,
  (forall a, m' a = m a) ->
  llvm_ret data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc fc' None m ro) ->
  llvm_ret data D m' gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc fc' None m' ro).
Proof.
  intros gp tp m0 Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro E H.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', j10, j28.
  split; [exact (ms_mem_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' EMS)|].
  exact (llvm_mem_ext data D Sp lo Bw m0 m m' _ _ _ _ _ _ _ _ _ _ _ _ _ j10 j28 E HM).
Qed.

End PTS.

(* ---------------------------------------------------------------- the sink words *)

Section SINKW.
Context {SH : sink_head} {SK : sink_syms}.

(* sink_none (Reusable/YI14.v) reads only env_addr bytes: kept when they are. *)
Lemma lp_sink_none_kept : forall (B : malloc_syms) mem mem' md,
  (forall a, env_addr a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  sink_none B mem md -> sink_none B mem' md.
Proof. intros B mem mem' md Hfr H. exact (sink_none_frame B mem mem' md Hfr H). Qed.

End SINKW.

Section G.

(* ---------------------------------------------------------------- the pieces not yet in the tree *)

Hypothesis llvm_op2_sr : forall {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (data : Z) (D : list byte)
    (gp tp : word) (Sp lo ops : Z) (c c1 : fuzz_in) (Bw : list byte) (A : nat -> Z) (k : nat)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (cfg : config) (P : config -> Prop),
  h_binds B API -> memset_contract -> memcpy_contract -> strlen_contract ->
  (forall fx'' : YK11.FPState, @build_and_receive_contract fx'' rc B API) ->
  snd (fuzz_u8_m D c) mod 9 = 2 ->
  llvm_case_sr B API data D gp tp 2 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b
    cfg ->
  (forall a, h_addr_ok a -> exists Bres cout k1,
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, k1))) ->
  (forall a Bres cout cfg', h_addr_ok a ->
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, S k)) ->
     llvm_latch_sr B API data D gp tp Sp lo ops cout Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.

Hypothesis llvm_op4 : forall (data : Z) (D : list byte) (Sp lo ops : Z) (c c1 c2 : fuzz_in) (B B1 : list byte)
    (m0 : word -> option byte) (gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32)
    (ms : machine_state) (Q : machine_state -> Prop),
  memset_contract -> memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract ->
  check_latest_submit_contract -> settle_contract ->
  llvm_case data D m0 gp tp 4 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  op_submit_m B D c1 = Some (B1, c2) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c2 B1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.

Hypothesis llvm_entry : forall (data : Z) (D : list byte) (regs0 F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) (Bw : list byte),
  memcpy_contract -> memset_contract -> diginet_session_config_default_contract -> diginet_session_init_contract ->
  reg_get regs0 10 = Z_to_bv 64 data -> reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length D)) ->
  bv_unsigned (reg_get regs0 2) mod 16 = 0 -> stk rsegs m lo (bv_unsigned (reg_get regs0 2)) ->
  lo + LLVM_FRAME + LLVM_LOOP_K <= bv_unsigned (reg_get regs0 2) -> bv_unsigned (reg_get regs0 2) < 2 ^ 63 ->
  W_BASE_PLAIN + W_LEN <= lo ->
  (D = [] \/ (0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\
              bytes_at rsegs m data D)) ->
  mem_inv rsegs m -> relro_img m -> wmem rsegs m Bw ->
  LLVMFuzzerTestOneInput_c.llvm_model_ok Bw D ->
  evt rsegs
    (fun ms =>
       (exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
          ms = MS (mkR (reg_get regs0 1) (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - LLVM_FRAME + LLVM_FRAME))
                       (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (reg_get regs0 8) (reg_get regs0 9) (Z_to_bv 64 0)
                       a1 a2 a3 a4 a5 a6 a7 (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20)
                       (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
                       (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) t3 t4 t5 t6)
                  F (ret_pc (reg_get regs0 1)) fc None m' (seg_rom rsegs) /\
          munch (LLVM_FP (bv_unsigned (reg_get regs0 2) - LLVM_FRAME)) m m' /\ wmono rsegs m m') \/
       (exists (c : fuzz_in) (Bh : list byte),
          llvm_head data D m (reg_get regs0 3) (reg_get regs0 4) (bv_unsigned (reg_get regs0 2) - LLVM_FRAME) lo 0 c Bh
            (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
            (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
            (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) F fc ms /\
          forall As, LLVMFuzzerTestOneInput_c.llvm_heap_ok As ->
            exists Bf, LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_plain Bh As D c O = Some (Bf, tt)))
    (MS (Regs6ss.mkR_of regs0) F (Z_to_bv 64 LLVM_ENTRY_PC) fc None m (seg_rom rsegs)).

(* ---------------------------------------------------------------- the walk at one allocator *)

Section MAIN.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HB : h_binds B API.
(* the sink words: in the image, apart from the allocator, its ctx, errno and the world *)
Hypothesis SINK : forall a, env_addr a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ ~ h_world a.
Hypothesis CDEF : diginet_session_config_default_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis MSET : memset_contract.
Hypothesis STRLEN : strlen_contract.
Hypothesis SINIT : diginet_session_init_contract.
Hypothesis MWAKE : m_wake_contract.
Hypothesis SWAKE : diginet_session_wake_contract.
Hypothesis CSWC : check_state_wake_code_contract.
Hypothesis SCLOSE : diginet_session_close_contract.
Hypothesis MTICK : m_tick_contract.
Hypothesis STICK : diginet_session_tick_contract.
Hypothesis SETTLE : settle_contract.
Hypothesis BAR : forall fx' : YK11.FPState, @build_and_receive_contract fx' rc B API.
Hypothesis SUBMIT : diginet_session_submit_contract.
Hypothesis CREF : check_refusal_submit_contract.
Hypothesis CLAT : check_latest_submit_contract.
Hypothesis RECV : forall fx' : YK11.FPState, @receive_contract fx' rc B API.

Variables (j : nat) (ra empty stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (data : Z) (D : list byte) (b : sbound) (Bw0 : list byte).
Hypothesis HKS : LLVMFuzzerTestOneInput_c.LLVM_K <= stk.
Hypothesis HRA : YK0s.ret_ok (Z_to_bv 64 ra).
Hypothesis PRE : LLVMFuzzerTestOneInput_c.llvm_walk_pre B API j ra empty stk L0 A0 regs0 mem0 md0 data
  (Z.of_nat (length D)) D b Bw0.
Hypothesis ROOM : LLVMFuzzerTestOneInput_c.llvm_room b.

(* the entry sp, the frame's sp, the bottom of the window, gp, tp and the 13 saved registers *)
Local Abbreviation SS := (bv_unsigned (reg_get regs0 2)).
Local Abbreviation SP := (bv_unsigned (reg_get regs0 2) - LLVM_FRAME).
Local Abbreviation LO := (bv_unsigned (reg_get regs0 2) - LLVM_FRAME - LLVM_LOOP_K).
Local Abbreviation GP := (reg_get regs0 3).
Local Abbreviation TP := (reg_get regs0 4).
Local Abbreviation R1 := (reg_get regs0 1).
Local Abbreviation R8 := (reg_get regs0 8).
Local Abbreviation R9 := (reg_get regs0 9).
Local Abbreviation R18 := (reg_get regs0 18).
Local Abbreviation R19 := (reg_get regs0 19).
Local Abbreviation R20 := (reg_get regs0 20).
Local Abbreviation R21 := (reg_get regs0 21).
Local Abbreviation R22 := (reg_get regs0 22).
Local Abbreviation R23 := (reg_get regs0 23).
Local Abbreviation R24 := (reg_get regs0 24).
Local Abbreviation R25 := (reg_get regs0 25).
Local Abbreviation R26 := (reg_get regs0 26).
Local Abbreviation R27 := (reg_get regs0 27).

Local Abbreviation POST :=
  (LLVMFuzzerTestOneInput_c.llvm_walk_post B API j ra stk L0 A0 regs0 mem0 md0 data (Z.of_nat (length D)) b).

(* ---- the evt cases ---- *)

(* An evt case i at the model's op: from the case entry to the latch, with the op's world and cursor. *)
Definition lp_evt_case (i : Z) : Prop :=
  forall (gp tp : word) (Sp lo ops : Z) (c : fuzz_in) (Bw : list byte) (As : nat -> Z) (k : nat)
    (Bres : list byte) (cout : fuzz_in) (k1 : nat) (ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m0 : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) (Q : machine_state -> Prop),
  snd (fuzz_u8_m D c) mod 9 = i ->
  LLVMFuzzerTestOneInput_op_m timg_plain Bw As D c k = Some (Bres, (cout, k1)) ->
  llvm_case data D m0 gp tp i Sp lo ops c (fst (fuzz_u8_m D c)) Bw ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc ms ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout Bres ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.

(* the model's op at op byte b mod 9 = i, unfolded to its case *)
Ltac lp_open Hop EO HC :=
  let c1 := fresh "c1" in let opb := fresh "opb" in let EU8 := fresh "EU8" in
  match type of Hop with snd (fuzz_u8_m ?D ?c) mod 9 = _ =>
    destruct (fuzz_u8_m D c) as [c1 opb] eqn:EU8 end;
  rewrite ?EU8 in HC; cbn [fst snd] in HC;
  rewrite ?EU8 in Hop; cbn [fst snd] in Hop;
  revert EO; unfold LLVMFuzzerTestOneInput_op_m; rewrite EU8; cbv beta iota zeta; rewrite Hop;
  cbn [Z.eqb Pos.eqb].

Lemma lp_op3 : lp_evt_case 3.
Proof.
  intros gp tp Sp lo ops c Bw As k Bres cout k1 ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 F fc ms Q Hop EO HC HK.
  lp_open Hop EO HC.
  destruct (fuzz_u8_m D c1) as [c2 sb] eqn:E2. cbv beta iota zeta.
  destruct (op_begin_m Bw) as [[B1 []]|] eqn:E3; cbv beta iota zeta; [|discriminate].
  destruct (fuzz_u16_m D c2) as [c3 t] eqn:E4. cbv beta iota zeta.
  match goal with |- context [m_tick_m ?X] => destruct (m_tick_m X) as [[B3 []]|] eqn:E5 end;
    cbv beta iota zeta; [|discriminate].
  match goal with |- context [diginet_session_tick_m timg_plain None ?X ?Y] =>
    destruct (diginet_session_tick_m timg_plain None X Y) as [[B4 r]|] eqn:E6 end;
    cbv beta iota zeta; [|discriminate].
  match goal with |- context [settle_m ?X 1] => destruct (settle_m X 1) as [[B5 []]|] eqn:E7 end;
    cbv beta iota zeta; [|discriminate].
  intros EO. destruct (lp_some3 _ _ _ _ _ _ _ _ _ EO) as (E8 & E9 & E10). subst Bres cout k1.
  eapply llvm_op3; [exact MSET | exact MTICK | exact STICK | exact SETTLE | exact HC | exact E2 | exact E3 | exact E4
                   | exact E5 | exact E6 | exact E7 | exact HK].
Qed.

Lemma lp_op4 : lp_evt_case 4.
Proof.
  intros gp tp Sp lo ops c Bw As k Bres cout k1 ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 F fc ms Q Hop EO HC HK.
  lp_open Hop EO HC.
  destruct (op_submit_m Bw D c1) as [[B1 c2]|] eqn:E3; cbv beta iota zeta; [|discriminate].
  intros EO. destruct (lp_some3 _ _ _ _ _ _ _ _ _ EO) as (E8 & E9 & E10). subst Bres cout k1.
  eapply llvm_op4; [exact MSET | exact MCPY | exact SUBMIT | exact CREF | exact CLAT | exact SETTLE | exact HC
                   | exact E3 | exact HK].
Qed.

Lemma lp_op5 : lp_evt_case 5.
Proof.
  intros gp tp Sp lo ops c Bw As k Bres cout k1 ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 F fc ms Q Hop EO HC HK.
  lp_open Hop EO HC.
  destruct (op_begin_m Bw) as [[B1 []]|] eqn:E3; cbv beta iota zeta; [|discriminate].
  destruct (m_wake_m B1) as [[B2 want]|] eqn:E4; cbv beta iota zeta; [|discriminate].
  match goal with |- context [diginet_session_wake_m timg_plain None ?X ?Y] =>
    destruct (diginet_session_wake_m timg_plain None X Y) as [[B3 rcode]|] eqn:E5 end;
    cbv beta iota zeta; [|discriminate].
  match goal with |- context [check_state_wake_code_m ?X ?Y ?W] =>
    destruct (check_state_wake_code_m X Y W) as [[B4 []]|] eqn:E6 end;
    cbv beta iota zeta; [|discriminate].
  match goal with |- context [settle_m ?X 0] => destruct (settle_m X 0) as [[B5 []]|] eqn:E7 end;
    cbv beta iota zeta; [|discriminate].
  intros EO. destruct (lp_some3 _ _ _ _ _ _ _ _ _ EO) as (E8 & E9 & E10). subst Bres cout k1.
  eapply llvm_op5; [exact MSET | exact MWAKE | exact SWAKE | exact CSWC | exact SETTLE | exact HC | exact E3
                   | exact E4 | exact E5 | exact E6 | exact E7 | exact HK].
Qed.

Lemma lp_op6 : lp_evt_case 6.
Proof.
  intros gp tp Sp lo ops c Bw As k Bres cout k1 ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 F fc ms Q Hop EO HC HK.
  lp_open Hop EO HC.
  destruct (op_begin_m Bw) as [[B1 []]|] eqn:E3; cbv beta iota zeta; [|discriminate].
  destruct (m_close_m B1) as [[B2 []]|] eqn:E4; cbv beta iota zeta; [|discriminate].
  match goal with |- context [diginet_session_close_m timg_plain None ?X ?Y] =>
    destruct (diginet_session_close_m timg_plain None X Y) as [[B3 rr]|] eqn:E5 end;
    cbv beta iota zeta; [|discriminate].
  match goal with |- context [settle_m ?X 0] => destruct (settle_m X 0) as [[B4 []]|] eqn:E6 end;
    cbv beta iota zeta; [|discriminate].
  intros EO. destruct (lp_some3 _ _ _ _ _ _ _ _ _ EO) as (E8 & E9 & E10). subst Bres cout k1.
  eapply llvm_op6; [exact MSET | exact SCLOSE | exact SETTLE | exact HC | exact E3 | exact E4 | exact E5 | exact E6
                   | exact HK].
Qed.

Lemma lp_op7 : lp_evt_case 7.
Proof.
  intros gp tp Sp lo ops c Bw As k Bres cout k1 ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 F fc ms Q Hop EO HC HK.
  lp_open Hop EO HC.
  intros EO. destruct (lp_some3 _ _ _ _ _ _ _ _ _ EO) as (E8 & E9 & E10). subst Bres cout k1.
  eapply llvm_op7; [exact HC | exact HK].
Qed.

(* An evt case at the SR level: the model's op at the stream with index k set to 1 gives the case's world and
   cursor; the case is one evt segment (_lift.v llvm_case_sr_of_evt). *)
Lemma lp_evt_sr : forall (i : Z) gp tp Sp lo ops c Bw (As : nat -> Z) (k : nat)
    ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg (P : config -> Prop),
  lp_evt_case i -> snd (fuzz_u8_m D c) mod 9 = i ->
  llvm_case_sr B API data D gp tp i Sp lo ops c (fst (fuzz_u8_m D c)) Bw ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    L A mem md b' cfg ->
  (forall a, h_addr_ok a -> LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k <> None) ->
  (forall a Bres cout k1 cfg', h_addr_ok a ->
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k = Some (Bres, (cout, k1)) ->
     llvm_latch_sr B API data D gp tp Sp lo ops cout Bres ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b'
       cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros i gp tp Sp lo ops c Bw As k ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg P
    HEV Hop HC HM K.
  assert (H1 : h_addr_ok 1) by (unfold h_addr_ok; lia).
  destruct (LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k 1) D c k) as [[Bres [cout k1]]|] eqn:EO;
    [|exfalso; exact (HM 1 H1 EO)].
  eapply (llvm_case_sr_of_evt B API data D); [exact HB | exact HC | |].
  - intros m0 F fc ms Q HCASE HK.
    exact (HEV gp tp Sp lo ops c Bw (aupd As k 1) k Bres cout k1 ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 F fc ms
             Q Hop EO HCASE HK).
  - intros cfg' HL. exact (K 1 Bres cout k1 cfg' H1 EO HL).
Qed.

(* ---- one pass of the loop: the nine cases ---- *)

Lemma lp_pass : forall gp tp Sp lo ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b',
  llvm_pass_sr B API data D gp tp Sp lo ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b'.
Proof.
  intros gp tp Sp lo ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b'.
  intros ops c Bw As k cfg P HC HM K.
  pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c)) 9 ltac:(lia)) as Hop9.
  assert (HM' : forall a, h_addr_ok a -> exists Bres cout k1,
            LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k = Some (Bres, (cout, k1))).
  { intros a Ha. destruct (LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k) as [[Bres [cout k1]]|] eqn:EO;
      [exists Bres, cout, k1; reflexivity | exfalso; exact (HM a Ha EO)]. }
  assert (K' : forall a Bres cout cfg', h_addr_ok a ->
            LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k = Some (Bres, (cout, S k)) ->
            llvm_latch_sr B API data D gp tp Sp lo ops cout Bres ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              L A mem md b' cfg' ->
            SR rsegs cfg' P).
  { intros a Bres cout cfg' Ha EO HL. exact (K a Bres cout (S k) cfg' Ha EO HL). }
  assert (Hcase : snd (fuzz_u8_m D c) mod 9 = 0 \/ snd (fuzz_u8_m D c) mod 9 = 1 \/
                  snd (fuzz_u8_m D c) mod 9 = 2 \/ snd (fuzz_u8_m D c) mod 9 = 3 \/
                  snd (fuzz_u8_m D c) mod 9 = 4 \/ snd (fuzz_u8_m D c) mod 9 = 5 \/
                  snd (fuzz_u8_m D c) mod 9 = 6 \/ snd (fuzz_u8_m D c) mod 9 = 7 \/
                  snd (fuzz_u8_m D c) mod 9 = 8) by lia.
  destruct Hcase as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E in HC.
  - eapply llvm_op0_sr; [exact HB | exact RECV | exact HC | exact E | exact HM | exact K].
  - eapply llvm_op1_sr; [exact HB | exact BAR | exact E | exact HC | exact HM' | exact K'].
  - exact (llvm_op2_sr B API data D gp tp Sp lo ops c (fst (fuzz_u8_m D c)) Bw As k L A mem md b'
             ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cfg P HB MSET MCPY STRLEN BAR E HC HM' K').
  - exact (lp_evt_sr 3 gp tp Sp lo ops c Bw As k ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg P
             lp_op3 E HC HM K).
  - exact (lp_evt_sr 4 gp tp Sp lo ops c Bw As k ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg P
             lp_op4 E HC HM K).
  - exact (lp_evt_sr 5 gp tp Sp lo ops c Bw As k ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg P
             lp_op5 E HC HM K).
  - exact (lp_evt_sr 6 gp tp Sp lo ops c Bw As k ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg P
             lp_op6 E HC HM K).
  - exact (lp_evt_sr 7 gp tp Sp lo ops c Bw As k ra' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L A mem md b' cfg P
             lp_op7 E HC HM K).
  - eapply llvm_op8_sr; [exact HB | exact RECV | exact HC | exact E | exact HM | exact K].
Qed.

(* ---- facts of the entry ---- *)

Lemma lp_nums : YM05.alloc_ceiling + stk <= SS /\ SS < 2 ^ 63 /\ SS mod 16 = 0 /\ 10080 <= stk /\
  SR_RES_TOP < YM05.alloc_ceiling /\ W_BASE_PLAIN + W_LEN <= SR_RES_TOP.
Proof.
  pose proof PRE as ((_ & _ & _ & _ & _ & Hal & Hceil & H63 & _) & _).
  pose proof sr_ceiling as Hc.
  assert (HK0 : LLVMFuzzerTestOneInput_c.LLVM_K = 10080) by reflexivity.
  change (spZ regs0) with SS in *.
  unfold SR_RES_TOP, W_BASE_PLAIN, W_LEN in *. repeat split; lia.
Qed.

Lemma lp_block : D <> [] -> exists q, In (q, Z.of_nat (length D)) (user_blocks A0) /\ ptr_addr L0 q = data.
Proof.
  intros HD. pose proof PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _).
  destruct Hpl as [[Hn _] | [_ H]]; [|exact H].
  exfalso. destruct D; [exact (HD eq_refl) | cbn in Hn; lia].
Qed.

Lemma lp_data_range : D <> [] ->
  4096 <= data /\ data + Z.of_nat (length D) <= YM05.alloc_ceiling /\ off_world data (Z.of_nat (length D)).
Proof.
  intros HD. pose proof PRE as ((HM0 & _) & _).
  pose proof HB as (SEGS & _ & _ & _ & _ & AX & _).
  destruct (lp_block HD) as (q & Hq & Hqp).
  assert (HL : 0 < Z.of_nat (length D)) by (destruct D; [exact (False_ind _ (HD eq_refl)) | cbn; lia]).
  destruct (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q _ HM0 Hq) as (R1' & R2').
  rewrite Hqp in R1', R2'. split; [lia|]. split; [lia|].
  apply (wmem_off_heap B data _ SEGS HL). intros i Hi.
  pose proof (ax_blocks_img AX L0 A0 mem0 md0 q _ i HM0 Hq Hi) as Hn. rewrite Hqp in Hn. exact Hn.
Qed.

Lemma lp_HIN : D <> [] -> exists q kq, In (q, kq) (user_blocks A0) /\ ptr_addr L0 q <= data /\
  data + Z.of_nat (length D) <= ptr_addr L0 q + kq.
Proof.
  intros HD. destruct (lp_block HD) as (q & Hq & Hqp). exists q, (Z.of_nat (length D)).
  split; [exact Hq|]. lia.
Qed.

Lemma lp_FR0 : sr_fr B API LLVM_SR_K (LLVM_SR_S SP) L0 A0 mem0 md0 L0 A0 mem0 md0.
Proof.
  pose proof PRE as ((HM0 & HW0 & HB0 & HID0 & _ & _ & _ & _ & Hstw0 & _ & Herr0 & _) & _ & _ & _ & _ & _ & Hro0 & _).
  pose proof lp_nums as (N1 & _ & _ & N4 & _).
  apply (sr_fr_refl B API); [exact HM0 | exact HW0 | exact HB0 | exact HID0 | | exact Herr0 | exact Hro0].
  intros a Ha. apply Hstw0. change (spZ regs0) with SS.
  unfold LLVM_SR_S, LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME in *. lia.
Qed.

(* ---- the end ---- *)

Lemma lp_post : forall (fx' : YK11.FPState) regs mem md L A,
  sr_fr B API LLVM_SR_K (LLVM_SR_S SP) L0 A0 mem0 md0 L A mem md ->
  frm_zero (@fp_csr fx') -> res_ok_slots A b ->
  YK11.getr regs 10 = Z_to_bv 64 0 -> regs_preserved regs0 regs ->
  POST (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 ra) mem (YK11.seg_rom (ms_segs B))) md).
Proof.
  intros fx' regs mem md L A
    (HM & HW & HB' & HID & (vm & Hmd) & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen)
    FZ RES Ha0 Hrp.
  pose proof PRE as ((HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0 &
    Hpl0 & Hrod0) & _ & _ & Hsn & _).
  pose proof HB as (SEGS & _ & _ & _ & _ & _ & ERRNO_LOW & CTX_LOW & _).
  pose proof lp_nums as (N1 & N2 & N3 & N4 & N5 & N6).
  change (spZ regs0) with SS in *.
  assert (ES : LLVM_SR_S SP = SS) by (unfold LLVM_SR_S; lia).
  rewrite ES in Hhigh, Hstw.
  unfold LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME in Hhigh, Hstw.
  exists fx', L, A, regs, mem, md.
  split; [reflexivity|]. split; [exact FZ|].
  split.
  { split; [exact HM|]. split; [exact HW|]. split; [exact HB'|]. split; [exact HID|].
    split; [exact Ha0|]. split; [exact Hrp|]. split; [exists vm; exact Hmd|].
    split.
    { intros q k Hq. destruct (Hub q k Hq) as [Hq1 Hq2]. exists q. split; [exact Hq1 | exact Hq2]. }
    split.
    { intros a Ha Hns. apply Hhigh; [exact Ha | | | ].
      - intros Hs. apply Hns. left. change (spZ regs0) with SS. lia.
      - intros Hs. apply Hns. right. exact Hs.
      - intros Hc. lia. }
    split.
    { intros a T1 T2 T3 T4 T5. apply Himg; [exact T1 | exact T2 | exact T3 | exact T4 |].
      intros Hw. apply T5. apply (proj2 (frame_G_world a)). exact Hw. }
    split.
    { intros q k i Hq _ Hi. assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      exact (Hbyt _ k i Hb Hi). }
    intros a [Hs|Hs]; [|exact (Herr a Hs)].
    change (spZ regs0) with SS in Hs.
    destruct (Z_lt_le_dec a (SS - (224 + 9856))) as [Hlt|Hge].
    - destruct (Hhigh a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hw]. apply Hw. apply Hstw0. lia.
    - apply Hstw. lia. }
  split.
  { assert (Hs1 : sink_none B mem md0).
    { apply (lp_sink_none_kept B mem0 mem md0); [|exact Hsn].
      intros a Ha. destruct (SINK a Ha) as (T1 & T2 & T3 & T4 & T5). exact (proj1 (Himg a T1 T2 T3 T4 T5)). }
    rewrite Hmd. destruct Hs1 as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite lp_fds_vm. exact H3. }
  split; [exact RES|].
  split.
  { intros i Hi. destruct Hpl0 as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
    assert (Hb : In (data, Z.of_nat (length D)) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
    exact (Hbyt data _ i Hb Hi). }
  split; [exact MI | exact I].
Qed.

(* the return pc: ra, a return address the contract gives *)
Lemma lp_ret_pc : MState.ret_pc R1 = Z_to_bv 64 ra.
Proof.
  pose proof PRE as ((_ & _ & _ & _ & Hra0 & _) & _).
  change R1 with (YK11.getr regs0 1). rewrite Hra0. exact (sr_ret_pc _ HRA).
Qed.

(* the register file at the return, as both exits leave it: a0 = 0 and the callee-saved registers of the entry *)
Lemma lp_ret_regs : forall regs t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  Regs6ss.xregs_eqv (mkR R1 (Z_to_bv 64 (SP + LLVM_FRAME)) GP TP t0 t1 t2 R8 R9 (Z_to_bv 64 0)
                       a1 a2 a3 a4 a5 a6 a7 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 t3 t4 t5 t6) regs ->
  YK11.getr regs 10 = Z_to_bv 64 0 /\ regs_preserved regs0 regs.
Proof.
  intros regs t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hx.
  split; [rewrite (sr_getr_eqv _ _ _ Hx); reflexivity|].
  intros r Hr. rewrite (sr_getr_eqv _ _ _ Hx).
  destruct (lp_callee_cases r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    try reflexivity.
  transitivity (Z_to_bv 64 SS).
  - transitivity (Z_to_bv 64 (SP + LLVM_FRAME)); [reflexivity | f_equal; lia].
  - apply MState.Z_to_bv_bv_unsigned.
Qed.

(* ---- the exit: the epilogue, then the post ---- *)

Lemma lp_exit : forall Bf cfg,
  llvm_out_sr B API data D GP TP SP LO Bf R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 L0 A0 mem0 md0 b cfg ->
  SR rsegs cfg POST.
Proof.
  intros Bf cfg HO.
  pose proof HB as (SEGS & _).
  apply (llvm_sr_seg B API data D
           (fun m0 F fc => llvm_out data D m0 GP TP SP LO Bf R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 F fc)
           (fun m0 F fc => llvm_ret data D m0 GP TP SP LO Bf R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 F fc)
           TP LLVM_OUT_PC SP LO L0 A0 mem0 md0 b cfg POST HB HO).
  - intros m0 F fc R pc0 fc0 m ro H. cbv beta in H. eapply lp_out_pt. exact H.
  - intros m0 F fc ms H. cbv beta in H. eapply llvm_exit; [exact H|].
    intros ms' H'. apply evt_done. exact H'.
  - intros m0 F fc ms H. cbv beta in H. eapply lp_ret_qf. exact H.
  - intros m0 F fc R pc0 fc0 m m' ro E H. cbv beta in H |- *. eapply lp_ret_ext; [exact E | exact H].
  - intros pc' cfg' H.
    destruct H as (fx' & regs & mem & md & L & A & -> & Hfrm & FR & Hc1 & Hc2 & Hres & Hroom & Htp & HIN & HPe).
    cbv beta in HPe.
    destruct HPe as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HM).
    assert (EPC : Z_to_bv 64 pc' = MState.ret_pc R1) by exact (f_equal ms_pc_val EMS).
    assert (ER : Regs6ss.mkR_of regs =
                 mkR R1 (Z_to_bv 64 (SP + LLVM_FRAME)) GP TP t0 t1 t2 R8 R9 (Z_to_bv 64 0)
                   a1 a2 a3 a4 a5 a6 a7 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 t3 t4 t5 t6)
      by exact (f_equal ms_regs EMS).
    assert (Hx : Regs6ss.xregs_eqv
                   (mkR R1 (Z_to_bv 64 (SP + LLVM_FRAME)) GP TP t0 t1 t2 R8 R9 (Z_to_bv 64 0)
                      a1 a2 a3 a4 a5 a6 a7 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 t3 t4 t5 t6) regs).
    { rewrite <- ER. exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv regs)). }
    apply SR_ret. rewrite EPC, lp_ret_pc, <- SEGS.
    destruct (lp_ret_regs regs t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hx) as [G10 RP].
    exact (lp_post fx' regs mem md L A FR Hfrm Hres G10 RP).
Qed.

(* ---- the whole walk ---- *)

Lemma lp_walk :
  SR (ms_segs B) (mkCfg (YK11.mkst regs0 (Z_to_bv 64 LLVMFuzzerTestOneInput_c.LLVM_ENTRY) mem0
                           (YK11.seg_rom (ms_segs B))) md0)
    POST.
Proof.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  pose proof PRE as ((HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0 &
    Hpl0 & Hrod0) & _ & HBD & Hsn0 & H47 & Hres0 & Hro0 & HG0 & HGI0 & Hfz0 & HWM0 & HMO).
  pose proof lp_nums as (N1 & N2 & N3 & N4 & N5 & N6).
  change (spZ regs0) with SS in *.
  rewrite SEGS.
  change (Z_to_bv 64 LLVMFuzzerTestOneInput_c.LLVM_ENTRY) with (Z_to_bv 64 LLVM_ENTRY_PC).
  assert (HSmax : LLVM_SR_S SP <= 2 ^ 64) by (unfold LLVM_SR_S; lia).
  assert (Hc1 : YM05.alloc_ceiling + LLVM_SR_K <= LLVM_SR_S SP)
    by (unfold LLVM_SR_S, LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME in *; lia).
  assert (Hc2 : YM05.alloc_ceiling <= LO) by (unfold LLVM_LOOP_K, LLVM_FRAME in *; lia).
  eapply (g_run B API SEGS AX HGG WORLD LLVM_SR_K (LLVM_SR_S SP) L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY_PC)
            mem0 md0 L0 A0 _ _ lp_FR0 Hc1 HSmax).
  - (* the entry *)
    apply (llvm_entry data D regs0 (@fp_regs fx) (@fp_csr fx) (normalize rsegs mem0) LO Bw0 MCPY MSET CDEF SINIT).
    + exact Hp0.
    + exact Hn0.
    + exact Hal0.
    + apply (norm_stk B); [exact SEGS | exact Hro0 | unfold LLVM_LOOP_K, LLVM_FRAME in *; lia | lia |].
      intros a Ha. apply Hstw0. unfold LLVM_LOOP_K, LLVM_FRAME in *. lia.
    + lia.
    + exact H630.
    + unfold LLVM_LOOP_K, LLVM_FRAME in *. lia.
    + destruct (Nat.eq_dec (length D) 0) as [E0|E0]; [left; apply length_zero_iff_nil; exact E0|].
      assert (HDn : D <> []) by (intros E; rewrite E in E0; exact (E0 eq_refl)).
      right. destruct (lp_data_range HDn) as (R1' & R2' & R3'). split; [lia|]. split; [lia|]. split; [exact R3'|].
      apply (bytes_at_normalize rsegs mem0 data D Hro0).
      apply (lp_blk_bytes B); [exact SEGS | lia | lia | exact HBD].
    + apply mem_inv_normalize.
    + exact (sr_relro_norm mem0 Hro0 (lp_relro_of_G B mem0 SEGS HG0)).
    + exact (sr_wmem_norm mem0 Bw0 Hro0 HWM0).
    + exact HMO.
  - (* the end states' form and footprint *)
    intros ms [HX | (c & Bh & HH & _)].
    + destruct HX as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM).
      do 5 eexists. exists (LLVM_FP SP). split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x _ NO. destruct (op08_fp SP x NO) as [Hw|Hw]; [left; exact Hw | right; left; exact Hw].
    + apply llvm_head_qf in HH as (R & pc' & m' & -> & _ & _ & MU & WM).
      do 5 eexists. exists (LLVM_FP SP). split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x _ NO. destruct (op08_fp SP x NO) as [Hw|Hw]; [left; exact Hw | right; left; exact Hw].
  - (* the continuations: the early exit's return, or the loop *)
    intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
    destruct HQ as [HX | (c & Bh & HH & HI)].
    + destruct HX as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & EQ & _ & _).
      unfold MS in EQ. injection EQ as ER EF EP EC EM. subst R F pc' fc.
      apply SR_ret. rewrite lp_ret_pc, <- SEGS.
      destruct (lp_ret_regs regs' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hx) as [G10 RP].
      exact (lp_post (mkFP (@fp_regs fx) (@fp_csr fx)) regs' m' md0 L0 A0 FR' Hfz0 Hres0 G10 RP).
    + pose proof HH as HH0. apply llvm_head_qf in HH0 as (R2 & pc2 & m2 & EQ & Etp2 & HmkR & _ & _).
      unfold MS in EQ. injection EQ; intros; subst R2 F pc' fc m2.
      pose proof HH as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                        t3 & t4 & t5 & t6 & mm & j10 & j28 & _ & _ & HN & HC & _).
      assert (HDn : D <> []) by (intros E; rewrite E in HC; unfold llvm_cursor in HC; cbn [length] in HC; lia).
      assert (EPC2 : Z_to_bv 64 pc2 = Z_to_bv 64 LLVM_HEAD_PC) by (eapply llvm_head_pc; exact HH).
      assert (HHSR : llvm_head_sr B API data D GP TP SP LO 0 c Bh R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
                       L0 A0 mem0 md0 b
                       (mkCfg (@YK11.mkst (mkFP (@fp_regs fx) (@fp_csr fx)) regs' (Z_to_bv 64 pc2) m'
                                 (YK11.seg_rom rsegs)) md0)).
      { unfold llvm_head_sr, llvm_sr_at. rewrite EPC2. rewrite EPC2 in HH.
        exists (mkFP (@fp_regs fx) (@fp_csr fx)), regs', m', md0, L0, A0.
        split; [reflexivity|]. split; [exact Hfz0|]. split; [exact FR'|]. split; [exact Hc1|].
        split; [exact Hc2|]. split; [exact Hres0|]. split; [exact ROOM|].
        split; [rewrite (sr_getr_eqv _ _ _ Hx), Etp2; exact Htp0|].
        split; [exact (lp_HIN HDn)|].
        cbn [fp_regs fp_csr]. rewrite (HmkR regs' Hx).
        eapply llvm_head_ext; [|exact HH]. intros x. symmetry. exact (proj1 Hrel x). }
      apply (llvm_loop_sr B API data D (Z.to_nat (OPS_MAX - 0)) GP TP SP LO 0 c O Bh
               R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 L0 A0 mem0 md0 b _ POST HB
               (lp_pass GP TP SP LO R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 L0 A0 mem0 md0 b) HHSR eq_refl).
      * intros As HAs. rewrite Z.sub_0_r. exact (HI As HAs).
      * intros Bf cfg'' _ HOUT. exact (lp_exit Bf cfg'' HOUT).
Qed.

End MAIN.

(* ---------------------------------------------------------------- the frame's allocator and sink words *)

Lemma lp_sink_src0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState) a,
  @env_addr src0_sink_head src0_sink a ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\ ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4) /\ ~ h_world a.
Proof.
  intros rc fx a Ha.
  assert (SL : sink_laws src0_msyms) by exact _.
  destruct SL as [SLE _]. destruct (SLE a Ha) as (T1 & T2 & T3 & T4).
  split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
  unfold env_addr in Ha. unfold h_world, W_BASE_PLAIN, W_LEN.
  cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_file sk_highs_addr sk_ones_addr src0_sink src0_sink_head
       YH03.src0_D_ofl_head YH03.src0_D_ofl_lock YH03.src0_D_libc YH03.src0_D_const_HIGHS_0x8080808080808080
       YH03.src0_D_const_ONES_0x0101010101010100] in Ha.
  lia.
Qed.

(* WalkAll.v LLVMFuzzerTestOneInput_walk, written out. *)
Theorem LLVMFuzzerTestOneInput_holds :
  forall (rc : RunCeil) (fx : FPState),
  diginet_session_config_default_contract -> memcpy_contract -> memset_contract -> strlen_contract ->
  diginet_session_init_contract -> m_wake_contract -> diginet_session_wake_contract ->
  check_state_wake_code_contract -> diginet_session_close_contract -> m_tick_contract ->
  diginet_session_tick_contract -> settle_contract ->
  (forall fx' : FPState, build_and_receive_contract (fx:=fx') (rc:=rc) src0_msyms (@ZAllocator.zlib_API rc)) ->
  diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract ->
  (forall fx' : FPState, receive_contract (fx:=fx') (rc:=rc) src0_msyms (@ZAllocator.zlib_API rc)) ->
  LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=src0_sink_head)
    (SK:=src0_sink) src0_msyms (@ZAllocator.zlib_API rc).
Proof.
  intros rc fx CDEF MCPY MSET STRLEN SINIT MWAKE SWAKE CSWC SCLOSE MTICK STICK SETTLE BAR SUBMIT CREF CLAT RECV.
  intros HB j Hj ra empty stk Hk Hra L A regs mem md p n pl b Bw PRE ROOM.
  pose proof PRE as (_ & Hn & _). subst n.
  exact (lp_walk src0_msyms (@ZAllocator.zlib_API rc) HB (lp_sink_src0 rc fx) CDEF MCPY MSET STRLEN SINIT MWAKE SWAKE
           CSWC SCLOSE MTICK STICK SETTLE BAR SUBMIT CREF CLAT RECV j ra empty stk L A regs mem md p pl b Bw Hk Hra PRE
           ROOM).
Qed.

End G.

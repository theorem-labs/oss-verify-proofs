(* The op loop of LLVMFuzzerTestOneInput at the SR level, plain image. The cases that call receive or
   build_and_receive (ops 0, 1, 2, 8) cannot be evt runs: those two callees are SR contracts (receive_c.v,
   build_and_receive_c.v), and an SR call ends an evt segment (TSRGlue.v g_run). So the loop's program points are
   also stated as SR configs: llvm_sr_at wraps an evt predicate of LLVMFuzzerTestOneInput_lh.v (over the
   normalized memory, as TSRGlue.v g_run runs evt segments) with the allocator state and the frame relation sr_fr
   of the walk.

   The walk's window. LLVMFuzzerTestOneInput's own frame is [Sp, Sp + LLVM_FRAME) (addi sp, sp, -0xe0 at 0x13664),
   and its deepest callee window lies below Sp: build_and_receive's 9856 bytes (LLVM_LOOP_K). sr_fr is taken with
   S = Sp + LLVM_FRAME (the walk's entry sp) and stk = LLVM_SR_K = LLVM_FRAME + LLVM_LOOP_K, which is
   LLVMFuzzerTestOneInput_c.v LLVM_K (224 + build_and_receive_FRAME = 10080). The footprint of the loop's evt
   segments, that window and the world, is _lh.v's LLVM_FP. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 AllocSlots AllocRoom MemNorm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame MState Regs6ss Exec Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TNeed TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c TSRGlue
  build_and_receive_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The walk's window below its entry sp (LLVMFuzzerTestOneInput_c.v LLVM_K). *)
Definition LLVM_SR_K : Z := LLVM_FRAME + LLVM_LOOP_K.

Example LLVM_SR_K_is_LLVM_K : LLVM_SR_K = LLVMFuzzerTestOneInput_c.LLVM_K.
Proof. reflexivity. Qed.

(* The walk's entry sp, the top of its window. *)
Definition LLVM_SR_S (Sp : Z) : Z := Sp + LLVM_FRAME.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context (data : Z) (D : list byte).

(* A program point pc of the loop as an SR config, from the walk's entry state (L0, A0, mem0, md0) with the
   budget b: the FP state free (frm_zero, as h_pre asks of every callee), sr_fr over the walk's window, the
   ceiling below it and below the stack bottom lo (the bytes of [lo, Sp) are then never the allocator's, so an SR
   call keeps the stack outside its window), the budget (res_ok_slots, and LLVMFuzzerTestOneInput_c.v llvm_room,
   which gives room_slots for every receive), tp, the input buffer inside a user block of the entry state
   (receive's and build_and_receive's h_src), and the evt predicate Pe of the point on the normalized memory.
   An evt segment starts at every SR point, so Pe's reference memory (llvm_mem's m0, the start of LLVM_FP's
   munch) is that same normalized memory. *)
Definition llvm_sr_at (Pe : (word -> option byte) -> bvmap 5 word -> bv 32 -> machine_state -> Prop)
    (pc Sp lo : Z)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound) (cfg : config) : Prop :=
  exists (fx' : YK11.FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (L : layout)
         (A : astate),
    cfg = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (YK11.seg_rom rsegs)) md /\
    frm_zero (@fp_csr fx') /\
    sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md /\
    YM05.alloc_ceiling + LLVM_SR_K <= LLVM_SR_S Sp /\ YM05.alloc_ceiling <= lo /\
    res_ok_slots A b /\ LLVMFuzzerTestOneInput_c.llvm_room b /\
    YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) /\
    (exists q kq, In (q, kq) (user_blocks A0) /\ ptr_addr L0 q <= data /\
       data + Z.of_nat (length D) <= ptr_addr L0 q + kq) /\
    Pe (normalize rsegs mem) (@fp_regs fx') (@fp_csr fx')
       (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None
                  (normalize rsegs mem) (seg_rom rsegs)).

Definition llvm_head_sr (gp tp : word) (Sp lo ops : Z) (c : fuzz_in) (Bw : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound) (cfg : config) : Prop :=
  llvm_sr_at (fun m0 F fc => llvm_head data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    LLVM_HEAD_PC Sp lo L0 A0 mem0 md0 b cfg.

Definition llvm_case_sr (gp tp : word) (i Sp lo ops : Z) (c c1 : fuzz_in) (Bw : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound) (cfg : config) : Prop :=
  llvm_sr_at (fun m0 F fc => llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (LLVM_CASE i) Sp lo L0 A0 mem0 md0 b cfg.

Definition llvm_latch_sr (gp tp : word) (Sp lo ops : Z) (c : fuzz_in) (Bw : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound) (cfg : config) : Prop :=
  llvm_sr_at (fun m0 F fc => llvm_latch data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    LLVM_LATCH_PC Sp lo L0 A0 mem0 md0 b cfg.

Definition llvm_out_sr (gp tp : word) (Sp lo : Z) (Bw : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound) (cfg : config) : Prop :=
  llvm_sr_at (fun m0 F fc => llvm_out data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    LLVM_OUT_PC Sp lo L0 A0 mem0 md0 b cfg.

(* ---- an evt predicate restarted over any memory equal to its own at every address ----
   g_run's continuation names the memory m' of the next SR config by mem_rel m' m0', m0' the evt segment's last
   memory: normalize m' and m0' agree at every address, so these lemmas re-establish the evt predicate of a
   program point over normalize m', as the reference memory of the segment that starts there. *)

Lemma ms_mem_of : forall R F pc fc rv m ro R' F' pc' fc' rv' m0 ro',
  MState.MS R F pc fc rv m ro = MState.MS R' F' pc' fc' rv' m0 ro' -> m = m0.
Proof. intros R F pc fc rv m ro R' F' pc' fc' rv' m0 ro' H. unfold MState.MS in H. inversion H. reflexivity. Qed.

Lemma ms_mem_swap : forall R F pc fc rv m ro R' F' pc' fc' rv' m0 ro' m',
  MState.MS R F pc fc rv m ro = MState.MS R' F' pc' fc' rv' m0 ro' ->
  MState.MS R F pc fc rv m' ro = MState.MS R' F' pc' fc' rv' m' ro'.
Proof.
  intros R F pc fc rv m ro R' F' pc' fc' rv' m0 ro' m' H. unfold MState.MS in *. inversion H. reflexivity.
Qed.

Lemma llvm_mem_ext : forall Sp lo Bw m0 m m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28,
  (forall a, m' a = m a) ->
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_mem data D Sp lo Bw m' m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.
Proof.
  intros Sp lo Bw m0 m m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 E HM.
  assert (MU0 : Frame.munch [] m m') by (intros x _; apply E).
  assert (WMO : Frame.wmono rsegs m m') by (intros x Hx; unfold wview in *; rewrite E; exact Hx).
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM
                   & HFN & HJ1 & HJ2 & HRW).
  assert (HM2 : llvm_mem data D Sp lo Bw m0 m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { apply (llvm_mem_after_call data D Sp lo 0 Bw Bw m0 m m');
      [exact HM | unfold LLVM_LOOP_K; lia | | exact WMO | | | | exact HFN].
    - intros x _. apply E.
    - intros a v Ha. rewrite E in Ha. exact (HMI a v Ha).
    - exact (Frame.stk_transport_disjoint rsegs [] m m' lo Sp HSTK MU0 WMO I).
    - exact (Frame.rw_cells_transport rsegs [] m m' _ _ HWM MU0 WMO I). }
  unfold llvm_mem in HM2 |- *. destruct HM2 as (_ & _ & REST).
  split; [apply Frame.munch_refl|]. split; [apply Frame.wmono_refl|]. exact REST.
Qed.

Lemma llvm_head_ext : forall gp tp m0 Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro,
  (forall a, m' a = m a) ->
  llvm_head data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m ro) ->
  llvm_head data D m' gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m' ro).
Proof.
  intros gp tp m0 Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro E H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HOPS & HN & HC & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  exists rr, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, r8, r19, r22, t3, t4, t5, t6, m', j10, j28.
  split; [exact (ms_mem_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' EMS)|].
  split; [exact HOPS|]. split; [exact HN|]. split; [exact HC|].
  exact (llvm_mem_ext Sp lo Bw m0 m m' _ _ _ _ _ _ _ _ _ _ _ _ _ j10 j28 E HM).
Qed.

Lemma llvm_case_ext : forall gp tp m0 i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro,
  (forall a, m' a = m a) ->
  llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m ro) ->
  llvm_case data D m' gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m' ro).
Proof.
  intros gp tp m0 i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro E H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HOPS & HN & HC & HC1 & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  exists rr, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, r8, t3, t4, t5, t6, m', j10, j28.
  split; [exact (ms_mem_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' EMS)|].
  split; [exact HOPS|]. split; [exact HN|]. split; [exact HC|]. split; [exact HC1|].
  exact (llvm_mem_ext Sp lo Bw m0 m m' _ _ _ _ _ _ _ _ _ _ _ _ _ j10 j28 E HM).
Qed.

Lemma llvm_latch_ext : forall gp tp m0 Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro,
  (forall a, m' a = m a) ->
  llvm_latch data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m ro) ->
  llvm_latch data D m' gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m' ro).
Proof.
  intros gp tp m0 Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro E H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r20 & r23 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HOPS & HC & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  exists rr, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, r8, r20, r23, t3, t4, t5, t6, m', j10, j28.
  split; [exact (ms_mem_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' EMS)|].
  split; [exact HOPS|]. split; [exact HC|].
  exact (llvm_mem_ext Sp lo Bw m0 m m' _ _ _ _ _ _ _ _ _ _ _ _ _ j10 j28 E HM).
Qed.

Lemma llvm_out_ext : forall gp tp m0 Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro,
  (forall a, m' a = m a) ->
  llvm_out data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m ro) ->
  llvm_out data D m' gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MState.MS R F pc fc' None m' ro).
Proof.
  intros gp tp m0 Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc fc' m m' ro E H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                  r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  exists rr, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, r8, r9, r18, r19, r20, r21, r22, r23, r24, r25,
    r26, r27, t3, t4, t5, t6, m', j10, j28.
  split; [exact (ms_mem_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' EMS)|].
  exact (llvm_mem_ext Sp lo Bw m0 m m' _ _ _ _ _ _ _ _ _ _ _ _ _ j10 j28 E HM).
Qed.

(* g_run's continuation names the next SR config's registers regs' by xregs_eqv R regs', R the evt segment's last
   register file; when R is a mkR form (as every evt predicate of the loop states it), the predicate's
   register file mkR_of regs' is that same form. *)
Lemma llvm_mkR_of_eqv : forall (regs : bvmap 5 word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
     x30 x31 : word),
  Regs6ss.xregs_eqv (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       x24 x25 x26 x27 x28 x29 x30 x31) regs ->
  Regs6ss.mkR_of regs = Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
                          x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
  intros regs x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 H.
  unfold Regs6ss.mkR_of.
  repeat match goal with |- context [?get regs ?r] => rewrite <- (H r eq_refl) end.
  reflexivity.
Qed.

(* ---- the loop's memory invariant across an SR call ---- *)

(* Above SR_RES_TOP (every byte of the stack, which lies above the ceiling) no address is read-only, so the
   normalized memory is the memory there. *)
Lemma sr_ro_hi : forall a, SR_RES_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold SR_RES_TOP in Ha; lia).
  unfold Mem.ro_addr. rewrite (MState.unsigned_lit a Ha').
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (sr_find_top a 1 seg E). lia.
Qed.

Lemma norm_mbyte : forall mem a, ro_agree rsegs mem -> mbyte rsegs (normalize rsegs mem) a = mbyte rsegs mem a.
Proof. intros mem a H. symmetry. exact (mbyte_rel rsegs mem (normalize rsegs mem) a (mem_rel_normalize rsegs mem H)). Qed.

Lemma norm_writable_hi : forall mem a, SR_RES_TOP <= a < 2 ^ 64 ->
  (writable_at rsegs (normalize rsegs mem) a <-> writable_at rsegs mem a).
Proof. intros mem a Ha. unfold writable_at, wview, normalize. cbv beta. rewrite (sr_ro_hi a Ha). reflexivity. Qed.

(* llvm_mem after an SR call whose window is [Sp - K, Sp): the call keeps the stack below its window and the loop's
   frame (mbyte and writability), leaves its window writable, keeps the input, and gives the world Bw'. A new
   evt segment starts after the call, from the memory the call returns. *)
Lemma llvm_mem_sr_call : forall Sp lo K Bw Bw' m0 mem mem' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28,
  llvm_mem data D Sp lo Bw m0 (normalize rsegs mem) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  ro_agree rsegs mem -> ro_agree rsegs mem' ->
  YM05.alloc_ceiling <= lo -> 0 <= K <= LLVM_LOOP_K ->
  (forall a, (lo <= a < Sp - K) \/ (Sp <= a < Sp + LLVM_FRAME) ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)) ->
  (forall a, Sp - K <= a < Sp -> writable_at rsegs mem' a) ->
  (forall i, 0 <= i < Z.of_nat (length D) -> mbyte rsegs mem' (data + i) = mbyte rsegs mem (data + i)) ->
  wmem rsegs mem' Bw' -> g_fail_next Bw' <= 1 -> relro_img mem' ->
  llvm_mem data D Sp lo Bw' (normalize rsegs mem') (normalize rsegs mem')
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28.
Proof.
  intros Sp lo K Bw Bw' m0 mem mem' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
    HM Hro Hro' Hlo HK Hkeep Hwin Hdat HWM' HFN' HRO'.
  pose proof sr_ceiling as Hc.
  unfold llvm_mem in HM |- *.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2
                  & HRW).
  split; [apply Frame.munch_refl|]. split; [apply Frame.wmono_refl|].
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  split.
  { destruct HD as (D0 & D1 & D2). split; [exact D0|]. split; [exact D1|]. intros i Hi.
    rewrite <- (D2 i Hi).
    change (mbyte rsegs (normalize rsegs mem') (data + Z.of_nat i) =
            mbyte rsegs (normalize rsegs mem) (data + Z.of_nat i)).
    rewrite !norm_mbyte by assumption. apply Hdat. lia. }
  split; [exact HSP|].
  split.
  { destruct HSTK as (T0 & T1 & T2). split; [exact T0|]. split; [exact T1|]. intros a Ha.
    assert (Hhi : SR_RES_TOP <= a < 2 ^ 64) by lia.
    destruct (Z_lt_le_dec a (Sp - K)) as [Hb|Hb].
    - destruct (Hkeep a (or_introl (conj (proj1 Ha) Hb))) as [Eb Ew].
      destruct (T2 a Ha) as [W1 (v & R1)].
      split.
      + apply (proj2 (norm_writable_hi mem' a Hhi)). apply Ew. apply (proj1 (norm_writable_hi mem a Hhi)). exact W1.
      + exists v. change (mbyte rsegs (normalize rsegs mem') a = Some v).
        rewrite norm_mbyte by exact Hro'. rewrite Eb. rewrite <- (norm_mbyte mem a Hro). exact R1.
    - assert (W : writable_at rsegs mem' a) by (apply Hwin; lia).
      split.
      + exact (proj2 (norm_writable_hi mem' a Hhi) W).
      + unfold writable_at in W. rewrite (sr_wview_hi mem' a Hhi) in W.
        destruct (mem' (Z_to_bv 64 a)) as [v|] eqn:Ev; [|contradiction].
        exists v. change (mbyte rsegs (normalize rsegs mem') a = Some v).
        rewrite norm_mbyte by exact Hro'. unfold mbyte. rewrite Ev. reflexivity. }
  split; [exact HLO|]. split; [exact HSP2|]. split; [exact HWOS|]. split; [exact HOWS|].
  split; [exact HOW|]. split; [exact HOWIN|].
  split; [apply mem_inv_normalize|].
  split; [exact (sr_relro_norm mem' Hro' HRO')|].
  split; [exact (sr_wmem_norm mem' Bw' Hro' HWM')|].
  split; [exact HFN'|]. split; [exact HJ1|]. split; [exact HJ2|].
  apply (sr_rw_cells_frame _ _ Sp _ HRW).
  intros a Ha. unfold llvm_frame_consts, llvm_saved in Ha. cbn [Cells.cells_size Cells.csize app] in Ha.
  assert (Hhi : SR_RES_TOP <= a < 2 ^ 64) by lia.
  assert (Hin : lo <= a < Sp - K \/ Sp <= a < Sp + 224) by lia.
  destruct (Hkeep a Hin) as [Eb Ew].
  rewrite !norm_mbyte by assumption. split; [exact Eb|].
  rewrite (norm_writable_hi mem a Hhi), (norm_writable_hi mem' a Hhi). exact Ew.
Qed.

(* ---- the arguments a caller in the loop gives an SR callee ---- *)

(* bytes the loop sees in the normalized memory are the block's bytes in the memory *)
Lemma llvm_blk_norm : forall mem p bs, ms_segs B = rsegs -> ro_agree rsegs mem ->
  Mem.bytes_at rsegs (normalize rsegs mem) p bs -> blk_data B mem p bs.
Proof.
  intros mem p bs SEGS Hro (H0 & H1 & H2). unfold blk_data. intros i Hi.
  pose proof (H2 (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  rewrite SEGS, <- (norm_mbyte mem (p + i) Hro). exact E.
Qed.

(* A 6-byte MAC in the image's read-only data, checked by computation: every byte read-only and equal to the
   image's. *)
Definition mac_rom_ok (p : Z) (mac : list byte) : bool :=
  forallb (fun i : nat =>
    Mem.ro_addr rsegs (Z_to_bv 64 (p + Z.of_nat i)) &&
    match seg_rom rsegs (Z_to_bv 64 (p + Z.of_nat i)), nth_error mac i with
    | Some x, Some y => Z.eqb (bv_unsigned x) (bv_unsigned y)
    | _, _ => false
    end) (seq 0 6).

Lemma llvm_mac_img : forall mem p mac, ms_segs B = rsegs -> ro_agree rsegs mem -> length mac = 6%nat ->
  mac_rom_ok p mac = true -> h_mac_at B mem p mac.
Proof.
  intros mem p mac SEGS Hro Hl Hok.
  assert (H : forall i, (i < 6)%nat -> Mem.ro_addr rsegs (Z_to_bv 64 (p + Z.of_nat i)) = true /\
             seg_rom rsegs (Z_to_bv 64 (p + Z.of_nat i)) = nth_error mac i).
  { intros i Hi. unfold mac_rom_ok in Hok. rewrite forallb_forall in Hok.
    specialize (Hok i ltac:(apply in_seq; lia)). apply andb_true_iff in Hok as [H1 H2]. split; [exact H1|].
    destruct (seg_rom rsegs _) as [x|]; destruct (nth_error mac i) as [y|]; try discriminate H2.
    apply Z.eqb_eq in H2. f_equal. apply bv_eq. exact H2. }
  split; [exact Hl|]. split.
  - unfold blk_data. intros i Hi. rewrite Hl in Hi.
    destruct (H (Z.to_nat i) ltac:(lia)) as [R1 R2]. rewrite Z2Nat.id in R1, R2 by lia.
    rewrite SEGS, <- R2. exact (Hro _ R1).
  - intros i Hi. destruct (H (Z.to_nat i) ltac:(lia)) as [R1 _]. rewrite Z2Nat.id in R1 by lia. exact R1.
Qed.

(* a span of the input buffer, as h_src asks it: inside the entry's user block of the input, which sr_fr keeps *)
Lemma llvm_src_data : forall stk S L0 A0 mem0 md0 L A mem md sp p n,
  sr_fr B API stk S L0 A0 mem0 md0 L A mem md ->
  (exists q kq, In (q, kq) (user_blocks A0) /\ ptr_addr L0 q <= data /\
     data + Z.of_nat (length D) <= ptr_addr L0 q + kq) ->
  data <= p -> p + n <= data + Z.of_nat (length D) -> off_world p n ->
  h_src L A sp p n.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md sp p n FR (q & kq & Hin & H1 & H2) Hp Hn Hw.
  pose proof FR as (_ & _ & _ & _ & _ & _ & _ & Hub & _).
  destruct (Hub q kq Hin) as [HinA Hpa].
  right. split; [exact Hw|]. left. exists q, kq. split; [exact HinA|]. rewrite Hpa. lia.
Qed.

(* ---- build_and_receive from the loop ---- *)

Lemma llvm_length_upd_in : forall (bs v : list byte) k m, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat m ->
  length bs = m -> length (upd bs k v) = m.
Proof. intros bs v k m Hk Hv Hb. subst m. apply length_upd; [exact Hk | exact Hv]. Qed.

(* spec.h:228-247 writes max(60, 30 + len) bytes (the proof of TSim/RxOpLib.v spec_build_frame_len) *)
Lemma llvm_bar_len : forall dst src send ack retry cmd body, (length body <= 1484)%nat ->
  0 <= bar_len dst src send ack retry cmd body <= 1514.
Proof.
  intros dst src send ack retry cmd body Hb. unfold bar_len. split; [lia|].
  cbv beta iota zeta delta [spec_build_frame fst].
  assert (Hn : 30 + Z.of_nat (length body) <=
               (if 30 + Z.of_nat (length body) <? 60 then 60 else 30 + Z.of_nat (length body)) <= 1514).
  { destruct (Z.ltb_spec (30 + Z.of_nat (length body)) 60); cbv beta iota; lia. }
  set (n := if 30 + Z.of_nat (length body) <? 60 then 60 else 30 + Z.of_nat (length body)) in *.
  clearbody n.
  match goal with |- Z.of_nat (length ?X) <= _ => assert (E : length X = Z.to_nat n) end.
  { destruct (Z.of_nat (length body) =? 0); cbv beta iota;
      repeat (apply llvm_length_upd_in;
              [lia | rewrite ?length_put16, ?length_put32, ?length_firstn; cbn [length]; lia | ]);
      apply repeat_length. }
  rewrite E. lia.
Qed.

(* The call of build_and_receive from the loop at sp = Sp: from the SR config at its entry, with the loop's facts
   and the callee's arguments, the continuation gets the heap frame a malloc returned, the model's world at it,
   the callee-saved registers, sr_fr, the budget and llvm_mem again (the callee's window [Sp - 9856, Sp) is the
   loop's LLVM_LOOP_K, and lies above the ceiling). The callee contract is taken at every FP state. *)
Lemma llvm_sr_bar : forall Sp lo Bw (fx' : YK11.FPState) regs m0 mem md L A L0 A0 mem0 md0 b
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
    (dstp srcp bodyp : Z) (dst src body : list byte) (send ack retry cmd : Z) (P : config -> Prop),
  h_binds B API ->
  (forall fx'' : YK11.FPState, @build_and_receive_contract fx'' rc B API) ->
  sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md ->
  YM05.alloc_ceiling <= lo ->
  frm_zero (@fp_csr fx') ->
  res_ok_slots A b -> LLVMFuzzerTestOneInput_c.llvm_room b ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  llvm_mem data D Sp lo Bw m0 (normalize rsegs mem) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  (exists q kq, In (q, kq) (user_blocks A0) /\ ptr_addr L0 q <= data /\
     data + Z.of_nat (length D) <= ptr_addr L0 q + kq) ->
  bar_args B L A regs mem Bw dstp srcp bodyp dst src body send ack retry cmd ->
  (forall (fx'' : YK11.FPState) regs' mem' md' L' A' a Bw',
     h_addr_ok a ->
     build_and_receive_m timg_plain Bw a dst src send ack retry cmd body = Some (Bw', tt) ->
     regs_preserved regs regs' -> frm_zero (@fp_csr fx'') ->
     sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L' A' mem' md' -> res_ok_slots A' b ->
     llvm_mem data D Sp lo Bw' (normalize rsegs mem') (normalize rsegs mem')
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
     SR rsegs (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 build_and_receive_ENTRY) mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros Sp lo Bw fx' regs m0 mem md L A L0 A0 mem0 md0 b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
    dstp srcp bodyp dst src body send ack retry cmd P HB HBAR FR Hlo Hfrm Hres Hroom Hsp Htp Hra HM HIN HARGS K.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERR & CTX & WORLD & RELRO).
  pose proof FR as (HMR & HW & HBd & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2
                   & HRW).
  assert (HREL : mem_rel rsegs mem (normalize rsegs mem)) by exact (mem_rel_normalize rsegs mem MI).
  pose proof sr_ceiling as Hc.
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2.
  assert (Hspz : spZ regs = Sp).
  { unfold spZ. rewrite Hsp. apply MState.unsigned_lit. unfold W_BASE_PLAIN, W_LEN in *. lia. }
  assert (HK0 : build_and_receive_FRAME = 9856) by reflexivity.
  (* the model's body bound, and the budget *)
  pose proof HARGS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMOD).
  assert (Hbody : (length body <= 1484)%nat).
  { pose proof (HMOD 1 ltac:(unfold h_addr_ok; lia)) as Hn. unfold build_and_receive_m in Hn.
    destruct (SPEC_MAX_BODY <? Z.of_nat (length body)) eqn:E; [exfalso; apply Hn; reflexivity|].
    apply Z.ltb_ge in E. unfold SPEC_MAX_BODY in E. lia. }
  pose proof (llvm_bar_len dst src send ack retry cmd body Hbody) as Hbl.
  assert (Hrs : room_slots b (Z.max 1 (bar_len dst src send ack retry cmd body))).
  { unfold LLVMFuzzerTestOneInput_c.llvm_room in Hroom. destruct Hroom as (R1 & R2 & R3).
    apply room_slots_small; lia. }
  (* h_pre at the call *)
  assert (HPRE : h_pre B API build_and_receive_FRAME L A regs mem md b Bw).
  { split.
    { apply (g_pre B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md regs build_and_receive_FRAME FR Hra);
        rewrite ?Hspz, ?HK0; unfold LLVM_SR_S, LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME; try lia.
      exact Htp. }
    split; [exact HID|]. split; [exact Hh|]. split; [exact Hl|].
    split; [rewrite SEGS; exact MI|]. split; [exact Hres|].
    split; [unfold w_off_stack in HWOS |- *; rewrite Hsp, HK0; unfold LLVM_LOOP_K in HWOS; lia|].
    split; [exact (sr_wmem_back mem (normalize rsegs mem) Bw HREL HWM)|].
    split; [exact HFN|].
    exact (sr_relro_back mem (normalize rsegs mem) HREL HRO). }
  (* the call *)
  rewrite <- SEGS.
  eapply SR_bind.
  { exact (HBAR fx' HB L A regs mem md b Bw dstp srcp bodyp dst src body send ack retry cmd HPRE Hfrm HARGS Hrs). }
  intros c2 (a & Bw' & Ha & Hca & Hnimg & HBM & Hpost).
  destruct Hpost as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hcpk & HID2 & Hh2 & Hl2 & Hblk2 & Hub2 &
                     Hlen2 & Hres2 & Hro2 & Hgk & HWM2 & HFN2 & HRO2).
  pose proof Hcpk as (HMR2 & HW2 & HB2 & Hle2 & Hstab & Hrp & Hvm & Hfr & Hkeep & Hscr).
  rewrite SEGS in Hro2.
  set (n := Z.max 1 (bar_len dst src send ack retry cmd body)) in *.
  assert (HElow : forall x, (h_world x \/ a <= x < a + n \/ ms_ctx B <= x < ms_ctx B + CTX_SIZE) ->
                    x < YM05.alloc_ceiling).
  { intros x [Hx|[Hx|Hx]]; [destruct (sr_world_img B SEGS WORLD x Hx) as [_ Hx2] | |]; lia. }
  assert (FR2 : sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L2 A2 mem2 md2).
  { apply (sr_fr_call B API SEGS AX ERR WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md
             build_and_receive_FRAME regs
             (fun x => h_world x \/ a <= x < a + n \/ ms_ctx B <= x < ms_ctx B + CTX_SIZE)
             L2 A2 regs2 mem2 md2 FR);
      rewrite ?Hspz, ?HK0; unfold LLVM_SR_S, LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME; try lia.
    - exact Hcpk.
    - intros x [Hx|[Hx|Hx]].
      + right. right. left. exact Hx.
      + right. left. split; [lia|]. pose proof (Hnimg (x - a) ltac:(lia)) as Hn.
        replace (a + (x - a)) with x in Hn by lia. exact Hn.
      + right. right. right. exact Hx.
    - intros x _. unfold h_world. lia.
    - intros x Hx Hw. exfalso. pose proof (HElow x Hx). lia.
    - intros p k Hpk. exact (Hub2 p k (proj1 (Hub p k Hpk))).
    - intros x k i Hin Hi. apply blocks_In in Hin as (p & Hp & Hpin).
      destruct (Hub p k Hpin) as [HpA Hpa].
      pose proof (Hkeep p k i HpA (Hub2 p k HpA) Hi) as E. rewrite Hpa, Hp in E. exact E.
    - exact HID2.
    - exact Hro2.
    - exact Hgk. }
  rewrite SEGS.
  apply (K fx2 regs2 mem2 md2 L2 A2 a Bw' Ha HBM Hrp Hfrm2 FR2 Hres2).
  rewrite SEGS in Hfr, Hkeep, Hscr.
  apply (llvm_mem_sr_call Sp lo build_and_receive_FRAME Bw Bw' m0 mem mem2); try assumption.
  - rewrite HK0. unfold LLVM_LOOP_K. lia.
  - intros x Hx. apply Hfr.
    + left. unfold LLVM_FRAME in Hx. lia.
    + intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ x HMR Ho). lia.
    + intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ x HMR2 Ho). lia.
    + unfold scratch_k. rewrite Hspz, HK0. unfold LLVM_FRAME in Hx. intros [Hs|Hs]; lia.
    + intros Hx2. pose proof (HElow x Hx2). unfold LLVM_FRAME in Hx. lia.
  - intros x Hx. apply Hscr. left. rewrite Hspz. exact Hx.
  - intros i Hi. destruct HIN as (q & kq & Hin & H1 & H2).
    destruct (Hub q kq Hin) as [HqA Hqa].
    pose proof (Hkeep q kq (data + i - ptr_addr L q) HqA (Hub2 q kq HqA) ltac:(rewrite Hqa; lia)) as E.
    replace (ptr_addr L q + (data + i - ptr_addr L q)) with (data + i) in E by lia. exact E.
Qed.

End SR.

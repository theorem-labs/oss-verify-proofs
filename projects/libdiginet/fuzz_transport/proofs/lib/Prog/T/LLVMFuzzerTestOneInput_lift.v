(* Lifting the evt stretches of the op loop to the SR level, so the loop's binder (LLVMFuzzerTestOneInput_loopsr.v)
   sees every program point as an SR config (_sr.v llvm_sr_at). TSRGlue.v g_run does it: an SR obligation is
   discharged by an evt run to some Q and an SR re-entry from Q. Its footprint premise is the munch llvm_mem carries
   from the segment's reference memory (LLVM_FP Sp, the window and the world: op08_fp), and its re-entry is the
   _ext restart of the end point's evt predicate over the next memory (_sr.v).

   llvm_sr_seg is that crossing once, for any two program points; three crossings of the loop are made with it:
     llvm_case_sr_of_evt  a case whose body is one evt segment (cases 3, 5, 6, 7: their callees are the evt ones,
                          memset / settle / the diginet_session_* ones), case entry -> latch;
     llvm_dispatch_sr     the switch (_disp.v llvm_dispatch), head -> case;
     llvm_latch_sr_go     the latch (_lat.v llvm_latch_go), latch -> head or out. The latch has two end points, so
                          its Q is their disjunction and llvm_sr_seg takes the end point's pc from the end state. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 AllocSlots AllocRoom MemNorm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c TSRGlue
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_disp LLVMFuzzerTestOneInput_lat LLVMFuzzerTestOneInput_sr
  LLVMFuzzerTestOneInput_op08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Section LIFT.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context (data : Z) (D : list byte).

(* An SR point whose evt predicate holds only at one pc is an SR point at that pc. *)
Lemma llvm_sr_at_pc : forall (Pe : (word -> option byte) -> bvmap 5 word -> bv 32 -> machine_state -> Prop)
    pc pc0 Sp lo L0 A0 mem0 md0 b cfg,
  (forall m0 F fc R pc1 fc1 m ro, Pe m0 F fc (MS R F pc1 fc1 None m ro) -> pc1 = Z_to_bv 64 pc0) ->
  llvm_sr_at B API data D Pe pc Sp lo L0 A0 mem0 md0 b cfg ->
  llvm_sr_at B API data D Pe pc0 Sp lo L0 A0 mem0 md0 b cfg.
Proof.
  intros Pe pc pc0 Sp lo L0 A0 mem0 md0 b cfg HPC H.
  unfold llvm_sr_at in *.
  destruct H as (fx' & regs & mem & md & L & A & Ecfg & REST).
  pose proof REST as (_ & _ & _ & _ & _ & _ & _ & _ & HPe).
  pose proof (HPC _ _ _ _ _ _ _ _ HPe) as E.
  rewrite E in Ecfg, REST.
  exists fx', regs, mem, md, L, A. split; [exact Ecfg | exact REST].
Qed.

(* One evt segment of the loop at the SR level: from an SR point of Pe at pc, an evt run to Qe (from every state of
   Pe, at every reference memory), whose end states are explicit register files (tp kept in x4) with LLVM_FP's munch
   and wmono from the reference memory, and Qe restarts over any memory equal to its own. The continuation gets the
   SR point of Qe at the end state's pc. *)
Lemma llvm_sr_seg :
  forall (Pe Qe : (word -> option byte) -> bvmap 5 word -> bv 32 -> machine_state -> Prop)
         tp pc Sp lo L0 A0 mem0 md0 b cfg (P : config -> Prop),
  h_binds B API ->
  llvm_sr_at B API data D Pe pc Sp lo L0 A0 mem0 md0 b cfg ->
  (forall m0 F fc R pc0 fc0 m ro, Pe m0 F fc (MS R F pc0 fc0 None m ro) ->
     YK11.getr R 4 = tp /\ Sp < 2 ^ 63) ->
  (forall m0 F fc ms, Pe m0 F fc ms -> evt rsegs (Qe m0 F fc) ms) ->
  (forall m0 F fc ms, Qe m0 F fc ms ->
     exists R pc' m, ms = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\
       YK11.getr R 4 = tp /\
       (forall regs, Regs6ss.xregs_eqv R regs -> Regs6ss.mkR_of regs = R) /\
       munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m) ->
  (forall m0 F fc R pc0 fc0 m m' ro, (forall a, m' a = m a) ->
     Qe m0 F fc (MS R F pc0 fc0 None m ro) -> Qe m' F fc (MS R F pc0 fc0 None m' ro)) ->
  (forall pc' cfg', llvm_sr_at B API data D Qe pc' Sp lo L0 A0 mem0 md0 b cfg' -> SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros Pe Qe tp pc Sp lo L0 A0 mem0 md0 b cfg P HB HC HPT HSEG HQF HQE HK.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERR & CTX & WORLD & RELRO).
  destruct HC as (fx' & regs & mem & md & L & A & -> & Hfrm & FR & Hc1 & Hc2 & Hres & Hroom & Htp & HIN & HPe).
  destruct (HPT _ _ _ _ _ _ _ _ HPe) as [Etp HSP2].
  assert (Etp' : YK11.getr regs 4 = tp) by exact Etp.
  assert (HSmax : LLVM_SR_S Sp <= 2 ^ 64) by (unfold LLVM_SR_S, LLVM_FRAME; lia).
  eapply (g_run B API SEGS AX HGG WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 fx' regs (Z_to_bv 64 pc)
            mem md L A (Qe (normalize rsegs mem) (@fp_regs fx') (@fp_csr fx')) P FR Hc1 HSmax).
  { exact (HSEG _ _ _ _ HPe). }
  { intros ms HQ. destruct (HQF _ _ _ _ HQ) as (R & pc' & m & -> & _ & _ & MU & WM).
    exists R, (@fp_regs fx'), (Z_to_bv 64 pc'), (@fp_csr fx'), m, (LLVM_FP Sp).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x _ NO. destruct (op08_fp Sp x NO) as [Hw|Hw]; [left; exact Hw | right; left; exact Hw]. }
  intros R F pc1 fc m0' HQ regs' m' Hx Hrel FR'.
  destruct (HQF _ _ _ _ HQ) as (R2 & pc' & m2 & EQ & Etp2 & HmkR & _ & _).
  unfold MS in EQ. injection EQ; intros; subst R2 F pc1 fc m2.
  apply (HK pc').
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split; [exact FR'|].
  split; [exact Hc1|]. split; [exact Hc2|].
  split; [exact Hres|]. split; [exact Hroom|].
  split; [rewrite (sr_getr_eqv _ _ _ Hx), Etp2, <- Etp'; exact Htp|].
  split; [exact HIN|].
  cbn [fp_regs fp_csr].
  rewrite (HmkR regs' Hx).
  eapply (HQE (normalize rsegs mem) _ _ _ _ _ m0'); [|exact HQ].
  intros x. symmetry. exact (proj1 Hrel x).
Qed.

(* ---- the end points' facts llvm_sr_seg asks for ---- *)

Lemma llvm_head_pt : forall m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro,
  llvm_head data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc0 fc0 None m ro) ->
  YK11.getr R 4 = tp /\ Sp < 2 ^ 63.
Proof.
  intros m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _ & _ & _ & HM).
  unfold llvm_mem in HM. destruct HM as (_ & _ & _ & _ & _ & _ & HSP2 & _).
  split; [|unfold LLVM_FRAME in HSP2; lia].
  apply (f_equal (fun ms => YK11.getr (ms_regs ms) 4)) in EMS. exact EMS.
Qed.

Lemma llvm_case_pt : forall m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro,
  llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (MS R F pc0 fc0 None m ro) ->
  YK11.getr R 4 = tp /\ Sp < 2 ^ 63.
Proof.
  intros m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _ & _ & _ & _ & HM).
  unfold llvm_mem in HM. destruct HM as (_ & _ & _ & _ & _ & _ & HSP2 & _).
  split; [|unfold LLVM_FRAME in HSP2; lia].
  apply (f_equal (fun ms => YK11.getr (ms_regs ms) 4)) in EMS. exact EMS.
Qed.

Lemma llvm_latch_pt : forall m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro,
  llvm_latch data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc0 fc0 None m ro) ->
  YK11.getr R 4 = tp /\ Sp < 2 ^ 63.
Proof.
  intros m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc0 fc0 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r20 & r23 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _ & _ & HM).
  unfold llvm_mem in HM. destruct HM as (_ & _ & _ & _ & _ & _ & HSP2 & _).
  split; [|unfold LLVM_FRAME in HSP2; lia].
  apply (f_equal (fun ms => YK11.getr (ms_regs ms) 4)) in EMS. exact EMS.
Qed.

Lemma llvm_head_qf : forall m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_head data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  exists R pc' m, ms = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\
    YK11.getr R 4 = tp /\
    (forall regs, Regs6ss.xregs_eqv R regs -> Regs6ss.mkR_of regs = R) /\
    munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m.
Proof.
  intros m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & _ & _ & _ & HM).
  unfold llvm_mem in HM. destruct HM as (MU & WM & _).
  do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [intros regs Hx; apply llvm_mkR_of_eqv; exact Hx|].
  split; [exact MU | exact WM].
Qed.

Lemma llvm_case_qf : forall m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  exists R pc' m, ms = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\
    YK11.getr R 4 = tp /\
    (forall regs, Regs6ss.xregs_eqv R regs -> Regs6ss.mkR_of regs = R) /\
    munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m.
Proof.
  intros m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & _ & _ & _ & _ & HM).
  unfold llvm_mem in HM. destruct HM as (MU & WM & _).
  do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [intros regs Hx; apply llvm_mkR_of_eqv; exact Hx|].
  split; [exact MU | exact WM].
Qed.

Lemma llvm_latch_qf : forall m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_latch data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  exists R pc' m, ms = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\
    YK11.getr R 4 = tp /\
    (forall regs, Regs6ss.xregs_eqv R regs -> Regs6ss.mkR_of regs = R) /\
    munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m.
Proof.
  intros m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r20 & r23 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & _ & _ & HM).
  unfold llvm_mem in HM. destruct HM as (MU & WM & _).
  do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [intros regs Hx; apply llvm_mkR_of_eqv; exact Hx|].
  split; [exact MU | exact WM].
Qed.

Lemma llvm_out_qf : forall m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_out data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  exists R pc' m, ms = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\
    YK11.getr R 4 = tp /\
    (forall regs, Regs6ss.xregs_eqv R regs -> Regs6ss.mkR_of regs = R) /\
    munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m.
Proof.
  intros m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                 r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HM).
  unfold llvm_mem in HM. destruct HM as (MU & WM & _).
  do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [intros regs Hx; apply llvm_mkR_of_eqv; exact Hx|].
  split; [exact MU | exact WM].
Qed.

(* the pc each end point holds at *)
Lemma llvm_head_pc : forall m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro,
  llvm_head data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc1 fc1 None m ro) ->
  pc1 = Z_to_bv 64 LLVM_HEAD_PC.
Proof.
  intros m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _).
  apply (f_equal ms_pc_val) in EMS. exact EMS.
Qed.

Lemma llvm_case_pc : forall m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro,
  llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (MS R F pc1 fc1 None m ro) ->
  pc1 = Z_to_bv 64 (LLVM_CASE i).
Proof.
  intros m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _).
  apply (f_equal ms_pc_val) in EMS. exact EMS.
Qed.

Lemma llvm_latch_pc : forall m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro,
  llvm_latch data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc1 fc1 None m ro) ->
  pc1 = Z_to_bv 64 LLVM_LATCH_PC.
Proof.
  intros m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r20 & r23 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _).
  apply (f_equal ms_pc_val) in EMS. exact EMS.
Qed.

Lemma llvm_out_pc : forall m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro,
  llvm_out data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MS R F pc1 fc1 None m ro) ->
  pc1 = Z_to_bv 64 LLVM_OUT_PC.
Proof.
  intros m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc1 fc1 m ro H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                 r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & _).
  apply (f_equal ms_pc_val) in EMS. exact EMS.
Qed.

(* ---- the three crossings ---- *)

(* A case whose whole body is one evt segment: from its entry to the latch. *)
Lemma llvm_case_sr_of_evt :
  forall gp tp i Sp lo ops c c1 cout Bw Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         L0 A0 mem0 md0 b cfg P,
  h_binds B API ->
  llvm_case_sr B API data D gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    L0 A0 mem0 md0 b cfg ->
  (forall m0 F fc ms (Q : machine_state -> Prop),
     llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
     (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout Bres
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
     evt rsegs Q ms) ->
  (forall cfg', llvm_latch_sr B API data D gp tp Sp lo ops cout Bres
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' -> SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp i Sp lo ops c c1 cout Bw Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         L0 A0 mem0 md0 b cfg P HB HC HEVT HK.
  apply (llvm_sr_seg
           (fun m0 F fc => llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
           (fun m0 F fc => llvm_latch data D m0 gp tp Sp lo ops cout Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
           tp (LLVM_CASE i) Sp lo L0 A0 mem0 md0 b cfg P HB HC).
  - intros m0 F fc R pc0 fc0 m ro H. cbv beta in H. eapply llvm_case_pt. exact H.
  - intros m0 F fc ms H. cbv beta in H. apply (HEVT m0 F fc ms _ H). intros ms' H'. apply evt_done. exact H'.
  - intros m0 F fc ms H. cbv beta in H. eapply llvm_latch_qf. exact H.
  - intros m0 F fc R pc0 fc0 m m' ro E H. cbv beta in H |- *. eapply llvm_latch_ext; [exact E | exact H].
  - intros pc' cfg' H. apply HK. unfold llvm_latch_sr.
    apply (llvm_sr_at_pc _ pc'); [|exact H].
    intros m0 F fc R pc1 fc1 m ro H'. cbv beta in H'. eapply llvm_latch_pc. exact H'.
Qed.

(* The switch (_disp.v llvm_dispatch): head -> the case the op byte selects. *)
Lemma llvm_dispatch_sr :
  forall gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P,
  h_binds B API ->
  llvm_head_sr B API data D gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  (forall cfg', llvm_case_sr B API data D gp tp (snd (fuzz_u8_m D c) mod 9) Sp lo ops c (fst (fuzz_u8_m D c)) Bw
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' -> SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P HB HC HK.
  apply (llvm_sr_seg
           (fun m0 F fc => llvm_head data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
           (fun m0 F fc => llvm_case data D m0 gp tp (snd (fuzz_u8_m D c) mod 9) Sp lo ops c (fst (fuzz_u8_m D c)) Bw
                             ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
           tp LLVM_HEAD_PC Sp lo L0 A0 mem0 md0 b cfg P HB HC).
  - intros m0 F fc R pc0 fc0 m ro H. cbv beta in H. eapply llvm_head_pt. exact H.
  - intros m0 F fc ms H. cbv beta in H. eapply llvm_dispatch; [exact H|].
    intros ms' H'. apply evt_done. exact H'.
  - intros m0 F fc ms H. cbv beta in H. eapply llvm_case_qf. exact H.
  - intros m0 F fc R pc0 fc0 m m' ro E H. cbv beta in H |- *. eapply llvm_case_ext; [exact E | exact H].
  - intros pc' cfg' H. apply HK. unfold llvm_case_sr.
    apply (llvm_sr_at_pc _ pc'); [|exact H].
    intros m0 F fc R pc1 fc1 m ro H'. cbv beta in H'. eapply llvm_case_pc. exact H'.
Qed.

(* The latch (_lat.v llvm_latch_go): latch -> the next head, or out with the reason it left. *)
Lemma llvm_latch_sr_go :
  forall gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P,
  h_binds B API ->
  llvm_latch_sr B API data D gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  (forall cfg', llvm_head_sr B API data D gp tp Sp lo (ops + 1) c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  L0 A0 mem0 md0 b cfg' -> SR rsegs cfg' P) ->
  (forall cfg', (0x3fe < ops \/ fi_n c = 0) ->
     llvm_out_sr B API data D gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P HB HC HH HO.
  apply (llvm_sr_seg
           (fun m0 F fc => llvm_latch data D m0 gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
           (fun m0 F fc ms =>
              llvm_head data D m0 gp tp Sp lo (ops + 1) c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms \/
              ((0x3fe < ops \/ fi_n c = 0) /\
               llvm_out data D m0 gp tp Sp lo Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms))
           tp LLVM_LATCH_PC Sp lo L0 A0 mem0 md0 b cfg P HB HC).
  - intros m0 F fc R pc0 fc0 m ro H. cbv beta in H. eapply llvm_latch_pt. exact H.
  - intros m0 F fc ms H. cbv beta in H. eapply llvm_latch_go; [exact H | |].
    + intros ms' H'. apply evt_done. left. exact H'.
    + intros ms' W H'. apply evt_done. right. split; [exact W | exact H'].
  - intros m0 F fc ms H. cbv beta in H. destruct H as [H|[_ H]].
    + eapply llvm_head_qf. exact H.
    + eapply llvm_out_qf. exact H.
  - intros m0 F fc R pc0 fc0 m m' ro E H. cbv beta in H |- *. destruct H as [H|[W H]].
    + left. eapply llvm_head_ext; [exact E | exact H].
    + right. split; [exact W|]. eapply llvm_out_ext; [exact E | exact H].
  - intros pc' cfg' H.
    destruct H as (fx' & regs & mem & md & L & A & Ecfg & Hfrm & FR & Hc1 & Hc2 & Hres & Hroom & Htp & HIN & HPe).
    cbv beta in HPe. destruct HPe as [HPe|[W HPe]].
    + apply HH. unfold llvm_head_sr.
      apply (llvm_sr_at_pc _ pc').
      { intros m0 F fc R pc1 fc1 m ro H'. cbv beta in H'. eapply llvm_head_pc. exact H'. }
      exists fx', regs, mem, md, L, A.
      split; [exact Ecfg|]. split; [exact Hfrm|]. split; [exact FR|]. split; [exact Hc1|]. split; [exact Hc2|].
      split; [exact Hres|]. split; [exact Hroom|]. split; [exact Htp|]. split; [exact HIN|]. exact HPe.
    + apply (HO cfg' W). unfold llvm_out_sr.
      apply (llvm_sr_at_pc _ pc').
      { intros m0 F fc R pc1 fc1 m ro H'. cbv beta in H'. eapply llvm_out_pc. exact H'. }
      exists fx', regs, mem, md, L, A.
      split; [exact Ecfg|]. split; [exact Hfrm|]. split; [exact FR|]. split; [exact Hc1|]. split; [exact Hc2|].
      split; [exact Hres|]. split; [exact Hroom|]. split; [exact Htp|]. split; [exact HIN|]. exact HPe.
Qed.

End LIFT.

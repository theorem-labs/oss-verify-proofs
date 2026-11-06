(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the walk piece
   rs_piece_W6b_stmt of lib/A/RtPgSeg.v, ent_build's cases 1, 4, 5 and 9 inside LLVMFuzzerTestOneInput (0x80714),
   from the case entries (rs_cut_D at 0x817c4, 0x81668, 0x81804, 0x81954) to the join J 0x81e00 (rs_cut_J).
   Proves no function (kind: segment lemma).

   The piece is a chain: the entry bridge of lib/A/RtPgEntBCut.v (eb_D: rs_cut_D -> the case block's premises),
   the case's block statement of lib/A/RtPgW6bBase.v (w6b_c1_stmt / w6b_c4_stmt / w6b_c5_stmt / w6b_c9_stmt, taken
   as hypotheses: other lanes prove them), and the join bridge (eb_J_of: the block's rts_post -> rs_cut_J), after which
   the piece's continuation at J (rs_from_J) runs. The meter of the segment needs ameter_laws MT (the post's mo_le
   chains through the case). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgW6aBase RtPgW6bBase RtPgEntBCut.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/A/RtPgSeg.v *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* image A's loaded segments, as RtPgSteps names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* one case: from the cut at its entry, through its block, to the cut at J and the piece's continuation there *)
Lemma w6b_case_of : forall pc (P : Z -> Prop) (X : world rsegs -> (word -> option byte) -> Prop) cx POST rest i k kd
  ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r,
  w6b_case_stmt B MT pc P X ->
  rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k ->
  (length ps = i)%nat -> (length es = k)%nat ->
  rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
  P kd -> X W2 mem2 ->
  SRr rsegs W2 (cfg_at rsegs pc regs2 mem2 md2) POST.
Proof.
  intros pc P X cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r HC HST HJ Hi Hk HD HP HX.
  destruct (eb_D B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD)
    as ((b & Erb & Eb) & HCTX & HIN & _ & _).
  subst rr kd.
  eapply SRr_bind.
  { exact (HC (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
      ly2 S2 W2 mem2 md2 regs2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx) (rs_cur rsegs cx rest r)
      (shadow_addr (q_pp (x_e cx) + 0x4000)) (q_pp (x_e cx)) b r HCTX HP HIN HX). }
  intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
  exact (HJ ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r) (snd (ent_build (b :: r))) (fst (ent_build (b :: r)))
    Hi Hk (eb_J_of B MT MTL cx rest sh np ps cnt es (b :: r) r (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2
             ly3 S3 W3 regs3 mem3 md3 HST HD HJ3 Hr3 Hf3 Hp3 Hio3 Hmo3 Hm3 HR3)).
Qed.

(* the piece: kind % 10 picks the case (rs_pc_D), each case's block is the hypothesis of its lane *)
Theorem w6b_piece_of : w6b_c1_stmt B MT -> w6b_c4_stmt B MT -> w6b_c5_stmt B MT -> w6b_c9_stmt B MT ->
  rs_piece_W6b_stmt rsegs B MT.
Proof.
  intros C1 C4 C5 C9 cx POST rest i k kd HST Hkd HJ ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hi Hk HD.
  destruct (eb_D B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (_ & _ & _ & HS & HV).
  cbn [In] in Hkd. destruct Hkd as [E | [E | [E | [E | []]]]].
  - replace (rs_pc_D kd) with W6B_D1 by (unfold rs_pc_D; rewrite <- E; reflexivity).
    exact (w6b_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C1 HST HJ Hi Hk HD
      (eq_sym E) HV).
  - replace (rs_pc_D kd) with W6B_D4 by (unfold rs_pc_D; rewrite <- E; reflexivity).
    exact (w6b_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C4 HST HJ Hi Hk HD
      (eq_sym E) I).
  - replace (rs_pc_D kd) with W6B_D5 by (unfold rs_pc_D; rewrite <- E; reflexivity).
    exact (w6b_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C5 HST HJ Hi Hk HD
      (eq_sym E) I).
  - replace (rs_pc_D kd) with W6_D9 by (unfold rs_pc_D; rewrite <- E; reflexivity).
    exact (w6b_case_of _ _ _ cx POST rest i k kd ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r C9 HST HJ Hi Hk HD
      (eq_sym E) HS).
Qed.
End p.

Print Assumptions w6b_piece_of.

(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6b.v at f3898085bda; for reac-pw/fuzz_headamp image A, proving HPgSeg's hs_piece_W6b_stmt: module paths and the rs_ prefix renamed to hs_, the strlen trampoline 0x41b98 (lib/A/Rt/StrlenDef.v STRLEN_ENTRY_A) and __asan_memcpy 0x51d0c. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the walk piece "ent_build B" of
   LLVMFuzzerTestOneInput (0x80bc0), lib/A/HPgSeg.v's hs_piece_W6b_stmt: the cases 1, 4, 5 and 9 of ent_build's
   `switch (kind % 10)` (pod.h:285-296, 326-339, 367-377), from each case entry to the join J 0x8237c.
   Proves no function (kind: segment lemma).

   hs_piece_W6b_of_blocks: the piece from the four case blocks of lib/A/HPgW6bBase.v. At a case entry (hs_cut_D)
   the kind byte kd is the first byte b of the turn's input rr = b :: r, and hs_pc_D kd is the case's pc
   (W6B_D1 / D4 / D5 / D9). lib/A/HPgEntBCut.v's eb_D_w6b gives the block's context and entry state, eb_D_img what
   cases 9 and 1 read of the image (ent_build.s, the table ent_build.vocab and its nine strings). The block runs to
   J; there eb_J_post turns its post into hs_cut_J, and the continuation hs_from_J runs on with the same property and
   pod counts.
   hs_piece_W6b: the piece itself, hs_piece_W6b_of_blocks applied to the four proved blocks (lib/A/HPgW6bC4.v,
   HPgW6bC5.v, HPgW6bC9.v, HPgW6bC1.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSeg HPgEntBCut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgW6aBase HPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgW6bC1 HPgW6bC4 HPgW6bC5 HPgW6bC9.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/A/HPgSeg.v *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_e {segs} _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma hs_piece_W6b_of_blocks :
  HPgW6bBase.w6b_c4_stmt B MT -> HPgW6bBase.w6b_c5_stmt B MT -> HPgW6bBase.w6b_c9_stmt B MT ->
  HPgW6bBase.w6b_c1_stmt B MT -> hs_piece_W6b_stmt rsegs B MT.
Proof.
  intros C4 C5 C9 C1 cx POST rest i k kd HST Hkd HJ.
  unfold hs_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hi Hk HD.
  pose proof (eb_D_w6b B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (Hctx & Hin).
  pose proof (eb_D_img B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (Hs9 & Hvoc).
  (* the kind byte is the first byte of the turn's input *)
  pose proof HD as (_ & _ & _ & _ & _ & _ & Hfu & _ & Hrr).
  destruct rr as [|b r0]; [congruence|].
  cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
  (* from J on: eb_J_post and the continuation *)
  assert (KJ : forall W3 c3,
    HPgW6aBase.w6_post B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
      (x_own cx) (x_k cx) regs2 ly2 S2 W2 mem2 md2 HPgW6aBase.W6_J HPgW6bBase.w6b_clob
      (HPgW6bBase.w6b_wr (e_R (x_e cx)) (e_F (x_e cx)))
      (HPgW6bBase.w6b_J_R (e_R (x_e cx)) (e_F (x_e cx)) (hs_cur rsegs cx rest r)
        (shadow_addr (e_pp (x_e cx) + 0x4000)) (e_pp (x_e cx)) r (b :: r)) W3 c3 ->
    SRr rsegs W3 c3 POST).
  { intros W3 c3 HP.
    destruct (eb_J_post B MT MTL cx rest sh np ps cnt es (b :: r) r (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2 W3 c3
      HST HD HP) as (regs3 & mem3 & md3 & ly3 & S3 & -> & HJc).
    exact (HJ ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r) _ _ Hi Hk HJc). }
  cbn [In] in Hkd. destruct Hkd as [E | [E | [E | [E | []]]]]; symmetry in E.
  - (* case 1 *)
    assert (Epc : hs_pc_D (bv_unsigned b) = HPgW6bBase.W6B_D1) by (unfold hs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin Hvoc)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - (* case 4 *)
    assert (Epc : hs_pc_D (bv_unsigned b) = HPgW6bBase.W6B_D4) by (unfold hs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin I)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - (* case 5 *)
    assert (Epc : hs_pc_D (bv_unsigned b) = HPgW6bBase.W6B_D5) by (unfold hs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin I)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - (* case 9 *)
    assert (Epc : hs_pc_D (bv_unsigned b) = HPgW6bBase.W6B_D9) by (unfold hs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin Hs9)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
Qed.

(* ============================== the piece ==============================
   The four case blocks (HPgW6bC4 / C5 / C9 / C1) in the piece. The calls the cases make are the kernel's
   __asan_memcpy (aintrin_realizes OCpy at 0x51d0c) and the strlen wrapper's contract (lib/A/Rt/StrlenDef.v
   astrlen_realizes) at its trampoline 0x41b98, both Section hypotheses here as in every walk lane that calls them. *)
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.
Hypothesis STRL : astrlen_realizes rsegs B W7_STRLEN.
Theorem hs_piece_W6b : hs_piece_W6b_stmt rsegs B MT.
Proof using MTL LAWS MCPY STRL.
  apply hs_piece_W6b_of_blocks.
  - eapply HPgW6bC4.w6b_c4; eassumption.
  - eapply HPgW6bC5.w6b_c5; eassumption.
  - eapply HPgW6bC9.w6b_c9; eassumption.
  - eapply HPgW6bC1.w6b_c1; eassumption.
Qed.

End b.

Print Assumptions hs_piece_W6b_of_blocks.
Print Assumptions hs_piece_W6b.

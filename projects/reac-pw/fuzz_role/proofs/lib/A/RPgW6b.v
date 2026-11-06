(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the walk piece "ent_build B" of
   LLVMFuzzerTestOneInput (0x7ff88), lib/A/RPgSeg.v's rs_piece_W6b_stmt: the cases 1, 4, 5 and 9 of ent_build's
   `switch (kind % 10)` (pod.h:285-296, 326-339, 367-377), from each case entry to the join J 0x8165c.
   Proves no function (kind: segment lemma).

   rs_piece_W6b_of_blocks: the piece from the four case blocks of lib/A/RPgW6bBase.v. At a case entry (rs_cut_D)
   the kind byte kd is the first byte b of the turn's input rr = b :: r, and rs_pc_D kd is the case's pc
   (W6B_D1 / D4 / D5 / D9). lib/A/RPgEntBCut.v's eb_D_w6b gives the block's context and entry state, eb_D_img what
   cases 9 and 1 read of the image (ent_build.s, the table ent_build.vocab and its nine strings). The block runs to
   J; there eb_J_post turns its post into rs_cut_J, and the continuation rs_from_J runs on with the same property and
   pod counts.
   rs_piece_W6b: the piece itself, rs_piece_W6b_of_blocks applied to the four proved blocks (lib/A/RPgW6bC4.v,
   RPgW6bC5.v, RPgW6bC9.v, RPgW6bC1.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgSeg RPgEntBCut.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgW6aBase RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgW6bC1 RPgW6bC4 RPgW6bC5 RPgW6bC9.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.Rt Require Import StrlenDef.
Import ListNotations.
(* the cut record's projections, with the segments implicit as inside lib/A/RPgSeg.v *)
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

Lemma rs_piece_W6b_of_blocks :
  RPgW6bBase.w6b_c4_stmt B MT -> RPgW6bBase.w6b_c5_stmt B MT -> RPgW6bBase.w6b_c9_stmt B MT ->
  RPgW6bBase.w6b_c1_stmt B MT -> rs_piece_W6b_stmt rsegs B MT.
Proof.
  intros C4 C5 C9 C1 cx POST rest i k kd HST Hkd HJ.
  unfold rs_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hi Hk HD.
  pose proof (eb_D_w6b B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (Hctx & Hin).
  pose proof (eb_D_img B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as (Hs9 & Hvoc).
  (* the kind byte is the first byte of the turn's input *)
  pose proof HD as (_ & _ & _ & _ & _ & _ & Hfu & _ & Hrr).
  destruct rr as [|b r0]; [congruence|].
  cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
  (* from J on: eb_J_post and the continuation *)
  assert (KJ : forall W3 c3,
    RPgW6aBase.w6_post B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
      (x_own cx) (x_k cx) regs2 ly2 S2 W2 mem2 md2 RPgW6aBase.W6_J RPgW6bBase.w6b_clob
      (RPgW6bBase.w6b_wr (e_R (x_e cx)) (e_F (x_e cx)))
      (RPgW6bBase.w6b_J_R (e_R (x_e cx)) (e_F (x_e cx)) (rs_cur rsegs cx rest r)
        (shadow_addr (e_pp (x_e cx) + 0x4000)) (e_pp (x_e cx)) r (b :: r)) W3 c3 ->
    SRr rsegs W3 c3 POST).
  { intros W3 c3 HP.
    destruct (eb_J_post B MT MTL cx rest sh np ps cnt es (b :: r) r (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2 W3 c3
      HST HD HP) as (regs3 & mem3 & md3 & ly3 & S3 & -> & HJc).
    exact (HJ ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r) _ _ Hi Hk HJc). }
  cbn [In] in Hkd. destruct Hkd as [E | [E | [E | [E | []]]]]; symmetry in E.
  - (* case 1 *)
    assert (Epc : rs_pc_D (bv_unsigned b) = RPgW6bBase.W6B_D1) by (unfold rs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin Hvoc)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - (* case 4 *)
    assert (Epc : rs_pc_D (bv_unsigned b) = RPgW6bBase.W6B_D4) by (unfold rs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin I)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - (* case 5 *)
    assert (Epc : rs_pc_D (bv_unsigned b) = RPgW6bBase.W6B_D5) by (unfold rs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin I)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
  - (* case 9 *)
    assert (Epc : rs_pc_D (bv_unsigned b) = RPgW6bBase.W6B_D9) by (unfold rs_pc_D; rewrite E; reflexivity).
    rewrite Epc. eapply SRr_bind; [exact (C9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ _ _ _ _ _ b r Hctx E Hin Hs9)|].
    intros W3 c3 _ HP. exact (KJ W3 c3 HP).
Qed.

(* ============================== the piece ==============================
   The four case blocks (RPgW6bC4 / C5 / C9 / C1) in the piece. The calls the cases make are the kernel's
   __asan_memcpy (aintrin_realizes OCpy at 0x510d4) and RoleA4Rt's strlen wrapper contract at its trampoline
   0x41ac8, both Section hypotheses here as in every walk lane that calls them. *)
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.
Hypothesis STRL : astrlen_realizes rsegs B W7_STRLEN.
Theorem rs_piece_W6b : rs_piece_W6b_stmt rsegs B MT.
Proof using MTL LAWS MCPY STRL.
  apply rs_piece_W6b_of_blocks.
  - eapply RPgW6bC4.w6b_c4; eassumption.
  - eapply RPgW6bC5.w6b_c5; eassumption.
  - eapply RPgW6bC9.w6b_c9; eassumption.
  - eapply RPgW6bC1.w6b_c1; eassumption.
Qed.

End b.

Print Assumptions rs_piece_W6b_of_blocks.
Print Assumptions rs_piece_W6b.

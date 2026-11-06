(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module paths and module names changed; 112 of its 154 lines of code are new or changed and 267 lines of the source are left out. *)
(* check_marks (fuzz_link.asan 0x8848c) on image A: the strcmp call and the exit of its walk (lib/A/Prog/check_marks.v,
   contract lib/A/Prog/check_marks_c.v `check_marks_acontract`, K = CHECK_MARKS_AK = 32 + 2 * ESTACK = 8224).
   - cm_call: the `jal wrapper_strcmp` of the loop (+0x74), at sp' = sp - 32 with a0 = q (got->name[i]) and a1 = y
     (m->mark[i]), through LinkWalkStrcmp.v `aj_gx_astrcmp_at` over lib/Reusable/AStrcmpDef.v `astrcmp_realizes`
     (the stop index of the two C strings from `astrcmp_cstr_meet`). It gives what the loop needs: the journal at
     the end memory, the registers the wrapper keeps, `a0 = 0` exactly when the two strings are equal (the
     `bnez a0` of +0x78), the memory outside [sp - K, sp - 32) unchanged, and every present byte still present.
     The wrapper writes only [sp' - 2 * ESTACK, sp') = [sp - K, sp - 32).
   - cm_exit: the Post at the `ret` (+0xa0), by LinkWalk.v `apost_leaf` with E empty: the write set
     `check_marks_awr` is [] and the run writes only inside [sp - K, sp); `check_marks_apost` is True.
   The two lemmas are lib/A/Prog/fuzz_if_nametoindex.v's ix_call and ix_exit with check_marks' frame (32 bytes) and K.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkStrcmp index_of_c check_marks_c CheckMarksKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis STRCMP : AStrcmpDef.astrcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strcmp).

(* ---- the call of wrapper_strcmp in the loop, in the shape the loop needs ---- *)
Lemma cm_call : forall (W : world SEGS) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k
    (regs rgs : bvmap 5 word) (memT : word -> option byte) q y nm n2 raw,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdq k ->
  spZ rgs = spZ regs - 32 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CHECK_MARKS_AK -> spZ regs <= sp0 ->
  getr rgs 3 = w64 (as_gp B) -> getr rgs 4 = w64 (as_tp B) ->
  getr rgs 1 = raw -> YK0s.ret_ok raw ->
  getr rgs 10 = w64 q -> getr rgs 11 = w64 y ->
  acstr_at SEGS (rdW W memT) q n2 -> acstr_at SEGS (rdW W memT) y nm ->
  cm_argf regs (rdW W memT) q n2 -> cm_argf regs (rdW W memT) y nm ->
  SRr SEGS W
    (mkCfg (mkst rgs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdq)
    (fun W2 cf => W2 = W /\ exists regs2 mem2 md2,
       cf = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       same_but_materialized mdq md2 /\
       aregs_preserved rgs regs2 /\
       (getr regs2 10 = w64 0 <-> n2 = nm) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs - 32) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k regs rgs memT q y nm n2 raw
  HGX HJ Hsp H16 Hwlo Hwhi Hgp Htp Hra Hraw H10 H11 CSq CSy AQ AY.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : CHECK_MARKS_AK = 8224) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof AQ as (Aq0 & Aqlen & Aqmem & Aqra & Aqhull & Aqpart).
pose proof AY as (Ay0 & Aylen & Aymem & Ayra & Ayhull & Aypart).
destruct (astrcmp_cstr_meet SEGS W memT q y n2 nm CSq CSy)
  as (kk & cb1 & cb2 & Hkk0 & Hkk1 & Hkk2 & HMEET & HIFF).
unfold apart_frame in Aqpart, Aypart.
eapply SRr_mono.
{ apply (aj_gx_astrcmp_at SK SEGS B LAWS pa_segs_low
    (pa_sigma LS___interceptor_trampoline_strcmp) STRCMP
    G XO OUT W rgs memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k q y kk cb1 cb2 raw).
  - exact HGX.
  - exact HJ.
  - rewrite Hsp. replace (spZ regs - 32) with (spZ regs - 2 * 16) by lia.
    rewrite Zminus_mod, H16. reflexivity.
  - lia.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact H10.
  - exact H11.
  - exact Aq0.
  - exact Ay0.
  - lia.
  - unfold amem_range, kHighMemBeg, kLowMemEnd in Aqmem. lia.
  - unfold amem_range, kHighMemBeg, kLowMemEnd in Aymem. lia.
  - exact HMEET.
  - apply (cm_src_ok W rgs memT q n2 kk CSq ltac:(lia)). intros a Ha. lia.
  - apply (cm_src_ok W rgs memT y nm kk CSy ltac:(lia)). intros a Ha. lia.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact (cm_amem_sub2 q (Z.of_nat (length n2) + 1) (kk + 1) Aqmem ltac:(lia) ltac:(lia)).
  - exact (cm_amem_sub2 y (Z.of_nat (length nm) + 1) (kk + 1) Aymem ltac:(lia) ltac:(lia)).
  - exact (cm_ra_sub2 _ q (Z.of_nat (length n2) + 1) q (kk + 1) Aqra ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (cm_hull_sub2 _ q (Z.of_nat (length n2) + 1) (kk + 1) Aqhull ltac:(lia) ltac:(lia)).
  - exact (cm_ra_sub2 _ y (Z.of_nat (length nm) + 1) y (kk + 1) Ayra ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (cm_hull_sub2 _ y (Z.of_nat (length nm) + 1) (kk + 1) Ayhull ltac:(lia) ltac:(lia)). }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsame & HP2 & Hres & Hfr & Hpres).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hsame|]. split; [exact HP2|].
split.
{ rewrite Hres. split.
  - intros Hw. apply (proj1 HIFF). apply cm_res_eq.
    rewrite Hw. apply unsigned_lit_small. lia.
  - intros Heq. rewrite (proj2 HIFF Heq). reflexivity. }
split; [|exact Hpres].
intros a Ha Hw. apply (Hfr a Ha). rewrite Hsp. lia.
Qed.

(* ---- the Post at the exit of the walk ---- *)
Lemma cm_exit : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) (mem2 : word -> option byte) md2,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - CHECK_MARKS_AK -> spZ regs <= sp0 ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  apost SK SEGS B CHECK_MARKS_AK 0
    (fun a => inFP (check_marks_awr regs (rdW W memc)) a)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2' mem2' md2' =>
       S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       check_marks_apost regs (rdW W memc) regs2' (rdW W2 mem2'))
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
  HJ HJ2 Hwlo Hwhi Hfd Hfs HP UN GR.
pose proof HJ2 as (HSTK2 & HXO2 & (memS2 & HJi2 & _) & _).
pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HK : CHECK_MARKS_AK = 8224) by reflexivity.
assert (HPW : forall a, spZ regs - CHECK_MARKS_AK <= a < spZ regs -> apresent (w_H W) mem2 a).
{ intros a Ha. apply Hpres2. lia. }
apply (apost_leaf SK SEGS B LAWS pa_segs_low CHECK_MARKS_AK 0
  (fun a => inFP (check_marks_awr regs (rdW W memc)) a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 _
  HJ HJ2 ltac:(lia) Hwlo ltac:(lia) Hfd Hfs HP
  ltac:(intros a Ha Hw _; exact (UN a Ha Hw)) GR
  HPW
  ltac:(intros x Hx; unfold check_marks_awr, inFP in Hx;
        destruct Hx as (yy & Hin & _); destruct Hin)).
split; [apply cm_set_fs_id|]. split; [apply Permutation_refl|].
exact I.
Qed.

End w.

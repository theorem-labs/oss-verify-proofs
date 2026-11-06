(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParse.v at afaa3cb55c1d for reac-pw/fuzz_rate's
   reac_rate_prop_parse: module paths and names changed to rate's (rt_parse_specX, the RtPgParse files), rt_parse_specX's
   extra premise 0 < Q is taken and not used, the theorems are named rt_parse_A_of_segs / rt_parse_A. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgParse.v at f7246d55e8c3 for image B
   (fuzz_rate.asan-ubsan): the image is lib/AU/Img0.v's, the segment statements are lib/AU/RtPgParseBaseB.v's, the
   segment files are image B's twins (lib/AU/RtPgParse{E,F,L,LB,K,FV,T}B.v of A's RtPgParse{E,F,L,LB,K,FV,T}.v:
   RtPgParseLB.v is the twin of A's L file, RtPgParseLBB.v of A's LB file), rt_parse_specX's premise 0 < Q goes into
   call_ok (image B's store tests Q against 0), the theorems are named rt_parse_B_of_segs / rt_parse_B, and the
   closure check of rt_parse_B is printed at the end. *)
(* reac_rate_prop_parse 0x8474c of reac-pw/fuzz_rate's ASan image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14): the composition of the walk's segments
   (lib/AU/RtPgParseBaseB.v's segE1_stmt .. segT_stmt, each proved in its own file) into lib/A/RtPgCSpec.v's
   rt_parse_specX B_PARSE B_KEY RtPgSatB.dcs_B.
   The two loops are closed here by well-founded induction on the bytes left: the find loop (L1) on
   x_len + 8 - r, each pass moving r forward by round_up8 (16 + value size) >= 16 and never past x_len + 7; the
   foreach loop (L2) on body + size + 8 - c, each pass moving c forward by round_up8 (8 + child size) >= 8 and
   never past body + size + 7. LB, K, FV and T are visited inside one foreach pass. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Spa Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0 RtPgParseBaseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgSatB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgParseEB RtPgParseFB RtPgParseLB RtPgParseLBB RtPgParseKB RtPgParseFVB RtPgParseTB.
Import ListNotations.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Section c.
Hypothesis SE1 : segE1_stmt B MT.
Hypothesis SE2 : segE2_stmt B MT.
Hypothesis SF : segF_stmt B MT.
Hypothesis SL : segL_stmt B MT.
Hypothesis SLB : segLB_stmt B MT.
Hypothesis SKV : segK_stmt B MT.
Hypothesis SFV : segFV_stmt B MT.
Hypothesis ST : segT_stmt B MT.

(* the foreach loop over the Struct of the property at r *)
Lemma L2_all : forall x, pre_ok B x -> forall r c ko, L2_ok B MT x r c ko.
Proof.
intros x Hpre r.
assert (IND : forall n c, (Z.to_nat (r + 16 + Spa.u32_at (x_bs x) (r + 8) + 8 - c) <= n)%nat ->
  forall ko, L2_ok B MT x r c ko).
{ induction n as [|n IH]; intros c Hc ko.
  - apply (SL x r c ko Hpre).
    + intros c' ko' Hc'. exfalso. lia.
    + apply (SLB x r c Hpre). intros c' ko' Hc'. exfalso. lia.
    + intros ck rv. apply (SKV x r c ck rv Hpre).
      * intros c' ko' Hc'. exfalso. lia.
      * intros v. apply (ST x v Hpre).
      * intros b. apply (SFV x b Hpre). intros v. apply (ST x v Hpre).
  - assert (Hs : forall c' ko', c < c' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> L2_ok B MT x r c' ko').
    { intros c' ko' Hc'. apply (IH c'). lia. }
    apply (SL x r c ko Hpre).
    + exact Hs.
    + apply (SLB x r c Hpre). exact Hs.
    + intros ck rv. apply (SKV x r c ck rv Hpre).
      * exact Hs.
      * intros v. apply (ST x v Hpre).
      * intros b. apply (SFV x b Hpre). intros v. apply (ST x v Hpre). }
intros c ko. exact (IND _ c (le_n _) ko).
Qed.

(* the find loop over the properties of the Props object *)
Lemma L1_all : forall x, pre_ok B x -> forall r, L1_ok B MT x r.
Proof.
intros x Hpre.
assert (IND : forall n r, (Z.to_nat (x_len x + 8 - r) <= n)%nat -> L1_ok B MT x r).
{ induction n as [|n IH]; intros r Hr.
  - apply (SF x r Hpre).
    + intros r' Hr'. exfalso. lia.
    + intros r0 c ko. apply (L2_all x Hpre).
  - apply (SF x r Hpre).
    + intros r' Hr'. apply (IH r'). lia.
    + intros r0 c ko. apply (L2_all x Hpre). }
intros r. apply (IND (Z.to_nat (x_len x + 8 - r)) r (le_n _)).
Qed.

Lemma parse_call : forall x null, call_ok B x null ->
SRr rsegs (x_W x) (cfg_at rsegs B_PARSE (x_regs x) (x_memc x) (x_mdc x)) (PPOST B MT x null).
Proof.
intros x null Hcall. apply (SE1 x null Hcall). intros Hn. subst null.
apply (SE2 x Hcall). apply (L1_all x Hcall).
Qed.

(* rt_parse_specX at image B, from the segment statements *)
Theorem rt_parse_B_of_segs : rt_parse_specX rsegs B MT B_PARSE B_KEY RtPgSatB.dcs_B.
Proof.
unfold rt_parse_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P Q bs
Hpre H10 H11 Hpod Hwc HQ0 HQ4 HQra Hkey Hdcs Hfrm.
set (x := PCtx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P Q bs).
exact (parse_call x null (conj Hpre (conj H10 (conj H11 (conj Hpod (conj Hwc (conj HQ0 (conj HQ4 (conj HQra
  (conj Hkey (conj Hdcs Hfrm))))))))))).
Qed.
End c.

(* the walk at image B: the eight segments, each proved in its own file *)
Section f.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = B_GOT_SH.
Hypothesis HCELL : as_shadow_cell B = B_SH_CELL.
Hypothesis STRCMP : astrcmp_realizes rsegs B B_STRCMP.
Theorem rt_parse_B : rt_parse_specX rsegs B MT B_PARSE B_KEY RtPgSatB.dcs_B.
Proof using MTL LAWS HGOT HCELL STRCMP.
apply rt_parse_B_of_segs.
- apply RtPgParseEB.segE1_ok; assumption.
- apply RtPgParseEB.segE2_ok; assumption.
- apply RtPgParseFB.segF_ok; assumption.
- apply RtPgParseLB.segL_ok; assumption.
- apply RtPgParseLBB.segLB_ok; assumption.
- apply RtPgParseKB.segK_ok; assumption.
- apply RtPgParseFVB.segFV_ok; assumption.
- apply RtPgParseTB.segT_ok; assumption.
Qed.
End f.
End b.

Print Assumptions rt_parse_B.
About rt_parse_B.

(* reac_role_prop_parse 0x82ef0 of reac-pw/fuzz_role's ASan image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb): the composition of the walk's segments
   (lib/A/RPgParseBase.v's segE1_stmt .. segT_stmt, each proved in its own file) into lib/A/RPgCSpec.v's
   rl_parse_specX A_PARSE A_KEY role_A_dcs.
   The two loops are closed here by well-founded induction on the bytes left: the find loop (L1) on
   x_len + 8 - r, each pass moving r forward by round_up8 (16 + value size) >= 16 and never past x_len + 7; the
   foreach loop (L2) on body + size + 8 - c, each pass moving c forward by round_up8 (8 + child size) >= 8 and
   never past body + size + 7. LB, K, FV and T are visited inside one foreach pass. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Spa Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgParseE RPgParseF RPgParseL RPgParseLB RPgParseK RPgParseFV RPgParseT.
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
SRr rsegs (x_W x) (cfg_at rsegs A_PARSE (x_regs x) (x_memc x) (x_mdc x)) (PPOST B MT x null).
Proof.
intros x null Hcall. apply (SE1 x null Hcall). intros Hn. subst null.
apply (SE2 x Hcall). apply (L1_all x Hcall).
Qed.

(* rl_parse_specX at image A, from the segment statements *)
Theorem rl_parse_A_of_segs : rl_parse_specX rsegs B MT A_PARSE A_KEY role_A_dcs.
Proof.
unfold rl_parse_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P Q bs
Hpre H10 H11 Hpod Hwc HQ4 HQra Hkey Hdcs Hfrm.
set (x := PCtx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P Q bs).
exact (parse_call x null (conj Hpre (conj H10 (conj H11 (conj Hpod (conj Hwc (conj HQ4 (conj HQra (conj Hkey (conj Hdcs Hfrm)))))))))).
Qed.
End c.

(* the walk at image A: the eight segments, each proved in its own file *)
Section f.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = A_GOT_SH.
Hypothesis HCELL : as_shadow_cell B = A_SH_CELL.
Hypothesis STRCMP : astrcmp_realizes rsegs B A_STRCMP.
Theorem rl_parse_A : rl_parse_specX rsegs B MT A_PARSE A_KEY role_A_dcs.
Proof using MTL LAWS HGOT HCELL STRCMP.
apply rl_parse_A_of_segs.
- apply RPgParseE.segE1_ok; assumption.
- apply RPgParseE.segE2_ok; assumption.
- apply RPgParseF.segF_ok; assumption.
- apply RPgParseL.segL_ok; assumption.
- apply RPgParseLB.segLB_ok; assumption.
- apply RPgParseK.segK_ok; assumption.
- apply RPgParseFV.segFV_ok; assumption.
- apply RPgParseT.segT_ok; assumption.
Qed.
End f.
End b.

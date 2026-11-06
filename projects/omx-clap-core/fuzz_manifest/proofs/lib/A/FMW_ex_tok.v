(* G4.ExTok: ex_seg_T (FMW_ex_base.v) from the five token sub-segments of FMW_ex_tok_base.v: the loop at TK_LH by strong
   induction on |text| - j (re-entry per iteration, as FMW_plain.v pl_loop). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
  FMW_ex_tok_t0 FMW_ex_tok_lh FMW_ex_tok_b FMW_ex_tok_e FMW_ex_tok_n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_base FMW_ex_tok_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma tk_glue : tk_seg_T0 B -> tk_seg_LH B -> tk_seg_B B -> tk_seg_E B -> tk_seg_N B -> ex_seg_R B -> ex_seg_T B.
Proof.
intros ST0 SLH SB SE SN SR.
intros cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 HLf HT.
set (p := mkTKP i d f name nl ns nl2 close).
assert (HLH : forall j, tk_k B cx TK_LH (tk_at_LH B cx p j)).
{ intros j. remember (length (cx_tb cx) - j)%nat as m eqn:Hm. revert j Hm.
  induction m as [m IH] using lt_wf_ind. intros j Hm.
  assert (HN : tk_k B cx TK_N (tk_at_N B cx p j)).
  { apply SN; [exact HLf|]. intros ly4 S4 W4 regs4 mem4 md4 H4.
    pose proof H4 as (_ & _ & _ & _ & Hb & _). unfold tk_bound in Hb.
    exact (IH (length (cx_tb cx) - S j)%nat ltac:(lia) (S j) eq_refl ly4 S4 W4 regs4 mem4 md4 H4). }
  assert (HE : tk_k B cx TK_E (tk_at_E B cx p j)) by (apply SE; [exact SR | exact HN]).
  apply SLH; [exact HN | exact HE | apply SB; [exact HN | exact HE]]. }
exact (ST0 cx i d f name nl ns nl2 close HLf (HLH 0%nat) ly3 S3 W3 regs3 mem3 md3 HT).
Qed.
End g.

(* ex_seg_T from the five sub-segments and G4's ex_seg_R *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis BCMP : abcmp_realizes tfibsegs B PC_bcmp.
Hypothesis SEG_R : ex_seg_R B.

Theorem ex_seg_T_holds : ex_seg_T B.
Proof.
  apply tk_glue.
  - exact (tk_seg_T0_holds B IMG STRLEN).
  - exact (tk_seg_LH_holds B BCMP).
  - exact (tk_seg_B_holds B).
  - exact (tk_seg_E_holds B).
  - exact (tk_seg_N_holds B).
  - exact SEG_R.
Qed.
End t.

Print Assumptions ex_seg_T_holds.

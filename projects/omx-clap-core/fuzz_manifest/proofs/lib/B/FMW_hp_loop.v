(* has_prefixed on fm.asan-ubsan (G2, image B): the loop. From the five segment statements of the kit
   (lib/B/FMW_hp_kit.v seg_*_ok, proved in FMW_hp_seg{H,N,P,Q,T}.v) and the loop invariant INV of FMW_hp_model.v
   (no token starts before the current occurrence), the walk from the loop head at every occurrence a reaches
   has_prefixed's post: fm's released plain proof lib/Prog/has_prefixed.v hp_loop :138, by induction on the text left. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g2rt FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SH : seg_head_ok B.
Hypothesis SN : seg_ncmp_ok B.
Hypothesis SP : seg_pre_ok B.
Hypothesis SQ : seg_post_ok B.
Hypothesis ST : seg_tail_ok B.

Lemma hp_loop : forall cx, hp_entry_ok B cx -> forall n a, (length (cx_tb cx) - a < n)%nat ->
  INV (cx_tb cx) (cx_pre cx) (cx_lb cx) a -> hp_cont B cx HP_HEAD a (fun _ => True).
Proof.
intros cx HE n. induction n as [|n IH]; intros a Hn Hinv; [lia|].
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & Hq & Hplen & Hqp & Htmax & _).
set (P := Z.to_nat (cx_plen cx)) in *.
set (Q := Z.to_nat (cx_q cx)) in *.
assert (HqP : (Q + P <= length (cx_tb cx))%nat) by lia.
assert (Hpre : cx_pre cx = firstn P (skipn Q (cx_tb cx))) by reflexivity.
assert (HP : length (cx_pre cx) = P) by (rewrite Hpre, length_firstn, length_skipn; lia).
(* the tail at a, once no token starts before a + 1 *)
assert (TAIL : INV (cx_tb cx) (cx_pre cx) (cx_lb cx) (S a) -> hp_cont B cx HP_TAIL a (fun _ => True)).
{ intros Hinv1. apply (ST cx a).
  - intros Hno. unfold hp_res. erewrite tok_none; [reflexivity | exact Hinv1 |].
    exact (noocc_mt (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP (S a) Hno).
  - intros j Hfo. apply IH.
    + destruct Hfo as ((Hl & _) & _). rewrite length_skipn in Hl.
      destruct (cx_lb cx) eqn:El; [contradiction|]. cbn [length] in Hl. lia.
    + exact (first_occ_inv (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP (S a) j Hinv1 Hfo). }
(* a tail reached with a reason C why no token starts at a - P - 1 *)
assert (TK : forall C : Prop,
  (C -> (a <= length (cx_tb cx))%nat -> (P + 1 <= a)%nat ->
     ManifestModel.token_at (cx_tb cx) (cx_pre cx) (cx_lb cx) (a - P - 1) = false) ->
  hp_cont B cx HP_TAIL a (fun _ => C)).
{ intros C HC lyc Sc W regs m mdc Hst Hc.
  pose proof Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
  pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hal.
  apply (TAIL (inv_step1 (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP a Hinv (HC Hc ltac:(lia))) lyc Sc W regs m mdc Hst I). }
apply (SH cx a).
- apply TK. intros [Hlt | Hne] _ HPa; [lia|]. exact (tok_colon (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP a HPa Hne).
- intros lyc Sc W regs m mdc Hst [HsB Hcol].
  pose proof HsB as (HPa & _).
  refine (SN cx a _ _ lyc Sc W regs m mdc Hst HsB).
  + apply TK. intros Hns Hal _.
    exact (tok_prefix (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP a Q Hpre HqP Hal HPa Hns).
  + intros lyc1 Sc1 W1 regs1 m1 mdc1 Hst1 [HsB1 Hstr].
    refine (SP cx a _ _ lyc1 Sc1 W1 regs1 m1 mdc1 Hst1 HsB1).
    * apply TK. intros (Hpos & Hb) _ _. exact (tok_before (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP a Hpos Hb).
    * intros lyc2 Sc2 W2 regs2 m2 mdc2 Hst2 HQ.
      pose proof Hst2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
      refine (SQ cx a _ _ lyc2 Sc2 W2 regs2 m2 mdc2 Hst2 I).
      -- intros Hnc. unfold hp_res.
         rewrite (tok_hit (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP a Q Hpre HqP HPa Hmt Hcol Hstr HQ Hnc).
         reflexivity.
      -- apply TK. intros Hnc _ _. exact (tok_after (cx_tb cx) (cx_pre cx) (cx_lb cx) P HP a HPa Hnc).
Qed.
End l.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YM05 YO0d YO0f YO09 YP09 YL0g YL0i YL01 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB StatementUbsan ManifestFF StatementUbsanCg.
Import ListNotations.
Local Open Scope Z_scope.

(* ManifestFF.v's frame lemmas for the agreement frame facts (StatementUbsanCg.frame_facts_cg). *)
Section FFcg.
Context {fx : FPState} {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z).
Hypothesis FF : frame_facts_cg B API LS SH SK ra empty.

Ltac ff_split := pose proof FF as FF'; unfold frame_facts_cg in FF';
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma ffc_guard_syms : guard_syms B.
Proof. ff_split. split; assumption. Qed.

Lemma ffc_malloc_syms_omx : malloc_syms_omx B.
Proof. ff_split. split; assumption. Qed.

Lemma ffc_errno_low : errno_low B.
Proof.
  ff_split. unfold errno_low.
  match goal with H : forall rc' : RunCeil, errno_addr B + 4 <= _ |- _ => apply H end.
Qed.

Lemma ffc_globals : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  ff_split.
  match goal with H : forall a, in_globals frame_G a -> in_img B a /\ _ |- _ => exact H end.
Qed.

Lemma ffc_statics_facts : statics_facts B.
Proof.
  intros a Ha. destruct (ffc_globals a (statics_in_frame_G a Ha)) as (H1 & H2 & H3 & _). tauto.
Qed.

Lemma ffc_statics_noerrno : statics_noerrno B.
Proof.
  intros a Ha. destruct (ffc_globals a (statics_in_frame_G a Ha)) as (_ & _ & _ & H4). exact H4.
Qed.

Lemma ffc_allocator : @frame_allocator rc fx B (API rc).
Proof.
  ff_split.
  match goal with H : forall (rc' : RunCeil) (fx' : FPState), @frame_allocator rc' fx' B (API rc') |- _ =>
    exact (H rc fx) end.
Qed.

Lemma ffc_statics_free : statics_free B (aa_MR (API rc)).
Proof.
  pose proof ffc_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  intros L A mem md a HM Ha.
  match goal with H : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a |- _ =>
    exact (H L A mem md a HM (statics_in_frame_G a Ha)) end.
Qed.

Lemma ffc_ctx_owned : ManifestB.ctx_owned B (aa_MR (API rc)).
Proof.
  pose proof ffc_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma ffc_alloc_extra : AllocExtra B (aa_MR (API rc)).
Proof.
  pose proof ffc_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma ffc_block_slack_present : block_slack_present B (API rc).
Proof.
  pose proof ffc_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

End FFcg.

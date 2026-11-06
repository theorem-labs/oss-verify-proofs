From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YM05 YO0d YO0f YO09 YP09 YL0g YL0i YL01 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB StatementUbsan.
Import ListNotations.
Local Open Scope Z_scope.

Lemma statics_in_frame_G : forall a, alloc_statics a -> in_globals frame_G a.
Proof.
  intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold in_globals, frame_G.
  destruct Ha as [H | [H | [H | H]]];
    first [ exists 0x2f620, 24; split; [right; left; reflexivity | lia]
          | exists 0x1f3a8, 8; split; [left; reflexivity | lia] ].
Qed.

Section FF.
Context {fx : FPState} {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z).
Hypothesis FF : frame_facts B API LS SH SK ra empty.

Ltac ff_split := pose proof FF as FF'; unfold frame_facts in FF';
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma ff_guard_syms : guard_syms B.
Proof. ff_split. split; assumption. Qed.

Lemma ff_malloc_syms_omx : malloc_syms_omx B.
Proof. ff_split. split; assumption. Qed.

Lemma ff_errno_low : errno_low B.
Proof.
  ff_split. unfold errno_low.
  match goal with H : forall rc' : RunCeil, errno_addr B + 4 <= _ |- _ => apply H end.
Qed.

Lemma ff_globals : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  ff_split.
  match goal with H : forall a, in_globals frame_G a -> in_img B a /\ _ |- _ => exact H end.
Qed.

Lemma ff_statics_facts : statics_facts B.
Proof.
  intros a Ha. destruct (ff_globals a (statics_in_frame_G a Ha)) as (H1 & H2 & H3 & _). tauto.
Qed.

Lemma ff_statics_noerrno : statics_noerrno B.
Proof.
  intros a Ha. destruct (ff_globals a (statics_in_frame_G a Ha)) as (_ & _ & _ & H4). exact H4.
Qed.

Lemma ff_allocator : @frame_allocator rc fx B (API rc).
Proof.
  ff_split.
  match goal with H : forall (rc' : RunCeil) (fx' : FPState), @frame_allocator rc' fx' B (API rc') |- _ =>
    exact (H rc fx) end.
Qed.

Lemma ff_statics_free : statics_free B (aa_MR (API rc)).
Proof.
  pose proof ff_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  intros L A mem md a HM Ha.
  match goal with H : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a |- _ =>
    exact (H L A mem md a HM (statics_in_frame_G a Ha)) end.
Qed.

Lemma ff_ctx_owned : ManifestB.ctx_owned B (aa_MR (API rc)).
Proof.
  pose proof ff_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma ff_alloc_extra : AllocExtra B (aa_MR (API rc)).
Proof.
  pose proof ff_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma ff_block_slack_present : block_slack_present B (API rc).
Proof.
  pose proof ff_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma ff_malloc : malloc_contract B (API rc).
Proof.
  pose proof ff_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma ff_free : free_contract B (API rc).
Proof.
  pose proof ff_allocator as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

End FF.

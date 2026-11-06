From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm RoAdapt.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma cj_keep : forall a, 0 <= a -> a < TASK_SIZE -> Mem.ro_addr segs (wa a) = false ->
  MemNorm.cj_drop segs (wa a) = false.
Proof.
  intros a H0 H1 H2. apply MemNorm.cj_drop_false_intro; [exact H2|]. right.
  unfold wa. rewrite unsigned_lit; [exact H1|]. unfold TASK_SIZE in *. lia.
Qed.

Lemma not_ro_keep : forall A n, 0 <= A -> A + n <= TASK_SIZE -> RoAdapt.not_ro segs A n ->
  forall i, 0 <= i < n -> MemNorm.cj_drop segs (wa (A + i)) = false.
Proof. intros A n H0 H1 Hn i Hi. apply cj_keep; [lia | lia | exact (Hn i Hi)]. Qed.

Lemma rw_cells_norm_cj : forall m A cs, MemNorm.ro_agree segs m -> A + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  RoAdapt.not_ro segs A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs ->
  rw_cells segs (MemNorm.normalize_cj segs m) A cs.
Proof.
  intros m A cs HR HB Hn [[Hwf Hb] Hw]. pose proof (MemNorm.mem_rel_cj_normalize segs m HR) as REL.
  split; [split; [exact Hwf|]|].
  - apply MemNorm.bytes_at_normalize_cj_low; [exact HR | | exact Hb].
    rewrite cells_bytes_length by exact Hwf. exact HB.
  - pose proof Hw as (W0 & W1 & W). eapply MemNorm.wr_at_norm_cj; [exact REL | exact Hw |].
    apply not_ro_keep; [exact W0 | exact HB | exact Hn].
Qed.

Lemma stk_norm_cj : forall m lo hi, MemNorm.ro_agree segs m -> hi <= TASK_SIZE -> RoAdapt.not_ro segs lo (hi - lo) ->
  stk segs m lo hi -> stk segs (MemNorm.normalize_cj segs m) lo hi.
Proof.
  intros m lo hi HR HB Hn (H1 & H2 & H). pose proof (MemNorm.mem_rel_cj_normalize segs m HR) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (K : MemNorm.cj_drop segs (wa a) = false).
  { apply cj_keep; [lia | lia |]. specialize (Hn (a - lo) ltac:(lia)). replace (lo + (a - lo)) with a in Hn by lia.
    exact Hn. }
  split.
  - rewrite (MemNorm.wview_rel_cj segs m _ _ REL K). exact Hv.
  - exists b. unfold mrd in *. rewrite (MemNorm.mem_rel_cj_keep segs m _ _ REL K). exact Hb.
Qed.

Lemma rw_cells_back_cj : forall m m0 A cs, MemNorm.mem_rel_cj segs m m0 -> rw_cells segs m0 A cs ->
  rw_cells segs m A cs.
Proof.
  intros m m0 A cs REL [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_rel_cj segs m m0 _ _ REL Hb).
  - exact (MemNorm.wr_at_rel_cj segs m m0 _ _ REL Hw).
Qed.

Lemma stk_back_cj : forall m m0 lo hi, MemNorm.mem_rel_cj segs m m0 -> stk segs m0 lo hi -> stk segs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (MemNorm.keep_of_wview_cj segs m m0 _ REL Hv) as K. split.
  - rewrite <- (MemNorm.wview_rel_cj segs m m0 _ REL K). exact Hv.
  - exists b. exact (MemNorm.mrd_rel_cj segs m m0 _ _ REL Hb).
Qed.

End WithSegs.

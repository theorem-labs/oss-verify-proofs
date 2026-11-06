From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm KindBGlue.
Import ListNotations.
Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x52000.
Definition nseg (a : Z) : Prop := a < IMG_LO \/ IMG_HI <= a.

Lemma rsegs_range : forallb (fun s => (IMG_LO <=? Z.of_N (seg_base s)) &&
  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_HI)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_seg : forall a s, find_segment rsegs a 1 = Some s -> IMG_LO <= a < IMG_HI.
Proof.
  intros a s H. destruct (KindBGlue.kb_find_segment rsegs a 1 s H) as (Hin & H1 & H2).
  pose proof rsegs_range as R. rewrite forallb_forall in R. specialize (R s Hin).
  apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2. lia.
Qed.

Lemma nseg_find : forall a, nseg a -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity].
  apply img_seg in E. unfold nseg in Ha. lia.
Qed.

Lemma wview_nseg : forall m x, nseg (bv_unsigned x) -> wview rsegs m x = m x.
Proof.
  intros m x H. unfold wview. destruct (m x); [reflexivity|]. rewrite (nseg_find _ H). reflexivity.
Qed.

Lemma mrd_nseg : forall m x, nseg (bv_unsigned x) -> mrd rsegs m x = m x.
Proof.
  intros m x H. unfold mrd. destruct (m x); [reflexivity|].
  apply MemNorm.seg_rom_unmapped. exact (nseg_find _ H).
Qed.

Lemma cj_keep_nseg : forall x, nseg (bv_unsigned x) -> bv_unsigned x < TASK_SIZE -> MemNorm.cj_drop rsegs x = false.
Proof.
  intros x H HT. apply MemNorm.cj_drop_false_intro.
  - unfold ro_addr. rewrite (nseg_find _ H). reflexivity.
  - right. exact HT.
Qed.

Lemma norm_nseg : forall mem m0 a, MemNorm.mem_rel_cj rsegs mem m0 -> 0 <= a < TASK_SIZE -> nseg a ->
  m0 (wa a) = mem (wa a).
Proof.
  intros mem m0 a HR Ha Hn. unfold TASK_SIZE in Ha.
  assert (Hu : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  apply (MemNorm.mem_rel_cj_keep rsegs mem m0). exact HR.
  apply cj_keep_nseg; rewrite Hu; [exact Hn | unfold TASK_SIZE; lia].
Qed.

Definition agree (m m' : word -> option byte) (A n : Z) : Prop :=
  forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i)).

Lemma bytes_at_agree : forall m m' A bs, bytes_at rsegs m A bs -> agree m m' A (Z.of_nat (length bs)) ->
  bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (H1 & H2 & H3) HG. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H3 i Hi). unfold mrd. rewrite (HG (Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma wr_at_agree : forall m m' A n, wr_at rsegs m A n -> agree m m' A n -> wr_at rsegs m' A n.
Proof.
  intros m m' A n (H1 & H2 & H3) HG. split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold wview. rewrite (HG i Hi). exact (H3 i Hi).
Qed.

Lemma rw_cells_agree : forall m m' A cs, rw_cells rsegs m A cs -> agree m m' A (Z.of_nat (cells_size cs)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[HW HB] HR] HG. split; [split; [exact HW|]|].
  - apply (bytes_at_agree m); [exact HB|]. rewrite (cells_bytes_length cs HW). exact HG.
  - exact (wr_at_agree m m' A _ HR HG).
Qed.

Lemma stk_agree : forall m m' lo hi, stk rsegs m lo hi -> agree m m' lo (hi - lo) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H3) HG. split; [exact H1|]. split; [exact H2|].
  intros a Ha. specialize (HG (a - lo) ltac:(lia)). replace (lo + (a - lo)) with a in HG by lia.
  unfold wview, mrd. rewrite HG. exact (H3 a Ha).
Qed.

Lemma agree_sub : forall m m' A n A' n', agree m m' A n -> A <= A' -> A' + n' <= A + n -> agree m m' A' n'.
Proof.
  intros m m' A n A' n' H H1 H2 i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

Lemma agree_sym : forall m m' A n, agree m m' A n -> agree m' m A n.
Proof. intros m m' A n H i Hi. symmetry. exact (H i Hi). Qed.

Lemma agree_trans : forall m1 m2 m3 A n, agree m1 m2 A n -> agree m2 m3 A n -> agree m1 m3 A n.
Proof. intros m1 m2 m3 A n H1 H2 i Hi. rewrite (H2 i Hi). exact (H1 i Hi). Qed.

Lemma agree_rel : forall mem m0 mem' m0' A n, MemNorm.mem_rel_cj rsegs mem m0 -> MemNorm.mem_rel_cj rsegs mem' m0' ->
  0 <= A -> A + n <= TASK_SIZE -> (forall a, A <= a < A + n -> nseg a) -> agree mem mem' A n -> agree m0 m0' A n.
Proof.
  intros mem m0 mem' m0' A n HR HR' HA HB Hn HG i Hi.
  rewrite (norm_nseg mem' m0' (A + i) HR') by (try apply Hn; lia).
  rewrite (norm_nseg mem m0 (A + i) HR) by (try apply Hn; lia).
  exact (HG i Hi).
Qed.

Lemma mem_inv_cj_rel : forall mem m0, MemNorm.mem_rel_cj rsegs mem m0 -> MemNorm.mem_inv_cj rsegs m0.
Proof.
  intros mem m0 [HR _] a b E. rewrite HR in E. exact (MemNorm.mem_inv_cj_normalize rsegs mem a b E).
Qed.

Lemma mem_inv_rel : forall mem m0, MemNorm.mem_rel_cj rsegs mem m0 -> mem_inv rsegs m0.
Proof. intros mem m0 H. exact (MemNorm.mem_inv_cj_inv rsegs m0 (mem_inv_cj_rel mem m0 H)). Qed.

Lemma task_mem_rel : forall mem m0, MemNorm.mem_rel_cj rsegs mem m0 -> MemNorm.task_mem rsegs m0.
Proof. intros mem m0 H. exact (MemNorm.mem_inv_cj_task rsegs m0 (mem_inv_cj_rel mem m0 H)). Qed.

Lemma nth_error_seq0 : forall k i, (i < k)%nat -> nth_error (seq 0 k) i = Some i.
Proof.
  intros k i H. rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact H).
  rewrite seq_nth by exact H. reflexivity.
Qed.

Lemma rwc_present : forall m A n, 0 <= A -> A + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> nseg (A + i) /\ m (wa (A + i)) <> None) ->
  exists bs, rw_cells rsegs m A [CB (Z.to_nat n) bs].
Proof.
  intros m A n HA HB Hn H.
  set (f := fun i : nat => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 (Z.to_nat n))).
  assert (L : length (map f (seq 0 (Z.to_nat n))) = Z.to_nat n) by (rewrite length_map, length_seq; reflexivity).
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact HA|]. rewrite L. split; [lia|].
    intros i Hi. rewrite nth_error_map, nth_error_seq0 by exact Hi. cbn [option_map].
    destruct (H (Z.of_nat i) ltac:(lia)) as [Hs Hp].
    rewrite mrd_nseg by (rewrite wa_unsigned by lia; exact Hs). unfold f.
    destruct (m (wa (A + Z.of_nat i))); [reflexivity | contradiction].
  - cbn [cells_size csize]. split; [exact HA|]. split; [lia|].
    intros i Hi. destruct (H i ltac:(lia)) as [Hs Hp].
    rewrite wview_nseg by (rewrite wa_unsigned by lia; exact Hs). exact Hp.
Qed.

(* Side-stack (FakeStack) preservation helper for the fuzz_ctrl LLVMFuzzerTestOneInput slot proof (asan-ubsan, image B).

   The segment lemmas of the slot wrappers' side-stack arm do a store (a `munch W mem mem'`) whose write set W
   stays clear of the FakeStack's metadata: the header word at FS + 88, the needs_gc byte at FS + 96, the per-class
   hint words (a_fs_hint) and the per-frame flag bytes (a_fs_flag). a_fs_ok_pres transports a_fs_ok across such a
   write: the metadata bytes are unchanged (munch outside W), and the whole [FS, FS + FS_SIZE) region stays present
   and writable (the store's presence/writability monotonicity). Its conclusion `a_fs_ok mem' FS` is exactly the
   third hypothesis of a Theorem Labs lane round 16's AC.a_laws_fs_store (Contract.v:1038), so a_fs_ok_store_AH composes the two
   to give AH, and a_fs_frame_write_AH specialises that to a frame-variable write.

   a_fs_frame_write_meta_disjoint specialises the metadata-disjointness to a frame-variable write: a store confined
   to a single fake frame [a_fs_frame FS c j, a_fs_frame FS c j + a_fs_B c) misses the metadata, because the frames
   start at FS + 36864, above every metadata cell. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT MemNorm KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract.
Import ListNotations.
Local Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.

(* Every valid class-c flag byte lives in [FS + 4096, FS + 36864): a_fs_flag FS c j = FS + 4096 + 2^15 -
   2^(15-c) + j with 0 <= j < a_fs_M c = 2^(14-c). *)
Lemma a_fs_flag_range : forall FS c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
  FS <= AC.a_fs_flag FS c j < FS + 36864.
Proof.
  intros FS c j Hc Hj.
  unfold AC.a_fs_flag, AC.a_fs_M in *.
  assert (He : 0 <= Z.of_nat c <= 10) by lia.
  assert (P2 : 2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (P3 : 0 < 2 ^ (14 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c)).
  { replace (15 - Z.of_nat c) with (Z.succ (14 - Z.of_nat c)) by lia.
    rewrite Z.pow_succ_r by lia. reflexivity. }
  change (2 ^ 15) with 32768 in *.
  lia.
Qed.

(* The FakeStack's metadata region: the header word at FS + 88, the needs_gc byte at FS + 96, the class hint words
   and the frame flag bytes. A write clear of these cells keeps a_fs_ok. *)
Definition fs_meta (FS q : Z) : Prop :=
  (FS + 88 <= q < FS + 96) \/
  q = FS + 96 \/
  (exists c, (c <= 10)%nat /\ AC.a_fs_hint FS c <= q < AC.a_fs_hint FS c + 8) \/
  (exists c j, (c <= 10)%nat /\ 0 <= j < AC.a_fs_M c /\ q = AC.a_fs_flag FS c j).

(* The whole metadata region sits below FS + 36864 (where the frames begin). *)
Lemma fs_meta_below : forall FS q, fs_meta FS q -> q < FS + 36864.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. assert (Z.of_nat c <= 10) by lia. lia.
  - subst q. exact (proj2 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* a_fs_ok is preserved by a write (munch W) whose footprint W misses the metadata cells, as long as the write
   keeps the FakeStack region present and writable (the store's monotonicity, as in AC.a_laws_fs_store). *)
Lemma a_fs_ok_pres :
  forall (W : list Frame.ivl) (mem mem' : word -> option byte) (FS : Z),
  AC.a_fs_ok mem FS ->
  Frame.munch W mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q) ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> (exists b, mbyte rsegs mem' q = Some b)) ->
  (forall q, fs_meta FS q -> Frame.outside W q) ->
  0 <= FS ->
  FS + AC.FS_SIZE <= 2 ^ 64 ->
  AC.a_fs_ok mem' FS.
Proof.
  intros W mem mem' FS Hok Hmunch Hwmono Hpres Hmeta HFS0 Hfsz.
  assert (HSZv : AC.FS_SIZE = 11571200) by reflexivity.
  unfold AC.a_fs_ok in Hok |- *.
  destruct Hok as (P1 & P2 & P3 & P4 & P5).
  split.
  { (* presence + writability over the whole FakeStack region *)
    intros q Hq. destruct (P1 q Hq) as (Hw & Hpa). split.
    - apply (Hwmono q); [lia | exact Hw].
    - apply (Hpres q); [lia | exact Hpa]. }
  split.
  { (* header word at FS + 88 *)
    unfold word_mem. intros k Hk.
    assert (Hk8 : Z.of_nat k < 8) by lia.
    assert (Hb2 : 0 <= FS + 88 + Z.of_nat k < 2 ^ 64) by lia.
    assert (Ho2 : Frame.outside W (FS + 88 + Z.of_nat k)).
    { apply Hmeta. unfold fs_meta. left. lia. }
    rewrite (KindBGlue.mbyte_munch rsegs W mem mem' (FS + 88 + Z.of_nat k) Hmunch Hb2 Ho2).
    exact (P2 k Hk). }
  split.
  { (* needs_gc byte at FS + 96 *)
    assert (Hb3 : 0 <= FS + 96 < 2 ^ 64) by lia.
    assert (Ho3 : Frame.outside W (FS + 96)).
    { apply Hmeta. unfold fs_meta. right. left. reflexivity. }
    rewrite (KindBGlue.mbyte_munch rsegs W mem mem' (FS + 96) Hmunch Hb3 Ho3).
    exact P3. }
  split.
  { (* class hint words *)
    intros c Hc. destruct (P4 c Hc) as [h Hh].
    exists h. unfold word_mem. intros k Hk.
    assert (Hk8 : Z.of_nat k < 8) by lia.
    assert (Hc10 : Z.of_nat c <= 10) by lia.
    assert (Hb4 : 0 <= AC.a_fs_hint FS c + Z.of_nat k < 2 ^ 64).
    { unfold AC.a_fs_hint. lia. }
    assert (Ho4 : Frame.outside W (AC.a_fs_hint FS c + Z.of_nat k)).
    { apply Hmeta. unfold fs_meta. right. right. left. exists c. split; [exact Hc | lia]. }
    rewrite (KindBGlue.mbyte_munch rsegs W mem mem' (AC.a_fs_hint FS c + Z.of_nat k) Hmunch Hb4 Ho4).
    exact (Hh k Hk). }
  { (* frame flag bytes *)
    intros c j Hc Hj.
    pose proof (a_fs_flag_range FS c j Hc Hj) as Hfr.
    assert (Hb5 : 0 <= AC.a_fs_flag FS c j < 2 ^ 64) by lia.
    assert (Ho5 : Frame.outside W (AC.a_fs_flag FS c j)).
    { apply Hmeta. unfold fs_meta. right. right. right. exists c, j.
      split; [exact Hc | split; [exact Hj | reflexivity]]. }
    rewrite (KindBGlue.mbyte_munch rsegs W mem mem' (AC.a_fs_flag FS c j) Hmunch Hb5 Ho5).
    exact (P5 c j Hc Hj). }
Qed.

(* The frames begin at FS + 36864 (a Theorem Labs lane fs_frame): a_fs_frame FS c j = FS + 36864 + c*2^20 + j*a_fs_B c. *)
Lemma a_fs_frame_above : forall FS c j, (c <= 10)%nat -> 0 <= j -> FS + 36864 <= AC.a_fs_frame FS c j.
Proof.
  intros FS c j Hc Hj.
  unfold AC.a_fs_frame, AC.a_fs_B.
  assert (H1 : 0 <= Z.of_nat c * 2 ^ 20).
  { apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]. }
  assert (H2 : 0 < 2 ^ Z.of_nat c) by (apply Z.pow_pos_nonneg; lia).
  assert (H3 : 0 <= j * (64 * 2 ^ Z.of_nat c)).
  { apply Z.mul_nonneg_nonneg; [lia | lia]. }
  lia.
Qed.

(* A frame-variable write whose footprint W stays inside one fake frame misses the metadata, so a_fs_ok_pres
   applies: the frame lies above FS + 36864 and every metadata cell lies below it. *)
Lemma a_fs_frame_write_meta_disjoint : forall FS c j (W : list Frame.ivl),
  (c <= 10)%nat -> 0 <= j ->
  Frame.sub_fp W [(AC.a_fs_frame FS c j, AC.a_fs_frame FS c j + AC.a_fs_B c)] ->
  forall q, fs_meta FS q -> Frame.outside W q.
Proof.
  intros FS c j W Hc Hj Hsub q Hm.
  apply Hsub. cbn. split; [| exact I]. intros [Hlo Hhi].
  pose proof (fs_meta_below FS q Hm) as Hb.
  pose proof (a_fs_frame_above FS c j Hc Hj) as Ha.
  lia.
Qed.

(* The FakeStack base word at tp witnesses a_in_fs for every address in [FS, FS + FS_SIZE). Round 21 added the
   base's range to AC.a_in_fs, so the base's range is a premise. *)
Section FsBase.
Variable B : AC.asan_syms.
Lemma a_fs_in : forall mem FS q,
  word_mem rsegs mem (AC.as_tp B) FS -> 0 <= FS < 2 ^ 64 -> FS <= q < FS + AC.FS_SIZE -> AC.a_in_fs B mem q.
Proof.
  intros mem FS q Hw Hr Hq. unfold AC.a_in_fs. exists FS. split; [exact Hr | split; [exact Hw | exact Hq]].
Qed.
End FsBase.

(* Composition with a Theorem Labs lane round 16's AC.a_laws_fs_store (Contract.v:1038): a metadata-disjoint store whose other
   touched cells lie in the a_store_ok set, the FakeStack region, or its shadow keeps the heap invariant AH. *)
Section Compose.
Variable B : AC.asan_syms.
Variable AH : list (Z * Z) -> (word -> option byte) -> Model -> Prop.
Variable rt_owned : list (Z * Z) -> (word -> option byte) -> Model -> Z -> Prop.
Variable stklo stkhi : (word -> option byte) -> Model -> Z.

Lemma a_fs_ok_store_AH :
  forall (W : list Frame.ivl) (H : list (Z * Z)) (mem mem' : word -> option byte) (md : Model) (FS : Z),
  AC.a_laws B AH rt_owned stklo stkhi ->
  AH H mem md ->
  word_mem rsegs mem (AC.as_tp B) FS ->
  0 <= FS < 2 ^ 64 ->
  FS + AC.FS_SIZE <= 2 ^ 64 ->
  Frame.munch W mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q) ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> (exists b, mbyte rsegs mem' q = Some b)) ->
  (forall q, fs_meta FS q -> Frame.outside W q) ->
  (forall q, 0 <= q < 2 ^ 64 -> ~ AC.a_store_ok H (stklo mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) -> mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)) ->
  AH H mem' md /\ (forall q, rt_owned H mem' md q <-> rt_owned H mem md q)
    /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md.
Proof.
  intros W H mem mem' md FS Hlaws Hah Hwtp Hfs Hfsz Hmunch Hwmono Hpres Hmeta Hagree.
  assert (Hok : AC.a_fs_ok mem FS)
    by (decompose [and ex] (AC.a_laws_fs_state B AH rt_owned stklo stkhi Hlaws H mem md FS Hah Hwtp Hfs); assumption).
  pose proof (a_fs_ok_pres W mem mem' FS Hok Hmunch Hwmono Hpres Hmeta (proj1 Hfs) Hfsz) as Hok'.
  exact (AC.a_laws_fs_store B AH rt_owned stklo stkhi Hlaws H mem mem' md FS Hah Hwtp Hfs Hagree Hwmono Hok').
Qed.

(* The frame-variable write: a store confined to one fake frame [a_fs_frame FS c j, + a_fs_B c) keeps AH. The
   frame lies in [FS + 36864, FS + FS_SIZE), so it both misses the metadata and never touches a cell outside the
   FakeStack region, discharging both hypotheses of a_fs_ok_store_AH. *)
Lemma a_fs_frame_write_AH :
  forall (W : list Frame.ivl) (H : list (Z * Z)) (mem mem' : word -> option byte) (md : Model) (FS : Z)
         (c : nat) (j : Z),
  AC.a_laws B AH rt_owned stklo stkhi ->
  AH H mem md ->
  word_mem rsegs mem (AC.as_tp B) FS ->
  0 <= FS < 2 ^ 64 ->
  FS + AC.FS_SIZE <= 2 ^ 64 ->
  (c <= 10)%nat -> 0 <= j ->
  AC.a_fs_frame FS c j + AC.a_fs_B c <= FS + AC.FS_SIZE ->
  Frame.munch W mem mem' ->
  Frame.sub_fp W [(AC.a_fs_frame FS c j, AC.a_fs_frame FS c j + AC.a_fs_B c)] ->
  (forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q) ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> (exists b, mbyte rsegs mem' q = Some b)) ->
  AH H mem' md /\ (forall q, rt_owned H mem' md q <-> rt_owned H mem md q)
    /\ stklo mem' md = stklo mem md /\ stkhi mem' md = stkhi mem md.
Proof.
  intros W H mem mem' md FS c j Hlaws Hah Hwtp Hfs Hfsz Hc Hj Hhi Hmunch Hsub Hwmono Hpres.
  apply (a_fs_ok_store_AH W H mem mem' md FS Hlaws Hah Hwtp Hfs Hfsz Hmunch Hwmono Hpres).
  - exact (a_fs_frame_write_meta_disjoint FS c j W Hc Hj Hsub).
  - intros q Hq Hns Hnr Hnsh.
    apply Hmunch. rewrite MState.unsigned_lit by exact Hq.
    apply Hsub. cbn. split; [| exact I]. intros [Hq1 Hq2].
    pose proof (a_fs_frame_above FS c j Hc Hj) as Hlo.
    lia.
Qed.
End Compose.

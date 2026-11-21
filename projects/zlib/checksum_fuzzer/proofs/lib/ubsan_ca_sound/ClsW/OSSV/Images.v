(** * OSSVerify.Core.Images: well-formed images

    The three computable checks lps asks every consumer to make about an
    image before quantifying over its valid entries
    ([Equivalence.image_entry_fetchable], [Equivalence.image_phdrs_readable],
    [Equivalence.image_brk_satisfiable]; lps states them as the module type
    [Equivalence.IMAGE_WF]).  Without them, an image malformed enough to have
    no valid entry, or to fault on its first instruction, would satisfy every
    "on every run" statement for no reason.

    Every harness's [Images.v] proves [image_wf] of each of its images with
    [check_image_wf], which decides it by computation. *)

From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.

(** The image's entry point holds a fetchable instruction, its program-header
    table lies inside one readable loaded segment, and there is room above
    its segments for a program break. *)
Definition image_wf (i : Image) : Prop :=
  match i with
  | mkImage segs pc ph =>
      image_entry_fetchable segs pc = true
      /\ image_phdrs_readable segs ph = true
      /\ image_brk_satisfiable segs = true
  end.

(** The same three checks as one boolean. *)
Definition image_wf_b (i : Image) : bool :=
  match i with
  | mkImage segs pc ph =>
      image_entry_fetchable segs pc && image_phdrs_readable segs ph
      && image_brk_satisfiable segs
  end.

Lemma image_wf_b_sound : forall i, image_wf_b i = true -> image_wf i.
Proof.
  intros [segs pc ph] H. cbn [image_wf_b image_wf] in *.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  exact (conj H1 (conj H2 H3)).
Qed.

Lemma image_wf_b_complete : forall i, image_wf i -> image_wf_b i = true.
Proof.
  intros [segs pc ph] (H1 & H2 & H3). cbn [image_wf_b].
  rewrite H1, H2, H3. reflexivity.
Qed.

(** [image_wf] of a module snapshot is exactly lps's [IMAGE_WF] obligations
    for that module. *)
Lemma image_wf_of_memimage : forall (segs : list Segment) pc ph,
  image_wf (mkImage segs pc ph)
  <-> (image_entry_fetchable segs pc = true
       /\ image_phdrs_readable segs ph = true
       /\ image_brk_satisfiable segs = true).
Proof. intros. reflexivity. Qed.

(** Proves [image_wf i] for a concrete image [i] by computation.  It fails,
    rather than proving anything, on an image that is not well formed. *)
Ltac check_image_wf := apply image_wf_b_sound; vm_compute; reflexivity.

(** The check bites: the image with no segments is not well formed, at any
    entry point. *)
Lemma image_wf_nil : forall pc ph, ~ image_wf (mkImage nil pc ph).
Proof.
  intros pc ph (H & _ & _). rewrite image_entry_fetchable_nil in H. discriminate.
Qed.

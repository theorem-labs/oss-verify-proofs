(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: the measured vDSO image (RVDSO_IMAGE, its size, pages and clock_gettime offset, and the claim rvdso_ok) as musl's __vdsosym reads it, now that the run's auxv publishes AT_SYSINFO_EHDR as its first pair. *)

(* Require set mirrors Lib/Mem.v's, plus [Vdso] for the image record.  Coq
   loads a required file's own requirements but does not IMPORT them, so
   requiring [Mem] alone would leave [seg_rom], [ov_read_bytes], [Segment]
   and [byte] unqualified-unavailable here even though [Mem] uses them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The image is a CONSTANT, not a function of the kernel build.        *)
(* ------------------------------------------------------------------ *)

(* Vdso.v:279 lists exactly one measured image.  Stated as a lemma rather
   than carried in a comment so the kernel rechecks it at every LPS bump:
   if a second image is ever measured, [vdso_image_of_const] below stops
   compiling and every use of [RVDSO_IMAGE] has to be revisited. *)
Lemma length_vdso_images : length vdso_images = 1%nat.
Proof. reflexivity. Qed.

Definition RVDSO_IMAGE : VdsoImage := nth 0 vdso_images vdso_image_default.

(* State.v:3784 [vdso_image_of kb = nth (kb_vdso kb mod length vdso_images) ...].
   With one image the modulus is 0 whatever the kernel build is, so no
   [KernelBuild] parameter enters any claim below. *)
Lemma vdso_image_of_const : forall kb, vdso_image_of kb = RVDSO_IMAGE.
Proof.
  intros kb. unfold vdso_image_of, RVDSO_IMAGE.
  rewrite length_vdso_images, Nat.mod_1_r. reflexivity.
Qed.

Definition RVDSO_SIZE : Z := Z.of_N (vi_size RVDSO_IMAGE).
Definition RVDSO_PAGES : Z := Z.of_N (vi_pages RVDSO_IMAGE).
Definition RVDSO_SPAN : Z := RVDSO_PAGES * 4096.

Lemma RVDSO_SIZE_val : RVDSO_SIZE = 5704. Proof. reflexivity. Qed.
Lemma RVDSO_PAGES_val : RVDSO_PAGES = 2. Proof. reflexivity. Qed.
Lemma RVDSO_SPAN_val : RVDSO_SPAN = 8192. Proof. reflexivity. Qed.
(* NEVER [cbv] on anything that mentions RVDSO_IMAGE: it reduces [nth 0
   vdso_images] to the record and normalizes [vi_bytes]' twelve PrimString
   chunks, which is the 59-minute shape Run.v:310-321 records.  The _val
   lemmas above are safe because projecting one field of a constructor is an
   iota step that never forces its siblings. *)
Lemma RVDSO_SIZE_span : 0 < RVDSO_SIZE <= RVDSO_SPAN.
Proof. rewrite RVDSO_SIZE_val, RVDSO_SPAN_val. lia. Qed.

(* ------------------------------------------------------------------ *)
(* What the lookup answers.                                            *)
(* ------------------------------------------------------------------ *)

(* The offset of [__vdso_clock_gettime] in the measured image.  This is the
   value musl's __vdsosym returns for (VDSO_CGT_VER, VDSO_CGT_SYM) on
   riscv64, and it is also the offset at which the MODEL places that entry
   ([Run.v:687] [vdso_entry_fn]), so the two agree by computation rather
   than by a reader's assertion.  That agreement is what keeps the restated
   [vdsosym_post] from being a lemma about a number nobody else uses. *)
Definition RVDSO_CGT_OFF : Z := 1460.

Lemma rvdso_cgt_off_measured :
  vdso_sym_off (vi_syms RVDSO_IMAGE) VdsoClockGettime = Some (Z.to_N RVDSO_CGT_OFF).
Proof. reflexivity. Qed.

Lemma rvdso_cgt_off_entry :
  vdso_fn_at_off (vi_syms RVDSO_IMAGE) (Z.to_N RVDSO_CGT_OFF) = Some VdsoClockGettime.
Proof. reflexivity. Qed.

(* The same hazard as RVDSO_SIZE_span above, and I left this one in: a `cbv`
   here unfolds RVDSO_SIZE through RVDSO_IMAGE to `nth 0 vdso_images` and
   normalizes the whole record, vi_bytes included.  Measured, not guessed --
   a farm build died here with
     VdsoImg.v, line 79, characters 19-31: Tactic failure: No applicable tactic.
   characters 19-31 being the `discriminate` that `cbv` had left nothing
   usable for.  Rewriting with the _val lemmas never reaches the chunks. *)
Lemma rvdso_cgt_off_range : 0 < RVDSO_CGT_OFF < RVDSO_SIZE.
Proof. unfold RVDSO_CGT_OFF. rewrite RVDSO_SIZE_val. lia. Qed.

(* ------------------------------------------------------------------ *)
(* The image's bytes, as a reader and as a list.                       *)
(* ------------------------------------------------------------------ *)

(* LPS's own image reader (Checks/Cases/Kernel/VdsoSym.v:422), inlined.  That
   file is LPS's EVIDENCE for what a libc finds, not part of its trusted
   specification, so it is not required here; the few lines it would supply
   are cheaper to carry than the dependency.

   ONE DELIBERATE DIFFERENCE from [image_peek], and it is the direction that
   costs nothing: the BYTE function is primary and TOTAL, and the reader is
   derived from it.  [image_peek] returns [segment_byte_at] directly, so it
   can in principle answer [None] at an offset inside [vi_size] if the chunk
   list were short of its declared size.  It is not -- the twelve chunks
   total exactly 5704 -- but proving that would be a fact about the chunks,
   and every consumer of this file only ever needs "inside the image, the
   reader answers [Some] of the byte at that offset".  Taking the byte as
   primary makes that true by construction and keeps [rvdso_peek_in] a one
   liner instead of an induction over PrimString chunks. *)
Definition rvdso_byte (o : Z) : byte :=
  match segment_byte_at (vi_bytes RVDSO_IMAGE) (Z.to_N o) with
  | Some b => b
  | None => Z_to_bv 8 0
  end.

Definition rvdso_peek (o : Z) : option byte :=
  if ((0 <=? o) && (o <? RVDSO_SIZE))%bool then Some (rvdso_byte o) else None.

Lemma rvdso_peek_in : forall o, 0 <= o < RVDSO_SIZE -> rvdso_peek o = Some (rvdso_byte o).
Proof.
  intros o [H0 H1]. unfold rvdso_peek.
  replace ((0 <=? o) && (o <? RVDSO_SIZE))%bool with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

(* A FOLDED list, never a literal one.  [vi_bytes] is 5704 bytes in twelve
   [PrimString] chunks, and Run.v:310-321 records one LPS fixture taking 59
   MINUTES because a [vm_compute] reached them.  Written as a fixpoint over
   offsets, the list stays one symbol in every goal that does not ask for a
   byte, and a read site forces only the prefix it names. *)
Fixpoint rvdso_byte_list (o : Z) (n : nat) : list byte :=
  match n with
  | O => []
  | S n' => rvdso_byte o :: rvdso_byte_list (o + 1) n'
  end.

Lemma length_rvdso_byte_list : forall n o, length (rvdso_byte_list o n) = n.
Proof. induction n as [|n IH]; intros o; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma nth_error_rvdso_byte_list : forall n o i,
  (i < n)%nat -> nth_error (rvdso_byte_list o n) i = Some (rvdso_byte (o + Z.of_nat i)).
Proof.
  induction n as [|n IH]; intros o i Hi; [lia|].
  destruct i as [|i]; cbn [rvdso_byte_list nth_error].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Definition rvdso_bytes : list byte := rvdso_byte_list 0 (Z.to_nat RVDSO_SIZE).

Lemma length_rvdso_bytes : length rvdso_bytes = Z.to_nat RVDSO_SIZE.
Proof. unfold rvdso_bytes. apply length_rvdso_byte_list. Qed.

Lemma nth_error_rvdso_bytes : forall i,
  (i < Z.to_nat RVDSO_SIZE)%nat -> nth_error rvdso_bytes i = Some (rvdso_byte (Z.of_nat i)).
Proof.
  intros i Hi. unfold rvdso_bytes. rewrite nth_error_rvdso_byte_list by exact Hi.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The claim: the image is mapped at the base the auxv published.      *)
(* ------------------------------------------------------------------ *)

Section WithSegs.
Variable segs : list Segment.

(* [vb] is AT_SYSINFO_EHDR, auxv pair 0 at this revision.

   WHICH HALF OF [mrd] SUPPLIES THE BYTES.  [Mem.v:57]
   [mrd segs m a := match m a with Some b => Some b | None => seg_rom segs a end],
   so a walk's load at [vb] is served either by the overlay [m] or by the
   segment list's rom.  It is NOT [m]: Run.v:290-305 puts the image in a
   SEGMENT ([seg_bytes := vi_bytes im], ["r--"], [SegVdsoText]), loads go
   through [ov_read_bytes] which is overlay-FIRST with a segment fallback,
   and nothing in the entry chain ever writes 5704 bytes at [vb].  An
   earlier draft of this file asserted [bytes_at segs m vb rvdso_bytes] as
   a claim to be produced; that is not merely expensive, it is NOT
   DERIVABLE, and no producer could have discharged it.

   So the claim is about the SEGMENT LIST, and [rvdso_rom] below says only
   things about [segs].  Two consequences worth the restatement:
     - it is invariant under every memory step, so it needs no [munch] /
       [wmono] transport and no framing obligation at any call site;
     - [bytes_at] follows from it together with [mem_inv], which every post
       in this tree already carries.
   The list that satisfies it is the run's ([Run.v:325-330 run_segments]),
   not the binary's own ([Ref/RSegs.v:26]); lifting a walk from one to the
   other is what RomStable already does for every other walk here. *)
Definition rvdso_rom (vb : Z) : Prop :=
  0 <= vb /\ vb mod 4096 = 0 /\ vb + RVDSO_SPAN <= 2^47
  /\ forall o : Z, 0 <= o < RVDSO_SIZE ->
       seg_rom segs (wa (vb + o)) = rvdso_peek o
       /\ ro_addr segs (wa (vb + o)) = true.

Definition rvdso_ok (m : word -> option byte) (vb : Z) : Prop :=
  bytes_at segs m vb rvdso_bytes
  /\ 0 <= vb /\ vb mod 4096 = 0 /\ vb + RVDSO_SPAN <= 2^47.

(* The image is read-only, so the overlay cannot hold any of it: [mem_inv]
   says [m] is defined only where [ro_addr] is false, and [ro_addr] is true
   across the whole window.  Hence [mrd] falls through to the rom at every
   offset, which is exactly [bytes_at]. *)
Lemma rvdso_ok_of_rom : forall m vb,
  rvdso_rom vb -> mem_inv segs m -> rvdso_ok m vb.
Proof.
  intros m vb (V0 & VA & VH & ROM) MI.
  pose proof RVDSO_SIZE_span as [S0 S1].
  split; [| split; [exact V0| split; [exact VA| exact VH]]].
  split; [exact V0|]. split; [rewrite length_rvdso_bytes, Z2Nat.id by lia; lia|].
  intros i Hi. rewrite length_rvdso_bytes in Hi.
  assert (Ho : 0 <= Z.of_nat i < RVDSO_SIZE) by lia.
  destruct (ROM (Z.of_nat i) Ho) as [RB RO].
  unfold mrd. destruct (m (wa (vb + Z.of_nat i))) as [b|] eqn:EM.
  - exfalso. rewrite (MI _ _ EM) in RO. discriminate RO.
  - rewrite RB, (rvdso_peek_in _ Ho), nth_error_rvdso_bytes by lia. reflexivity.
Qed.

Lemma rvdso_ok_bytes : forall m vb, rvdso_ok m vb -> bytes_at segs m vb rvdso_bytes.
Proof. intros m vb (H & _). exact H. Qed.

Lemma rvdso_ok_range : forall m vb,
  rvdso_ok m vb -> 0 <= vb /\ vb + RVDSO_SPAN <= 2^47.
Proof. intros m vb (_ & H0 & _ & H2). split; [exact H0| exact H2]. Qed.

(* A read of [n] bytes at image offset [o].  The [bs] a caller supplies is
   closed by [vm_compute; reflexivity], and forcing it reaches only the
   bytes between [o] and [o + n]. *)
Lemma rvdso_read : forall m vb o n bs,
  rvdso_ok m vb ->
  0 <= o -> (Z.to_nat o + n <= Z.to_nat RVDSO_SIZE)%nat ->
  bs = firstn n (skipn (Z.to_nat o) rvdso_bytes) ->
  ov_read_bytes segs m (wa (vb + o)) n = Some bs.
Proof.
  intros m vb o n bs ROK Ho Hn ->.
  pose proof (bytes_at_ov_read segs m vb rvdso_bytes (Z.to_nat o) n
                (rvdso_ok_bytes m vb ROK)) as K.
  rewrite length_rvdso_bytes in K. specialize (K Hn).
  (* Normalise K's index BEFORE using it.  [bytes_at_ov_read] states its
     address as [wa (a + Z.of_nat k)] with [k := Z.to_nat o], and the goal
     says [wa (vb + o)]; [Z.of_nat (Z.to_nat o)] is not syntactically [o],
     so rewriting with K first fails to find its own left-hand side.  That
     is what a farm build reported at :235 --
       Found no subterm matching
       "ov_read_bytes segs m (wa (vb + Z.of_nat (Z.to_nat o))) n". *)
  rewrite Z2Nat.id in K by exact Ho. exact K.
Qed.

(* NO FRAME LEMMA, DELIBERATELY.  An earlier draft carried an
   [rvdso_ok_frame] transporting the claim across a [munch], with a window
   clause every caller had to discharge -- 34 call sites of
   [rauxv_ok_frame] across 20 files would have inherited it.  Restating the
   claim over the ROM removes the obligation rather than threading it:
   [rvdso_rom] mentions no memory, so it survives every step for free, and
   [rvdso_ok_of_rom] re-derives the [bytes_at] form at any point from the
   [mem_inv] that every post here already carries.  Keeping the transport
   lemma as well would invite a caller to take on a window condition that
   no longer exists. *)

End WithSegs.

Arguments rvdso_ok segs m vb : simpl never.

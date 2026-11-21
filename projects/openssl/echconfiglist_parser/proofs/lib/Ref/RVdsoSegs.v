(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the segment list the __vdsosym walk runs against (the binary's segments
   followed by the vDSO pair), and the fetch and read facts that carry over to it. *)

(* At LPS 727298f3 the auxv publishes AT_SYSINFO_EHDR as pair 0, so musl's __vdsosym reads
   the vDSO ELF by ordinary loads.  Those bytes are served only by the run's segment list
   ([Run.run_segments] appends [Run.vdso_segments], two "r--" segments), so the walk runs
   against [VW_BSEGS ++ tail] with the vDSO pair [tail] kept abstract behind its two
   permission facts ([VdsoSegs.vdso_segments_nx], [VdsoSegs.vdso_segments_nw]).  Fetch over
   that list is fetch over the binary's own list ([RomStable.fetch_word_app_nx], an
   equality), and a read the binary's list serves is served the same way
   ([RomStable.ov_read_bytes_app_nx]). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec Frame VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RVdsoAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithTail.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

  Definition rvsegs : list Segment := VW_BSEGS ++ tail.

  Lemma rv_fetch_word : forall a, fetch_word rvsegs a = fetch_word VW_BSEGS a.
  Proof. intros a. unfold rvsegs. exact (fetch_word_app_nx VW_BSEGS tail Hnx a). Qed.

  Lemma rv_fetch_word_ov : forall m a, fetch_word_ov rvsegs m a = fetch_word_ov VW_BSEGS m a.
  Proof. intros m a. unfold rvsegs. exact (fetch_word_ov_app_nx VW_BSEGS tail Hnx m a). Qed.

  (* [ov_read_bytes_app_nx]'s proof uses no permission hypothesis, so it takes none. *)
  Lemma rv_read_keep : forall n m a bs,
    ov_read_bytes VW_BSEGS m a n = Some bs -> ov_read_bytes rvsegs m a n = Some bs.
  Proof. intros n m a bs H. unfold rvsegs. exact (ov_read_bytes_app_nx VW_BSEGS tail n m a bs H). Qed.

  Lemma rv_mem_inv : forall m, mem_inv rvsegs m -> mem_inv VW_BSEGS m.
  Proof.
    intros m MI a b Hab. specialize (MI a b Hab).
    unfold ro_addr, rvsegs in *. rewrite find_segment_app in MI.
    destruct (find_segment VW_BSEGS (bv_unsigned a) 1) as [s|]; [exact MI|reflexivity].
  Qed.

  Definition rv_image (m : word -> option byte) (vb : Z) : Prop := rvdso_ok rvsegs m vb.

  Lemma rv_image_of_rom : forall m vb,
    rvdso_rom rvsegs vb -> mem_inv rvsegs m -> rv_image m vb.
  Proof. intros m vb ROM MI. exact (rvdso_ok_of_rom rvsegs m vb ROM MI). Qed.

  Lemma rv_read_image : forall m vb o n bs,
    rv_image m vb ->
    0 <= o -> (Z.to_nat o + n <= Z.to_nat RVDSO_SIZE)%nat ->
    bs = firstn n (skipn (Z.to_nat o) rvdso_bytes) ->
    ov_read_bytes rvsegs m (wa (vb + o)) n = Some bs.
  Proof. intros m vb o n bs IM Ho Hn Hbs. exact (rvdso_read rvsegs m vb o n bs IM Ho Hn Hbs). Qed.

End WithTail.

Arguments rvsegs tail /.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: rv_mrd_keep and rv_bytes_at_keep, which carry the auxv claim's reads from rsegs onto the segment list the vDSO walk runs over. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Ref/RVdsoXfer.v, its two transfer lemmas renamed rv_ to av_ and joined to the segment-list, fetch and read lemmas of proofs/openssl/echconfiglist_parser/lib/Ref/RVdsoSegs.v; 36 of its 54 lines of code are new or changed and 12 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/Ref/RVdsoXfer.v, lines 33-44, 56 and 58-71 and projects/openssl/echconfiglist_parser/proofs/lib/Ref/RVdsoSegs.v, lines 14-26, 43-58 and 62, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the segment list the ASan build's __vdsosym walk runs
   against, the binary's segments followed by the vDSO pair, and the fetch and read facts that
   carry over to it; the As copy of Ref/RVdsoSegs.v together with the two transfer lemmas of
   Ref/RVdsoXfer.v.

   At LPS 727298f3 the auxv publishes AT_SYSINFO_EHDR as pair 0, so musl's __vdsosym reads the
   vDSO ELF by ordinary loads.  Those bytes are served only by the run's segment list
   ([Run.run_segments] appends [Run.vdso_segments], two "r--" segments), so the walk runs against
   [asegs ++ tail] with the pair [tail] kept abstract behind its two permission facts.  Fetch over
   that list is fetch over the binary's own list ([RomStable.fetch_word_app_nx], an equality), and
   a read the binary's list serves is served the same way ([RomStable.ov_read_bytes_app_nx],
   [RomStable.memory_read_app_nx]; neither takes a permission hypothesis). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec Frame Cells VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import AVdsoAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithTail.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.

  Local Notation VS := (VW_BSEGS ++ tail).

  Lemma av_fetch_word : forall a, fetch_word VS a = fetch_word VW_BSEGS a.
  Proof. intros a. exact (fetch_word_app_nx VW_BSEGS tail Hnx a). Qed.

  Lemma av_fetch_word_ov : forall m a, fetch_word_ov VS m a = fetch_word_ov VW_BSEGS m a.
  Proof. intros m a. exact (fetch_word_ov_app_nx VW_BSEGS tail Hnx m a). Qed.

  (* [ov_read_bytes_app_nx]'s proof uses no permission hypothesis, so it takes none. *)
  Lemma av_read_keep : forall n m a bs,
    ov_read_bytes VW_BSEGS m a n = Some bs -> ov_read_bytes VS m a n = Some bs.
  Proof. intros n m a bs H. exact (ov_read_bytes_app_nx VW_BSEGS tail n m a bs H). Qed.

  Lemma av_mem_inv : forall m, mem_inv VS m -> mem_inv VW_BSEGS m.
  Proof.
    intros m MI a b Hab. specialize (MI a b Hab).
    unfold ro_addr in *. rewrite find_segment_app in MI.
    destruct (find_segment VW_BSEGS (bv_unsigned a) 1) as [s|]; [exact MI|reflexivity].
  Qed.

  Definition av_image (m : word -> option byte) (vb : Z) : Prop := rvdso_ok VS m vb.

  Lemma av_image_of_rom : forall m vb,
    rvdso_rom VS vb -> mem_inv VS m -> av_image m vb.
  Proof. intros m vb ROM MI. exact (rvdso_ok_of_rom VS m vb ROM MI). Qed.

  Lemma av_read_image : forall m vb o n bs,
    av_image m vb ->
    0 <= o -> (Z.to_nat o + n <= Z.to_nat RVDSO_SIZE)%nat ->
    bs = firstn n (skipn (Z.to_nat o) rvdso_bytes) ->
    ov_read_bytes VS m (wa (vb + o)) n = Some bs.
  Proof. intros m vb o n bs IM Ho Hn Hbs. exact (rvdso_read VS m vb o n bs IM Ho Hn Hbs). Qed.

  (* Ref/RVdsoXfer.v's two lemmas: a read the binary's list serves, through [mrd] and
     [bytes_at], is served the same by the run's list.  [memory_read_app_nx] takes no
     permission hypothesis. *)
  Lemma av_mrd_keep : forall m a b,
    mrd VW_BSEGS m a = Some b -> mrd VS m a = Some b.
  Proof.
    intros m a b H. unfold mrd in *.
    destruct (m a) as [b0|] eqn:EM; [exact H|].
    unfold seg_rom in *.
    destruct (memory_read VW_BSEGS a 1) as [bs|] eqn:E; [|discriminate H].
    rewrite (memory_read_app_nx VW_BSEGS tail a 1 bs E). exact H.
  Qed.

  Lemma av_bytes_at_keep : forall m a bs,
    bytes_at VW_BSEGS m a bs -> bytes_at VS m a bs.
  Proof.
    intros m a bs (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:EN.
    - apply av_mrd_keep. rewrite (H2 i Hi), EN. reflexivity.
    - apply nth_error_None in EN. lia.
  Qed.

End WithTail.

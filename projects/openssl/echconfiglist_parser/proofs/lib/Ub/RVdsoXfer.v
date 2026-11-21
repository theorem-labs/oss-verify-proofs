(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the ubsan binary's copy of Ref/RVdsoXfer.v: rv_mrd_keep and rv_bytes_at_keep, which carry the auxv claim's reads from usegs onto the segment list the vDSO walk runs over. *)
(* IN A NEW FILE, AND THAT IS THE POINT.  In the plain binary's copy an earlier version of these two
   lemmas was appended to Ref/RVdsoSegs.v, which was GREEN; they did not
   compile, and a probe round went targets 5 built 2 because
   the breakage cascaded to RVdsoSym.vo and RVdsoWalk.vo, which require it.
   RVdsoSegs.v was restored byte-identical and
   the next round confirmed targets 5 built 4.  Topical home is
   not the criterion; BLAST RADIUS is.  These lemmas belong beside rvsegs
   and they live here instead, where being wrong costs only this file.

   WHY THEY ARE NEEDED.  A later probe round of the plain copy is the first round
   whose printed context reached the real obstruction: the walk's preamble
   SUCCEEDS -- hcb/hsb fire and EchAuxv's 16-binder destructure yields

     AVC : rw_cells rsegs m 3208976 [C8 (Z_to_bv 64 av)]
     AVL : bytes_at rsegs m av (u64s (rauxv_list v rnd execfn r))

   -- while the goal is `evt rvsegs ...`.  In this copy the claim speaks about usegs and
   the walk steps over usegs ++ tail, so the auxv facts have to be carried
   across before the load at RAUXV_CELL can discharge.  rv_read_keep covers
   ov_read_bytes alone, which is not what `step` consumes there.

   SOUND IN THIS DIRECTION ONLY, and only because the tail is "r--":
   appending can ENLARGE seg_rom and never shrink it.  The lemma underneath
   is RomStable's memory_read_app_nx, which -- checked in the file, after
   this cone bit me three times on exactly this question -- takes NO
   permission hypothesis: its proof only destructs find_segment.  By
   contrast fetch_word_app_nx DOES take Hnx.  Same Section, different
   argument lists, and only the proof says which. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec Frame Cells VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RVdsoSegs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Xfer.
  Variable tail : list Segment.

  Local Notation VS := (rvsegs tail).

  (* PropExec.v:292  seg_rom segs addr = match memory_read segs addr 1 with
                                         Some (b :: _) => Some b | _ => None end
     -- memory_read takes the WORD, not bv_unsigned of it, and its count is
     an N.  The earlier draft passed `bv_unsigned a` and a nat, which is what
     a probe round reported at RVdsoSegs.v:150 characters
     33-46: exactly the `(bv_unsigned a)` token. *)
  Lemma rv_mrd_keep : forall m a b,
    mrd usegs m a = Some b -> mrd VS m a = Some b.
  Proof.
    intros m a b H. unfold mrd, rvsegs in *.
    destruct (m a) as [b0|] eqn:EM; [exact H|].
    unfold seg_rom in *.
    destruct (memory_read usegs a 1) as [bs|] eqn:E; [|discriminate H].
    rewrite (memory_read_app_nx usegs tail a 1 bs E). exact H.
  Qed.

  Lemma rv_bytes_at_keep : forall m a bs,
    bytes_at usegs m a bs -> bytes_at VS m a bs.
  Proof.
    intros m a bs (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:EN.
    - apply rv_mrd_keep. rewrite (H2 i Hi), EN. reflexivity.
    - apply nth_error_None in EN. lia.
  Qed.

End Xfer.

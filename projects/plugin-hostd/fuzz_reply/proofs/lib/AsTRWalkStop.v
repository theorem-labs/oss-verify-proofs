(* fuzz_reply, both ASan builds: where the runtime's frame walk stops when a caller's s0 is not a real-stack address.
   Shared by lib/A (asan) and lib/B (asan-ubsan); it holds no address of either image.

   What it models, from the llvmorg-20.1.8 sources (verbatim copies with checksums in the ASan kit's source depot,
   src-llvm-20.1.8/, `sha256sum -c SHA256SUMS` all OK):
   - asan_stack.h:35-48 GET_STACK_TRACE(max_size, fast), used by the malloc, free and realloc wrappers through
     GET_STACK_TRACE_MALLOC / _FREE (:60-63) with max_size = the trace-depth limit. For max_size <= 2 the macro does
     not walk: it stores GetCurrentPc() and, for 2, GET_CALLER_PC() (the wrapper's ra). For max_size > 2 it calls
     Unwind with a second GetCurrentPc() call, whose return address is a different pc. So a wrapper has two frame-0
     pcs: [pcs] on the short branch and [pcl] on the walking branch (asan image: malloc 0x54040 / 0x5408c,
     free 0x53f10 / 0x53f2c, realloc 0x5430c / 0x54328; asan-ubsan: malloc 0x54098 / 0x540e4, free 0x53f68 / 0x53f84,
     realloc 0x54364 / 0x54380).
   - sanitizer_stacktrace.cpp:97-147 BufferedStackTrace::UnwindFast, RISC-V branch: trace_buffer[0] = pc (:102);
     no walk when stack_top < 4096 (:104); the loop (:110-112) runs while IsValidFrame(frame, stack_top, bottom),
     frame is 8-aligned and size < max_depth; it reads pc1 = frame[-1] (:126), stops when pc1 < page size (:133),
     records pc1 unless pc1 = pc (:135-137), sets bottom = frame (:138) and moves to frame[-2] (:141, :145; on RISC-V
     GetCanonicFrame returns bp unchanged).
   - sanitizer_stacktrace.h:170-172 IsValidFrame(frame, top, bottom) = frame > bottom && frame < top - kFrameSize,
     kFrameSize = 2 * sizeof(uhwptr) = 16 (:166). THIS is the check that ends the walk at a non-stack s0: after the
     wrapper's own frame record, bottom is the wrapper's frame, and a caller s0 that is not in (bottom, top - 16)
     fails it. In the images: asan UnwindFast 0x74c98, the two compares on the next frame at 0x74d80 (bgeu frame,
     new: new <= bottom ends the walk) and 0x74d84 (bgeu new, top - 16); asan-ubsan UnwindFast 0x74cf0, compares at
     0x74dd8 and 0x74ddc. The depot's Put compares the 64-bit hash only (asan 0x74484, asan-ubsan 0x744dc; see
     AsDepotIds.v).

   The walk reads memory through `ld` (the 8-byte word at an address). `fuel` only bounds the number of loop rounds
   the model runs; get_stack_trace_stop shows that the loop's own test ends the walk in round 2, so the result is
   the same for every fuel >= 1. *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
  Variable ld : Z -> Z.   (* the 8-byte word UnwindFast loads at an address *)
  Variable pg : Z.        (* GetPageSizeCached() *)

  (* sanitizer_stacktrace.h:170-172 with kFrameSize = 16 *)
  Definition is_valid_frame (frame top bottom : Z) : bool := (bottom <? frame) && (frame <? top - 16).

  (* the loop of sanitizer_stacktrace.cpp:110-146 (RISC-V); size counts the stored frames; ld (frame - 8) is pc1 *)
  Fixpoint uwalk (fuel : nat) (pc top bottom frame : Z) (size maxd : nat) : list Z :=
    match fuel with
    | O => []
    | S f =>
        if is_valid_frame frame top bottom && (frame mod 8 =? 0) && Nat.ltb size maxd then
          if ld (frame - 8) <? pg then []
          else if ld (frame - 8) =? pc then uwalk f pc top frame (ld (frame - 16)) size maxd
          else ld (frame - 8) :: uwalk f pc top frame (ld (frame - 16)) (S size) maxd
        else []
    end.

  (* sanitizer_stacktrace.cpp:97-105 *)
  Definition unwind_fast (fuel : nat) (pc bp top bot : Z) (maxd : nat) : list Z :=
    pc :: (if top <? 4096 then [] else uwalk fuel pc top bot bp 1 maxd).

  (* asan_stack.h:35-48: mcs = the trace-depth limit, pcs / pcl = the short / walking branch's frame-0 pc,
     ra = the wrapper's return address (GET_CALLER_PC), bp = the wrapper's frame (GET_CURRENT_FRAME). The walking
     branch is the fast unwinder on the current thread's stack [bot, top) (asan_stack.cpp UnwindImpl with
     fast_unwind_on_malloc); an unwind the runtime declines records the empty trace, which Put does not store
     (AsDepotIds.dput). *)
  Definition get_stack_trace (fuel mcs : nat) (pcs pcl ra bp top bot : Z) : list Z :=
    if Nat.leb mcs 2 then firstn mcs [pcs; ra] else unwind_fast fuel pcl bp top bot mcs.

  (* The frame-0 pc a wrapper records under depth limit mcs. *)
  Definition pc0_of (mcs : nat) (pcs pcl : Z) : Z := if Nat.leb mcs 2 then pcs else pcl.

  (* The walk stops after two words when the caller's s0 (the word the wrapper saved at frame - 16) is not an
     address of the real stack (bot, top): the recorded trace is the first mcs words of [pc0; ra]. *)
  Lemma get_stack_trace_stop : forall fuel mcs pcs pcl ra fr top bot s0c,
      (1 <= fuel)%nat ->
      4096 <= top -> bot < fr -> fr < top - 16 -> fr mod 8 = 0 ->
      ld (fr - 8) = ra -> pg <= ra -> ra <> pcl ->
      ld (fr - 16) = s0c -> ~ (bot < s0c < top) ->
      get_stack_trace fuel mcs pcs pcl ra fr top bot = firstn mcs [pc0_of mcs pcs pcl; ra].
  Proof.
    intros fuel mcs pcs pcl ra fr top bot s0c Hf Htop Hb Ht Ha Hra Hpg Hne Hs0 Hns.
    unfold get_stack_trace, pc0_of. destruct (Nat.leb mcs 2) eqn:E; [reflexivity|].
    apply Nat.leb_gt in E. unfold unwind_fast.
    replace (top <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct fuel as [|f]; [lia|]. cbn [uwalk].
    unfold is_valid_frame.
    replace (bot <? fr) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (fr <? top - 16) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (fr mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Ha).
    replace (Nat.ltb 1 mcs) with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [andb]. rewrite Hra.
    replace (ra <? pg) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (ra =? pcl) with false by (symmetry; apply Z.eqb_neq; exact Hne).
    rewrite Hs0.
    assert (W : uwalk f pcl top fr s0c 2 mcs = []).
    { destruct f as [|f]; [reflexivity|]. cbn [uwalk]. unfold is_valid_frame.
      assert (V : (fr <? s0c) && (s0c <? top - 16) = false).
      { destruct (Z.ltb_spec fr s0c); destruct (Z.ltb_spec s0c (top - 16)); cbn;
          first [reflexivity | exfalso; lia]. }
      rewrite V. reflexivity. }
    rewrite W. destruct mcs as [|[|[|m]]]; [lia|lia|lia|reflexivity].
  Qed.

  (* The two shapes of a non-stack s0 at the five fuzz_reply sites: an image address or a small integer, and an
     address inside a heap block that is disjoint from the stack. *)
  Lemma nonstack_of_below : forall bot top v, v <= bot -> ~ (bot < v < top).
  Proof. intros. lia. Qed.

  Lemma nonstack_of_block : forall bot top p n v,
      p <= v < p + n -> (p + n <= bot \/ top <= p) -> ~ (bot < v < top).
  Proof. intros. lia. Qed.

  (* send_line (both builds): s0 = len (asan 0x8276c, asan-ubsan 0x8288c). relay_event passes strlen + 1 of an event
     block of at most 65536 bytes, drain at most 6001 (the bltu against 6001 = 0x1771), gesture_end the strlen of a
     held line (at most 6000) or 5. *)
  Lemma send_line_s0 : forall len bot top, len <= 65536 -> 65536 <= bot -> ~ (bot < len < top).
  Proof. intros. lia. Qed.

  (* gestures_end (both builds): s0 = s + 48 (asan 0x82588, asan-ubsan 0x8265c), s = blk + 56 k with k < n, blk the
     g_src block of n entries of 56 bytes, an ASan heap block, so disjoint from the stack. *)
  Lemma gestures_end_s0 : forall blk n k bot top,
      0 <= k < n -> (blk + 56 * n <= bot \/ top <= blk) -> ~ (bot < blk + 56 * k + 48 < top).
  Proof. intros blk n k bot top Hk Hd. apply (nonstack_of_block bot top blk (56 * n)); lia. Qed.
End Walk.

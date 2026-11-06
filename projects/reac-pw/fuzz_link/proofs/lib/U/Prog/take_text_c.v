(* take_text (projects/reac-pw/fuzz_link/source/fuzz_link.c:319-330): the harness`s cut of an
   attribute`s text into a buffer. UBSAN BUILD ONLY: the plain build inlines take_text into talk,
   so it has no plain twin; in the ubsan build talk calls it (link/donors/premises-ubsan.txt,
   talk, at 0x15e18 for the alias and 0x15ea0 for the kind).

   a0 = d, a1 = n, a2 = out, a3 = cap (read from link/ct/dis/ubsan/take_text.s: out and cap are
   the two registers tested against 0 first, d is the base of the scan, n its bound). A NULL out or
   a zero cap writes nothing outside the frame. Otherwise the payload is the n bytes at d, the text
   is that payload up to its first NUL and to cap-1 bytes, and a NUL is written after it.
   THE POST IS THE REAL VALUE, and it is link_spec`s `cut_text`, stated exactly as
   lib/Prog/copy_attr_c.v states it for the library`s copy_attr: the two are the same function,
   which is why the two sides` buffers hold the same C string.
   One part of the Post differs from copy_attr_c.v on purpose: take_text saves ra, s0 and s1 in
   its frame BEFORE it tests out and cap (take_text.s +0x00 to +0x14), so on the no-op paths the
   memory is unchanged outside that frame, not unchanged everywhere. The Post says exactly that
   (`munch` over the 32-byte frame).

   The UBSan guards (link/donors/ubsan-checks.tsv, take_text, 1 trap at 0x16034, 4 guard
   branches), and the premise that answers each:
   - 0x15fcc (fuzz_link.c:324, d + k does not wrap, k < n): answered by the bytes_at of the
     payload, which gives d + n <= 2 ^ 64.
   - 0x15fd8 (fuzz_link.c:324, d + k is NULL exactly when d is NULL) and 0x15fdc (fuzz_link.c:324,
     d is not NULL): premise `0 < arg regs 0`, with the no-wrap above.
   - 0x16014 (fuzz_link.c:329, out + k does not wrap, k <= cap - 1): answered by the rw_cells of
     the buffer (buf_arg), which gives out + cap <= 2 ^ 64.
   The other premises are what a provable statement needs, not guards:
   - the payload and the buffer are not inside this function`s 32-byte frame: the frame is
     written before the payload is read and before the buffer is written;
   - the payload and the buffer do not overlap (memcpy`s separation premise).
   The scan reads only up to the first NUL, but the premise asks for all n bytes, as
   copy_attr_c.v does: talk holds the whole attribute inside its chunk.
   K = 32 (its own frame; memcpy uses no stack: link/donors/premises-ubsan.txt and
   lib/U/Prog/memcpy_c.v, which keeps sp and takes no stack premise).
   Entry read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc). 
   L6 AND L7 APPLIED HERE TOO (LinkLib's two findings on copy_attr, 2026-10-30): take_text is the
   harness-side twin of copy_attr, and talk calls it on the SAME buffer again for a second
   attribute of the same type. So the Post keeps the whole buffer `rw_cells` (wmono gives
   writability, not readability), and a NULL buffer owns no bytes in the write set (`buf_arg` is
   trivially true of NULL with any cap).
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition TAKE_TEXT : Z := 0x15f9c.
Lemma TAKE_TEXT_is_entry : TAKE_TEXT = P_take_text. Proof. reflexivity. Qed.

Definition take_text_contract : Prop :=
  leaf TAKE_TEXT 32
    (fun regs m => exists pay,
       bytes_at rsegs m (arg regs 0) pay
       /\ Z.of_nat (length pay) = arg regs 1
       /\ 0 < arg regs 0
       /\ (arg regs 0 + arg regs 1 <= spZ regs - 32 \/ spZ regs <= arg regs 0)
       /\ buf_arg m (arg regs 2) (arg regs 3)
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             (arg regs 2 + arg regs 3 <= spZ regs - 32 \/ spZ regs <= arg regs 2)
             /\ (arg regs 0 + arg regs 1 <= arg regs 2 \/ arg regs 2 + arg regs 3 <= arg regs 0)))
    (fun regs m => [(arg regs 2, arg regs 2 + (if arg regs 2 =? 0 then 0 else arg regs 3))])
    (fun regs m regs' m' =>
       (arg regs 2 = 0 -> munch [(spZ regs - 32, spZ regs)] m m')
       /\ (arg regs 3 = 0 -> munch [(spZ regs - 32, spZ regs)] m m')
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             forall pay, bytes_at rsegs m (arg regs 0) pay ->
               Z.of_nat (length pay) = arg regs 1 ->
               cstr_at m' (arg regs 2) (cut_text pay (arg regs 3)))
       /\ (arg regs 2 <> 0 -> 1 <= arg regs 3 ->
             exists junk, rw_cells rsegs m' (arg regs 2) [CB (Z.to_nat (arg regs 3)) junk])).

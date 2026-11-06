(* nl_attr_put (projects/reac-pw/fuzz_link/source/netlink.h:283-289): the harness puts one attribute
   into the reply it is building. UBSAN BUILD ONLY: the plain build inlines nl_attr_put into
   attr_text, so it has no plain twin; in the ubsan build attr_text is inlined into kernel and
   calls this function (link/donors/premises-ubsan.txt, kernel, at 0x149b4 and 0x14c18).

   a0 = w (a struct nl_w), a1 = type, a2 = p, a3 = n. It puts the 16-bit length 4 + n, the 16-bit
   type, the n bytes at p (memcpy) and the NL_ALIGN padding (memset) into w->b. Each nl_put that
   does not fit raises w->full and writes nothing.
   THE WEAKEST FORM THE CALLER NEEDS, the reading attr_text_c.v uses: plain_halts and ubsan_halts
   do not need to know WHICH reply bytes the harness builds, because both readers walk the same
   chunk whatever it holds. So the Post says only that the writer stays a writer: it touches no
   byte outside the 4112-byte structure, its length never passes 4096, and it never shrinks.

   The UBSan guards (link/donors/ubsan-checks.tsv, nl_attr_put, 1 trap at 0x15b44, 9 guard
   branches), and the premise that answers each:
   - 0x159cc (netlink.h:227, `andi a0, a0, 7` then bnez, before the load of w->n): w is
     8-aligned. Premise `arg regs 0 mod 8 = 0`.
   - 0x15a08, 0x15a58, 0x15aa4, 0x15b00 (netlink.h:232, the bound test of w->b + w->n, trap when
     w->n >= 4097), for the length, the type, the data and the padding: answered by nlw_wf, which
     gives w->n <= 4096 (the fit tests before the two 16-bit puts pass also for a w->n within 2
     of 2 ^ 64, so the premise is required).
   - 0x15a10, 0x15a5c, 0x15aac, 0x15b08 (netlink.h:232, w + w->n does not wrap): answered by
     nlw_at, whose bytes_at gives w + 4112 <= 2 ^ 64, with w->n <= 4096.
   The other premises are what a provable statement needs, not guards:
   - the n bytes at p are readable (memcpy`s premise);
   - n + 4096 < 2 ^ 64: the data put tests `w->n + n > 4096` in unsigned arithmetic, so a wrapping
     sum would pass the test and hand memcpy a length no buffer has;
   - the data does not overlap the structure (memcpy`s separation premise; empty data needs none);
   - the structure is not inside this function`s 32-byte frame, whose saved registers the writes
     would otherwise overwrite.
   K = 32 (its own frame; memcpy and memset use no stack: link/donors/premises-ubsan.txt and
   lib/U/Prog/memcpy_c.v, lib/U/Prog/memset_c.v, which keep sp and take no stack premise).
   Entry read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition NL_ATTR_PUT : Z := 0x159b0.
Lemma NL_ATTR_PUT_is_entry : NL_ATTR_PUT = P_nl_attr_put. Proof. reflexivity. Qed.

Definition nl_attr_put_contract : Prop :=
  leaf NL_ATTR_PUT 32
    (fun regs m => exists bs src,
       nlw_at m (arg regs 0) bs /\ nlw_wf bs
       /\ arg regs 0 mod 8 = 0
       /\ bytes_at rsegs m (arg regs 2) src /\ Z.of_nat (length src) = arg regs 3
       /\ arg regs 3 + NL_CHUNK_MAX < 2 ^ 64
       /\ (arg regs 3 = 0 \/ arg regs 2 + arg regs 3 <= arg regs 0
           \/ arg regs 0 + NW_SIZE <= arg regs 2)
       /\ (arg regs 0 + NW_SIZE <= spZ regs - 32 \/ spZ regs <= arg regs 0))
    (fun regs m => [(arg regs 0, arg regs 0 + NW_SIZE)])
    (fun regs m regs' m' => forall bs, nlw_at m (arg regs 0) bs ->
       exists bs', nlw_at m' (arg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs').

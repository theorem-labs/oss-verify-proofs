(* nl_begin (projects/reac-pw/fuzz_link/source/netlink.h:266-275): the harness starts a message of
   the reply it is building. UBSAN BUILD ONLY: the plain build inlines nl_begin into kernel, so it
   has no plain twin.

   a0 = w (a struct nl_w), a1 = type. It answers at = w->n, then puts the 16-byte message header
   into w->b with five nl_put calls (a 4-byte 0, the 16-bit type, a 16-bit 0, a 4-byte 1, a
   4-byte 0). Each nl_put that does not fit raises w->full and writes nothing.
   THE WEAKEST FORM THE CALLER NEEDS, the reading attr_text_c.v uses: plain_halts and ubsan_halts
   do not need to know WHICH reply bytes the harness builds, because both readers walk the same
   chunk whatever it holds. So the Post says only that the writer stays a writer: it touches no
   byte outside the 4112-byte structure, its length never passes 4096, and it never shrinks. The
   one value the Post does state is the answer, at = w->n at entry: kernel passes it to nl_end,
   whose write under the test `at + 4 <= w->n` stays inside w->b only when at + 4 does not wrap,
   and the answer being the old length (at most 4096) is what gives that.

   The UBSan guards (link/donors/ubsan-checks.tsv, nl_begin, 1 trap at 0x159ac, 11 guard
   branches), and the premise that answers each:
   - 0x1580c (netlink.h:268, `andi a0, a0, 7` then bnez, before the load of w->n): w is
     8-aligned. Premise `arg regs 0 mod 8 = 0`.
   - 0x15848, 0x1589c, 0x158e8, 0x1592c, 0x15980 (netlink.h:232, the bound test of w->b + w->n,
     trap when w->n >= 4097), one for each of the five nl_put calls: answered by nlw_wf, which
     gives w->n <= 4096. The fit test before each one passes also for a w->n within 4 of 2 ^ 64
     (the unsigned sum wraps), so this premise is required, not only convenient.
   - 0x15850, 0x158a4, 0x158ec, 0x15934, 0x15984 (netlink.h:232, w + w->n does not wrap): answered
     by nlw_at, whose bytes_at gives w + 4112 <= 2 ^ 64, with w->n <= 4096.
   K = 0 (frame 0, no call: link/donors/premises-ubsan.txt).
   Entry read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition NL_BEGIN : Z := 0x15804.
Lemma NL_BEGIN_is_entry : NL_BEGIN = P_nl_begin. Proof. reflexivity. Qed.

Definition nl_begin_contract : Prop :=
  leaf NL_BEGIN 0
    (fun regs m => exists bs,
       nlw_at m (arg regs 0) bs /\ nlw_wf bs
       /\ arg regs 0 mod 8 = 0)
    (fun regs m => [(arg regs 0, arg regs 0 + NW_SIZE)])
    (fun regs m regs' m' => forall bs, nlw_at m (arg regs 0) bs ->
       res regs' = nw_n bs
       /\ exists bs', nlw_at m' (arg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs').

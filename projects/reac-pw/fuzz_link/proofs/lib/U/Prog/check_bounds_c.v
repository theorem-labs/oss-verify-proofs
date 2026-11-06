(* check_bounds (fuzz_link.c:555-566), UBSAN build: a text written into a buffer of `cap` bytes ends
   in a NUL inside them, and the guard byte after them is as text_buf left it.

   The twin of lib/Prog/check_bounds_c.v, with the same premises and the same Post.
   `if (!text_within(buf, cap)) abort();` with text_within = `memchr(buf,0,cap) != NULL &&
   (uint8_t)buf[cap] == 0x5a`. a0 = buf, a1 = cap. Claim (e) of the halting theorem.
   `tbuf_at` already says the byte at buf+cap is 0x5a, so the only premise left is that a NUL is
   among the cap bytes; the caller gets it from link_spec cut_text_len. The function reads cap+1
   bytes from buf after its prologue, so buf is apart from its frame. K = 32 (own frame of 32;
   memchr uses no stack). The Post is `only_frame`: the prologue stores ra, s0 and s1 into
   [sp-32, sp) and nothing restores those bytes, so memory is NOT unchanged; `leaf` already says
   only that window changed.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/check_bounds.s):
   - branch 0x1562c (fuzz_link.c:641, `not a0, s1; bltu a0, s0`): traps when buf + cap passes
     2^64 - 1, before the read of buf[cap]. ANSWERED BY THE PLAIN PREMISES, no premise added:
     tbuf_at is rw_cells over cap + 1 bytes, so rw_cells_bound gives buf + cap + 1 <= 2^64.
   - the `unimp` at 0x15658 follows the call to abort and is reached only through it.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_BOUNDS : Z := 0x15600.
Lemma CHECK_BOUNDS_is_entry : CHECK_BOUNDS = P_check_bounds. Proof. reflexivity. Qed.

Definition check_bounds_contract : Prop :=
  leaf CHECK_BOUNDS 32
    (fun regs m => exists bs,
       arg regs 0 <> 0 /\ 1 <= arg regs 1
       /\ tbuf_at m (arg regs 0) (arg regs 1) bs /\ In (zb 0) bs
       /\ apart_frame regs 32 (arg regs 0) (arg regs 1 + 1))
    writes_nothing
    only_frame.

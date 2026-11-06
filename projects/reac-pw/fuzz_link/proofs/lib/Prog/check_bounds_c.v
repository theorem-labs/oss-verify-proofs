(* check_bounds (fuzz_link.c:555-566): a text written into a buffer of `cap` bytes ends in a NUL
   inside them, and the guard byte after them is as text_buf left it.

   `if (!text_within(buf, cap)) abort();` with text_within = `memchr(buf,0,cap) != NULL &&
   (uint8_t)buf[cap] == 0x5a`. a0 = buf, a1 = cap. Claim (e) of plain_halts.
   `tbuf_at` already says the byte at buf+cap is 0x5a (what text_buf wrote and what no reader may
   touch), so the only premise left is that a NUL is among the cap bytes; the caller gets it from
   link_spec cut_text_len, because model_read and reac_link_alias_read both store a NUL at index 0
   before anything else. K = 32 (own frame; memchr uses no stack).
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_BOUNDS : Z := 0x151c0.
Lemma CHECK_BOUNDS_is_entry : CHECK_BOUNDS = P_check_bounds. Proof. reflexivity. Qed.

Definition check_bounds_contract : Prop :=
  leaf CHECK_BOUNDS 32
    (fun regs m => exists bs,
       arg regs 0 <> 0 /\ 1 <= arg regs 1
       /\ tbuf_at m (arg regs 0) (arg regs 1) bs /\ In (zb 0) bs
       /\ apart_frame regs 32 (arg regs 0) (arg regs 1 + 1))
    writes_nothing
    only_frame.

(* nl_error (netlink.h:305-315): the harness puts an NLMSG_ERROR into the reply it is building,
   whole or cut after `cut` payload bytes.

   a0 = w (a struct nl_w), a1 = code, a2 = cut. Same reading as attr_text: the contract says only
   that the writer stays a writer, because plain_halts needs the two readers to agree on the chunk
   and not the grammar that made it. K = 80 (own frame; memcpy and memset use no stack). In the
   UBSan build nl_error is inlined into kernel and has no contract.
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images).
   THE CUT MUST BE BOUNDED (LinkHelpers, 2026-10-30): the C test `cut < NL_ERR_BODY`
   (netlink.h:312) is NOT in the binary. At +0x154 `bgez s1, +0x15c` only replaces a NEGATIVE cut
   by 20; every cut >= 0 is kept, and +0x188 memcpy then copies `cut` bytes out of the 20-byte
   body at sp+0xc whenever w->n + cut < 4097. So the Pre must bound it. The one call site (kernel
   +0xafc to +0xb18) computes a2 = (slti(c < 0) - 1) | ((c << 57) >> 61), which is 2^64 - 1 or a
   value in 0..7, and meets either arm. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition NL_ERROR_F : Z := 0x154b4.
Lemma NL_ERROR_F_is_entry : NL_ERROR_F = P_nl_error. Proof. reflexivity. Qed.

Definition nl_error_contract : Prop :=
  leaf NL_ERROR_F 80
    (fun regs m => exists bs, nlw_at m (arg regs 0) bs /\ nlw_wf bs
       /\ apart_frame regs 80 (arg regs 0) NW_SIZE
       /\ (arg regs 2 <= NL_ERR_BODY \/ 2 ^ 63 <= arg regs 2))
    (fun regs m => [(arg regs 0, arg regs 0 + NW_SIZE)])
    (fun regs m regs' m' => forall bs, nlw_at m (arg regs 0) bs ->
       exists bs', nlw_at m' (arg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs').

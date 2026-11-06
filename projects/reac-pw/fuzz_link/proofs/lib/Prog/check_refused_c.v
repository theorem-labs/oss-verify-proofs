(* check_refused (fuzz_link.c:519-531): a read or a write that was refused opened no socket.

   `if (opened != opened_before) abort();` with a0 = opened_before and a1 = opened, compiled to
   one `bne a1, a0`. Claim (c) of plain_halts. The returning path uses no stack.
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_REFUSED : Z := 0x151ac.
Lemma CHECK_REFUSED_is_entry : CHECK_REFUSED = P_check_refused. Proof. reflexivity. Qed.

Definition check_refused_contract : Prop :=
  leaf CHECK_REFUSED 0
    (fun regs m => getr regs 10 = getr regs 11)
    writes_nothing
    unchanged.

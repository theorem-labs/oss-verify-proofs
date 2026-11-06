(* check_refused (fuzz_link.c:519-531), UBSAN build: a read or a write that was refused opened no
   socket.

   The twin of lib/Prog/check_refused_c.v, with the same premise and the same Post.
   `if (opened != opened_before) abort();` with a0 = opened_before and a1 = opened, compiled to one
   `bne a1, a0` and a `ret`, as in the plain build. Claim (c) of the halting theorem. The returning
   path uses no stack (the 16-byte frame is pushed only on the abort path, +0x08), so K = 0.
   UBSan guards: link/donors/ubsan-checks.tsv gives check_refused no guard branch. Its one `unimp`
   (0x155fc) follows the call to abort and is reached only through it, so no premise is added.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_REFUSED : Z := 0x155e8.
Lemma CHECK_REFUSED_is_entry : CHECK_REFUSED = P_check_refused. Proof. reflexivity. Qed.

Definition check_refused_contract : Prop :=
  leaf CHECK_REFUSED 0
    (fun regs m => getr regs 10 = getr regs 11)
    writes_nothing
    unchanged.

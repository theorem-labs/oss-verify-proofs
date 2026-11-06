(* check_socket (fuzz_link.c:487-496), UBSAN build: every socket opened was closed, and no other
   descriptor was used.

   The twin of lib/Prog/check_socket_c.v, with the same premise and the same Post. As in the plain
   build, the compiler dropped the `const struct nl_kernel *k` argument (every call passes &g_nl)
   and reads the global directly: `g_nl+0x40000` plus 0x214 (open), 0x218 (opened), 0x21c (closed)
   and 0x220 (misuse), at +0x10 to +0x24. The contract therefore names no argument. Claim (a) of
   the halting theorem. The returning path uses no stack (the 16-byte frame is pushed only on the
   abort path, +0x30), so K = 0.
   UBSan guards: link/donors/ubsan-checks.tsv gives check_socket no guard branch. Its one `unimp`
   (0x15518) follows the call to abort and is reached only through it, so no premise is added.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_SOCKET : Z := 0x154dc.
Lemma CHECK_SOCKET_is_entry : CHECK_SOCKET = P_check_socket. Proof. reflexivity. Qed.

Definition check_socket_contract : Prop :=
  leaf CHECK_SOCKET 0
    (fun regs m => exists bs, nlk_at m bs
       /\ nk_open bs = 0 /\ nk_opened bs = nk_closed bs /\ nk_misuse bs = 0)
    writes_nothing
    unchanged.

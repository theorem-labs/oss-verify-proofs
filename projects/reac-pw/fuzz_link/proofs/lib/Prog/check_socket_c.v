(* check_socket (fuzz_link.c:487-496): every socket opened was closed, and no other descriptor was
   used.

   SURPRISE OF THE BINARY: the C function takes a `const struct nl_kernel *k`, but every call
   passes `&g_nl`, so the compiler dropped the argument and reads the global directly
   (`g_nl+0x40000+0x214` at +0x10, and the call sites in LLVMFuzzerTestOneInput pass no argument).
   The contract therefore names no argument. Claim (a) of plain_halts.
   The returning path uses no stack; the 16-byte frame is pushed only on the abort path, +0x30.
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_SOCKET : Z := 0x150e4.
Lemma CHECK_SOCKET_is_entry : CHECK_SOCKET = P_check_socket. Proof. reflexivity. Qed.

Definition check_socket_contract : Prop :=
  leaf CHECK_SOCKET 0
    (fun regs m => exists bs, nlk_at m bs
       /\ nk_open bs = 0 /\ nk_opened bs = nk_closed bs /\ nk_misuse bs = 0)
    writes_nothing
    unchanged.

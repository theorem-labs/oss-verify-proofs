(* check_requests (fuzz_link.c:498-517): the operation sent exactly the requests it owes, in order
   and byte for byte.

   SURPRISE OF THE BINARY: the C function takes `(const struct nl_kernel *k, const struct model *m)`,
   but every call passes `&g_nl` for k, so the compiler dropped that argument and reads the global
   directly. In BOTH images the one remaining argument a0 is `m`: the plain body computes
   `m->n_req` as `a0 + 0x2010 + 0x80` (= a0 + 8336) and `g_nl.n_sent` from the global, and the
   call sites in LLVMFuzzerTestOneInput load a0 from the model pointer alone. Claim (b) of
   plain_halts. K = 48 (own frame; bcmp uses no stack).
   Entry and frame read from the plain image (the unstripped twin of the pin ebe34b259b9f);
   the stack bound K is the function's own frame plus the deepest frame of every callee it can
   reach on the path this contract covers (link/ct/stack.py over both images). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_REQUESTS : Z := 0x15284.
Lemma CHECK_REQUESTS_is_entry : CHECK_REQUESTS = P_check_requests. Proof. reflexivity. Qed.

Definition check_requests_contract : Prop :=
  leaf CHECK_REQUESTS 48
    (fun regs m => exists kbs mbs,
       nlk_at m kbs /\ frame_apart_gnl regs 48 /\ model_at m (arg regs 0) mbs
       /\ nlk_wf kbs /\ model_wf mbs /\ requests_are kbs mbs
       /\ apart_frame regs 48 (arg regs 0) MD_SIZE /\ apart_gnl (arg regs 0) MD_SIZE)
    writes_nothing
    only_frame.

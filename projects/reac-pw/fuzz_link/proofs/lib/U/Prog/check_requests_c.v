(* check_requests (fuzz_link.c:498-517), UBSAN build: the operation sent exactly the requests it owes,
   in order and byte for byte.

   The twin of lib/Prog/check_requests_c.v, with its premises, its Post, and the premises the
   UBSan guards below need. As in the plain build, the compiler dropped the `k` argument (every
   call passes &g_nl): a0 is `m`. The body reads `m->n_req` at a0 + 0x2000 + 0x90 (= a0 + 8336) and
   `g_nl.n_sent` at g_nl + 0x42000 + 0x2a8, then for each i compares `sent_len[i]` with
   `m->req_len[i]` and calls bcmp on min(req_len, 512) bytes of `sent[i]` and `m->req[i]`.
   Claim (b) of the halting theorem. K = 96 (own frame of 96; bcmp uses no stack). The Post is
   `only_frame`: the prologue stores ra and s0-s10 into [sp-96, sp) and nothing restores those
   bytes; `leaf` already says only that window changed.
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/check_requests.s); every guard
   branches to the `unimp` at 0x157f8:
   - branch 0x1570c (fuzz_link.c:629, `andi a1, a0, 7` at +0x34): traps unless `m` is 8-aligned.
     ADDED: `arg regs 0 mod 8 = 0`.
   - branch 0x1576c (fuzz_link.c:632, `beq s3, s5` with s5 = 0x80): traps when the loop reaches
     i = 16, the end of `sent_len[16]`; the loop runs i < n_sent. ADDED:
     `nk_n_sent kbs <= NL_SENT_MAX`, and with it `nlk_wf kbs` and `model_wf mbs`, the form the
     plain twin now carries (LinkHelpers, 2026-10-30): without a bound on the count the contract
     is false in BOTH builds, because requests_are holds of two rings that are zero past entry 16.
   - branch 0x15770 (fuzz_link.c:632, `bltu s9, s3`): traps when m + 8208 + 8i passes 2^64 - 1.
     branch 0x1578c (fuzz_link.c:633, `bltu s7, s2`): traps when m + 12 + 512i passes 2^64 - 1.
     ANSWERED BY THE PLAIN PREMISES, no premise added: model_at is a u8arr of MD_SIZE bytes, so
     bytes_at gives m + MD_SIZE <= 2^64, and both sums stay below m + 8336 for i <= 15.
   - the `unimp` at 0x15800 follows the call to abort and is reached only through it.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition CHECK_REQUESTS : Z := 0x156d4.
Lemma CHECK_REQUESTS_is_entry : CHECK_REQUESTS = P_check_requests. Proof. reflexivity. Qed.

Definition check_requests_contract : Prop :=
  leaf CHECK_REQUESTS 96
    (fun regs m => exists kbs mbs,
       nlk_at m kbs /\ frame_apart_gnl regs 96 /\ model_at m (arg regs 0) mbs /\ requests_are kbs mbs
       /\ apart_frame regs 96 (arg regs 0) MD_SIZE /\ apart_gnl (arg regs 0) MD_SIZE
       /\ arg regs 0 mod 8 = 0 /\ nk_n_sent kbs <= NL_SENT_MAX
       /\ nlk_wf kbs /\ model_wf mbs)
    writes_nothing
    only_frame.

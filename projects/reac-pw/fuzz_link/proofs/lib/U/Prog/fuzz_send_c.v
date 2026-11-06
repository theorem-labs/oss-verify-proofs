(* fuzz_send (netlink.h:89-105), UBSAN build: the fake send(). It keeps the request for the harness to
   read, or fails once with the errno the input chose.

   The twin of lib/Prog/fuzz_send_c.v, with its premises, its Post, and the premises the UBSan
   guards below need. a0 = fd, a1 = buf, a2 = len; the flags argument is dead. A call on anything
   but the open NL_FD is misuse. A pending send_errno is used once and cleared, and then NOTHING is
   recorded. Otherwise, while n_sent < 16, the first min(len, 512) bytes go into
   g_nl.sent[n_sent] with sent_len = len, and the answer is len. K = 32 (own frame of 32; memcpy and
   ___errno_location, called as __errno_location at 0x17638, use no stack).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/fuzz_send.s); every guard
   branches to the `unimp` at 0x1370c:
   - branch 0x13638 (netlink.h:95, `beqz a0` after ___errno_location): traps when the errno
     address is NULL. ADDED: `errno_at regs <> 0`.
   - branch 0x13640 (netlink.h:95, `andi a1, a0, 3`): traps unless the errno address is 4-aligned.
     ADDED: `errno_at regs mod 4 = 0`.
     Both run only on the failing path; they are stated unconditionally, like the `wr_at` of errno,
     because errno is fixed by tp for the whole run.
   - branch 0x13684 (netlink.h:101, `bgeu a0, a3` with a3 = 17) and branch 0x136c8 (netlink.h:102,
     `bltu a3, a0` with a3 = 15): index guards on g_nl.n_sent. Branch 0x136bc (netlink.h:102,
     `addiw a2, a0, 1; blt a2, a0`): g_nl.n_sent++ overflow. ANSWERED BY THE PLAIN PREMISES:
     nlk_wf gives 0 <= n_sent <= 16, and all three sit behind the `n_sent < 16` test
     (`blt a2, a0` with a2 = 15 at +0x88), so n_sent <= 15 there.
   - branch 0x1369c (netlink.h:101) and branch 0x136e0 (netlink.h:102): pointer-sum guards on
     g_nl + 0x40224 + 512 n_sent and g_nl + 0x42228 + 8 n_sent, constant addresses far below
     2^64; they cannot be taken. No premise.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_SEND : Z := 0x135e4.
Lemma FUZZ_SEND_is_entry : FUZZ_SEND = P_fuzz_send. Proof. reflexivity. Qed.

Definition fuzz_send_contract : Prop :=
  leaf FUZZ_SEND 32
    (fun regs m => exists bs req, nlk_at m bs /\ frame_apart_gnl regs 32 /\ nlk_wf bs
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 32 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ bytes_at rsegs m (arg regs 1) req /\ Z.of_nat (length req) = arg regs 2
       /\ 0 <= arg regs 2 <= NL_SENT_LEN
       /\ apart_gnl (arg regs 1) (arg regs 2)
       /\ apart_frame regs 32 (arg regs 1) (arg regs 2)
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0)
    (fun regs m => [(A_G_NL + NK_SEND_ERRNO, A_G_NL + NK_N_SENT + 4);
                    (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' => forall bs req, nlk_at m bs ->
       bytes_at rsegs m (arg regs 1) req -> Z.of_nat (length req) = arg regs 2 ->
       exists bs', nlk_at m' bs'
       /\ nlk_wf bs'
       /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_end_errno bs' = nk_end_errno bs
       /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
       /\ nk_closed bs' = nk_closed bs
       /\ nk_misuse bs' =
            (if (arg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
       /\ (nk_send_errno bs <> 0 ->
             getr regs' 10 = wz (-1) /\ nk_send_errno bs' = 0
             /\ u32_at m' (errno_at regs) (nk_send_errno bs)
             /\ nk_n_sent bs' = nk_n_sent bs /\ nk_sent bs' = nk_sent bs)
       /\ (nk_send_errno bs = 0 ->
             getr regs' 10 = getr regs 12 /\ nk_send_errno bs' = 0
             /\ nk_sent bs' = owe (nk_sent bs) req
             /\ nk_n_sent bs' = Z.of_nat (length (owe (nk_sent bs) req)))).

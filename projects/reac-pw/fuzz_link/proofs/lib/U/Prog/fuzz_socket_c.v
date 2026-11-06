(* fuzz_socket (netlink.h:72-87), UBSAN build: the fake socket(). It hands out NL_FD = 7, or fails
   once with the errno the input chose.

   The twin of lib/Prog/fuzz_socket_c.v, with its premises, its Post, and the premises the UBSan
   guards below need. The three arguments are dead. The function reads g_nl.socket_errno: when it
   is not 0 it puts it in errno, clears it and answers -1; otherwise it notes a second open as
   misuse, marks the socket open, counts the open and answers 7. K = 32 (own frame of 32;
   ___errno_location, called as __errno_location at 0x17638, uses no stack).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/fuzz_socket.s); every guard
   branches to the `unimp` at 0x135e0:
   - branch 0x1356c (netlink.h:78, `beqz a0` after ___errno_location): traps when the errno
     address is NULL. ADDED: `errno_at regs <> 0`.
   - branch 0x13574 (netlink.h:78, `andi a1, a0, 3`): traps unless the errno address is 4-aligned.
     ADDED: `errno_at regs mod 4 = 0`.
     Both run only on the failing path; they are stated unconditionally, like the `wr_at` of errno,
     because errno is fixed by tp for the whole run.
   - branch 0x135c0 (netlink.h:85, `addiw a0, a1, 1; blt a0, a1`): traps when g_nl.opened++
     overflows int. Answered by `nk_opened bs + 1 < 2 ^ 31`, which the plain twin now also has.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_SOCKET : Z := 0x13540.
Lemma FUZZ_SOCKET_is_entry : FUZZ_SOCKET = P_fuzz_socket. Proof. reflexivity. Qed.

Definition fuzz_socket_contract : Prop :=
  leaf FUZZ_SOCKET 32
    (fun regs m => exists bs, nlk_at m bs /\ frame_apart_gnl regs 32 /\ nlk_wf bs /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 32 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ nk_opened bs + 1 < 2 ^ 31
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0)
    (fun regs m => [(A_G_NL + NK_SOCKET_ERRNO, A_G_NL + NK_MISUSE + 4);
                    (errno_at regs, errno_at regs + 4)])
    (fun regs m regs' m' => forall bs, nlk_at m bs -> exists bs', nlk_at m' bs'
       /\ nlk_wf bs'
       /\ nk_send_errno bs' = nk_send_errno bs /\ nk_end_errno bs' = nk_end_errno bs
       /\ nk_closed bs' = nk_closed bs
       /\ (nk_socket_errno bs <> 0 ->
             getr regs' 10 = wz (-1) /\ nk_socket_errno bs' = 0
             /\ u32_at m' (errno_at regs) (nk_socket_errno bs)
             /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
             /\ nk_misuse bs' = nk_misuse bs)
       /\ (nk_socket_errno bs = 0 ->
             getr regs' 10 = wz NL_FD /\ nk_socket_errno bs' = 0
             /\ nk_open bs' = 1 /\ nk_opened bs' = nk_opened bs + 1
             /\ nk_misuse bs' = (if nk_open bs =? 0 then nk_misuse bs else 1))).

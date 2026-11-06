(* fuzz_recv (netlink.h:107-137), UBSAN build: the fake recv(). It hands out the next queued chunk
   whole, or fails with the errno the input chose once the queue is empty.

   The twin of lib/Prog/fuzz_recv_c.v, with its premises, its Post, and the premises the UBSan
   guards below need. a0 = fd, a1 = buf, a2 = len; the flags argument is dead. A call on anything
   but the open NL_FD is misuse. Past the chunk it writes zeros to the next 4-byte boundary and then
   whole NLMSG_ERROR messages of -ENOTRECOVERABLE (+0x134 to +0x190: length 0x24, type 2, code
   0xffffff7d). THE WEAKEST FORM THE CALLER NEEDS, as in the plain twin: the contract says only that
   the chunk is at the front of the buffer and the rest of the buffer holds some bytes.
   K = 112 (own frame of 112; memcpy, memset and ___errno_location, called as __errno_location at
   0x17638, use no stack).
   UBSan guards (link/donors/ubsan-checks.tsv, link/ct/dis/ubsan/fuzz_recv.s); every guard
   branches to the `unimp` at 0x13910:
   - branch 0x138b0 (netlink.h:113, `beqz a0` after ___errno_location): traps when the errno
     address is NULL. ADDED: `errno_at regs <> 0`.
   - branch 0x138b8 (netlink.h:113, `andi a1, a0, 3`): traps unless the errno address is 4-aligned.
     ADDED: `errno_at regs mod 4 = 0`.
     Both run only on the empty-queue path; they are stated unconditionally, like the `wr_at` of
     errno, because errno is fixed by tp for the whole run.
   - branch 0x137ec (netlink.h:126, `add a0, s2, s1; bltu a0, s1`): traps when buf + n passes
     2^64 - 1, n = min(chunk_len, len). rw_cells gives only buf + len <= 2^64, and n = len is
     possible (a chunk of 4096 bytes and len = 4096), so ADDED: `arg regs 1 + arg regs 2 < 2 ^ 64`.
   - branch 0x137fc (netlink.h:126, `snez; seqz; xor; beqz`) and branch 0x13858 (netlink.h:131,
     the same test on b + o): trap when exactly one of buf and the sum is NULL. ADDED:
     `arg regs 1 <> 0` (with the bound above, no sum is then 0).
   - branch 0x1384c (netlink.h:131, b + o), 0x1387c (netlink.h:133, b + o + 4) and 0x13888
     (netlink.h:134, b + o + 16): trap when the sum passes 2^64 - 1. The loop runs only while
     o + 36 <= len, so all three are below buf + len; answered by the bound above.
   - branch 0x13790 (netlink.h:116, `bgeu a0, 64`): index guard on chunk_len[next]. ANSWERED BY THE
     PLAIN PREMISES: on that path next < n_chunks <= 64 (nlk_wf).
   - branch 0x137a4 (netlink.h:116) and branch 0x137d0 (netlink.h:119): pointer-sum guards on
     g_nl + 0x40000 + 8 next and g_nl + 4096 next, constant addresses far below 2^64; they cannot
     be taken. No premise.
   Entry and frame read from the ubsan image (the unstripped twin of the pin 9b4e4a5746dc,
   link/donors/premises-ubsan.txt); the stack bound K is the function's own frame plus the deepest
   frame of every callee it can reach on the path this contract covers. 
   THE BUFFER STAYS READABLE ON EVERY PATH (LinkLib's L8, 2026-10-30): the Post says the whole
   buffer is still `rw_cells`, on the failure path too. The write set names the buffer on every
   path, but the failure arm (n_chunks <= next) said nothing of it, and nl_talk's buffer is its own
   frame (sp+24, 16384 bytes; calls at 0x160c4 and 0x16120): after a failing recv nl_talk could
   not show its frame readable, so it could not release it (stk_release needs rw_cells). True of
   the binary: the failure arm returns -1 before touching the buffer. The same class as L6.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition FUZZ_RECV : Z := 0x13710.
Lemma FUZZ_RECV_is_entry : FUZZ_RECV = P_fuzz_recv. Proof. reflexivity. Qed.

Definition fuzz_recv_contract : Prop :=
  leaf FUZZ_RECV 112
    (fun regs m => exists bs junk, nlk_at m bs /\ frame_apart_gnl regs 112 /\ nlk_wf bs
       /\ wr_at rsegs m (errno_at regs) 4
       /\ apart_frame regs 112 (errno_at regs) 4 /\ apart_gnl (errno_at regs) 4
       /\ NL_CHUNK_MAX <= arg regs 2
       /\ rw_cells rsegs m (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk]
       /\ apart_gnl (arg regs 1) (arg regs 2)
       /\ apart_frame regs 112 (arg regs 1) (arg regs 2)
       /\ errno_at regs <> 0 /\ errno_at regs mod 4 = 0
       /\ arg regs 1 <> 0 /\ arg regs 1 + arg regs 2 < 2 ^ 64)
    (fun regs m => [(A_G_NL + NK_NEXT, A_G_NL + NK_MISUSE + 4);
                    (errno_at regs, errno_at regs + 4);
                    (arg regs 1, arg regs 1 + arg regs 2)])
    (fun regs m regs' m' => forall bs, nlk_at m bs -> exists bs', nlk_at m' bs'
       /\ nlk_wf bs'
       /\ nk_n_chunks bs' = nk_n_chunks bs /\ nk_end_errno bs' = nk_end_errno bs
       /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_send_errno bs' = nk_send_errno bs
       /\ nk_chunks bs' = nk_chunks bs
       /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
       /\ nk_closed bs' = nk_closed bs /\ nk_n_sent bs' = nk_n_sent bs
       /\ nk_misuse bs' =
            (if (arg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
       /\ (nk_n_chunks bs <= nk_next bs ->
             getr regs' 10 = wz (-1) /\ nk_next bs' = nk_next bs
             /\ u32_at m' (errno_at regs) (nk_end_errno bs))
       /\ (nk_next bs < nk_n_chunks bs ->
             let c := nk_chunk bs (nk_next bs) in
             getr regs' 10 = wz (Z.of_nat (length c)) /\ nk_next bs' = nk_next bs + 1
             /\ exists rest, bytes_at rsegs m' (arg regs 1) (c ++ rest)
                /\ Z.of_nat (length rest) = arg regs 2 - Z.of_nat (length c))
       /\ exists junk, rw_cells rsegs m' (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk]).

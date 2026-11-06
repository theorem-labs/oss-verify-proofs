(* fuzz_recv (netlink.h:107-137) on image A (fuzz_link.asan 0x823cc, 688 bytes; listing
   (internal path) (internal record, sha256 549eae89aefb)): the fake recv(). It hands out the
   next queued chunk whole, or fails with the errno the input chose once the queue is empty. a0 = fd, a1 = buf,
   a2 = len; the flags argument is dead. The plain contract is lib/Prog/fuzz_recv_c.v; this file states the SAME
   link_spec result in link_amem.v's `aleaf` form, and adds the buffer conjunct of AMEND-lib L8.

   The image-A code, in order:
     +0x00..+0x2c  push a 96-byte frame; save ra, s0..s9;  +0x30 s0 := len;  +0x34 s1 := buf
     +0x38..+0x3c  a3 := LA_GOT_SHADOW's content;  +0x44..+0x48 a1 := LA_G_NL
     +0x4c  bne a0, 7 -> +0x60;  +0x58 lw open;  +0x5c bnez -> +0x70;  +0x6c sw 1, 0x220   misuse := 1 unless
            a0 = 7 and open <> 0
     +0x74..+0x80  a4 := g + 0x40000; a5 := lw 0x200 = n_chunks; a2 := lw 0x204 = next; s3 := the shadow base
     +0x84  bge a2, a5 -> +0x21c                                      (queue empty: the failure arm)
     chunk arm (next < n_chunks):
     +0x88..+0x90  a0 := g + 0x40000 + 8 * next (chunk_len[next])
     +0x94..+0xa0  the instrumented check of the 8-byte load of chunk_len[next]: shadow byte (lbu) <> 0 goes to
                   errpath_load8 (0x5a4fc) at once
     +0xa4  ld s2, 0(a0);  +0xa8..+0xac  s2 := len if s2 >= len (unsigned)
     +0xc0  sw next + 1, 0x204                                         next := next + 1
     +0xc4..+0xd0  checked_memcpy(buf, g + 4096 * next, s2) (0x52d78)
     +0xd4..+0xe4  s4 := (s2 + 3) rounded down to 4, or len if that is not below len
     +0xe8..+0xf4  checked_memset(buf + s2, 0, s4 - s2) (0x53214)
     +0xf8..+0x1c8  while s4 + 36 <= len: checked_memset(buf + s4 + 6, 0, 30), then the 36-byte NLMSG_ERROR
                   header in place by byte stores (+0x14c..+0x158 length 0x24, +0x184..+0x188 type 2, +0x1b8..+0x1c4
                   code 0xffffff7d), each 4- or 2-byte group behind the instrumented check of its first and last
                   byte (s = 0, or (a & 7) < s; else errpath_store_n 0x5a9fc with the size), s4 += 36
     +0x23c  a0 := s2
     failure arm (+0x21c): s0 := lw 0x208 = end_errno; +0x220 jal ___errno_location (a0 := tp - 164);
     +0x224..+0x230, +0x274..+0x27c  the instrumented check of the 4-byte store to a0 (errpath_store4 0x5a77c);
     +0x234 sw s0, 0(a0)  errno := end_errno;  +0x238 s2 := -1;  +0x23c a0 := s2
     +0x240..+0x270  restore, pop, ret.
   0x40200 = NK_N_CHUNKS, 0x40204 = NK_NEXT, 0x40208 = NK_END_ERRNO, 0x40000 = NK_CHUNK_LEN, 4096 * i = the chunk
   (link_spec.v:706-716).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x2c; the calls +0xd0, +0xf4, +0x120 take
     ecall_pre-style premises at sp - 96 that the walk derives from the journal; +0x270 ret.
   - K = 96 + ESTACK = 4192: the 96-byte frame, then the window of checked_memcpy / checked_memset
     (Reusable/YG0d.v aintrin_realizes over ecall_pre); ___errno_location pushes nothing. No realignment.
     link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5: 4192. The plain K (80) does not carry over.
   - `exists bs, anlk_at m LA_G_NL bs`: the loads +0x58, +0x78, +0x7c, +0xa4, +0x21c and the stores +0x6c, +0xc0;
     checked_memcpy's source bytes visible (`src_ok`).
   - `nlk_wf bs`: carried for the Post's `nlk_wf bs'`; it bounds next <= n_chunks <= 64 and each chunk_len by 4096,
     so with `NL_CHUNK_MAX <= len` the clamp +0xa8 keeps s2 = chunk_len and the answer is the chunk's length.
   - g_nl's shadow (slice convention C2): `range_addressable (ard m) SHADOW_OFF LA_G_NL NK_SIZE`: the check
     +0x94..+0xa0 (an aligned 8-byte granule: shadow byte 0) and checked_memcpy's source check on
     [g + 4096 next, + s2); `shadow_hull_vis (ard m) LA_G_NL NK_SIZE`: checked_memcpy's source hull.
   - buf: `0 < buf` (the U twin's `buf <> 0`; checked_memcpy's dest is never NULL, and the write set below needs no
     aivl); `abuf m buf len`: checked_memcpy / checked_memset's dest writable (`dest_ok`) and the byte stores of
     the trailing messages; `NL_CHUNK_MAX <= len` (the plain premise: the chunk fits whole);
     `amem_range buf len`: the dest range of every checked call and `d + n <= 2 ^ 63`;
     `range_addressable (ard m) SHADOW_OFF buf len`: the dest checks of the three checked calls and the
     instrumented store checks of the trailing headers (all inside [buf, buf + len), since s4 <= len);
     `shadow_hull_vis (ard m) buf len`: the dest hulls; `apart_gnl LA_G_NL buf len`: checked_memcpy's
     `d + n <= x \/ x + n <= d`, and the Post reads g_nl after buf is written; `apart_frame regs K buf len`: the
     frame stores and the callees' windows do not touch buf (`dest_ok`).
   - errno (slice convention C1): `as_errno B = as_tp B - 164`, `awrange m (as_errno B) 4` (+0x234),
     `range_addressable (ard m) SHADOW_OFF (as_errno B) 4` (the check +0x224..+0x230), `apart_frame regs K
     (as_errno B) 4`, `apart_gnl LA_G_NL (as_errno B) 4`.
   - the write set [(LA_G_NL + NK_NEXT, LA_G_NL + NK_MISUSE + 4); (buf, buf + len)] and apre's `ajw` on it: the
     stores +0x6c, +0xc0 (g_nl: `inG G`), and the checked calls and byte stores into buf (in a run, nl_talk's
     receive buffer in its class-9 side frame: `in_frames own`).
   - registers: +0x23c a0 := s2 (the chunk's length, or -1).
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   The Post: the plain Post over the A views, and on BOTH arms `abuf m' buf len`, the buffer still readable and writable (AMEND-lib
   L8, link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 6a: nl_talk's buffer is in its own frame, which it
   releases after a failing recv too; `akept` excepts the write set, so without this the caller knows nothing of buf after the call).
   It is true of the code: the failure arm writes no byte of buf, the chunk arm writes bytes into it. Like the plain Post it does
   not state the trailing NLMSG_ERROR messages (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 3 item 2).

   What does NOT carry over from the plain text:
   - errno in the write set (as fuzz_socket_c.v: `ajw` holds of no errno byte; the journal and `akept` except
     [as_errno B, as_errno B + 4)).
   - `frame_apart_gnl regs 80` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a).
   - `errno_at regs` is restated as `as_errno B` with the premise tying the two.

   Satisfiability witness (a run; lib/A/Prog/kernel_witness.v `fuzz_recv_apre_sat` closes the function-specific
   part): nl_talk's call after its fuzz_send, in the run of kernel_c.v's witness (op_read): a0 = 7, a1 = nl_talk's
   receive buffer at its class-9 side frame + 0x20 (shadow 0 after frame_alloc_9 and nl_talk's unpoisoning),
   a2 = 0x4000 (nl_talk +0x1ec `lui a2, 4`); g_nl with n_chunks = 1 (the reply kernel() queued: chunk_len[0] = 40),
   next = 0, open = 1, n_sent = 1; g_nl's object shadow 0; errno at TFIB_ERRNO = 0x631b6c.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_RECV_A : Z := 0x823cc.
Lemma FUZZ_RECV_A_is_entry : FUZZ_RECV_A = LA_fuzz_recv. Proof. reflexivity. Qed.

(* the stack bound on image A: the 96-byte frame and the window of checked_memcpy / checked_memset *)
Definition FUZZ_RECV_AFRAME : Z := 96.
Definition FUZZ_RECV_AK : Z := FUZZ_RECV_AFRAME + ESTACK.
Lemma FUZZ_RECV_AK_val : FUZZ_RECV_AK = 4192. Proof. reflexivity. Qed.

(* the write set: g_nl's next .. misuse words and the buffer (as the plain contract's, without errno) *)
Definition fuzz_recv_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL + NK_NEXT, LA_G_NL + NK_MISUSE + 4);
   (aarg regs 1, aarg regs 1 + aarg regs 2)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition fuzz_recv_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs, anlk_at segs m LA_G_NL bs /\ nlk_wf bs
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE
    /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    /\ as_errno B = as_tp B - 164
    /\ awrange segs m (as_errno B) 4
    /\ range_addressable (ard segs m) SHADOW_OFF (as_errno B) 4
    /\ apart_frame regs FUZZ_RECV_AK (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4
    /\ NL_CHUNK_MAX <= aarg regs 2
    /\ 0 < aarg regs 1 /\ abuf segs m (aarg regs 1) (aarg regs 2)
    /\ amem_range (aarg regs 1) (aarg regs 2)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 1) (aarg regs 2)
    /\ shadow_hull_vis (ard segs m) (aarg regs 1) (aarg regs 2)
    /\ apart_gnl LA_G_NL (aarg regs 1) (aarg regs 2)
    /\ apart_frame regs FUZZ_RECV_AK (aarg regs 1) (aarg regs 2).

Definition fuzz_recv_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (forall bs, anlk_at segs m LA_G_NL bs -> exists bs', anlk_at segs m' LA_G_NL bs'
    /\ nlk_wf bs'
    /\ nk_n_chunks bs' = nk_n_chunks bs /\ nk_end_errno bs' = nk_end_errno bs
    /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_send_errno bs' = nk_send_errno bs
    /\ nk_chunks bs' = nk_chunks bs
    /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
    /\ nk_closed bs' = nk_closed bs /\ nk_n_sent bs' = nk_n_sent bs
    /\ nk_misuse bs' =
         (if (aarg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
    /\ (nk_n_chunks bs <= nk_next bs ->
          getr regs' 10 = w64 (-1) /\ nk_next bs' = nk_next bs
          /\ au32_at segs m' (as_errno B) (nk_end_errno bs))
    /\ (nk_next bs < nk_n_chunks bs ->
          let c := nk_chunk bs (nk_next bs) in
          getr regs' 10 = w64 (Z.of_nat (length c)) /\ nk_next bs' = nk_next bs + 1
          /\ exists rest, abytes segs m' (aarg regs 1) (c ++ rest)
             /\ Z.of_nat (length rest) = aarg regs 2 - Z.of_nat (length c)))
  /\ abuf segs m' (aarg regs 1) (aarg regs 2).

Definition fuzz_recv_acontract : Prop :=
  aleaf SK segs rlo rhi B FUZZ_RECV_A FUZZ_RECV_AK 0 [] fuzz_recv_apre fuzz_recv_awr fuzz_recv_apost.

End c.

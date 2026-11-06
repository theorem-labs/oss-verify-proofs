(* fuzz_send (netlink.h:89-105) on image A (fuzz_link.asan 0x82290, 316 bytes; listing
   (internal path) (internal record, sha256 a64d77d6e373)): the fake send(). It keeps the
   request for the harness to read, or fails once with the errno the input chose. a0 = fd, a1 = buf, a2 = len; the flags
   argument is dead. The plain contract is lib/Prog/fuzz_send_c.v; this file states the SAME link_spec result in
   link_amem.v's `aleaf` form.

   The image-A code, in order:
     +0x00..+0x14  push a 48-byte frame; save ra, s0..s3;  +0x18 s0 := a2 (len)
     +0x1c..+0x20  a2 := LA_GOT_SHADOW's content (LA_SHADOW_CELL);  +0x28..+0x2c s1 := LA_G_NL
     +0x30  bne a0, 7 -> +0x44 (the whole 64-bit a0);  +0x3c lw open (g + 0x40214);  +0x40 bnez -> +0x54
     +0x50  sw 1, 0x220 (g + 0x40000)       misuse := 1 unless a0 = 7 and open <> 0
     +0x5c  lw s3, 0x210 = send_errno;  +0x60 s2 := the shadow base;  +0x64 beqz s3 -> +0x94
     errno arm (send_errno <> 0):
     +0x68  jal ___errno_location (0x90a7c): a0 := tp - 164
     +0x6c..+0x78, +0x128..+0x130  the instrumented check of the 4-byte store to a0 (s = 0, or (a0 & 7) + 3 < s;
                   else errpath_store4 0x5a77c)
     +0x7c  sw s3, 0(a0)  errno := send_errno;  +0x88 sw zero, 0x210  send_errno := 0;  +0x8c s0 := -1; j +0x108
     ok arm (send_errno = 0):
     +0x94..+0x9c  a0 := lw (g + 0x422a8) = n_sent;  +0xa4 blt 15, a0 -> +0x108 (ring full: record nothing)
     +0xa8..+0xb4  a2 := len if len < 512 (unsigned), else 512
     +0xb8..+0xc8  a0 := g + 0x40224 + 512 * n_sent;  +0xcc checked_memcpy(a0, buf, a2) (0x52d78)
     +0xd0..+0xec  a2 := lw n_sent; +0xec sw n_sent + 1;  a0 := g + 0x42228 + 8 * n_sent
     +0xf4..+0x100  the instrumented check of the 8-byte store to a0: shadow byte (lbu) <> 0 goes to errpath_store8
                   (0x5a81c) at once, so it passes only when the shadow byte is 0
     +0x104  sd s0, 0(a0)  sent_len[n_sent] := len
     +0x108  a0 := s0;  +0x10c..+0x124 restore, pop, ret.
   0x40000 + 0x210 = NK_SEND_ERRNO, 0x40224 = NK_SENT, 0x42228 = NK_SENT_LEN, 0x422a8 = NK_N_SENT
   (link_spec.v:712-719).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x14; the call +0xcc takes ecall_pre-style
     premises at sp - 48 that the walk derives from the journal; +0x124 ret.
   - K = 48 + ESTACK = 4144: the 48-byte frame, then checked_memcpy's window [sp' - ESTACK, sp') at sp' = sp - 48
     (Reusable/YG0d.v aintrin_realizes over ecall_pre); ___errno_location pushes nothing. No realignment.
     link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5: 4144. The plain K (48) does not carry over.
   - `exists bs, anlk_at m LA_G_NL bs`: the loads +0x3c, +0x5c, +0x9c, +0xd8 and the stores +0x50, +0x88, +0xec,
     +0x104; checked_memcpy's dest bytes writable (`dest_ok`).
   - `nlk_wf bs`: carried for the Post's `nlk_wf bs'`; it bounds n_sent by 16 and each sent_len by 512.
   - `abytes m buf req`, `length req = len`, `0 <= len <= NL_SENT_LEN`: checked_memcpy reads [buf, buf + len) (len
     <= 512, so +0xb0 keeps a2 = len) (`src_ok`); the Post's `owe` names those bytes.
   - `amem_range buf len`, `range_addressable (ard m) SHADOW_OFF buf len`, `0 < len -> shadow_hull_vis (ard m) buf
     len`: checked_memcpy's source checks (YG0d.v aintrin_realizes OCpy: `0 <= x`, `x + n <= 2 ^ 63`, amem_range,
     range_addressable, shadow_hull_vis).
   - g_nl's shadow (slice convention C2): `range_addressable (ard m) SHADOW_OFF LA_G_NL NK_SIZE`: checked_memcpy's
     dest check on [g + NK_SENT + 512 n, + len) and the check +0xf4..+0x100 of sent_len[n] (an aligned 8-byte
     granule, so range_addressable gives its shadow byte 0, YG0v.v saddr_ok); `shadow_hull_vis (ard m) LA_G_NL
     NK_SIZE`: checked_memcpy's dest hull. amem_range of the dest is a closed fact (g_nl ends below kLowMemEnd).
   - `apart_gnl LA_G_NL buf len`: checked_memcpy's `d + n <= x \/ x + n <= d`, and the Post reads the request after the
     ring is written (the plain separation, link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 5).
   - `apart_frame regs K buf len`: the frame stores do not touch the request, and checked_memcpy's source is outside
     its window (`src_ok`).
   - errno (slice convention C1, link-a/contracts/kernel.md (internal record, sha256 977f60b79b94)): `as_errno B = as_tp B - 164`
     (+0x68 answers tp - 164), `awrange m (as_errno B) 4` (+0x7c), `range_addressable (ard m) SHADOW_OFF (as_errno B) 4`
     (the check +0x6c..+0x78), `apart_frame regs K (as_errno B) 4`, `apart_gnl LA_G_NL (as_errno B) 4`.
   - the write set [LA_G_NL + NK_SEND_ERRNO, LA_G_NL + NK_N_SENT + 4) and apre's `ajw` on it: the stores +0x50, +0x88,
     +0xec, +0x104 and checked_memcpy's dest bytes (inside g_nl.sent). Image bytes: `ajw` holds of them through `inG G`
     (LA_G holds all of g_nl). The store of checked_memcpy into G is lifted onto the journal by link_ajkit.v aj_gx_intrin_at
     (slice convention C3; link-a/form/FORM.md (internal record, sha256 13aeff774164) section 10 question 9).
   - registers: +0x108 a0 := s0 = the whole a2 of the call, or -1 (the Post's result).
   - the read set `fuzz_send_ard` = the request's bytes [buf, buf + len), and aleaf_rd's premise that each is a
     byte `akept` keeps (`akb`): checked_memcpy reads them (+0xcc), and the Post's `owe (nk_sent bs) req` names the
     bytes the Pre read. Without it the request may lie in a free side frame or a free heap range, which the Pre's
     byte and shadow facts do not exclude (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 11;
     link_amem.v: nl_talk's frame_alloc_9 at 0x889f8 writes its fresh frame before fuzz_send reads req). In a run the
     request is nl_talk's a0 (nl_talk +0x74, +0x1bc; the call +0x1c8): a buffer in reac_link_alias_read's class-1 side
     frame (alias_read +0x180) or in reac_link_alias_write's class-3 side frame (alias_write +0x1f4), a frame of Sc:
     `akb`'s frame clause (the kernel comparer, 2026-10-30).
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   What does NOT carry over from the plain text:
   - errno in the write set (as fuzz_socket_c.v: `ajw` holds of no errno byte; the journal and `akept` except
     [as_errno B, as_errno B + 4)).
   - `frame_apart_gnl regs 48` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a: the window is on
     the real stack above alloc_ceiling, g_nl is an image byte).
   - `errno_at regs` is restated as `as_errno B` with the premise tying the two.

   Satisfiability witness (a run; lib/A/Prog/kernel_witness.v `fuzz_send_apre_sat` closes the function-specific part): nl_talk's
   call +0x1c8 after fuzz_socket answered 7, in the run of link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f)
   section 1 (op_read): a0 = 7, a1 = the 32-byte RTM_GETLINK request (nlmsghdr + ifinfomsg) that reac_link_alias_read
   built in its class-1 side frame and passed to nl_talk, a2 = 32; g_nl with open = 1, n_sent = 0, send_errno = 0; the
   request's shadow 0 (alias_read clears it, +0x184..+0x190), g_nl's object shadow 0; errno at TFIB_ERRNO = 0x631b6c.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_SEND_A : Z := 0x82290.
Lemma FUZZ_SEND_A_is_entry : FUZZ_SEND_A = LA_fuzz_send. Proof. reflexivity. Qed.

(* the stack bound on image A: the 48-byte frame and checked_memcpy's window *)
Definition FUZZ_SEND_AFRAME : Z := 48.
Definition FUZZ_SEND_AK : Z := FUZZ_SEND_AFRAME + ESTACK.
Lemma FUZZ_SEND_AK_val : FUZZ_SEND_AK = 4144. Proof. reflexivity. Qed.

(* the write set: g_nl's send_errno .. n_sent (as the plain contract's, without errno: see the header) *)
Definition fuzz_send_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL + NK_SEND_ERRNO, LA_G_NL + NK_N_SENT + 4)].

(* the read set: the request's bytes [buf, buf + len) *)
Definition fuzz_send_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  rd_ivl (aarg regs 1) (aarg regs 1 + aarg regs 2) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition fuzz_send_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs req, anlk_at segs m LA_G_NL bs /\ nlk_wf bs
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE
    /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    /\ as_errno B = as_tp B - 164
    /\ awrange segs m (as_errno B) 4
    /\ range_addressable (ard segs m) SHADOW_OFF (as_errno B) 4
    /\ apart_frame regs FUZZ_SEND_AK (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4
    /\ abytes segs m (aarg regs 1) req /\ Z.of_nat (length req) = aarg regs 2
    /\ 0 <= aarg regs 2 <= NL_SENT_LEN
    /\ amem_range (aarg regs 1) (aarg regs 2)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 1) (aarg regs 2)
    /\ (0 < aarg regs 2 -> shadow_hull_vis (ard segs m) (aarg regs 1) (aarg regs 2))
    /\ apart_gnl LA_G_NL (aarg regs 1) (aarg regs 2)
    /\ apart_frame regs FUZZ_SEND_AK (aarg regs 1) (aarg regs 2).

Definition fuzz_send_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs req, anlk_at segs m LA_G_NL bs ->
    abytes segs m (aarg regs 1) req -> Z.of_nat (length req) = aarg regs 2 ->
    exists bs', anlk_at segs m' LA_G_NL bs'
    /\ nlk_wf bs'
    /\ nk_socket_errno bs' = nk_socket_errno bs /\ nk_end_errno bs' = nk_end_errno bs
    /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
    /\ nk_closed bs' = nk_closed bs
    /\ nk_misuse bs' =
         (if (aarg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1)
    /\ (nk_send_errno bs <> 0 ->
          getr regs' 10 = w64 (-1) /\ nk_send_errno bs' = 0
          /\ au32_at segs m' (as_errno B) (nk_send_errno bs)
          /\ nk_n_sent bs' = nk_n_sent bs /\ nk_sent bs' = nk_sent bs)
    /\ (nk_send_errno bs = 0 ->
          getr regs' 10 = getr regs 12 /\ nk_send_errno bs' = 0
          /\ nk_sent bs' = owe (nk_sent bs) req
          /\ nk_n_sent bs' = Z.of_nat (length (owe (nk_sent bs) req))).

Definition fuzz_send_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B FUZZ_SEND_A FUZZ_SEND_AK 0 [] fuzz_send_apre fuzz_send_ard fuzz_send_awr
    fuzz_send_apost.

End c.

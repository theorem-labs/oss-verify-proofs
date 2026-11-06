(* nl_talk (reac_link_alias.c:37-93) on image A (fuzz_link.asan 0x88974, 1504 bytes; listing
   (internal path) (internal record, sha256 628c2741aace)): the library sends one request and
   reads the answer until its ACK or its RTM_NEWLINK. a0 = req, a1 = len, a2 = kind, a3 = kind_n, a4 = alias,
   a5 = alias_n. The plain contract is lib/Prog/nl_talk_c.v; this file states the SAME link_spec result (`talk_core`:
   the code `talk_rc_lib`, the attributes `talk_attrs`, the state `talk_after`) in the read-set form `aleaf_rd`.

   The image-A code, in order:
     +0x00..+0x38  push a 192-byte frame (+0x04 `sd zero, 0(sp)` probes it); save ra, s0..s11
     +0x3c  s0 := the entry sp;  +0x40 `andi sp, sp, -0x20`: sp realigned down by 0 or 16;  +0x44 s1 := sp
     +0x50, +0x54  kind_n, kind spilled to 0x38(s1), 0x30(s1)
     +0x5c..+0x70  the side-stack switch (.got+0xb8 = 0xa1a28 -> 0xaa440) and the shadow base (.got+0x60 = 0xa19d0
                   -> 0xaa438, into s5)
     +0x78  `beqz a2` -> the real-stack arm +0x90..+0xbc (a 16672-byte frame carved below sp with probes)
     +0x7c..+0x84  frame_alloc_9(0x4120 = 16672) (0x3e15c): the class-9 side frame (32768 bytes), into s4 and s2
     +0x98  `bnez s4` skips the real-stack arm
     +0xc0..+0xe8  the frame's magic 0x41b58ab3, its descriptor 0x201ef and the pc 0x88974 stored at s2 + 0, 8, 16
     +0xf0..+0x19c  shadow of the frame: 0xf1 x 4 (left redzone [s2, s2 + 32)), meta_fill_f8(shadow + 4, 2048)
                   (0x55f94: the buffer [s2 + 32, s2 + 16416) marked unusable, out of scope), 0xf3 x 32 (right
                   redzone [s2 + 16416, s2 + 16672))
     +0x1a0..+0x1b0  fuzz_socket(16, 0x80003, 0) (0x821cc); +0x1b4 `bltz` -> +0x2cc
     +0x1bc..+0x1c8  fuzz_send(fd, req, len, 0) (0x82290); +0x1cc `bltz` -> +0x2ec
     +0x1d4..+0x1e8  meta_fill_00(shadow + 4, 2048) (0x55e74): the 16384-byte buffer at s10 = s2 + 32 usable
     +0x1ec..+0x200  fuzz_recv(fd, s10, 16384, 0) (0x823cc); +0x204 `bltz` -> +0x2ac; +0x294..+0x2a4 the next recv
     +0x208..+0x270  the message walk over the bytes recv answered (NLMSG_ERROR -> +0x4ac, RTM_NEWLINK -> +0x314)
     +0x314..+0x4a0  the attribute walk of the first RTM_NEWLINK: IFLA_IFALIAS (20) -> copy_attr(rta, alias,
                   alias_n) at +0x38c; IFLA_LINKINFO (18) -> the nested walk, IFLA_INFO_KIND (1) -> copy_attr(rta,
                   kind, kind_n) at +0x3f4 (0x89438); every attribute is visited, so a later one overwrites
     +0x2ac..+0x30c  the three failure arms: ___errno_location (0x90a7c), the instrumented check of the 4-byte load
                   of errno, rc := -errno (`negw`); the send arm closes the socket (+0x308)
     +0x4dc..+0x4f0  fuzz_close(fd) (0x8267c); meta_fill_f8(shadow + 4, 2048)
     +0x4f8..+0x500  the retired magic 0x45e0360e stored at s2
     +0x504..+0x514  `beqz s4` -> +0x51c (real-stack arm: meta_fill_00 of the 2084 shadow bytes); else
                   frame_release_9(s4, 16672) (0x3e2d4)
     +0x52c..+0x56c  a0 := rc; restore s0..s11, ra; pop; ret.

   THE RECEIVE BUFFER IS IN THE SIDE FRAME, NOT ON THE STACK. The plain frame held the 16384-byte buffer (plain K = 16592);
   here it is in the class-9 frame nl_talk takes and releases, so it is not in the write set and not in K. The real-stack
   arm (+0x90..+0xbc, +0x51c) is not taken under the premises (link-a/form/FORM.md (internal record, sha256 13aeff774164)
   section 4.2, the recorded answer 3): the switch cell holds 1 by AR's const law (asyms_ok.aso_const_law,
   Reusable/YG0f.v:194: `z4 (as_uar_cell B) 1`), and with `aside_room Sc [(9, 1)]` frame_alloc_9 returns frame_addr >= 4096
   (astack_malloc_realizes YG0d.v:292-307, stack_malloc_progressP YCbq.v:803-805, frames_bounds YCbq.v:447-450). The walk
   needs the class-9 widening of AsanAPI.aa_stack_malloc and the frame_alloc_9 / frame_release_9 contracts (the lib/A frame,
   link-a/form/FORM.md (internal record, sha256 13aeff774164) section 10 item 7; written new, from scene's class-8 files).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok, the window (apre): the frame stores +0x04..+0x38 lie in [sp - 192, sp); every
     callee runs at the realigned sp (>= sp - 208) with the premises of its own contract; +0x56c ret.
   - K = 192 + 16 + COPY_ATTR_AK = 8448: the frame, the realignment slack of +0x40, then the deepest callee window,
     copy_attr's 8240 (copy_attr_c.v). The other callees' windows are smaller: fuzz_recv 96 + ESTACK = 4192,
     fuzz_send 48 + ESTACK = 4144, fuzz_socket 32, fuzz_close 0, ___errno_location 0, frame_alloc_9 / meta_fill_* /
     frame_release_9 ESTACK (their released templates take ecall_pre: scene StackFreeDef.v astack_free_realizes,
     grant SetShadowDef.v aset_shadow_realizes). The plain K (16592) does not carry over.
   - SIDE = [(9, 1)]: nl_talk's own class-9 frame; none of its callees takes a side frame. EV = 0: frame_alloc_9 changes
     only the side stack (stack_malloc_post YG01.v:556-558: `exists f, s' = set_fs f s`).
   - `anlk_at m LA_G_NL kbs`, `nlk_wf kbs`, `nk_open kbs = 0`, `nk_opened kbs + 1 < 2 ^ 31`, `nk_closed kbs + 1 < 2 ^ 31`:
     the Pres of fuzz_socket (+0x1b0), fuzz_send (+0x1c8), fuzz_recv (+0x200, +0x2a4) and fuzz_close (+0x308, +0x4e0)
     and the Post's fields; the two bounds keep `opened + 1` and `closed + 1` exact.
   - `range_addressable (ard m) SHADOW_OFF LA_G_NL NK_SIZE` and `shadow_hull_vis (ard m) LA_G_NL NK_SIZE`: the Pres of
     fuzz_send and fuzz_recv (fuzz_send_c.v, fuzz_recv_c.v): their instrumented checks at
     variable offsets into g_nl (fuzz_send +0xf4, the 8-byte store into the length ring) and checked_memcpy's
     destination in g_nl's ring. On image A both hold at every state by AR (zshadow_ok, YG0n.v:190, with the
     instance's as_zero_shadow, lib/A/AF0m.v Tfib_zero_shadow row (0xa6d60, 0x61f138 - 0xa6d60), which holds g_nl;
     the shadow is mapped), so a caller states them at once and the walk carries them across a callee.
   - errno: `as_errno B = as_tp B - 164` (what ___errno_location returns; AF0m.v TFIB_ERRNO = TFIB_TP - 0xa4),
     `awrange m (as_errno B) 4` (the store of fuzz_socket / fuzz_send / fuzz_recv on failure; the loads +0x2c0,
     +0x2e0, +0x300), `range_addressable (ard m) SHADOW_OFF (as_errno B) 4` (the checks +0x2b0..+0x2bc,
     +0x2d0..+0x2dc, +0x2f0..+0x2fc and the callees' store checks; AF0m.v row (0x631300, IMG_TOP - 0x631300) holds
     errno 0x631b6c), apart from the frame, g_nl and both buffers (the plain separations).
   - `abytes m req r`, `length r = len`, `0 <= len <= NL_SENT_LEN`, `amem_range req len`, `range_addressable` of
     [req, req + len) and its `shadow_hull_vis`: fuzz_send's checked_memcpy of the request into g_nl's ring (its
     source, YG0d.v:332-333); `apart_frame regs K req len`, `apart_gnl`: the frame stores and the ring write do not
     touch it.
   - the READ SET [req, req + len) (`nl_talk_ard`) and aleaf_rd's `akb` on it: frame_alloc_9 (+0x84) changes the
     runtime's bytes, and +0xe0..+0x19c store into the frame it hands out and into that frame's shadow, BEFORE
     fuzz_send reads req at +0x1c8. A free class-9 frame is visible memory, with zero shadow if it was never used, so
     without `akb` a req inside the frame frame_alloc_9 is about to hand out meets every other premise and the Post's
     `nk_sent kbs' = owe .. req` is false. `akb` puts req where akept keeps it (a block, a live side frame, the image,
     the real-stack row [ly_stk_lo, ly_stk_hi) outside [sp - K, sp)), which is disjoint from a free frame. At its callers req is
     the request in reac_link_alias_read's class-1 frame or reac_link_alias_write's class-3 frame: a live frame.
   - the buffers: `abuf_arg m kind kind_n`, `abuf_arg m alias alias_n` and, when the buffer is there,
     `amem_range`, `range_addressable` and `shadow_hull_vis` over it: copy_attr's Pre at +0x38c and +0x3f4
     (copy_attr_c.v: `abuf`, `amem_range`, `range_addressable`, `shadow_hull_vis` of out);
     `apart_frame regs K kind kind_n`: copy_attr's `apart_frame regs COPY_ATTR_AK out n` at the realigned sp;
     `apart kind kind_n alias alias_n`: a copy into one keeps the other's text (the Post); `apart_gnl`, apart from
     errno: the callees' g_nl and errno stores keep the buffers. copy_attr's `apart out n (a + 4) (l - 4)` (the
     attribute is in nl_talk's fresh frame) follows from apre's `ajw` on the write set: each buffer byte is a byte the
     journal lets a callee write (the window, a block, a live frame, G or an out cell), none of them a free frame.
   - the write set: g_nl's [LA_G_NL, LA_G_NL + NK_N_SENT + 4) (fuzz_socket, fuzz_send, fuzz_recv, fuzz_close; the
     caller's G must hold it: `ajw` holds of image bytes only by `inG G`), `aivl kind kind_n`, `aivl alias alias_n`
     (copy_attr; a NULL buffer owns no byte, the plain L7 rule).

   What does NOT carry over from the plain text:
   - errno in the write set. On image A the write set is also a premise (`ajw`), and errno is not in LA_G, not in a
     block, not in a frame: no caller could meet it. The journal and apost's `akept` already let errno change
     (YCbq.v:359, link_amem.v akept's image clause), so the A write set drops it.
   - `errno_at regs` (tp - 164) is `as_errno B`, with `as_errno B = as_tp B - 164` as a premise (gp, tp are apre's).
   - `frame_apart_gnl regs 16592` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a: the window is on the
     real stack above alloc_ceiling, g_nl is an image byte). The plain K and its stack probes of the receive buffer: see above.
   - `apart (errno_at regs) 4 req len` (the library comparer, 2026-10-30): no instruction or callee needs it. errno is
     written only on fuzz_socket's failure arm, which skips fuzz_send, and on fuzz_send's errno arm, which does not
     read req; nothing reads req after fuzz_send.
   Every plain Post conjunct carries over unchanged in content, over the A views.

   Satisfiability witness (a run; lib/A/Prog/alib_witness.v `nl_talk_apre_sat` closes the function-specific part at a
   memory holding these values): reac_link_alias_read's call at 0x88858 in op_read of the run of link-a/form/WITNESS.md
   (internal record, sha256 b8aaf8151f7f) section 1 (LLVMFuzzerTestOneInput 0x836a8 -> reac_link_alias_read). Registers:
   ra = 0x8885c; a0 = the 32-byte RTM_GETLINK `req_read 4` (name "nl2", if_index 4) at frame_addr ly 1 p1 + 32 in
   reac_link_alias_read's class-1 frame, a1 = 32; a2, a4 = op_read's two text_buf(16) blocks (malloc(17), 17 bytes
   0x5a), a3 = a5 = 16; sp = reac_link_alias_read's realigned sp; gp, tp the image's. Memory: g_nl as interfaces()
   and kernel() leave it before the socket opens (open = opened = closed = misuse = 0, socket_errno = send_errno = 0
   (the input's flags & 3 = 0), end_errno one of nl_errno's 105, 4, 11, 1, 24, 111, n_sent = 0, one queued chunk,
   n_if = 64), errno 0 at 0x631b6c; every shadow byte a `range_addressable` premise reads is 0 (g_nl's object and errno
   by the image's zero shadow, the request by frame_alloc_1's `zero_shadow` and the unpoisoning at +0x184..+0x190, the
   blocks' first 16 bytes by the chunk shadow) and every byte of a `shadow_hull_vis` hull is visible (it also covers
   the frame's left redzone, a block's last granule (shadow 1) and its redzone). The journal: LLVMFuzzerTestOneInput's
   (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1) with G = LA_G, so `ajw` holds of the
   g_nl range by `inG`, and of the two blocks by `in_tmp_block` (allocated after the journal began); own = [(1, p1);
   (4, p4)] and frames S = [], so `aside_room Sc [(9, 1)]` is 0 + 1 <= 32; the read set [req, req + 32) lies in
   the frame (1, p1) of Sc (`akb`'s frame clause); the window [sp0 - STK, sp0) holds the chain's 416 + 144 + 8448
   bytes (STK = LLVMFuzzerTestOneInput's K, link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5);
   `st_nev S + k + 0 <= EV_MAX` as in link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1.

   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem copy_attr_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition NL_TALK_A : Z := 0x88974.
Lemma NL_TALK_A_is_entry : NL_TALK_A = LA_nl_talk. Proof. reflexivity. Qed.

(* the stack bound on image A: the 192-byte frame, the realignment slack of +0x40, copy_attr's window *)
Definition NL_TALK_AFRAME : Z := 192.
Definition NL_TALK_ASLACK : Z := 16.
Definition NL_TALK_AK : Z := NL_TALK_AFRAME + NL_TALK_ASLACK + COPY_ATTR_AK.
Lemma NL_TALK_AK_val : NL_TALK_AK = 8448. Proof. reflexivity. Qed.

(* the side-stack room: nl_talk's own class-9 frame *)
Definition NL_TALK_ASIDE : list (Z * Z) := [(9, 1)].

(* the write set: g_nl up to n_sent, and the two buffers, which a NULL pointer does not own *)
Definition nl_talk_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4); aivl (aarg regs 2) (aarg regs 3); aivl (aarg regs 4) (aarg regs 5)].

(* the read set: the request fuzz_send copies *)
Definition nl_talk_ard (regs : bvmap 5 word) (m : word -> option byte) : Z -> Prop :=
  rd_ivl (aarg regs 0) (aarg regs 0 + aarg regs 1).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* errno at the image's address: what ___errno_location returns, writable, its shadow usable, apart from the frame
   of a call with stack bound K and from g_nl *)
Definition aerrno_ok (K : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  as_errno B = as_tp B - 164 /\ awrange segs m (as_errno B) 4 /\
  range_addressable (ard segs m) SHADOW_OFF (as_errno B) 4 /\
  apart_frame regs K (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4.

(* a range the runtime checks (a checked copy, a string wrapper): in a memory band, its shadow usable and visible *)
Definition achk (m : word -> option byte) (p n : Z) : Prop :=
  amem_range p n /\ range_addressable (ard segs m) SHADOW_OFF p n /\ shadow_hull_vis (ard segs m) p n.

Definition nl_talk_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs req,
    anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs /\ nk_open kbs = 0
    /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    /\ aerrno_ok NL_TALK_AK regs m
    (* the request *)
    /\ abytes segs m (aarg regs 0) req /\ Z.of_nat (length req) = aarg regs 1
    /\ 0 <= aarg regs 1 <= NL_SENT_LEN
    /\ amem_range (aarg regs 0) (aarg regs 1)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) (aarg regs 1)
    /\ (0 < aarg regs 1 -> shadow_hull_vis (ard segs m) (aarg regs 0) (aarg regs 1))
    /\ apart_frame regs NL_TALK_AK (aarg regs 0) (aarg regs 1) /\ apart_gnl LA_G_NL (aarg regs 0) (aarg regs 1)
    (* the two buffers *)
    /\ abuf_arg segs m (aarg regs 2) (aarg regs 3) /\ abuf_arg segs m (aarg regs 4) (aarg regs 5)
    /\ (aarg regs 2 <> 0 -> apart (as_errno B) 4 (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> apart (as_errno B) 4 (aarg regs 4) (aarg regs 5))
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aarg regs 4 <> 0 -> 1 <= aarg regs 5 ->
          apart (aarg regs 2) (aarg regs 3) (aarg regs 4) (aarg regs 5))
    /\ (aarg regs 2 <> 0 -> apart_frame regs NL_TALK_AK (aarg regs 2) (aarg regs 3)
          /\ apart_gnl LA_G_NL (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> apart_frame regs NL_TALK_AK (aarg regs 4) (aarg regs 5)
          /\ apart_gnl LA_G_NL (aarg regs 4) (aarg regs 5))
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> achk m (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> achk m (aarg regs 4) (aarg regs 5)).

Definition nl_talk_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall kbs req,
    anlk_at segs m LA_G_NL kbs -> abytes segs m (aarg regs 0) req ->
    Z.of_nat (length req) = aarg regs 1 ->
    let K0 := nk_kstate kbs in
    getr regs' 10 = w64 (talk_rc_lib K0)
    /\ (exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
          /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
          /\ nk_n_if kbs' = nk_n_if kbs
          /\ nk_socket_errno kbs' = 0
          /\ nk_send_errno kbs' = k_send (talk_after K0)
          /\ nk_next kbs' = Z.of_nat (k_next (talk_after K0))
          /\ nk_sent kbs' = (if talk_owes K0 then owe (nk_sent kbs) req else nk_sent kbs)
          /\ nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs'))
          /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
          /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
          /\ (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs)
          /\ (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1))
    /\ (forall pay, a_kind (talk_attrs K0) = Some pay -> aarg regs 2 <> 0 -> 1 <= aarg regs 3 ->
          acstr_at segs m' (aarg regs 2) (cut_text pay (aarg regs 3)))
    /\ (forall pay, a_alias (talk_attrs K0) = Some pay -> aarg regs 4 <> 0 -> 1 <= aarg regs 5 ->
          acstr_at segs m' (aarg regs 4) (cut_text pay (aarg regs 5)))
    /\ (a_kind (talk_attrs K0) = None -> aarg regs 2 <> 0 -> forall s,
          Z.of_nat (length s) < aarg regs 3 -> acstr_at segs m (aarg regs 2) s ->
          acstr_at segs m' (aarg regs 2) s)
    /\ (a_alias (talk_attrs K0) = None -> aarg regs 4 <> 0 -> forall s,
          Z.of_nat (length s) < aarg regs 5 -> acstr_at segs m (aarg regs 4) s ->
          acstr_at segs m' (aarg regs 4) s)
    /\ (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> abuf segs m' (aarg regs 2) (aarg regs 3))
    /\ (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> abuf segs m' (aarg regs 4) (aarg regs 5)).

Definition nl_talk_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B NL_TALK_A NL_TALK_AK 0 NL_TALK_ASIDE
    nl_talk_apre nl_talk_ard nl_talk_awr nl_talk_apost.

End c.

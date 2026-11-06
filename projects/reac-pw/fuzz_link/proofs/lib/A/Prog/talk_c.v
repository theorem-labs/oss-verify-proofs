(* talk (fuzz_link.c:333-384) on image A (fuzz_link.asan 0x8763c, 1924 bytes; listing
   (internal path) (internal record, sha256 5526460cb5be)): the harness model of one request and
   its reply. a0 = m (the model block), a1 = r, a2 = len, a3 = kind, a4 = kind_n, a5 = alias, a6 = alias_n. The plain
   contract is lib/Prog/talk_c.v; this file states the SAME link_spec result (`talk_rc_model`, `talk_attrs`,
   `talk_after`, `talk_owes` of `md_kstate mbs kbs`) in link_amem.v's `aleaf_rd` form.

   The image-A code, in order:
     +0x00..+0x34  push a 144-byte frame (addi sp, sp, -0x90); save ra, s0..s11. No realignment.
     +0x38..+0x48  s2 := alias_n, s0 := alias, s3 := kind_n, s1 := kind, s5 := len;  +0x58 s4 := m
     +0x4c..+0x54  s7 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     socket arm:   +0x6c lw socket_errno (m + 0);  +0x70 beqz -> +0x88;  +0x7c sw zero, 0(m);  +0x80 negw;  return -e
     send arm:     +0x9c lw send_errno (m + 4);  +0xa0 beqz -> +0xf4;  +0xac sw zero, 4(m);  +0xb0 negw;  return -e
     owe:          +0xf4..+0x110 s6 := m + 0x2090 (MD_N_REQ), lw n_req;  +0x118 blt 15, n_req -> +0x16c (ring full)
                   +0x11c..+0x12c checked_memcpy(m + 12 + 512 n_req, r, len) (0x52d78); a1 still holds r: no
                   instruction from the entry to +0x12c writes a1 on this path
                   +0x138 lw n_req;  +0x150 sw n_req + 1;  +0x168 sd len, req_len[n_req] (m + 0x2010 + 8 n_req)
                   The C bound `len < NL_SENT_LEN ? len : NL_SENT_LEN` is NOT in the binary (+0x128 a2 := s5 = len):
                   the Pre's `len <= NL_SENT_LEN` makes the two the same (link-a/plan/CONTRACTS.md
                   (internal record, sha256 5cd783c633c3) 6a, a source test is not a binary test).
     chunk loop:   +0x16c..+0x180 a0 := m + 8, lw next;  +0x184..+0x194 a5 := g_nl + 0x40000, lw n_chunks
                   (0x200(a5): a constant offset into the global, left unchecked);  +0x198 bge next, n_chunks -> +0x290
                   (lw end_errno, 0x208(a5), unchecked;  j +0x80 negw: return -end_errno)
                   +0x1b4..+0x1bc sw next + 1, 0(a0);  +0x1c0..+0x1d8 ld left := chunk_len[c] (g_nl + 0x40000 + 8 c)
                   +0x1dc bge left, 16 -> +0x1f8;  else +0x1e0..+0x1f0 lw next, lw n_chunks, blt -> +0x1ac
     message walk: +0x1f8..+0x200 s4 := b = g_nl + 4096 c, off t2 := 0;  +0x218 lwu ml, 0(b + off);  +0x21c, +0x220
                   ml < 16 or left < ml -> next chunk (+0x1e0);  +0x238 lhu type, 4(b + off);  +0x23c type 16 ->
                   +0x298;  +0x240 type 2 -> +0x2a8;  else +0x244..+0x258 off += align4(ml), left -= align4(ml), loop
                   while left >= 16, else next chunk
     NLMSG_ERROR:  +0x2a8 ml < 36 -> a1 := -5;  else +0x5ec..+0x638 the code at b + off + 16, read byte by byte, the
                   top byte by `lb` (so a1 is the sign-extended int32);  +0x63c code <= 0 -> return it, else return
                   0xf4240 = RC_FAILS
     RTM_NEWLINK:  +0x298 ml < 36 -> return 0;  +0x2b8..+0x308 al s6 := ml - 32, a s11 := off + 32, frame slots
                   0x10 := b + 4, 0x18 := kind_n - 1, 0 := alias_n - 1, 0x20 := (kind = 0 or kind_n = 0),
                   8 := (alias = 0 or alias_n = 0)
                   attribute loop +0x30c..+0x5ac: l := 2 bytes at b + a;  l < 4 or al < l -> return 0;  t := 2 bytes at
                   b + a + 2;  t = 20 (IFLA_IFALIAS) and slot 8 = 0 -> take_text into alias (+0x39c..+0x58c);
                   t = 18 (IFLA_LINKINFO) and l >= 8 -> the inner walk +0x3f0..+0x518 over [a + 4, a + l), each inner
                   attribute with type 1 (INFO_KIND) and slot 0x20 = 0 -> take_text into kind (+0x47c..+0x4f4);
                   +0x598..+0x5ac a += align4(l), al -= align4(l);  al < 4 -> return 0
     take_text (inline, both arms): scan d[k] for k < l - 4 up to the first NUL (+0x3b4..+0x3d4 / +0x490..+0x4b0);
                   k := min(k, cap - 1) unsigned (+0x55c..+0x564 / +0x4c8..+0x4d0);  checked_memcpy(buf, d, k)
                   (+0x570 alias / +0x4dc kind);  sb zero, buf[k] (+0x588 / +0x4f4)
     +0xb4..+0xf0  a0 := a1;  restore, pop, ret.
   The image does what link_spec's `talk_core` says: the message test (left >= 16, 16 <= ml <= left), the attribute
   test (al >= 4 before l is read, 4 <= l <= al), the align-4 steps, the last IFLA_IFALIAS and the last INFO_KIND
   win, `cut_text` (first NUL, then cap - 1), and `norm_rc` on a positive NLMSG_ERROR code.

   THE WRITE SET, store by store: +0x7c [m, m + 4), +0xac [m + 4, m + 8), +0x1bc [m + 8, m + 12) (a0 = m + 8 is
   kept through the chunk loop), +0x150 [m + 0x2090, + 4), +0x168 [m + 0x2010 + 8 n, + 8), checked_memcpy +0x12c
   [m + 12 + 512 n, + len) with n <= 15 and len <= 512: all inside [m, m + MD_SIZE); checked_memcpy +0x4dc and the
   store +0x4f4: [kind, kind + k + 1) with k <= kind_n - 1; +0x570 and +0x588: [alias, alias + k + 1) with
   k <= alias_n - 1; the frame stores (+0x04..+0x34, +0x2bc, +0x2d8, +0x2e8, +0x2f8, +0x308) inside [sp - 144, sp).
   After +0x200 s4 holds the chunk address, and no store goes through it. So talk writes NO byte of g_nl on image A
   (the plain claim holds), and Wr = [(m, m + MD_SIZE); aivl kind kind_n; aivl alias alias_n].

   THE 22 INSTRUMENTED CHECKS (27 shadow loads: five 2- or 4-byte loads that are not aligned are checked at their
   first and last byte; 27 error-path calls), each with its range and the premise that makes it pass:
     1 +0x5c..+0x68, +0x64c..+0x654  load4 [m, m + 4) socket_errno          range_addressable m MD_SIZE
     2 +0x74..+0x78, +0x660..+0x668  store4 [m, m + 4)                      the same
     3 +0x88..+0x98, +0x674..+0x67c  load4 [m + 4, m + 8) send_errno        the same
     4 +0xa4..+0xa8, +0x684..+0x68c  store4 [m + 4, m + 8)                  the same
     5 +0xfc..+0x10c, +0x694..+0x69c load4 [m + 0x2090, + 4) n_req          the same
     6 +0x130..+0x134, +0x6b8..+0x6c0 load4 n_req again                    the same
     7 +0x158..+0x164                store8 req_len[n] (lbu <> 0 -> errpath_store8): an 8-byte access covers the end
                                     of its first granule, so range_addressable gives that shadow byte 0 at any
                                     alignment (YG0v.v check_passes_whole)
                                                                            the same
     8 +0x16c..+0x17c, +0x6a8..+0x6b0 load4 [m + 8, + 4) next               the same
     9 +0x1ac..+0x1b0, +0x280..+0x284 store4 next                           the same
     10 +0x1c0..+0x1d4               load8 chunk_len[c] (lbu <> 0 -> errpath_load8; an aligned granule)
                                                                            range_addressable (g_nl + NK_CHUNK)
                                                                            NK_N_CHUNKS, the chunk queue
     11 +0x1e0..+0x1e4, +0x288..+0x28c load4 next (the loop)               range_addressable m MD_SIZE
     12 +0x204..+0x214, +0x260..+0x26c load4 ml at b + off                  the chunk queue
     13 +0x224..+0x234, +0x270..+0x27c load2 type at b + off + 4            the chunk queue
     14 +0x5ec..+0x610, +0x6cc..+0x6ec loadN(4) code at b + off + 16, first and last byte   the chunk queue
     15 +0x30c..+0x330, +0x5b0..+0x5c4, +0x758..+0x768 loadN(2) l at b + a  the chunk queue
     16 +0x350..+0x374, +0x5c8..+0x5dc, +0x76c..+0x780 loadN(2) t at b + a + 2   the chunk queue
     17 +0x3b4..+0x3c4, +0x3dc..+0x3e4, +0x74c..+0x754 load1 alias payload byte  the chunk queue
     18 +0x574..+0x584, +0x5e0..+0x5e8 store1 alias[k], k <= alias_n - 1   range_addressable alias alias_n
     19 +0x3f8..+0x41c, +0x51c..+0x530, +0x71c..+0x72c loadN(2) inner l at b + i  the chunk queue
     20 +0x438..+0x45c, +0x534..+0x548, +0x730..+0x744 loadN(2) inner t at b + i + 2   the chunk queue
     21 +0x490..+0x4a0, +0x4b8..+0x4c0, +0x70c..+0x714 load1 kind payload byte   the chunk queue
     22 +0x4e0..+0x4f0, +0x54c..+0x554, +0x748 store1 kind[k], k <= kind_n - 1   range_addressable kind kind_n
   Every chunk address the walk forms lies in [g_nl, g_nl + NK_CHUNK_LEN): the message reads stay in
   [b, b + left) with left <= chunk_len[c] <= NL_CHUNK_MAX (nlk_wf), and c < n_chunks <= 64.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores; the three checked_memcpy calls take ecall_pre-style
     premises at sp' = sp - 144 that the walk derives from the journal (pcap's aj_intrin_atS, A/Prog/YC85G.v);
     +0xf0 ret.
   - K = 144 + ESTACK = 4240: the 144-byte frame (+0x00), then checked_memcpy's window [sp' - ESTACK, sp') (Reusable/YG0d.v
     aintrin_realizes over ecall_pre). No realignment, no other callee (errpath_* only). link-a/form/FORM.md
     (internal record, sha256 13aeff774164) section 5: 4240. The plain K (144: memcpy counted as using no stack) does not carry over.
   - `amodel_at m mbs`, `model_wf mbs`: the loads and stores of checks 1-9 and 11; checked_memcpy's destination
     writable (`dest_ok`); model_wf's `0 <= n_req <= 16` keeps [m + 12 + 512 n, + len) and req_len[n] inside the
     block when the +0x118 test lets n <= 15 through, and `0 <= next < 2 ^ 31` makes the signed +0x198 compare the
     spec's.
   - `anlk_at g_nl kbs`, `nlk_wf kbs`: n_chunks, end_errno, chunk_len[c] and the chunk bytes the walk reads
     (`nk_chunks kbs` of `md_kstate`); nlk_wf bounds n_chunks by 64 and each chunk_len by 4096.
   - `abytes m r req`, `length req = len`, `0 <= len <= NL_SENT_LEN`: checked_memcpy +0x12c reads [r, r + len)
     (`src_ok`, `0 <= x`, `n < 2 ^ 32`); the Post's `owe ... req` names those bytes.
   - `abuf_arg` of the two buffers: checked_memcpy's destination writable, and the NUL stores +0x4f4, +0x588.
   - the model block's shadow: `range_addressable m MD_SIZE` (checks 1-9, 11; checked_memcpy +0x12c's destination
     check), `shadow_hull_vis m MD_SIZE` and `amem_range m MD_SIZE` (checked_memcpy's destination hull and range,
     `d + n <= 2 ^ 63`). The hull and the range of the sub-range [m + 12 + 512 n, + len) follow from the block's.
   - the chunk queue's shadow: `range_addressable (g_nl + NK_CHUNK) NK_N_CHUNKS` = [g_nl, g_nl + 262656), the chunks
     and the chunk_len array (checks 10, 12-17, 19-21; the source checks of checked_memcpy +0x4dc / +0x570), and its
     `shadow_hull_vis` (their source hulls). The `amem_range` of a source inside g_nl is a closed fact (g_nl ends
     below kLowMemEnd), and `src_ok` comes from `anlk_at` and the window being on the real stack (journal).
   - the request's shadow: `amem_range r len`, `range_addressable r len`, `0 < len -> shadow_hull_vis r len`:
     checked_memcpy +0x12c's source (YG0d.v:332-333).
   - the buffers' shadow (kind <> 0, kind_n >= 1; the same for alias): `amem_range`, `range_addressable`,
     `shadow_hull_vis` over [kind, kind + kind_n): checked_memcpy +0x4dc's destination ([kind, kind + k),
     k <= kind_n - 1) and check 22; `d + n <= 2 ^ 63` from amem_range, `0 <= d` from abuf.
   - separations (the plain ones, link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a class 1):
     `apart r len m MD_SIZE` (checked_memcpy +0x12c's `d + n <= x \/ x + n <= d`); each buffer apart from g_nl (checked_memcpy
     +0x4dc / +0x570's source-destination disjointness, and the walk reads the chunks after a buffer write), from the model
     block and from the other buffer (both are written and stated in the Post); the model block apart from g_nl (it is written
     before the chunks are read); `apart_frame` of m, r and the buffers (the frame stores, and checked_memcpy's window).
   - the write set and apre's `ajw` on it: the stores listed above.
   - the read set Rd (`aleaf_rd`) = [r, r + len): the bytes read through the pointer argument r that are not in Wr
     (checked_memcpy +0x12c). The model block is read and written (it is in Wr); the buffers are only written; g_nl
     is read at addresses the code forms from LA_G_NL, not through an argument. talk has no allocating callee.
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   THE PLAIN `a_kind = None -> munch [...]` CLAUSES: `akept` does NOT give them. akept excepts the whole write set
   E = Wr, and the kind buffer is in Wr, so akept says nothing about the kind buffer's bytes. The plain clause says
   that when the reply names no kind, every byte outside the model block, the alias buffer and the frame is kept:
   the part outside Wr is akept's, the part that is lost is the kind buffer itself. Its callers need it:
   model_read stores a NUL at kind[0] (+0x138) and at alias[0] (+0x154) before the call (+0x1e8), and its Post's
   `acstr_at m' kind (r_kind R)` with `r_kind R = text_of_attr None kc = []` holds only if that NUL survives talk;
   op_read then hands model_read's buffers wk / wa to check_read as the expected texts (fuzz_link.c:696;
   check_read_c.v asks `acstr_at` of them), and model_mark hands kind / alias to model_decide. So each `munch` clause
   becomes an explicit clause over the A views: when the reply names no kind (no alias), the kind (alias) buffer's
   bytes [kind, kind + kind_n) keep their values (`abytes m kb -> abytes m' kb`). It is true of the image: the only
   writes to a buffer are in its take_text arm, which runs only for an attribute that makes `a_kind` (`a_alias`)
   Some.

   What does NOT carry over from the plain text:
   - `frame_apart_gnl regs 144` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a): on image A the
     window is on the real stack above alloc_ceiling (the journal's `astk_ok`, YCbq.v:330-332) and g_nl is an image byte.
   - the two `munch` clauses, replaced as above.
   - `wz` is written `w64` (the same Z_to_bv 64): every return value is the 64-bit sign extension of the int32 the
     C returns (`negw` +0x80 / +0xb0, `addi` -5, the `lb`-built code, `addiw` 0xf4240, `mv` zero).
   The rest of the plain Post is the A Post unchanged; no plain conjunct is false of image A.
   Released proofs (rule 24): none of talk (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): the hits,
   boost-beast/http_request and boost-json/fuzz_parse, are generic identifiers of unrelated units).

   CALL SITES (link-a/facts/asan-set.tsv (internal record, sha256 e26bb6a28c00): talk's callers are model_read and model_write):
   - model_read +0x1cc..+0x1e8 (0x86614): a0 = s7 (m), a1 = s9 = s11 + 0x20 (the request in model_read's class-1
     side frame), a2 = 32, a3 = s5 (kind), a4 = s6 (kind_n), a5 = s3 (alias), a6 = s4 (alias_n); sp = model_read's
     realigned sp. model_read_c.v's header maps each conjunct.
   - model_write +0x1d8..+0x1f4 (0x882f4): a0 = s4 (m), a1 = s9 = s11 + 0x20 (the request in model_write's class-4
     side frame), a2 = s10 = 32 + align4(4 + alen) <= 292, a3..a6 = 0 (the buffer conjuncts are vacuous).

   Satisfiability witness (a real run; the closed lemma is `hb_talk_apre_sat` of lib/A/Prog/help_witness.v):
   LLVMFuzzerTestOneInput (entry sp SP0 = 0x7ffffffff000, realigned sp 0x7fffffffee60) on an input whose first op
   is op_read (op byte 0): name byte 0 -> "nl0" = g_names[0] at LA_G_NAMES = 0x62fac0; kc = 16, ac = 16; kernel:
   flags 0, errno byte 0, end errno byte 0 (end_errno = ENOBUFS = 105), one chunk, mode 1 (the input's own bytes),
   40 bytes:  28 00 00 00 10 00 00 00 01 00 00 00 00 00 00 00 | 16 x 00 | 07 00 14 00 61 62 00 00
   (nlmsghdr: length 40, type 16, seq 1; ifinfomsg zero; IFLA_IFALIAS rta_len 7, payload "ab" and its NUL, one pad
   byte). model_read (0x8368c) calls talk at 0x86614:
   - registers: ra = 0x86618; sp = 0x7fffffffede0 (model_read's entry sp 0x7fffffffee60 - 0x80, already 32-aligned);
     a0 = M, the calloc(1, 8856) block (a 16-aligned heap address, e.g. 0x621000000100); a1 = R = F1 + 0x20 with
     F1 = frame_addr ly 1 p1, model_read's class-1 side frame (fake-stack range, e.g. 0x7f0000008000); a2 = 32;
     a3 = WK = F4 + 0x2e0, a4 = 16, a5 = WA = F4 + 0x330, a6 = 16, with F4 = frame_addr ly 4 p4,
     LLVMFuzzerTestOneInput's class-4 side frame (+0x2d0, +0x2dc set the slots 0x88(s1), 0x80(s1); e.g.
     0x7f0000100000); gp, tp = as_gp B, as_tp B.
   - memory: M's 8856 bytes all 0 (calloc, then model_begin's zero stores): model_wf (n_req 0, next 0, errnos 0,
     n_mark 0); g_nl: n_chunks 1, next 0, chunk_len[0] = 40, chunk[0] the 40 bytes above, end_errno 105,
     socket_errno = send_errno = 0, open = opened = closed = misuse = 0, n_sent 0, n_if 64 and the interfaces()
     table: nlk_wf; R's 32 bytes = req_read 2 (20 00 00 00 12 00 01 00 01 00 00 00 00 00 00 00 | 00 00 00 00 02 00
     00 00 | 8 x 00); WK, WA: 40 zero bytes (checked_memset at LLVMFuzzerTestOneInput +0xe58, +0xe80; model_read's
     NUL stores at [0]).
   - shadow: M's 1107 shadow bytes 0 (a calloc chunk of whole granules); g_nl's object shadow 0; R: frame_alloc_1
     zeroes F1's shadow and model_read +0x18c..+0x198 set its bytes 4..7 to 0 again, so [F1 + 32, F1 + 64) is
     addressable; WK, WA: 0 (LLVMFuzzerTestOneInput +0xe34..+0xe44, +0xe5c..+0xe6c); every hull is visible (heap:
     AR's shadow law; side frames: am_client; g_nl: the image's shadow).
   - separations: M (heap), R, WK, WA (fake stack, below alloc_ceiling) are outside [sp - 4240, sp) (real stack,
     above it); M, R, WK, WA are pairwise disjoint (block vs frames; R in F1, WK, WA in F4 at disjoint offsets);
     none is in g_nl (an image byte); amem_range of each (high memory below kHighMemEnd).
   - Rd: [R, R + 32) lies in F1 and (1, p1) is in frames Sc: akb. The journal: as link-a/form/WITNESS.md
     (internal record, sha256 b8aaf8151f7f) section 1, with own = frames Sc = [(1, p1); (4, p4)]; `ajw` on M by `in_tmp_block`
     (calloc'd after the journal began), on WK and WA by `in_frames` (LLVMFuzzerTestOneInput's own frame); aside_room Sc [] holds.
   The Post at this witness: a0 = 0; next = 1, n_req = 1, req[0] = R's 32 bytes, req_len[0] = 32; WA holds "ab"
   and its NUL (cut_text of "ab" and its NUL at 16); a_kind = None, so WK keeps its 40 zero bytes.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition TALK_A : Z := 0x8763c.
Lemma TALK_A_is_entry : TALK_A = LA_talk. Proof. reflexivity. Qed.

(* the stack bound on image A: the 144-byte frame and checked_memcpy's window *)
Definition TALK_AFRAME : Z := 144.
Definition TALK_AK : Z := TALK_AFRAME + ESTACK.
Lemma TALK_AK_val : TALK_AK = 4240. Proof. reflexivity. Qed.

(* the write set: the model block and the two buffers, which a NULL pointer does not own *)
Definition talk_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + MD_SIZE); aivl (aarg regs 3) (aarg regs 4); aivl (aarg regs 5) (aarg regs 6)].

(* the read set: the request, which checked_memcpy reads at +0x12c *)
Definition talk_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  rd_ivl (aarg regs 1) (aarg regs 1 + aarg regs 2) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition talk_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists mbs kbs req,
    amodel_at segs m (aarg regs 0) mbs /\ model_wf mbs
    /\ anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs
    /\ abytes segs m (aarg regs 1) req /\ Z.of_nat (length req) = aarg regs 2
    /\ 0 <= aarg regs 2 <= NL_SENT_LEN
    /\ abuf_arg segs m (aarg regs 3) (aarg regs 4) /\ abuf_arg segs m (aarg regs 5) (aarg regs 6)
    (* the model block: checks 1-9 and 11, checked_memcpy +0x12c's destination *)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) MD_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) MD_SIZE
    /\ amem_range (aarg regs 0) MD_SIZE
    (* the chunk queue (the chunks and chunk_len): checks 10, 12-17, 19-21, the sources of +0x4dc and +0x570 *)
    /\ range_addressable (ard segs m) SHADOW_OFF (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ shadow_hull_vis (ard segs m) (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    (* the request: checked_memcpy +0x12c's source *)
    /\ amem_range (aarg regs 1) (aarg regs 2)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 1) (aarg regs 2)
    /\ (0 < aarg regs 2 -> shadow_hull_vis (ard segs m) (aarg regs 1) (aarg regs 2))
    /\ apart (aarg regs 1) (aarg regs 2) (aarg regs 0) MD_SIZE
    (* the two buffers: checked_memcpy +0x4dc / +0x570's destinations, checks 22 and 18 *)
    /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
          apart_gnl LA_G_NL (aarg regs 3) (aarg regs 4)
          /\ apart (aarg regs 3) (aarg regs 4) (aarg regs 0) MD_SIZE
          /\ amem_range (aarg regs 3) (aarg regs 4)
          /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 3) (aarg regs 4)
          /\ shadow_hull_vis (ard segs m) (aarg regs 3) (aarg regs 4))
    /\ (aarg regs 5 <> 0 -> 1 <= aarg regs 6 ->
          apart_gnl LA_G_NL (aarg regs 5) (aarg regs 6)
          /\ apart (aarg regs 5) (aarg regs 6) (aarg regs 0) MD_SIZE
          /\ amem_range (aarg regs 5) (aarg regs 6)
          /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 5) (aarg regs 6)
          /\ shadow_hull_vis (ard segs m) (aarg regs 5) (aarg regs 6))
    /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> aarg regs 5 <> 0 -> 1 <= aarg regs 6 ->
          apart (aarg regs 3) (aarg regs 4) (aarg regs 5) (aarg regs 6))
    /\ apart_gnl LA_G_NL (aarg regs 0) MD_SIZE /\ apart_frame regs TALK_AK (aarg regs 0) MD_SIZE
    /\ apart_frame regs TALK_AK (aarg regs 1) (aarg regs 2)
    /\ (aarg regs 3 <> 0 -> apart_frame regs TALK_AK (aarg regs 3) (aarg regs 4))
    /\ (aarg regs 5 <> 0 -> apart_frame regs TALK_AK (aarg regs 5) (aarg regs 6)).

Definition talk_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall mbs kbs req,
    amodel_at segs m (aarg regs 0) mbs -> anlk_at segs m LA_G_NL kbs ->
    abytes segs m (aarg regs 1) req -> Z.of_nat (length req) = aarg regs 2 ->
    let K0 := md_kstate mbs kbs in
    getr regs' 10 = w64 (talk_rc_model K0)
    /\ (exists mbs', amodel_at segs m' (aarg regs 0) mbs' /\ model_wf mbs'
          /\ md_next mbs' = Z.of_nat (k_next (talk_after K0))
          /\ md_socket_errno mbs' = 0
          /\ md_send_errno mbs' = k_send (talk_after K0)
          /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs
          /\ md_reqs mbs' = (if talk_owes K0 then owe (md_reqs mbs) req else md_reqs mbs)
          /\ md_n_req mbs' = Z.of_nat (length (md_reqs mbs')))
    /\ (forall pay, a_kind (talk_attrs K0) = Some pay -> aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
          acstr_at segs m' (aarg regs 3) (cut_text pay (aarg regs 4)))
    /\ (forall pay, a_alias (talk_attrs K0) = Some pay -> aarg regs 5 <> 0 -> 1 <= aarg regs 6 ->
          acstr_at segs m' (aarg regs 5) (cut_text pay (aarg regs 6)))
    (* the plain `a_kind = None -> munch ...` clauses: the buffer the reply does not name keeps its bytes *)
    /\ (a_kind (talk_attrs K0) = None -> aarg regs 3 <> 0 -> 1 <= aarg regs 4 ->
          forall kb, abytes segs m (aarg regs 3) kb -> Z.of_nat (length kb) = aarg regs 4 ->
            abytes segs m' (aarg regs 3) kb)
    /\ (a_alias (talk_attrs K0) = None -> aarg regs 5 <> 0 -> 1 <= aarg regs 6 ->
          forall ab, abytes segs m (aarg regs 5) ab -> Z.of_nat (length ab) = aarg regs 6 ->
            abytes segs m' (aarg regs 5) ab)
    /\ (aarg regs 3 <> 0 -> 1 <= aarg regs 4 -> abuf segs m' (aarg regs 3) (aarg regs 4))
    /\ (aarg regs 5 <> 0 -> 1 <= aarg regs 6 -> abuf segs m' (aarg regs 5) (aarg regs 6)).

Definition talk_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B TALK_A TALK_AK 0 [] talk_apre talk_ard talk_awr talk_apost.

End c.

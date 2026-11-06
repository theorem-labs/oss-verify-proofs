(* kernel (fuzz_link.c:256-282, with msg_build :174-254 and netlink.h's writers :225-335 inlined) on image A (fuzz_link.asan
   0x83d30, 9888 bytes; listing (internal path) (internal record, sha256 7bc02d6772b3)): the
   fake kernel of one operation, as the input spells it. a0 = in, the input cursor (struct fuzz_in: p at [a0], n at
   [a0 + 8]). It takes the two failure flags and three errno bytes, empties the chunk queue of g_nl and fills it with at
   most three chunks: the input's own bytes or the messages msg_build makes. The plain contract is lib/Prog/kernel_c.v;
   this file states the SAME link_spec result in the `aleaf_rd` form of link_amem.v (`aleaf` with the read set Rd:
   link-a/form/FORM.md (internal record, sha256 13aeff774164) section 11, link_amem.v `akb` / `aleaf_rd`).

   The image-A code, in phases (F = kernel's class-8 side frame, w1 = F + 0x20 and w2 = F + 0x1130 two struct nl_w of
   NW_SIZE = 4112 bytes in it; "fuzz_u8" = the inlined `if (n == 0) 0 else { n--; *p++ }` on the cursor):
     +0x00..+0x3c  push a 352-byte frame (+0x04 `sd zero, 0(sp)`, ra and s0..s11 at sp + 0xf8..0x158); s0 := entry sp
     +0x40..+0x44  `andi sp, sp, -0x20` (up to 16 more bytes); s1 := sp (every spill below is at s1 + 0x18..0xf0)
     +0x48..+0x5c  s4 := the shadow base (.got+0x60 0xa19d0 -> 0xaa438); a2 := the side-stack switch cell (.got+0xb8
                   0xa1a28 -> 0xaa440, `lw` +0x58); s2 := a0
     +0x64         `beqz a2` -> +0x7c (real-stack arm); +0x68..+0x70 frame_alloc_8(0x2240) (0x3df90); s3 := F
     +0x84         `bnez s3` -> +0xac; +0x88..+0xa8 the real-stack arm (0x2240 bytes carved below sp with probes)
     +0xac..+0xd4  store at F the frame magic 0x41b58ab3, the frame descriptor 0x1c1bd and the pc 0x83d30
     +0xd8..+0x218 poison F's shadow (s6 = shadow(F)): 0xf1 x4 (32-byte left redzone), meta_fill_f8(s6 + 4, 0x202) (w1,
                   scope-poisoned) (0x55f94), 0xf2 x32, meta_fill_f8(s6 + 0x226, 0x202) (w2), 0xf3 x32 (right redzone)
     +0x21c..+0x40c fuzz_u8 x3 (flags; b1 -> e = nl_errno(b1); b2 -> end = nl_errno(b2)): the nl_errno.e lookups
                   +0x324..+0x340 and +0x3bc..+0x3dc (e[0] = 105 folded to an immediate at +0x304 when n = 0)
     +0x3fc..+0x418 g_nl (`auipc`/`addi` = 0x5dcac0): `sd zero` +0x40c (n_chunks and next := 0), `sw` +0x410 end_errno,
                   +0x414 socket_errno := -(flags & 1) & e, +0x418 send_errno := (bit 1 of flags) & e. Constant
                   offsets into a global: no instrumented check.
     +0x41c..+0x494 c := fuzz_u8 & 3; c = 0 -> +0x2140
     +0x498..+0x518 loop set-up: s5 := w2, s9 := w2 + 0x1000 (&w2.n), the room constants
     +0x51c..+0x58c per chunk: mode := fuzz_u8; mode & 1 -> raw path +0x1f30
     msg path:
     +0x594..+0x5c0 meta_fill_00(shadow(w2), 0x202) (0x55e74); checked_memset(w2, 0, 4112) (0x53214) (`w = { 0 }`)
     +0x5c4..+0x62c m := fuzz_u8 % 6 (m = 0 -> +0x1e9c)
     +0x634..+0x6cc per message: kind := fuzz_u8; the jump table at .rodata 0x20f78 on kind & 7 (`lw` +0x6c4,
                   `jr` +0x6cc; a read under arodata_okP, as the code bytes are the image's)
       kind 1:     +0x6d0..+0x6dc, +0x1b7c nl_error(w2, 0, -1) (0x86e4c)
       kind 2:     +0x1178..+0x11bc c := fuzz_u8 (0 when n = 0, +0x1b2c); +0x1b30..+0x1b74 a1 := msg_build.codes[c & 3]
                   (0x210e0, `lw` +0x1b58), a2 := (slti(c < 0) - 1) | ((c >> 4) & 7), so 2^64 - 1 or 0..7;
                   +0x1b7c nl_error(w2, a1, a2)
       kind 0, 7:  +0x6e0..+0x958 nl_begin and the 16-byte ifinfomsg (stores into w2; checked_memset +0x950);
                   +0x960..+0x9d4 nattr := fuzz_u8 % 5; per attribute +0x9d8..+0xb48: a := fuzz_u8; t := texts[(a >> 3)
                   % 11] (0xa17c0, `ld` +0xa70; when n = 0 the compiler folds texts[0] to .str.1 0x20fc0, +0xac8);
                   a % 6 = 0: attr_text(w2, 20, t, a & 0x80) +0xb40 (0x86b18);
                   a % 6 = 1: checked_memset(long_alias, 'a', 300) +0xaf8, attr_text(w2, 20, long_alias, 0) +0xb40;
                   a % 6 = 2, 3: the nest header (stores), for 3 the "data" attribute (stores +0xd18..+0xd64,
                   padding checked_memset +0xda4), attr_text(w2, 1, t, a & 0x80) +0xdc8, the nest length (stores
                   +0xdd8..+0xe0c);
                   a % 6 = 4: attr_text(w2, 3, .str.8 0x210c0 = "x", 0) +0xb40;
                   a % 6 = 5: the "abcd" attribute of type 99 (stores +0xe14..+0xf80, padding checked_memset +0xf70);
                   +0x106c..+0x10c4 nl_end; +0x10c8..+0x114c kind 7's unpadded end or nl_pad (checked_memset +0x113c)
       kinds 3..6: +0x11c0..+0x1b28 stores into w2 (3, 4, 5: nl_begin, payload, nl_end; 6: put32(8), put32(3))
     +0x1b80..+0x1b8c next message
     +0x1e9c..+0x1eb0 w2.n = 0: put32(0) (`sw zero` +0x1ea4)
     +0x1eb4..+0x1f18 nl_queue: i := n_chunks (`lw` +0x1eb8); i <= 63 and w2.n <> 0: checked_memcpy(g_nl + 4096 i, w2,
                   w2.n) +0x1ee4 (0x52d78); n_chunks := i + 1 (`sw` +0x1ef4); chunk_len[i] := w2.n (`sd` +0x1f18)
     +0x1f1c..+0x1f24 meta_fill_f8(shadow(w2), 0x202)
     raw path:
     +0x1f30..+0x1f48 meta_fill_00(shadow(w1), 0x202); checked_memset(w1, 0, 4112)
     +0x1f4c..+0x1ffc u16 := two fuzz_u8; want := 1 + u16 % 4096
     +0x2000..+0x203c fuzz_take: k := min(want, n); [a0] := p + k; [a0 + 8] := n - k
     +0x2040..+0x2084 nl_put: w1.n + k < 4097 always (w1.n = 0); k <> 0: checked_memcpy(w1, p, k) +0x2074; w1.n += k
     +0x2088..+0x20ec nl_queue as above (checked_memcpy +0x20b8, `sw` n_chunks +0x20c8, `sd` chunk_len +0x20ec)
     +0x20f0..+0x20f8 meta_fill_f8(shadow(w1), 0x202)
     +0x2100..+0x210c next chunk
     +0x2140..+0x2170 [F] := 0x45e0360e; s3 <> 0: frame_release_8(F, 0x2240) (0x3e10c) (s3 = 0: meta_fill_00(s6, 0x448),
                   the real-stack arm's)
     +0x2174..+0x21b0 sp := s0 - 0x160; restore; ret (the only returning path)
     +0xf88..+0x1068, +0x1b90..+0x1e78, +0x2110..+0x213c, +0x21b4..+0x269c the slow paths of the 1-, 2- and 4-byte
                   checks and the error paths (errpath_load1 0x5a31c, errpath_load4 0x5a45c, errpath_load8 0x5a4fc,
                   errpath_store8 0x5a81c, errpath_store_n 0x5a9fc).

   THE INSTRUMENTED CHECKS: 132 shadow-byte loads (link-a/facts/asan-facts.tsv (internal record, sha256 05ab19b7928f) counts 98:
   the loads whose shadow address is computed in place; 34 reuse the cursor's two shadow addresses kept in s8 (+0x21c..+0x220)
   and at 0xc0(s1) (+0x44c..+0x450)). Each failing arm reaches an errpath_* call, which the proof shows is not reached.
   - [a0 + 8, a0 + 16) (cursor n, 8 bytes; `lbu`, `bnez` -> errpath_load8 / errpath_store8, no slow path, so it
     passes only when s = 0): +0x224 +0x248 +0x294 +0x30c +0x348 +0x41c +0x438 +0x51c +0x534 +0x594 +0x5cc +0x64c
     +0x668 +0x960 +0x974 +0x9d8 +0x9ec +0x117c +0x1f4c +0x1f5c +0x1f9c +0x1ff8 +0x2030 (23).
   - [a0, a0 + 8) (cursor p, the same kind): +0x260 +0x2a8 +0x35c +0x454 +0x54c +0x5e4 +0x680 +0x98c +0xa04 +0x1194
     +0x1f70 +0x1fb0 +0x201c (13). Premise for both: `range_addressable (ard m) SHADOW_OFF a0 16`: each 8-byte range
     holds the last byte of the granule its shadow byte covers, where saddr_ok (Reusable/YG0v.v:29) leaves only s = 0.
   - the input byte at p (1 byte; `lb`; s = 0 passes, else (p & 7) < s passes, else errpath_load1): +0x280 +0x2c8
     +0x37c +0x474 +0x56c +0x604 +0x6a0 +0x9ac +0xa24 +0x11b0 +0x1f8c +0x1fc8 (12). Premise: `range_addressable (ard m)
     SHADOW_OFF wp wn` (each p read is in [wp, wp + wn), the cursor only advances inside it).
   - nl_errno.e[i] (4 bytes; `lb`; s = 0, else (x & 7) + 3 < s, else errpath_load4): +0x334, +0x3cc. Premise:
     `range_addressable (ard m) SHADOW_OFF LA_NL_ERRNO_E 24`.
   - texts[j] (8 bytes, +0xa64, `lbu`, s = 0 only). Premise: `range_addressable (ard m) SHADOW_OFF LA_TEXTS 88`.
   - msg_build.codes[c & 3] (4 bytes, +0x1b4c, slow path +0x1c38). Premise: `range_addressable ... LA_MSG_CODES 16`.
   - chunk_len[i] of g_nl (8 bytes, +0x1f10, +0x20e4, s = 0 only). Premise (convention C2 of the slice):
     `range_addressable (ard m) SHADOW_OFF LA_G_NL NK_SIZE`.
   - the 2- and 4-byte stores into w2 (first and last byte of each; slow paths +0xf88..+0x1068, +0x1b90..+0x1e78):
     +0x718 .. +0x1b00 (78 loads), every one inside [w2, w2 + 4096). They pass with no premise: frame_alloc_8 zeroes
     the shadow of the 0x2240 bytes asked (class 8 is size-premised: A/AStackApi.v:10-16 astack_malloc_sz_realizes,
     Reusable/AsStackSz.v:41), which hold w1 and w2; kernel poisons only its redzones and w1 / w2, and unpoisons w2
     (meta_fill_00 +0x5b0, +0x1e88) before any of them.

   WHICH INSTRUCTION NEEDS WHICH PREMISE:
   - the journal, gp/tp, ret_ok, sp (apre): the frame stores +0x04..+0x38 and the spills at s1 + 0x18..0xf0, all in
     [sp - K, sp); every runtime call runs at sp' = s1 >= sp - 368 with an ESTACK window (ecall_pre, YG0d.v:285-291),
     every own callee at s1 with its K, all inside [sp - K, sp); AR's const law fixes the switch cell at 1 (+0x58: the
     `beqz` +0x64 falls through) and the shadow base (+0x5c); +0x21b0 ret.
   - `aside_room Sc KERNEL_SIDE`: frame_alloc_8 at +0x70 hands out F (count_cid 8 < fs_frames 8 = 64), F >= 4096 (frames_bounds,
     YCbq.v:447-450), so `bnez s3` +0x84 is taken and the real-stack arm (whose shadow stores AR's zshadow_ok forbids,
     link-a/form/FORM.md (internal record, sha256 13aeff774164) section 4.2) is not; the same room for nl_error's frame_alloc_1.
   - apre's `ajw` on the write set: g_nl's [NK_CHUNK, NK_OPEN) (the stores +0x40c..+0x418, +0x1ef4, +0x20c8, +0x1f18,
     +0x20ec, and checked_memcpy's destinations +0x1ee4, +0x20b8, i <= 2), long_alias (checked_memset +0xaf8), all
     by `inG G` (a checked runtime write into G: convention C3, lifted by link_ajkit.v aj_gx_intrin_at);
     the cursor (the stores +0x258, +0x274, ... +0x202c, +0x203c) by the caller's window, below.
   - `anlk_at m LA_G_NL kbs`, `nlk_wf kbs`: the g_nl loads (`lw` n_chunks +0x1eb8, +0x1eec, +0x208c, +0x20c0) and
     stores; the Post's unchanged fields keep their nlk_wf bounds.
   - `range_addressable ... LA_G_NL NK_SIZE`, `shadow_hull_vis ... LA_G_NL NK_SIZE` (C2): the chunk_len checks, and
     checked_memcpy's destination premises (YG0d.v:329-330) for [LA_G_NL + 4096 i, + w.n). `amem_range` of it and
     `0 <= d`, `d + n <= 2 ^ 63` are closed facts (0x5dcac0 + 271992 < kLowMemEnd); dest_ok's `~ aowned` from gx_ok
     and AR_owned_image_law (YG0d.v:481-482), its window clause from the journal (the window is above alloc_ceiling).
   - the cursor: `au64_at m a0 wp`, `au64_at m (a0 + 8) wn` with `0 <= wp, wn < 2 ^ 64` (au64_at fixes only the low
     64 bits, so the ranges are stated), `awrange m a0 16`: every fuzz_u8's `ld` / `sd` of [a0] and [a0 + 8] and
     fuzz_take's +0x2024..+0x203c; `range_addressable ... a0 16`: the 36 cursor checks; `apart_frame regs K a0 16`,
     `apart_gnl`, `apart a0 16 long_alias 304`: the cursor stores and the frame / g_nl / long_alias stores do not
     overwrite each other.
   - the input `exists d, abytes m wp d /\ |d| = wn`: the 12 `lbu` of input bytes (+0x28c +0x2d4 +0x388 +0x480 +0x578
     +0x610 +0x6ac +0x9b8 +0xa2c +0x11b8 +0x1f94 +0x1fd0) and checked_memcpy's source [p, p + k) at +0x2074 (src_ok);
     `amem_range wp wn`, `range_addressable ... wp wn`, `shadow_hull_vis ... wp wn` (wn > 0): the 12 input checks and
     checked_memcpy's source premises (YG0d.v:332-333; a sub-range's hull is inside the range's); `kernel_apart regs
     wp wn`: no store of kernel (frame, g_nl, long_alias, cursor) changes an input byte before it is read, and the
     source is outside checked_memcpy's window [s1 - ESTACK, s1).
   - nl_errno.e, STATED IN THE PRE (`au32_at` of the six values), not left to arodata_okP: the Post states the three
     errno values, and arodata_okP pins .rodata to `seg_rom segs` with segs a parameter of the contract, so the values
     are not fixed by the premises otherwise; the caller discharges it from arodata_okP at the image (0x21080 is
     .rodata, outside as_owned_static and errno). `lw` +0x340 (e), +0x3dc (end); `range_addressable ... 24`: +0x334,
     +0x3cc; `kernel_apart regs LA_NL_ERRNO_E 24`: the reads follow the cursor stores +0x258..+0x2bc.
   - msg_build.codes (link_aaddr.v lacks it: LA_MSG_CODES below): `abytes` of its 16 bytes, `lw` +0x1b58 (its value
     only goes to nl_error's a1, which nl_error's Pre leaves free); `range_addressable ... 16`: +0x1b4c; `kernel_apart`.
   - texts (.data.rel.ro 0xa17c0; the plain lesson `p <> 0`: the Pre states each entry): `range_addressable ...
     LA_TEXTS 88`: +0xa64; `kernel_apart regs LA_TEXTS 88`; each entry `au64_at m (LA_TEXTS + 8 j) p` (`ld` +0xa70)
     with `kernel_str regs m p` (below). (The pin is ET_EXEC: nothing relocates the table, and it lies in
     PT_GNU_RELRO 0xa1340 .. 0xa3000, inside PcapRelro.v's [0xa1380, 0xa26c8), so at the image arodata_okP gives the
     caller the file's words.)
   - .str.1 0x20fc0 and .str.8 0x210c0 (link_aaddr.v lacks them: LA_STR_EMPTY, LA_STR_X below), passed directly to
     attr_text: `kernel_str` of each.
   - `kernel_str regs m p` gives what attr_text's Pre asks of its string a2 (attr_text_c.v attr_text_apre): `p <> 0`,
     `acstr_at m p s`, `|s| + 1 < 2 ^ 32` (the strlen contract's `aread_ok`, attr_text_c.v), the readable slack to the
     next 8-byte boundary (the strlen wrapper's word-wise reads), `amem_range`, `range_addressable` and
     `shadow_hull_vis` of [p, p + |s| + 1) (the wrapper's check and checked_memcpy's source premises), and
     `kernel_apart regs p (|s| + 1)`: kernel's stores (cursor, long_alias memset, g_nl copies, frame) do not change
     the string before attr_text reads it, and it is outside attr_text's window (attr_text runs at s1 >= sp - 368, its
     window [s1 - ATTR_TEXT_AK, s1) is inside [sp - K, sp)).
   - long_alias: `au8arr m LA_LONG_ALIAS (la ++ [NUL])`, |la| = 300: checked_memset's dest_ok (writable) +0xaf8, and the
     NUL at 300 (never written: the memset is 300 bytes) is attr_text's acstr_at of "a" x 300; the 3 slack bytes
     (0x62fd40 + 301 = 0x62fe6d, (- 0x62fe6d) mod 8 = 3) readable: attr_text's slack; `range_addressable` and
     `shadow_hull_vis` of its 301 bytes: checked_memset's destination (300) and attr_text's string (301);
     `apart_frame regs K LA_LONG_ALIAS 304`: the frame stores and every callee window.
   - the interface names (`kernel_apart regs p (|nm| + 1)` for each name of g_nl's table): the Post's `aiftab_at m'`;
     kernel never reads them, its writes must miss them.
   - the read set `kernel_ard` (aleaf_rd's `akb` on each byte, link_amem.v): the bytes kernel reads, or its
     Post says are kept, after a call that moves the A-state or keeps image bytes only outside as_owned_static and
     errno: frame_alloc_8 (+0x70) keeps only bytes that are not runtime-owned (astack_malloc_realizes, YG0d.v:305-306),
     attr_text and nl_error keep image bytes only outside as_owned_static, errno and their write set (akept,
     link_amem.v), and nl_error takes a class-1 frame inside. `akb` puts each byte where every such call keeps it,
     and outside every fresh side frame (AR_client_img_law YG0d.v:497-502, sep_block_frame YCbq.v:426, frames_bounds),
     so no frame_alloc hands it out. It holds: the cursor (16 bytes); the input [wp, wp + wn) (read through the cursor
     after frame_alloc_8 and the callees); g_nl (its queue fields are read back after attr_text / nl_error, and the
     Post keeps the rest); nl_errno.e, msg_build.codes, the texts table (fixed image objects read after frame_alloc_8);
     every texts string, .str.1 and .str.8 with its NUL (read through a pointer by attr_text, whose own Rd asks `akb`
     of string and NUL); long_alias's 300 bytes and its NUL (attr_text's Rd); the interface names with their NULs
     (kept by the Post). NOT in it: the slack after a string's NUL to its 8-byte granule's end, and long_alias's 3
     bytes after its NUL. Those are the global's redzone, bytes of as_owned_static, where `akb`'s image clause fails
     (the slot entry comparer, by computation over AF0m.v's Tfib_owned_static: (0x62fe6d, 0x53), (0x20fc1, 0x1f),
     (0x210c2, 0x1e), (0x2110f, 0x11)), and no value of theirs enters a Post: the strlen wrapper needs them only
     visible (`atail_vis`), which holds at every state at the image, not by a read set: mbyte falls back to seg_rom
     (YP09.v:18-22), seg_rom is Some on all of [0x10000, 0x654000) (AB13.v:148 tfib_rom_all), and image bytes are
     never hidden (YK04.v:38 H_off_segments). (No callee contract keeps an owned-static byte: frame_alloc_8's
     Reusable/AsStackSz.v:44-45 and the A posts' akept do not.) A length known only from memory (the input's wn, a
     string's |s|) is the unique value the Pre's views fix: the ranges are stated (au64_at with 0 <= v < 2 ^ 64;
     acstr_at's abytes bounds p and p + |s| + 1).
   EV = 0: no allocator event (stack_malloc / stack_free change only st_fs, YG00.v:576-589).
   SIDE = [(8, 1); (1, 1)]: kernel's class-8 frame and nl_error's class-1 frame (nl_error_c.v); attr_text and the
   runtime callees take none, and nl_error is called with kernel's frame live, so at most one of each.

   THE STACK BOUND (convention C4): K = 352 (`addi sp, sp, -0x160` +0x00) + 16 (`andi sp, sp, -0x20` +0x40: s1 >= sp -
   0x160 - 16) + the deepest callee window = max(ESTACK for checked_memcpy, checked_memset, frame_alloc_8 (sidestack89
   of the libc slice: stated bound ESTACK), frame_release_8 (?: no released contract; ESTACK stated by the donor),
   meta_fill_00 / meta_fill_f8 (?: donor bound ESTACK, measured 0); ATTR_TEXT_AK = 4160 (?: wrapper_strlen ESTACK assumed;
   8256 if the libc slice gives it 2 * ESTACK, then K = 8624); NL_ERROR_AK = 4272) = 368 + 4272 = 4640. link-a/form/FORM.md
   (internal record, sha256 13aeff774164) section 5's 4608? omitted the slack of both kernel and nl_error.

   THE WRITE SET (the plain one at image A's addresses): g_nl's [NK_CHUNK, NK_OPEN) (the chunks, chunk_len, n_chunks,
   next and the three errno words), long_alias's 301 bytes, the cursor's 16 bytes. Nothing else outside kernel's
   window and its own side frame is written: frame_release_8 writes F's shadow (0xf5) and F's flag (runtime-owned),
   meta_fill_* write F's shadow, checked_memcpy / checked_memset write their destinations (the write set or w1 / w2),
   attr_text and nl_error write w2 (their write set) and nl_error its own class-1 frame, all inside the call; F and
   its shadow are not frames of Sc (`frames S2 = frames Sc`), so akept does not cover them and Wr need not name them.
   At the call from LLVMFuzzerTestOneInput `ajw` holds of every byte: g_nl's and long_alias's by `inG LA_G`; the
   cursor's by the window [sp0 - STK, sp0): it is s1 + 0x118 .. s1 + 0x128 of LLVMFuzzerTestOneInput's REAL frame
   (its listing: +0x40 `andi sp`, +0x44 `mv s1, sp`, +0x2e4 / +0x2e8 store data and size there, and every call of
   kernel, +0x6ec +0xad0 +0xdb0 +0x1010, passes `addi a0, s1, 0x118` at sp = s1), not its class-4 side frame.

   WHAT DOES NOT CARRY OVER FROM THE PLAIN TEXT:
   - `frame_apart_gnl regs 4416` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a: from the journal) and K = 4416.
   - `rw_cells rsegs m a0 [C8 wp; C8 wn]` with words: `au64_at` of Z values with 0 <= v < 2 ^ 64, plus `awrange`; the
     Post's cursor clause takes the same ranges (else wn - 2 ^ 64 meets au64_at and `0 <= adv <= wn` is false).
   - the texts clause's `Z.of_nat (length s) < NL_CHUNK_MAX`: neither kernel nor attr_text's A Pre needs it.
   - the texts clause's `kernel_apart regs p (|s| + 1 + |slack|)`: on image A the separation covers the string and
     its NUL, what attr_text reads through its checks and checked_memcpy; the slack is only read, and attr_text asks
     only that it be readable (`abytes`), which kernel_str states at entry and the image's ROM fallback keeps (above).
   - ADDED: every shadow premise above; nl_errno.e's values, msg_build.codes, .str.1 and .str.8 (the plain image fixed
     them through `rsegs`; here segs is a parameter); the read set kernel_ard.
   Nothing of the plain Post is false of image A (re-read against the listing): next = 0 (+0x40c, never stored again),
   n_chunks <= 3 (c = byte & 3 at +0x484, one nl_queue per chunk), each chunk_len in 1..4096 (nl_put's room test, `w.n <> 0`
   at +0x1ecc / +0x20a0), the errno words from nl_errno.e or 0, the fields from NK_OPEN on untouched, the cursor advanced by
   fuzz_u8 / fuzz_take (p + adv, n - adv, adv <= n), long_alias 300 bytes then its NUL. The four link-a/plan/CONTRACTS.md
   (internal record, sha256 5cd783c633c3) 6a classes: every pointer range (input, strings, names, cursor) is apart from
   every write of kernel and its callees (kernel_apart, and akb for the fresh side frames); the u64 views state their ranges
   in Pre and Post; no source-only premise (the C bounds kernel relies on are all tests in the binary: & 3, % 6, % 5, %
   11, & 3 of codes, nl_put's room test); kernel makes no allocator call, and its Post places nothing it does not keep.

   SATISFIABILITY WITNESS (the whole Pre, at a real call). The run: LLVMFuzzerTestOneInput (entry 0x827d4) on the
   13-byte input 00 00 10 10 | 00 00 00 01 00 01 00 01 04: op 0 (read), name 0 ("nl0"), kc = ac = 16, then kernel at
   0x82ec0 (+0x6ec): flags 0, e and end bytes 0 (105, ENOBUFS), c = 1 chunk, mode 0, m = 1, kind 0 (RTM_NEWLINK),
   nattr 1, a = 4: attr_text(w2, 3, "x", 0) at +0xb40 (attr_text_c.v's witness call).
   Registers at 0x83d30: ra = 0x82ec4 (ret_ok, >= 4096); a0 = KW_CUR = KW_SP + 0x118; sp = KW_SP =
   LLVMFuzzerTestOneInput's s1 (32-aligned, so sp mod 16 = 0; kernel's s1 = KW_SP - 0x160, the AT_SP of
   attr_text_c.v); gp, tp = as_gp B, as_tp B.
   Memory: the cursor = (KW_IN + 4, 9); the input at KW_IN, a heap block (KW_IN, 13) of S (the driver's copy:
   pcap's entry Pre `In (p, n) (ablocks B ly S)`, PcapEntry.v:46); g_nl as memset and interfaces() leave it
   (fuzz_link.c:86-100): all zero but if_name[j] / if_index[j] for j < 64 (j < 60: g_names[k], k = j + j / 15, index
   k + 2; j = 60..63: odd[j - 59], index 101 + (j - 60)) and n_if = 64, so nlk_wf; g_names[k] = "nl<k>" NUL-padded to
   8; long_alias 301 zero bytes and its 3 slack bytes zero (.bss); the texts table = KW_TXT below, the addresses of
   fuzz_link.c:121-122's strings in that order (read from the pin's PT_LOAD with pyelftools, as link_aaddr.v's
   .symtab values were: texts[0] = .str.1, every string at the start of its own 32-byte slot), each NUL-terminated
   with zero slack; .str.1 = 00 (slack 7), .str.8 = 78 00 (slack 6); nl_errno.e = 69 00 00 00 04 00 00 00 0b 00 00 00
   01 00 00 00 18 00 00 00 6f 00 00 00; codes =
   ff ff ff ff ed ff ff ff a1 ff ff ff 05 00 00 00 (-EPERM, -ENODEV, -EOPNOTSUPP, 5). Shadow: the run's values over
   each hull: 0 over full granules, the partial count on a last granule (input 00 05; long_alias 37 x 00 then 05;
   .str.1 01, .str.8 02 [INFERENCE] as attr_text_c.v), redzone poison elsewhere ([INFERENCE] 0xf9 for globals, 0xfa
   for the heap); the cursor's shadow 0 (the real stack, zshadow_ok YG0n.v:188-191).
   Separation: KW_CUR >= sp (apart_frame); the input (heap), g_nl, long_alias, g_names and the .rodata / relro objects
   are below sp - K and pairwise apart at these addresses (g_names[63] + 5 = 0x62fcbd < long_alias 0x62fd40).
   The journal: LLVMFuzzerTestOneInput's (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1):
   G = LA_G, XO = 0, OUT = [], FP = [sink_token], STK its K (which counts kernel's 4640), sp0 its entry sp, own = [(4,
   p4)], frames S = []; `aside_room Sc [(8, 1); (1, 1)]` (count 0 + 1 <= 64, <= 8192); `st_nev S + k + 0 <= EV_MAX`;
   `ajw` as in THE WRITE SET; `akb` of kernel_ard: the cursor in the real-stack row outside [sp - K, sp) (it is in the
   journal's window: link_amem.v akb_of_window); the input in a heap block of Sc; every other range image bytes outside
   as_owned_static (to check when the lib/A frame generates that list) and errno (0x631b6c).
   The Post at this witness: n_chunks 1, next 0, chunk 0 = the 40 bytes 28 00 00 00 10 00 00 00 01 00 00 00 00 00 00 00,
   16 zero bytes, 06 00 03 00 78 00 00 00; chunk_len[0] = 40; end_errno 105, socket_errno = send_errno = 0; the
   cursor (KW_IN + 13, 0), adv = 9; long_alias unchanged.
   Closed lemma of the function-specific Pre: lib/A/Prog/kernel_witness.v `kernel_apre_sat : forall segs regs,
   aarg regs 0 = KW_CUR -> spZ regs = KW_SP -> kernel_apre segs regs kw_mem` (KW_SP = 0x7ffffffdd160,
   LLVMFuzzerTestOneInput's s1 at 0x82ec0; KW_CUR = KW_SP + 0x118; the 13 input bytes above at 0x602000000050;
   kw_mem = g_nl after memset and interfaces() with the 64-entry table, g_names, long_alias, the texts table
   (0x20fc0, 0x21100 .. 0x21220), the odd strings (0x20fe0, 0x21000, 0x21020, 0x21040), .str.1, .str.8,
   nl_errno.e, msg_build.codes, zero shadow over every hull the Pre names).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import attr_text_c nl_error_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition KERNEL_A : Z := 0x83d30.
Lemma KERNEL_A_is_entry : KERNEL_A = LA_kernel. Proof. reflexivity. Qed.

(* image-A addresses link_aaddr.v does not hold yet, each from the kernel listing *)
(* msg_build.codes, int32[4]: +0x1b34 auipc a1, 0xfff9c; +0x1b3c addi a1, a1, -0x784 *)
Definition LA_MSG_CODES : Z := 0x210e0.
(* .str.1, "" (texts[0], folded by the compiler): +0xacc auipc a0, 0xfff9c; +0xad0 addi s11, a0, 0x7c4 *)
Definition LA_STR_EMPTY : Z := 0x20fc0.
(* .str.8, "x": +0xb2c auipc a0, 0xfff9d; +0xb30 addi a2, a0, -0x79c *)
Definition LA_STR_X : Z := 0x210c0.

(* the stack bound on image A: the 352-byte frame, the 16 bytes the prologue's `andi sp, sp, -0x20` may add, and the
   deepest callee window (nl_error's K; attr_text's K and the runtime callees' ESTACK are smaller) *)
Definition KERNEL_AFRAME : Z := 352.
Definition KERNEL_AK : Z := KERNEL_AFRAME + 16 + Z.max ESTACK (Z.max ATTR_TEXT_AK NL_ERROR_AK).
Lemma KERNEL_AK_val : KERNEL_AK = 4640. Proof. reflexivity. Qed.

(* the side frames live in kernel's call tree: its own class-8 frame and nl_error's class-1 frame *)
Definition KERNEL_SIDE : list (Z * Z) := [(8, 1); (1, 1)].

(* the write set: g_nl's chunk queue and errno words, long_alias, the cursor (as the plain contract's) *)
Definition kernel_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL + NK_CHUNK, LA_G_NL + NK_OPEN);
   (LA_LONG_ALIAS, LA_LONG_ALIAS + LONG_ALIAS_SIZE);
   (aarg regs 0, aarg regs 0 + 16)].

(* the n bytes at `a` are apart from kernel's writes outside its side frames: its frame and callee windows (K),
   g_nl, long_alias with the 3 slack bytes strlen reads after it, and the cursor (the plain helper, at image A's K) *)
Definition kernel_apart (regs : bvmap 5 word) (a n : Z) : Prop :=
  apart_frame regs KERNEL_AK a n /\ apart_gnl LA_G_NL a n
  /\ apart a n LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
  /\ apart a n (aarg regs 0) 16.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* a string kernel hands to attr_text as a2: what attr_text_apre asks of it, and apart from kernel's writes *)
Definition kernel_str (regs : bvmap 5 word) (m : word -> option byte) (p : Z) : Prop :=
  exists s slack,
    p <> 0 /\ acstr_at segs m p s /\ Z.of_nat (length s) + 1 < 2 ^ 32
    /\ abytes segs m (p + Z.of_nat (length s) + 1) slack
    /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ amem_range p (Z.of_nat (length s) + 1)
    /\ range_addressable (ard segs m) SHADOW_OFF p (Z.of_nat (length s) + 1)
    /\ shadow_hull_vis (ard segs m) p (Z.of_nat (length s) + 1)
    /\ kernel_apart regs p (Z.of_nat (length s) + 1).

Definition kernel_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs,
    anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE
    /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    (* the cursor, and the input it points at *)
    /\ (exists wp wn,
          au64_at segs m (aarg regs 0) wp /\ au64_at segs m (aarg regs 0 + 8) wn
          /\ 0 <= wp < 2 ^ 64 /\ 0 <= wn < 2 ^ 64
          /\ (exists d, abytes segs m wp d /\ Z.of_nat (length d) = wn)
          /\ amem_range wp wn
          /\ range_addressable (ard segs m) SHADOW_OFF wp wn
          /\ (0 < wn -> shadow_hull_vis (ard segs m) wp wn)
          /\ kernel_apart regs wp wn)
    /\ awrange segs m (aarg regs 0) 16
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) 16
    /\ apart_frame regs KERNEL_AK (aarg regs 0) 16 /\ apart_gnl LA_G_NL (aarg regs 0) 16
    /\ apart (aarg regs 0) 16 LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
    (* nl_errno.e *)
    /\ (forall i, 0 <= i < 6 ->
          au32_at segs m (LA_NL_ERRNO_E + 4 * i) (nth (Z.to_nat i) nl_errno_tab 0))
    /\ range_addressable (ard segs m) SHADOW_OFF LA_NL_ERRNO_E 24
    /\ kernel_apart regs LA_NL_ERRNO_E 24
    (* msg_build.codes *)
    /\ (exists cs, abytes segs m LA_MSG_CODES cs /\ length cs = 16%nat)
    /\ range_addressable (ard segs m) SHADOW_OFF LA_MSG_CODES 16
    /\ kernel_apart regs LA_MSG_CODES 16
    (* texts, and the two strings the compiler passes directly *)
    /\ range_addressable (ard segs m) SHADOW_OFF LA_TEXTS (8 * TEXTS_N)
    /\ kernel_apart regs LA_TEXTS (8 * TEXTS_N)
    /\ (forall i, 0 <= i < TEXTS_N ->
          exists p, au64_at segs m (LA_TEXTS + 8 * i) p /\ kernel_str regs m p)
    /\ kernel_str regs m LA_STR_EMPTY /\ kernel_str regs m LA_STR_X
    (* long_alias: 300 bytes, its NUL, and the 3 slack bytes strlen reads *)
    /\ (exists la sl,
          au8arr segs m LA_LONG_ALIAS (la ++ [zb 0]) /\ Z.of_nat (length la) = 300
          /\ abytes segs m (LA_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat)
    /\ range_addressable (ard segs m) SHADOW_OFF LA_LONG_ALIAS LONG_ALIAS_SIZE
    /\ shadow_hull_vis (ard segs m) LA_LONG_ALIAS LONG_ALIAS_SIZE
    /\ apart_frame regs KERNEL_AK LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
    (* the interface names are apart from kernel's writes *)
    /\ (forall tab i nm ix p, aiftab_at segs m LA_G_NL kbs tab -> nth_error tab i = Some (nm, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
          kernel_apart regs p (Z.of_nat (length nm) + 1)).

(* the read set: every byte kernel reads, or its Post keeps, after a call that moves the A-state (frame_alloc_8)
   or keeps image bytes only outside as_owned_static and errno (attr_text, nl_error); a string with its NUL, never
   the redzone after it (header) *)
Definition kernel_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  (aarg regs 0 <= a < aarg regs 0 + 16)
  \/ (exists wp wn, au64_at segs m (aarg regs 0) wp /\ au64_at segs m (aarg regs 0 + 8) wn
        /\ 0 <= wp < 2 ^ 64 /\ 0 <= wn < 2 ^ 64 /\ wp <= a < wp + wn)
  \/ (LA_G_NL <= a < LA_G_NL + NK_SIZE)
  \/ (LA_NL_ERRNO_E <= a < LA_NL_ERRNO_E + 24)
  \/ (LA_MSG_CODES <= a < LA_MSG_CODES + 16)
  \/ (LA_TEXTS <= a < LA_TEXTS + 8 * TEXTS_N)
  \/ (exists i p s, 0 <= i < TEXTS_N /\ au64_at segs m (LA_TEXTS + 8 * i) p /\ acstr_at segs m p s
        /\ p <= a <= p + Z.of_nat (length s))
  \/ (exists s, acstr_at segs m LA_STR_EMPTY s /\ LA_STR_EMPTY <= a <= LA_STR_EMPTY + Z.of_nat (length s))
  \/ (exists s, acstr_at segs m LA_STR_X s /\ LA_STR_X <= a <= LA_STR_X + Z.of_nat (length s))
  \/ (LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE)
  \/ (exists kbs tab i nm ix p, anlk_at segs m LA_G_NL kbs /\ aiftab_at segs m LA_G_NL kbs tab
        /\ nth_error tab i = Some (nm, ix) /\ au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p
        /\ acstr_at segs m p nm /\ p <= a <= p + Z.of_nat (length nm)).

Definition kernel_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall kbs, anlk_at segs m LA_G_NL kbs ->
  exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
    /\ nk_next kbs' = 0 /\ 0 <= nk_n_chunks kbs' <= 3
    /\ In (nk_end_errno kbs') nl_errno_tab
    /\ (nk_socket_errno kbs' = 0 \/ In (nk_socket_errno kbs') nl_errno_tab)
    /\ (nk_send_errno kbs' = 0 \/ In (nk_send_errno kbs') nl_errno_tab)
    /\ nk_open kbs' = nk_open kbs /\ nk_opened kbs' = nk_opened kbs
    /\ nk_closed kbs' = nk_closed kbs /\ nk_misuse kbs' = nk_misuse kbs
    /\ nk_n_sent kbs' = nk_n_sent kbs /\ nk_sent kbs' = nk_sent kbs
    /\ nk_n_if kbs' = nk_n_if kbs
    /\ (forall tab, aiftab_at segs m LA_G_NL kbs tab -> aiftab_at segs m' LA_G_NL kbs' tab)
    /\ (forall wp wn, au64_at segs m (aarg regs 0) wp -> au64_at segs m (aarg regs 0 + 8) wn ->
          0 <= wp < 2 ^ 64 -> 0 <= wn < 2 ^ 64 ->
          exists adv, 0 <= adv <= wn
          /\ au64_at segs m' (aarg regs 0) (wp + adv) /\ au64_at segs m' (aarg regs 0 + 8) (wn - adv))
    /\ awrange segs m' (aarg regs 0) 16
    /\ (exists la, au8arr segs m' LA_LONG_ALIAS (la ++ [zb 0]) /\ Z.of_nat (length la) = 300).

Definition kernel_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B KERNEL_A KERNEL_AK 0 KERNEL_SIDE
    kernel_apre kernel_ard kernel_awr kernel_apost.

End c.

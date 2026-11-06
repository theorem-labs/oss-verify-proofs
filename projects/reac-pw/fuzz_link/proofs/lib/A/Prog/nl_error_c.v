(* nl_error (netlink.h:305-315) on image A (fuzz_link.asan 0x86e4c, 2032 bytes; listing
   (internal path) (internal record, sha256 7ca564e0b716)): an NLMSG_ERROR put into the reply
   kernel builds, whole or cut after `cut` payload bytes: nl_begin(w, NL_ERROR), a 20-byte body holding code, nl_put of
   the body, nl_end, nl_pad (netlink.h:225-280). a0 = w (a struct nl_w: b[4096] at NW_B = 0, the 8-byte n at
   NW_N = 4096, the 4-byte full at NW_FULL = 4104, NW_SIZE = 4112), a1 = code, a2 = cut. The plain contract is
   lib/Prog/nl_error_c.v; this file states the SAME link_spec result (`nlw_wf`, `nw_n` does not shrink) in
   link_amem.v's `aleaf` form. nl_error reads through a pointer only w (in the write set) and its own frames, so it
   has no read set (plain `aleaf`, not `aleaf_rd`).

   The image-A code, in order (n is the 8 bytes at w + 4096 each time it is loaded; F is the side frame):
     +0x00..+0x38  push a 160-byte frame; +0x04 `sd zero, 0(sp)`; save ra, s0..s11
     +0x3c..+0x44  s0 := the entry sp; +0x40 `andi sp, sp, -0x20` (realign: up to 16 bytes more); s1 := sp
     +0x48..+0x50  `sd a2, 0x18(s1)` (all 64 bits of cut, in the real frame); s7 := code, s2 := w
     +0x54..+0x68  a1 := the side-stack switch (.got+0xb8 = 0xa1a28 -> 0xaa440, `lw`); s10 := the shadow base
                   (.got+0x60 = 0xa19d0 -> 0xaa438)
     +0x70  `beqz a1, +0x84` (switch 0: the real-stack fallback, s4 := 0)
     +0x74..+0x7c  frame_alloc_1(0x60) (0x3da88); s4 := F
     +0x88..+0x90  s3 := w + 4096; s9 := s4; `bnez s4, +0xb0` (F = 0: the fallback +0x94..+0xac, a frame on the real
                   stack below a probing loop)
     +0xb0..+0xdc  F + 0 := 0x41b58ab3, F + 8 := 0x1d884 (the frame's description, .rodata), F + 16 := 0x86e4c
     +0xbc, +0xe0..+0x118  s8 := the shadow address of F; shadow bytes s8 + 0..3 := 0xf1, s8 + 4..6 := 0xf8,
                   s8 + 7..11 := 0xf3 (left redzone [F, F + 32), the body [F + 32, F + 52) marked unusable, right
                   redzone to F + 96)
     +0xf8, +0x11c  s11 := the shadow address of w + 4096
     +0x120..+0x128  check C1; +0x124 `sd s9, 0x30(s1)` (F, in the real frame)
     +0x12c  s6 := n (= at, nl_begin's start)
     +0x130..+0x1ac  nl_put32(w, 0): `bltu` -4098, n - 4093 (room for 4 bytes, n <= 4092) -> +0x164; no room: check
                   C2, full := 1 (+0x144..+0x15c), -> +0x1b0; room: check C4 of [w + n, w + n + 4) (+0x164..+0x188),
                   4 zero bytes at w + n (+0x18c..+0x198), check C1, n := n + 4 (+0x19c..+0x1ac)
     +0x1b0..+0x234  nl_put16(w, 2): room n <= 4094 (+0x1b8..+0x1cc), no room C2 and full := 1 (+0x1d0..+0x1ec),
                   C3 of [w + n, w + n + 2) (+0x1f0..+0x214), 02 00 at w + n (+0x218..+0x220), C1, n := n + 2
     +0x238..+0x2b8  nl_put16(w, 0), the same (C2 +0x258..+0x274, C3 +0x278..+0x29c, stores +0x2a0..+0x2a4)
     +0x2bc..+0x344  nl_put32(w, 1), as +0x130 (C2 +0x2d8..+0x2f4, C4 +0x2f8..+0x31c, stores +0x320..+0x330)
     +0x348..+0x3dc  nl_put32(w, 0), as +0x130 (C2 +0x36c..+0x388, C4 +0x390..+0x3b4, stores +0x3b8..+0x3c4);
                   s5 := w, s2 := code
     +0x3e0..+0x3f0  s7 := F + 32 (the body); shadow bytes s8 + 4, s8 + 5 := 0, s8 + 6 := 4 (the body's 20 bytes usable)
     +0x3f4..+0x400  checked_memset(F + 36, 0, 16) (0x53214)
     +0x404  `sw s2, 0(s7)`: code into body[0..4) (no instrumented check)
     +0x408..+0x410  a2 := the cut, reloaded; `bgez a2, +0x414`; a cut with bit 63 set becomes 20 (cut')
     +0x414..+0x434  check C1; s2 := F; s4 := w; `bltu` n + cut', 4097 -> +0x458
     +0x438..+0x454  no room: check C2; full := 1; -> +0x484
     +0x458..+0x468  `beqz a2` (cut' = 0: no copy); checked_memcpy(w + n, F + 32, cut') (0x52d78)
     +0x46c..+0x480  check C1; n := n + cut'
     +0x484..+0x494  check C1; nl_end (netlink.h:277-280, nl_set32 :259-263): `bltu` n, at + 4 -> +0x4e0
     +0x498..+0x4dc  check C4 of [w + at, w + at + 4); the 4 bytes of n - at, little-endian, at w + at
     +0x4e0..+0x54c  nl_pad, as attr_text +0x1d4..+0x240: check C1; p := ((n + 3) mod 2 ^ 32) & ~3; `bltu` p, 4097;
                   no room: C2 and full := 1 (+0x504..+0x520); else checked_memset(w + n, 0, p - n) (0x53214) when
                   p <> n (+0x524..+0x538), C1, n := p
     +0x550..+0x568  shadow bytes s8 + 4..6 := 0xf8 (the body unusable again); F + 0 := 0x45e0360e (`sd`)
     +0x56c  `beqz s2, +0x5c0` (F = 0: the fallback's shadow clearing +0x5c0..+0x5ec)
     +0x570..+0x5b0  the 16 shadow bytes of the 128-byte class-1 frame := 0xf5
     +0x5b4..+0x5b8  a0 := the 8 bytes at F + 0x78 (the flag address frame_alloc_1 left at F + fs_frame_bytes 1 - 8);
                   `sb zero, 0(a0)`: the frame's flag := 0, the inline release of a class <= 7 frame (link-a/form/FORM.md (internal record, sha256 13aeff774164) 4.2)
     +0x5f0..+0x62c  sp := s0 - 160; restore; pop; ret
     +0x630..+0x7ec  the error paths: errpath_store4 (0x5a77c), errpath_store_n (0x5a9fc), errpath_load8 (0x5a4fc).

   The instrumented checks (a load of the shadow byte s of an address a and a compare; each failing arm calls an
   errpath_* entry, which the proof shows is not reached):
   - C1, the 8 bytes of n, [w + 4096, w + 4104): the shadow byte of w + 4096, at s11, loaded at +0x120, +0x19c,
     +0x1b0, +0x224, +0x238, +0x2a8, +0x2bc, +0x334, +0x348, +0x3c8, +0x414, +0x470, +0x484, +0x4e0, +0x53c (`lbu`;
     `bnez` -> errpath_load8 with a0 = w + 4096). No slow path: it passes only when s = 0, which
     `range_addressable (ard m) SHADOW_OFF w NW_SIZE` gives (the 8-byte range holds the last byte of its first
     granule, where saddr_ok, Reusable/YG0v.v:29, leaves only s = 0). The calls between the loads leave that byte as
     it was: frame_alloc_1 keeps every byte the runtime does not own outside its window (YG0d.v:305-306
     astack_malloc_realizes; w's shadow is a client byte of kernel's frame, not a runtime-owned one), checked_memset
     / checked_memcpy change only their destination and their window.
   - C2, the 4-byte store of full, [w + 4104, w + 4108): +0x150, +0x1dc, +0x264, +0x2e4, +0x378, +0x444, +0x510
     (`lb`; s = 0 passes, else (a & 7) + 3 < s passes, else errpath_store4).
   - C3, the 2-byte stores into b, [w + n, w + n + 2), n <= 4094: the first byte +0x1fc, +0x284, the last byte
     +0x210, +0x298 (s = 0 or a & 7 < s, else errpath_store_n(a, 2)).
   - C4, the 4-byte stores into b, [w + n, w + n + 4), n <= 4092, and nl_end's [w + at, w + at + 4), at + 4 <= n:
     the first byte +0x170, +0x304, +0x39c, +0x4a4, the last byte (a + 3) +0x184, +0x318, +0x3b0, +0x4b8
     (errpath_store_n(a, 4)).
   All ranges are inside [w, w + NW_SIZE), so `range_addressable (ard m) SHADOW_OFF w NW_SIZE` makes each check pass.
   That is 34 shadow-byte loads = errpath_calls 34 in link-a/facts/asan-facts.tsv (internal record, sha256 05ab19b7928f);
   its `checks` 19 counts the loads whose address is computed in place (C2's 7, C3's 4, C4's 8), not the 15 loads
   of C1 through s11. The whole object (NW_SIZE): kernel's w is a 4112-byte variable whose 514 shadow bytes kernel
   sets to 0 (meta_fill_00, kernel +0x5b0), as convention C2 of the slice states g_nl whole.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x38, +0x48, +0x124 (inside [sp - K, sp)); the four
     runtime calls take ecall_pre-style premises that the walk derives from the journal at the realigned sp (pcap's
     aj_stack_malloc_atS and aj_intrin_atS, A/Prog/YC85G.v); +0x62c ret.
   - K = 160 + 16 + ESTACK = 4272: the 160-byte frame, the realignment slack of +0x40 (the entry sp is 16-aligned, so
     `andi sp, sp, -0x20` lowers sp by 0 or 16), then the deepest callee window, ESTACK for frame_alloc_1, checked_memset and
     checked_memcpy (ecall_pre YG0d.v:285-291; YG0d.v:292-307, :325-343), each called at the realigned sp. link-a/form/FORM.md
     (internal record, sha256 13aeff774164) section 5's 4256 has no slack (convention C4 adds it). The plain K (80) does not carry over.
   - `anlw_at m w bs`, `nlw_wf bs`: every load and store of n, full and b. nlw_wf's n <= 4096 keeps each room test
     exact (no wrap in n - 4093, n + cut', at + 4, n + 3) and n <= 4096 after each step; full is only stored as 1.
   - `apart_frame regs K w NW_SIZE`: the frame stores do not touch w; the destinations of checked_memcpy /
     checked_memset are outside their window [sp' - ESTACK, sp') (dest_ok, YG0d.v:319-320).
   - `a2 <= NL_ERR_BODY \/ 2 ^ 63 <= a2` (the plain cut bound, re-checked on image A): the C test `cut <
     NL_ERR_BODY` (netlink.h:312) is not in the binary. The image-A counterpart of the plain +0x154 `bgez` is
     +0x40c `bgez a2, +0x414` (on all 64 bits of the cut spilled at +0x48 and reloaded at +0x408), which only turns a
     cut with bit 63 set into 20 (+0x410); the counterpart of the plain +0x188 memcpy is +0x468 checked_memcpy(w + n,
     F + 32, cut'), reached whenever cut' <> 0 and n + cut' < 4097. Its source must be addressable
     (`range_addressable x n`, YG0d.v:333): the shadow stores +0x3e8..+0x3f0 make exactly the body's 20 bytes
     [F + 32, F + 52) usable (granules 0, 0, then 4), so a cut' above 20 would take the copy into the unusable rest of
     granule 6 and the right redzone, and the checked call would report. With the bound, cut' <= 20. The one call
     site passes 2 ^ 64 - 1 or 0..7 (below).
   - `amem_range w NW_SIZE`, `range_addressable (ard m) SHADOW_OFF w NW_SIZE`, `shadow_hull_vis (ard m) w NW_SIZE`:
     checks C1..C4; checked_memcpy's and checked_memset's `amem_range d n`, `range_addressable d n` and shadow hull
     (YG0d.v:324, :329-330) of their destinations [w + n, w + n + cut') and [w + n, w + p), inside [w, w + 4096).
   - `aside_room Sc [(1, 1)]` (apre's SIDE): frame_alloc_1's `count_cid 1 (frames Sc) < fs_frames 1` (YG0d.v:295),
     so it returns F = frame_addr ly 1 pos >= 4096 (`frames_bounds`, Reusable/YCbq.v:447-450).
   - NOT premises (the walk derives them from AR, the journal and frame_alloc_1's Post): the .got cells and the
     switch value 1 (AR's const law, YG0f.v:193-195); F's 128 bytes (fs_frame_bytes 1; the code uses 96) present and
     their shadow zero at the return of frame_alloc_1 (YG0d.v:302, :304), so the frame stores, checked_memset(F + 36,
     0, 16) (dest in a frame, below alloc_ceiling, outside the window; its range addressable after +0x3e8..+0x3f0)
     and the copy's source premises hold; the flag address at F + 0x78 (YG0d.v:303, not written by the code before
     +0x5b4); `d + n <= x \/ x + n <= d` of the copy: w is in a live frame, a block, G or the journal's window (apre's
     `ajw` on the write set), so it is not in the free class-1 frame frame_alloc_1 hands out (the side stack's frames
     are pairwise disjoint, AR's al_sep, the lemma above frames_bounds in YCbq.v).
   - the write set `[(w, w + NW_SIZE)]` (the plain one) and apre's `ajw` on it: the stores of n (+0x1ac, +0x234,
     +0x2b8, +0x344, +0x3dc, +0x480, +0x54c), of full (+0x15c, +0x1e8, +0x270, +0x2f0, +0x384, +0x450, +0x51c) and of
     b (+0x18c..+0x198, +0x21c..+0x220, +0x2a0..+0x2a4, +0x324..+0x330, +0x3b8..+0x3c4, +0x4d0..+0x4dc),
     checked_memcpy's [w + n, w + n + cut') and checked_memset's [w + n, w + p). w is never NULL (below). In a run w
     is in kernel's class-8 side frame, so `ajw` holds by `in_frames own`.
   EV = 0 (no allocator event; a side frame is not one: `aleaf`'s `S2 = set_fs (st_fs S2) Sc`), SIDE = [(1, 1)] (its
   own class-1 frame; its callees take none).
   Bytes written outside the window [sp - K, sp) and outside the write set: those of its own class-1 side frame F,
   which it takes and releases inside the call (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 2:
   not in Wr; `frames S2 = frames Sc`): F + 0..24 and F + 0..8 again (+0xd4..+0xdc, +0x568), the body F + 32..52
   (+0x404, checked_memset +0x400), F's 16 shadow bytes (+0xe8..+0x118, +0x3e8..+0x3f0, +0x554..+0x55c, +0x570..+0x5b0),
   F's flag (+0x5b8); frame_alloc_1 sets that flag, zeroes F's shadow and stores the flag address at F + 0x78
   (YG0d.v:301-306). checked_memcpy / checked_memset write their destinations only (YG0d.v aintrin_realizes): inside the
   write set or the body. The real-stack fallback arms are not walked: refuted under the premises (link-a/form/FORM.md
   (internal record, sha256 13aeff774164) 4.2; the recorded answer to question 3): +0x70 `beqz a1` (the switch cell is 1
   by AR's const law), +0x90 `bnez s4` and +0x56c `beqz s2` (F >= 4096 by aside_room and frames_bounds).
   The plain conjuncts carry over as link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 6a's four
   classes require: w apart from the frame and the callee windows, and not in the side frame frame_alloc_1 hands out (by
   `ajw`, above); no u16/u32/u64 view in the Pre or the Post; the source-only test `cut < NL_ERR_BODY` replaced by the
   binary's premise (above), over all 64 bits of a2 as +0x40c tests them; the code's C type is not a premise (+0x404
   stores its low 4 bytes, the Post does not depend on it).

   The call site (kernel +0x1b7c, listing (internal path) (internal record, sha256 7bc02d6772b3)): a0 = s5 = w = kernel's
   class-8 side frame + 0x1130 (kernel +0x4dc; a 4112-byte variable zeroed by checked_memset at kernel +0x5c0, never NULL), reached
   - from +0x6d0..+0x6dc (`kind % 8 = 1`, fuzz_link.c:221-223 [INFERENCE: the arm of the jump table at 0x20f78
     indexed by kind & 7, +0x6b0..+0x6cc, whose entries are data and not read here]): a1 = 0, a2 = -1 = 2 ^ 64 - 1;
   - through +0x1b30..+0x1b78 (`kind % 8 = 2`, fuzz_link.c:224-229; +0x1b2c sets c = 0 when no input is left):
     a1 = msg_build.codes[c & 3] (0x210e0, `lw`, sign-extended), a2 = (slti(sext8 c < 0) - 1) | ((c & 0xff) >> 4 & 7),
     which is 0..7 when c & 0x80 and 2 ^ 64 - 1 otherwise. Both meet the cut bound.

   What does NOT carry over from the plain text:
   - the plain K = 80 (above).
   - the plain `leaf` frame clauses (`munch`, `wmono`, `mem_inv`, `stk`): replaced by the journal and apost's
     `akept` (link_amem.v). Every conjunct of the plain Pre and Post carries over in content; none is false of
     image A (the Post's three: the 4112 bytes stay present and writable, n stays <= 4096 and full in {full, 1},
     n only grows: each put adds, nl_end writes inside [w, w + n), nl_pad sets n to NL_ALIGN(n) >= n).

   SATISFIABILITY WITNESS (the whole Pre, at a real call). The run: LLVMFuzzerTestOneInput calls kernel
   (0x82ec0, 0x832a4, 0x83584 or 0x837e4; a0 = s1 + 0x118, the input cursor) on input bytes that make kernel
   read flags 0, two errno bytes, n = 1 chunk, mode 0, m = 1 message, kind 1: the call at kernel +0x1b7c
   from +0x6d0, nl_error(w, 0, -1), on the w kernel has just zeroed. Registers at 0x86e4c: ra = 0x858b0
   (ret_ok); a0 = w = F8 + 0x1130, F8 = frame_addr ly 8 p8 (kernel's frame); a1 = 0; a2 = 2 ^ 64 - 1 (so
   `2 ^ 63 <= a2`); sp = kernel's realigned sp ((sp_k - 0x160) & ~0x1f), sp mod 16 = 0; gp, tp = as_gp B,
   as_tp B. Memory: w's 4112 bytes all 0 (n = 0, full = 0): anlw_at, nlw_wf. Shadow: w's 514 shadow bytes 0
   (kernel +0x5b0 meta_fill_00), visible (a side frame's shadow is a client range, am_client YG0n.v:221).
   amem_range: w's frame is app memory (`in_app`, frames_bounds). w (fake stack, below alloc_ceiling) is
   below the window [sp - 4272, sp) (`astk_ok`, YCbq.v:330-332). The journal: LLVMFuzzerTestOneInput's,
   `ajournal_gx segs B LA_G 0 [] STK sp0 [sink_token] ly S W0 mem0 md0 own lyc Sc W memc mdc k`
   (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1), own = [(8, p8); (4, p4)] (kernel's
   and LLVMFuzzerTestOneInput's side frames), frames Sc = own; `ajw` of [w, w + 4112) by `in_frames own`
   (0x1130 + 4112 <= 0x2240, the size kernel asks of frame_alloc_8 at +0x68..+0x70); `aside_room Sc [(1, 1)]`:
   count_cid 1 own = 0, 0 + 1 <= fs_frames 1 = 8192;
   STK (LLVMFuzzerTestOneInput's K, which counts kernel's K) covers the chain LLVMFuzzerTestOneInput -> kernel ->
   nl_error; `st_nev S + k + 0 <= EV_MAX`.
   The Post at this witness: w's bytes 0..35 = 24 00 00 00 02 00 00 00 01 00 00 00 00 00 00 00 (nl_end's length 36,
   type NL_ERROR, seq 1) then the 20-byte body (code 0 and 16 zero bytes); n = 36 (NL_ALIGN(36) = 36: no padding),
   full = 0.
   Closed lemma of the function-specific Pre: lib/A/Prog/kernel_witness.v `nl_error_apre_sat : forall segs regs,
   aarg regs 0 = NE_W -> aarg regs 2 = 2 ^ 64 - 1 -> spZ regs = NE_SP -> nl_error_apre segs regs ne_mem` (NE_W =
   kernel's w2 = its class-8 frame + 0x1130, NE_SP = kernel's realigned sp; ne_mem = w2 zero, zero shadow).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition NL_ERROR_A : Z := 0x86e4c.
Lemma NL_ERROR_A_is_entry : NL_ERROR_A = LA_nl_error. Proof. reflexivity. Qed.

(* the stack bound on image A: the 160-byte frame, the 16 bytes the prologue's `andi sp, sp, -0x20` may add, and
   the window of frame_alloc_1 / checked_memset / checked_memcpy *)
Definition NL_ERROR_AFRAME : Z := 160.
Definition NL_ERROR_AK : Z := NL_ERROR_AFRAME + 16 + ESTACK.
Lemma NL_ERROR_AK_val : NL_ERROR_AK = 4272. Proof. reflexivity. Qed.

(* the write set: the struct nl_w (as the plain contract's; w is never NULL) *)
Definition nl_error_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + NW_SIZE)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition nl_error_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs,
    anlw_at segs m (aarg regs 0) bs /\ nlw_wf bs
    /\ apart_frame regs NL_ERROR_AK (aarg regs 0) NW_SIZE
    /\ (aarg regs 2 <= NL_ERR_BODY \/ 2 ^ 63 <= aarg regs 2)
    /\ amem_range (aarg regs 0) NW_SIZE
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) NW_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) NW_SIZE.

Definition nl_error_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs, anlw_at segs m (aarg regs 0) bs ->
    exists bs', anlw_at segs m' (aarg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs'.

Definition nl_error_acontract : Prop :=
  aleaf SK segs rlo rhi B NL_ERROR_A NL_ERROR_AK 0 [(1, 1)] nl_error_apre nl_error_awr nl_error_apost.

End c.

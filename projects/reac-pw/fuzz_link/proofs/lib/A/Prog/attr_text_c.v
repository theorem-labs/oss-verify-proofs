(* attr_text (fuzz_link.c:168-172) on image A (fuzz_link.asan 0x86b18, 820 bytes; listing
   (internal path) (internal record, sha256 03340ee12716)): one attribute holding a text, put
   into the reply kernel builds: `nl_attr_put(w, type, s, strlen(s) + !bare)` (netlink.h:283-289, nl_put :225-235,
   nl_pad :247-251). a0 = w (a struct nl_w: b[4096] at NW_B = 0, the 8-byte n at NW_N = 4096, the 4-byte full at
   NW_FULL = 4104, NW_SIZE = 4112), a1 = type, a2 = s, a3 = bare. The plain contract is lib/Prog/attr_text_c.v; this
   file states the SAME link_spec result (`nlw_wf`, `nw_n` does not shrink) in the `aleaf_rd` form of link_amem.v
   (`aleaf` with the read set `Rd`, FORM change of 2026-10-30: s is read through a2 and is not in the write set).

   The image-A code, in order (n is the 8 bytes at w + 4096 each time it is loaded):
     +0x00..+0x20  push a 64-byte frame; save ra, s0..s6
     +0x24..+0x30  s3 := bare, s2 := s, s4 := type, s1 := w
     +0x34..+0x3c  s6 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x40..+0x44  s0 := w + 4096
     +0x48..+0x4c  wrapper_strlen(s) (0x43044): a0 := the index of the first NUL at s
     +0x50..+0x5c  s5 := (s0 >> 3) + s6; check C1
     +0x60..+0x7c  a2 := n; s3 := strlen(s) + (a3 = 0) (`seqz` of all 64 bits of a3) = len; `bltu` -4098, n - 4095:
                   room for 2 bytes (n <= 4094) -> +0xa0
     +0x80..+0x9c  no room: check C2; full := 1 (`sw`); -> +0xec
     +0xa0..+0xd4  check C3 of [w + n, w + n + 2); `sb` the low two bytes of len + 4, little-endian, at w + n
     +0xd8..+0xe8  check C1; n := n + 2
     +0xec..+0x16c the same for the low two bytes of type: room test +0xfc..+0x104, no room +0x108..+0x124 (C2,
                   full := 1, -> +0x170), C3 +0x128..+0x14c, stores +0x150..+0x158, C1 and n := n + 2 +0x15c..+0x16c
     +0x170..+0x188  check C1; `bltu` n + len, 4097: room for len bytes -> +0x1ac
     +0x18c..+0x1a8  no room: check C2; full := 1; -> +0x1d4
     +0x1ac..+0x1bc  `beqz s3` (len = 0: no copy); checked_memcpy(w + n, s, len) (0x52d78)
     +0x1c0..+0x1d0  check C1; n := n + len
     +0x1d4..+0x1f4  check C1; p := ((n + 3) mod 2 ^ 32) & ~3 (NL_ALIGN: `addi`, `srliw`, `slli`);
                   `bltu` p, 4097 -> +0x218
     +0x1f8..+0x214  no room: check C2; full := 1; -> +0x244
     +0x218..+0x22c  `beq` p, n (no padding); checked_memset(w + n, 0, p - n) (0x53214)
     +0x230..+0x240  check C1; n := p
     +0x244..+0x268  restore, pop, ret
     +0x26c..+0x330  the error paths: errpath_store4 (0x5a77c), errpath_store_n (0x5a9fc), errpath_load8 (0x5a4fc).

   The instrumented checks (a load of the shadow byte s of an address a and a compare; each failing arm calls an
   errpath_* entry, which the proof shows is not reached):
   - C1, the 8 bytes of n, [w + 4096, w + 4104): the shadow byte of w + 4096, at s5, loaded at +0x58, +0xd8, +0xec,
     +0x15c, +0x170, +0x1c0, +0x1d4, +0x230 (`lbu`; `bnez` -> errpath_load8 with a0 = w + 4096). No slow path: it
     passes only when s = 0. `range_addressable (ard m) SHADOW_OFF w NW_SIZE` gives s = 0: the 8-byte range holds the
     last byte of its first granule, where saddr_ok (Reusable/YG0v.v:29) leaves only s = 0. The callees between
     the loads leave that byte as it was: checked_memcpy / checked_memset change no byte outside their destination
     (inside w->b) and their window (YG0d.v aintrin_realizes).
   - C2, the 4-byte store of full, [w + 4104, w + 4108): +0x8c, +0x114, +0x198, +0x204 (`lb`; s = 0 passes, else
     (a & 7) + 3 < s passes, else errpath_store4).
   - C3, the 2-byte stores into b, [w + n, w + n + 2) with n <= 4094: the first byte +0xac, +0x134 (s = 0 or
     a & 7 < s, else errpath_store_n(a, 2)), the last byte +0xc0, +0x148 (the same of a + 1).
   All three ranges are inside [w, w + NW_SIZE), so `range_addressable (ard m) SHADOW_OFF w NW_SIZE` makes each check
   pass (C2 and C3 by saddr_ok of each byte). That is 16 shadow-byte loads = errpath_calls 16 in
   link-a/facts/asan-facts.tsv (internal record, sha256 05ab19b7928f); its `checks` 9 counts only the loads whose
   address is computed in place (+0x58, C2's 4, C3's 4), not the 7 reloads of C1 through s5. The whole object (NW_SIZE)
   and not the 4108 bytes the checks cover: kernel's w is a 4112-byte variable whose 514 shadow bytes kernel sets to 0
   (meta_fill_00, kernel +0x5b0), as convention C2 of the slice states g_nl whole.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x20 (inside [sp - K, sp)); the three runtime
     calls take ecall_pre-style premises that the walk derives from the journal at sp - 64 (link_ajkit.v
     aj_gx_intrin_at for checked_memcpy / checked_memset, aj_gx_strlen_at for the strlen wrapper); +0x268 ret.
   - K = 64 + ESTACK = 4160: the 64-byte frame (no realignment: no `andi sp`), then the deepest callee window,
     ESTACK for checked_memcpy / checked_memset (YG0d.v:325-343 aintrin_realizes) and for wrapper_strlen: link's
     strlen contract (lib/A/Rt/RtString.v:74-84 `astrlen_realizes`, the libc port of
     plugin-hostd/fuzz_command's, on the form branch since f961453c8093) takes `PRE ESTACK` and `aread_ok ESTACK`.
     The plain K (64: strlen, memcpy and memset counted as using no stack) does not carry over.
   - `anlw_at m w bs`, `nlw_wf bs`: every load and store of n, full and b. nlw_wf's n <= 4096 keeps each room test
     exact (no wrap in n - 4095, n + len, n + 3) and n <= 4096 after each step; full is only ever stored as 1.
   - `s <> 0`, `acstr_at m s str`: the strlen wrapper returns |str| (the first NUL); checked_memcpy reads
     len = |str| + (a3 = 0) <= |str| + 1 bytes of [s, s + |str| + 1).
   - `|str| + 1 < 2 ^ 32`: the strlen contract's `aread_ok ESTACK x (|str| + 1)` carries `0 <= n < 2 ^ 32`
     (lib/A/Rt/RtDefs.v:36), as astrnlen_realizes's `k + 1 < 2 ^ 32` (YG0d.v:414); amem_range alone
     allows a high-memory string of up to 2 ^ 47 bytes (the kernel comparer's refusal, 2026-10-30).
   - the slack (`exists slack, abytes m (s + |str| + 1) slack /\ (- (s + |str| + 1)) mod 8 <= |slack|`): the plain
     conjunct (AMEND-slot item 1); the strlen contract asks the bytes after the NUL to its 8-byte granule's end to
     be visible (`atail_vis (x + |str|)`, RtString.v:80, RtDefs.v:54-55: musl's word loop). No shadow
     premise on those bytes: the runtime's check covers [s, s + |str| + 1) only, and long_alias's bytes 301..303
     share a granule whose shadow byte is 5.
   - `apart w NW_SIZE s (|str| + 1)`: checked_memcpy's `d + n <= x \/ x + n <= d` (YG0d.v:332), and the stores of
     +0xd0..+0xd4 and +0x154..+0x158 do not change the string before the copy reads it.
   - `apart_frame regs K w NW_SIZE`: the frame stores do not touch w; checked_memcpy's / checked_memset's dest_ok
     (outside their window [sp - 64 - ESTACK, sp - 64), YG0d.v:319-320).
   - `apart_frame regs K s (|str| + 1)`: the frame stores do not touch the string; checked_memcpy's src_ok
     (YG0d.v:321-322) and the strlen wrapper's source outside its window. (It also follows from `akb` on the read set.)
   - `amem_range w NW_SIZE`, `range_addressable (ard m) SHADOW_OFF w NW_SIZE`, `shadow_hull_vis (ard m) w NW_SIZE`:
     checks C1..C3; checked_memcpy's and checked_memset's `amem_range d n`, `range_addressable d n` and shadow hull
     (YG0d.v:324, :329-330) of their destinations [w + n, w + n + len) and [w + n, w + p), both inside [w, w + 4096).
   - `amem_range s (|str| + 1)`, `range_addressable (ard m) SHADOW_OFF s (|str| + 1)`, `shadow_hull_vis (ard m) s
     (|str| + 1)`: checked_memcpy's source premises (YG0d.v:332-333), and the strlen wrapper's range check of
     [s, s + |str| + 1) (the runtime checks the bytes it read, as astrnlen_realizes's premises YG0d.v:416-418 say).
     `0 <= len < 2 ^ 32` and `x + len <= 2 ^ 63` follow: n + len <= 4096 from the room test, and amem_range.
   - the read set `attr_text_ard` (aleaf_rd's `akb` on each byte): the string and its NUL are read through a2 and
     are not in the write set; `akb` puts them where the call keeps them, so no callee's frame_alloc or malloc can
     hand them out. NOT in it: the slack after the NUL. No value of it enters the Post (the strlen contract asks it
     only visible, `atail_vis`), and for a global's string it is the global's redzone, bytes of as_owned_static where
     `akb`'s image clause fails (the slot entry comparer: long_alias + 301..303, the slack after .str.1, .str.8
     and the texts strings); its visibility at the strlen call is the Pre's slack premise (no callee runs before it).
   - the write set `[(w, w + NW_SIZE)]` (the plain one) and apre's `ajw` on it: the stores of n (+0xe8, +0x16c,
     +0x1d0, +0x240), of full (+0x98, +0x120, +0x1a4, +0x210) and of b (+0xd0..+0xd4, +0x154..+0x158),
     checked_memcpy's [w + n, w + n + len) and checked_memset's [w + n, w + p). w is never NULL (below). In a run w
     is in kernel's class-8 side frame, so `ajw` holds by `in_frames own`.
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).
   Bytes written outside the window [sp - K, sp): those of the write set only. The runtime callees write nothing
   else: checked_memcpy / checked_memset write their destination only (YG0d.v aintrin_realizes), and the strlen
   wrapper writes nothing outside its window (the libc contract to come; the runtime's strlen stores nothing).
   The plain conjuncts carry over as link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 6a's four
   classes require: s apart from all writes (w, the frame, the callee windows); no u16/u32/u64 view in the Pre or the
   Post; the C types of type and bare are not premises (+0x150..+0x158 store type's low two bytes, +0x64 tests all 64
   bits of a3, and the Post depends on neither); attr_text calls no allocator.

   The call sites (kernel, listing (internal path) (internal record, sha256 7bc02d6772b3); w = s5 = kernel's
   class-8 side frame + 0x1130, set at kernel +0x4dc, a 4112-byte variable zeroed by checked_memset at kernel +0x5c0, never NULL):
   - +0xb40, reached from +0xb10..+0xb20 (a % 6 = 0: a1 = 20, a2 = s11 = texts[(a >> 3) % 11] loaded at +0xa70,
     or .str.1 0x20fc0 when no input is left, +0xac8; a3 = a & 0x80), from +0xadc..+0xb0c (a % 6 = 1: long_alias
     0x62fd40 after checked_memset(long_alias, 'a', 300) at +0xaf8; a1 = 20; a3 = 0) and from +0xb24..+0xb3c
     (a % 6 = 4: a1 = 3, a2 = .str.8 0x210c0 = "x", a3 = 0);
   - +0xdc8 (a % 6 = 2 or 3, inside the nest): a1 = 1, a2 = s11 = t, a3 = s7 & 0x80.

   What does NOT carry over from the plain text:
   - the plain K = 64 (above).
   - the plain `leaf` frame clauses (`munch`, `wmono`, `mem_inv`, `stk`): replaced by the journal and apost's
     `akept` (link_amem.v). Every conjunct of the plain Pre and Post carries over in content; none is false of
     image A (the Post's three: the 4112 bytes stay present and writable, n stays <= 4096 and full in {full, 1},
     n only grows).

   SATISFIABILITY WITNESS (the whole Pre, at a real call). The run: LLVMFuzzerTestOneInput calls kernel (0x82ec0,
   0x832a4, 0x83584 or 0x837e4; a0 = s1 + 0x118, the input cursor) on input bytes that make kernel read flags 0,
   two errno bytes, n = 1 chunk, mode 0, m = 1 message, kind 0 (RTM_NEWLINK: nl_begin and the 16-byte ifinfomsg,
   so n = 32), one attribute, a = 4: the call at kernel +0xb40 from +0xb24, attr_text(w, 3, "x", 0).
   Registers at 0x86b18: ra = 0x84874 (ret_ok); a0 = w = F8 + 0x1130, F8 = frame_addr ly 8 p8 (kernel's frame);
   a1 = 3; a2 = 0x210c0; a3 = 0; sp = kernel's realigned sp ((sp_k - 0x160) & ~0x1f, sp_k kernel's entry sp), so
   sp mod 16 = 0; gp, tp = as_gp B, as_tp B.
   Memory: w's 4112 bytes: 00 00 00 00 10 00 00 00 01 00 00 00 00 00 00 00 (nlmsghdr, length 0 until nl_end, type 16,
   seq 1), 16 zero bytes (ifinfomsg), zeros to 4096, n = 32, full = 0: anlw_at, nlw_wf. At 0x210c0: 78 00 and the 6
   bytes after it ([INFERENCE] zero: .rodata redzone): acstr_at with str = "x", slack of 6 bytes = (-(0x210c2))
   mod 8. Shadow: w's 514 shadow bytes 0 (kernel +0x5b0 meta_fill_00), visible (a side frame's shadow is a client
   range, am_client YG0n.v:221); the granule of 0x210c0 has shadow byte 2 or 0 ([INFERENCE] ASan gives a string
   literal a right redzone; .str.8 ends 30 bytes before msg_build.codes at 0x210e0), and either makes
   `range_addressable ... 0x210c0 2` true; the hull's shadow bytes are visible ([INFERENCE] the image's shadow is in
   the shadow band AR reads, zshadow_ok YG0n.v:188-191 and as_zero_shadow). amem_range: 0x210c2 < kLowMemEnd; w's
   frame is app memory (`in_app`, frames_bounds YCbq.v:447-450). Separation: w (fake stack, below alloc_ceiling)
   and 0x210c0 (image) are below the window [sp - 4160, sp) (`astk_ok`, YCbq.v:330-332), and apart.
   The journal: LLVMFuzzerTestOneInput's, `ajournal_gx segs B LA_G 0 [] STK sp0 [sink_token] ly S W0 mem0 md0 own lyc
   Sc W memc mdc k` (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1), own = [(8, p8); (4, p4)]
   (kernel's and LLVMFuzzerTestOneInput's side frames), frames Sc = own; `ajw` of [w, w + 4112) by `in_frames own`
   (0x1130 + 4112 <= 0x2240, the size kernel asks of frame_alloc_8 at +0x68..+0x70); STK (LLVMFuzzerTestOneInput's K,
   which counts kernel's K) covers the chain LLVMFuzzerTestOneInput -> kernel -> attr_text;
   `st_nev S + k + 0 <= EV_MAX`; `aside_room Sc []`. The read set [0x210c0, 0x210c1] ("x" and its NUL): image bytes
   outside as_owned_static, errno and the write set, so `akb` holds by akept's image clause.
   The Post at this witness: bytes 32..39 of w = 06 00 03 00 78 00 00 00 (rta_len 6, type 3, "x", NUL, 2 bytes of
   padding by checked_memset), n = 40, full = 0.
   Closed lemma of the function-specific Pre: lib/A/Prog/kernel_witness.v `attr_text_apre_sat : forall segs regs,
   aarg regs 0 = AT_W -> aarg regs 2 = AT_S -> spZ regs = AT_SP -> attr_text_apre segs regs at_mem` (AT_W = kernel's
   class-8 frame + 0x1130, AT_S = LA_STR_X, AT_SP = kernel's realigned sp; at_mem = w2 as above, the .rodata
   bytes, zero shadow over the hulls).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition ATTR_TEXT_A : Z := 0x86b18.
Lemma ATTR_TEXT_A_is_entry : ATTR_TEXT_A = LA_attr_text. Proof. reflexivity. Qed.

(* the stack bound on image A: the 64-byte frame and the deepest runtime callee's window (ESTACK: checked_memcpy,
   checked_memset, and link's strlen contract lib/A/Rt/RtString.v astrlen_realizes) *)
Definition ATTR_TEXT_AFRAME : Z := 64.
Definition ATTR_TEXT_AK : Z := ATTR_TEXT_AFRAME + ESTACK.
Lemma ATTR_TEXT_AK_val : ATTR_TEXT_AK = 4160. Proof. reflexivity. Qed.

(* the write set: the struct nl_w (as the plain contract's; w is never NULL) *)
Definition attr_text_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + NW_SIZE)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the read set: the string at a2 and its NUL (not the bytes after the NUL: header) *)
Definition attr_text_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  exists s, acstr_at segs m (aarg regs 2) s /\ aarg regs 2 <= a <= aarg regs 2 + Z.of_nat (length s).

Definition attr_text_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs s,
    anlw_at segs m (aarg regs 0) bs /\ nlw_wf bs
    /\ aarg regs 2 <> 0 /\ acstr_at segs m (aarg regs 2) s /\ Z.of_nat (length s) + 1 < 2 ^ 32
    /\ (exists slack, abytes segs m (aarg regs 2 + Z.of_nat (length s) + 1) slack
          /\ (- (aarg regs 2 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))
    /\ apart (aarg regs 0) NW_SIZE (aarg regs 2) (Z.of_nat (length s) + 1)
    /\ apart_frame regs ATTR_TEXT_AK (aarg regs 0) NW_SIZE
    /\ apart_frame regs ATTR_TEXT_AK (aarg regs 2) (Z.of_nat (length s) + 1)
    /\ amem_range (aarg regs 0) NW_SIZE
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) NW_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) NW_SIZE
    /\ amem_range (aarg regs 2) (Z.of_nat (length s) + 1)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 2) (Z.of_nat (length s) + 1)
    /\ shadow_hull_vis (ard segs m) (aarg regs 2) (Z.of_nat (length s) + 1).

Definition attr_text_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs, anlw_at segs m (aarg regs 0) bs ->
    exists bs', anlw_at segs m' (aarg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs'.

Definition attr_text_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B ATTR_TEXT_A ATTR_TEXT_AK 0 []
    attr_text_apre attr_text_ard attr_text_awr attr_text_apost.

End c.

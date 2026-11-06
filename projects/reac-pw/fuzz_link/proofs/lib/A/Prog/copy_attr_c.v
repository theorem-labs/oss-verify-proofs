(* copy_attr (reac_link_alias.c:25-35) on image A (fuzz_link.asan 0x89438, 204 bytes; listing
   (internal path) (internal record, sha256 cabe69abda9c)): the library's cut of an
   attribute's text into a buffer. a0 = a (a struct rtattr), a1 = out, a2 = n. The plain contract is
   lib/Prog/copy_attr_c.v; this file states the SAME link_spec result (`cut_text`) in link_amem.v's `aleaf` form.

   The image-A code, in order:
     +0x00..+0x18  push a 48-byte frame; save ra, s0..s4           (before the NULL test, unlike the plain code)
     +0x1c  beqz a1 -> +0x90; +0x24 beqz a2 -> +0x90               (out NULL or n = 0: restore and return)
     +0x2c..+0x34  s4 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x38..+0x44, +0xb0..+0xbc  the instrumented check of the 2-byte load of a->rta_len: shadow byte s of a; s = 0
                   passes; else (a & 7) + 1 < s passes; else errpath_load2 (0x5a3bc)
     +0x48  lhu a1, 0(a): l;  +0x4c..+0x58  wrapper_strnlen(a + 4, l - 4) (0x43048)
     +0x5c..+0x64  s3 := r if r < n (unsigned) else n - 1
     +0x6c..+0x74  checked_memcpy(out, a + 4, s3) (0x52d78)
     +0x78..+0x88, +0xc0..+0xc4  the instrumented check of the 1-byte store to out + s3: shadow byte s of out + s3;
                   s = 0 passes; else (out + s3) & 7 < s passes; else errpath_store1 (0x5a63c)
     +0x8c  sb zero, 0(out + s3);  +0x90..+0xac  restore, pop, ret.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x18 (inside [sp - K, sp)); the two runtime
     calls take ecall_pre-style premises that the walk derives from the journal at sp - 48 (pcap's aj_intrin_atS,
     A/Prog/YC85G.v, for checked_memcpy; for the strnlen wrapper no journal lift exists yet: pcap's aj_strcmp_at,
     A/Prog/PcapFuzzFopen.v:109-125, is the model); +0xac ret.
   - K = 48 + 2 * ESTACK = 8240: the 48-byte frame, then the deepest callee window, the strnlen wrapper's
     [sp' - 2 * ESTACK, sp') of Reusable/YG0d.v:402-420 astrnlen_realizes (checked_memcpy's is ESTACK,
     YG0d.v:318-336). The plain K (80 = 48 + strnlen's 32) does not carry over.
   - `au16_at m a l`, `RTA_HDR <= l <= 65535`: +0x48 `lhu`. The range is repeated in the Post (its walker's lesson:
     `au16_at`, like `u16_at`, fixes only l mod 2 ^ 16).
   - `abytes m (a + 4) pay`, `length pay = l - 4`: the strnlen wrapper reads the payload up to its first NUL or to
     l - 4 bytes; checked_memcpy reads s3 <= l - 4 of them.
   - `0 < a`, `amem_range a l`: the strnlen wrapper's `0 < x` and amem_range; checked_memcpy's `amem_range x n` and
     `x + n <= 2 ^ 63` (YG0d.v:317, :321, :325).
   - `apart_frame regs K a l`: the attribute is outside [sp - K, sp): the frame stores do not touch it, and the
     wrapper and checked_memcpy ask their source to be outside their own windows (YG0d.v:315, :409).
   - `range_addressable (ard m) SHADOW_OFF a 2`: the check +0x38..+0x44 passes (s = 0, or a & 7 < s - 1).
   - `range_addressable (ard m) SHADOW_OFF (a + 4) (l - 4)` and its `shadow_hull_vis`: the strnlen wrapper checks
     the bytes it read, checked_memcpy checks [a + 4, a + 4 + s3) and reads the shadow hull (YG0d.v:323-326).
   - the visible bytes after the attribute up to its 8-byte granule's end: a placeholder for the wider strnlen
     contract (the libc slice's), whose wrapper may read the payload word-wise; the kit's astrnlen_realizes asks the
     same of the bytes after the NUL (YG0d.v:412).
   - out <> 0 and n >= 1 (both tests +0x1c, +0x24 fall through):
     `apart_frame regs K out n`: the frame stores, and checked_memcpy's dest outside its window (YG0d.v:313);
     `apart out n (a + 4) (l - 4)`: checked_memcpy's `d + n <= x \/ x + n <= d` (YG0d.v:325);
     `abuf m out n`: checked_memcpy's dest is writable (dest_ok), and +0x8c's store;
     `amem_range out n`: checked_memcpy's dest range;
     `range_addressable (ard m) SHADOW_OFF out n` and its `shadow_hull_vis`: checked_memcpy's dest check, and the
     check +0x78..+0x88 of out + s3 (s3 <= n - 1).
   - the write set `[aivl out n]` and apre's `ajw` on it: checked_memcpy writes [out, out + s3) and +0x8c writes
     out + s3. A NULL out owns no byte (aivl, the plain L7 rule): with the plain `(out, out + n)` the `ajw` premise
     would ask the caller to let it write [0, n), which no journal does.
   - the read set `copy_attr_ard` = the attribute's bytes [a, a + l), and aleaf_rd's premise that each is
     a byte `akept` keeps (`akb`: a heap block, a side frame, the image, or the real-stack row [ly_stk_lo,
     ly_stk_hi) outside [sp - K, sp)): the code reads them at +0x48 (`lhu`, a and a + 1), and the strnlen
     wrapper and checked_memcpy read the payload [a + 4, a + l). Without it the attribute may lie in a free side
     frame or a free heap range, which the Pre's byte and shadow facts do not exclude; a frame_alloc / malloc
     in the caller's chain could hand that range out and write it, and the Post's `cut_text pay n`, over the
     bytes the Pre read, would not speak of the bytes the code reads (the gap in link-a/form/FORM.md
     (internal record, sha256 13aeff774164) section 11). The real caller nl_talk passes an attribute inside the
     reply in its class-9 side frame (0x88d00), which is a frame of Sc: `akb`'s frame clause.
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   What does NOT carry over from the plain text:
   - the plain Post's `out = 0 -> m' = m`. On image A the frame is pushed at +0x00..+0x18, BEFORE `beqz a1` at
     +0x1c, so memory changes on that path too; apost's `akept` (everything outside [sp - K, sp) and the write set,
     which is empty for out = 0) is the true statement, as the UBSan twin's `munch [(sp - 80, sp)]` is.
   - the plain `arg regs 0 + RTA_HDR < 2 ^ 64`: implied by `amem_range a l`.

   THE STRNLEN CALLEE (open, see link-a/form/FORM.md (internal record, sha256 13aeff774164) section 10 item 8; owner: libc slice):
   the released wrapper contract astrnlen_realizes (YG0d.v:402-420) applies only when a NUL lies at an index k with k + 8 <= the
   bound. copy_attr calls it on a payload the input controls: with no NUL, with a payload under 8 bytes, or as in the witness of
   link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) ("ab\0\0": bound 4, NUL at 2), the premise is false. The memchr contract
   has the same bound (YG0d.v:388). This contract does not narrow its premises to that case; its walk needs the wider strnlen contract.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition COPY_ATTR_A : Z := 0x89438.
Lemma COPY_ATTR_A_is_entry : COPY_ATTR_A = LA_copy_attr. Proof. reflexivity. Qed.

(* the stack bound on image A: the 48-byte frame and the strnlen wrapper's window *)
Definition COPY_ATTR_AFRAME : Z := 48.
Definition COPY_ATTR_AK : Z := COPY_ATTR_AFRAME + 2 * ESTACK.
Lemma COPY_ATTR_AK_val : COPY_ATTR_AK = 8240. Proof. reflexivity. Qed.

(* the write set: the buffer, which a NULL out does not own *)
Definition copy_attr_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [aivl (aarg regs 1) (aarg regs 2)].

(* the read set: the attribute's bytes [a, a + l), with l the 16-bit length at a (bounded as in the Pre, so the
   length is the one the code's `lhu` reads) *)
Definition copy_attr_ard (segs : list Segment) (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  exists l, au16_at segs m (aarg regs 0) l /\ RTA_HDR <= l <= 65535 /\ rd_ivl (aarg regs 0) (aarg regs 0 + l) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition copy_attr_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists l pay,
    au16_at segs m (aarg regs 0) l /\ RTA_HDR <= l <= 65535
    /\ abytes segs m (aarg regs 0 + RTA_HDR) pay
    /\ Z.of_nat (length pay) = l - RTA_HDR
    /\ 0 < aarg regs 0 /\ amem_range (aarg regs 0) l
    /\ apart_frame regs COPY_ATTR_AK (aarg regs 0) l
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) 2
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0 + RTA_HDR) (l - RTA_HDR)
    /\ (0 < l - RTA_HDR -> shadow_hull_vis (ard segs m) (aarg regs 0 + RTA_HDR) (l - RTA_HDR))
    /\ (forall b, aarg regs 0 + l <= b < (aarg regs 0 + l + 7) / 8 * 8 -> ard segs m b <> None)
    /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 ->
          apart_frame regs COPY_ATTR_AK (aarg regs 1) (aarg regs 2)
          /\ apart (aarg regs 1) (aarg regs 2) (aarg regs 0 + RTA_HDR) (l - RTA_HDR)
          /\ abuf segs m (aarg regs 1) (aarg regs 2)
          /\ amem_range (aarg regs 1) (aarg regs 2)
          /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 1) (aarg regs 2)
          /\ shadow_hull_vis (ard segs m) (aarg regs 1) (aarg regs 2)).

Definition copy_attr_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  (aarg regs 1 <> 0 -> 1 <= aarg regs 2 ->
     forall l pay, au16_at segs m (aarg regs 0) l -> RTA_HDR <= l <= 65535 ->
       abytes segs m (aarg regs 0 + RTA_HDR) pay ->
       Z.of_nat (length pay) = l - RTA_HDR ->
       acstr_at segs m' (aarg regs 1) (cut_text pay (aarg regs 2)))
  /\ (aarg regs 1 <> 0 -> 1 <= aarg regs 2 -> abuf segs m' (aarg regs 1) (aarg regs 2)).

Definition copy_attr_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B COPY_ATTR_A COPY_ATTR_AK 0 [] copy_attr_apre (copy_attr_ard segs) copy_attr_awr
    copy_attr_apost.

End c.

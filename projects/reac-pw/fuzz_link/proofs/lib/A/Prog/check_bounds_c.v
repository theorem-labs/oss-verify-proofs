(* check_bounds (fuzz_link.c:555-566, text_within :639-642) on image A (fuzz_link.asan 0x868ac, 132 bytes; listing
   (internal path) (internal record, sha256 fbb55f0071c4)): a text written into a buffer
   of `cap` bytes ends in a NUL inside them, and the guard byte after them is as text_buf left it. a0 = buf, a1 = cap.
   The plain contract is lib/Prog/check_bounds_c.v; this file states the same premises in link_amem.v's `aleaf_rd` form.

   The image-A code, in order:
     +0x00..+0x10  push a 32-byte frame; save ra, s0, s1, s2
     +0x14  s0 := cap;  +0x18..+0x20  s2 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW,
                   which holds LA_SHADOW_CELL = 0xaa438, which holds the base);  +0x24  s1 := buf
     +0x28..+0x30  wrapper_memchr(buf, 0, cap) (0x43060)
     +0x34  beqz a0 -> +0x70 (abort path)                              (no NUL among the cap bytes)
     +0x38..+0x48, +0x78..+0x80  the instrumented check of the 1-byte load of buf[cap]: shadow byte s of buf + cap;
                   s = 0 passes; else (buf + cap) & 7 < s passes; else errpath_load1 (0x5a31c)
     +0x4c  lbu a0, 0(buf + cap);  +0x50..+0x54  a0 <> 0x5a -> +0x70 (abort path)
     +0x58..+0x6c  restore, pop, ret
     +0x70  jal before_abort (0x5b318); +0x74 jal abort (0x90ac4).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x10 (inside [sp - K, sp)); the memchr call takes
     ecall_pre at sp' = sp - 32, which the walk derives from the journal; +0x6c ret.
   - K = 32 + ESTACK = 4128: the 32-byte frame, then the memchr wrapper's window [sp' - ESTACK, sp') (the general
     memchr contract, boxreg origin/ossv/recipes lib/A/Rt/MemchrDef.v `amemchr_realizes`, takes ecall_pre; the
     port onto link is the libc slice's). No realignment. The plain K (32: memchr counted as using no stack) does
     not carry over.
   - `aarg regs 0 <> 0`: memchr's `0 < x` (the caller skips the call for a NULL buffer: LLVMFuzzerTestOneInput
     0x836f0 `beqz s7`, 0x83704 `beqz s10`).
   - `1 <= aarg regs 1`, `aarg regs 1 < 2 ^ 32`: memchr's `0 <= n < 2 ^ 32` (cap < 40 at both call sites,
     fuzz_link.c:680), and `0 < n` for its shadow hull.
   - `atbuf_at m buf cap bs`: the cap bytes memchr reads and the guard byte 0x5a that +0x4c reads; `In (zb 0) bs`:
     memchr finds a NUL (its result `x + k` with k < cap is not 0), so +0x34 falls through; the guard makes +0x54
     fall through. THE ABORT PATH IS UNREACHABLE under these two.
   - `amem_range buf cap`: memchr's amem_range (and its `x + n <= 2 ^ 63`).
   - `range_addressable (ard m) SHADOW_OFF buf (cap + 1)`: memchr's range check of [buf, buf + cap) and the check
     +0x38..+0x48 of buf + cap (YG0v.v check_passes_lb); text_buf's malloc(cap + 1) block has exactly these cap + 1
     bytes addressable.
   - `shadow_hull_vis (ard m) buf cap`: memchr's shadow hull (cap >= 1).
   - `apart_frame regs K buf (cap + 1)`: the buffer is outside this frame (the frame stores do not change it) and
     outside memchr's window (its `src_ok`). memchr's `rom_view` premise is no premise here: it follows from apre's
     `arodata_okP` and the image instance.
   The write set is empty. The read set (`aleaf_rd`): the bytes read through the argument, [buf, buf + cap] (the cap
   bytes and the guard). EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   What does NOT carry over from the plain text: nothing is false of image A. The plain Post `only_frame` (True)
   stays True; `akept` gives the frame clause.
   Released proofs (rule 24): none of check_bounds (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).

   Satisfiability witness (op_read, LLVMFuzzerTestOneInput 0x836fc): buf = the kind buffer text_buf(kc) gave, a
   malloc(kc + 1) block, kc = 16; its bytes after reac_link_alias_read: a NUL at index 0 (reac_link_alias_read stores
   it first) and 0x5a at 1..16 (bs = [0] ++ 15 x 0x5a; the guard at index 16 is 0x5a); shadow of the block's three
   granules 0, 0, 1; sp = LLVMFuzzerTestOneInput's realigned sp on the real stack, above alloc_ceiling, the block
   below it. The closed lemma of `check_bounds_apre` is in lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_BOUNDS_A : Z := 0x868ac.
Lemma CHECK_BOUNDS_A_is_entry : CHECK_BOUNDS_A = LA_check_bounds. Proof. reflexivity. Qed.

(* the stack bound on image A: the 32-byte frame and the memchr wrapper's window *)
Definition CHECK_BOUNDS_AFRAME : Z := 32.
Definition CHECK_BOUNDS_AK : Z := CHECK_BOUNDS_AFRAME + ESTACK.
Lemma CHECK_BOUNDS_AK_val : CHECK_BOUNDS_AK = 4128. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_bounds_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

(* the read set: the cap bytes and the guard byte *)
Definition check_bounds_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  rd_ivl (aarg regs 0) (aarg regs 0 + aarg regs 1 + 1) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_bounds_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs,
    aarg regs 0 <> 0 /\ 1 <= aarg regs 1 < 2 ^ 32
    /\ atbuf_at segs m (aarg regs 0) (aarg regs 1) bs /\ In (zb 0) bs
    /\ amem_range (aarg regs 0) (aarg regs 1)
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) (aarg regs 1 + 1)
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) (aarg regs 1)
    /\ apart_frame regs CHECK_BOUNDS_AK (aarg regs 0) (aarg regs 1 + 1).

(* the abort path is not taken; the plain Post `only_frame` is True *)
Definition check_bounds_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Definition check_bounds_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B CHECK_BOUNDS_A CHECK_BOUNDS_AK 0 []
    check_bounds_apre check_bounds_ard check_bounds_awr check_bounds_apost.

End c.

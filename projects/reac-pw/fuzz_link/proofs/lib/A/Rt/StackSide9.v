(* The image-A contracts of the class-9 side-stack routines of reac-pw/fuzz_link's asan build (pin 059dae63e07c):
   frame_alloc_9 (0x3e15c, 376 B, 94 instructions) and frame_release_9 (0x3e2d4, 80 B, 20 instructions). Their one
   caller in link's own code is nl_talk: frame_alloc_9 at 0x889f8 (a0 = 0x4120 = 16672), frame_release_9 at 0x88e88
   (a0 = the frame frame_alloc_9 returned, a1 = 0x4120).

   Both contracts are the released generic statements at class 9, unchanged:
   - frame_alloc_9: `astack_malloc_sz_realizes tfibsegs B 0x3e15c 9` (lib/Reusable/AsStackSz.v);
   - frame_release_9: `astack_free_realizes tfibsegs B 0x3e2d4 9` (lib/Reusable/StackFreeDef.v, sf_span 9 n = n / 8).
   Class 9 frames: fs_frames 9 = 32 frames of fs_frame_bytes 9 = 32768 bytes; the flag bytes at F + 36800 + pos
   (kFakeFlagsOff 4096 + fs_flags_off 9, and fs_flags_off 9 = 0x3fe << 5 = 0x7fc0: 4096 + 0x7fc0 = 0x8fc0 = 36800);
   the frames at F + 0x909000 + pos * 32768; the hint word at F + 72.

   What frame_alloc_9 does, and the premise each step needs (offsets from 0x3e15c):
   - +0x0..+0x18: a 48-byte frame below sp (`addi sp, sp, -0x30`, five `sd`). +0x20..+0x28: the TLS address of the
     thread's side-stack pointer through the .got pair 0xa26b0 and `jal 0x430a4` (the wrapper of __tls_get_addr; its
     callees use 32 + 144 more bytes, 224 in all). ecall_pre gives sp mod 16 = 0, the ESTACK = 4096 present bytes
     below sp, tp = as_tp B and gp = as_gp B, and AR, whose constant cells give the TLS chain its values
     ([tp] = F, the fake stack of the thread).
   - +0x2c..+0x3c: s2 = F (beqz s2 to the lazy-create path at +0xbc, not taken: AR puts F at [tp]); the GC byte at
     F + 0x60 is read (beqz: the GC call at +0x48 is not taken when it is 0, as AR states for the side stack);
     s3 = the stack-size log [F + 0x58] = 20.
   - +0x4c..+0xb0: the free-slot search over the 32 flag bytes from the hint [F + 0x48]: `addi a1, s3, -0xf` (32
     frames), `addi a4, zero, 0x3fe` (flags at F + 0x1000 + 0x7fc0), the 7-word loop at +0x98 (`and`, `add`, `lbu`,
     `beqz t0` to +0xe4). The premises `count_cid 9 (frames S) < fs_frames 9` and
     `apath (stack_malloc 9 S) [] (PFake 9 pos, S')` say a free slot exists and the model takes slot pos, so the
     loop exits at +0xe4 with a3 = flag_addr ly 9 pos, the address of pos's flag byte (t0 = that byte = 0) (the
     exhausted path +0xb4 / return 0 is not reached).
   - +0xe4..+0x124: the hint := c + 1, where c = [F + 0x48] + k is the unmasked probe counter at the free slot and
     pos = c mod 32 (`addi a2, a2, 1`; `sd a2, 0x48(s2)`): fs_probe's hint' (YG00.v:574); the flag byte := 1
     (`sb a0, 0(a3)`); the frame address s2 = F + 0x9000 + (9 << 20) + (pos << 15); its word +0x18 := s0 = sp at
     entry (`addi s0, sp, 0x30` at +0x18), the caller's sp at the call (the real-stack word); its word +0x7ff8
     := the flag address (`lui a4, 8`; `sd a3, -8(a4)`): the Post's rdword at frame + fs_frame_bytes 9 - 8.
   - +0x128: `jal 0x3e324` (MemToShadow, result discarded). +0x12c..+0x138: PoisonShadow(frame, s1 = a0 at entry =
     n, 0) at 0x551a8: the premises `getr regs 10 = w64 n`, `8 <= n <= fs_frame_bytes 9`, `n mod 8 = 0` make the
     n / 8 shadow bytes of [frame, frame + n) 0 (the Post's zero_shadow ... n), inside the frame.
   - +0x13c..+0x158: a0 = s2 = frame_addr ly 9 pos; the saved registers come back; `ret` to the caller's ra
     (ecall_pre's ret_ok ra). The Post keeps the callee-saved registers (aregs_preserved) and writes only owned bytes
     of S / S' and the stack window.

   What frame_release_9 does (offsets from 0x3e2d4):
   - +0x0..+0x14: a 32-byte frame; s0 = a1 = n, s1 = a0 = frame_addr ly 9 pos (premise).
   - +0x18..+0x24: `lui a0, 8`; the word at frame + 0x8000 - 8 (premise `rdword ... = Some (flag_addr ly 9 pos)`) is
     the flag address; `sb zero` clears the flag byte (the Post's stack_free_state 9 pos S).
   - +0x2c: `jal 0x3e324` (MemToShadow); +0x30..+0x4c: the saved registers come back and `j 0x551a8` (PoisonShadow,
     a tail jump) with a0 = frame, a1 = n, a2 = 0xf5: the n / 8 shadow bytes of the frame := 0xf5 (sf_span 9 n),
     returning to the caller's ra. The premise `In (9, pos) (frames S)` makes the frame live: Wf's wfs_live
     (YG01.v:407) gives 0 <= pos < 32 for the two leaf summaries, and astack_free_law (YG0d.v:309) turns the cleared
     flag byte into AR at stack_free_state 9 pos S. The flag byte is owned by the side stack; the frame's shadow
     bytes are client bytes while the frame is live, and the Post names them and the flag byte explicitly.

   Neither contract states the 0 return of frame_alloc_9 (no free slot, no side stack, or `blez` at +0x5c on a
   frame count <= 0): the premises exclude it (the last through AR's cell `z8 (AF 88) 20`, the stack-size log).
   The caller decides the use-after-return flag word ([0xaa440] through .got 0xa1a28) before it calls. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 AsStackSz StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
Import ListNotations.
Open Scope Z_scope.

Definition CID9 : Z := 9.
Definition PC_STACK_MALLOC_9 : Z := 0x3e15c.
Definition PC_STACK_FREE_9 : Z := 0x3e2d4.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition stack_malloc_9_contract (B : asyms) : Prop :=
astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_9 CID9.
Definition stack_free_9_contract (B : asyms) : Prop :=
astack_free_realizes tfibsegs B PC_STACK_FREE_9 CID9.
End b.

(* The class-9 constants the contracts name, computed by the kernel from the model's definitions. *)
Lemma cid9_consts :
fs_frames CID9 = 32 /\ fs_frame_bytes CID9 = 32768 /\ sf_span CID9 0x4120 = 0x824 /\
(forall ly pos, frame_addr ly CID9 pos = ly_F ly + 0x909000 + pos * 32768) /\
(forall ly pos, flag_addr ly CID9 pos = ly_F ly + 36800 + pos).
Proof.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
- intros ly pos. unfold frame_addr, fs_frame_off, CID9. change kFakeFramesOff with 36864.
  change (Z.shiftl 1 kStackSizeLog) with 1048576. change (fs_frame_bytes 9) with 32768. lia.
- intros ly pos. unfold flag_addr, fs_flag_off, CID9. change kFakeFlagsOff with 4096. change (fs_flags_off 9) with 32704. lia.
Qed.

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ieq(s, n, word) (fuzz_segconf.c:127-138; at 0x150d8 in the UBSan image 1696d6c34ffd, size 204,
    frame 32 bytes, saves ra and s0-s2).
    As compiled: k = strlen(word) (`jal strlen` 0x150fc); n <> k returns 0 (`bne` 0x15100); n = 0 returns 1
    (`beqz` 0x15108); else for i = 0 .. n-1 (a3 = a5 = s + i, a4 = a6 = word + i): the pointer checks below, then
    a = s[i] + 32 (s[i] - 'A' <u 26) (`lbu`, `sltiu`, `slli`, `add` 0x1514c-0x15160, SegModel.lower), a <> word[i]
    (`lbu` 0x15154, `bne` 0x15164) returns 0; all equal returns 1.
    It reads word's string with strlen's slack and, when n = strlen(word), the n bytes at s; it writes only its frame
    [sp - 32, sp) (strlen uses no stack and stores nothing).
    UBSan traps (all to the `unimp` at 0x151a0), each checked at every i < n: 0x15124 `bltu a3,s2` (s + i wraps)
    and 0x15138 `bltu a4,s0` (word + i wraps): s + n <= 2^64 (bytes_at) and word + length w + 1 <= 2^64 (cstr_at)
    with i < n = length w; 0x15130 and 0x15144 (`seqz`/`xor`/`beqz`: s + i = 0 against s <> 0, word + i likewise):
    0 < s <= s + i < 2^64 and the same for word; 0x15134 `beqz s2` (s null) and 0x15148 `beqz s0` (word null): s <> 0
    and word <> 0 in the premise.

    Post in the spine's terms: a0 = b2z (SegModel.ieq (zs l) w), l the n bytes at s and w the C string at word
    (strlen's k = length w, w NUL-free; ieq is length (zs l) = length w and ieq_go's lower a = x at every place).

    Callee contract its walk takes as a premise (frame leaf in the base): strlen_contract (Prog/strlen_c.v under
    lib/U, STRLEN = 0x1f5cc: word's NUL and slack, cstr_at).

    Call sites: m_file, nine (m_header and m_key inline there), the same nine words as in the plain build. At each,
    a0 points into the text block (a heap block: nonzero, outside [lo, sp)), a1 is the length of that range (the
    bytes [s, s + n) lie in the block), a2 a .rodata literal (cstr_at from the image through mem_inv; its slack lies
    in .rodata): 0x14494 (c:168: b, 7, "segment" 0x10313; be - b >= 8, `blt` 0x14484), 0x145e4 (c:213: k, kn, "role"
    0x10298), 0x146d0 (c:228: k, kn, "model" 0x10811), and 0x1478c, 0x147a4, 0x147dc, 0x14830, 0x14864, 0x1487c
    (c:236 "ignore", c:249 "knock" with k, kn; c:238 "yes", "true", c:240 "no", "false" with v, vn). *)
Definition IEQ : Z := 0x150d8.
Definition IEQ_STACK : Z := 32.

Definition ieq_pre (m : word -> option byte) (sp lo s n word : Z) (l : list byte) (w : list Z) : Prop :=
  s <> 0 /\ bytes_at rsegs m s l /\ Z.of_nat (length l) = n /\ apart s n lo sp /\
  word <> 0 /\ cstr_at rsegs m word w /\ apart word (Z.of_nat (length w) + 1) lo sp /\
  stack_ok rsegs m lo sp IEQ_STACK /\ mem_inv rsegs m.

Definition ieq_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (l : list byte) (w : list Z),
    ieq_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) l w ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (b2z (ieq (zs l) w))
         m
         ([(bv_unsigned sp - IEQ_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IEQ) fc None m (seg_rom rsegs)).

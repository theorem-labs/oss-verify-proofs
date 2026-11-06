From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ieq(s, n, word) (fuzz_segconf.c:127-138; at 0x14c2c in the image 3776ca44d75c, size 128,
    frame 32 bytes, saves ra and s0-s2).
    As compiled: k = strlen(word) (`jal strlen` 0x14c50); n <> k returns 0 (`bne` 0x14c54); n = 0 returns 1
    (`beqz` 0x14c5c); else for i = 0 .. n-1: a = s[i] + 32 (s[i] - 'A' <u 26) (`lbu`, `sltiu`, `slli`, `add`
    0x14c60-0x14c74, SegModel.lower), a <> word[i] (`lbu` 0x14c68, `bne` 0x14c78) returns 0; all equal returns 1.
    It reads word's string with strlen's slack and, when n = strlen(word), the n bytes at s; it writes only its frame
    [sp - 32, sp) (strlen uses no stack and stores nothing).

    Post in the spine's terms: a0 = b2z (SegModel.ieq (zs l) w), l the n bytes at s and w the C string at word
    (strlen's k = length w, w NUL-free; ieq is length (zs l) = length w and ieq_go's lower a = x at every place).

    Callee contract its walk takes as a premise (frame leaf in the base): strlen_contract (Prog/strlen_c.v,
    STRLEN = 0x1ec30: word's NUL and slack, cstr_at).

    Call sites: m_file, nine (m_header and m_key inline there). At each, a0 points into the text block (a heap block:
    nonzero, outside [lo, sp)), a1 is the length of that range (the bytes [s, s + n) lie in the block), a2 a .rodata
    literal (cstr_at from the image through mem_inv; its slack lies in .rodata):
    0x14400 (c:168: b, 7, "segment" 0x10313; be - b >= 8, `blt` 0x143ec), 0x14308 (c:213: k, kn, "role" 0x10298),
    0x144e4 (c:228: k, kn, "model" 0x10811), 0x145b0 (c:236: k, kn, "ignore" 0x1054f), 0x145ec (c:249: k, kn,
    "knock" 0x102a3), 0x145c8 (c:238: v, vn, "yes" 0x1042f), 0x14660 (c:238: v, vn, "true" 0x10517), 0x14690
    (c:240: v, vn, "no" 0x10711), 0x146a8 (c:240: v, vn, "false" 0x1029d). *)
Definition IEQ : Z := 0x14c2c.
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

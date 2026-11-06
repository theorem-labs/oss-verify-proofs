From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** trim(s) (reac_segconf.c:50-59, static; at 0x15660 in the image 3776ca44d75c; frame 16 bytes):
    past the leading blanks ({' ', '\t', '\r'}: `bltu 0x20, c` then the bit mask 0x100002200), e = s + strlen(s)
    (`jal strlen`, 0x1ec30), back over the trailing blanks while e > s, `sb zero,0(e)` (also when e = s +
    strlen(s): a NUL over the NUL), return s.

    Post in the spine's terms: a0 = p + trim_lead s (seg_spec), and the bytes at p are the first
    trim_lead s + length (r_trim s) bytes of s, then a NUL: the C string at a0 is SegModel.r_trim s. It writes its frame
    and the one byte of the NUL.

    Callee contract its walk takes as a premise: strlen_contract (Prog/strlen_c.v, 0x1ec30: the string, its NUL
    and the slack to the next 8-byte boundary).

    Call sites (reac_segconf_parse_file): 0x14ea4, 0x14efc, 0x14f08, 0x14f94 and 0x15114 (trim(buf), trim(line) after `*eq = 0`, trim(eq + 1),
    trim(line + 1) after `*close = 0`, trim(body + 7)); every argument points into parse_file's buf[512] (its frame:
    above this sp), at a C string of at most 511 bytes whose bytes and slack lie in buf and the frame bytes after it,
    all present and writable. *)
Definition TRIM : Z := 0x15660.
Definition TRIM_STACK : Z := 16.

Definition trim_pre (m : word -> option byte) (sp lo p : Z) (s : list Z) : Prop :=
  p <> 0 /\ cstr_at rsegs m p s /\ wr_at rsegs m p (Z.of_nat (length s) + 1) /\
  apart p (Z.of_nat (length s) + 8) lo sp /\ stack_ok rsegs m lo sp TRIM_STACK /\ mem_inv rsegs m.

(** Where it stores the NUL. *)
Definition trim_end_addr (p : Z) (s : list Z) : Z := p + Z.of_nat (trim_lead s + length (r_trim s)).

Definition trim_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : list Z),
    trim_pre m (bv_unsigned sp) lo (bv_unsigned a0) s ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (bv_unsigned a0 + Z.of_nat (trim_lead s))
         m
         ([(bv_unsigned sp - TRIM_STACK, bv_unsigned sp); (trim_end_addr (bv_unsigned a0) s, trim_end_addr (bv_unsigned a0) s + 1)])
         lo
         (fun m' => bytes_at rsegs m' (bv_unsigned a0) (zb (firstn (trim_lead s + length (r_trim s)) s) ++ [ZERO])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TRIM) fc None m (seg_rom rsegs)).

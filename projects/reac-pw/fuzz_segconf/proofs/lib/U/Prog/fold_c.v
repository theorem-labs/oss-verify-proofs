From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** fold(s, n, out, cap) (fuzz_segconf.c:140-148; at 0x151a4 in the UBSan image 1696d6c34ffd, size 148, read
    with a disassembler from the unstripped twin afc060e3cc9c; a leaf: no frame, no stack access, no call).
    The plain build has no such function: clang inlines fold into m_file at its two sites, so there is no plain
    contract.
    As compiled: k = n when n <u cap - 1, else cap - 1 (`addi a3,a3,-1`, `bltu`, `mv` 0x151a4-0x151ac); k = 0 goes to
    0x1522c (the out + k check, then `sb zero` at out + k, return 0); else for i = 0 .. k-1 (a6 = a7 = s + i, t0 =
    out + i, t1 counts k down): the pointer checks below, `lbu` s[i] (0x151e8), + 32 (s[i] - 'A' <u 26)
    (0x151f8-0x15204, SegModel.lower), `sb` to out[i] (0x15208); then the out + k check (0x15218), `sb zero` at
    out + k (0x15220), a0 = k (0x15224).
    It reads the first k bytes at s; it writes [out, out + k + 1), k = min(n, cap - 1) = length (h_fold l cap).
    UBSan traps (all to the `unimp` at 0x15234): at each i < k, 0x151d0 `bltu a6,a0` (s + i wraps: s + n <= 2^64,
    bytes_at), 0x151dc (`seqz`/`xor`/`beqz`: s + i = 0 against s <> 0), 0x151e0 `beqz a0` (s null: s <> 0 in the
    premise), 0x151e4 `bltu ~out,i` (out + i wraps); after the loop 0x15218 `bltu ~out,k`, and on the k = 0 path
    0x15230 `bgeu ~out,k` falls through to the `unimp` only when ~out < k (out + k + 1 <= 2^64: wr_at).

    Post in the spine's terms: a0 = length (SegModel.h_fold (zs l) cap) and out holds h_fold (zs l) cap and a NUL,
    l the n bytes at s (fold_out below; cap >= 1, so cap - 1 is exact and h_fold's firstn (cap - 1) is k).

    No callee.

    Call sites: m_file, two (m_key, c:219 and c:229): a0 = v (m_file's slot sp + 0x90: the unquoted value, a pointer
    into the text block, nonzero, its vn bytes in the block), a1 = s5 = vn, a2 = sp + 0x48 = low[64] (m_file's
    frame, 272 bytes, above fold's sp, which is m_file's; apart from the text block), a3 = 64 (0x145fc, role) or 24
    (0x146e8, model): k + 1 <= cap <= 64 bytes of low. *)
Definition FOLD : Z := 0x151a4.
Definition FOLD_STACK : Z := 0.

(** The folded text fold stores (without its NUL). *)
Definition fold_out (l : list byte) (cap : Z) : list Z := h_fold (zs l) (Z.to_nat cap).

Definition fold_pre (m : word -> option byte) (sp lo s n out cap : Z) (l : list byte) : Prop :=
  1 <= cap /\
  s <> 0 /\ bytes_at rsegs m s l /\ Z.of_nat (length l) = n /\ apart s n lo sp /\
  wr_at rsegs m out (Z.of_nat (length (fold_out l cap)) + 1) /\
  apart out (Z.of_nat (length (fold_out l cap)) + 1) lo sp /\
  apart s n out (out + Z.of_nat (length (fold_out l cap)) + 1) /\
  stack_ok rsegs m lo sp FOLD_STACK /\ mem_inv rsegs m.

Definition fold_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (l : list byte),
    fold_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3) l ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (Z.of_nat (length (fold_out l (bv_unsigned a3))))
         m
         ([(bv_unsigned a2, bv_unsigned a2 + Z.of_nat (length (fold_out l (bv_unsigned a3))) + 1)])
         lo
         (fun m' => bytes_at rsegs m' (bv_unsigned a2) (zb (fold_out l (bv_unsigned a3) ++ [0]))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FOLD) fc None m (seg_rom rsegs)).

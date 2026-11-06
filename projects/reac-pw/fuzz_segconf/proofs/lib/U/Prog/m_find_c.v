From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** m_find(c, name, n) (fuzz_segconf.c:150-156; at 0x14ccc in the UBSan image 1696d6c34ffd, size 208; frame 64
    bytes, saves ra and s0-s6).
    As compiled: c & 3 <> 0 traps (0x14cf8); n = c->n (`lw` of c + 0x2000, 0x14d04); n <= 0 returns NULL (`blez`
    0x14d08); else for i = 0 .. n-1 (s0 = c + 256 i, s3 = 256 i, s5 counts n down, s6 counts 32 down):
    strlen(c->seg[i].name) (`jal strlen` 0x14d38) <> n goes on (`bne` 0x14d3c); else bcmp(c->seg[i].name, name, n)
    (`jal bcmp` 0x14d4c) = 0 returns &c->seg[i] (`beqz` 0x14d50 to 0x14d6c); none returns NULL (0x14d68).
    It reads c->n, the names of seg[0 .. n) (each with strlen's slack, inside the 16-byte name field: c is
    16-aligned) and at most n bytes at name; it writes only its frame [sp - 64, sp) (strlen and bcmp use no stack and
    store nothing).
    UBSan traps (all to the `unimp` at 0x14d98): 0x14cf8 alignment c & 3 (c 16-aligned); 0x14d2c `beqz s6`, the
    bound seg[i] with i = 32 (s6 = 32 - i > 0 since i < c->n = length (mc_seg mc) <= 32: mconf_enc); 0x14d30
    `bltu s4,s3` with s4 = ~c, s3 = 256 i, c + 256 i wrapping (c + 9236 <= 2^64: bytes_at of the block).

    Post in the spine's terms: a0 = m_find_ptr c mc (zs l), i.e. &c->seg[i] = seg_spec.mseg_addr c i for
    SegModel.m_find mc (zs l) = Some i, else 0, where l is the n bytes at name (not NUL-terminated: m_header passes
    a pointer into the text block). strlen = n is SegModel.strlen (ms_name g) = length (zs l) (the names are
    NUL-free: mconf_enc), and bcmp's 0 is SegModel.leqb (firstn n (ms_name g)) (zs l).

    Callee contracts its walk takes as premises (frame leaves in the base): strlen_contract (Prog/strlen_c.v under
    lib/U, STRLEN = 0x1f5cc: the name's NUL and slack), bcmp_contract (Prog/bcmp_c.v under lib/U, BCMP = 0x1edc8:
    StrFun.memcmp_model over the 16 name bytes and l, n < 16 on that path).

    Call sites. At each, a0 = the mconf block (calloc(1, 9236): nonzero, 16-aligned, holding the model state mc:
    mconf_at), the n bytes at name lie in the text block, in main's frame or in .rodata, so outside [lo, sp):
    - m_file 0x144f4 (m_header, c:179): a0 = s0 = c, a1 = nm (the stripped name, in the text block), a2 = s5 = n =
      ne - nm, 1 <= n <= 15 (`beq` 0x144dc, `bgeu` 0x144e8).
    - LLVMFuzzerTestOneInput 0x13e20 (c:642): a0 = s5 = m, a1 = sp + 0x60 (main's 18-byte probe buffer, "<name>x"
      written by snprintf at 0x13e08), a2 = strlen(probe) (0x13e10).
    - LLVMFuzzerTestOneInput 0x13e54 (c:645): a0 = m (main's slot sp + 0x50), a1 = "nosuch0" (seg_spec.STR_NOSUCH,
      0x10540), a2 = 7. *)
Definition M_FIND : Z := 0x14ccc.
Definition M_FIND_STACK : Z := 64.

(** &c->seg[i] for the spine's m_find, else NULL. *)
Definition m_find_ptr (c : Z) (mc : mconf) (name : list Z) : Z :=
  match m_find mc name with Some i => mseg_addr c i | None => 0 end.

Definition m_find_pre (m : word -> option byte) (sp lo c name n : Z) (mc : mconf) (l : list byte) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ mconf_at rsegs m c mc /\ apart c SEG_M_SIZE lo sp /\
  bytes_at rsegs m name l /\ Z.of_nat (length l) = n /\ apart name n lo sp /\
  stack_ok rsegs m lo sp M_FIND_STACK /\ mem_inv rsegs m.

Definition m_find_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (mc : mconf) (l : list byte),
    m_find_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) mc l ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (m_find_ptr (bv_unsigned a0) mc (zs l))
         m
         ([(bv_unsigned sp - M_FIND_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_FIND) fc None m (seg_rom rsegs)).

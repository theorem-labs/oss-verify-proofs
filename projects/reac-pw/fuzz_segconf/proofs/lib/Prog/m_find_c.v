From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** m_find(c, name, n) (fuzz_segconf.c:150-156; at 0x149dc in the image 3776ca44d75c, size 132; frame 48 bytes,
    saves ra and s0-s3).
    As compiled: s3 = c->n (`lw` of c + 0x2000, 0x14a00); n <= 0 returns NULL (`blez`, 0x14a04); else for i = 0 ..
    n-1 (s0 = c + 256 i, `addi s0,s0,0x100` 0x14a34; s3 counts down, 0x14a30): strlen(c->seg[i].name) (`jal strlen`
    0x14a14) <> n goes on (`bne` 0x14a18); else bcmp(c->seg[i].name, name, n) (`jal bcmp` 0x14a28) = 0 returns
    &c->seg[i] (`beqz` 0x14a2c to 0x14a40); none returns NULL (0x14a3c).
    It reads c->n, the names of seg[0 .. n) (each with strlen's slack, inside the 16-byte name field: c is
    16-aligned) and at most n bytes at name; it writes only its frame [sp - 48, sp) (strlen and bcmp use no stack and
    store nothing).

    Post in the spine's terms: a0 = m_find_ptr c mc (zs l), i.e. &c->seg[i] = seg_spec.mseg_addr c i for
    SegModel.m_find mc (zs l) = Some i, else 0, where l is the n bytes at name (not NUL-terminated: m_header passes
    a pointer into the text block). strlen = n is SegModel.strlen (ms_name g) = length (zs l) (the names are
    NUL-free: mconf_enc), and bcmp's 0 is SegModel.leqb (firstn n (ms_name g)) (zs l).

    Callee contracts its walk takes as premises (frame leaves in the base): strlen_contract (Prog/strlen_c.v,
    STRLEN = 0x1ec30: the name's NUL and slack), bcmp_contract (Prog/bcmp_c.v, BCMP = 0x1e42c:
    StrFun.memcmp_model over the 16 name bytes and l, n < 16 on that path).

    Call sites. At each, a0 = the mconf block (calloc(1, 9236): nonzero, 16-aligned, holding the model state mc:
    mconf_at), the n bytes at name lie in the text block, in main's frame or in .rodata, so outside [lo, sp):
    - m_file 0x14494 (m_header, c:179): a0 = s0 = c, a1 = s5 = nm (the stripped name, in the text block), a2 = s6 =
      n = ne - nm, 1 <= n <= 15 (`beq` 0x14478, `bgeu` 0x14484).
    - LLVMFuzzerTestOneInput 0x13c40 (c:642): a0 = s0 = m, a1 = sp + 0x40 (main's 18-byte probe buffer, "<name>x"
      written by snprintf at 0x13c28), a2 = strlen(probe) (0x13c30).
    - LLVMFuzzerTestOneInput 0x13c74 (c:645): a0 = s0 = m, a1 = "nosuch0" (seg_spec.STR_NOSUCH, 0x10540), a2 = 7. *)
Definition M_FIND : Z := 0x149dc.
Definition M_FIND_STACK : Z := 48.

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

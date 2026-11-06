From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
Import ListNotations.
Open Scope Z_scope.

(** m_refuse(c, line) (fuzz_segconf.c:101-111; at 0x14b8c in the image 3776ca44d75c, size 160; frame 16 bytes,
    saves ra and s0).
    As compiled: s0 = c + 0x2008 = &c->refused (0x14b98-0x14ba0); n_kept = `lw 0x3a4(s0)` (c + 0x23ac, 0x14ba4);
    7 < n_kept (signed `blt` 0x14bac) skips to refused++; else a5 = c + 0x200c + 112 n_kept = &kept[n_kept]
    (0x14bb4-0x14bcc), a3 = c + 0x23b4 = c->reading (0x14bd0), a4 = line; line <= 0 (`blez a4` 0x14bd4) calls
    snprintf(a5, 112, "%s: " (0x108c4), reading) (`jal snprintf` 0x14c00), else snprintf(a5, 112, "%s:%d: "
    (0x10338), reading, line) (0x14be8); then n_kept++ (`lw`/`addi`/`sw` 0x14c04-0x14c0c); refused++ (0x14c10-0x14c18,
    an unsigned 32-bit add: the premise mc_refused mc + 1 < 2^32 keeps the spine's + 1 exact). It never writes
    kept_knock: m_key's knock branch has set kept_knock[n_kept] = 1 before the call (fuzz_segconf.c:251-252), which
    the premise's mconf_atp knock states.
    It reads n_kept, refused, the reading string (snprintf's %s, with its slack: c->reading ends at the end of the
    9236-byte block, so up to 4 bytes past it, blk_slack) and the format in .rodata; it writes its frame and
    snprintf's below it, [sp - M_REFUSE_STACK, sp), the slot kept[n_kept] (112 bytes: snprintf writes its text and
    NUL there) and n_kept when n_kept < 8, and refused.

    Post in the spine's terms: memory holds SegModel.m_refuse mc line knock (seg_spec.mconf_at, the knock flag of
    kept[n_kept] now part of mc_kept), registers and FP state as seg_env.ret_void_fp says (printf writes fa0 and
    fflags).

    Callee contract its walk takes as a premise: snprintf_m_contract (Prog/snprintf_m_c.v, SNPRINTF = 0x19078; or
    its pf_parse form snprintf_contract, Prog/snprintf_c.v): the format literal in .rodata (mem_inv), the arguments
    PA_s (mc_reading mc) (NUL-free, slack from blk_slack, apart from [lo, sp - 16) and from the slot by the struct
    layout) and PA_i line (0 <= line <= 65536 < 2^31), rw_cells of the 112-byte slot (mconf_atp's bytes, wr_at),
    pf_img_free of the slot (blk_noimg rsegs c SEG_M_SIZE), SNPRINTF_K = seg_env.PRINTF_K = 5936 bytes of stack
    below m_refuse's sp - 16, and seg_env.printf_env (frm0, MemNorm.task_mem, the stack-protector cells, the stack
    above the image). Spec/SegPrintfBridge.v ties its text to the spine (seg_printf_model, pm_addr_line, pm_addr,
    snprintf_s_firstn): the slot then holds SegModel.snprintf_s 112 F_addr_line [AS reading; AI line] (line > 0) or
    snprintf_s 112 F_addr [AS reading] (line = 0), at most 95 + 1 + 5 + 2 bytes before its NUL.

    Call sites (a0 = the mconf block: calloc(1, 9236), nonzero, 16-aligned, above the image, writable; a1 = line):
    - m_file (a0 = s0 = c, a1 = s3 = line, 1 <= line <= 65536): 0x143a8 (c:227), 0x143d0 (c:277; also the knock
      branch c:251-253, which stores kept_knock[n_kept] = 1 at 0x1461c when n_kept <= 7 and jumps here: knock =
      true), 0x144b8 (c:190), 0x144c8 (c:169), 0x14644 (m_header's join after c:182's overflow++ and the other
      header refusals), 0x14744 (m_key's join). knock = false at every site but the knock branch.
    - LLVMFuzzerTestOneInput (m_cross inline, c:302 and c:305): 0x13a70 and 0x13a90, a0 = s0 = m, a1 = 0, knock =
      false. *)
Definition M_REFUSE : Z := 0x14b8c.
Definition M_REFUSE_STACK : Z := 16 + PRINTF_K.

Definition m_refuse_pre (m : word -> option byte) (fc : bv 32) (sp lo c line : Z) (mc : mconf) (knock : bool)
    : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_M_SIZE /\
  mconf_atp rsegs knock m c mc /\ wr_at rsegs m c SEG_M_SIZE /\ blk_slack rsegs m c SEG_M_SIZE /\
  apart c (SEG_M_SIZE + 4) lo sp /\
  0 <= line <= 65536 /\ mc_refused mc + 1 < 2 ^ 32 /\
  printf_env m fc lo sp /\ stack_ok rsegs m lo sp M_REFUSE_STACK /\ mem_inv rsegs m.

(** The bytes it writes: the frames, kept[n_kept] and n_kept when n_kept < 8, refused. *)
Definition m_refuse_W (sp c : Z) (mc : mconf) : list ivl :=
  (sp - M_REFUSE_STACK, sp) ::
  (if Z.of_nat (length (mc_kept mc)) <? 8 then
     [(kept_addr c (length (mc_kept mc)), kept_addr c (length (mc_kept mc)) + MC_KEPT_LEN);
      (c + MC_NKEPT, c + MC_NKEPT + 4)]
   else []) ++
  [(c + MC_REFUSED, c + MC_REFUSED + 4)].

Definition m_refuse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (mc : mconf) (knock : bool),
    m_refuse_pre m fc (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) mc knock ->
    evt rsegs
      (ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
         m
         (m_refuse_W (bv_unsigned sp) (bv_unsigned a0) mc)
         lo
         (fun m' => mconf_at rsegs m' (bv_unsigned a0) (m_refuse mc (bv_unsigned a1) knock)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_REFUSE) fc None m (seg_rom rsegs)).

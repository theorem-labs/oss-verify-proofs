From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
Import ListNotations.
Open Scope Z_scope.

(** m_refuse(c, line) (fuzz_segconf.c:101-111; at 0x14f30 in the UBSan image 1696d6c34ffd, size 248; frame 16
    bytes, saves ra and s0).
    As compiled: c & 3 <> 0 traps (0x14f40); s0 = c + 0x2008 = &c->refused (0x14f48-0x14f50); n_kept =
    `lw 0x3a4(s0)` (c + 0x23ac, 0x14f54); 7 < n_kept (signed `blt` 0x14f5c) skips to refused++; else line <= 0
    (`blez a4` 0x14f60) calls snprintf(&kept[n_kept], 112, "%s: " (0x108c4), c->reading) (`jal snprintf`
    0x14ff4), else snprintf(&kept[n_kept], 112, "%s:%d: " (0x10338), c->reading, line) (0x14fa8), with &kept[n_kept]
    = c + 0x200c + 112 n_kept and c->reading = c + 0x23b4; then n_kept++ (`addiw`, overflow check, `sw`
    0x14ff8-0x15004); refused++ (0x15008-0x15010, an unsigned 32-bit add, no check: the premise mc_refused mc + 1 <
    2^32 keeps the spine's + 1 exact). It never writes kept_knock: m_key's knock branch has set kept_knock[n_kept] = 1
    before the call (fuzz_segconf.c:251-252), which the premise's mconf_atp knock states.
    It reads n_kept, refused, the reading string (snprintf's %s, with its slack: c->reading ends at the end of the
    9236-byte block, so up to 4 bytes past it, blk_slack) and the format in .rodata; it writes its frame and
    snprintf's below it, [sp - M_REFUSE_STACK, sp), the slot kept[n_kept] (112 bytes: snprintf writes its text and
    NUL there) and n_kept when n_kept < 8, and refused.
    UBSan traps (all to the `unimp` at 0x15024): 0x14f40 alignment c & 3 (c 16-aligned); 0x14f68 `bgeu a1,9` and
    0x14fb4 `bltu 8,a1`, the bound kept[n_kept] (n_kept <= 7 on both paths: the `blt` at 0x14f5c); 0x14f88 and
    0x14fd4 `bltu ~(c + 0x200c), 112 n_kept`, c + 0x200c + 112 n_kept wrapping (c + 9236 <= 2^64: bytes_at of the
    block); 0x15000 `blt a0,a1`, the signed overflow of n_kept++ (n_kept <= 7).

    Post in the spine's terms: memory holds SegModel.m_refuse mc line knock (seg_spec.mconf_at, the knock flag of
    kept[n_kept] now part of mc_kept), registers and FP state as seg_env.ret_void_fp says (printf writes fa0 and
    fflags).

    Callee contract its walk takes as a premise: snprintf_m_contract (Prog/snprintf_m_c.v under lib/U, SNPRINTF =
    0x19a14; or its pf_parse form snprintf_contract, Prog/snprintf_c.v under lib/U): the format literal in .rodata
    (mem_inv), the arguments PA_s (mc_reading mc) (NUL-free, slack from blk_slack, apart from [lo, sp - 16) and from
    the slot by the struct layout) and PA_i line (0 <= line <= 65536 < 2^31), rw_cells of the 112-byte slot
    (mconf_atp's bytes, wr_at), pf_img_free of the slot (blk_noimg rsegs c SEG_M_SIZE), SNPRINTF_K =
    seg_env.PRINTF_K = 5936 bytes of stack below m_refuse's sp - 16, and seg_env.printf_env (frm0, MemNorm.task_mem,
    the stack-protector cells, the stack above the image). Spec/SegPrintfBridge.v ties its text to the spine
    (seg_printf_model, pm_addr_line, pm_addr, snprintf_s_firstn): the slot then holds SegModel.snprintf_s 112
    F_addr_line [AS reading; AI line] (line > 0) or snprintf_s 112 F_addr [AS reading] (line = 0), at most 95 + 1 +
    5 + 2 bytes before its NUL.

    Call sites (a0 = the mconf block: calloc(1, 9236), nonzero, 16-aligned, above the image, writable; a1 = line):
    - m_file (a0 = s0 = c, a1 = s3 = line, 1 <= line <= 65536): 0x14520 (c:190), 0x14658 (c:227), 0x14670
      (m_header's join of the header refusals), 0x14684 (c:201), 0x146b0 (c:277; also the knock branch c:251-253,
      which stores kept_knock[n_kept] = 1 at 0x14818 when n_kept <= 7 and jumps here: knock = true), 0x147c4
      (c:231), 0x148c8 (c:255), 0x148f4 (c:183). knock = false at every site but the knock branch.
    - LLVMFuzzerTestOneInput (m_cross inline, c:302 and c:305): 0x13bcc and 0x13bec, a0 = m (main's slot sp +
      0x50), a1 = 0, knock = false. *)
Definition M_REFUSE : Z := 0x14f30.
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

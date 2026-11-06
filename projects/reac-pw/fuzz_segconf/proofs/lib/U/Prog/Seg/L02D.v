(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): the interface of its inner
   walk, 0x13aac .. 0x13c34. As the plain twin
   (lib/Prog/Seg/L02D.v), with this build's frame (sp = S - 240, label[40] at sp + 0x60, saves at [S - 104, S)),
   register map (P_K13aac / P_K13c34 of U/Prog/seg_cuts.v) and frame cells (0x28 = m + 0x10, 0x30 = the label
   format, 0x38 = m & 3, 0x40 = nfiles, 0x48 = c, 0x50 = m), and its five trap branches, each not taken:
   0x13acc (`not a0,s7; bltu a0,s10`: t + n wraps), 0x13b54 and 0x13b84 (`ld 0x38(sp); bnez`: m & 3),
   0x13b9c (`beq s9,s5`: i = 33) and 0x13ba0 (`bltu s2,s8`: ~m < 256 i).
   The code: 0x13aac `beqz a0` to abort (dead); s7 = t; s10 = n <> 0: memcpy(t, s9, n) (0x13ac4); the trap
   0x13acc; s10 = t + n, `sb zero, 0(s10)`; lb = s8: bit 7: memset(longl, 'L', 120) (0x13b18), s9 = longl; lb = 0:
   s9 = 0; else snprintf(sp + 0x60, 40, `ld a2,0x30(sp)`, lb) (0x13afc), s9 = sp + 0x60; s10 = `ld 0x40(sp)` =
   nfiles on every path; join 0x13b28: s0 = f + 1 (`addiw`), `bgeu s0,s10` (the last turn).
   Drop-in: m_file(`ld 0x50(sp)` = m, t, s9) (0x13b3c); reac_segconf_parse_file(`ld 0x48(sp)` = c, t, s9)
   (0x13b4c); the trap 0x13b54; s4 &= (a0 == m->n) (`lw 0(s11)`); to 0x13c2c.
   Last: m_file(m, t, NULL) (0x13b7c); the trap 0x13b84; m_cross inline (0x13b88-0x13c08: s9 = i < m->n, s8 =
   256 i, s10 = `ld 0x28(sp)` + 256 i, m_refuse(m, 0) at 0x13bcc / 0x13bec); reac_segconf_parse(c, t) (0x13c14);
   s4 &= (a0 == m->n); s10 = `ld 0x40(sp)` = nfiles.
   0x13c2c: s1 -= s6; a0 = s7; at 0x13c34 `jal free`.
   Statement text of a segment's inner walk. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require memcpy_c snprintf_m_c memset_c m_refuse_c
  reac_segconf_parse_file_c reac_segconf_parse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M.
Import ListNotations.
Open Scope Z_scope.

(** The label format's address ("reac-pw.conf.d/%u-x.conf", .rodata; U/Prog/seg_cuts.LABEL_FMT). *)
Definition L02_FMT : Z := 0x1093b.
(** main's frame: sp = S - 240, the label buffer label[40] at sp + 0x60, the saved registers at [S - 104, S). *)
Definition L02_FRAME : Z := 240.

(** What the segment may write: the stack window below main's frame, the label buffer, longl's 120 written bytes,
    the text block, the mconf block and the reader block. *)
Definition L02_W (S c mm t nt : Z) : list ivl :=
  [(S - 65536, S - L02_FRAME); (S - L02_FRAME + 0x60, S - L02_FRAME + 0x88);
   (sa_longl SA, sa_longl SA + 120); (t, t + nt); (mm, mm + SEG_M_SIZE); (c, c + SEG_C_SIZE)].

(** The memory at 0x13aac: as the plain twin's, with this build's frame cells. *)
Definition L02_mem (S c mm t nt src nf : Z) (s : list Z) (rc : rconf) (mc : mconf) (m : word -> option byte)
    : Prop :=
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ ssp_ok m /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  S mod 16 = 0 /\ 2 ^ 40 <= S - 65536 /\ S <= 2 ^ 47 /\
  stk rsegs m (S - 65536) S /\ (forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None) /\
  bytes_at rsegs m (S - L02_FRAME + 0x28) (le8 (Z_to_bv 64 (mm + 0x10))) /\
  bytes_at rsegs m (S - L02_FRAME + 0x30) (le8 (Z_to_bv 64 L02_FMT)) /\
  bytes_at rsegs m (S - L02_FRAME + 0x38) (le8 (Z_to_bv 64 (mm mod 4))) /\
  bytes_at rsegs m (S - L02_FRAME + 0x40) (le8 (Z_to_bv 64 nf)) /\
  bytes_at rsegs m (S - L02_FRAME + 0x48) (le8 (Z_to_bv 64 c)) /\
  bytes_at rsegs m (S - L02_FRAME + 0x50) (le8 (Z_to_bv 64 mm)) /\
  c <> 0 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\ c + SEG_C_SIZE <= S - 65536 /\
  mm <> 0 /\ mm mod 16 = 0 /\ blk_noimg rsegs mm SEG_M_SIZE /\ mm + SEG_M_SIZE <= S - 65536 /\
  t <> 0 /\ t mod 16 = 0 /\ blk_noimg rsegs t nt /\ t + nt <= S - 65536 /\
  nt = Z.of_nat (length s) + 1 /\
  apart t nt mm (mm + SEG_M_SIZE) /\ apart t nt c (c + SEG_C_SIZE) /\ apart mm SEG_M_SIZE c (c + SEG_C_SIZE) /\
  apart t nt (sa_longl SA) (sa_longl SA + 128) /\ apart mm SEG_M_SIZE (sa_longl SA) (sa_longl SA + 128) /\
  apart c SEG_C_SIZE (sa_longl SA) (sa_longl SA + 128) /\
  rconf_at rsegs m c rc /\ wr_at rsegs m c SEG_C_SIZE /\
  mconf_at rsegs m mm mc /\ wr_at rsegs m mm SEG_M_SIZE /\ blk_slack rsegs m mm SEG_M_SIZE /\
  (exists junk, rw_cells rsegs m t [CB (Z.to_nat nt) junk]) /\ blk_slack rsegs m t nt /\
  bytes_at rsegs m src (zb s) /\ apart src (Z.of_nat (length s)) t (t + nt) /\
  (exists junk, rw_cells rsegs m (sa_longl SA) [CB 120 junk]) /\
  (exists sl, bytes_at rsegs m (sa_longl SA + 120) (ZERO :: sl) /\ length sl = 7%nat).

(** The state at 0x13c34 (`jal free(text)`): sp, gp, tp, s2 (~m), s3 (src + n'), s5 (33), s6 (n') and s11 (&m->n)
    as at 0x13aac; a0 = s7 = t, s0 = f + 1, s1 = the count - n', s10 = nfiles, s4 = the new returned flag; the writes
    inside L02_W; the machine kept; c and m holding the turn's result. *)
Definition L02_post (S c mm t nt x1 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
    (sp gp tp s2 s3 s5 s6 s11 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s4' s7' s8' s9' s10'
                    t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5 s6 s7' s8' s9' s10'
                 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x13c34) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ munch (L02_W S c mm t nt) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    MemNorm.task_mem rsegs m' /\
    a0' = Z_to_bv 64 t /\ s7' = Z_to_bv 64 t /\ s0' = Z_to_bv 64 (f + 1) /\ s1' = Z_to_bv 64 (x1 - x6) /\
    s10' = Z_to_bv 64 nf /\
    s4' = Z_to_bv 64 (b2z (seg_ret (l02_step s lb (f + 1 =? nf) (rc, mc, ret)))) /\
    rconf_at rsegs m' c (seg_rc (l02_step s lb (f + 1 =? nf) (rc, mc, ret))) /\
    mconf_at rsegs m' mm (seg_mc (l02_step s lb (f + 1 =? nf) (rc, mc, ret))).

(** The inner walk: from 0x13aac with the cut's registers (a0 = t, s10 = n, s9 = src, s1 = the count before the
    take, s6 = n', s8 = lb, s0 = f, s4 = ret, s11 = &m->n, s2 = ~m, s5 = 33, sp = S - 240) to L02_post. *)
Definition L02_inner : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S c mm t nt src x1 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool),
    sp = Z_to_bv 64 (S - L02_FRAME) -> a0 = Z_to_bv 64 t -> s11 = Z_to_bv 64 (mm + MC_N) ->
    s2 = bv_not (Z_to_bv 64 mm) -> s5 = Z_to_bv 64 33 ->
    s0 = Z_to_bv 64 f -> 0 <= f < nf -> nf <= 4 ->
    s4 = Z_to_bv 64 (b2z ret) -> s10 = Z_to_bv 64 (Z.of_nat (length s)) ->
    s9 = Z_to_bv 64 src -> s1 = Z_to_bv 64 x1 -> s6 = Z_to_bv 64 x6 -> s8 = Z_to_bv 64 lb ->
    frm0 fc -> L02_model s lb rc mc -> L02_mem S c mm t nt src nf s rc mc m ->
    evt rsegs (L02_post S c mm t nt x1 x6 f nf lb s rc mc ret sp gp tp s2 s3 s5 s6 s11 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13aac) fc None m (seg_rom rsegs)).

(** The callee contracts the inner walk takes (U/Prog/SegEnd.v's K_L02), this build's entries. *)
Definition K_L02 : Prop :=
  memcpy_c.memcpy_contract /\ snprintf_m_c.snprintf_m_contract /\ memset_c.memset_contract /\
  m_file_contract /\ m_refuse_c.m_refuse_contract /\
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract /\ reac_segconf_parse_c.reac_segconf_parse_contract.

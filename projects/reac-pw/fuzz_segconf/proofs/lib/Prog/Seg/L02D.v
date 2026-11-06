(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the interface of its inner
   walk, 0x13984 .. 0x13ad8. The inner walk is stated over the
   machine words of the cut and a memory that already holds every fact the callees ask (the slot side, Prog/Seg/L02.v,
   builds that memory from FR and the cut predicate P_K13984 and reads P_K13ad8 back from the post). It is generic
   in the turn's data: the text s (the bytes fuzz_str copies), the label byte lb, the turn kind
   last = (f + 1 =? nfiles) and the reader/model states (rc, mc) with the returned flag ret; the post is l02_step,
   seg_spec.seg_turn_step with s and lb explicit.
   The code:
   - 0x13984 `beqz a0` to abort (dead: t <> 0); s7 = t; n = s9 <> 0: memcpy(t, s3, n) (0x1399c); s9 = t + n,
     `sb zero, 0(s9)` (the NUL); lb = s8: bit 7 (`slli a0,s8,0x38; bltz`) memset(longl, 'L', 120) (0x139e4), s9 =
     longl; else lb = 0: s9 = 0; else snprintf(sp + 0x40, 40, "reac-pw.conf.d/%u-x.conf" (`ld a2,0x28(sp)`), lb)
     (0x139c8), s9 = sp + 0x40; join 0x139f0.
   - s11 = f + 1 (`addiw`), `bgeu s11,s2` (f + 1 >= nfiles: the last turn).
     Drop-in: m_file(m = s0, t, s9) (0x13a04); s8 = `ld 0x30(sp)` = c; reac_segconf_parse_file(c, t, s9)
     (0x13a18); a0 = (a0 == m->n) ? -1 : 0 (`lw 0(s10)`, xor, snez, addiw -1); to 0x13ac8.
     Last: m_file(m, t, NULL) (0x13a34); m_cross inline (0x13a38-0x13aa8: i = s1 < m->n, s8 = `ld 0x20(sp)` + 256 i
     = &m->seg[i].role, role_set at 4(s8), model_set at 0x10(s8), m_refuse(m, 0) at 0x13a70 / 0x13a90 and the
     stores `sw zero` to model_set / role, role_set); s8 = c; reac_segconf_parse(c, t) (0x13ab8); a0 = (a0 == m->n).
   - 0x13ac8: s4 = a0 & s4; s3 += s6; s5 -= s6; a0 = s7; at 0x13ad8 `jal free`.
   Statement text of a segment's inner walk. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require memcpy_c snprintf_m_c memset_c m_refuse_c
  reac_segconf_parse_file_c reac_segconf_parse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M.
Import ListNotations.
Open Scope Z_scope.

(** The label format's address ("reac-pw.conf.d/%u-x.conf", .rodata; seg_cuts.LABEL_FMT). *)
Definition L02_FMT : Z := 0x1093b.
(** main's frame: sp = S - 208, the label buffer label[40] at sp + 0x40, the saved registers at [S - 104, S). *)
Definition L02_FRAME : Z := 208.

(** What the segment may write: the stack window below main's frame (its callees' frames), the label buffer,
    longl's 120 written bytes, the text block, the mconf block and the reader block. *)
Definition L02_W (S c mm t nt : Z) : list ivl :=
  [(S - 65536, S - L02_FRAME); (S - L02_FRAME + 0x40, S - L02_FRAME + 0x68);
   (sa_longl SA, sa_longl SA + 120); (t, t + nt); (mm, mm + SEG_M_SIZE); (c, c + SEG_C_SIZE)].

(** The memory at 0x13984: the machine the printing callees need (mem_inv, MemNorm.task_mem, the stack-protector
    cells, the two .data.rel.ro tables), the stack window [S - 65536, S) present, writable and outside the image, the
    frame cells main reads (0x20 = m + 0x10, 0x28 = the label format, 0x30 = c), the three live blocks (16-aligned,
    outside the image's reserved pages, below the window, pairwise apart and apart from longl's 128 bytes), their
    contents (c holds rc, m holds mc, t is n + 1 writable bytes), the slack after m and after t, the text's source
    bytes (apart from t), and longl (120 writable bytes, then the NUL GI keeps and 7 present bytes). *)
Definition L02_mem (S c mm t nt src : Z) (s : list Z) (rc : rconf) (mc : mconf) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ ssp_ok m /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  S mod 16 = 0 /\ 2 ^ 40 <= S - 65536 /\ S <= 2 ^ 47 /\
  stk rsegs m (S - 65536) S /\ (forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None) /\
  bytes_at rsegs m (S - L02_FRAME + 0x20) (le8 (Z_to_bv 64 (mm + 0x10))) /\
  bytes_at rsegs m (S - L02_FRAME + 0x28) (le8 (Z_to_bv 64 L02_FMT)) /\
  bytes_at rsegs m (S - L02_FRAME + 0x30) (le8 (Z_to_bv 64 c)) /\
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

(** The state at 0x13ad8 (`jal free(text)`): sp, gp, tp, s0 (m), s2 (nfiles), s6 (n') and s10 (&m->n) as at
    0x13984; a0 = s7 = t, s8 = c, s11 = f + 1, s3 = src + n', s5 = the count - n', s4 = the new returned flag; the
    writes inside L02_W; the machine kept; c and m holding the turn's result. *)
Definition L02_post (S c mm t nt src x5 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
    (sp gp tp s0 s2 s6 s10 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s7' s8' s9' s11'
                    t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2 s3' s4' s5' s6 s7' s8' s9' s10
                 s11' t3' t4' t5' t6') F' (Z_to_bv 64 0x13ad8) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ munch (L02_W S c mm t nt) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    MemNorm.task_mem rsegs m' /\
    a0' = Z_to_bv 64 t /\ s7' = Z_to_bv 64 t /\ s8' = Z_to_bv 64 c /\ s11' = Z_to_bv 64 (f + 1) /\
    s3' = Z_to_bv 64 (src + x6) /\ s5' = Z_to_bv 64 (x5 - x6) /\
    s4' = Z_to_bv 64 (b2z (seg_ret (l02_step s lb (f + 1 =? nf) (rc, mc, ret)))) /\
    rconf_at rsegs m' c (seg_rc (l02_step s lb (f + 1 =? nf) (rc, mc, ret))) /\
    mconf_at rsegs m' mm (seg_mc (l02_step s lb (f + 1 =? nf) (rc, mc, ret))).

(** The inner walk: from 0x13984 with the cut's registers (a0 = t, s0 = m, s10 = &m->n, s2 = nfiles, s11 = f,
    s4 = ret, s9 = n, s3 = src, s5 = the count before the take, s6 = n', s8 = lb, sp = S - 208) to L02_post. *)
Definition L02_inner : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S c mm t nt src x5 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool),
    sp = Z_to_bv 64 (S - L02_FRAME) -> a0 = Z_to_bv 64 t -> s0 = Z_to_bv 64 mm -> s10 = Z_to_bv 64 (mm + MC_N) ->
    s2 = Z_to_bv 64 nf -> s11 = Z_to_bv 64 f -> 0 <= f < nf -> nf <= 4 ->
    s4 = Z_to_bv 64 (b2z ret) -> s9 = Z_to_bv 64 (Z.of_nat (length s)) ->
    s3 = Z_to_bv 64 src -> s5 = Z_to_bv 64 x5 -> s6 = Z_to_bv 64 x6 -> s8 = Z_to_bv 64 lb ->
    frm0 fc -> L02_model s lb rc mc -> L02_mem S c mm t nt src s rc mc m ->
    evt rsegs (L02_post S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s6 s10 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13984) fc None m (seg_rom rsegs)).

(** The callee contracts the inner walk takes (SegEnd.v's K_L02): memcpy, snprintf (the printf_model form, for
    the label's %u), memset, m_file, m_refuse, reac_segconf_parse_file, reac_segconf_parse. *)
Definition K_L02 : Prop :=
  memcpy_c.memcpy_contract /\ snprintf_m_c.snprintf_m_contract /\ memset_c.memset_contract /\
  m_file_contract /\ m_refuse_c.m_refuse_contract /\
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract /\ reac_segconf_parse_c.reac_segconf_parse_contract.

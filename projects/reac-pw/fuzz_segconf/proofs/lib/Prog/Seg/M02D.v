(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the interface of its inner
   walk, 0x13ae0 .. `jal calloc` at 0x13c98. The inner walk is
   stated over the machine words of the cut and a memory m0 that already holds every fact the callees ask (the slot
   side, Prog/Seg/M02.v, builds that memory from FR and the cut predicate P_K13ae0, and reads P_K13cac back after the
   two callocs). It is generic in the reader / model states (rc, mc) and the returned flag ret; its premise
   M02_model is the six checks of SegModel.harness_ok the segment runs (MainBPure.mb_checks).
   The code:
   - A, 0x13ae0 .. 0x13b88: check_segments(c = s8, m = s0, returned = s4) (0x13aec); i = s1 < m->n (`lw a0,0(s10)`,
     reloaded each turn), s3 = m + 256 i, `sw s2(0x5a),0x40(sp)`; reac_segconf_role(c, s3, sp + 0x40),
     `lw a1,0x40(sp)`, check_role(a0, a1, s3); reac_segconf_model(c, s3), check_model(a0, s3);
     reac_segconf_ignored(c, s3), check_ignore(a0, s3); s4 = reac_segconf_role_file(c, s3),
     a1 = reac_segconf_ignore_file(c, s3), check_provenance(s4, a1, s3).
   - B, 0x13b88 .. 0x13c00: check_refusals(c, m) (0x13b90); a0 = m->n_kept (`lw 0x3ac(s10)`), s6 = cap
     (`ld s6,0x18(sp)`); s2 = &c->n_refusals, s3 = c->refusal[i], s4 = m->kept[i], s5 = &m->kept_knock[i]; per i
     with i < n_refusals (`lw a0,0(s2)`, `bge`) and i < n_kept (`lw a0,0x3ac(s10)`, `blt`): check_address(s3, s4),
     check_knock_refused(s3, `lw a1,0(s5)`).
   - C, 0x13c00 .. 0x13c64: per i < m->n (s1 = i, s4 = m + 256 i, s3 = "%sx" 0x108cd): snprintf(sp + 0x40, 18, s3,
     s4) (0x13c28), strlen(sp + 0x40), m_find(m, sp + 0x40, len) (0x13c40), check_absent(c, sp + 0x40) when it is
     NULL (0x13c50).
   - D, 0x13c64 .. 0x13c98: m_find(m, "nosuch0" 0x10540, 7) (0x13c74), check_absent(c, "nosuch0") when NULL
     (0x13c88); s4 = s6 + 1 = cap + 1, a1 = 18, a0 = s4, `jal calloc` (0x13c98, to CallocBigC.CALLOC_PC 0x16904,
     ra = 0x13c9c).
   What the segment writes: its callees' frames below main's sp = S - 208, the out cell r at sp + 0x40 and the
   probe[18] at sp + 0x40 (M02_W); nothing else (c, m and main's other frame cells keep their bytes).
   Part of the proof of LLVMFuzzerTestOneInput: this file states segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (statement text of a segment's inner walk). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
Import ListNotations.
Open Scope Z_scope.

(** main's frame: sp = S - 208; the out cell r and the probe[18] share sp + 0x40; the cap cell is sp + 0x18. *)
Definition M02_FRAME : Z := 208.
(** calloc's entry (CallocBigC.CALLOC_PC) and the return address of the first calloc. *)
Definition M02_CALLOC : Z := 0x16904.
Definition M02_RA : Z := 0x13c9c.

(** What the segment may write: the stack below main's frame (its callees' frames) and [sp + 0x40, sp + 0x52). *)
Definition M02_W (S : Z) : list ivl :=
  [(S - 65536, S - M02_FRAME); (S - M02_FRAME + 0x40, S - M02_FRAME + 0x52)].

(** The six checks of SegModel.harness_ok the segment runs, at the state (rc, mc, ret) after the file loop. *)
Definition M02_model (rc : rconf) (mc : mconf) (ret : bool) : Prop :=
  check_segments rc mc ret = true /\
  forallb (check_seg rc) (mc_seg mc) = true /\
  check_refusals rc mc = true /\
  check_kept_all (rc_refusal rc) (mc_kept mc) = true /\
  forallb (fun g => probe_ok rc mc (snprintf_s 18 F_probe [AS (ms_name g)])) (mc_seg mc) = true /\
  probe_ok rc mc S_nosuch = true.

(** The memory at 0x13ae0: the machine the callees need (mem_inv; MemNorm.task_mem and the stack-protector cells
    for snprintf and strstr), the stack window [S - 65536, S) present, writable and outside the image (no reserved
    segment covers it: it lies above 0x60000 = Tac_slot.SL_TOP), S 16-aligned and at most 2^47, main's cap cell
    sp + 0x18, and the two live blocks c and m (16-aligned, below the window) holding rc and mc. *)
Definition M02_mem (S c mm cap : Z) (rc : rconf) (mc : mconf) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ ssp_ok m /\
  S mod 16 = 0 /\ 0x60000 <= S - 65536 /\ S <= 2 ^ 47 /\
  stk rsegs m (S - 65536) S /\ (forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None) /\
  bytes_at rsegs m (S - M02_FRAME + 0x18) (le8 (Z_to_bv 64 cap)) /\
  0 < c /\ c mod 16 = 0 /\ c + SEG_C_SIZE <= S - 65536 /\
  0 < mm /\ mm mod 16 = 0 /\ mm + SEG_M_SIZE <= S - 65536 /\
  rconf_at rsegs m c rc /\ mconf_at rsegs m mm mc.

(** A later memory of the segment: written only inside M02_W since m0, writability kept, the machine facts. *)
Definition M02_inv (S : Z) (m0 m : word -> option byte) : Prop :=
  munch (M02_W S) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ MemNorm.task_mem rsegs m.

(** A state of the segment at pc: sp, gp, tp, s0 = m, s8 = c, s10 = &m->n as at 0x13ae0, s6 as P6 says, fcsr's
    rounding mode 0, the memory an M02_inv successor of m0. *)
Definition M02_mid (pc S c mm : Z) (P6 : word -> Prop) (gp tp : word) (m0 : word -> option byte)
    : machine_state -> Prop :=
  fun ms => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s9' s11'
                    t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms = MS (mkR ra' (Z_to_bv 64 (S - M02_FRAME)) gp tp t0' t1' t2' (Z_to_bv 64 mm) s1' a0' a1' a2' a3' a4' a5' a6'
                 a7' s2' s3' s4' s5' s6' s7' (Z_to_bv 64 c) s9' (Z_to_bv 64 (mm + MC_N)) s11' t3' t4' t5' t6')
            F' (Z_to_bv 64 pc) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ M02_inv S m0 m' /\ P6 s6'.

(** The state at calloc's entry (`jal calloc` at 0x13c98): ra = 0x13c9c, a0 = s4 = cap + 1, a1 = 18, s6 = cap,
    s0 = m, s8 = c, s10 = &m->n; sp, gp, tp as at 0x13ae0. *)
Definition M02_post (S c mm cap : Z) (gp tp : word) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' s1' a2' a3' a4' a5' a6' a7' s2' s3' s5' s7' s9' s11' t3' t4' t5' t6' : word)
                   (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 M02_RA) (Z_to_bv 64 (S - M02_FRAME)) gp tp t0' t1' t2' (Z_to_bv 64 mm) s1'
                 (Z_to_bv 64 (cap + 1)) (Z_to_bv 64 18) a2' a3' a4' a5' a6' a7' s2' s3' (Z_to_bv 64 (cap + 1)) s5'
                 (Z_to_bv 64 cap) s7' (Z_to_bv 64 c) s9' (Z_to_bv 64 (mm + MC_N)) s11' t3' t4' t5' t6')
            F' (Z_to_bv 64 M02_CALLOC) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ M02_inv S m0 m'.

(** The pieces. Each starts from a state with the registers it reads and any M02_inv successor m of m0. *)
Definition M02_A_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf) (mc : mconf)
         (ret : bool),
    sp = Z_to_bv 64 (S - M02_FRAME) -> s0 = Z_to_bv 64 mm -> s8 = Z_to_bv 64 c -> s10 = Z_to_bv 64 (mm + MC_N) ->
    s4 = Z_to_bv 64 (b2z ret) -> frm0 fc ->
    M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m ->
    evt rsegs (M02_mid 0x13b88 S c mm (fun _ => True) gp tp m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13ae0) fc None m (seg_rom rsegs)).

Definition M02_B_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf) (mc : mconf)
         (ret : bool),
    sp = Z_to_bv 64 (S - M02_FRAME) -> s0 = Z_to_bv 64 mm -> s8 = Z_to_bv 64 c -> s10 = Z_to_bv 64 (mm + MC_N) ->
    frm0 fc ->
    M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m ->
    evt rsegs (M02_mid 0x13c00 S c mm (fun w => w = Z_to_bv 64 cap) gp tp m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b88) fc None m (seg_rom rsegs)).

Definition M02_C_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf) (mc : mconf)
         (ret : bool),
    sp = Z_to_bv 64 (S - M02_FRAME) -> s0 = Z_to_bv 64 mm -> s8 = Z_to_bv 64 c -> s10 = Z_to_bv 64 (mm + MC_N) ->
    s6 = Z_to_bv 64 cap -> frm0 fc ->
    M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m ->
    evt rsegs (M02_mid 0x13c64 S c mm (fun w => w = Z_to_bv 64 cap) gp tp m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c00) fc None m (seg_rom rsegs)).

Definition M02_D_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf) (mc : mconf)
         (ret : bool),
    sp = Z_to_bv 64 (S - M02_FRAME) -> s0 = Z_to_bv 64 mm -> s8 = Z_to_bv 64 c -> s10 = Z_to_bv 64 (mm + MC_N) ->
    s6 = Z_to_bv 64 cap -> frm0 fc ->
    M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m ->
    evt rsegs (M02_post S c mm cap gp tp m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c64) fc None m (seg_rom rsegs)).

(** The whole inner walk: from 0x13ae0 on m0 itself to calloc's entry. *)
Definition M02_inner : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (S c mm cap : Z) (rc : rconf) (mc : mconf)
         (ret : bool),
    sp = Z_to_bv 64 (S - M02_FRAME) -> s0 = Z_to_bv 64 mm -> s8 = Z_to_bv 64 c -> s10 = Z_to_bv 64 (mm + MC_N) ->
    s4 = Z_to_bv 64 (b2z ret) -> frm0 fc ->
    M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 ->
    evt rsegs (M02_post S c mm cap gp tp m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13ae0) fc None m0 (seg_rom rsegs)).

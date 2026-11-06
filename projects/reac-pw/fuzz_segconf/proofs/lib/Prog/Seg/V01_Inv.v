(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f = pinned 3776ca44d75c):
   K13cac -> K13f40, [0x13cac, 0x13f40) and the -1 exit [0x13fa0, 0x13fb0) of the plain binary.
   This file fixes the interface between the pieces of the walk: the states the run passes
   through, their invariants, and the statement of each piece (a Prop each piece file proves).

   The run (one evt, on the normalized memory; registers ra 1, sp 2, gp 3, tp 4, s0 8, s1 9, a0-a7 10-17, s2-s11
   18-27; sp = S - 208 throughout; s0 = m, s10 = m + 0x2000 never change):
   - HEAD  0x13cac .. 0x13d60: NULL tests of tab, mt (dead), memset(&tab[cap], 0x5a, 18), `sw zero, 0x3c(sp)`, the
           flags & 1 / cap > 0 branch (memcpy "enp1s0" into tab[0] and mt[0], vid 33, n = 1), 0x20(sp) = mt,
           s4 = m->n; m->n <= 0 goes to TAIL (0x13efc: 0x18(sp) = 0, s6 = a1), else the loop registers and the mask
           2^50 + 3 at 0x28(sp), then LOOP at turn 0.
   - LOOP  0x13d64 (turn i, [v01_head_st]): SPLIT (0x13d64 .. 0x13e60: ignore test, strrchr, the digit loop 0x13db0
           [v01_dig_stmt], the parent loop 0x13dec [v01_par_stmt], memcpy(v.parent, name, pn), the NUL, v.vid) ends at
           JOIN (0x13d74, the `continue`) or at ADD (0x13e64, [v01_add_st]); ADD (0x13e64 .. 0x13ef8: the duplicate
           loop 0x13e80 [v01_dup_stmt], the cap test, memcpy(&mt[mn], &v, 20), added++) ends at JOIN or, when
           mn >= cap, at the -1 exit 0x13fa0 .. 0x13fac, which goes to TAIL. JOIN (0x13d74 .. 0x13d84) goes to LOOP
           at turn i + 1 or to TAIL.
   - TAIL  0x13f04 .. 0x13f3c: reac_segconf_declared(c, tab, cap, sp + 0x3c), check_declared(got, want, tab, n, mt,
           mn, cap); END at 0x13f40 ([v01_end]).
   The frame cells of main (sp = S - 208): 0 mn spill, 8 flags then tab spill, 0x10 cap, 0x18 added, 0x20 mt, 0x28 the
   mask, 0x30 c, 0x3c n (int), 0x40 .. 0x54 v (parent[16], vid). The model (Spec/SegModel.v): m_declared (m_decl_go
   over mc_seg) from seg_tab0 inp with cap = seg_cap inp; [V01_RES] its result, which TAIL hands to check_declared.
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_env seg_cuts.
Import ListNotations.
Open Scope Z_scope.

(* ---- Constants ---- *)
(* m_split's character mask (0x13d48 .. 0x13d58): bits 0, 1 and 50 for '-', '.' and '_' (ch - 0x2d). *)
Definition V01_MASK : Z := 2 ^ 50 + 3.
(* The errno cell errno_addr B = ms_tp B + ms_errno_off B = 0x32c10 - 164 (Tac_seg.ERRNO_CELL). *)
Definition V01_ERRNO : Z := 0x32b6c.

(* ---- The machine state of the run at pc, all 31 registers named ---- *)
Definition vst (pc : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
    t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(* ---- The payload's names ---- *)
Definition v_cap (inp : list byte) : Z := seg_cap inp.
Definition v_mc (inp : list byte) : mconf := seg_mc (run (seg_pay inp)).
Definition v_rc (inp : list byte) : rconf := seg_rc (run (seg_pay inp)).
Definition v_segs (inp : list byte) : list mseg := mc_seg (v_mc inp).
Definition v_nsegs (inp : list byte) : Z := Z.of_nat (length (v_segs inp)).
Definition v_tab0 (inp : list byte) : list (list Z * Z) := seg_tab0 inp.
Definition v_n0 (inp : list byte) : Z := Z.of_nat (length (v_tab0 inp)).
(* What the harness's m_declared computes (H:663) and check_declared receives as (want, mt, mn). *)
Definition V01_RES (inp : list byte) : Z * list (list Z * Z) := m_declared (v_mc inp) (v_tab0 inp) (v_cap inp).

(* ---- Write sets ---- *)
(* What the run writes before reac_segconf_declared: the stack window below the saved registers (main's frame cells
   and the callees' frames) and the two tables. *)
Definition v01_W (inp : list byte) (S tab mt : Z) : list ivl :=
  [(S - 65536, S - 104); (mt, mt + MT_N inp); (tab, tab + TAB_N inp)].
(* The whole run's: reac_segconf_declared also writes the errno cell (Tac_seg.seg_We). *)
Definition v01_We (inp : list byte) (S tab mt : Z) : list ivl := (V01_ERRNO, V01_ERRNO + 4) :: v01_W inp S tab mt.

(* ---- Facts fixed for the whole run ---- *)
(* The stack window [S - 65536, S) and the four live blocks c, m, tab, mt (each below the window, 16-aligned, in no
   reserved page of the image, pairwise apart). *)
Definition v01_geo (inp : list byte) (S c mm tab mt : Z) : Prop :=
  S mod 16 = 0 /\ 0x60000 <= S - 65536 /\ S <= 2 ^ 47 /\
  (forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None) /\
  4096 <= c /\ c + SEG_C_SIZE <= S - 65536 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\
  4096 <= mm /\ mm + SEG_M_SIZE <= S - 65536 /\ mm mod 16 = 0 /\ blk_noimg rsegs mm SEG_M_SIZE /\
  4096 <= tab /\ tab + TAB_N inp <= S - 65536 /\ tab mod 16 = 0 /\ blk_noimg rsegs tab (TAB_N inp) /\
  4096 <= mt /\ mt + MT_N inp <= S - 65536 /\ mt mod 16 = 0 /\ blk_noimg rsegs mt (MT_N inp) /\
  apart c SEG_C_SIZE mm (mm + SEG_M_SIZE) /\ apart c SEG_C_SIZE tab (tab + TAB_N inp) /\
  apart c SEG_C_SIZE mt (mt + MT_N inp) /\ apart mm SEG_M_SIZE tab (tab + TAB_N inp) /\
  apart mm SEG_M_SIZE mt (mt + MT_N inp) /\ apart tab (TAB_N inp) mt (mt + MT_N inp).

(* The facts of the run's start memory m0 that lie outside v01_W, so every memory m with munch (v01_W ..) m0 m and
   wmono m0 m keeps them (Frame.bytes_at_transport, rw_cells_transport): the reader's state in c, the model's in m,
   the errno cell (present and writable), the stack-protector cells. *)
Definition v01_base (inp : list byte) (c mm : Z) (m0 : word -> option byte) : Prop :=
  rconf_at rsegs m0 c (v_rc inp) /\ mconf_at rsegs m0 mm (v_mc inp) /\
  (exists ev : word, rw_cells rsegs m0 V01_ERRNO [C4 ev]) /\ ssp_ok m0.

(* ---- Memory invariants ---- *)
(* Main's frame cells [sp, sp + 0x40) (sp = S - 208), one cell each: 0, 8, 0x10, 0x18, 0x20, 0x28, 0x30 (8 bytes),
   0x38, 0x3c (4 bytes). *)
Definition v01_frame (S : Z) (w00 w08 w10 w18 w20 w28 w30 w38 w3c : word) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (S - 208) [C8 w00; C8 w08; C8 w10; C8 w18; C8 w20; C8 w28; C8 w30; C4 w38; C4 w3c].

(* The memory facts every state from the loop on carries: the run so far writes only v01_W and keeps writability,
   mem_inv, the stack below main's frame, and the table tab as HEAD leaves it (tab0 in its first entries, the free
   entries below tab[cap] present and writable, the guard entry tab[cap]). *)
Definition v01_mem (inp : list byte) (S tab mt : Z) (m0 m : word -> option byte) : Prop :=
  munch (v01_W inp S tab mt) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  stk rsegs m (S - 65536) (S - 208) /\
  rtab_at rsegs m tab (v_tab0 inp) /\
  (exists fr, rw_cells rsegs m (tab + RVLAN_SIZE * v_n0 inp)
                [CB (Z.to_nat (RVLAN_SIZE * (v_cap inp - v_n0 inp))) fr]) /\
  guard_at rsegs m tab (v_cap inp).

(* The table mt holds T, its free entries (up to mt[cap]) present and writable. *)
Definition v01_mt (inp : list byte) (mt : Z) (T : list (list Z * Z)) (m : word -> option byte) : Prop :=
  Z.of_nat (length T) <= v_cap inp /\
  mtab_at rsegs m mt T /\
  (exists fr, rw_cells rsegs m (mt + MVLAN_SIZE * Z.of_nat (length T))
                [CB (Z.to_nat (MVLAN_SIZE * (v_cap inp + 1 - Z.of_nat (length T)))) fr]).

(* The model's loop invariant before turn k: T the table so far, added the count so far. *)
Definition v01_model (inp : list byte) (k : nat) (T : list (list Z * Z)) (added : Z) : Prop :=
  added + v_n0 inp = Z.of_nat (length T) /\
  m_decl_go (skipn k (v_segs inp)) T (v_cap inp) added = V01_RES inp.

(* ---- The states ---- *)
(* LOOP 0x13d64 at turn i (also JOIN 0x13d74 after turn i, with v01_model (Nat.succ i)): s0 = m, s1 = m + 256 i,
   s2 = i, s3 = tab, s4 = m->n, s6 = mn, s8 = 4094, s9 = -(m + 256 i), s10 = m + 0x2000, s11 = -10. *)
Definition v01_loop_st (pc : Z) (inp : list byte) (S mm tab : Z) (i : nat) (T : list (list Z * Z))
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state :=
  vst pc ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 (Z_to_bv 64 mm) (Z_to_bv 64 (mm + 256 * Z.of_nat i))
    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 tab) (Z_to_bv 64 (v_nsegs inp)) s5
    (Z_to_bv 64 (Z.of_nat (length T))) s7 (Z_to_bv 64 4094) (Z_to_bv 64 (- (mm + 256 * Z.of_nat i)))
    (Z_to_bv 64 (mm + 0x2000)) (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m.

(* The memory at LOOP (turn i) and at JOIN (after turn i): k = i at LOOP, k = S i at JOIN. *)
Definition v01_loop_mem (inp : list byte) (S c tab mt : Z) (m0 : word -> option byte) (i k : nat)
    (T : list (list Z * Z)) (added : Z) (m : word -> option byte) : Prop :=
  (i < length (v_segs inp))%nat /\ v01_model inp k T added /\ v01_mem inp S tab mt m0 m /\ v01_mt inp mt T m /\
  (exists w00 w08 w38, v01_frame S w00 w08 (Z_to_bv 64 (v_cap inp)) (Z_to_bv 64 added) (Z_to_bv 64 mt)
                         (Z_to_bv 64 V01_MASK) (Z_to_bv 64 c) w38 (Z_to_bv 64 (v_n0 inp)) m) /\
  (exists vb, rw_cells rsegs m (S - 208 + 64) [CB 20 vb]).

(* ADD 0x13e64, turn i, segment i not ignored and m_split of its name = Some (p, vid): s5 = vid, 8(sp) = tab (the
   spill at 0x13e40), v = (p, vid) at sp + 0x40 (struct mvlan, 20 bytes); s3 and s7 are free here. *)
Definition v01_add_st (inp : list byte) (S mm : Z) (i : nat) (T : list (list Z * Z)) (vid : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state :=
  vst 0x13e64 ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 (Z_to_bv 64 mm) (Z_to_bv 64 (mm + 256 * Z.of_nat i))
    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat i)) s3 (Z_to_bv 64 (v_nsegs inp)) (Z_to_bv 64 vid)
    (Z_to_bv 64 (Z.of_nat (length T))) s7 (Z_to_bv 64 4094) (Z_to_bv 64 (- (mm + 256 * Z.of_nat i)))
    (Z_to_bv 64 (mm + 0x2000)) (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m.

Definition v01_add_mem (inp : list byte) (S c tab mt : Z) (m0 : word -> option byte) (i : nat)
    (T : list (list Z * Z)) (added : Z) (p : list Z) (vid : Z) (m : word -> option byte) : Prop :=
  (i < length (v_segs inp))%nat /\ v01_model inp i T added /\
  ms_ignore (nth i (v_segs inp) mseg_d) = false /\ m_split (ms_name (nth i (v_segs inp) mseg_d)) = Some (p, vid) /\
  v01_mem inp S tab mt m0 m /\ v01_mt inp mt T m /\
  (exists w00 w38, v01_frame S w00 (Z_to_bv 64 tab) (Z_to_bv 64 (v_cap inp)) (Z_to_bv 64 added) (Z_to_bv 64 mt)
                     (Z_to_bv 64 V01_MASK) (Z_to_bv 64 c) w38 (Z_to_bv 64 (v_n0 inp)) m) /\
  (exists vb, rw_cells rsegs m (S - 208 + 64) [CB 20 vb] /\ mvlan_enc (p, vid) vb).

(* TAIL 0x13f04: s0 = m, s3 = tab, s6 = mn = length (snd V01_RES), 0x18(sp) = fst V01_RES, mt holds snd V01_RES. *)
Definition v01_tail_st (S mm tab : Z) (mn : Z)
    (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  vst 0x13f04 ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 (Z_to_bv 64 mm) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
    (Z_to_bv 64 tab) s4 s5 (Z_to_bv 64 mn) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.

Definition v01_tail_mem (inp : list byte) (S c tab mt : Z) (m0 m : word -> option byte) : Prop :=
  v01_mem inp S tab mt m0 m /\ v01_mt inp mt (snd (V01_RES inp)) m /\
  (exists w00 w08 w28 w38, v01_frame S w00 w08 (Z_to_bv 64 (v_cap inp)) (Z_to_bv 64 (fst (V01_RES inp)))
                             (Z_to_bv 64 mt) w28 (Z_to_bv 64 c) w38 (Z_to_bv 64 (v_n0 inp)) m).

(* END 0x13f40 (K13f40): s0 = m, s1 = c, s3 = tab, s4 = mt; sp, gp, tp, F, fc as at the start. *)
Definition v01_end_st (S c mm tab mt : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  vst 0x13f40 ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 (Z_to_bv 64 mm) (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7 s2
    (Z_to_bv 64 tab) (Z_to_bv 64 mt) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.

(* ---- The continuations each piece hands its exit states to ---- *)
(* The continuations of one turn i (K_loop_at at LOOP before it, K_join_at at JOIN after it, K_add_at at ADD in it):
   a piece that runs turn i hands on states of turn i only. *)
Definition K_loop_at (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (i : nat) : Prop :=
  forall T added (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word) m,
    v01_loop_mem inp S c tab mt m0 i i T added m ->
    evt rsegs Q (v01_loop_st 0x13d64 inp S mm tab i T ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6
                   F fc m).

Definition K_loop (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) : Prop :=
  forall i, K_loop_at inp S c mm tab mt m0 gp tp F fc Q i.

Definition K_join_at (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (i : nat) : Prop :=
  forall T added (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word) m,
    v01_loop_mem inp S c tab mt m0 i (Nat.succ i) T added m ->
    evt rsegs Q (v01_loop_st 0x13d74 inp S mm tab i T ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6
                   F fc m).

Definition K_add_at (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (i : nat) : Prop :=
  forall T added p vid (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 : word) m,
    v01_add_mem inp S c tab mt m0 i T added p vid m ->
    evt rsegs Q (v01_add_st inp S mm i T vid ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 F fc m).

Definition K_tail (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) : Prop :=
  forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m,
    v01_tail_mem inp S c tab mt m0 m ->
    evt rsegs Q (v01_tail_st S mm tab (Z.of_nat (length (snd (V01_RES inp)))) ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4
                   a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).

Definition K_end (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m,
    munch (v01_We inp S tab mt) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    Q (v01_end_st S c mm tab mt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc
         m).

(* ---- The piece statements ---- *)

(* HEAD (V01_Head.v; callees memset, memcpy): from K13cac to LOOP at turn 0 or to TAIL. At 0x13cac: a0 = mt,
   s3 = tab, s4 = cap + 1, s6 = cap, s0 = m, s10 = m + 0x2000 (seg_cuts.P_K13cac); 8(sp) = flags, 0x10(sp) = cap,
   0x30(sp) = c (P_mcore); both tables all zero; m0 is this memory. *)
Definition v01_head_pre (inp : list byte) (S c tab mt : Z) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ stk rsegs m (S - 65536) (S - 208) /\
  (exists w00 w18 w20 w28 w38 w3c, v01_frame S w00 (Z_to_bv 64 (seg_flags inp)) (Z_to_bv 64 (v_cap inp)) w18 w20
                                     w28 (Z_to_bv 64 c) w38 w3c m) /\
  (exists vb, rw_cells rsegs m (S - 208 + 64) [CB 20 vb]) /\
  rw_cells rsegs m tab [CB (Z.to_nat (TAB_N inp)) (repeat ZERO (Z.to_nat (TAB_N inp)))] /\
  rw_cells rsegs m mt [CB (Z.to_nat (MT_N inp)) (repeat ZERO (Z.to_nat (MT_N inp)))].

Definition v01_head_stmt : Prop :=
  forall (inp : list byte) (S c mm tab mt : Z) (m : word -> option byte) (gp tp : word) (F : bvmap 5 word)
         (fc : bv 32) (Q : machine_state -> Prop)
         (ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word),
    v01_geo inp S c mm tab mt -> v01_base inp c mm m -> v01_head_pre inp S c tab mt m ->
    K_loop inp S c mm tab mt m gp tp F fc Q -> K_tail inp S c mm tab mt m gp tp F fc Q ->
    evt rsegs Q (vst 0x13cac ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 (Z_to_bv 64 mm) s1 (Z_to_bv 64 mt) a1 a2 a3
                   a4 a5 a6 a7 s2 (Z_to_bv 64 tab) (Z_to_bv 64 (v_cap inp + 1)) s5 (Z_to_bv 64 (v_cap inp)) s7
                   s8 s9 (Z_to_bv 64 (mm + 0x2000)) s11 t3 t4 t5 t6 F fc m).

(* SPLIT (V01_Split.v; callees strrchr, memcpy; the digit and parent loops by v01_dig_stmt and v01_par_stmt): from
   LOOP at turn i to JOIN after turn i (segment ignored, or m_split of its name None: T and added unchanged) or to
   ADD in turn i. *)
Definition v01_split_stmt : Prop :=
  forall (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word) (F : bvmap 5 word)
         (fc : bv 32) (Q : machine_state -> Prop) (i : nat),
    v01_geo inp S c mm tab mt -> v01_base inp c mm m0 ->
    K_join_at inp S c mm tab mt m0 gp tp F fc Q i -> K_add_at inp S c mm tab mt m0 gp tp F fc Q i ->
    K_loop_at inp S c mm tab mt m0 gp tp F fc Q i.

(* ADD (V01_Add.v; callee memcpy; the duplicate loop by v01_dup_stmt): from ADD in turn i to JOIN after turn i (a
   duplicate: T unchanged; or the entry appended: T ++ [(p, vid)], added + 1) or, when mn >= cap, through the -1
   exit to TAIL. *)
Definition v01_add_stmt : Prop :=
  forall (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word) (F : bvmap 5 word)
         (fc : bv 32) (Q : machine_state -> Prop) (i : nat),
    v01_geo inp S c mm tab mt -> v01_base inp c mm m0 ->
    K_join_at inp S c mm tab mt m0 gp tp F fc Q i -> K_tail inp S c mm tab mt m0 gp tp F fc Q ->
    K_add_at inp S c mm tab mt m0 gp tp F fc Q i.

(* LOOP (V01_Loop.v): JOIN goes to LOOP at turn i + 1 or to TAIL; with SPLIT and ADD, every LOOP state reaches TAIL. *)
Definition v01_loop_stmt : Prop :=
  forall (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word) (F : bvmap 5 word)
         (fc : bv 32) (Q : machine_state -> Prop),
    v01_geo inp S c mm tab mt -> v01_base inp c mm m0 ->
    K_tail inp S c mm tab mt m0 gp tp F fc Q -> K_loop inp S c mm tab mt m0 gp tp F fc Q.

(* TAIL (V01_Tail.v; callees reac_segconf_declared, check_declared): from TAIL to END. *)
Definition v01_tail_stmt : Prop :=
  forall (inp : list byte) (S c mm tab mt : Z) (m0 : word -> option byte) (gp tp : word) (F : bvmap 5 word)
         (fc : bv 32) (Q : machine_state -> Prop),
    v01_geo inp S c mm tab mt -> v01_base inp c mm m0 -> bv_unsigned tp = 0x32c10 ->
    K_end inp S c mm tab mt m0 gp tp F fc Q -> K_tail inp S c mm tab mt m0 gp tp F fc Q.

(* The digit loop of m_split (V01_Dig.v), 0x13db0 .. 0x13dd0 (H:329-334): a2 = q the current character (dot[1] on
   entry, nonzero), a1 = ptr the address of the next one, s5 = vid so far, a4 = 10, s8 = 4094, s11 = -10; the
   characters from ptr on are rest and its NUL. It writes only a1, a2, a3, s5 and no memory; it exits to JOIN
   (0x13d74) when m_digits refuses (a character that is not a digit, or vid > 4094), else at 0x13dd4 with s5 = the
   value. *)
Definition v01_dig_stmt : Prop :=
  forall (Q : machine_state -> Prop) (m : word -> option byte) (rest : list byte) (q vid ptr : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32),
    0 < q < 256 -> 0 <= vid <= 4094 -> 0 <= ptr ->
    bytes_at rsegs m ptr (rest ++ [ZERO]) -> ~ In ZERO rest ->
    (m_digits (q :: zs rest) vid = None -> forall a1' a2' a3' s5' : word,
       evt rsegs Q (vst 0x13d74 ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' (Z_to_bv 64 10) a5 a6 a7 s2 s3 s4 s5' s6 s7
                      (Z_to_bv 64 4094) s9 s10 (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m)) ->
    (forall v, m_digits (q :: zs rest) vid = Some v -> forall a1' a2' a3' : word,
       evt rsegs Q (vst 0x13dd4 ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' (Z_to_bv 64 10) a5 a6 a7 s2 s3 s4
                      (Z_to_bv 64 v) s6 s7 (Z_to_bv 64 4094) s9 s10 (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m)) ->
    evt rsegs Q (vst 0x13db0 ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 ptr) (Z_to_bv 64 q) a3 (Z_to_bv 64 10) a5 a6
                   a7 s2 s3 s4 (Z_to_bv 64 vid) s6 s7 (Z_to_bv 64 4094) s9 s10 (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc m).

(* The parent loop of m_split (V01_Par.v), 0x13dec .. 0x13e3c (H:339-344): a0 = k the characters left (k >= 1),
   a1 = ptr the next one, the mask 2^50 + 3 at sp + 0x28; the k characters at ptr are cs. It writes only a0, a1, a3,
   a4, a5 and no memory; it exits to JOIN (0x13d74) at the first character that is not a parent character
   (SegModel.h_parent_ok), else at 0x13e40. *)
Definition v01_par_stmt : Prop :=
  forall (Q : machine_state -> Prop) (m : word -> option byte) (cs : list byte) (k ptr spv : Z)
         (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32),
    k = Z.of_nat (length cs) -> 1 <= k -> 0 <= ptr -> 0 <= spv ->
    bytes_at rsegs m ptr cs -> bytes_at rsegs m (spv + 0x28) (le8 (Z_to_bv 64 V01_MASK)) ->
    (forallb h_parent_ok (zs cs) = false -> forall a0' a1' a3' a4' a5' : word,
       evt rsegs Q (vst 0x13d74 ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3' a4' a5' a6 a7 s2 s3 s4 s5 s6
                      s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) ->
    (forallb h_parent_ok (zs cs) = true -> forall a0' a1' a3' a4' a5' : word,
       evt rsegs Q (vst 0x13e40 ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3' a4' a5' a6 a7 s2 s3 s4 s5 s6
                      s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) ->
    evt rsegs Q (vst 0x13dec ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 k) (Z_to_bv 64 ptr) a2 a3 a4 a5
                   a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).

(* The duplicate loop of m_declared (V01_Dup.v; callee strcmp), 0x13e80 .. 0x13eac (H:361-362): s7 = mt + 20 k,
   s6 = mt + 20 mn (mn = length T >= 1, k < mn), s3 = acc (0 or 1), s5 = vid, sp = spv; mt holds T, the parent of v
   at spv + 0x40 is the C string p. It writes only ra, a0 - a3, s3, s7 and no memory; it exits at 0x13eb0 with
   s3 = acc OR the model's existsb over the entries k .. mn - 1. *)
Definition v01_dup_stmt : Prop :=
  forall (Q : machine_state -> Prop) (m : word -> option byte) (mt spv vid : Z) (T : list (list Z * Z))
         (sy : list byte) (k : nat) (acc : bool)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32),
    mtab_at rsegs m mt T -> (k < length T)%nat -> 0 <= mt -> mt + MVLAN_SIZE * Z.of_nat (length T) < 2 ^ 63 ->
    0 <= spv -> spv + 0x40 + 16 < 2 ^ 63 ->
    bytes_at rsegs m (spv + 0x40) (sy ++ [ZERO]) -> ~ In ZERO sy -> 0 < vid <= 4094 ->
    (forall ra' a0' a1' a2' a3' s7' : word,
       evt rsegs Q (vst 0x13eb0 ra' (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2
                      (Z_to_bv 64 (b2z (acc || existsb (fun e => (snd e =? vid) && (strcmp (fst e) (zs sy) =? 0))
                                                        (skipn k T))))
                      s4 (Z_to_bv 64 vid) (Z_to_bv 64 (mt + MVLAN_SIZE * Z.of_nat (length T))) s7' s8 s9 s10 s11
                      t3 t4 t5 t6 F fc m)) ->
    evt rsegs Q (vst 0x13e80 ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                   (Z_to_bv 64 (b2z acc)) s4 (Z_to_bv 64 vid) (Z_to_bv 64 (mt + MVLAN_SIZE * Z.of_nat (length T)))
                   (Z_to_bv 64 (mt + MVLAN_SIZE * Z.of_nat k)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m).

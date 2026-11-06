(* The op_unmark arm (c3) of LLVMFuzzerTestOneInput, plain image: its program points and the cut
   predicates its one segment passes through.

   The segment (fuzz_link.c:733-742, the listing 0x13a1c-0x13a64, 0x13b24-0x13bc8, 0x13dc4-0x13ddc and
   the tail 0x1406c-0x14078) runs from the loop head of operation i (lh_ms, op byte % 6 = 3):
     HEAD  dispatch, kernel(sp+0x40) at 0x13b28, model_begin 0x13b2c-0x13b48     -> c3_mb  (0x13b4c)
     LOOP  the inlined model_unmark loop 0x13b4c-0x13bb4 (model_read, bcmp, model_write) -> c3_ub (0x13bb8)
     TAIL  n_mark = 0, reac_served_unmark_all(marks), check_socket, check_marks, check_requests, the tail
           -> lh_ms E (i + 1) or ex_ms E.
   Every cut is stated on the canonical mkR state; a piece that passes a leaf call ends up to ms_eqv
   (LDefs.eqv_cl). Every cut carries `munch (c3_W E) m0 m /\ wmono rsegs m0 m` against the memory m0 at
   the loop head, so the segment's seg_fp follows (LC3Lib.c3_seg_fp). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Program points of the arm (plain listing)
   ========================================================================== *)

Definition L3_KCALL : Z := 0x13b28.   (* jal kernel, a0 = sp + 0x40 *)
Definition L3_KRET : Z := 0x13b2c.    (* lw a0, 0x20c(s1): model_begin *)
Definition L3_MB : Z := 0x13b4c.      (* lw a0, 0x204(s10): m->n_mark, the loop test *)
Definition L3_BODY : Z := 0x13b5c.    (* addi a4, sp, 0x78: one model_read of m->mark[j] *)
Definition L3_RD_RA : Z := 0x13b78.   (* after model_read *)
Definition L3_CMP_RA : Z := 0x13b90.  (* after bcmp *)
Definition L3_LATCH : Z := 0x13ba8.   (* lw a0, 0x204(s10), after model_write or a skip *)
Definition L3_UB : Z := 0x13bb8.      (* sw zero, 0x204(s10): m->n_mark = 0 *)
Definition L3_UA_RA : Z := 0x13bc4.   (* after reac_served_unmark_all: jal check_socket *)

(* ==========================================================================
   2. What every cut of the arm keeps
   ========================================================================== *)

(* the memory at a cut: the frame (cursor cells (P, N) as kernel left them), the saved registers, the
   fake kernel kbs, the model mbs, the marks gbs, the image views lh_mem keeps, the payload, errno, the
   guard, and the memory invariants *)
Definition c3_mem (E : lenv) (P N : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  (exists j0 j1 j2, rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P N j0 j1 j2)) /\
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ la_ok m /\ texts_at m /\ ifptrs_at m /\
  model_at m (e_md E) mbs /\ model_wf mbs /\
  marks_at m (e_mk E) gbs /\ marks_wf gbs /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m /\
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* the fake kernel's bookkeeping during operation i, after model_begin *)
Definition c3_kfacts (i : Z) (kbs : list byte) : Prop :=
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i /\
  nk_n_sent kbs = 0.

(* what reac_served_unmark_all computes (its Post), and what the model's loop must compute: link_spec
   `unmark` over the kept names, from the kernel's request list and chunk state after model_begin *)
Definition c3_U (kbs gbs : list byte) : list (list byte) * kstate :=
  unmark link_tab (mk_names gbs) (nk_sent kbs) (nk_kstate kbs).

(* the register file at a cut: sp, gp, tp, s0 = m, s1 = &g_nl + 0x40000, s5 = 46, s6 = the jump table,
   s7 = marks, s8 = 0xab, s9 = 4, s10 = &m->n_req, s11 = i; the others are given *)
Definition c3_regs (E : lenv) (i : Z) (gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word)
  : bvmap 5 word :=
  mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6.

(* ==========================================================================
   3. The cuts
   ========================================================================== *)

(* 0x13b4c, after kernel and model_begin: the model's state is the kernel's (md_kstate = nk_kstate),
   no request owed yet on either side *)
Definition c3_mb (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz L3_MB) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c3_mem E P N kbs mbs gbs m /\ c3_kfacts i kbs /\
    md_kstate mbs kbs = nk_kstate kbs /\ md_n_req mbs = 0 /\ marks_are gbs mbs /\
    munch (c3_W E) m0 m /\ wmono rsegs m0 m.

(* 0x13b5c, the loop body for mark j: s2 = &m->mark[j], s3 = j; the requests owed so far and the
   model's state, walked by `unmark` over the remaining names, give c3_U *)
Definition c3_lp (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (P N : Z) (kbs gbs : list byte)
    (j : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (mbs : list byte),
    ms = MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_md E + MD_MARK + MARK_LEN * j)) (wz j) s4
                     t3 t4 t5 t6)
            F (wz L3_BODY) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= j < md_n_mark mbs /\
    c3_mem E P N kbs mbs gbs m /\ c3_kfacts i kbs /\ marks_are gbs mbs /\
    unmark_walk link_tab (skipn (Z.to_nat j) (mk_names gbs)) (md_reqs mbs) (md_kstate mbs kbs) = c3_U kbs gbs /\
    munch (c3_W E) m0 m /\ wmono rsegs m0 m.

(* 0x13bb8, after the loop: the model owes exactly the requests `unmark` owes *)
Definition c3_ub (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte),
    ms = MS (c3_regs E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz L3_UB) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c3_mem E P N kbs mbs gbs m /\ c3_kfacts i kbs /\ marks_are gbs mbs /\
    md_reqs mbs = fst (c3_U kbs gbs) /\
    munch (c3_W E) m0 m /\ wmono rsegs m0 m.

(* the end of the segment: the next loop head or the exit, within the arm's footprint *)
Definition c3_post (E : lenv) (i : Z) (gp : word) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  ((i < 47 /\ lh_ms E (i + 1) gp ms) \/ ex_ms E gp ms) /\
  seg_fp (e_S E) [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)] m0 (ms_mem ms).

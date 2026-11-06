(* Arms 4 and 5 of the slot's loop (fuzz_link.c:744-762), plain image: op_decide (op byte % 6 = 4,
   L_OP4 = 0x13a9c) and op_refused (op byte % 6 = 5, L_OP5 = 0x13bf4). The cut predicates of their evt
   segments, in the style of LDefs' lh_ms: the whole register file as `mkR`, frm0, and memory facts
   only over the slot's carried regions (the frame [S - 480, S), g_nl, g_names, long_alias, .rodata /
   .data.rel.ro, the md and mk blocks, the payload, errno, the GOT guard cells, and the heap blocks
   text_of hands this arm).

   op_decide (0x13a9c - 0x13af8):
     c45_13aa4  the call of text_of (0x15aa8) at 0x13aa4: a0 = sp+0x40 (cursor), a1 = sp+0x78; ra 0x13aa8
     c45_13aa8  its return: a0 = the kind string s1 (own1 at sp+0x78)
     c45_13ab4  the call of text_of at 0x13ab4: a0 = sp+0x40, a1 = sp+0x50; ra 0x13ab8; s2 = s1
     c45_13ab8  its return: a0 = the alias string s2v (own2 at sp+0x50)
     c45_13ae8  the call of free (0x173d4) at 0x13ae8: a0 = own1; ra 0x13aec (after reac_served_decide,
                model_decide and check_verdict, all `leaf`)
     c45_13aec  its return
     c45_13af0  the call of free at 0x13af0: a0 = own2; ra 0x13af4
     c45_end    the arm's end (0x13af4, and 0x13dd8 for op_refused): `bltu s5, s11` then the tail
   op_refused (0x13bf4 - 0x13c7c, 0x13dd0 - 0x13ddc):
     c45_13c70  the call of mark_quietly (0x15d88) at 0x13c70 after the byte w and model_begin:
                a0 = (w & 1 ? NULL : marks), a1 = (w & 2 ? "" : NULL); ra 0x13c74
     c45_13c74  its return, with mark_quietly's Post (mark_quietly_c.v) in the form it gives it

   Offsets from the frame base sp = S - 480 (LDefs section 2): the eight pointer cells 0x00 - 0x40,
   the cursor (p, n) at 0x40 / 0x48, the 40-byte buffer at 0x50 (op_decide's `oa` cell), the 256-byte
   buffer at 0x78 (op_decide's `ok` cell), the saved registers at 0x178. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Program points
   ========================================================================== *)

Definition C45_FREE : Z := 0x173d4.          (* free (FrameAPI: ms_free B = 0x173d4) *)
Definition C45_TO1_RA : Z := 0x13aa8.        (* jal text_of at 0x13aa4 *)
Definition C45_TO2_RA : Z := 0x13ab8.        (* jal text_of at 0x13ab4 *)
Definition C45_FR1_RA : Z := 0x13aec.        (* jal free at 0x13ae8 *)
Definition C45_FR2_RA : Z := 0x13af4.        (* jal free at 0x13af0 *)
Definition C45_MQ_RA : Z := 0x13c74.         (* jal mark_quietly at 0x13c70 *)
Definition C45_END_D : Z := 0x13af4.         (* op_decide's end: bltu s5, s11, 0x1413c; j 0x1406c *)
Definition C45_END_R : Z := 0x13dd8.         (* op_refused's end (after check_requests), the same two *)

(* ==========================================================================
   2. The memory both arms keep
   ========================================================================== *)

(* the frame base and the four places the arms use *)
Definition c45_sp (E : lenv) : Z := e_S E - SLOT_FRAME.

(* the eight cells below the cursor (sp+0x00 .. sp+0x40), as lh_cells has them *)
Definition c45_ptrs (E : lenv) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E));
   C8 (wz A_G_NAMES); C8 (wz A_JT); C8 (wz GNL42)].

(* the frame without its two buffers: the pointer cells, the cursor (P, N), the saved bytes *)
Definition c45_frame (E : lenv) (j0 : list byte) (P N : Z) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (c45_sp E) (c45_ptrs E j0) /\
  rw_cells rsegs m (c45_sp E + FO_P) [C8 (wz P); C8 (wz N)] /\
  bytes_at rsegs m (e_S E - 104) (e_saved E).

(* the cursor is a suffix of the payload (cursor_ok without its memory half) *)
Definition c45_cur (E : lenv) (P N : Z) : Prop :=
  exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P = e_p0 E + k /\ N = Z.of_nat (length (e_pl E)) - k.

(* what neither arm writes: g_names, odd, the policy strings, long_alias, texts, the interface
   pointers, errno's writability, the guard words, the payload *)
Definition c45_keep (E : lenv) (m : word -> option byte) : Prop :=
  gnames_at m /\ odd_at m /\ policy_ro m /\ la_ok m /\ texts_at m /\ ifptrs_at m /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m /\ bytes_at rsegs m (e_p0 E) (e_pl E).

(* the fake kernel, the model and the marks at operation i, as lh_mem has them *)
Definition c45_kmg (E : lenv) (i : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i /\
  model_at m (e_md E) mbs /\ model_wf mbs /\
  marks_at m (e_mk E) gbs /\ marks_wf gbs /\ marks_are gbs mbs.

(* the three machine facts every cut keeps *)
Definition c45_mach (E : lenv) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* the register file of both arms: the callee-saved words of the loop (s0, s1, s5 .. s11), sp, gp,
   tp fixed; the rest as given *)
Definition c45_R (E : lenv) (i : Z) (gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word)
  : bvmap 5 word :=
  mkR ra (wz (c45_sp E)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6.

(* where a string text_of answered lies (text_of_c.v Post): a `texts` entry in .rodata when it
   allocated nothing, else the whole of its fresh block, which lies below the stack window *)
Definition c45_loc (E : lenv) (own s : Z) (t : list byte) : Prop :=
  (own = 0 /\ A_RO_LO <= s /\ s + Z.of_nat (length t) + 1 <= A_RO_END) \/
  (own <> 0 /\ s = own /\
   exists k, 1 <= k <= 320 /\ Z.of_nat (length t) + 1 <= k /\
             4096 <= own /\ own + k <= e_S E - SLOT_STACK_Z).

(* ==========================================================================
   3. op_decide's cuts
   ========================================================================== *)

(* at the call of text_of at 0x13aa4 (pc = 0x15aa8, ra = 0x13aa8): in = sp+0x40, own = sp+0x78 *)
Definition c45_13aa4 (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte) (w2 : word),
    ms = MS (c45_R E i gp (wz C45_TO1_RA) t0 t1 t2 (wz (c45_sp E + FO_P)) (wz (c45_sp E + FO_B256))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz P_text_of) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 w2] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at its return (pc 0x13aa8): a0 = s1, the kind; own1 in the ok cell *)
Definition c45_13aa8 (E : lenv) (i : Z) (gp : word) (own1 : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N s1 : Z) (kbs mbs gbs j0 j1 j2 t1v : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 (wz s1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_TO1_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    s1 <> 0 /\ cstr_at m s1 t1v /\ c45_loc E own1 s1 t1v /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at the call of text_of at 0x13ab4 (pc = 0x15aa8, ra = 0x13ab8): in = sp+0x40, own = sp+0x50;
   s2 = s1 *)
Definition c45_13ab4 (E : lenv) (i : Z) (gp : word) (own1 : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N s1 : Z) (kbs mbs gbs j0 j1 j2 t1v : list byte) (w1 : word),
    ms = MS (c45_R E i gp (wz C45_TO2_RA) t0 t1 t2 (wz (c45_sp E + FO_P)) (wz (c45_sp E + FO_B40))
               a2 a3 a4 a5 a6 a7 (wz s1) s3 s4 t3 t4 t5 t6)
            F (wz P_text_of) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [C8 w1] /\
    rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    s1 <> 0 /\ cstr_at m s1 t1v /\ c45_loc E own1 s1 t1v /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at its return (pc 0x13ab8): a0 = s2v, the alias; s2 = s1; own2 in the oa cell *)
Definition c45_13ab8 (E : lenv) (i : Z) (gp : word) (own1 own2 : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N s1 s2v : Z) (kbs mbs gbs j0 j1 j2 t1v t2v : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 (wz s2v) a1 a2 a3 a4 a5 a6 a7 (wz s1) s3 s4 t3 t4 t5 t6)
            F (wz C45_TO2_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [C8 (wz own2)] /\
    rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    s1 <> 0 /\ cstr_at m s1 t1v /\ c45_loc E own1 s1 t1v /\
    s2v <> 0 /\ cstr_at m s2v t2v /\ c45_loc E own2 s2v t2v /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at the call of free at 0x13ae8 (pc = 0x173d4, ra = 0x13aec): a0 = own1 (from the ok cell), after
   check_verdict returned *)
Definition c45_13ae8 (E : lenv) (i : Z) (gp : word) (own1 own2 : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp (wz C45_FR1_RA) t0 t1 t2 (wz own1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [C8 (wz own2)] /\
    rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at its return (pc 0x13aec) *)
Definition c45_13aec (E : lenv) (i : Z) (gp : word) (own1 own2 : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_FR1_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [C8 (wz own2)] /\
    rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at the call of free at 0x13af0 (pc = 0x173d4, ra = 0x13af4): a0 = own2 (from the oa cell) *)
Definition c45_13af0 (E : lenv) (i : Z) (gp : word) (own1 own2 : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp (wz C45_FR2_RA) t0 t1 t2 (wz own2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [C8 (wz own2)] /\
    rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* at its return (pc 0x13af4 = C45_END_D) *)
Definition c45_13af4 (E : lenv) (i : Z) (gp : word) (own1 own2 : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_FR2_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [C8 (wz own2)] /\
    rw_cells rsegs m (c45_sp E + FO_B40 + 8) [CB 32 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [C8 (wz own1)] /\
    rw_cells rsegs m (c45_sp E + FO_B256 + 8) [CB 248 j2] /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* the end of either arm (pc = C45_END_D or C45_END_R): the memory lh_mem asks at operation i + 1,
   the buffers as plain bytes *)
Definition c45_end (E : lenv) (i : Z) (gp : word) (pc : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz pc) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] /\
    c45_kmg E (i + 1) kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* ==========================================================================
   3b. The dispatch, the arms' end and what a segment writes
   ========================================================================== *)

(* after the dispatch (0x13a1c - 0x13a64), at op_pc op: the op byte was at P; a0 = P + 1, a1 = N - 1,
   a2 = P, s2 = N; the cursor cells hold (P + 1, N - 1) *)
Definition c45_disp (E : lenv) (i : Z) (gp : word) (op : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 (wz (P + 1)) (wz (N - 1)) (wz P) a3 a4 a5 a6 a7 (wz N) s3 s4
               t3 t4 t5 t6)
            F (wz (op_pc op)) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 1 <= N /\
    c45_frame E j0 (P + 1) (N - 1) m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] /\
    c45_kmg E i kbs mbs gbs m /\ c45_keep E m /\ c45_mach E m.

(* where an arm ends: the next loop head, or the exit (LLoop ARM_OK) *)
Definition c45_fin (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  (i < 47 /\ lh_ms E (i + 1) gp ms) \/ ex_ms E gp ms.

(* the heap blocks the arms' own code writes (op_refused's model_begin writes the model block); the
   text_of blocks of op_decide are only read *)
Definition c45_hp (E : lenv) : list (Z * Z) := [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)].

(* a segment's post, a Theorem Labs lane's form: the cut, and what the segment wrote since its start memory m0 *)
Definition c45_post (E : lenv) (m0 : word -> option byte) (Q : machine_state -> Prop) (ms : machine_state)
  : Prop :=
  Q ms /\ seg_fp (e_S E) (c45_hp E) m0 (ms_mem ms).

(* ==========================================================================
   4. op_refused's cuts
   ========================================================================== *)

(* mark_quietly's two arguments and the name the second one is (fuzz_link.c:759) *)
Definition c45_mq_a0 (E : lenv) (w : Z) : Z := if Z.odd w then 0 else e_mk E.
Definition c45_mq_a1 (w : Z) : Z := if Z.testbit w 1 then A_EMPTY else 0.
Definition c45_mq_nm (w : Z) : option (list byte) := if Z.testbit w 1 then Some [] else None.

(* at the call of mark_quietly at 0x13c70 (pc = 0x15d88, ra = 0x13c74), after model_begin: kbs and mbs
   are the kernel and the model AFTER model_begin (n_sent = 0, n_req = 0) *)
Definition c45_13c70 (E : lenv) (i : Z) (gp : word) (w : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp (wz C45_MQ_RA) t0 t1 t2 (wz (c45_mq_a0 E w)) (wz (c45_mq_a1 w))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz P_mark_quietly) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= w < 256 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] /\
    c45_kmg E i kbs mbs gbs m /\ nk_n_sent kbs = 0 /\ md_n_req mbs = 0 /\
    c45_keep E m /\ c45_mach E m.

(* at its return (pc 0x13c74): a0 = rc. kbs, mbs, gbs are the call's. The model block, the frame and
   the kept regions are carried; the kernel and the marks are as mark_quietly_c.v's Post gives them:
   with a0 = NULL (w odd) rc = -EINVAL and g_nl unchanged (the marks block is not written); else the
   library's mark of the name over the call's marks and kernel *)
Definition c45_13c74 (E : lenv) (i : Z) (gp : word) (w : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 rc a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs j0 j1 j2 : list byte),
    ms = MS (c45_R E i gp ra t0 t1 t2 rc a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6)
            F (wz C45_MQ_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= w < 256 /\
    c45_frame E j0 P N m /\ c45_cur E P N /\
    rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
    rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] /\
    nlk_wf kbs /\ nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\
    nk_opened kbs <= 64 * i /\ nk_n_sent kbs = 0 /\
    model_at m (e_md E) mbs /\ model_wf mbs /\ md_n_req mbs = 0 /\
    marks_wf gbs /\ marks_are gbs mbs /\
    (Z.odd w = true ->
       rc = wz (- E_INVAL) /\ nlk_at m kbs /\ iftab_at m kbs link_tab /\ marks_at m (e_mk E) gbs) /\
    (Z.odd w = false ->
       let M := mark_lib link_tab (c45_mq_nm w) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
       rc = wz (m_rc M)
       /\ (exists gbs', marks_at m (e_mk E) gbs' /\ marks_wf gbs' /\ mk_names gbs' = m_marks M
             /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
       /\ (exists kbs', nlk_at m kbs' /\ nlk_wf kbs'
             /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
             /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m kbs' link_tab
             /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
             /\ nk_sent kbs' = m_reqs M
             /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
             /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
             /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
             /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2)) /\
    c45_keep E m /\ c45_mach E m.

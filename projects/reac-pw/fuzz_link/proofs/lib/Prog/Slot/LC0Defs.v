(* op_read (fuzz_link.c:677-700), the arm taken when the operation byte is 0 mod 6, plain image:
   the cut predicates of its five segments.

   The arm runs 0x13a68 (the jump table's entry for op 0) to 0x13f7c, and its allocator-facing calls
   cut it into five segments:

     S1  lh_ms E i gp + lh_op E ms 0       -> c0_cut_kc     (text_buf (kc) at 0x13e4c, ra 0x13e50)
     S2  c0_ret_kc (0x13e50)               -> c0_cut_ac     (text_buf (ac) at 0x13e58, ra 0x13e5c)
     S3  c0_ret_ac (0x13e5c)               -> c0_cut_fk     (free (kind) at 0x13f64, ra 0x13f68)
     S4  c0_ret_fk (0x13f68)               -> c0_cut_fa     (free (alias) at 0x13f6c, ra 0x13f70)
     S5  c0_ret_fa (0x13f70)               -> lh_ms E (i+1) gp \/ ex_ms E gp

   S3 is split inside the lane at c0_mid (0x13ed4, the return address of reac_link_alias_read).

   The head of the arm (0x13a68 - 0x13e24) is name_of + the two `% 40` bytes, inlined: it takes at
   most four bytes of the input (the operation byte, the selector, the kind cap, the alias cap) and
   stops early when the input runs out. c0_sel / c0_kc / c0_ac / c0_used read them off the input
   suffix; LDefs' sel_name / sel_ptr turn the selector into the name.

   Every address and offset is read from the plain image (the unstripped twin of the pin
   ebe34b259b9f; link/ct/dis/plain/LLVMFuzzerTestOneInput.s). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The arm's program points
   ========================================================================== *)

Definition C0_TEXT_BUF : Z := 0x14fb0.        (* text_buf *)
Definition C0_FREE : Z := 0x173d4.            (* free *)
Definition C0_RA_KC : Z := 0x13e50.           (* return of text_buf (kc) *)
Definition C0_CALL_AC : Z := 0x13e58.
Definition C0_RA_AC : Z := 0x13e5c.           (* return of text_buf (ac) *)
Definition C0_MID : Z := 0x13ed4.             (* return of reac_link_alias_read *)
Definition C0_RA_FK : Z := 0x13f68.           (* return of free (kind) *)
Definition C0_RA_FA : Z := 0x13f70.           (* return of free (alias) *)

(* ==========================================================================
   2. The head: what the arm takes off the input
   ========================================================================== *)

(* `l` is the input suffix at the cursor (its first byte is the operation byte). *)
Definition c0_b (l : list byte) (k : nat) : Z := bz (nth k l (zb 0)).

(* the selector name_of reads (0x13a6c); with no byte left the code runs the s = 0 path
   (0x13c18: a3 = 0), which is g_names[0] *)
Definition c0_sel (l : list byte) : Z := if (length l <? 2)%nat then 0 else c0_b l 1.
(* the two caps (0x13cc0 - 0x13cfc), 0 when the input ran out *)
Definition c0_kc (l : list byte) : Z := if (length l <? 3)%nat then 0 else c0_b l 2 mod 40.
Definition c0_ac (l : list byte) : Z := if (length l <? 4)%nat then 0 else c0_b l 3 mod 40.
(* the bytes the head takes: the operation byte, then one each while the input lasts *)
Definition c0_used (l : list byte) : Z := Z.min 4 (Z.of_nat (length l)).

(* ==========================================================================
   3. The frame and the facts every cut carries
   ========================================================================== *)

(* the 480-byte frame of the arm: lh_cells with the 256-byte buffer split into wk (40 bytes, the
   model's kind buffer at sp+0x78) and the 216 bytes after it that this arm never reads *)
Definition c0_cells (md mk P N : Z) (j0 wa wk j2 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (md + MD_MARK)); C8 (wz A_EMPTY); C8 (wz mk); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N); CB 40 wa; CB 40 wk; CB 216 j2].

Definition c0_frame (E : lenv) (P N : Z) (wa wk : list byte) (m : word -> option byte) : Prop :=
  exists j0 j2, rw_cells rsegs m (e_S E - SLOT_FRAME) (c0_cells (e_md E) (e_mk E) P N j0 wa wk j2).

(* a block the arm allocated: outside the image and the stack, and apart from the three blocks the
   slot carries. The glue gets it from text_buf's `fresh_block` and the frame's accounting. *)
Definition c0_blk (E : lenv) (a n : Z) : Prop :=
  blk_out (e_S E) a n /\
  apart a n (e_md E) MD_SIZE /\ apart a n (e_mk E) MK_SIZE /\
  apart a n (e_p0 E) (Z.of_nat (length (e_pl E))).

(* the memory facts the whole arm carries: lh_mem's, with the cursor at (P, N) and the kernel, model
   and marks bytes free *)
Definition c0_base (E : lenv) (P N : Z) (kbs mbs gbs : list byte) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ la_ok m /\ texts_at m /\ ifptrs_at m /\
  model_at m (e_md E) mbs /\ model_wf mbs /\
  marks_at m (e_mk E) gbs /\ marks_wf gbs /\ marks_are gbs mbs /\
  cursor_ok m (e_p0 E) (e_pl E) P N /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m /\
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME).

(* what model_begin (0x13e28 - 0x13e44) left: the model's cursor and request list are empty and its
   two errnos are the fake kernel's, so md_kstate mbs kbs = nk_kstate kbs and both request lists
   are empty: the two readers compute the same link_spec function *)
Definition c0_begun (kbs mbs : list byte) : Prop :=
  nk_next kbs = 0 /\ nk_n_sent kbs = 0 /\ md_next mbs = 0 /\ md_n_req mbs = 0 /\
  md_socket_errno mbs = nk_socket_errno kbs /\ md_send_errno mbs = nk_send_errno kbs /\
  nk_opened kbs = nk_closed kbs.

(* the result of a text_buf call: NULL for a zero cap, else a block of cap + 1 bytes of 0x5a *)
Definition c0_buf (E : lenv) (cap a : Z) (m : word -> option byte) : Prop :=
  (cap = 0 -> a = 0) /\
  (cap <> 0 -> a <> 0 /\ c0_blk E a (cap + 1) /\
     tbuf_at m a cap (repeat (zb GUARD_BYTE) (Z.to_nat cap))).

(* LDefs' `eqv_cl` is the closure of a cut under register equivalence: a segment that passes a
   `leaf` contract gets back a register map that only agrees with `mkR ...` register by register
   (lib/Lib/Regs6ss.v xregs_eqv), so that is the strongest post such a segment can have. *)
Lemma c0_eqv_intro : forall Q ms, Q ms -> eqv_cl Q ms.
Proof.
  intros Q ms H. exists ms. split; [exact H|].
  repeat split; try reflexivity; try (intros r _; reflexivity).
Qed.

(* ==========================================================================
   4. The five cuts
   ========================================================================== *)

(* S1 -> : the call of text_buf (kc) at 0x13e4c. a0 = kc, s2 = the name, s5 = ac, s6 = kc, and the
   kernel has run and model_begin after it. *)
Definition c0_cut_kc (E : lenv) (i : Z) (gp : word) (P N sel kc ac : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR (wz C0_RA_KC) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz kc) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr sel)) s3 s4 (wz ac) (wz kc) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_TEXT_BUF) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= sel < 256 /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= N /\
    nk_opened kbs <= 64 * i /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m /\ c0_begun kbs mbs.

(* -> S2 : its return, 0x13e50. a0 = the kind buffer. *)
Definition c0_ret_kc (E : lenv) (i : Z) (gp : word) (P N sel kc ac K : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz K) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr sel)) s3 s4 (wz ac) (wz kc) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_RA_KC) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= sel < 256 /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= N /\
    0 <= K < 2 ^ 64 /\ nk_opened kbs <= 64 * i /\
    c0_buf E kc K m /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m /\ c0_begun kbs mbs.

(* S2 -> : the call of text_buf (ac) at 0x13e58. a0 = ac, s3 = the kind buffer. *)
Definition c0_cut_ac (E : lenv) (i : Z) (gp : word) (P N sel kc ac K : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR (wz C0_RA_AC) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz ac) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr sel)) (wz K) s4 (wz ac) (wz kc) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_TEXT_BUF) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= sel < 256 /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= N /\
    0 <= K < 2 ^ 64 /\ nk_opened kbs <= 64 * i /\
    c0_buf E kc K m /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m /\ c0_begun kbs mbs.

(* -> S3 : its return, 0x13e5c. a0 = the alias buffer. *)
Definition c0_ret_ac (E : lenv) (i : Z) (gp : word) (P N sel kc ac K A : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz A) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr sel)) (wz K) s4 (wz ac) (wz kc) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_RA_AC) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= sel < 256 /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= N /\
    0 <= K < 2 ^ 64 /\ 0 <= A < 2 ^ 64 /\ nk_opened kbs <= 64 * i /\
    (kc <> 0 -> ac <> 0 -> apart K (kc + 1) A (ac + 1)) /\
    c0_buf E kc K m /\ c0_buf E ac A m /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m /\ c0_begun kbs mbs.

(* the lane's own split of S3: 0x13ed4, the return address of reac_link_alias_read. s7 = the model's
   answer, a0 = the library's, s9 = g_nl.opened as it was before the two readers (0x13e80), and the
   kind and alias buffers hold the texts the two readers left. *)
Definition c0_mid (E : lenv) (i : Z) (gp : word) (P N sel kc ac K A op0 want rc : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz rc) a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr sel)) (wz K) (wz A) (wz ac) (wz kc) (wz want) s8 (wz op0)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_MID) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= sel < 256 /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= N /\
    0 <= K < 2 ^ 64 /\ 0 <= A < 2 ^ 64 /\ 0 <= op0 < 2 ^ 31 /\
    nk_opened kbs <= 64 * i + 1 /\ nk_opened kbs = nk_closed kbs /\
    (kc <> 0 -> ac <> 0 -> apart K (kc + 1) A (ac + 1)) /\
    (* The two readers' answers agree. `kbs0` is the fake kernel as the two readers FOUND it
       (model_read runs first and leaves g_nl alone, so both read the same one); `kbs` is the kernel
       AFTER them, whose errnos talk cleared and whose cursor it moved, so read_core must not be read
       over it (C0Rd, 2026-10-30). It enters as the BYTES, not as a kstate, so that the three errnos
       are fld_u32 values and the answer is bounded: check_read's Pre needs rc <> 0 when the model
       answered RC_FAILS, which a kstate with an unbounded k_sock would not give (C0Chk). *)
    exists kbs0 : list byte,
    let nm := sel_name sel in
    let R := read_core link_tab nm kc ac [] (nk_kstate kbs0) in
    nlk_wf kbs0 /\ rc = r_rc R /\ want = norm_rc (r_rc R) /\
    ((nm = None \/ nm = Some [] \/ (forall s, nm = Some s -> index_of link_tab s = 0)) ->
       nk_opened kbs = op0) /\
    (* the four texts check_read compares *)
    (kc <> 0 -> cstr_at m K (r_kind R) /\
       exists bs, tbuf_at m K kc bs /\ In (zb 0) bs) /\
    (ac <> 0 -> cstr_at m A (r_alias R) /\
       exists bs, tbuf_at m A ac bs /\ In (zb 0) bs) /\
    cstr_at m (e_S E - SLOT_FRAME + FO_B256) (if kc <? 1 then [] else r_kind R) /\
    cstr_at m (e_S E - SLOT_FRAME + FO_B40) (if ac <? 1 then [] else r_alias R) /\
    (kc <> 0 -> c0_blk E K (kc + 1)) /\ (ac <> 0 -> c0_blk E A (ac + 1)) /\
    (kc = 0 -> K = 0) /\ (ac = 0 -> A = 0) /\
    requests_are kbs mbs /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m.

(* S3 -> : the call of free (kind) at 0x13f64. a0 = s3 = the kind buffer. *)
Definition c0_cut_fk (E : lenv) (i : Z) (gp : word) (P N sel kc ac K A : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR (wz C0_RA_FK) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz K) a1 a2 a3 a4 a5 a6 a7
                 s2 (wz K) (wz A) (wz 46) (wz A_JT) s7 s8 (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= N /\
    0 <= K < 2 ^ 64 /\ 0 <= A < 2 ^ 64 /\
    nk_opened kbs <= 64 * i + 1 /\ nk_opened kbs = nk_closed kbs /\
    (kc <> 0 -> ac <> 0 -> apart K (kc + 1) A (ac + 1)) /\
    (kc = 0 -> K = 0) /\ (kc <> 0 -> K <> 0 /\ c0_blk E K (kc + 1)) /\
    (ac = 0 -> A = 0) /\ (ac <> 0 -> A <> 0 /\ c0_blk E A (ac + 1)) /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m.

(* -> S4 : its return, 0x13f68. The kind block is gone. *)
Definition c0_ret_fk (E : lenv) (i : Z) (gp : word) (P N ac A : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word)
         (fc : bv 32) (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (wz A) (wz 46) (wz A_JT) s7 s8 (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_RA_FK) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= ac < 40 /\ 0 <= N /\ 0 <= A < 2 ^ 64 /\
    nk_opened kbs <= 64 * i + 1 /\ nk_opened kbs = nk_closed kbs /\
    (ac = 0 -> A = 0) /\ (ac <> 0 -> A <> 0 /\ c0_blk E A (ac + 1)) /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m.

(* S4 -> : the call of free (alias) at 0x13f6c. a0 = s4 = the alias buffer. *)
Definition c0_cut_fa (E : lenv) (i : Z) (gp : word) (P N ac A : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word)
         (fc : bv 32) (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR (wz C0_RA_FA) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz A) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (wz A) (wz 46) (wz A_JT) s7 s8 (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= ac < 40 /\ 0 <= N /\ 0 <= A < 2 ^ 64 /\
    nk_opened kbs <= 64 * i + 1 /\ nk_opened kbs = nk_closed kbs /\
    (ac = 0 -> A = 0) /\ (ac <> 0 -> A <> 0 /\ c0_blk E A (ac + 1)) /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m.

(* -> S5 : its return, 0x13f70. Both blocks are gone; the tail restores s7 and s8. *)
Definition c0_ret_fa (E : lenv) (i : Z) (gp : word) (P N : Z)
    (kbs mbs gbs : list byte) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word)
         (fc : bv 32) (m : word -> option byte) (wa wk : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 (wz 46) (wz A_JT) s7 s8 (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz C0_RA_FA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= N /\
    nk_opened kbs <= 64 * i + 1 /\ nk_opened kbs = nk_closed kbs /\
    c0_frame E P N wa wk m /\ c0_base E P N kbs mbs gbs m.

(* ==========================================================================
   5. The heap blocks the arm holds at each cut (LDefs' seg_fp `hp`)
   ========================================================================== *)

(* the two blocks of the slot itself *)
Definition c0_hp2 (E : lenv) : list (Z * Z) := [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)].
(* a text_buf result is a block only when its cap is not 0 (text_buf answers NULL for 0) *)
Definition c0_opt (cap a : Z) : list (Z * Z) := if cap =? 0 then [] else [(a, cap + 1)].

(* S1 writes under c0_hp2; S2 under c0_hpK; S3 under c0_hpKA; S4 under c0_hpA; S5 under c0_hp2 *)
Definition c0_hpK (E : lenv) (kc K : Z) : list (Z * Z) := c0_hp2 E ++ c0_opt kc K.
Definition c0_hpA (E : lenv) (ac A : Z) : list (Z * Z) := c0_hp2 E ++ c0_opt ac A.
Definition c0_hpKA (E : lenv) (kc K ac A : Z) : list (Z * Z) :=
  c0_hp2 E ++ c0_opt kc K ++ c0_opt ac A.

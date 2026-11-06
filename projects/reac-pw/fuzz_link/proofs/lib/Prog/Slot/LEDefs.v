(* The slot's ENTRY and EXIT (arm `en`, prefix LE): the cut predicates of the entry run
   0x1384c -> the two calloc calls -> the loop head 0x13a1c (or the exit 0x1413c, or the early
   return), and of the exit run 0x1413c -> free -> free -> ret.

   The cuts follow SLOT-COMMON.md "The shape of a segment walk": a cut at an allocator-facing call
   names the callee's entry pc and the return address in ra, and the next segment starts at that
   return address with the callee's Post facts.  Every segment's post also carries `munch W` and
   `wmono` against the segment's own starting memory, so that the SR glue (S-FR) can see which
   regions the segment changed.

   Addresses are read from the plain image (the unstripped twin of the pin ebe34b259b9f),
   link/ct/dis/plain/LLVMFuzzerTestOneInput.s. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The program points the entry and the exit use
   ========================================================================== *)

Definition L_CALLOC : Z := 0x1729c.      (* calloc *)
Definition L_FREE : Z := 0x173d4.        (* free *)
Definition L_MEMSET : Z := 0x1f060.      (* memset *)
Definition L_SNPRINTF : Z := 0x19d2c.    (* snprintf *)
Definition L_IF_HEAD : Z := 0x138cc.     (* the head of the 64-name loop *)
Definition L_IF_DONE : Z := 0x13928.     (* after it *)
Definition L_ODD_HEAD : Z := 0x13948.    (* the head of the odd loop *)
Definition L_ODD_DONE : Z := 0x13988.    (* after it *)
Definition L_FREE1_RA : Z := 0x14144.    (* free (marks) returns here *)
Definition L_FREE2_RA : Z := 0x1414c.    (* free (m) returns here: L_RET0 *)

Definition A_FMT_NL : Z := 0x10483.      (* "nl%d" *)
Definition FMT_NL : list Z := [110; 108; 37; 100].

(* the two scratch constants the entry builds *)
Definition GNL_OFF : Z := 0x42000.       (* s5: g_nl + 0x42000 = GNL42 *)
Definition A_ODD_END : Z := A_ODD + 0x28.

(* ==========================================================================
   2. The entry's fixed data
   ========================================================================== *)

(* the 13 registers the prologue saves and the epilogue restores *)
Record lregs : Type := LRegs {
  r_ra : word; r_s0 : word; r_s1 : word; r_s2 : word; r_s3 : word; r_s4 : word;
  r_s5 : word; r_s6 : word; r_s7 : word; r_s8 : word; r_s9 : word; r_s10 : word; r_s11 : word
}.

Definition lr_bytes (R : lregs) : list byte :=
  saved_bytes (r_ra R) (r_s0 R) (r_s1 R) (r_s2 R) (r_s3 R) (r_s4 R) (r_s5 R) (r_s6 R)
              (r_s7 R) (r_s8 R) (r_s9 R) (r_s10 R) (r_s11 R).

(* what one call of the slot gets from its caller: the stack top S, the payload pl at p0, gp, and
   the caller's callee-saved registers *)
Record lent : Type := LEnt {
  n_S : Z; n_p0 : Z; n_pl : list byte; n_gp : word; n_R : lregs
}.

Definition n_len (G : lent) : Z := Z.of_nat (length (n_pl G)).

(* The placement the frame gives: the stack window above the image, and the payload.  For size 0
   the payload pointer is the frame's `empty` (0x31b60, an image address just below g_nl) and
   there is no payload byte; for size >= 1 it is a user block of the allocator, which the frame
   puts outside the image and below the stack window (LDefs' blk_out, lenv_ok's payload clause).
   a Theorem Labs lane, 2026-10-30. *)
Definition le_place (G : lent) : Prop :=
  0x960e0 + SLOT_STACK_Z <= n_S G /\ n_S G <= 2 ^ 47 /\ n_S G mod 16 = 0 /\
  (0 < n_len G -> blk_out (n_S G) (n_p0 G) (n_len G)) /\ n_len G < 2 ^ 32.

(* the environment the loop head runs in, once the two blocks exist *)
Definition le_env (G : lent) (md mk : Z) : lenv :=
  LEnv (n_S G) md mk (n_p0 G) (n_pl G) (lr_bytes (n_R G)).

(* ==========================================================================
   3. The memory views the entry carries
   ========================================================================== *)

(* the image facts no operation changes: the two pointer tables, the policy strings, the guard *)
Definition le_img (m : word -> option byte) : Prop :=
  odd_at m /\ texts_at m /\ policy_ro m /\ guard_m m.

(* what every cut of the entry and the exit keeps *)
Definition le_base (G : lent) (m : word -> option byte) : Prop :=
  le_img m /\ la_ok m /\ bytes_at rsegs m (n_p0 G) (n_pl G) /\ wr_at rsegs m A_ERRNO 4 /\
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m.

(* the fake kernel interfaces() leaves: zeroed, then the 64-entry table.  This is exactly the
   kernel part of LDefs' lh_mem at operation 0. *)
Definition le_kern (m : word -> option byte) : Prop :=
  (exists kbs, nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
     nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = 0 /\ nk_closed kbs = 0) /\
  gnames_at m /\ ifptrs_at m.

(* a block calloc(1, n) handed out: non-zero, 16-aligned, out of the image, n zero bytes *)
Definition blk_zero (S a n : Z) (m : word -> option byte) : Prop :=
  a <> 0 /\ a mod 16 = 0 /\ blk_out S a n /\ u8arr rsegs m a (zeros n).

(* the memory the entry starts from: g_nl and g_names writable (image .bss), the rest as le_base *)
Definition le_entry_mem (G : lent) (m : word -> option byte) : Prop :=
  le_base G m /\
  (exists jk, rw_cells rsegs m A_G_NL [CB (Z.to_nat NK_SIZE) jk]) /\
  (exists jg, rw_cells rsegs m A_G_NAMES [CB (Z.to_nat G_NAMES_SIZE) jg]) /\
  stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G).

(* The 376 bytes of the frame below the saved registers, as the entry fills them.
   `fr_cells0`: after `sd a0, 0x40(sp)` at 0x13890 stored in.p (FO_P = 64).
   `fr_cells1`: after `sd a4, 8(sp)` at 0x13940 stored &odd[0] too (FO_ODD = 8).
   The loop head's `lh_cells` refines `fr_cells1` further; nothing between 0x13940 and 0x139f4
   writes the frame. *)
Definition fr_cells0 (p : Z) (j0 j1 : list byte) : list cell :=
  [CB 64 j0; C8 (wz p); CB 304 j1].
Definition fr_cells1 (p : Z) (j0 j1 j2 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); CB 48 j1; C8 (wz p); CB 304 j2].

Definition le_frame (G : lent) (m : word -> option byte) : Prop :=
  (exists j0 j1 j2, rw_cells rsegs m (n_S G - SLOT_FRAME) (fr_cells1 (n_p0 G) j0 j1 j2)) /\
  bytes_at rsegs m (n_S G - 104) (lr_bytes (n_R G)) /\
  wr_at rsegs m (n_S G - 104) 104.

(* ==========================================================================
   4. The cuts of the entry run
   ========================================================================== *)

(* (E0 end) the call calloc (1, 8856) at 0x13994: pc = calloc, ra = 0x13998.
   s0 = g_names + 512, s1 = 0x2000, s2 = the input size, s3 = g_nl, s4 = 63, s5 = 0x42000,
   s6 = 66, s7 = 15, s8 = 0x42, s9 = g_nl + 0x42000; s10, s11 are the caller's. *)
Definition le_cut1 (G : lent) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
    ms = MS (mkR (wz L_CALLOC1_RA) (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
                 (wz (A_G_NAMES + G_NAMES_SIZE)) (wz 0x2000) (wz 1) (wz MD_SIZE) a2 a3 a4 a5 a6 a7
                 (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42) (wz GNL42)
                 (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
            F (wz L_CALLOC) fc None m (seg_rom rsegs) /\
    frm0 fc /\ n_len G < 2 ^ 26 /\
    le_base G m /\ le_kern m /\ le_frame G m /\
    stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

(* (E1 start) 0x13998, calloc's answer md in a0 *)
Definition le_cut1r (G : lent) (md : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
    ms = MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
                 (wz (A_G_NAMES + G_NAMES_SIZE)) (wz 0x2000) (wz md) a1 a2 a3 a4 a5 a6 a7
                 (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42) (wz GNL42)
                 (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
            F (wz L_CALLOC1_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ n_len G < 2 ^ 26 /\
    le_base G m /\ le_kern m /\ le_frame G m /\ blk_zero (n_S G) md MD_SIZE m /\
    stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

(* (E1 end) the call calloc (1, 516) at 0x139a4: pc = calloc, ra = 0x139a8, s0 = md *)
Definition le_cut2 (G : lent) (md : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
    ms = MS (mkR (wz L_CALLOC2_RA) (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
                 (wz md) (wz 0x2000) (wz 1) (wz MK_SIZE) a2 a3 a4 a5 a6 a7
                 (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42) (wz GNL42)
                 (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
            F (wz L_CALLOC) fc None m (seg_rom rsegs) /\
    frm0 fc /\ n_len G < 2 ^ 26 /\
    le_base G m /\ le_kern m /\ le_frame G m /\ blk_zero (n_S G) md MD_SIZE m /\
    stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

(* (E2 start) 0x139a8, calloc's answer mk in a0, md in s0 *)
Definition le_cut2r (G : lent) (md mk : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
    ms = MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
                 (wz md) (wz 0x2000) (wz mk) a1 a2 a3 a4 a5 a6 a7
                 (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42) (wz GNL42)
                 (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
            F (wz L_CALLOC2_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ n_len G < 2 ^ 26 /\
    le_base G m /\ le_kern m /\ le_frame G m /\
    blk_zero (n_S G) md MD_SIZE m /\ blk_zero (n_S G) mk MK_SIZE m /\
    stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

(* ==========================================================================
   5. The cuts of the exit run
   ========================================================================== *)

(* what the three exit segments keep: the frame, the saved bytes, errno, the guard, and the NUL of
   msg_build's long_alias (the slot's GI carries it across driver calls) *)
Definition le_tail_mem (S : Z) (R : lregs) (m : word -> option byte) : Prop :=
  (exists j, rw_cells rsegs m (S - SLOT_FRAME) [CB 376 j]) /\
  bytes_at rsegs m (S - 104) (lr_bytes R) /\ wr_at rsegs m (S - 104) 104 /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m /\ la_ok m /\
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m (S - SLOT_STACK_Z) (S - SLOT_FRAME).

(* the call free (marks) at 0x14140: pc = free, ra = 0x14144, a0 = mk, s0 = md *)
Definition le_free1 (S : Z) (gp : word) (R : lregs) (md mk : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms = MS (mkR (wz L_FREE1_RA) (wz (S - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz md) s1
                 (wz mk) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz L_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ le_tail_mem S R m.

(* 0x14144, free (marks) has returned *)
Definition le_free1r (S : Z) (gp : word) (R : lregs) (md : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms = MS (mkR ra (wz (S - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz md) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz L_FREE1_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ le_tail_mem S R m.

(* the call free (m) at 0x14148: pc = free, ra = 0x1414c, a0 = md *)
Definition le_free2 (S : Z) (gp : word) (R : lregs) (md : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms = MS (mkR (wz L_FREE2_RA) (wz (S - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 s0 s1
                 (wz md) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz L_FREE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ le_tail_mem S R m.

(* 0x1414c: the epilogue, reached from free (m) and from the early return *)
Definition le_free2r (S : Z) (gp : word) (R : lregs) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms = MS (mkR ra (wz (S - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 s0 s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz L_FREE2_RA) fc None m (seg_rom rsegs) /\
    frm0 fc /\ le_tail_mem S R m.

(* the state after the slot's `ret`: a0 = 0, sp = S, every callee-saved register restored *)
Definition le_fin (S : Z) (gp : word) (R : lregs) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
    ms = MS (mkR (r_ra R) (wz S) gp (wz A_TP) t0 t1 t2 (r_s0 R) (r_s1 R)
                 (wz 0) a1 a2 a3 a4 a5 a6 a7 (r_s2 R) (r_s3 R) (r_s4 R) (r_s5 R) (r_s6 R)
                 (r_s7 R) (r_s8 R) (r_s9 R) (r_s10 R) (r_s11 R) t3 t4 t5 t6)
            F (ret_pc (r_ra R)) fc None m (seg_rom rsegs) /\
    frm0 fc /\ wr_at rsegs m A_ERRNO 4 /\ guard_m m /\ la_ok m /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ stk rsegs m (S - SLOT_STACK_Z) S.

(* ==========================================================================
   6. The write windows of the segments (witnesses for LDefs' seg_fp)
   ========================================================================== *)

(* E0 writes the stack window (its frame and snprintf's), the fake kernel and the names *)
Definition le_W0 (G : lent) : list ivl :=
  [(n_S G - SLOT_STACK_Z, n_S G); (A_G_NL, A_G_NL + NK_SIZE);
   (A_G_NAMES, A_G_NAMES + G_NAMES_SIZE)].

(* E2 and the exit segments write only inside the stack window *)
Definition le_W2 (G : lent) : list ivl := [(n_S G - SLOT_STACK_Z, n_S G)].

Lemma seg_fp_W0 : forall (G : lent) (m m' : word -> option byte),
  munch (le_W0 G) m m' -> wmono rsegs m m' -> seg_fp (n_S G) [] m m'.
Proof.
  intros G m m' MU WM. exists (le_W0 G). split; [exact MU|]. split; [exact WM|].
  intros x Hx Ho. unfold le_W0, own_w in *. cbn [outside] in Ho.
  destruct (Z.le_gt_cases (n_S G - SLOT_STACK_Z) x) as [H1|H1];
    [ destruct (Z.lt_ge_cases x (n_S G)) as [H2|H2]; [left; lia|] | ];
  (destruct (Z.le_gt_cases A_G_NL x) as [H3|H3];
    [ destruct (Z.lt_ge_cases x (A_G_NL + NK_SIZE)) as [H4|H4]; [right; left; lia|] | ]);
  (destruct (Z.le_gt_cases A_G_NAMES x) as [H5|H5];
    [ destruct (Z.lt_ge_cases x (A_G_NAMES + G_NAMES_SIZE)) as [H6|H6];
        [right; right; left; lia|] | ]);
  exfalso; apply Ho; repeat split; lia.
Qed.

Lemma seg_fp_W2 : forall (G : lent) (m m' : word -> option byte),
  munch (le_W2 G) m m' -> wmono rsegs m m' -> seg_fp (n_S G) [] m m'.
Proof.
  intros G m m' MU WM. exists (le_W2 G). split; [exact MU|]. split; [exact WM|].
  intros x Hx Ho. unfold le_W2, own_w in *. cbn [outside] in Ho.
  destruct (Z.le_gt_cases (n_S G - SLOT_STACK_Z) x) as [H1|H1];
    [ destruct (Z.lt_ge_cases x (n_S G)) as [H2|H2]; [left; lia|] | ];
  exfalso; apply Ho; repeat split; lia.
Qed.

Lemma seg_fp_nil : forall (S : Z) (hp : list (Z * Z)) (m : word -> option byte), seg_fp S hp m m.
Proof.
  intros S hp m. exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
  intros x Hx Ho. exfalso. apply Ho. exact I.
Qed.

(* the exit segments run with the two blocks still held, then with none *)
Lemma seg_fp_stk : forall (S : Z) (hp : list (Z * Z)) (m m' : word -> option byte),
  munch [(S - SLOT_STACK_Z, S)] m m' -> wmono rsegs m m' -> seg_fp S hp m m'.
Proof.
  intros S hp m m' MU WM. exists [(S - SLOT_STACK_Z, S)]. split; [exact MU|]. split; [exact WM|].
  intros x Hx Ho. unfold own_w. cbn [outside] in Ho.
  destruct (Z.le_gt_cases (S - SLOT_STACK_Z) x) as [H1|H1];
    [ destruct (Z.lt_ge_cases x S) as [H2|H2]; [left; lia|] | ];
  exfalso; apply Ho; repeat split; lia.
Qed.

(* ==========================================================================
   7. The interface loop: how many names are in the table after k of the 64
   ========================================================================== *)

(* interfaces() skips k with k % 16 = 15 (fuzz_link.c:94).  `kept k` is the list of the k' < k it
   keeps, in order: the names the table holds after the loop has done k of its 64 rounds. *)
Definition keep (k : nat) : bool := negb (Nat.eqb (Nat.modulo k 16) 15).

Fixpoint kept (k : nat) : list nat :=
  match k with O => [] | S k' => kept k' ++ (if keep k' then [k'] else []) end.

Lemma kept_S : forall k, kept (S k) = kept k ++ (if keep k then [k] else []).
Proof. reflexivity. Qed.

(* the loop's whole run: the 60 names the interface table keeps, as link_ptrs names them *)
Lemma kept_64 : kept 64 = filter (fun k => negb (Nat.eqb (Nat.modulo k 16) 15)) (seq 0 64).
Proof. vm_compute. reflexivity. Qed.

Lemma kept_64_length : length (kept 64) = 60%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma kept_lt : forall k j, In j (kept k) -> (j < k)%nat.
Proof.
  induction k as [|k IH]; intros j H; [destruct H|].
  rewrite kept_S in H. apply in_app_or in H. destruct H as [H|H].
  - specialize (IH j H). lia.
  - destruct (keep k); cbn in H; [destruct H as [->|[]]; lia | destruct H].
Qed.

Lemma kept_le : forall k, (length (kept k) <= k)%nat.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite kept_S, app_length. destruct (keep k); cbn [length]; lia.
Qed.

(* ==========================================================================
   8. Reading a field out of a byte view of a block
   ========================================================================== *)

Lemma bytes_at_det : forall m A bs bs',
  bytes_at rsegs m A bs -> bytes_at rsegs m A bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m A bs bs' (_ & _ & H) (_ & _ & H') HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi).
    rewrite (proj2 (nth_error_None bs' i) ltac:(lia)). reflexivity.
Qed.

Lemma bytes_at_split : forall m A bs k,
  bytes_at rsegs m A bs ->
  bytes_at rsegs m A (firstn k bs) /\
  bytes_at rsegs m (A + Z.of_nat (length (firstn k bs))) (skipn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact H.
Qed.

Lemma slice_of_bytes : forall m A bs off n pay,
  bytes_at rsegs m A bs -> bytes_at rsegs m (A + off) pay ->
  0 <= off -> Z.of_nat (length pay) = n -> off + n <= Z.of_nat (length bs) ->
  slice bs off n = pay.
Proof.
  intros m A bs off n pay HB HP Hoff HL Hn.
  assert (HS : bytes_at rsegs m (A + off) (slice bs off n)).
  { destruct (bytes_at_split m A bs (Z.to_nat off) HB) as [_ HB1].
    rewrite firstn_length in HB1.
    replace (Nat.min (Z.to_nat off) (length bs)) with (Z.to_nat off) in HB1 by lia.
    replace (A + Z.of_nat (Z.to_nat off)) with (A + off) in HB1 by lia.
    destruct (bytes_at_split m (A + off) (skipn (Z.to_nat off) bs) (Z.to_nat n) HB1) as [HB2 _].
    exact HB2. }
  symmetry. eapply bytes_at_det; [exact HP | exact HS |].
  unfold slice. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma fld_u32_of_mem : forall m A bs off v,
  bytes_at rsegs m A bs -> bytes_at rsegs m (A + off) (le4 (wz v)) ->
  0 <= off -> off + 4 <= Z.of_nat (length bs) -> 0 <= v < 2 ^ 32 ->
  fld_u32 bs off = v.
Proof.
  intros m A bs off v HB HP Hoff Hn Hv.
  unfold fld_u32, rdn.
  rewrite (slice_of_bytes m A bs off 4 (le4 (wz v)) HB HP Hoff
             ltac:(rewrite length_le4; reflexivity) Hn).
  rewrite bytes_le_to_Z_le4. unfold wz. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma fld_u64_of_mem : forall m A bs off v,
  bytes_at rsegs m A bs -> bytes_at rsegs m (A + off) (le8 (wz v)) ->
  0 <= off -> off + 8 <= Z.of_nat (length bs) -> 0 <= v < 2 ^ 64 ->
  fld_u64 bs off = v.
Proof.
  intros m A bs off v HB HP Hoff Hn Hv.
  unfold fld_u64, rdn.
  rewrite (slice_of_bytes m A bs off 8 (le8 (wz v)) HB HP Hoff
             ltac:(rewrite length_le8; reflexivity) Hn).
  unfold le8, word_to_le_bytes.
  rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
  unfold wz. rewrite unsigned_lit by lia. change (8 * Z.of_nat 8) with 64. apply Z.mod_small. lia.
Qed.

(* ==========================================================================
   9. A block of zeros reads as zero in every field
   ========================================================================== *)

Lemma zeros_length : forall n, 0 <= n -> Z.of_nat (length (zeros n)) = n.
Proof. intros n Hn. unfold zeros. rewrite repeat_length. lia. Qed.

Lemma skipn_rep : forall {A : Type} (x : A) k n, skipn k (repeat x n) = repeat x (n - k)%nat.
Proof.
  intros A x k. induction k as [|k IH]; intros n.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [repeat skipn Nat.sub]. apply IH.
Qed.

Lemma firstn_rep : forall {A : Type} (x : A) k n, firstn k (repeat x n) = repeat x (Nat.min k n).
Proof.
  intros A x k. induction k as [|k IH]; intros n; [reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [repeat firstn Nat.min]. f_equal. apply IH.
Qed.

Lemma slice_zeros : forall n off k, 0 <= off -> 0 <= k -> off + k <= n ->
  slice (zeros n) off k = zeros k.
Proof.
  intros n off k Hoff Hk Hn. unfold slice, zeros.
  rewrite skipn_rep, firstn_rep. f_equal. lia.
Qed.

Lemma bytes_le_to_Z_zeros : forall k, bytes_le_to_Z (zeros k) = 0.
Proof.
  intros k. unfold zeros. remember (Z.to_nat k) as n. clear Heqn k.
  induction n as [|n IH]; cbn [repeat bytes_le_to_Z]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma fld_u32_zeros : forall n off, 0 <= off -> off + 4 <= n -> fld_u32 (zeros n) off = 0.
Proof.
  intros n off Ho Hn. unfold fld_u32, rdn.
  rewrite (slice_zeros n off 4) by lia. apply bytes_le_to_Z_zeros.
Qed.

Lemma fld_u64_zeros : forall n off, 0 <= off -> off + 8 <= n -> fld_u64 (zeros n) off = 0.
Proof.
  intros n off Ho Hn. unfold fld_u64, rdn.
  rewrite (slice_zeros n off 8) by lia. apply bytes_le_to_Z_zeros.
Qed.

(* the model block calloc hands out is well formed and holds no mark and no request *)
Lemma model_wf_zeros : model_wf (zeros MD_SIZE).
Proof.
  unfold model_wf, model_marks_wf, md_n_req, md_next, md_socket_errno, md_send_errno, md_n_mark.
  rewrite !(fld_u32_zeros MD_SIZE) by (unfold MD_SIZE, MD_N_REQ, MD_NEXT, MD_SOCKET_ERRNO,
                                       MD_SEND_ERRNO, MD_N_MARK; lia).
  split; [unfold NL_SENT_MAX; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros i Hi; lia|].
  split; [unfold MARKS_MAX; lia|]. unfold slots_terminated. intros i Hi. lia.
Qed.

Lemma marks_wf_zeros : marks_wf (zeros MK_SIZE).
Proof.
  unfold marks_wf, mk_n. rewrite (fld_u32_zeros MK_SIZE) by (unfold MK_SIZE, MK_N; lia).
  split; [unfold MARKS_MAX; lia|]. unfold slots_terminated. intros i Hi. lia.
Qed.

Lemma marks_are_zeros : marks_are (zeros MK_SIZE) (zeros MD_SIZE).
Proof.
  unfold marks_are, mk_n, md_n_mark, mk_names, md_marks.
  rewrite (fld_u32_zeros MK_SIZE) by (unfold MK_SIZE, MK_N; lia).
  rewrite (fld_u32_zeros MD_SIZE) by (unfold MD_SIZE, MD_N_MARK; lia).
  split; reflexivity.
Qed.

(* ==========================================================================
   10. The read-only strings the entry needs
   ========================================================================== *)

Lemma ro_cstr : forall m a s,
  mem_inv rsegs m -> ro_bytes_b rsegs a (s ++ [zb 0]) = true ->
  0 <= a -> a + Z.of_nat (length (s ++ [zb 0])) <= 2 ^ 64 -> ~ In (zb 0) s ->
  cstr_at m a s.
Proof.
  intros m a s MI HB Ha Hl Hn. split; [|exact Hn].
  apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact HB.
Qed.

(* ==========================================================================
   11. The two loops of interfaces()
   ========================================================================== *)

(* one row of the interface table: the name pointer and the index *)
Definition le_ifrow (m : word -> option byte) (i : nat) (p ix : Z) : Prop :=
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\
  u32_at m (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) ix.

(* the table holds exactly the rows ps / ixs *)
Definition le_tabl (m : word -> option byte) (ps ixs : list Z) : Prop :=
  length ps = length ixs /\
  u32_at m (A_G_NL + NK_N_IF) (Z.of_nat (length ps)) /\
  forall i, (i < length ps)%nat -> le_ifrow m i (nth i ps 0) (nth i ixs 0).

(* the ten counters memset left at zero and no later instruction of the entry writes *)
Definition le_zfields (m : word -> option byte) : Prop :=
  u32_at m (A_G_NL + NK_N_CHUNKS) 0 /\ u32_at m (A_G_NL + NK_NEXT) 0 /\
  u32_at m (A_G_NL + NK_END_ERRNO) 0 /\ u32_at m (A_G_NL + NK_SOCKET_ERRNO) 0 /\
  u32_at m (A_G_NL + NK_SEND_ERRNO) 0 /\ u32_at m (A_G_NL + NK_OPEN) 0 /\
  u32_at m (A_G_NL + NK_OPENED) 0 /\ u32_at m (A_G_NL + NK_CLOSED) 0 /\
  u32_at m (A_G_NL + NK_MISUSE) 0 /\ u32_at m (A_G_NL + NK_N_SENT) 0.

(* the fake kernel block as the loops keep it: 271992 readable bytes, all of them writable, the
   counters still zero, and the table as far as it is built.  The byte list is left existential:
   every field the walk needs is read from memory with fld_u32_of_mem / fld_u64_of_mem. *)
Definition le_nlk (m : word -> option byte) (ps ixs : list Z) : Prop :=
  (exists kb, Z.of_nat (length kb) = NK_SIZE /\ bytes_at rsegs m A_G_NL kb) /\
  wr_at rsegs m A_G_NL NK_SIZE /\ le_zfields m /\ le_tabl m ps ixs.

(* g_names after k of the 64 rounds: the first k slots hold their name, the rest are writable *)
Definition le_gnames (m : word -> option byte) (k : nat) : Prop :=
  (forall j, (j < k)%nat -> exists rest,
     bytes_at rsegs m (A_G_NAMES + 8 * Z.of_nat j) (gname (Z.of_nat j) ++ zb 0 :: rest) /\
     length (gname (Z.of_nat j) ++ zb 0 :: rest) = 8%nat) /\
  (exists jg, rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k)
                [CB (Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat k)) jg]).

(* the rows the first loop has written after k rounds *)
Definition g_ps (k : nat) : list Z := map (fun j => A_G_NAMES + 8 * Z.of_nat j) (kept k).
Definition g_ixs (k : nat) : list Z := map (fun j => Z.of_nat j + 2) (kept k).

(* the four rows the odd loop adds *)
Definition o_ps : list Z := [0x1039c; 0x1056a; 0x103bc; 0x10598].
Definition o_ixs : list Z := [101; 102; 103; 104].

Lemma link_ptrs_eq : link_ptrs = g_ps 64 ++ o_ps.
Proof. unfold link_ptrs, g_ps, o_ps. rewrite kept_64. reflexivity. Qed.

(* what the entry's own code keeps while interfaces() runs: the image facts, the payload, the
   frame and the stack, plus the two tables being built *)
Definition le_if_mem (G : lent) (k : nat) (ps ixs : list Z) (m : word -> option byte) : Prop :=
  le_base G m /\ le_nlk m ps ixs /\ le_gnames m k /\
  (exists j0 j1 j2, rw_cells rsegs m (n_S G - SLOT_FRAME) (fr_cells1 (n_p0 G) j0 j1 j2)) /\
  bytes_at rsegs m (n_S G - 104) (lr_bytes (n_R G)) /\
  wr_at rsegs m (n_S G - 104) 104 /\
  stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

(* the same, before the odd loop has stored &odd[0] into the frame cell at +8 *)
Definition le_if_mem0 (G : lent) (k : nat) (ps ixs : list Z) (m : word -> option byte) : Prop :=
  le_base G m /\ le_nlk m ps ixs /\ le_gnames m k /\
  (exists j0 j1, rw_cells rsegs m (n_S G - SLOT_FRAME) (fr_cells0 (n_p0 G) j0 j1)) /\
  bytes_at rsegs m (n_S G - 104) (lr_bytes (n_R G)) /\
  wr_at rsegs m (n_S G - 104) 104 /\
  stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

(* ==========================================================================
   12. The decimal the name loop prints
   ========================================================================== *)

Lemma pf_dec_small : forall k, 0 <= k < 100 -> pf_dec k = dec2 k.
Proof.
  intros k Hk. unfold pf_dec, dec2.
  rewrite (proj2 (Z.ltb_ge k 0) ltac:(lia)).
  destruct (Z.ltb_spec k 10) as [H|H].
  - cbn [pf_digits]. rewrite (proj2 (Z.ltb_lt k 10) H). reflexivity.
  - cbn [pf_digits]. rewrite (proj2 (Z.ltb_ge k 10) ltac:(lia)).
    assert (Hd : k / 10 < 10) by (Z.div_mod_to_equations; lia).
    assert (Hd0 : 0 <= k / 10) by (apply Z.div_pos; lia).
    cbn [pf_digits]. rewrite (proj2 (Z.ltb_lt (k / 10) 10) Hd). reflexivity.
Qed.

Lemma gname_of_text : forall k, 0 <= k < 100 ->
  pf_text [PLit 110; PLit 108; Pd] [AInt k] = Some (gname_z k).
Proof.
  intros k Hk. cbn [pf_text option_map]. rewrite pf_dec_small by lia.
  rewrite app_nil_r. unfold gname_z. reflexivity.
Qed.

Lemma gname_length : forall k, 0 <= k < 100 -> (length (gname k) <= 4)%nat.
Proof.
  intros k Hk. unfold gname, gname_z, dec2. rewrite map_length.
  destruct (Z.ltb_spec k 10); cbn [length]; lia.
Qed.

Lemma gname_bytes : forall k, pf_bytes (gname_z k) = gname k.
Proof. reflexivity. Qed.

(* ==========================================================================
   13. Where the payload is, and how every segment carries it
   ========================================================================== *)

(* The four loaded segments of the plain image are [0x10000, 0x97000) with no gap, so a block the
   allocator placed outside them lies wholly below or wholly above the image.  (LC3Lib's
   `c3_img_free` is the same fact in the c3 arm; a Theorem Labs lane may fold the two into LDefs.) *)
Lemma le_img_free : forall a n, pf_img_free a n -> 1 <= n -> a + n <= 0x10000 \/ 0x97000 <= a.
Proof.
  intros a n H Hn.
  destruct (Z_le_dec (a + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_dec 0x97000 a) as [R|R]; [right; exact R|].
  exfalso.
  assert (HL : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)
               = [(65536, 8192); (73728, 57344); (131072, 4096); (135168, 483328)])
    by (vm_compute; reflexivity).
  unfold pf_img_free in H.
  remember (segments_reserved rsegs) as l eqn:El. clear El.
  destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn [map] in HL; try discriminate HL.
  injection HL as E1 F1 E2 F2 E3 F3 E4 F4.
  set (y := Z.max a 0x10000).
  assert (Hy : 0 <= y - a < n) by lia.
  replace (a + (y - a)) with y in H by lia.
  destruct (Z_lt_dec y 0x12000) as [Y1|Y1]; [apply (H (y - a) Hy s1); [left; reflexivity | lia]|].
  destruct (Z_lt_dec y 0x20000) as [Y2|Y2]; [apply (H (y - a) Hy s2); [right; left; reflexivity | lia]|].
  destruct (Z_lt_dec y 0x21000) as [Y3|Y3];
    [apply (H (y - a) Hy s3); [right; right; left; reflexivity | lia]|].
  apply (H (y - a) Hy s4); [right; right; right; left; reflexivity | lia].
Qed.

(* the three places the payload can be: empty, below the image, or above it and below the stack *)
Lemma le_pay_cases : forall (G : lent), le_place G ->
  n_pl G = [] \/
  (1 <= n_len G /\ 4096 <= n_p0 G /\ n_p0 G + n_len G <= n_S G - SLOT_STACK_Z /\
   (n_p0 G + n_len G <= 0x10000 \/ 0x97000 <= n_p0 G)).
Proof.
  intros G (_ & _ & _ & HD & _).
  destruct (n_pl G) as [|b l] eqn:EP; [left; reflexivity|].
  assert (HN : 1 <= n_len G) by (unfold n_len; rewrite EP; cbn [length]; lia).
  right. destruct (HD ltac:(lia)) as (HB1 & HB2 & HB3).
  split; [exact HN|]. split; [exact HB1|]. split; [exact HB2|].
  exact (le_img_free (n_p0 G) (n_len G) HB3 HN).
Qed.

(* a segment that writes only inside the image or inside the stack window keeps the payload *)
Lemma pay_keep : forall (G : lent) (W : list ivl) (m m' : word -> option byte),
  le_place G -> bytes_at rsegs m (n_p0 G) (n_pl G) -> munch W m m' ->
  (forall x, 0 <= x < 0x10000 -> outside W x) ->
  (forall x, 0x97000 <= x < n_S G - SLOT_STACK_Z -> outside W x) ->
  bytes_at rsegs m' (n_p0 G) (n_pl G).
Proof.
  intros G W m m' PL PAY MU OLO OHI.
  destruct (le_pay_cases G PL) as [HE | (HN & HB1 & HB2 & HB3)].
  - rewrite HE in PAY |- *. destruct PAY as (H1 & H2 & _).
    split; [exact H1|]. split; [exact H2|]. intros i Hi. cbn in Hi. lia.
  - destruct PAY as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    intros i Hi. rewrite <- (H3 i Hi). unfold mrd.
    assert (HO : outside W (bv_unsigned (wa (n_p0 G + Z.of_nat i)))).
    { unfold wa. rewrite unsigned_lit by lia.
      unfold n_len in *. destruct HB3 as [HB|HB]; [apply OLO | apply OHI]; lia. }
    rewrite (MU (wa (n_p0 G + Z.of_nat i)) HO). reflexivity.
Qed.

(* the same for one store: into the image, or into the stack window *)
Lemma pay_keep_w : forall (G : lent) (m : word -> option byte) (a : Z) (bs : list byte),
  le_place G -> bytes_at rsegs m (n_p0 G) (n_pl G) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ((0x10000 <= a /\ a + Z.of_nat (length bs) <= 0x960e0) \/ n_S G - SLOT_STACK_Z <= a) ->
  bytes_at rsegs (write_to_mem m (wa a) bs) (n_p0 G) (n_pl G).
Proof.
  intros G m a bs PL PAY Ha Hb Hw.
  pose proof PL as PL2. destruct PL2 as (HS1 & _). unfold SLOT_STACK_Z in HS1, Hw |- *.
  apply (pay_keep G [(a, a + Z.of_nat (length bs))] m); try assumption.
  - intros y Hy. cbn [outside] in Hy. destruct Hy as [Hy _].
    rewrite (write_to_mem_spec bs m a y Ha Hb).
    destruct ((a <=? bv_unsigned y) && (bv_unsigned y <? a + Z.of_nat (length bs)))%bool eqn:E;
      [exfalso | reflexivity].
    apply andb_prop in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Hy. lia.
  - intros x Hx. cbn [outside]. split; [|exact I].
    destruct Hw as [[HA HB]|HA]; lia.
  - intros x Hx. unfold SLOT_STACK_Z in Hx. cbn [outside]. split; [|exact I].
    destruct Hw as [[HA HB]|HA]; lia.
Qed.

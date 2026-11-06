(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c): satisfiability of the cut predicates of LLVMFuzzerTestOneInput
    (Prog/seg_cuts.v: P_K138a4, P_K138e8 at f = 0 and f = 1, P_K13984, P_K13ad8, P_K13ae0, P_K13cac, P_K13f40) and
    the entry facts of the HEAD cuts of reac_segconf_parse_file (Prog/reac_segconf_parse_file_pieces_c.v: H_HEAD) and
    of m_file (Prog/m_file_c.v: H_MF_HEAD), of commit aca5136e2baf. One closed lemma each, at the
    real run of the input INP2 (Prog/SegSatKit234.v).

    proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Nothing here is an
    Axiom, a Parameter, an admit or an Admitted.

    The cuts' ghosts: inp = INP2 (140 bytes), p = INPA (the input block, holding them), Sp = S_TOP (main's entry sp);
    c = C0, m = M0, the text blocks TX1A (turn 0) and TX2A (turn 1), tab = TAB0, mt = MT0. main's frame cells
    (seg_cuts.celz, at Sp - 208 + off) hold the values the stores of seg_cuts.v's comment put there; the registers
    the cut names hold its map (seg_cuts.v), every other register 0. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SegSatKit SegSatKit234 SegSat234.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import
  refuse_c reac_segconf_parse_file_c reac_segconf_parse_file_pieces_c m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_cuts.
Import ListNotations.
Open Scope Z_scope.

(** A conjunct of a cut predicate: its registers by computation, the rest by sat2. *)
Ltac csat :=
  lazymatch goal with
  | |- _ /\ _ => split; csat
  | |- seg_cuts.rgz _ _ _ => unfold seg_cuts.rgz; apply bv_eq; vm_compute; reflexivity
  | |- seg_cuts.celz _ _ _ _ => unfold seg_cuts.celz; csat
  | |- seg_cuts.P_mcore _ _ _ _ _ _ _ => unfold seg_cuts.P_mcore; csat
  | |- seg_cuts.P_lcore _ _ _ _ _ _ _ => unfold seg_cuts.P_lcore; csat
  | |- _ => sat2 rsegs_below
  end.

(** ** The cut predicates *)

(** main's frame at the loop: 8 flags (1), 0x10 the cap byte (4), 0x18 cap (4), 0x20 m + 0x10, 0x28 the label
    format, 0x30 c. At K138a4 only the flags cell is stored yet. *)
Definition FRM_A : list Z := zrep 8 ++ le8z 1.
Definition FRM_L : list Z :=
  zrep 8 ++ le8z 1 ++ le8z 4 ++ le8z 4 ++ le8z (M0 + 0x10) ++ le8z seg_cuts.LABEL_FMT ++ le8z C0.
(** After the loop 0x18 still holds cap (seg_cuts.P_K13ae0); at K13cac the cells P_mcore names. *)
Definition R_INP : region := (INPA, inp_img).

(** K138a4 (0x138a4): calloc(1, 9236) has returned m; c = malloc(16616) not yet initialised (zeros here), m all
    zero; the cursor past the three header bytes. *)
Definition REGS_A : bvmap 5 word :=
  rmap [(2, SP_MAIN); (10, M0); (24, C0); (9, 4); (18, 2); (19, seg_cur_at INP2 INPA 0); (21, seg_cur_n INP2 0);
        (26, MC_N)].
Definition RS_A : list region := [(SP_MAIN, FRM_A); (C0, zrep 16616); (M0, zrep 9236); R_INP; R_STACK].
Lemma P_K138a4_sat : seg_cuts.P_K138a4 INP2 INPA S_TOP C0 M0 REGS_A (RMEM RS_A).
Proof. unfold seg_cuts.P_K138a4. csat. Qed.

(** K138e8 (0x138e8), the file-loop head at turn f: c, m hold seg_run INP2 f, s4 its returned. *)
Definition REGS_E (f : nat) : bvmap 5 word :=
  rmap [(2, SP_MAIN); (8, M0); (26, M0 + MC_N); (18, 2); (27, Z.of_nat f); (19, seg_cur_at INP2 INPA f);
        (21, seg_cur_n INP2 f); (20, b2z (seg_ret (seg_run INP2 f)))].
Definition RS_E (f : nat) : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (seg_run INP2 f))); (M0, mblk_img false (seg_mc (seg_run INP2 f)));
   R_INP; R_STACK].
Lemma P_K138e8_sat_0 : seg_cuts.P_K138e8 INP2 INPA S_TOP 0 C0 M0 (REGS_E 0) (RMEM (RS_E 0)).
Proof. unfold seg_cuts.P_K138e8. csat. Qed.
Lemma P_K138e8_sat_1 : seg_cuts.P_K138e8 INP2 INPA S_TOP 1 C0 M0 (REGS_E 1) (RMEM (RS_E 1)).
Proof. unfold seg_cuts.P_K138e8. csat. Qed.

(** K13984 (0x13984), malloc(n + 1) of turn f has returned the text block t (bytes not yet copied). *)
Definition TXA (f : nat) : Z := if (f =? 0)%nat then TX1A else TX2A.
Definition REGS_T (f : nat) : bvmap 5 word :=
  rmap [(2, SP_MAIN); (8, M0); (26, M0 + MC_N); (18, 2); (27, Z.of_nat f); (20, b2z (seg_ret (seg_run INP2 f)));
        (10, TXA f); (25, seg_txt_n INP2 f); (22, seg_turn_np INP2 f); (19, seg_turn_at INP2 INPA f);
        (21, Z.of_nat (length (seg_turn_tail INP2 f))); (24, seg_lb INP2 f)].
Definition RS_T (f : nat) : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (seg_run INP2 f))); (M0, mblk_img false (seg_mc (seg_run INP2 f)));
   (TXA f, zrep 80); R_INP; R_STACK].
Lemma P_K13984_sat_0 :
  seg_cuts.P_K13984 INP2 INPA S_TOP 0 C0 M0 TX1A (seg_cuts.TXT_N INP2 0) (REGS_T 0) (RMEM (RS_T 0)).
Proof. unfold seg_cuts.P_K13984. csat. Qed.
Lemma P_K13984_sat_1 :
  seg_cuts.P_K13984 INP2 INPA S_TOP 1 C0 M0 TX2A (seg_cuts.TXT_N INP2 1) (REGS_T 1) (RMEM (RS_T 1)).
Proof. unfold seg_cuts.P_K13984. csat. Qed.

(** K13ad8 (0x13ad8), `jal free(text)` after turn f: c, m hold seg_after INP2 f; the text block holds the text. *)
Definition TXI (f : nat) : list Z := txt_img (seg_txt INP2 f).
Definition REGS_F (f : nat) : bvmap 5 word :=
  rmap [(2, SP_MAIN); (8, M0); (26, M0 + MC_N); (18, 2); (10, TXA f); (23, TXA f); (27, Z.of_nat (S f));
        (19, seg_cur_at INP2 INPA (S f)); (21, seg_cur_n INP2 (S f)); (20, b2z (seg_ret (seg_after INP2 f)));
        (24, C0)].
Definition RS_F (f : nat) : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (seg_after INP2 f))); (M0, mblk_img false (seg_mc (seg_after INP2 f)));
   (TXA f, TXI f); R_INP; R_STACK].
Lemma P_K13ad8_sat_0 :
  seg_cuts.P_K13ad8 INP2 INPA S_TOP 0 C0 M0 TX1A (seg_cuts.TXT_N INP2 0) (REGS_F 0) (RMEM (RS_F 0)).
Proof. unfold seg_cuts.P_K13ad8. csat. Qed.
Lemma P_K13ad8_sat_1 :
  seg_cuts.P_K13ad8 INP2 INPA S_TOP 1 C0 M0 TX2A (seg_cuts.TXT_N INP2 1) (REGS_F 1) (RMEM (RS_F 1)).
Proof. unfold seg_cuts.P_K13ad8. csat. Qed.

(** K13ae0 (0x13ae0), after the file loop: c, m hold run P2. *)
Definition REGS_X : bvmap 5 word :=
  rmap [(2, SP_MAIN); (8, M0); (26, M0 + MC_N); (24, C0); (20, b2z (seg_ret (run (seg_pay INP2))))].
Definition RS_X : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (run (seg_pay INP2)))); (M0, mblk_img false (seg_mc (run (seg_pay INP2))));
   R_INP; R_STACK].
Lemma P_K13ae0_sat : seg_cuts.P_K13ae0 INP2 INPA S_TOP C0 M0 REGS_X (RMEM RS_X).
Proof. unfold seg_cuts.P_K13ae0. csat. Qed.

(** K13cac (0x13cac), calloc(cap + 1, 20) has returned mt; tab = calloc(cap + 1, 18) and mt all zero. *)
Definition REGS_C : bvmap 5 word :=
  rmap [(2, SP_MAIN); (8, M0); (26, M0 + MC_N); (10, MT0); (19, TAB0); (20, 5); (22, 4)].
Definition RS_C : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (run (seg_pay INP2)))); (M0, mblk_img false (seg_mc (run (seg_pay INP2))));
   (TAB0, zrep 90); (MT0, zrep 100); R_INP; R_STACK].
Lemma P_K13cac_sat :
  seg_cuts.P_K13cac INP2 INPA S_TOP C0 M0 TAB0 (seg_cuts.TAB_N INP2) MT0 (seg_cuts.MT_N INP2) REGS_C (RMEM RS_C).
Proof. unfold seg_cuts.P_K13cac. csat. Qed.

(** K13f40 (0x13f40), before the four frees: a register map only. *)
Definition REGS_Z : bvmap 5 word := rmap [(2, SP_MAIN); (20, MT0); (19, TAB0); (8, M0); (9, C0)].
Lemma P_K13f40_sat :
  seg_cuts.P_K13f40 INP2 INPA S_TOP C0 M0 TAB0 (seg_cuts.TAB_N INP2) MT0 (seg_cuts.MT_N INP2) REGS_Z (RMEM RS_C).
Proof. unfold seg_cuts.P_K13f40. csat. Qed.

(** ** The HEAD cuts *)

(** reac_segconf_parse_file's H_HEAD (0x14dc4), turn 0 (called from main at 0x13a18: entry sp SP_MAIN, sp =
    SP_PF1), at the start of line 2 of T1 (o = 17, ln = 1, d = [line 1]): c holds the state after line 1 (PF1 1:
    seg[0] = eth0.5, cur = Some 0, cur_name = "eth0.5"). The saved registers are main's at the call (ra = 0x13a1c,
    s0 = m, s2 = nfiles, s8 = c, s10 = m + 0x2000, s11 = f = 0). *)
Definition PFV : pf_sv :=
  PFSv (Z_to_bv 64 0x13a1c) (Z_to_bv 64 M0) (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 0)
       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 C0) (Z_to_bv 64 0) (Z_to_bv 64 (M0 + MC_N))
       (Z_to_bv 64 0).
Definition PFS : rconf * option nat * list Z := PF1 1.
Definition PF_FRM : list Z :=
  zrep 8 ++
  wimg [Z_to_bv 64 (C0 + RC_OVERFLOW); Z_to_bv 64 PF_BOX_WORD; Z_to_bv 64 PF_TAP_WORD; Z_to_bv 64 (C0 + RC_GEN);
        Z_to_bv 64 (C0 + RC_READING); Z_to_bv 64 (C0 + RC_N); Z_to_bv 64 PF_STR_LONG; Z_to_bv 64 PF_STR_BLANKS] ++
  zrep (0x358 - 0x48) ++ padz (snd PFS) 16 ++ wimg (sv_list PFV).
Definition RS_PFH : list region := [(SP_PF1, PF_FRM); (C0, rconf_img (fst (fst PFS))); (TX1A, txt_img T1); R_STACK].
Lemma pf_head_sat :
  pf_hctx (RMEM RS_PFH) (Z_to_bv 32 0) SP_PF1 LO PFV C0 TX1A T1 17 1 (firstn 1 L1) /\
  pf_state (RMEM RS_PFH) SP_PF1 C0 (fst (fst PFS)) (snd (fst PFS)) (snd PFS) (length (skipn 17 T1)) /\
  (17 < length T1)%nat /\ (length (skipn 17 T1) <= length (skipn 17 T1))%nat /\
  pf_regs (Z_to_bv 64 C0) (Z_to_bv 64 HASH) (Z_to_bv 64 (TX1A + Z.of_nat 17)) (Z_to_bv 64 1) (Z_to_bv 64 SEMI)
    (Z_to_bv 64 SP) (Z_to_bv 64 TAB) C0 (TX1A + Z.of_nat 17) 1 /\
  Z_to_bv 64 512 = Z_to_bv 64 512 /\
  Z_to_bv 64 (pf_cur_ptr C0 (snd (fst PFS))) = Z_to_bv 64 (pf_cur_ptr C0 (snd (fst PFS))).
Proof.
  unfold pf_hctx, pf_env, pf_text, pf_spill, pf_lctx, pf_state, pf_nm_at, pf_cnt, pf_regs, printf_env, ssp_ok.
  vmeq (snd (fst PFS)). unfold pf_cur_ok. csat.
Qed.

(** m_file's H_MF_HEAD (0x1407c), turn 1 (called from main at 0x13a34: sp0 = SP_MAIN, sp = SP_MF), at the start of
    line 2 of T2 (line = 1): m holds the state after line 1 (MF2 1: seg[1] = eth1.7 new, cur = Some 1), k0 = 1 (the
    kept refusal of turn 0). The saved registers are main's at the call (ra = 0x13a38, s0 = m, s2 = nfiles, s8 = c,
    s10 = m + 0x2000, s11 = f = 1). *)
Definition MFS : mconf * option nat := MF2 1.
Definition REST2 : list Z := skipn 17 T2.
Definition MF_SAVED : list word :=
  [Z_to_bv 64 1; Z_to_bv 64 (M0 + MC_N); Z_to_bv 64 0; Z_to_bv 64 C0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 2; Z_to_bv 64 0; Z_to_bv 64 M0; Z_to_bv 64 0x13a38].
Definition MF_FRM : list Z :=
  zrep 8 ++ le8z (M0 + MC_KNOCK) ++ le8z (M0 + MC_N) ++ le8z (M0 + MC_READING) ++ le8z (cur_ptr M0 (snd MFS)) ++
  zrep (0x68 - 0x28) ++ wimg MF_SAVED.
Definition RS_MFH : list region := [(SP_MF, MF_FRM); (M0, mblk_img false (fst MFS)); (TX2A, txt_img T2); R_STACK].
Lemma REST2_ne : REST2 <> [].
Proof. vm_compute. discriminate. Qed.
Lemma m_file_head_sat :
  (length REST2 < S (length REST2))%nat /\ REST2 <> [] /\
  m_file_loop (RMEM RS_MFH) (Z_to_bv 32 0) SP_MAIN SP_MF LO M0 (TX2A + 17) (fst MFS) (snd MFS) 1 1 REST2
    (Z_to_bv 64 0x13a38) (Z_to_bv 64 M0) (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 0)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 C0) (Z_to_bv 64 0) (Z_to_bv 64 (M0 + MC_N))
    (Z_to_bv 64 1) /\
  m_file_regs M0 (TX2A + 17) 1 (Z_to_bv 64 M0) (Z_to_bv 64 0x3b) (Z_to_bv 64 (TX2A + 17)) (Z_to_bv 64 1)
    (Z_to_bv 64 9) (Z_to_bv 64 0x1ff) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20).
Proof.
  split; [apply Nat.lt_succ_diag_r|]. split; [exact REST2_ne|].
  unfold m_file_loop, m_file_regs, cell8, printf_env, ssp_ok, words_img.
  vmeq (snd MFS). unfold cur_ok. csat.
Qed.

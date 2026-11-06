(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd): satisfiability of the cut predicates of LLVMFuzzerTestOneInput
    (U/Prog/seg_cuts.v, the UBSan twins of the plain cuts: P_K13984 (calloc(m)), P_K139e4 (the file-loop head) at
    f = 0 and f = 1, P_K13aac (malloc(text)), P_K13c34 (free(text)), P_K13c3c (after the loop), P_K13e90
    (calloc(mt)), P_K141ec (the frees)) and the entry facts of the HEAD cuts of reac_segconf_parse_file
    (U/Prog/reac_segconf_parse_file_pieces_c.v: H_HEAD) and of m_file (U/Prog/m_file_c.v: H_MF_HEAD), of
    commit aca5136e2baf. One closed lemma each, at the real run of the input INP2
    (Prog/SegSatKit234.v).

    proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Nothing here is an
    Axiom, a Parameter, an admit or an Admitted.

    The ghosts as in the plain file Prog/sat/F234SatCuts.v; main's frame (240 bytes) holds the cells U/seg_cuts.v's
    comment lists (8 flags, 0x10 the cap byte, 0x20 cap, 0x28 m + 0x10, 0x30 the label format, 0x38 m & 3, 0x40
    nfiles, 0x48 c, 0x50 m); the registers the cut names hold its map, every other register 0. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SegSatKit SegSatKit234.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SegSat234.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import
  refuse_c reac_segconf_parse_file_c reac_segconf_parse_file_pieces_c m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require seg_cuts.
Import ListNotations.
Open Scope Z_scope.

Ltac csat :=
  lazymatch goal with
  | |- _ /\ _ => split; csat
  | |- seg_cuts.rgz _ _ _ => unfold seg_cuts.rgz; apply bv_eq; vm_compute; reflexivity
  | |- getr _ _ = _ => apply bv_eq; vm_compute; reflexivity
  | |- seg_cuts.celz _ _ _ _ => unfold seg_cuts.celz; csat
  | |- seg_cuts.P_mcore _ _ _ _ _ _ _ => unfold seg_cuts.P_mcore; csat
  | |- seg_cuts.P_lcore _ _ _ _ _ _ _ => unfold seg_cuts.P_lcore; csat
  | |- _ => sat2 rsegs_below
  end.

(** ** The cut predicates *)

Definition FRM_L : list Z :=
  zrep 8 ++ le8z 1 ++ le8z 4 ++ zrep 8 ++ le8z 4 ++ le8z (M0 + 0x10) ++ le8z seg_cuts.LABEL_FMT ++ le8z (M0 mod 4) ++
  le8z 2 ++ le8z C0 ++ le8z M0.
Definition R_INP : region := (INPA, inp_img).
(** The registers P_mcore and P_lcore name: s2 = ~m, s11 = &m->n, s5 = 33. *)
Definition RCORE : list (Z * Z) := [(2, SP_MAIN); (18, - M0 - 1); (27, M0 + MC_N); (21, 33)].

(** K13984 (0x13984): calloc(1, 9236) has returned m; c not yet initialised (zeros here), m all zero. *)
Definition REGS_A : bvmap 5 word :=
  rmap [(2, SP_MAIN); (10, M0); (8, C0); (18, 4); (21, 1); (22, 2); (19, seg_cur_at INP2 INPA 0);
        (9, seg_cur_n INP2 0); (27, MC_N)].
Definition RS_A : list region := [(C0, zrep 16616); (M0, zrep 9236); R_INP; R_STACK].
Lemma P_K13984_sat : seg_cuts.P_K13984 INP2 INPA S_TOP C0 M0 REGS_A (RMEM RS_A).
Proof. unfold seg_cuts.P_K13984. csat. Qed.

(** K139e4 (0x139e4), the file-loop head at turn f. *)
Definition REGS_E (f : nat) : bvmap 5 word :=
  rmap (RCORE ++ [(8, Z.of_nat f); (19, seg_cur_at INP2 INPA f); (9, seg_cur_n INP2 f);
                  (20, b2z (seg_ret (seg_run INP2 f)))]).
Definition RS_E (f : nat) : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (seg_run INP2 f))); (M0, mblk_img false (seg_mc (seg_run INP2 f)));
   R_INP; R_STACK].
Lemma P_K139e4_sat_0 : seg_cuts.P_K139e4 INP2 INPA S_TOP 0 C0 M0 (REGS_E 0) (RMEM (RS_E 0)).
Proof. unfold seg_cuts.P_K139e4. csat. Qed.
Lemma P_K139e4_sat_1 : seg_cuts.P_K139e4 INP2 INPA S_TOP 1 C0 M0 (REGS_E 1) (RMEM (RS_E 1)).
Proof. unfold seg_cuts.P_K139e4. csat. Qed.

(** K13aac (0x13aac), malloc(n + 1) of turn f has returned the text block t. *)
Definition TXA (f : nat) : Z := if (f =? 0)%nat then TX1A else TX2A.
Definition REGS_T (f : nat) : bvmap 5 word :=
  rmap (RCORE ++ [(10, TXA f); (26, seg_txt_n INP2 f); (22, seg_turn_np INP2 f); (25, seg_turn_at INP2 INPA f);
                  (19, seg_turn_at INP2 INPA f + seg_turn_np INP2 f); (9, Z.of_nat (length (seg_turn_tail INP2 f)));
                  (24, seg_lb INP2 f); (8, Z.of_nat f); (20, b2z (seg_ret (seg_run INP2 f)))]).
Definition RS_T (f : nat) : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (seg_run INP2 f))); (M0, mblk_img false (seg_mc (seg_run INP2 f)));
   (TXA f, zrep 80); R_INP; R_STACK].
Lemma P_K13aac_sat_0 :
  seg_cuts.P_K13aac INP2 INPA S_TOP 0 C0 M0 TX1A (seg_cuts.TXT_N INP2 0) (REGS_T 0) (RMEM (RS_T 0)).
Proof. unfold seg_cuts.P_K13aac. csat. Qed.
Lemma P_K13aac_sat_1 :
  seg_cuts.P_K13aac INP2 INPA S_TOP 1 C0 M0 TX2A (seg_cuts.TXT_N INP2 1) (REGS_T 1) (RMEM (RS_T 1)).
Proof. unfold seg_cuts.P_K13aac. csat. Qed.

(** K13c34 (0x13c34), `jal free(text)` after turn f. *)
Definition REGS_F (f : nat) : bvmap 5 word :=
  rmap (RCORE ++ [(10, TXA f); (23, TXA f); (8, Z.of_nat (S f)); (19, seg_cur_at INP2 INPA (S f));
                  (9, seg_cur_n INP2 (S f)); (20, b2z (seg_ret (seg_after INP2 f))); (26, 2)]).
Definition RS_F (f : nat) : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (seg_after INP2 f))); (M0, mblk_img false (seg_mc (seg_after INP2 f)));
   (TXA f, txt_img (seg_txt INP2 f)); R_INP; R_STACK].
Lemma P_K13c34_sat_0 :
  seg_cuts.P_K13c34 INP2 INPA S_TOP 0 C0 M0 TX1A (seg_cuts.TXT_N INP2 0) (REGS_F 0) (RMEM (RS_F 0)).
Proof. unfold seg_cuts.P_K13c34. csat. Qed.
Lemma P_K13c34_sat_1 :
  seg_cuts.P_K13c34 INP2 INPA S_TOP 1 C0 M0 TX2A (seg_cuts.TXT_N INP2 1) (REGS_F 1) (RMEM (RS_F 1)).
Proof. unfold seg_cuts.P_K13c34. csat. Qed.

(** K13c3c (0x13c3c), after the file loop. *)
Definition REGS_X : bvmap 5 word := rmap (RCORE ++ [(20, b2z (seg_ret (run (seg_pay INP2))))]).
Definition RS_X : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (run (seg_pay INP2)))); (M0, mblk_img false (seg_mc (run (seg_pay INP2))));
   R_INP; R_STACK].
Lemma P_K13c3c_sat : seg_cuts.P_K13c3c INP2 INPA S_TOP C0 M0 REGS_X (RMEM RS_X).
Proof. unfold seg_cuts.P_K13c3c. csat. Qed.

(** K13e90 (0x13e90), calloc(cap + 1, 20) has returned mt; tab and mt all zero. *)
Definition REGS_C : bvmap 5 word := rmap (RCORE ++ [(10, MT0); (9, TAB0); (20, 5); (8, 4)]).
Definition RS_C : list region :=
  [(SP_MAIN, FRM_L); (C0, rconf_img (seg_rc (run (seg_pay INP2)))); (M0, mblk_img false (seg_mc (run (seg_pay INP2))));
   (TAB0, zrep 90); (MT0, zrep 100); R_INP; R_STACK].
Lemma P_K13e90_sat :
  seg_cuts.P_K13e90 INP2 INPA S_TOP C0 M0 TAB0 (seg_cuts.TAB_N INP2) MT0 (seg_cuts.MT_N INP2) REGS_C (RMEM RS_C).
Proof. unfold seg_cuts.P_K13e90. csat. Qed.

(** K141ec (0x141ec), before the four frees: a register map only. *)
Definition REGS_Z : bvmap 5 word := rmap [(2, SP_MAIN); (20, MT0); (18, TAB0); (19, M0); (8, C0)].
Lemma P_K141ec_sat :
  seg_cuts.P_K141ec INP2 INPA S_TOP C0 M0 TAB0 (seg_cuts.TAB_N INP2) MT0 (seg_cuts.MT_N INP2) REGS_Z (RMEM RS_C).
Proof. unfold seg_cuts.P_K141ec. csat. Qed.

(** ** The HEAD cuts *)

(** reac_segconf_parse_file's H_HEAD (0x153a8), turn 0 (called from main at 0x13b4c: entry sp SP_MAIN, sp =
    SP_PF1), at the start of line 2 of T1 (o = 17, ln = 1, d = [line 1]): c holds PF1 1 (seg[0] = eth0.5, cur =
    Some 0, cur_name = "eth0.5"). The saved registers are main's at the call (ra = 0x13b50, s0 = f = 0, s2 = ~m,
    s4 = returned = 1, s5 = 33, s11 = m + 0x2000). *)
Definition PFV : pf_sv :=
  PFSv (Z_to_bv 64 0x13b50) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (- M0 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 1)
       (Z_to_bv 64 33) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
       (Z_to_bv 64 (M0 + MC_N)).
Definition PFS : rconf * option nat * list Z := PF1 1.
Definition PF_FRM : list Z :=
  zrep 16 ++
  wimg [Z_to_bv 64 (C0 + RC_OVERFLOW); Z_to_bv 64 (RSEG_SIZE * 32); Z_to_bv 64 PF_BOX_WORD; Z_to_bv 64 PF_TAP_WORD;
        pf_not (SP_PF1 + PF_LOWM); Z_to_bv 64 (C0 + RC_GEN); pf_not (SP_PF1 + PF_LOW); pf_not C0;
        Z_to_bv 64 (C0 + RC_READING); Z_to_bv 64 (C0 + RC_N)] ++
  zrep 16 ++
  wimg [Z_to_bv 64 PF_STR_LONG; Z_to_bv 64 PF_STR_BLANKS; pf_not (SP_PF1 + PF_BUF)] ++
  le8z (pf_cur_ptr C0 (snd (fst PFS))) ++ le8z C0 ++
  zrep (0x3a8 - 0x98) ++ padz (snd PFS) 16 ++ wimg (sv_list PFV).
Definition RS_PFH : list region := [(SP_PF1, PF_FRM); (C0, rconf_img (fst (fst PFS))); (TX1A, txt_img T1); R_STACK].
Lemma pf_head_sat :
  pf_hctx (RMEM RS_PFH) (Z_to_bv 32 0) SP_PF1 LO PFV C0 TX1A T1 17 1 (firstn 1 L1) /\
  pf_state (RMEM RS_PFH) SP_PF1 C0 (fst (fst PFS)) (snd (fst PFS)) (snd PFS) (length (skipn 17 T1)) /\
  (17 < length T1)%nat /\ (length (skipn 17 T1) <= length (skipn 17 T1))%nat /\
  pf_regs (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) (Z_to_bv 64 (TX1A + Z.of_nat 17)) (Z_to_bv 64 1) (Z_to_bv 64 (-1))
    (Z_to_bv 64 HASH) (Z_to_bv 64 1) (TX1A + Z.of_nat 17) 1 /\
  pf_curslot (RMEM RS_PFH) SP_PF1 C0 (snd (fst PFS)).
Proof.
  unfold pf_hctx, pf_env, pf_text, pf_spill, pf_lctx, pf_state, pf_nm_at, pf_cnt, pf_regs, pf_curslot, printf_env,
    ssp_ok.
  vmeq (snd (fst PFS)). unfold pf_cur_ok. csat.
Qed.

(** m_file's H_MF_HEAD (0x14348), turn 1 (called from main at 0x13b7c: sp0 = SP_MAIN, sp = SP_MF), at the start of
    line 2 of T2 (line = 1): m holds MF2 1 (seg[1] = eth1.7 new, cur = Some 1), k0 = 1. The saved registers are
    main's at the call (ra = 0x13b80, s0 = f = 1, s2 = ~m, s4 = returned = 1, s5 = 33, s11 = m + 0x2000). *)
Definition MFS : mconf * option nat := MF2 1.
Definition REST2 : list Z := skipn 17 T2.
(** saved_at's order: s11, s10, ..., s0, ra. *)
Definition MF_SAVED : list word :=
  [Z_to_bv 64 (M0 + MC_N); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 33;
   Z_to_bv 64 1; Z_to_bv 64 0; Z_to_bv 64 (- M0 - 1); Z_to_bv 64 0; Z_to_bv 64 1; Z_to_bv 64 0x13b80].
Definition MF_FRM : list Z :=
  zrep 8 ++ le8z (- 1 - M0) ++ le8z (M0 + MC_KNOCK) ++ le8z (- 1 - (M0 + MC_KNOCK)) ++ le8z (M0 + MC_READING) ++
  le8z (M0 + MC_N) ++ le8z (cur_ptr M0 (snd MFS)) ++ zrep (0xa8 - 0x38) ++ wimg MF_SAVED.
Definition RS_MFH : list region := [(SP_MF, MF_FRM); (M0, mblk_img false (fst MFS)); (TX2A, txt_img T2); R_STACK].
Lemma REST2_ne : REST2 <> [].
Proof. vm_compute. discriminate. Qed.
Lemma m_file_head_sat :
  (length REST2 < S (length REST2))%nat /\ REST2 <> [] /\
  m_file_loop (RMEM RS_MFH) (Z_to_bv 32 0) SP_MAIN SP_MF LO M0 (TX2A + 17) (fst MFS) (snd MFS) 1 1 REST2
    (Z_to_bv 64 0x13b80) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (- M0 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 1)
    (Z_to_bv 64 33) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
    (Z_to_bv 64 (M0 + MC_N)) /\
  m_file_regs M0 (TX2A + 17) 1 (Z_to_bv 64 M0) (Z_to_bv 64 (TX2A + 17)) (Z_to_bv 64 1) (Z_to_bv 64 1)
    (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (M0 + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
    (Z_to_bv 64 0x3b).
Proof.
  split; [apply Nat.lt_succ_diag_r|]. split; [exact REST2_ne|].
  unfold m_file_loop, m_file_regs, cell8, printf_env, ssp_ok, words_img.
  vmeq (snd MFS). unfold cur_ok. csat.
Qed.

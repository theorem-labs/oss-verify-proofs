(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA Nodes RzCPS NodesA FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow MainSkel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_auxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition TP_A : Z := 0x6ab368.
Definition ERRNO_A : Z := TP_A - 164.
Definition MAIN_RA : Z := 0x14f034.
Definition GOT_STDERR : Z := 0x16ee38.
Definition STDERR_VAR : Z := 0x16e0c8.
Definition RET_OPEN : Z := 0xae1e8.
Definition GOT_LLVMINIT : Z := 0x16ee40.
Definition TR_INIT : Z := 0x6a9790.
Definition TR_EMPTY : Z := 0x6a97a0.

Definition fds0 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Lemma asegs_below : segs_below_b bsegs SEGTOP_A = true.
Proof. lazy. reflexivity. Qed.
Lemma asegs_wx : wx_segs_nowrap bsegs.
Proof. apply wx_segs_nowrap_of_b. lazy. reflexivity. Qed.

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma PMfd_mat_stable : forall F0 fs0, mat_stable (PMfd F0 fs0).
Proof. intros F0 fs0. exact (mat_stable_obs (fun fds fs' _ _ _ => fds = F0 /\ fs' = fs0)). Qed.

Lemma ASTA_PM_mat_stable : forall Σ F0 fs0, mat_stable (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo).
Proof. intros Σ F0 fs0. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| apply PMfd_mat_stable]. Qed.

Lemma asta_evt : forall Σ F0 fs0 Pm Q, (forall ms, Pm ms -> evt bsegs Q ms) ->
  cps bsegs (ASTA RT Σ (PMfd F0 fs0) Pm) (ASTA RT Σ (PMfd F0 fs0) Q).
Proof.
  intros Σ F0 fs0 Pm Q H. unfold ASTA.
  apply (ast_evt bsegs SEGTOP_A asegs_wx asegs_below); [apply ASTA_PM_mat_stable| exact H].
Qed.

Lemma ASTA_conseq : forall Σ PMc Pm Pm' c, ASTA RT Σ PMc Pm c -> (forall ms, Pm ms -> Pm' ms) -> ASTA RT Σ PMc Pm' c.
Proof. intros Σ PMc Pm Pm' c H HP. unfold ASTA in *. eapply AST_conseq; [exact H| exact HP| auto]. Qed.

Lemma ASTA_ex : forall {X} Σ PMc (Pm : X -> machine_state -> Prop) c,
  ASTA RT Σ PMc (fun ms => exists x, Pm x ms) c -> exists x, ASTA RT Σ PMc (Pm x) c.
Proof. intros X Σ PMc Pm c H. unfold ASTA in *. exact (AST_exI SEGTOP_A (rt_allow RT Σ) Pm _ c H). Qed.

Lemma ASTA_unpack : forall Σ PMc (Pm : machine_state -> Prop) c, ASTA RT Σ PMc Pm c -> exists ms, Pm ms /\ ASTA RT Σ PMc (eq ms) c.
Proof.
  intros Σ PMc Pm [ms mo] (H1 & H2 & H3 & H4). exists (restrict (HID (rt_allow RT Σ) mo) ms). split; [exact H2|].
  split; [exact H1|]. split; [reflexivity|]. split; [exact H3| exact H4].
Qed.

End Kit.

Definition fp_local (W : list (Z * Z)) (P : mem -> Prop) : Prop :=
  forall m m', P m -> (forall a : word, in_ranges W (bv_unsigned a) -> m' a = m a) -> P m'.

Definition stderr_cells (m : mem) : Prop :=
  ro_cells bsegs m GOT_STDERR [C8 (Z_to_bv 64 STDERR_VAR)] /\ ro_cells bsegs m STDERR_VAR [C8 (Z_to_bv 64 STDERR_FILE)].

Definition S_SHORT : Z := 0x21b9c.
Definition S_OVER : Z := 0x162e0.
Definition drv_consts (m : mem) : Prop :=
  stderr_cells m /\ ro_cells bsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] /\ ro_cells bsegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)]

  /\ acc bsegs m S_SHORT 31 /\ acc bsegs m S_OVER 31.

Lemma drv_ssp : forall m g, drv_consts m -> ro_cells bsegs m SSP_GUARD [C8 g] -> ssp_cells m.
Proof. intros m g (_ & H & _) HG. exists g. split; assumption. Qed.

Definition drv_cell (x : Z) : Prop :=
  (ERRNO_A <= x < ERRNO_A + 4) \/ (SSP_GUARD <= x < SSP_GUARD + 8) \/ (g_read_stage <= x < g_read_stage + 65536)
  \/ (0x6cb600 <= x < 0x6cb600 + 8).
Lemma auxc_drv : forall x, auxc x -> drv_cell x.
Proof. intros x Hx. unfold auxc, EL_AUXV_CELL in Hx. unfold drv_cell. lia. Qed.

Section Drv.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.

Variable LIB : mem -> Prop.

Variable argvb : list (list byte).
Variable fs : Fs.

Definition CLX (so : stdout_st) (m : mem) : Prop :=
  OUT_rep so m /\ ERR_rep m /\ XENV m /\ LIB m /\ (exists g, ro_cells bsegs m SSP_GUARD [C8 g])
  /\ (exists v, rw_cells bsegs m ERRNO_A [C4 v]) /\ stk bsegs m g_read_stage (g_read_stage + 65536).

Definition argv_rep (m : mem) (ap : Z) : Prop :=
  exists ptrs : list word, u64arr bsegs m ap ptrs /\ length ptrs = Nat.min 2 (length argvb)
    /\ (forall i s p, nth_error argvb i = Some s -> nth_error ptrs i = Some p ->
         bytes_at bsegs m (bv_unsigned p) (s ++ [Z_to_bv 8 0])
         /\ ap + 8 * Z.of_nat (length argvb) <= bv_unsigned p /\ bv_unsigned p + Z.of_nat (length s) + 1 <= USTACK_TOP - 16)

    /\ (forall i s p, nth_error argvb i = Some s -> nth_error ptrs i = Some p ->
         exists slack, bytes_at bsegs m (bv_unsigned p + Z.of_nat (length s) + 1) slack
           /\ (- (bv_unsigned p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
           /\ bv_unsigned p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16).

Definition CREDIT_DRV : Z := 2^35.

Definition sigma0_ok (Σ : rts RT) (usp : Z) : Prop :=
  rt_live RT Σ = [] /\ rt_frames RT Σ = [] /\ CREDIT_DRV <= rt_credit RT Σ /\ usp <= rt_sp0 RT Σ <= usp + 48
  /\ 0x7fff80000000 <= rt_sp0 RT Σ     .

Definition START (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 MAIN_RA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
             (Z_to_bv 64 (Z.of_nat (length argvb))) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc a_main m)) c
    /\ ART RT Σ m /\ mem_inv bsegs m /\ CLX stdout_init m /\ argv_rep m ap /\ el_auxvA usp m
    /\ stk bsegs m (rt_sp0 RT Σ - STACK_WIN) usp /\ sigma0_ok Σ usp
    /\ usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp.

Definition main_frame (m : mem) (usp : Z) (s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
  (exists junk, rw_cells bsegs m (usp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 MAIN_RA)])
  /\ el_auxvA usp m.

Definition MAINCTX (Σ : rts RT) (so : stdout_st) (usp ap : Z) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv bsegs m /\ CLX so m /\ argv_rep m ap /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk bsegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
  /\ usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ <= usp + 48.

Definition path_b : list byte := nth 1 argvb [].

Definition path_slack (m : mem) (path : Z) : Prop :=
  exists slack, bytes_at bsegs m (path + Z.of_nat (length path_b) + 1) slack
    /\ (- (path + Z.of_nat (length path_b) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ path + Z.of_nat (length path_b) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16.

Definition OPEN (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path : Z) (gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
             (Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_open m)) c
    /\ MAINCTX Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok Σ usp
    /\ bytes_at bsegs m path (path_b ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length path_b) + 1 <= USTACK_TOP - 16
    /\ path_slack m path.

Definition FAILED (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path : Z) (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (ret_stf (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1 (Z_to_bv 64 path)
              s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m) c
    /\ MAINCTX Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok Σ usp
    /\ bytes_at bsegs m path (path_b ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length path_b) + 1 <= USTACK_TOP - 16
    /\ path_slack m path.

Definition OPENED (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path : Z) (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) ent,
    ASTA RT Σ (PMfd (fd_insert fds0 (Z_to_bv 64 3) ent) fs)
      (ret_stf (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1 (Z_to_bv 64 path)
              s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 3) m) c
    /\ MAINCTX Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok Σ usp
    /\ bytes_at bsegs m path (path_b ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length path_b) + 1 <= USTACK_TOP - 16
    /\ open_ent path_b fs = Some ent /\ path_slack m path.

Definition EXIT (code : Z) : config -> Prop := EXITc fs code.

End Drv.

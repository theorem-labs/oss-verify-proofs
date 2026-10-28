(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_agree D_libiface D_clx D_rlkit D_libiface_pem X_ax D_trpro D_trwalk D_trdefs D_tr1 D_tr2.
From Stdlib Require Import Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma filter_perm : forall {A : Type} (f : A -> bool) (l l' : list A), Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros A f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f y), (f x); [apply perm_swap| apply perm_skip| apply perm_skip|]; apply Permutation_refl.
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma filter_all : forall {A : Type} (f : A -> bool) (l : list A), (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros A f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH.
  intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma live_remove_perm : forall p n (l r : list (Z * Z)), Permutation l ((p, n) :: r) -> (forall q k, In (q, k) r -> q <> p) ->
  Permutation (live_remove p l) r.
Proof.
  intros p n l r HP HR. unfold live_remove.
  apply (Permutation_trans (filter_perm (fun e : Z * Z => negb (fst e =? p)) _ _ HP)). cbn. rewrite Z.eqb_refl. cbn.
  rewrite filter_all; [apply Permutation_refl|]. intros [q k] Hin. cbn. rewrite (proj2 (Z.eqb_neq q p) (HR q k Hin)). reflexivity.
Qed.

Section Tr3.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
(* [comment removed for export] *)
Variable LIB : mem -> Prop.
Variable CG : cgraph.
(* [comment removed for export] *)
Variable LIB0P : mem -> Prop.
Variable LIBP : list (Z * Z) -> mem -> Prop.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis FRN : free_null_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis INITC : fuzz_init_cps RT LIB0P LIBP FZ_SITES FZ_CALLS.
Hypothesis FUZZC : fuzz_one_cps RT LIBP FZ_SITES FZ_CALLS.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Variable XENV' : mem -> Prop.
Hypothesis XENV'_loc : fp_local XENV_FP XENV'.
Hypothesis XENV_ax : forall m, XENV m -> exists fin p1 p2, ax_chunks false fin p1 p2 m.
Hypothesis XENV_libc : forall m, XENV m -> libc_cells m.
Hypothesis XENV_incb : forall m, XENV m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV_step : forall m m', XENV m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV' m'.
Hypothesis XENV_fp_ax : forall x, (0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INCB) -> in_ranges XENV_FP x.
Hypothesis XENV'_ax : forall m, XENV' m -> exists fin p1 p2, ax_chunks true fin p1 p2 m.
Hypothesis XENV'_incb : forall m, XENV' m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV'_upd : forall m m', XENV' m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV' m'.
Hypothesis LIB_pre : forall m, LIB m -> LIB0P m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].
Hypothesis LOC0 : lib0_local_d LIB0P.
Hypothesis LOCP : lib_local_d LIBP.
Hypothesis CGH : cg_has CG FZ_SITES FZ_CALLS.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Lemma tr_later : forall n k j usp buf cap x0 x1 x2 x3 x4 x5, Z.to_nat k = n -> 1 <= k <= 4 -> (j + n < 499)%nat ->
  cpsE asegs (TLOOP RT OUT_rep ERR_rep XENV' LIBP CG fs k (so_lines j) usp buf cap x0 x1 x2 x3 x4 x5) []
             (TFREE RT OUT_rep ERR_rep XENV' LIBP CG fs (so_lines (j + n)) usp buf cap x0 x1 x2 x3 x4 x5).
Proof using AF AF_DRV FUZZC VPR OUT_loc ERR_loc XENV'_loc IO_img XENV_img LOCP CGH XENV'_ax XENV'_incb XENV'_upd XENV_fp_ax.
  induction n as [|n IH]; intros k j usp buf cap x0 x1 x2 x3 x4 x5 Hn Hk Hj; [lia|].
  change ([] : list event) with (evw 1 (emit0_out (so_lines j)) ++ []).
  eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP XENV' XENV_FP CG LIBP FZ_SITES FZ_CALLS fs AF AF_DRV FUZZC VPR OUT_loc ERR_loc
                             XENV'_loc IO_img XENV_img XENV'_ax XENV'_incb XENV'_upd XENV_fp_ax LOCP CGH); right; exists j; split; [lia| reflexivity]|].
  rewrite emit0_next_lines.
  intros T c [(K1 & HL)|(K1 & HF)] Hk'.
  - replace (j + S n)%nat with (S j + n)%nat in Hk' by lia.
    exact (IH (k - 1) (S j) usp buf cap x0 x1 x2 x3 x4 x5 ltac:(lia) ltac:(lia) ltac:(lia) T c HL Hk').
  - assert (n = 0%nat) by lia. subst n. replace (j + 1)%nat with (S j) in Hk' by lia.
    exact (cpsE_nil asegs _ _ (cps_refl asegs _) T c HF Hk').
Qed.

(* [comment removed for export] *)
Lemma tr_end : forall so usp buf cap x0 x1 x2 x3 x4 x5,
  cps asegs (TFREE RT OUT_rep ERR_rep XENV' LIBP CG fs so usp buf cap x0 x1 x2 x3 x4 x5)
            (TRET RT OUT_rep ERR_rep XENV' LIBP CG fs so usp buf cap x0 x1 x2 x3 x4 x5).
Proof using AF FRE FRN OUT_loc ERR_loc XENV'_loc IO_img XENV_img LOCP.
  intros so usp buf cap x0 x1 x2 x3 x4 x5 T c HF Hk.
  destruct HF as (Σ & CL & plen & d & owned & payload & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11
                  & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HT).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & (LVP & LIBc & LVN & LVS & LCG) & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).
  assert (CLIN : forall p n, In (p, n) CL -> In (p, n) (rt_live RT Σ)).
  { intros p n Hin. apply (Permutation_in _ (Permutation_sym LVP)). apply in_or_app. right. exact Hin. }
  (* [comment removed for export] *)
  assert (TAIL : forall (Σ' : rts RT) (m' : mem) (v : word) (t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' : word) F' fc' cf,
            ASTA RT Σ' (PMfd fds0 fs)
              (eq (MS (mkR (Z_to_bv 64 0x1f2f64) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
                           (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned) (Z_to_bv 64 (-1)) (Z_to_bv 64 TR_INIT)
                           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc (Z_to_bv 64 0x1f2f64)) fc' None m'
                      (seg_rom asegs))) cf ->
            ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo (usp - 160) ->
            rt_sp0 RT Σ' = rt_sp0 RT Σ -> CLIC RT LIBP CG Σ' CL [(buf, cap)] m' -> rt_frames RT Σ' = [] ->
            CLX OUT_rep ERR_rep XENV' LIBT so m' -> agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
            realizes asegs cf T).
  { intros Σ' m' v t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F' fc' cf Hc ART1 MI1 ST1 SP1 LV1 FRS1 CLX1 AG1.
    rewrite (ret_pc_even 0x1f2f64) in Hc by lia.
    assert (TF1 : tr_frame m' (usp - 80) (Z_to_bv 64 0x1f2d08) x0 x1 x2 x3 x4 x5).
    { apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul. }
    pose proof (tr_free_ret_walk (usp - 80) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned)
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' x0 x1 x2 x3 x4 x5 F' fc' m' lo
                  ltac:(replace (usp - 80 - 80) with (usp - 160) by lia; exact ST1) ltac:(ul) ltac:(ul) B16' ltac:(ul) TF1 MI1) as W1.
    replace (usp - 80 - 80) with (usp - 160) in W1 by lia.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' _ fs _ _ W1') Hc).
    intros cf2 Hc2. apply Hk.
    destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & ((s6' & s7' & ->) & ST2) & Hc2').
    exists Σ', CL, gp, t0', t1', t2', b1, b2, b3, b4, b5, b6, b7, s6', s7', s8, s9, s10, s11, t3', t4', t5', t6'.
    exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m'.
    split; [exact Hc2'|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
    split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul|].
    rewrite SP1. split; [exact ST2|]. split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
    split; [exact LV1|]. split; [exact FRS1| exact UT0]. }
  destruct (Z.eq_dec plen 0) as [Z0|NZ].
  - (* [comment removed for export] *)
    destruct (P0 Z0) as [-> ->].
    apply (FRN Σ (PMfd fds0 fs) (Z_to_bv 64 0x1f2f64) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
             (Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
    + unfold unwind_ok, fp_invalid. rewrite EU, !unsigned_lit by ul. left. split; [cbn; tauto|]. left. ul.
    + intros cf1 (v & Hc1).
      destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & _) & Hc1').
      destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
      rewrite EU in ST1, PRES1.
      apply (TAIL Σ m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1 ST1 eq_refl); try assumption.
      * split; [unfold tr_live in LVP; rewrite (proj2 (Z.eqb_eq plen 0) Z0) in LVP; exact LVP|].
        split; [| split; [exact LVN|]; split; [exact LVS| exact LCG]].
        apply (LOCP CL m m1 LIBc). intros a Ha. apply PRES1; [| lia].
        destruct Ha as [Ha|(p & n & Hin & Hr)]; [right; left; exact (proj1 (LIBD_static _ Ha))|].
        right; right; left. exists p, n. split; [exact (CLIN _ _ Hin)| exact Hr].
      * exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV' XENV_FP LIBT OUT_loc ERR_loc XENV'_loc LIBT_loc IO_img XENV_img
                 _ m m1 _ _ _ _ _ CLX0 PRES1 WM1 ltac:(intros x Hx; lia)).
      * apply (agree_stack_pres_ex _ _ _ _ _ _ _ PRES1). ul.
  - (* [comment removed for export] *)
    pose proof (P1 ltac:(lia)) as ->.
    assert (LVP' : Permutation (rt_live RT Σ) ((owned, plen) :: [(buf, cap)] ++ CL)).
    { unfold tr_live in LVP. rewrite (proj2 (Z.eqb_neq plen 0) NZ) in LVP. exact LVP. }
    assert (INO : In (owned, plen) (rt_live RT Σ)) by (apply (Permutation_in _ (Permutation_sym LVP')); left; reflexivity).
    destruct (Permutation_vs_cons_inv LVP') as (l1 & l2 & EL).
    assert (PR : Permutation ([(buf, cap)] ++ CL) (l1 ++ l2)).
    { apply (@Permutation_cons_app_inv _ _ l1 l2 (owned, plen)). rewrite <- EL. exact (Permutation_sym LVP'). }
    assert (DISJ : forall q k, In (q, k) ([(buf, cap)] ++ CL) -> q <> owned).
    { intros q k Hin E. subst q.
      assert (Hk0 : 0 < k) by (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact CAP0| exact (LVS _ _ Hin)]).
      destruct (af_live_disj RT AF Σ m owned plen owned k l1 l2 ART0 EL (Permutation_in _ PR Hin)); lia. }
    apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0x1f2f64) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
             (Z_to_bv 64 owned) (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) (Z_to_bv 64 (-1)) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m owned plen lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
    + unfold unwind_ok, fp_invalid. rewrite EU, !unsigned_lit by ul. left. split; [cbn; tauto|]. left. ul.
    + intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1 & CG1).
      destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
      destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
      rewrite EU in ST1, PRES1.
      assert (LVR : Permutation (rt_live RT Σ1) ([(buf, cap)] ++ CL)) by (rewrite LV1; exact (live_remove_perm owned plen _ _ LVP' DISJ)).
      apply (TAIL Σ1 m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1); try assumption.
      * split; [exact LVR|]. split; [| split; [exact LVN|]; split; [exact LVS| rewrite CG1; exact LCG]].
        apply (LOCP CL m m1 LIBc). intros a Ha. apply PRES1.
        destruct Ha as [Ha|(p & n & Hin & Hr)]; [right; left; exact (proj1 (LIBD_static _ Ha))|].
        right; right; left. exists p, n. split; [| exact Hr]. apply (Permutation_in _ (Permutation_sym LVR)). right. exact Hin.
      * rewrite FRS1. exact FRS.
      * exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV' XENV_FP LIBT OUT_loc ERR_loc XENV'_loc LIBT_loc IO_img XENV_img _ m m1 _ _ _ CLX0 PRES1).
      * exact (agree_stack_pres _ _ _ _ _ PRES1).
Qed.

(* [comment removed for export] *)
Theorem target_run_cpsE : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  TPRE RT OUT_rep ERR_rep XENV LIB CG Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x1f2d08) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (evw 1 [48; 10])
    (TRET RT OUT_rep ERR_rep XENV' LIBP CG fs (so_lines (Z.to_nat (tr_calls L c0b) - 1)) usp buf cap x0 x1 x2 x3 x4 x5).
Proof using AF AF_DRV MAL FRE FRN MCP INITC FUZZC VPR OUT_loc ERR_loc XENV_loc IO_img XENV_img LIB_pre LOC0 LOCP CGH
            XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax XENV'_ax XENV'_incb XENV'_upd.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP.
  pose proof (tr_calls_range L c0b) as TCR.
  eapply cps_cpsE; [exact (tr_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG LIB0P LIBP FZ_SITES FZ_CALLS fs AF AF_DRV MAL MCP INITC
                              OUT_loc ERR_loc XENV_loc IO_img XENV_img XENV' XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax
                              LIB_pre LOC0 LOCP CGH Σ usp buf cap cp L pp plen c0b payload
                              gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP)|].
  change (evw 1 [48; 10]) with (evw 1 (emit0_out stdout_init) ++ []).
  eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP XENV' XENV_FP CG LIBP FZ_SITES FZ_CALLS fs AF AF_DRV FUZZC VPR OUT_loc ERR_loc
                             XENV'_loc IO_img XENV_img XENV'_ax XENV'_incb XENV'_upd XENV_fp_ax LOCP CGH); left; reflexivity|].
  change (emit0_next stdout_init) with (so_lines 0).
  intros T c [(K1 & HL)|(K1 & HF)] Hk.
  - eapply (tr_later (Z.to_nat (tr_calls L c0b - 1)) (tr_calls L c0b - 1) 0 usp buf cap x0 x1 x2 x3 x4 x5 eq_refl ltac:(lia) ltac:(lia)
              T c HL).
    intros c' Hc'.
    replace (0 + Z.to_nat (tr_calls L c0b - 1))%nat with (Z.to_nat (tr_calls L c0b) - 1)%nat in Hc' by lia.
    exact (tr_end _ usp buf cap x0 x1 x2 x3 x4 x5 T c' Hc' Hk).
  - rewrite K1 in Hk. change (Z.to_nat 1 - 1)%nat with 0%nat in Hk.
    exact (cpsE_nil asegs _ _ (tr_end (so_lines 0) usp buf cap x0 x1 x2 x3 x4 x5) T c HF Hk).
Qed.

End Tr3.

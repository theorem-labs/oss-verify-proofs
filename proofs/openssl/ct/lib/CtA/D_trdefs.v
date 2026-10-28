(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_libkit D_rlkit D_trpro D_trwalk D_atiface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition tr_live (plen owned buf cap : Z) : list (Z * Z) := (if plen =? 0 then [] else [(owned, plen)]) ++ [(buf, cap)].

Lemma zeros_out_snoc : forall k, zeros_out k ++ [48; 10] = zeros_out (S k).
Proof.
  intros k. unfold zeros_out. induction k as [|k IH]; [reflexivity|].
  change (concat (repeat [48; 10] (S k))) with ([48; 10] ++ concat (repeat [48; 10] k)).
  change (concat (repeat [48; 10] (S (S k)))) with ([48; 10] ++ concat (repeat [48; 10] (S k))).
  rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma emit0_next_lines : forall j, emit0_next (so_lines j) = so_lines (S j).
Proof. intros j. unfold emit0_next, so_lines. cbn. f_equal. apply zeros_out_snoc. Qed.

Lemma emit0_out_lines : forall j, emit0_out (so_lines j) = [].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition incb (b : Z) (m : mem) : Prop := exists p : list byte, rw_cells ctasegs m (TR_INIT + 1) [CB 3 p; C1 (Z_to_bv 8 b)].

Lemma incb_agree : forall b (m m' : mem), incb b m -> agree_on (fun x => TR_INIT + 1 <= x < TR_INIT + 5) m m' -> incb b m'.
Proof.
  intros b m m' (p & C) AG. exists p. apply (rw_cells_agree_nw ctasegs m m' _ _ C).
  eapply agree_sub; [exact AG|]. intros x Hx. destruct C as [[Hw _] _]. cbn in Hw. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

(* [comment removed for export] *)
Lemma tr_cells_join : forall (m : mem) l p b, rw_cells ctasegs m TR_INIT [C1 l] -> rw_cells ctasegs m (TR_INIT + 1) [CB 3 p; C1 b] ->
  rw_cells ctasegs m TR_INIT (tr_cells l p b).
Proof.
  intros m l p b H1 H2. unfold tr_cells. change [C1 l; CB 3 p; C1 b] with ([C1 l] ++ [CB 3 p; C1 b]).
  apply rw_cells_app'. split; [exact H1|]. cbn [cells_size csize Nat.add]. exact H2.
Qed.
Lemma tr_cells_split : forall (m : mem) l p b, rw_cells ctasegs m TR_INIT (tr_cells l p b) -> rw_cells ctasegs m (TR_INIT + 1) [CB 3 p; C1 b].
Proof.
  intros m l p b H. unfold tr_cells in H. change [C1 l; CB 3 p; C1 b] with ([C1 l] ++ [CB 3 p; C1 b]) in H.
  apply rw_cells_app' in H. cbn [cells_size csize Nat.add] in H. exact (proj2 H).
Qed.
Lemma incb_cells : forall b (m : mem), incb b m -> exists l p, rw_cells ctasegs m TR_INIT (tr_cells l p (Z_to_bv 8 b)).
Proof. intros b m (p & C). destruct (latch_exists m) as (l & LT). exists l, p. exact (tr_cells_join m l p _ LT C). Qed.

Section TrDefs.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.
Variable fs : Fs.
#[local] Notation LIB := lib_exit_cells.

(* [comment removed for export] *)
Definition TCTX (Σ : rts RT) (LW : list (Z * Z)) (so : stdout_st) (icb : Z) (usp buf cap plen d owned : Z) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv ctasegs m /\ CLX OUT_rep ERR_rep XENV LIB so m
  /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ tr_frame m (usp - 80) (Z_to_bv 64 0x1f3db8) x0 x1 x2 x3 x4 x5 x6 x7
  /\ stk ctasegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 160)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ Permutation (rt_live RT Σ) (LW ++ tr_live plen owned buf cap) /\ rt_frames RT Σ = []
  /\ plen = Z.of_nat (length payload) /\ plen < 2^26 /\ bytes_at ctasegs m d payload
  /\ (plen = 0 -> d = TR_EMPTY /\ owned = 0) /\ (0 < plen -> d = owned) /\ 0 < cap /\ usp + 16 <= USTACK_TOP
  /\ LIBA Σ LW m /\ incb icb m.

(* [comment removed for export] *)
Definition TLOOP (k : Z) (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (LW : list (Z * Z)) (plen d owned : Z) (payload : list byte)
         (gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 0x1f3fe8) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT) (Z_to_bv 64 k)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)) c
    /\ TCTX Σ LW so 1 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m
    /\ 1 <= k <= 4 /\ k * FUZZ_COST <= rt_credit RT Σ
    /\ lroom3 (rt_live RT Σ) (FUZZ_LIVE + k * KEEP_LIVE + 1) (FUZZ_PB + k * KEEP_PB + LW_MAX) (FUZZ_NB + k * KEEP_NB + 1).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TFREE (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (LW : list (Z * Z)) (plen d owned : Z) (payload : list byte)
         (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 0x1f4014) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) (Z_to_bv 64 (-1)) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)) c
    /\ TCTX Σ LW so 0 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m
    /\ Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX.

(* [comment removed for export] *)
Definition TRET (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (MS (mkR (Z_to_bv 64 0x1f3db8) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1 (Z_to_bv 64 0)
                   a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1f3db8) fc None m (seg_rom ctasegs))) c
    /\ ART RT Σ m /\ mem_inv ctasegs m /\ CLX OUT_rep ERR_rep XENV LIB so m
    /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ stk ctasegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
    /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
    /\ (In (buf, cap) (rt_live RT Σ) /\ Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX) /\ rt_frames RT Σ = [] /\ usp + 16 <= USTACK_TOP
    /\ incb 0 m.

End TrDefs.

Section TrTransport.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.
Hypothesis AF : art_facts RT.
#[local] Notation LIB := lib_exit_cells.

Lemma tr_frame_agree : forall m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7, tr_frame m sp ra x0 x1 x2 x3 x4 x5 x6 x7 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> wmono ctasegs m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7 (junk & FR) AG WM. exists junk.
  apply (rw_cells_agree ctasegs m m' _ _ FR); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

Lemma tr_frame_agree_nw : forall m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7, tr_frame m sp ra x0 x1 x2 x3 x4 x5 x6 x7 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7 (junk & FR) AG. exists junk.
  apply (rw_cells_agree_nw ctasegs m m' _ _ FR). eapply agree_sub; [exact AG|]. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

(* [comment removed for export] *)
Lemma TCTX_agree_nw : forall Σ Σ' LW LW' so so' icb usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m',
  TCTX RT OUT_rep ERR_rep XENV LIBA Σ LW so icb usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> stk ctasegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> Permutation (rt_live RT Σ') (LW' ++ tr_live plen owned buf cap) -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV LIB so' m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  LIBA Σ' LW' m' -> incb icb m' ->
  TCTX RT OUT_rep ERR_rep XENV LIBA Σ' LW' so' icb usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m'.
Proof using AF.
  intros Σ Σ' LW LW' so so' icb usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & LB0 & _)
    ART1 MI1 ST1 ESP ELV EFR CLX1 AGS AGD LB1 IC1.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  split; [apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  rewrite ESP, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact ELV|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree ctasegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact LB1| exact IC1].
Qed.

(* [comment removed for export] *)
Lemma tr_live_in : forall Σ LW plen owned buf cap e, Permutation (rt_live RT Σ) (LW ++ tr_live plen owned buf cap) ->
  In e (tr_live plen owned buf cap) -> In e (rt_live RT Σ).
Proof. intros Σ LW plen owned buf cap e P H. apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. right. exact H. Qed.

Lemma tr_live_in_lw : forall Σ LW plen owned buf cap e, Permutation (rt_live RT Σ) (LW ++ tr_live plen owned buf cap) ->
  In e LW -> In e (rt_live RT Σ).
Proof. intros Σ LW plen owned buf cap e P H. apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. left. exact H. Qed.

End TrTransport.

(* [comment removed for export] *)
Section TrClx.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV1 : mem -> Prop.
Variable XENV1_FP : list (Z * Z).
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV1_loc : fp_local XENV1_FP XENV1.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV1_img : forall x, in_ranges XENV1_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis INCB_off : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> outside IO_FP x /\ outside XENV1_FP x.
Hypothesis ATXW_off : forall x, in_ranges ATX_W x -> outside IO_FP x.

Lemma CLX_switch : forall so (LIBp : mem -> Prop) (m m' : mem) W, CLX OUT_rep ERR_rep XENV LIBp so m -> munch W m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> ~ in_ranges ATX_W x -> outside W x) -> XENV1 m' -> LIBp m' ->
  CLX OUT_rep ERR_rep XENV1 LIBp so m'.
Proof using OUT_loc ERR_loc IO_img ATXW_off.
  intros so LIBp m m' W (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & (l & LT) & CC) MU HW X1 L'.
  assert (AG : agree_on (fun x => in_ranges IO_FP x \/ drv_cell x) m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x [Hx|Hx].
    - apply HW; [exact (client_static_range x (proj1 (IO_img x Hx)))|].
      intros Hin. exact (not_in_ranges_of_outside _ _ (ATXW_off x Hin) Hx).
    - apply HW; [exact (client_static_range x (drv_cell_static x Hx))|].
      intros (lo & hi & Hin & Hr). unfold ATX_W in Hin. unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage in Hx.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [exact X1|].
  split; [exact L'|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right. exact (Hd x Hx). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree ctasegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exact (errno_exists m')|].
  split; [apply (stk_agree_nw ctasegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]|].
  split; [exact (latch_exists m')|].
  unfold cancel_cells in *; apply (rw_cells_agree_nw ctasegs m m' _ _ CC); apply AGD; cbn; unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage; lia.
Qed.

Lemma CLX_incb_munch : forall so (LIBp : mem -> Prop) (m m' : mem) W, fp_local LIB_FP LIBp ->
  CLX OUT_rep ERR_rep XENV1 LIBp so m -> munch W m m' -> wmono ctasegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> ~ (TR_INIT + 1 <= x < TR_INIT + 5) -> outside W x) -> CLX OUT_rep ERR_rep XENV1 LIBp so m'.
Proof using OUT_loc ERR_loc XENV1_loc IO_img XENV1_img INCB_off.
  intros so LIBp m m' W LIB_loc H MU WM HW.
  apply (CLX_agree OUT_rep ERR_rep IO_FP XENV1 XENV1_FP LIBp OUT_loc ERR_loc XENV1_loc LIB_loc so m m' H); [| exact WM].
  apply (agree_of_munch _ _ _ _ MU). intros x Hx.
  apply HW; [exact (CLX_FP_range IO_FP XENV1_FP IO_img XENV1_img x Hx)|].
  intros Hr. destruct (INCB_off x Hr) as [O1 O2].
  destruct Hx as [Hx|[Hx|[Hx|Hx]]].
  - exact (not_in_ranges_of_outside _ _ O1 Hx).
  - exact (not_in_ranges_of_outside _ _ O2 Hx).
  - destruct Hx as (lo & hi & Hin & Hx). unfold LIB_FP in Hin. unfold TR_INIT in Hr.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage in Hx. unfold TR_INIT in Hr. lia.
Qed.

End TrClx.


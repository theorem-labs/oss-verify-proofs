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
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit D_trpro D_trwalk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import D_libiface_pem.
From Stdlib Require Import Permutation.
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
Definition LIBT : mem -> Prop := fun _ => True.
Lemma LIBT_loc : fp_local LIB_FP LIBT.
Proof. intros m m' _ _. exact I. Qed.

(* [comment removed for export] *)
Section ClxT.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Lemma CLX_T_munch_latch : forall so m m' W, CLX OUT_rep ERR_rep XENV LIB so m -> munch W m m' -> wmono asegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> x <> TR_INIT -> outside W x) ->
  (exists v, rw_cells asegs m' TR_INIT [C1 v]) -> CLX OUT_rep ERR_rep XENV LIBT so m'.
Proof using OUT_loc ERR_loc XENV_loc IO_img XENV_img.
  intros so m m' W H MU WM HW LT.
  set (FP' := fun x => (in_ranges IO_FP x \/ in_ranges XENV_FP x \/ drv_cell x) /\ x <> TR_INIT).
  assert (AG : agree_on FP' m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x (Hx & He). apply HW; [| exact He].
    apply client_static_range. destruct Hx as [Hx|[Hx|Hx]]; [exact (proj1 (IO_img x Hx))| exact (proj1 (XENV_img x Hx))| exact (drv_cell_static x Hx)]. }
  destruct H as (H1 & H2 & H3 & _ & (g & SG) & (v & ER) & RS & _).
  assert (NE : forall x, in_ranges IO_FP x \/ in_ranges XENV_FP x -> x <> TR_INIT).
  { intros x [Hx|Hx] Hn; [apply (proj1 (proj2 (IO_img x Hx)))| apply (proj1 (proj2 (XENV_img x Hx)))]; right; right; right; unfold TR_INIT in *; lia. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NE; left; exact Hx]]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NE; left; exact Hx]]|].
  split; [apply (XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [right; left; exact Hx| apply NE; right; exact Hx]]|].
  split; [exact I|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ x <> TR_INIT) ->
                  agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. destruct (Hd x Hx) as [D1 D2]. split; [right; right; exact D1| exact D2]. }
  unfold drv_cell in AGD. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in AGD.
  split; [exists g; apply (ro_cells_agree asegs m m' _ _ SG); apply AGD; cbn; unfold SSP_GUARD; lia|].
  split; [exists v; apply (rw_cells_agree asegs m m' _ _ ER); [apply AGD; cbn; unfold ERRNO_A, TP_A; lia| exact WM]|].
  split; [apply (stk_agree asegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); unfold g_read_stage; lia| cbv beta; lia]| exact WM]|].
  exact LT.
Qed.
(* [comment removed for export] *)
Lemma outside_LIB_W : forall x, outside LIB_FP x -> ~ (ERRNO_A <= x < ERRNO_A + 4) -> outside LIB_W x.
Proof. intros x H NE. unfold LIB_FP in H. unfold LIB_W. cbn [outside] in *. unfold ERRNO_A, TP_A in NE. repeat split; try tauto; lia. Qed.

Lemma CLX_T_cli : forall so m m' live frames sp, CLX OUT_rep ERR_rep XENV LIBT so m -> rt_pres_fp live frames sp LIB_W m m' ->
  (exists v, rw_cells asegs m' ERRNO_A [C4 v]) -> CLX OUT_rep ERR_rep XENV LIBT so m'.
Proof using OUT_loc ERR_loc XENV_loc IO_img XENV_img.
  intros so m m' live frames sp (H1 & H2 & H3 & _ & (g & SG) & _ & RS & (l & LT)) PR ER.
  set (FP' := fun x => in_ranges IO_FP x \/ in_ranges XENV_FP x \/ (drv_cell x /\ ~ (ERRNO_A <= x < ERRNO_A + 4))).
  assert (AG : agree_on FP' m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PR). intros x [Hx|[Hx|[Hx NE]]].
    - destruct (IO_img x Hx) as (CS & ND & OL). split; [right; left; exact CS|]. apply outside_LIB_W; [exact OL|]. intros Hn. apply ND. left. exact Hn.
    - destruct (XENV_img x Hx) as (CS & ND & _ & OL). split; [right; left; exact CS|]. apply outside_LIB_W; [exact OL|]. intros Hn. apply ND. left. exact Hn.
    - split; [right; left; exact (drv_cell_static x Hx)|]. unfold LIB_W. unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in *.
      cbn [outside]. repeat split; try exact I; lia. }
  split; [apply (OUT_loc so m m' H1); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; left; exact Hx]|].
  split; [apply (XENV_loc m m' H3); [apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; right; left; exact Hx]|].
  split; [exact I|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ ~ (ERRNO_A <= x < ERRNO_A + 4)) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. right; right. exact (Hd x Hx). }
  unfold drv_cell in AGD. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in AGD.
  split; [exists g; apply (ro_cells_agree asegs m m' _ _ SG); apply AGD; cbn; unfold SSP_GUARD; lia|].
  split; [exact ER|].
  split; [apply (stk_agree_nw asegs m m' _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); unfold g_read_stage; lia| cbv beta; lia]|].
  exists l. apply (rw_cells_agree_nw asegs m m' _ _ LT); apply AGD; cbn; unfold TR_INIT; lia.
Qed.
End ClxT.

Section TrDefs.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIBP : list (Z * Z) -> mem -> Prop.
Variable CG : cgraph.                (* [comment removed for export] *)
Variable fs : Fs.
Notation LIB := LIBT.

(* [comment removed for export] *)
Definition CLIC (Σ : rts RT) (CL DRV : list (Z * Z)) (m : mem) : Prop :=
  Permutation (rt_live RT Σ) (DRV ++ CL) /\ LIBP CL m /\ Z.of_nat (length CL) <= CLI_MAX /\ (forall p n, In (p, n) CL -> 0 < n)
  /\ rt_cg RT Σ = CG.

(* [comment removed for export] *)
Definition TCTX (Σ : rts RT) (CL : list (Z * Z)) (so : stdout_st) (usp buf cap plen d owned : Z) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB so m
  /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ tr_frame m (usp - 80) (Z_to_bv 64 0x1f2d08) x0 x1 x2 x3 x4 x5
  /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 160)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ CLIC Σ CL (tr_live plen owned buf cap) m /\ rt_frames RT Σ = []
  /\ plen = Z.of_nat (length payload) /\ plen < 2^26 /\ bytes_at asegs m d payload
  /\ (plen = 0 -> d = TR_EMPTY /\ owned = 0) /\ (0 < plen -> d = owned) /\ 0 < cap /\ usp + 16 <= USTACK_TOP.

(* [comment removed for export] *)
Definition TLOOP (k : Z) (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (CL : list (Z * Z)) (plen d owned : Z) (payload : list byte)
         (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (MS (mkR ra (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
                   a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                   s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 p_loop) fc None m (seg_rom asegs))) c
    /\ TCTX Σ CL so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m
    /\ 1 <= k <= 4 /\ k * FUZZ_COST <= rt_credit RT Σ.

(* [comment removed for export] *)
Definition TFREE (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (CL : list (Z * Z)) (plen d owned : Z) (payload : list byte)
         (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 0x1f2f64) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) (Z_to_bv 64 (-1)) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)) c
    /\ TCTX Σ CL so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m.

(* [comment removed for export] *)
Definition TRET (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (CL : list (Z * Z)) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (MS (mkR (Z_to_bv 64 0x1f2d08) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1 (Z_to_bv 64 0)
                   a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1f2d08) fc None m (seg_rom asegs))) c
    /\ ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB so m
    /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
    /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
    /\ CLIC Σ CL [(buf, cap)] m /\ rt_frames RT Σ = [] /\ usp + 16 <= USTACK_TOP.

End TrDefs.

Section TrTransport.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIBP : list (Z * Z) -> mem -> Prop.
Variable CG : cgraph.
Hypothesis AF : art_facts RT.
Notation LIB := LIBT.

Lemma tr_frame_agree : forall m m' sp ra x0 x1 x2 x3 x4 x5, tr_frame m sp ra x0 x1 x2 x3 x4 x5 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> wmono asegs m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5.
Proof.
  intros m m' sp ra x0 x1 x2 x3 x4 x5 (junk & x6 & x7 & FR) AG WM. exists junk, x6, x7.
  apply (rw_cells_agree asegs m m' _ _ FR); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

Lemma tr_frame_agree_nw : forall m m' sp ra x0 x1 x2 x3 x4 x5, tr_frame m sp ra x0 x1 x2 x3 x4 x5 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5.
Proof.
  intros m m' sp ra x0 x1 x2 x3 x4 x5 (junk & x6 & x7 & FR) AG. exists junk, x6, x7.
  apply (rw_cells_agree_nw asegs m m' _ _ FR). eapply agree_sub; [exact AG|]. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

(* [comment removed for export] *)
Lemma TCTX_agree : forall Σ Σ' CL CL' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m m',
  TCTX RT OUT_rep ERR_rep XENV LIBP CG Σ CL so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m ->
  ART RT Σ' m' -> mem_inv asegs m' -> wmono asegs m m' -> stk asegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV LIB so' m' -> CLIC RT LIBP CG Σ' CL' (tr_live plen owned buf cap) m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  TCTX RT OUT_rep ERR_rep XENV LIBP CG Σ' CL' so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m'.
Proof using AF.
  intros Σ Σ' CL CL' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0)
    ART1 MI1 WM ST1 ESP EFR CLX1 LIC1 AGS AGD.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree m m' usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia| exact WM]|].
  split; [apply (tr_frame_agree m m' _ _ _ _ _ _ _ _ TF0); [eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia| exact WM]|].
  rewrite ESP, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
  split; [exact LIC1|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree asegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma TCTX_agree_nw : forall Σ Σ' CL CL' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m m',
  TCTX RT OUT_rep ERR_rep XENV LIBP CG Σ CL so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m ->
  ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV LIB so' m' -> CLIC RT LIBP CG Σ' CL' (tr_live plen owned buf cap) m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  TCTX RT OUT_rep ERR_rep XENV LIBP CG Σ' CL' so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m'.
Proof using AF.
  intros Σ Σ' CL CL' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0)
    ART1 MI1 ST1 ESP EFR CLX1 LIC1 AGS AGD.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  split; [apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  rewrite ESP, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
  split; [exact LIC1|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree asegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

End TrTransport.

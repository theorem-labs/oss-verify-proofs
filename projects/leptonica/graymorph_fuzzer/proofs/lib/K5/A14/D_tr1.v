(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit X_atexit D_trpro D_trwalk D_trdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma tr_calls_range : forall L c0, 1 <= tr_calls L c0 <= 4.
Proof.
  intros L c0. unfold tr_calls. destruct (L =? 0); [lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned c0) (2^2) ltac:(lia)). lia.
Qed.

Section Tr1.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
(* [comment removed for export] *)
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable LIB : mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Hypothesis REG_out : forall m, XENV m -> reg_pre m.
Hypothesis REG_in : forall m m', XENV m ->
  (forall a : word, in_ranges XENV_FP (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
  reg_post m' -> XENV1 m'.
Hypothesis REG_fp : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Definition TPRE (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB stdout_init m /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ CREDIT_DRV - 5 * cap <= rt_credit RT Σ /\ cap <= 67108864
  /\ buf <= cp /\ cp + 1 <= buf + cap /\ (0 < L -> bytes_at asegs m cp [c0b]) /\ 0 <= L < 32768
  /\ buf <= pp /\ pp + plen <= buf + cap /\ bytes_at asegs m pp payload /\ plen = Z.of_nat (length payload) /\ plen < 2^26
  /\ usp + 16 <= USTACK_TOP.

Lemma REG_img : forall x, in_ranges REG_CELLS x -> client_static x /\ ~ drv_cell x /\ ~ in_ranges IO_FP x /\ ~ in_ranges LIB_FP x.
Proof using XENV_img REG_fp.
  intros x Hx. destruct (XENV_img x (REG_fp x Hx)) as (S & D & O1 & O2).
  split; [exact S|]. split; [exact D|]. split; [exact (not_in_ranges_of_outside _ _ O1)| exact (not_in_ranges_of_outside _ _ O2)].
Qed.

Lemma CLX_reg : forall so m m' W,
  CLX OUT_rep ERR_rep XENV LIB so m -> munch W m m' -> wmono asegs m m' ->
  (forall x, 0x10000 <= x < SEGTOP_A -> x <> TR_INIT -> ~ in_ranges REG_CELLS x -> outside W x) ->
  reg_post m' -> (exists v, rw_cells asegs m' TR_INIT [C1 v]) -> CLX OUT_rep ERR_rep XENV1 LIB so m'.
Proof using OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc IO_img XENV_img REG_in REG_fp.
  intros so m m' W H MU WM HW RP LT.
  set (FP' := fun x => CLX_FP IO_FP XENV_FP x /\ x <> TR_INIT /\ ~ in_ranges REG_CELLS x).
  assert (AG : agree_on FP' m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x (Hx & He & Hr). apply HW; [exact (CLX_FP_range IO_FP XENV_FP IO_img XENV_img x Hx)| exact He| exact Hr]. }
  destruct H as (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & _).
  assert (NE : forall x, in_ranges IO_FP x \/ in_ranges LIB_FP x -> x <> TR_INIT /\ ~ in_ranges REG_CELLS x).
  { intros x [Hx|Hx]; split.
    - intros ->. exact (proj1 (proj2 (IO_img _ Hx)) ltac:(right; right; right; unfold TR_INIT; lia)).
    - intros Hr. exact (proj1 (proj2 (proj2 (REG_img x Hr))) Hx).
    - intros ->. exact (proj2 (LIB_img _ Hx) ltac:(right; right; right; unfold TR_INIT; lia)).
    - intros Hr. exact (proj2 (proj2 (proj2 (REG_img x Hr))) Hx). }
  split; [apply (OUT_loc so m m' H1); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NE; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [left; exact Hx| apply NE; left; exact Hx]|].
  split.
  { apply (REG_in m m' H3); [| exact RP]. intros a Ha Hr. apply AG. split; [right; left; exact Ha|]. split; [| exact Hr].
    intros E. apply (proj1 (proj2 (XENV_img _ Ha))). right; right; right. rewrite E. unfold TR_INIT; lia. }
  split; [apply (LIB_loc m m' H4); apply (agree_ranges_sub _ _ _ _ AG); intros x Hx; split; [right; right; left; exact Hx| apply NE; right; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ x <> TR_INIT /\ ~ in_ranges REG_CELLS x) ->
                  agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. destruct (Hd x Hx) as (D1 & D2 & D3). split; [right; right; right; exact D1| split; [exact D2| exact D3]]. }
  assert (AGD' : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ x <> TR_INIT) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. apply AGD. intros x Hx. destruct (Hd x Hx) as [D1 D2]. split; [exact D1|]. split; [exact D2|].
    intros Hr. exact (proj1 (proj2 (REG_img x Hr)) D1). }
  unfold drv_cell in AGD'. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in AGD'.
  split; [exists g; apply (ro_cells_agree asegs m m' _ _ SG); apply AGD'; cbn; unfold SSP_GUARD; lia|].
  split; [exists v; apply (rw_cells_agree asegs m m' _ _ ER); [apply AGD'; cbn; unfold ERRNO_A, TP_A; lia| exact WM]|].
  split; [apply (stk_agree asegs m m' _ _ RS); [eapply agree_sub; [apply (AGD' g_read_stage 65536); unfold g_read_stage; lia| cbv beta; lia]| exact WM]|].
  exact LT.
Qed.

Lemma flag_static : forall x, TR_INIT <= x < TR_INIT + 1 -> client_static x.
Proof. intros x Hx. apply drv_cell_static. right; right; right. exact Hx. Qed.

Theorem tr_start : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  TPRE Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cps asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x8ffec) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (TLOOP RT OUT_rep ERR_rep XENV1 LIB fs (tr_calls L c0b) stdout_init usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using All.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP T c HA Hk.
  destruct HP as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & CR & CAPB & Hcp1 & Hcp2 & HC0 & HL
                  & Hpp1 & Hpp2 & BP & PL & PB & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  pose proof (AF_DRV Σ m ART0) as (_ & _ & GI & _).
  pose proof CLX0 as (_ & _ & XE0 & _ & _ & _ & _ & (l & LT)).
  destruct (REG_out m XE0) as (p1 & p2 & cdt & thr & sec & tm1 & j1 & j2 & ATX & F1 & A1 & LIBC & LATCH).
  pose proof (tr_calls_range L c0b) as TCR.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).
  assert (CSEG : SEGTOP_A <= cp \/ cp + 1 <= 0x10000) by (destruct PR3; [right| left]; lia).
  assert (HWA : forall W, (W = TR_PRO_W (usp - 80) \/ W = (TR_INIT, TR_INIT + 1) :: TR_PRO_W (usp - 80)) ->
            (forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (usp - 208) (bv_unsigned a) -> outside W (bv_unsigned a))
            /\ (forall x, 0x10000 <= x < SEGTOP_A -> x <> TR_INIT -> ~ in_ranges REG_CELLS x -> outside W x)
            /\ (forall x, usp - 80 <= x < USTACK_TOP -> outside W x)
            /\ (forall x, pp <= x < pp + plen -> outside W x)).
  { intros W HWW.
    assert (GEN : forall x, (usp - 208 <= x < usp - 80 -> False) -> (TR_INIT <= x < TR_INIT + 1 -> False) -> (in_ranges REG_CELLS x -> False) -> outside W x).
    { intros x X1 X2 X3. rewrite in_REG_CELLS in X3. unfold TR_INIT in X2.
      destruct HWW as [-> | ->]; unfold TR_PRO_W; cbn [outside]; unfold TR_INIT; repeat split; try exact I; intros Hx; first [apply X1 | apply X2 | apply X3]; lia. }
    split; [| split; [| split]].
    - intros a Ha. apply GEN; intros Hx; apply Ha.
      + left. ul.
      + right; left. apply flag_static. exact Hx.
      + right; left. exact (proj1 (REG_img _ Hx)).
    - intros x Hx Hne Hr. apply GEN; intros Hx'; [ul| unfold TR_INIT in Hne, Hx'; lia| exact (Hr Hx')].
    - intros x Hx. apply GEN; intros Hx'; [ul| unfold TR_INIT in Hx'; ul|]. rewrite in_REG_CELLS in Hx'. ul.
    - intros x Hx. apply GEN; intros Hx'; [ul| unfold TR_INIT in Hx'; destruct PR3; ul|]. rewrite in_REG_CELLS in Hx'. destruct PR3; ul. }
  destruct (Z.eq_dec plen 0) as [Z0|NZ].
  - (* [comment removed for export] *)
    destruct payload as [|b payload]; [| cbn in PL; lia]. cbn in PL. clear PL. subst plen.
    pose proof (tr_pro_empty (usp - 80) cp L pp c0b l p1 p2 cdt thr sec tm1 j1 j2 (Z_to_bv 64 0x8ffec) gp t0 t1 t2 x0 x1 a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST0 ltac:(ul) ltac:(ul) B16' ltac:(ul) ltac:(ul) HL ltac:(ul) ltac:(ul)
                  CSEG HC0 ATX F1 A1 LIBC LATCH LT GI MI0) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA).
    intros cf1 Hc1. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1
                                                & (WM1 & MI1 & TF1 & ST1 & RP1 & LIBC1) & FL1) & Hc1').
    destruct (HWA _ (or_intror eq_refl)) as (HW1 & HW2 & HW3 & HW4).
    assert (ART1 : ART RT Σ m1).
    { apply (af_frame RT AF Σ m m1 (usp - 208) ART0); [ul| |exact WM1]. intros a Ha. apply MU1. apply HW1. exact Ha. }
    assert (CLX1 : CLX OUT_rep ERR_rep XENV1 LIB stdout_init m1).
    { apply (CLX_reg _ m m1 _ CLX0 MU1 WM1 HW2 RP1). eexists. exact FL1. }
    exists Σ, 0, TR_EMPTY, 0, [], gp, u0, u1, u2, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 cp), s8, s9, s10, s11.
    exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F, fc, m1.
    split; [replace (usp - 80 - 80) with (usp - 160) in Hc1' by lia; exact Hc1'|].
    split; [| split; [exact TCR| unfold FUZZ_COST, CREDIT_DRV in *; nia]].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
    split; [apply (main_frame_agree m m1 usp _ _ _ _ _ _ _ _ FR0); [apply (agree_of_munch _ _ _ _ MU1); intros x Hx; apply HW3; ul| exact WM1]|].
    split; [exact TF1|]. split; [replace (usp - 160) with (usp - 80 - 80) by lia; exact ST1|].
    split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
    split; [rewrite LV; reflexivity|]. split; [exact FRS|]. split; [reflexivity|]. split; [lia|].
    split; [apply bytes_at_nil; unfold TR_EMPTY; lia|]. split; [intros _; split; reflexivity|]. split; [intros Hp; lia|]. split; [lia|].
    split; [exact UT0| exact FL1].
  - (* [comment removed for export] *)
    pose proof (tr_pro_copy (usp - 80) cp L pp c0b l p1 p2 cdt thr sec tm1 j1 j2 (Z_to_bv 64 0x8ffec) gp t0 t1 t2 x0 x1 a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST0 ltac:(ul) ltac:(ul) B16' ltac:(ul) ltac:(ul) HL ltac:(ul) ltac:(ul)
                  CSEG HC0 ATX F1 A1 LIBC LATCH LT GI MI0 plen ltac:(lia)) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA).
    intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1
                                                & (WM1 & MI1 & TF1 & ST1 & RP1 & LIBC1) & FL1) & Hc1').
    destruct (HWA _ (or_introl eq_refl)) as (HW1 & HW2 & HW3 & HW4).
    assert (ART1 : ART RT Σ m1).
    { apply (af_frame RT AF Σ m m1 (usp - 208) ART0); [ul| |exact WM1]. intros a Ha. apply MU1. apply HW1. exact Ha. }
    assert (CLX1 : CLX OUT_rep ERR_rep XENV1 LIB stdout_init m1).
    { apply (CLX_reg _ m m1 _ CLX0 MU1 WM1 HW2 RP1). eexists. exact FL1. }
    assert (AGM1 : agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). exact HW3. }
    assert (BP1 : bytes_at asegs m1 pp payload).
    { apply (bytes_at_agree asegs m m1 _ _ BP). apply (agree_of_munch _ _ _ _ MU1). rewrite <- PL. exact HW4. }
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
    replace (usp - 80 - 80) with (usp - 160) in Hc1', ST1 by lia.
    apply (MAL Σ (PMfd fds0 fs) (Z_to_bv 64 0x901ac) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 plen)
             (Z_to_bv 64 pp) (Z_to_bv 64 plen) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_BASE)
             (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 plen lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + lia.
    + rewrite LV. reflexivity.
    + unfold mcost, CREDIT_DRV in *. destruct (Z.leb_spec plen 64512); lia.
    + unfold call_ok. rewrite EU2. split; [exact ST1|]. ul.
    + unfold unwind_ok. rewrite EU2, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
    + intros cf2 (Σ1 & owned & Hc2 & LV1 & FRS1 & SP1 & CR1 & Pow & Pal & Ptop).
      destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2').
      destruct RS2 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & ->).
      rewrite EU2 in ST2, PRES2.
      rewrite (ret_pc_even 0x901ac) in Hc2' by lia.
      assert (INO : In (owned, plen) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
      assert (INB1 : In (buf, cap) (rt_live RT Σ1)) by (rewrite LV1, LV; right; left; reflexivity).
      assert (DISJ : owned + plen <= buf \/ buf + cap <= owned).
      { apply (af_live_disj RT AF Σ1 m2 owned plen buf cap [] [(buf, cap)] ART2); [rewrite LV1, LV; reflexivity| left; reflexivity]. }
      pose proof (af_live_range RT AF Σ1 m2 owned plen ART2 INO) as (OR1 & OR2 & OR3).
      assert (CLX2 : CLX OUT_rep ERR_rep XENV1 LIB stdout_init m2) by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc
                                                                              XENV1_loc LIB_loc IO_img XENV_img _ m1 m2 _ _ _ CLX1 PRES2 WM2).
      pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.
      assert (BP2 : bytes_at asegs m2 pp payload).
      { apply (bytes_at_agree asegs m1 m2 _ _ BP1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx.
        rewrite <- PL in Hx. right; right; left. exists buf, cap. split; [exact INB| lia]. }
      assert (FL2 : rw_cells asegs m2 TR_INIT [C1 l]).
      { apply (rw_cells_agree asegs m1 m2 _ _ FL1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx.
        right; left. apply flag_static. cbn [cells_size csize Nat.add] in Hx. lia. }
      pose proof (tr_copy_walk (usp - 160) owned gp v0 v1 v2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) d1 d2 d3 d4 d5 d6 d7
                    (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_BASE) (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11
                    v3 v4 v5 v6 F2 fc2 m2 ltac:(ul) MI2) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W2') Hc2').
      intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & <- & Hc3').
      apply (MCP Σ1 (PMfd fds0 fs) (Z_to_bv 64 0x901c0) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) v0 v1 v2 (Z_to_bv 64 plen)
               (Z_to_bv 64 pp) (Z_to_bv 64 owned) (Z_to_bv 64 pp) (Z_to_bv 64 plen) d3 d4 d5 d6 d7 (Z_to_bv 64 owned) (Z_to_bv 64 cp)
               (Z_to_bv 64 TR_BASE) (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11 v3 v4 v5 v6 F2 fc2 m2 owned pp payload lo);
        try reflexivity; try assumption.
      * apply PMfd_fdfs_only.
      * apply PMfd_mat_stable.
      * rewrite <- PL. reflexivity.
      * ul.
      * ul.
      * lia.
      * rewrite <- PL. exact (checked_src_live RT AF Σ1 m2 _ lo buf cap pp plen ART2 INB1 ltac:(lia) ltac:(lia) ltac:(rewrite SP1; lia)).
      * rewrite <- PL. exact (checked_dst_live RT AF Σ1 m2 _ owned plen owned plen ART2 INO ltac:(lia) ltac:(lia) ltac:(lia)).
      * rewrite <- PL. lia.
      * unfold call_ok. rewrite EU2, SP1. split; [exact ST2|]. ul.
      * intros cf4 Hc4.
        destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BS3) & Hc4').
        destruct RS3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
        rewrite EU2 in ST3, PRES3. rewrite <- PL in PRES3.
        rewrite (ret_pc_even 0x901c0) in Hc4' by lia.
        assert (CLX3 : CLX OUT_rep ERR_rep XENV1 LIB stdout_init m3)
          by exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img
                      _ m2 m3 _ _ _ _ _ CLX2 PRES3 WM3 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
        pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES3 ltac:(ul)) as AG3.
        assert (FL3 : rw_cells asegs m3 TR_INIT [C1 l]).
        { apply (rw_cells_agree asegs m2 m3 _ _ FL2); [| exact WM3]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3). intros x Hx.
          cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply flag_static; lia| unfold TR_INIT, SEGTOP_A in *; lia]. }
        pose proof (tr_copy_ret_walk (usp - 160) owned gp w0 w1 w2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 owned) e1 e2 e3 e4 e5
                      e6 e7 (Z_to_bv 64 cp) (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 l FL3 MI3) as W3.
        lazymatch type of W3 with evt asegs _ ?X =>
          assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
        clear W3.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc4').
        intros cf5 Hc5. apply Hk.
        destruct (ASTA_unpack RT Σ1 _ _ cf5 Hc5) as (ms5 & (m4 & -> & MU4 & WM4 & MI4 & FL4) & Hc5').
        assert (HWF : forall x, TR_INIT <= x < TR_INIT + 1 \/ outside [(TR_INIT, TR_INIT + 1)] x).
        { intros x. cbn [outside]. lia. }
        assert (ART4 : ART RT Σ1 m4).
        { apply (af_frame RT AF Σ1 m3 m4 (usp - 160) ART3); [rewrite SP1; ul| |exact WM4]. intros a Ha. apply MU4.
          destruct (HWF (bv_unsigned a)) as [Hx|Hx]; [| exact Hx]. exfalso. apply Ha. right; left. apply flag_static. exact Hx. }
        assert (CLX4 : CLX OUT_rep ERR_rep XENV1 LIB stdout_init m4).
        { apply (CLX_munch_latch OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img _ m3 m4 _ CLX3 MU4 WM4);
            [| eexists; exact FL4]. intros x Hx Hne. cbn [outside]. split; [lia| exact I]. }
        assert (AG34 : agree_on (fun x => outside [(TR_INIT, TR_INIT + 1)] x) m3 m4) by (apply (agree_of_munch _ _ _ _ MU4); intros x Hx; exact Hx).
        exists Σ1, plen, owned, owned, payload, gp, w0, w1, w2, e2, e3, e4, e5, e6, e7, (Z_to_bv 64 cp), s8, s9, s10, s11.
        exists w3, w4, w5, w6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4.
        split; [exact Hc5'|]. split; [| split; [exact TCR| rewrite CR1; unfold mcost, FUZZ_COST, CREDIT_DRV in *;
                                                 destruct (Z.leb_spec plen 64512); nia]].
        assert (AG13 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m3).
        { apply (agree_trans _ m1 m2 m3); [eapply agree_sub; [exact AG2|]; intros x Hx; cbv beta in *; lia|].
          eapply agree_sub; [exact AG3|]. intros x Hx; cbv beta in *; lia. }
        assert (AG14 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m4).
        { apply (agree_trans _ m1 m3 m4); [exact AG13|]. eapply agree_sub; [exact AG34|]. intros x Hx. cbn [outside]. unfold TR_INIT. split; [ul| exact I]. }
        split; [exact ART4|]. split; [exact MI4|]. split; [exact CLX4|].
        split; [apply (main_frame_agree m m4 usp _ _ _ _ _ _ _ _ FR0); [apply (agree_trans _ m m1 m4);
                 [eapply agree_sub; [exact AGM1|]; intros x Hx; cbv beta in *; ul| eapply agree_sub; [exact AG14|]; intros x Hx; cbv beta in *; ul]
                | exact (wmono_trans asegs m m1 m4 WM1 (wmono_trans asegs m1 m3 m4 (wmono_trans asegs m1 m2 m3 WM2 WM3) WM4))]|].
        split; [apply (tr_frame_agree m1 m4 _ _ _ _ _ _ _ _ _ _ TF1); [eapply agree_sub; [exact AG14|]; intros x Hx; cbv beta in *; lia
                | exact (wmono_trans asegs m1 m3 m4 (wmono_trans asegs m1 m2 m3 WM2 WM3) WM4)]|].
        rewrite SP1. split.
        { apply (stk_agree asegs m3 m4 _ _ ST3); [| exact WM4]. eapply agree_sub; [exact AG34|]. intros x Hx. cbn [outside]. unfold TR_INIT. split; [ul| exact I]. }
        split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
        split; [rewrite LV1, LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity|].
        split; [rewrite FRS1; exact FRS|]. split; [exact PL|]. split; [lia|].
        split; [apply (bytes_at_agree asegs m3 m4 _ _ BS3); eapply agree_sub; [exact AG34|]; intros x Hx; cbn [outside]; unfold TR_INIT, SEGTOP_A in *; split; [lia| exact I]|].
        split; [intros Hp; lia|]. split; [intros _; reflexivity|]. split; [lia|]. split; [exact UT0| exact FL4].
Qed.

End Tr1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_agree D_libiface D_clx D_rlkit D_libiface_pem X_ax D_trpro D_trwalk D_trdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma tr_calls_range : forall L c0, 1 <= tr_calls L c0 <= 4.
Proof.
  intros L c0. unfold tr_calls. destruct (L =? 0); [lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned c0) (2^2) ltac:(lia)). lia.
Qed.

Lemma errno_A' : errno_cell (Z_to_bv 64 TP_A) = ERRNO_A.
Proof. unfold errno_cell, ERRNO_A, TP_A. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma LIBW_outside_hi : forall x, SEGTOP_A <= x -> outside LIB_W x.
Proof. intros x Hx. unfold LIB_W, SEGTOP_A in *. cbn [outside]. repeat split; try exact I; lia. Qed.
Lemma LIBW_outside_lo : forall x, x < 0x10000 -> outside LIB_W x.
Proof. intros x Hx. unfold LIB_W in *. cbn [outside]. repeat split; try exact I; lia. Qed.
(* [comment removed for export] *)
Lemma LIBD_static : forall x, in_ranges LIB_D x -> client_static x /\ ~ drv_cell x.
Proof.
  intros x (lo & hi & Hin & Hx). unfold LIB_D in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [apply client_static_intro; lia|]);
    unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT; lia|]). destruct Hin.
Qed.

Section Tr1.
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
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis INITC : fuzz_init_cps RT LIB0P LIBP FZ_SITES FZ_CALLS.
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
(* [comment removed for export] *)
Hypothesis LIB_pre : forall m, LIB m -> LIB0P m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].
Hypothesis LOC0 : lib0_local_d LIB0P.
Hypothesis LOCP : lib_local_d LIBP.
Hypothesis CGH : cg_has CG FZ_SITES FZ_CALLS.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, INIT_COST, LIVE_MAX, CLI_MAX, FUZZ_LIVE, g_read_stage in *; lia.

(* [comment removed for export] *)
Lemma CLX_T_after_pro : forall so m m' sp fin p1 p2,
  CLX OUT_rep ERR_rep XENV LIB so m -> munch (pro_W sp) m m' -> wmono asegs m m' -> SEGTOP_A + 128 <= sp ->
  ax_chunks true fin p1 p2 m' -> (exists v, rw_cells asegs m' TR_INIT [C1 v]) -> CLX OUT_rep ERR_rep XENV' LIBT so m'.
Proof using OUT_loc ERR_loc IO_img XENV_img XENV_incb XENV_step XENV_fp_ax.
  intros so m m' sp fin p1 p2 (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & _) MU WM SP AX LT.
  set (AXP := fun x => 0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INIT).
  assert (AG : agree_on (fun x => 0x10000 <= x < SEGTOP_A /\ ~ AXP x) m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x [Hx Hn]. unfold AXP, TR_INIT in Hn. unfold pro_W, TR_INIT, SEGTOP_A in *. cbn.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I]. }
  assert (NIO : forall x, in_ranges IO_FP x -> ~ AXP x).
  { intros x Hx HA. destruct (IO_img x Hx) as (_ & ND & _). unfold AXP in HA. destruct HA as [HA|[HA|HA]].
    - exact (not_in_ranges_of_outside _ _ (proj1 (proj2 (proj2 (XENV_img x (XENV_fp_ax x ltac:(left; exact HA)))))) Hx).
    - exact (not_in_ranges_of_outside _ _ (proj1 (proj2 (proj2 (XENV_img x (XENV_fp_ax x ltac:(right; left; exact HA)))))) Hx).
    - apply ND. rewrite HA. unfold drv_cell, TR_INIT. lia. }
  split; [apply (OUT_loc so m m' H1); eapply agree_sub; [exact AG|]; intros x Hx; split; [exact (client_static_range x (proj1 (IO_img x Hx)))| exact (NIO x Hx)]|].
  split; [apply (ERR_loc m m' H2); eapply agree_sub; [exact AG|]; intros x Hx; split; [exact (client_static_range x (proj1 (IO_img x Hx)))| exact (NIO x Hx)]|].
  split.
  { apply (XENV_step m m' H3).
    - eapply agree_sub; [exact AG|]. intros x (Hx & N1 & N2 & N3). split; [exact (client_static_range x (proj1 (XENV_img x Hx)))|].
      unfold AXP. intros [A|[A|A]]; [exact (N1 A)| exact (N2 A)|].
      apply (proj1 (proj2 (XENV_img x Hx))). rewrite A. unfold drv_cell, TR_INIT. lia.
    - exists fin, p1, p2. exact AX.
    - apply (rw_cells_agree asegs m m' _ _ (XENV_incb m H3)); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. unfold AXP, TR_INIT, TR_INCB, SEGTOP_A in *. cbv beta. lia. }
  split; [exact I|].
  split; [exists g; apply (ro_cells_agree asegs m m' _ _ SG); eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx;
          unfold AXP, SSP_GUARD, TR_INIT, SEGTOP_A in *; cbv beta in *; lia|].
  split; [exists v; apply (rw_cells_agree asegs m m' _ _ ER); [| exact WM]; eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx;
          unfold AXP, ERRNO_A, TP_A, TR_INIT, SEGTOP_A in *; cbv beta in *; lia|].
  split; [apply (stk_agree asegs m m' _ _ RS); [| exact WM]; eapply agree_sub; [exact AG|]; intros x Hx; unfold AXP, g_read_stage, TR_INIT, SEGTOP_A in *; cbv beta in *; lia|].
  exact LT.
Qed.

(* [comment removed for export] *)
Definition TPRE (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB stdout_init m /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ CREDIT_DRV - 5 * cap <= rt_credit RT Σ /\ cap <= 67108864
  /\ buf <= cp /\ cp + 1 <= buf + cap /\ (0 < L -> bytes_at asegs m cp [c0b]) /\ 0 <= L < 32768
  /\ buf <= pp /\ pp + plen <= buf + cap /\ bytes_at asegs m pp payload /\ plen = Z.of_nat (length payload) /\ plen < 2^26
  /\ usp + 16 <= USTACK_TOP /\ rt_cg RT Σ = CG.

Theorem tr_start : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  TPRE Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cps asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x1f2d08) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (TLOOP RT OUT_rep ERR_rep XENV' LIBP CG fs (tr_calls L c0b) stdout_init usp buf cap x0 x1 x2 x3 x4 x5).
Proof using AF AF_DRV MAL MCP INITC OUT_loc ERR_loc XENV_loc IO_img XENV_img LIB_pre LOC0 LOCP CGH XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP T c HA Hk.
  destruct HP as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & CR & CAPB & Hcp1 & Hcp2 & HC0 & HL
                  & Hpp1 & Hpp2 & BP & PL & PB & UT0 & HCG).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  pose proof (AF_DRV Σ m ART0) as (_ & _ & GI & _).
  pose proof CLX0 as (_ & _ & XE0 & HLIB & _ & _ & _ & _).
  destruct (LIB_pre m HLIB) as [L0 LT].
  destruct (XENV_ax m XE0) as (fin & p1 & p2 & AXC). pose proof (XENV_libc m XE0) as LC0.
  pose proof (tr_calls_range L c0b) as TCR.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).
  assert (B16'' : (usp - 160) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia).
  assert (CSEG : SEGTOP_A <= cp \/ cp + 1 <= 0x10000) by (destruct PR3; [right| left]; lia).
  (* [comment removed for export] *)
  pose proof (tr_pro_init (usp - 80) cp L pp plen fin p1 p2 (Z_to_bv 64 0x1f2d08) gp t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7
                s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST0 ltac:(ul) ltac:(ul) B16' ltac:(ul) ltac:(ul) HL ltac:(ul) ltac:(ul)
                LT AXC LC0 GI MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA).
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m1 & ->
                                               & MU1 & WM1 & MI1 & TF1 & ST1 & LT1 & AX1 & LC1) & Hc1').
  replace (usp - 80 - 80) with (usp - 160) in Hc1' by lia. replace (usp - 80 - 80) with (usp - 160) in ST1 by lia.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 208) ART0); [ul| |exact WM1].
    intros a Ha. apply MU1. unfold pro_W, TR_INIT. cbn [outside]. split; [intros Hin; apply Ha; left; ul|].
    split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
    split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
    split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I]. }
  assert (CLX1 : CLX OUT_rep ERR_rep XENV' LIBT stdout_init m1)
    by exact (CLX_T_after_pro _ m m1 (usp - 80) (Z_to_bv 8 0) p1 p2 CLX0 MU1 WM1 ltac:(ul) AX1 ltac:(exists (Z_to_bv 8 1); exact LT1)).
  assert (L01 : LIB0P m1).
  { apply (LOC0 m m1 L0). intros a Ha. apply MU1. destruct (LIBD_static _ Ha) as [CS ND].
    pose proof (client_static_range _ CS) as R. unfold pro_W, TR_INIT. cbn [outside]. split; [ul|].
    destruct Ha as (l1 & h1 & Hin & Hlh). unfold LIB_D in Hin.
    split; [intros Hx; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin|].
    split; [intros Hx; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin|].
    split; [intros Hx; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin| exact I]. }
  assert (AGM1 : agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold pro_W, TR_INIT. cbn. split; [lia|]. split; [ul|]. split; [ul|]. split; [ul| exact I]. }
  assert (BP1 : bytes_at asegs m1 pp payload).
  { apply (bytes_at_agree asegs m m1 _ _ BP). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold pro_W, TR_INIT. cbn.
    rewrite <- PL in Hx. split; [ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul| exact I]. }
  assert (HC01 : 0 < L -> bytes_at asegs m1 cp [c0b]).
  { intros HLp. apply (bytes_at_agree asegs m m1 _ _ (HC0 HLp)). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold pro_W, TR_INIT. cbn in Hx |- *.
    split; [ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul| exact I]. }
  (* [comment removed for export] *)
  apply (INITC Σ (PMfd fds0 fs) (Z_to_bv 64 RA_TR_INIT) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
           (Z_to_bv 64 pp) (Z_to_bv 64 0x5a9f08) (Z_to_bv 64 (usp - 160)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) x5
           s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - intros p n Hin. rewrite LV in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. lia.
  - rewrite LV. cbn [length Z.of_nat Pos.of_succ_nat]. ul.
  - ul.
  - unfold fp_invalid. rewrite EU2, !unsigned_lit by ul. left. ul.
  - rewrite HCG. exact CGH.
  - io_ssp_tac AF_DRV.
  - rewrite errno_A'. destruct CLX1 as (_ & _ & _ & _ & _ & ER1 & _). exact ER1.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact B16''.
  - rewrite EU2. lia.
  - intros cf2 (Σi & CL & Hc2 & PERM & LEN & POS & FRSi & SPi & CRi & CGi).
    destruct (ASTA_unpack RT Σi _ _ cf2 Hc2) as (ms2 & (mi & RSi & (ARTi & MIi & STi) & PRESi & LIBi & ERRi) & Hc2').
    destruct RSi as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fi & fci & ->).
    rewrite EU2 in STi, PRESi. rewrite errno_A' in ERRi.
    unfold RA_TR_INIT in Hc2'. rewrite (ret_pc_even 0x1f2fc0) in Hc2' by lia. fold RA_TR_INIT in Hc2'.

    unfold cli_pres in PRESi.
    assert (CLXi : CLX OUT_rep ERR_rep XENV' LIBT stdout_init mi)
      by exact (CLX_T_cli OUT_rep ERR_rep IO_FP XENV' XENV_FP OUT_loc ERR_loc XENV'_loc IO_img XENV_img _ m1 mi _ _ _ CLX1 PRESi ERRi).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRESi ltac:(intros x Hx; apply LIBW_outside_hi; ul)) as AGi.
    assert (AGB : agree_on (fun x => buf <= x < buf + cap) m1 mi).
    { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRESi). intros x Hx. split; [right; right; left; exists buf, cap; split; [exact INB| lia]|].
      destruct PR3 as [R3|R3]; [apply LIBW_outside_lo; lia| apply LIBW_outside_hi; lia]. }
    assert (TFi : tr_frame mi (usp - 80) (Z_to_bv 64 0x1f2d08) x0 x1 x2 x3 x4 x5).
    { apply (tr_frame_agree_nw m1 mi _ _ _ _ _ _ _ _ TF1). eapply agree_sub; [exact AGi|]. intros x Hx; cbv beta in *; ul. }
    assert (FRi : main_frame mi usp c0 c1 c2 c3 c4 c5 c6 c7).
    { apply (main_frame_agree_nw m mi usp _ _ _ _ _ _ _ _ FR0). apply (agree_trans _ m m1 mi).
      - eapply agree_sub; [exact AGM1|]. intros x Hx; cbv beta in *; ul.
      - eapply agree_sub; [exact AGi|]. intros x Hx; cbv beta in *; ul. }
    assert (BPi : bytes_at asegs mi pp payload).
    { apply (bytes_at_agree asegs m1 mi _ _ BP1). eapply agree_sub; [exact AGB|]. intros x Hx; cbv beta in *. rewrite <- PL in Hx. lia. }
    assert (HC0i : 0 < L -> bytes_at asegs mi cp [c0b]).
    { intros HLp. apply (bytes_at_agree asegs m1 mi _ _ (HC01 HLp)). eapply agree_sub; [exact AGB|]. intros x Hx; cbv beta in *. cbn in Hx. lia. }
    assert (LVi : Permutation (rt_live RT Σi) ([(buf, cap)] ++ CL)) by (rewrite LV in PERM; exact (Permutation_trans PERM (Permutation_app_comm _ _))).
    assert (INBi : In (buf, cap) (rt_live RT Σi)) by (apply (Permutation_in _ (Permutation_sym LVi)); left; reflexivity).
    assert (LENi : Z.of_nat (length (rt_live RT Σi)) = Z.of_nat (length CL) + 1).
    { rewrite (Permutation_length LVi). cbn [length app]. lia. }
    clear W1'.
    destruct (Z.eq_dec plen 0) as [Z0|NZ].
    + (* [comment removed for export] *)
      destruct payload as [|b payload]; [| cbn in PL; lia]. cbn in PL. clear PL. subst plen.
      pose proof (tr_pro_empty (usp - 160) cp L pp c0b gp u0 u1 u2 (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7 x5 s6 s7
                    s8 s9 s10 s11 u3 u4 u5 u6 Fi fci mi ltac:(ul) HL HC0i CSEG MIi) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σi _ fs _ _ W2') Hc2').
      intros cf3 Hc3. apply Hk.
      destruct (ASTA_unpack RT Σi _ _ cf3 Hc3) as (ms3 & (a0'' & ->) & Hc3').
      exists Σi, CL, 0, TR_EMPTY, 0, [], (Z_to_bv 64 RA_TR_INIT), gp, u0, u1, u2, a0'', b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 cp), s8, s9, s10, s11.
      exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, Fi, fci, mi.
      split; [exact Hc3'|].
      split; [| split; [exact TCR| ul]].
      split; [exact ARTi|]. split; [exact MIi|]. split; [exact CLXi|]. split; [exact FRi|]. split; [exact TFi|].
      rewrite SPi. split; [exact STi|].
      split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
      split; [split; [exact LVi|]; split; [exact LIBi|]; split; [exact LEN|]; split; [exact POS| rewrite CGi; exact HCG]|].
      split; [exact FRSi|]. split; [reflexivity|]. split; [lia|].
      split; [apply bytes_at_nil; unfold TR_EMPTY; lia|]. split; [intros _; split; reflexivity|]. split; [intros Hp; lia|]. split; [lia| exact UT0].
    + (* [comment removed for export] *)
      pose proof (tr_pro_copy (usp - 160) cp L pp plen c0b gp u0 u1 u2 (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7 x5 s6 s7
                    s8 s9 s10 s11 u3 u4 u5 u6 Fi fci mi ltac:(ul) HL ltac:(lia) HC0i CSEG MIi) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σi _ fs _ _ W2') Hc2').
      intros cf3 Hc3.
      destruct (ASTA_unpack RT Σi _ _ cf3 Hc3) as (ms3 & <- & Hc3').
      apply (MAL Σi (PMfd fds0 fs) (Z_to_bv 64 0x1f2ecc) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 plen)
               (Z_to_bv 64 pp) (Z_to_bv 64 plen) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT)
               (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Fi fci mi plen lo); try reflexivity; try assumption.
      * apply PMfd_fdfs_only.
      * apply PMfd_mat_stable.
      * lia.
      * rewrite LENi. ul.
      * unfold mcost in *. destruct (Z.leb_spec plen 64512); ul.
      * unfold call_ok. rewrite EU2, SPi. split; [exact STi|]. ul.
      * unfold unwind_ok, fp_invalid. rewrite EU2, !unsigned_lit by ul. left. split; [cbn; tauto|]. left. ul.
      * intros cf4 (Σ1 & owned & Hc4 & LV1 & FRS1 & SP1 & CR1 & Pow & Pal & Ptop & CG1).
        destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc4').
        destruct RS2 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & ->).
        rewrite EU2 in ST2, PRES2.
        rewrite (ret_pc_even 0x1f2ecc) in Hc4' by lia.
        assert (INO : In (owned, plen) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
        assert (INB1 : In (buf, cap) (rt_live RT Σ1)) by (rewrite LV1; right; exact INBi).
        assert (LV1' : Permutation (rt_live RT Σ1) ((owned, plen) :: [(buf, cap)] ++ CL)) by (rewrite LV1; apply perm_skip; exact LVi).
        assert (DISJ : forall p n, In (p, n) (rt_live RT Σi) -> owned + plen <= p \/ p + n <= owned).
        { intros p n Hin. exact (af_live_disj RT AF Σ1 m2 owned plen p n [] (rt_live RT Σi) ART2 ltac:(rewrite LV1; reflexivity) Hin). }
        pose proof (af_live_range RT AF Σ1 m2 owned plen ART2 INO) as (OR1 & OR2 & OR3).
        assert (CLX2 : CLX OUT_rep ERR_rep XENV' LIBT stdout_init m2)
          by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV' XENV_FP LIBT OUT_loc ERR_loc XENV'_loc LIBT_loc IO_img XENV_img _ mi m2 _ _ _ CLXi PRES2 WM2).
        pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.
        assert (AGL2 : forall a : word, in_ranges LIB_D (bv_unsigned a) \/ in_live CL (bv_unsigned a) -> m2 a = mi a).
        { intros a [Ha|Ha]; apply PRES2.
          - right; left. exact (proj1 (LIBD_static _ Ha)).
          - right; right; left. destruct Ha as (p & n & Hin & Hr). exists p, n. split; [| exact Hr].
            apply (Permutation_in _ (Permutation_sym LVi)). right. exact Hin. }
        assert (LIB2 : LIBP CL m2) by exact (LOCP CL mi m2 LIBi AGL2).
        assert (BP2 : bytes_at asegs m2 pp payload).
        { apply (bytes_at_agree asegs mi m2 _ _ BPi). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx.
          rewrite <- PL in Hx. right; right; left. exists buf, cap. split; [exact INBi| lia]. }
        (* [comment removed for export] *)
        pose proof (tr_copy_walk (usp - 160) owned gp v0 v1 v2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) d1 d2 d3 d4 d5 d6 d7
                      (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11
                      v3 v4 v5 v6 F2 fc2 m2 ltac:(ul) MI2) as W3.
        lazymatch type of W3 with evt asegs _ ?X =>
          assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
        clear W3.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc4').
        intros cf5 Hc5.
        destruct (ASTA_unpack RT Σ1 _ _ cf5 Hc5) as (ms5 & <- & Hc5').
        apply (MCP Σ1 (PMfd fds0 fs) (Z_to_bv 64 0x1f2ee0) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) v0 v1 v2 (Z_to_bv 64 plen)
                 (Z_to_bv 64 pp) (Z_to_bv 64 owned) (Z_to_bv 64 pp) (Z_to_bv 64 plen) d3 d4 d5 d6 d7 (Z_to_bv 64 owned) (Z_to_bv 64 cp)
                 (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F2 fc2 m2 owned pp payload lo);
          try reflexivity; try assumption.
        -- apply PMfd_fdfs_only.
        -- apply PMfd_mat_stable.
        -- rewrite <- PL. reflexivity.
        -- ul.
        -- ul.
        -- lia.
        -- rewrite <- PL. exact (checked_src_live RT AF Σ1 m2 _ lo buf cap pp plen ART2 INB1 ltac:(lia) ltac:(lia) ltac:(rewrite SP1, SPi; lia)).
        -- rewrite <- PL. exact (checked_dst_live RT AF Σ1 m2 _ owned plen owned plen ART2 INO ltac:(lia) ltac:(lia) ltac:(lia)).
        -- rewrite <- PL. destruct (DISJ buf cap INBi); lia.
        -- unfold call_ok. rewrite EU2, SP1, SPi. split; [exact ST2|]. ul.
        -- intros cf6 Hc6.
           destruct (ASTA_unpack RT Σ1 _ _ cf6 Hc6) as (ms6 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BS3) & Hc6').
           destruct RS3 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
           rewrite EU2 in ST3, PRES3. rewrite <- PL in PRES3.
           rewrite (ret_pc_even 0x1f2ee0) in Hc6' by lia.
           assert (CLX3 : CLX OUT_rep ERR_rep XENV' LIBT stdout_init m3)
             by exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV' XENV_FP LIBT OUT_loc ERR_loc XENV'_loc LIBT_loc IO_img XENV_img
                         _ m2 m3 _ _ _ _ _ CLX2 PRES3 WM3 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
           pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES3 ltac:(ul)) as AG3.
           assert (AGL3 : forall a : word, in_ranges LIB_D (bv_unsigned a) \/ in_live CL (bv_unsigned a) -> m3 a = m2 a).
           { intros a [Ha|Ha]; apply PRES3.
             - right; left. exact (proj1 (LIBD_static _ Ha)).
             - pose proof (client_static_range _ (proj1 (LIBD_static _ Ha))) as R. unfold SEGTOP_A in *. lia.
             - right; right; left. destruct Ha as (p & n & Hin & Hr). exists p, n. split; [| exact Hr].
               apply (Permutation_in _ (Permutation_sym LV1')). right; right. exact Hin.
             - destruct Ha as (p & n & Hin & Hr).
               destruct (DISJ p n ltac:(apply (Permutation_in _ (Permutation_sym LVi)); right; exact Hin)); lia. }
           assert (LIB3 : LIBP CL m3) by exact (LOCP CL m2 m3 LIB2 AGL3).
           (* [comment removed for export] *)
           pose proof (tr_copy_ret_walk (usp - 160) owned gp w0 w1 w2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 owned) e1 e2 e3 e4 e5
                         e6 e7 (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
                         F3 fc3 m3 MI3) as W4.
           lazymatch type of W4 with evt asegs _ ?X =>
             assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
           clear W4.
           apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W4') Hc6').
           intros cf7 Hc7. apply Hk.
           destruct (ASTA_unpack RT Σ1 _ _ cf7 Hc7) as (ms7 & <- & Hc7').
           exists Σ1, CL, plen, owned, owned, payload, (Z_to_bv 64 0x1f2ee0), gp, w0, w1, w2, (Z_to_bv 64 owned), e1, e2, e3, e4, e5, e6, e7,
                  (Z_to_bv 64 cp), s8, s9, s10, s11.
           exists w3, w4, w5, w6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
           split; [exact Hc7'|]. split; [| split; [exact TCR| rewrite CR1; unfold mcost in *; destruct (Z.leb_spec plen 64512); ul]].
           assert (AG13 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) mi m3).
           { apply (agree_trans _ mi m2 m3); [eapply agree_sub; [exact AG2|]; intros x Hx; cbv beta in *; lia|].
             eapply agree_sub; [exact AG3|]. intros x Hx; cbv beta in *; lia. }
           split; [exact ART3|]. split; [exact MI3|]. split; [exact CLX3|].
           split; [apply (main_frame_agree_nw mi m3 usp _ _ _ _ _ _ _ _ FRi); eapply agree_sub; [exact AG13|]; intros x Hx; cbv beta in *; ul|].
           split; [apply (tr_frame_agree_nw mi m3 _ _ _ _ _ _ _ _ TFi); eapply agree_sub; [exact AG13|]; intros x Hx; cbv beta in *; lia|].
           rewrite SP1, SPi. split; [exact ST3|].
           split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
           split; [split; [unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); exact LV1'|]; split; [exact LIB3|]; split; [exact LEN|];
                   split; [exact POS| rewrite CG1, CGi; exact HCG]|].
           split; [rewrite FRS1; exact FRSi|]. split; [exact PL|]. split; [lia|]. split; [exact BS3|].
           split; [intros Hp; lia|]. split; [intros _; reflexivity|]. split; [lia| exact UT0].
Qed.

End Tr1.

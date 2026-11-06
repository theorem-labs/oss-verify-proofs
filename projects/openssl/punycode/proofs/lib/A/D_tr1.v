(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit
  X_ax D_trpro D_trwalk D_trdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Hypothesis XENV_ax : forall m, XENV m -> exists k fin p1 p2, AXA k fin p1 p2 m.
Hypothesis XENV_libc : forall m, XENV m -> libc_cells m.
Hypothesis XENV_incb : forall m, XENV m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV_upd : forall m m', XENV m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc7f20 <= x < 0xbc7f50) /\ ~ (0xbc8040 <= x < 0xbc8050) /\ x <> TR_INIT /\ x <> TR_INCB) m m' ->
  (exists k fin p1 p2, AXA k fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV m'.
Hypothesis XENV_fp_ax : forall x, (0xbc7f20 <= x < 0xbc7f50 \/ 0xbc8040 <= x < 0xbc8050 \/ x = TR_INIT \/ x = TR_INCB) -> in_ranges XENV_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Lemma CLX_after_pro : forall so m m' sp k fin p1 p2,
  CLX OUT_rep ERR_rep XENV LIB so m -> munch (pro_W sp) m m' -> wmono asegs m m' -> SEGTOP_A + 128 <= sp ->
  AXA k fin p1 p2 m' -> CLX OUT_rep ERR_rep XENV LIB so m'.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img XENV_incb XENV_upd XENV_fp_ax.
  intros so m m' sp k fin p1 p2 (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & _) MU WM SP AX.
  set (AXP := fun x => 0xbc7f20 <= x < 0xbc7f50 \/ 0xbc8040 <= x < 0xbc8050 \/ x = TR_INIT).
  assert (AG : agree_on (fun x => 0x10000 <= x < SEGTOP_A /\ ~ AXP x) m m').
  { apply (agree_of_munch _ _ _ _ MU). intros x [Hx Hn]. unfold AXP, TR_INIT in Hn. unfold pro_W, TR_INIT, SEGTOP_A in *. cbn.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I]. }
  assert (NAX : forall x, in_ranges IO_FP x \/ in_ranges LIB_FP x \/ drv_cell x -> ~ AXP x).
  { intros x Hx HA. assert (HX : in_ranges XENV_FP x) by (apply XENV_fp_ax; unfold AXP in HA; tauto).
    destruct (XENV_img x HX) as (_ & ND & NIO & NLIB).
    destruct Hx as [Hx|[Hx|Hx]]; [exact (not_in_ranges_of_outside _ _ NIO Hx)| exact (not_in_ranges_of_outside _ _ NLIB Hx)| exact (ND Hx)]. }
  split; [apply (OUT_loc so m m' H1); eapply agree_sub; [exact AG|]; intros x Hx; split; [exact (client_static_range x (proj1 (IO_img x Hx)))| apply NAX; left; exact Hx]|].
  split; [apply (ERR_loc m m' H2); eapply agree_sub; [exact AG|]; intros x Hx; split; [exact (client_static_range x (proj1 (IO_img x Hx)))| apply NAX; left; exact Hx]|].
  split.
  { apply (XENV_upd m m' H3).
    - eapply agree_sub; [exact AG|]. intros x (Hx & N1 & N2 & N3 & N4). split; [exact (client_static_range x (proj1 (XENV_img x Hx)))|].
      unfold AXP. intros [A|[A|A]]; [exact (N1 A)| exact (N2 A)| exact (N3 A)].
    - exists k, fin, p1, p2. exact AX.
    - apply (rw_cells_agree asegs m m' _ _ (XENV_incb m H3)); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. unfold AXP, TR_INIT, TR_INCB, SEGTOP_A in *. cbv beta. lia. }
  split; [apply (LIB_loc m m' H4); eapply agree_sub; [exact AG|]; intros x Hx; split; [exact (client_static_range x (proj1 (LIB_img x Hx)))| apply NAX; right; left; exact Hx]|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m').
  { intros lo n Hd. eapply agree_sub; [exact AG|]. intros x Hx. split; [exact (client_static_range x (drv_cell_static x (Hd x Hx)))| apply NAX; right; right; exact (Hd x Hx)]. }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree asegs m m' _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree asegs m m' _ _ ER); [apply AGD; cbn; lia| exact WM]|].
  split; [apply (stk_agree asegs m m' _ _ RS); [eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]| exact WM]| exact I].
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
  /\ usp + 16 <= USTACK_TOP.

Theorem tr_start : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  TPRE Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cps asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x1f2d64) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (TLOOP RT OUT_rep ERR_rep XENV LIB fs (tr_calls L c0b) stdout_init usp buf cap x0 x1 x2 x3 x4 x5).
Proof using AF AF_DRV MAL MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img XENV_ax XENV_libc XENV_incb XENV_upd XENV_fp_ax.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP T c HA Hk.
  destruct HP as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & CR & CAPB & Hcp1 & Hcp2 & HC0 & HL
                  & Hpp1 & Hpp2 & BP & PL & PB & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  pose proof (AF_DRV Σ m ART0) as (_ & _ & GI & _).
  pose proof CLX0 as (_ & _ & XE0 & _).
  destruct (XENV_ax m XE0) as (k & fin & p1 & p2 & AX0). pose proof (XENV_libc m XE0) as LC0.
  pose proof (tr_calls_range L c0b) as TCR.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).
  assert (CSEG : SEGTOP_A <= cp \/ cp + 1 <= 0x10000) by (destruct PR3; [right| left]; lia).
  (* [comment removed for export] *)
  pose proof (tr_pro_latch (usp - 80) cp L pp plen k fin p1 p2 (Z_to_bv 64 0x1f2d64) gp t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 x4 x5
                s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST0 ltac:(ul) ltac:(ul) B16' ltac:(ul) ltac:(ul) HL ltac:(ul) ltac:(ul)
                AX0 LC0 GI MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA).
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4'
                                                 & t5' & t6' & fin' & m1 & -> & MU1 & WM1 & MI1 & TF1 & ST1 & AX1 & LC1) & Hc1').
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 208) ART0); [ul| |exact WM1].
    intros a Ha. apply MU1. unfold pro_W, TR_INIT. cbn [outside]. split; [intros Hin; apply Ha; left; ul|].
    split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
    split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
    split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I]. }
  assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1) by exact (CLX_after_pro _ m m1 (usp - 80) true fin' p1 p2 CLX0 MU1 WM1 ltac:(ul) AX1).
  assert (AGM1 : agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold pro_W, TR_INIT. cbn. split; [lia|]. split; [ul|]. split; [ul|]. split; [ul| exact I]. }
  assert (FR1 : main_frame m1 usp c0 c1 c2 c3 c4 c5 c6 c7).
  { apply (main_frame_agree m m1 usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AGM1|]; intros x Hx; cbv beta in *; ul| exact WM1]. }
  assert (BP1 : bytes_at asegs m1 pp payload).
  { apply (bytes_at_agree asegs m m1 _ _ BP). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold pro_W, TR_INIT. cbn.
    rewrite <- PL in Hx. split; [ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul| exact I]. }
  assert (HC1 : 0 < L -> bytes_at asegs m1 cp [c0b]).
  { intros HL0. apply (bytes_at_agree asegs m m1 _ _ (HC0 HL0)). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold pro_W, TR_INIT. cbn.
    cbn in Hx. split; [ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul|]. split; [destruct PR3; ul| exact I]. }
  replace (usp - 80 - 80) with (usp - 160) in Hc1', ST1 by lia.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  destruct (Z.eq_dec plen 0) as [Z0|NZ].
  - (* [comment removed for export] *)
    destruct payload as [|b payload]; [| cbn in PL; lia]. cbn in PL. clear PL. subst plen.
    pose proof (tr_pro_empty (usp - 160) cp L pp c0b ra' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F fc m1 ltac:(ul) HL HC1 CSEG MI1) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W2') Hc1').
    intros cf2 Hc2. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & (a0'' & ->) & Hc2').
    exists Σ, 0, TR_EMPTY, 0, [], ra', gp, t0', t1', t2', a0'', a1', a2', a3', a4', a5', a6', a7', (Z_to_bv 64 cp), s8, s9, s10, s11.
    exists t3', t4', t5', t6', c0, c1, c2, c3, c4, c5, c6, c7, F, fc, m1.
    split; [exact Hc2'|].
    split; [| split; [exact TCR| unfold FUZZ_COST, CREDIT_DRV in *; nia]].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|]. split; [exact FR1|].
    split; [exact TF1|]. split; [exact ST1|].
    split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
    split; [rewrite LV; reflexivity|]. split; [exact FRS|]. split; [reflexivity|]. split; [lia|].
    split; [apply bytes_at_nil; unfold TR_EMPTY; lia|]. split; [intros _; split; reflexivity|]. split; [intros Hp; lia|]. split; [lia| exact UT0].
  - (* [comment removed for export] *)
    pose proof (tr_pro_copy (usp - 160) cp L pp plen c0b ra' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F fc m1 ltac:(ul) HL ltac:(lia) HC1 CSEG MI1) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W2') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
    apply (MAL Σ (PMfd fds0 fs) (Z_to_bv 64 0x1f2f28) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
             (Z_to_bv 64 pp) (Z_to_bv 64 plen) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT)
             (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 plen lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + lia.
    + rewrite LV. reflexivity.
    + unfold mcost, CREDIT_DRV in *. destruct (Z.leb_spec plen 64512); lia.
    + unfold call_ok. rewrite EU2. split; [exact ST1|]. ul.
    + unfold unwind_ok, fp_invalid. rewrite EU2, !unsigned_lit by ul. split; [cbn; tauto|]. left. left. ul.
    + intros cf3 (Σ1 & owned & Hc3 & LV1 & FRS1 & SP1 & CR1 & Pow & Pal & Ptop).
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc3').
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
      rewrite EU2 in ST2, PRES2.
      rewrite (ret_pc_even 0x1f2f28) in Hc3' by lia.
      assert (INO : In (owned, plen) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
      assert (INB1 : In (buf, cap) (rt_live RT Σ1)) by (rewrite LV1, LV; right; left; reflexivity).
      assert (DISJ : owned + plen <= buf \/ buf + cap <= owned).
      { apply (af_live_disj RT AF Σ1 m2 owned plen buf cap [] [(buf, cap)] ART2); [rewrite LV1, LV; reflexivity| left; reflexivity]. }
      pose proof (af_live_range RT AF Σ1 m2 owned plen ART2 INO) as (OR1 & OR2 & OR3).
      assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2) by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc
                                                                              XENV_loc LIB_loc IO_img XENV_img _ m1 m2 _ _ _ CLX1 PRES2 WM2).
      pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.
      assert (BP2 : bytes_at asegs m2 pp payload).
      { apply (bytes_at_agree asegs m1 m2 _ _ BP1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx.
        rewrite <- PL in Hx. right; right; left. exists buf, cap. split; [exact INB| lia]. }
      (* [comment removed for export] *)
      pose proof (tr_copy_walk (usp - 160) owned gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11
                    u3 u4 u5 u6 F2 fc2 m2 ltac:(ul) MI2) as W3.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & <- & Hc4').
      apply (MCP Σ1 (PMfd fds0 fs) (Z_to_bv 64 0x1f2f3c) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 plen)
               (Z_to_bv 64 pp) (Z_to_bv 64 owned) (Z_to_bv 64 pp) (Z_to_bv 64 plen) b3 b4 b5 b6 b7 (Z_to_bv 64 owned) (Z_to_bv 64 cp)
               (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 owned pp payload lo);
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
      * intros cf5 Hc5.
        destruct (ASTA_unpack RT Σ1 _ _ cf5 Hc5) as (ms5 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BS3) & Hc5').
        destruct RS3 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
        rewrite EU2 in ST3, PRES3. rewrite <- PL in PRES3.
        rewrite (ret_pc_even 0x1f2f3c) in Hc5' by lia.
        assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB stdout_init m3)
          by exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                      _ m2 m3 _ _ _ _ _ CLX2 PRES3 WM3 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
        pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES3 ltac:(ul)) as AG3.
        (* [comment removed for export] *)
        pose proof (tr_copy_ret_walk (usp - 160) owned gp w0 w1 w2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 owned) d1 d2 d3 d4 d5
                      d6 d7 (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
                      F3 fc3 m3 MI3) as W4.
        lazymatch type of W4 with evt asegs _ ?X =>
          assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
        clear W4.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W4') Hc5').
        intros cf6 Hc6. apply Hk.
        destruct (ASTA_unpack RT Σ1 _ _ cf6 Hc6) as (ms6 & <- & Hc6').
        exists Σ1, plen, owned, owned, payload, (Z_to_bv 64 0x1f2f3c), gp, w0, w1, w2, (Z_to_bv 64 owned), d1, d2, d3, d4, d5, d6, d7,
               (Z_to_bv 64 cp), s8, s9, s10, s11.
        exists w3, w4, w5, w6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
        split; [exact Hc6'|]. split; [| split; [exact TCR| rewrite CR1; unfold mcost, FUZZ_COST, CREDIT_DRV in *;
                                                 destruct (Z.leb_spec plen 64512); nia]].
        assert (AG13 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m3).
        { apply (agree_trans _ m1 m2 m3); [eapply agree_sub; [exact AG2|]; intros x Hx; cbv beta in *; lia|].
          eapply agree_sub; [exact AG3|]. intros x Hx; cbv beta in *; lia. }
        split; [exact ART3|]. split; [exact MI3|]. split; [exact CLX3|].
        split; [apply (main_frame_agree m1 m3 usp _ _ _ _ _ _ _ _ FR1); [eapply agree_sub; [exact AG13|]; intros x Hx; cbv beta in *; ul
                | exact (wmono_trans asegs m1 m2 m3 WM2 WM3)]|].
        split; [apply (tr_frame_agree m1 m3 _ _ _ _ _ _ _ _ TF1); [eapply agree_sub; [exact AG13|]; intros x Hx; cbv beta in *; lia
                | exact (wmono_trans asegs m1 m2 m3 WM2 WM3)]|].
        rewrite SP1. split; [exact ST3|].
        split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
        split; [rewrite LV1, LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity|].
        split; [rewrite FRS1; exact FRS|]. split; [exact PL|]. split; [lia|]. split; [exact BS3|].
        split; [intros Hp; lia|]. split; [intros _; reflexivity|]. split; [lia| exact UT0].
Qed.

End Tr1.

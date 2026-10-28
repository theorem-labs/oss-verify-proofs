(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_libiface_pem D_agree D_clx PLayout I_lkit I_ut Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_G_kit Fz_W7_defs Fz_W7_segs Fz_W7_inv Fz_W7_calls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Section W7X.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
(* [comment removed for export] *)
Hypothesis libenv_errno : forall m LBL E, libenv m LBL E -> exists v, rw_cells asegs m (errno_cell (wz TP_A)) [C4 v].
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable LIB : list (Z * Z) -> mem -> Prop.
Variable REST : mem -> Prop.
Variable REST_fp : Z -> Prop.
Hypothesis REST_agree : forall m m', REST m -> agree_on REST_fp m m' -> REST m'.
Hypothesis REST_fp_where : forall a, REST_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.
Hypothesis W7_CLOSE : forall CL m (canary : word) E LBL, In (E, 904) CL -> incl_live LBL CL -> ~ In (E, 904) LBL ->
    cl_env m (Z_to_bv 8 1) canary -> sec_off m -> libenv m LBL E -> errst_at_rest E [] m -> REST m -> LIB CL m.

Local Notation w7a := (w7a RT).
Local Notation w7_com := (w7_com RT libenv FZ_SITES FZ_CALLS REST).
Local Notation w7_at := (w7_at RT LIB).
Local Notation P5 x := (x RT libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P7 x := (x RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST) (only parsing).

(* [comment removed for export] *)
Definition EXIT_stmt : Prop :=
  forall (en : w7a) Σ m crem (F : bvmap 5 word) (fc : bv 32) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 : word) (lowj : list byte),
  w7_com en Σ m crem [] -> errst_at_rest (a_E RT en) [] m ->
  rw_cells asegs m (a_SP RT en + -160) [CB 56 lowj] ->
  w7_at en Σ (MS (mkR ra1 (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) (wz (a_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7
                   (wz (a_f RT en)) s3 s4 s5 (wz (-8)) s7 s8 s9 (wz (a_f RT en / 8 + 2147450880)) (wz (a_f RT en)) t3 t4 t5 t6)
              F (wz J_w7_exit) fc None m (seg_rom asegs)).

Theorem EXIT_proof : EXIT_stmt.
Proof.
  intros en Σ m crem F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 lowj COM REST0 LOW56. unfold w7_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  assert (HLO : a_lo RT en <= bv_unsigned (a_sp RT en) - 176) by (clear - LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1, a_SP in *; lia).
  assert (SPH : bv_unsigned (a_sp RT en) <= 2 ^ 47) by (clear - TOP; unfold USTACK_TOP, a_SP in *; lia).
  unfold a_sp1, a_SP in ST, GAP, TOP, LOW56, SAVED.
  (* [comment removed for export] *)
  destruct (rw_cells_forget asegs m (a_f RT en) _ (rw_cells_head m _ _ _ FHD)) as (hj & HDR). cbn [cells_size csize Nat.add] in HDR.
  destruct FSJ as [sjr FSJ'].
  assert (FSJ'' : rw_cells asegs m (shad (a_f RT en) + Z.of_nat (cells_size w7_shadow_live)) [CB 12 sjr]) by exact FSJ'.
  destruct (rw_cells_forget asegs m _ _ (proj2 (rw_cells_app m (shad (a_f RT en)) w7_shadow_live [CB 12 sjr]) (conj FSH FSJ''))) as (sj & SB).
  unfold shad in SB, SH1, SH2, SH8. cbn [cells_size csize Nat.add app w7_shadow_live map length] in SB.
  pose proof (w7_x1_walk ra1 (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 F fc m (a_f RT en) (a_lo RT en) (a_pd RT en) hj sj
                PD HLO HLOS SPH F0 FSEG FLO FSHR ST HDR SB MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (ra2 & m1 & -> & MU1 & WM1 & MI1 & HDR1 & SB1) & Hc1'). clear Hc1 HA.
  (* [comment removed for export] *)
  assert (NWS : forall a, a_lo RT en <= a -> outside [(a_f RT en, a_f RT en + 8); (a_f RT en / 8 + 2147450880, a_f RT en / 8 + 2147450880 + 32)] a).
  { intros a Ha. cbn [outside]. clear - Ha FLO SH2 HLOS. split; [lia|]. split; [lia| exact I]. }
  assert (NWC : forall a, client_static a -> outside [(a_f RT en, a_f RT en + 8); (a_f RT en / 8 + 2147450880, a_f RT en / 8 + 2147450880 + 32)] a).
  { intros a Ha. pose proof (client_static_range a Ha). cbn [outside]. clear - H FSEG SH1. unfold SEGTOP_A in *. split; [lia|]. split; [lia| exact I]. }
  assert (NWL : forall p n a, In (p, n) (rt_live RT Σ) -> p <= a < p + n -> outside [(a_f RT en, a_f RT en + 8); (a_f RT en / 8 + 2147450880, a_f RT en / 8 + 2147450880 + 32)] a).
  { intros p n a Hin Hp. pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 INF) as [SHL _]. destruct (FLV p n Hin) as [X|X]; destruct (SHL p n Hin) as [Y|Y].
    all: try replace (a_f RT en + fs_size 2) with (a_f RT en + 64 * 4) in Y by reflexivity; try rewrite (shad_add64 (a_f RT en) 4 F64) in Y; unfold shad, SHB in Y.
    all: cbn [outside]; clear - X Y Hp; split; [lia|]; split; [lia| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (a_lo RT en) ART0 LOW); [| exact WM1]. intros a NA. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros R; apply NA.
    - do 3 right; left. exists (a_f RT en), 2%nat. split; [exact INF| change (fs_size 2) with 256; clear - R; lia].
    - do 4 right. exists (a_f RT en), 2%nat. split; [exact INF|]. replace (a_f RT en + fs_size 2) with (a_f RT en + 64 * 4) by reflexivity. rewrite (shad_add64 (a_f RT en) 4 F64). unfold shad, SHB. clear - R; lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ m1 (a_f RT en) 2%nat [] ART1 FRS) as (Σ2 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 2) with 256 in FW. replace (a_f RT en + 256 - 8) with (a_f RT en + 248) in FW by lia.
  assert (FLLO : flg + 1 <= a_lo RT en) by (clear - FLW LOW; lia).
  assert (FR1 : rw_cells asegs m1 (bv_unsigned (a_sp RT en) + -160) ([CB 56 lowj] ++ w7_savedl RT en)).
  { apply (rw_cells_agree asegs m m1); [| | exact WM1].
    - apply (proj2 (rw_cells_app m _ [CB 56 lowj] (w7_savedl RT en))). split; [exact LOW56|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned (a_sp RT en) + -160 + 56) with (bv_unsigned (a_sp RT en) + -104) by lia. exact SAVED.
    - intros a Ha. apply MU1. apply NWS. cbv beta in Ha. unfold w7_savedl in Ha. cbn [cells_size csize Nat.add app] in Ha. clear - Ha HLO. lia. }
  unfold w7_savedl in FR1. cbn [app] in FR1.
  assert (ST1 : stk asegs m1 (a_lo RT en) (bv_unsigned (a_sp RT en) + -160 - a_pd RT en)) by (eapply stk_munch; [exact ST| exact MU1| exact WM1| intros x Hx; apply NWS; clear - Hx; lia]).
  assert (GAP1 : stk asegs m1 (bv_unsigned (a_sp RT en) + -160 - a_pd RT en) (bv_unsigned (a_sp RT en) + -160)) by (eapply stk_munch; [exact GAP| exact MU1| exact WM1| intros x Hx; apply NWS; clear - Hx HLO PD; lia]).
  pose proof (w7_x2_walk ra2 (a_ra RT en) (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 (wz (-11)) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 (wz (-8)) s7 s8 s9 (wz (a_f RT en / 8 + 2147450880)) t3 t4 t5 t6
                (a_s0 RT en) (a_s1 RT en) (a_s2 RT en) (a_s3 RT en) (a_s4 RT en) (a_s5 RT en) (a_s6 RT en) (a_s7 RT en) (a_s8 RT en) (a_s9 RT en) (a_s10 RT en) (a_s11 RT en)
                F fc m1 (a_f RT en) flg (a_lo RT en) (a_pd RT en) lowj PD HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP1 FR1 FW FLC MI1) as W2.
  cl_lift W2 Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (u0 & u1 & u2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FLC2) & Hc2'). clear Hc2 Hc1'.
  destruct (REL m2 MU2 WM2 FLC2) as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2 & CG2).
  (* [comment removed for export] *)
  assert (NFL : forall a, (client_static a \/ in_live (rt_live RT Σ) a \/ a_lo RT en <= a) -> outside [(flg, flg + 1)] a).
  { intros a Ha. cbn [outside]. split; [| exact I]. intros R. assert (E : a = flg) by (clear - R; lia). subst a.
    destruct Ha as [H|[H|H]]; [apply NAC; right; left; exact H| apply NAC; do 2 right; left; exact H| clear - H FLLO; lia]. }
  assert (A02 : forall a : word, (client_static (bv_unsigned a) \/ in_live (rt_live RT Σ) (bv_unsigned a) \/ a_lo RT en <= bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite (MU2 a (NFL _ Ha)). apply MU1. destruct Ha as [H|[(p & n & Hin & Hp)|H]]; [exact (NWC _ H)| exact (NWL p n _ Hin Hp)| exact (NWS _ H)]. }
  apply Hk. unfold w7_post. exists Σ2, (a_CL RT en).
  split.
  - eapply ASTA_conseq; [exact (ASTA_switch RT Σ Σ2 (a_PMc RT en) _ c2 Hc2' AL2 AM2)|]. intros ms <-. exists m2.
    split; [exists u0, u1, u2, i1, i2, i3, i4, i5, i6, i7, u3, u4, u5, u6, F, fc; reflexivity|].
    split; [split; [exact ART2| split; [exact MI2| exact ST2]]|].
    split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply A02. destruct Ha as [H|[H|[H|[H|H]]]].
             - do 2 right. clear - H HLO. lia.
             - left. exact H.
             - right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [exact (DLV _ Hin)| exact Hp].
             - destruct H as (f & k & [] & _).
             - destruct H as (f & k & [] & _). }
    assert (LE2 : libenv m2 (a_LBL RT en) (a_E RT en)).
    { eapply libenv_agree; [exact LE|]. intros a Ha. apply A02. destruct (libenv_fp_where _ _ Ha) as [(_ & CS & _)|(p & n & Hin & Hp)]; [left; exact CS| right; left; exists p, n; split; [exact (CLL _ (INCL _ Hin))| exact Hp]]. }
    split; [| exact (libenv_errno _ _ _ LE2)].
    apply (W7_CLOSE (a_CL RT en) m2 (a_canary RT en) (a_E RT en) (a_LBL RT en) INE INCL NLE).
    + apply (cl_env_agree m m2 _ _ CLE). intros a Ha. apply A02. left. exact (cl_cell_static _ Ha).
    + apply (sec_off_agree m m2 SEC). intros a Ea. apply A02. left. rewrite Ea. exact sec_init_static.
    + exact LE2.
    + apply (errst_rest_agree m m2 _ _ REST0). intros a Ha. apply A02. destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & [] & _)].
      right; left. exists (a_E RT en), 904. split; [exact (CLL _ INE)| exact R].
    + apply (REST_agree m m2 RST). intros a Ha. apply A02. left. exact (proj1 (REST_fp_where _ Ha)).
  - rewrite LV2, FRS2, SP2, CR2, CG2. split; [exact PERM|]. split; [exact CLM|]. split; [intros p n Hin; exact (LPOS _ (CLL _ Hin))|].
    split; [reflexivity|]. split; [exact SP0|]. split; [clear - CR CR0; lia| exact CG].
Qed.
End W7X.

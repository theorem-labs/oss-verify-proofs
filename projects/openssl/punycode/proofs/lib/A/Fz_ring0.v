(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow R_small R_m2s R_thread R_tlsgetaddr R_fs_defs R_prim_defs RT_iface RT_state RT_rep RT_trans
  RT_facts0 RT_sep RT_facts RT_release RT_stackmalloc RT_icfacts RT_artfacts D_kit D_clx Fz_defs Fz_voc Fz_iface Fz_ckit.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit AShadow ARt ACode ARtIc AIface AFakeStack AImg ABridge KBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

Section Ring.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

(* [comment removed for export] *)
Lemma ring_xn_shadow : stk asegs m 0x80010f08 0x80010f10.
Proof.
  destruct (ART_shadow Σ m HA) as (_ & _ & SW & _).
  destruct (stk_split asegs m _ 0x80010f08 _ SW ltac:(vm_compute; split; discriminate)) as (_ & S2).
  exact (proj1 (stk_split asegs m _ 0x80010f10 _ S2 ltac:(vm_compute; split; discriminate))).
Qed.

(* [comment removed for export] *)
Lemma ring_live_mem : forall p n, In (p, n) (live Σ) -> AShadow.memrange p (n + 8) /\ (0 < n -> AShadow.shw_ok m p n).
Proof.
  intros p n Hin. pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold rtA_sp0, sp_window_hi in *.
  assert (Ms : forall x, x mod 64 = 0 -> shad x mod 8 = 0).
  { intros x Hx. unfold shad, SHB. Z.div_mod_to_equations. lia. }
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hi & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(sc & Hs & Hq & Hn' & -> & Y1 & Y5)].
  - pose proof (ART_prim Σ m HA c Hc) as (_ & _ & _ & _ & _ & _ & SR).
    pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
    pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold l_ACEIL, STACK_WIN, rb, kUserCap in *.
    assert (C37 : c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia.
    assert (Hrb : (SB + c * 2 ^ 32) mod 64 = 0) by (clear - P3; Z.div_mod_to_equations; lia).
    assert (Hrb2 : (SB + c * 2 ^ 32 + 2 ^ 32) mod 64 = 0) by (clear - P3; Z.div_mod_to_equations; lia).
    split.
    + unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
      split; [lia|]. destruct G4 as [G4|G4]; [left| right]; lia.
    + intros Hn. apply (shw_ok_of_stk m _ _ _ _ SR).
      * unfold shad, SHB. clear - G1 P1 Hc. Z.div_mod_to_equations. lia.
      * pose proof (Ms _ Hrb) as M8. unfold AShadow.sha, AShadow.SB, shad, SHB in *. clear - M8 Y1 Y3 Hrb. Z.div_mod_to_equations. lia.
      * pose proof (Ms _ Hrb2) as M8. unfold AShadow.sha, AShadow.SB, shad, SHB in *. clear - M8 Y2 Y4 Hrb2 Hn. Z.div_mod_to_equations. lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). pose proof (ART_chunk Σ m HA) as (_ & HS). pose proof (HS k sc Hk) as (_ & _ & _ & _ & SR & _).
    destruct (map_geo Σ m HA k sc Hk) as (Hn0 & (G1 & G2 & G3 & G4 & G5) & _ & M2 & Hroom). unfold s_ubeg in *. rewrite <- Hn' in *.
    unfold l_ACEIL, STACK_WIN in *.
    assert (Mb : s_mb sc mod 64 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
    assert (Me : (s_mb sc + smsz (s_n sc)) mod 64 = 0) by (clear - G2 M2; Z.div_mod_to_equations; lia).
    split.
    + unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
      split; [lia|]. destruct G4 as [G4|G4]; [left| right]; lia.
    + intros Hn. apply (shw_ok_of_stk m _ _ _ _ SR).
      * unfold shad, SHB. clear - G1. Z.div_mod_to_equations. lia.
      * pose proof (Ms _ Mb) as M8. unfold AShadow.sha, AShadow.SB, shad, SHB in *. clear - M8 Mb. Z.div_mod_to_equations. lia.
      * pose proof (Ms _ Me) as M8. unfold AShadow.sha, AShadow.SB, shad, SHB in *. clear - M8 Me Y1 Hn. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Hypothesis MI : mem_inv asegs m.

Local Ltac k8 H := exact (KBridge.cell_C8 asegs m _ _ (proj1 H)).
Local Ltac k8r H := exact (KBridge.cell_C8 asegs m _ _ H).

Lemma ring_rt_ok : ARt.rt_ok m.
Proof.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & (M1 & M2 & M3) & _ & _ & _ & IC).
  unfold icells_rep in IC. destruct IC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RI1 & RI2 & _).
  pose proof (rw_cells_head m _ _ _ M1) as A0.
  pose proof (rw_cells_head m _ _ _ (rw_cells_tail m _ _ _ M1)) as A1. 
  pose proof (rw_cells_head m _ _ _ (rw_cells_tail m _ _ _ (rw_cells_tail m _ _ _ M1))) as A2.
  pose proof (rw_cells_tail m _ _ _ (rw_cells_tail m _ _ _ (rw_cells_tail m _ _ _ M1))) as A3.
  pose proof (rw_cells_head m _ _ _ M3) as B0.
  pose proof (rw_cells_head m _ _ _ (rw_cells_tail m _ _ _ M3)) as B1.
  pose proof (rw_cells_tail m _ _ _ (rw_cells_tail m _ _ _ M3)) as B2.
  cbn [csize] in *.
  unfold ARt.rt_ok, ARt.G_SB, ARt.C_SB, ARt.G_MIDBEG, ARt.C_MIDBEG, ARt.G_MIDEND, ARt.C_MIDEND, ARt.G_HIEND, ARt.C_HIEND, ARt.G_RINTRIN, ARt.C_RINTRIN.
  split; [k8 A0|]. split; [k8 M2|]. split; [k8 A1|]. split; [k8 B1|]. split; [k8 A2|]. split; [eexists; k8 B2|].
  split; [k8 A3|]. split; [k8 B0|]. split; [k8r RI1|]. eexists. exact (KBridge.cell_C1 asegs m _ _ RI2).
Qed.

Lemma fs_dtv : exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m.
Proof. destruct (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma one8 : zxb (Z_to_bv 8 1) = W 1. Proof. reflexivity. Qed.
Lemma zero8 : zxb (Z_to_bv 8 0) = W 0. Proof. reflexivity. Qed.

Lemma ring_ic_ok : ARtIc.ic_ok m.
Proof.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC).
  unfold icells_rep in IC. destruct IC as (_ & I2 & _ & _ & _ & I6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I17 & I18 & _).
  destruct fs_dtv as (dtvbeg & _ & (AI & _ & _ & _ & (D1 & _))).
  destruct (lib_ro_cells m (rta_lib_ro Σ m HA)) as (L1 & L2 & _).
  unfold ARtIc.ic_ok, ARtIc.C_INITED, ARtIc.G_CF, ARtIc.C_CF, ARtIc.R_STRLEN, ARtIc.R_STRCHR, ARtIc.R_MEMCPY.
  split; [rewrite <- one8; exact (KBridge.cell_C1 asegs m _ _ (proj1 AI))|].
  split; [k8 D1|].
  split; [rewrite <- zero8; exact (KBridge.cell_C1 asegs m _ _ I2)|].
  split; [rewrite <- one8; exact (KBridge.cell_C1 asegs m _ _ I18)|].
  split; [rewrite <- one8; exact (KBridge.cell_C1 asegs m _ _ L2)|].
  split; [k8r I17|]. split; [k8r L1|]. split; [k8r I6|].
  split; apply (img_ok_ro m _ _ MI); lia.
Qed.

Lemma ring_uar_on : AIface.uar_on m.
Proof.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & (_ & _ & U1 & U2) & _).
  unfold AIface.uar_on, AIface.G_UAR, AIface.C_UAR. split; [k8r U1| exact (KBridge.cell_C4 asegs m _ _ U2)].
Qed.

Lemma m2048 : W (-2048) = W 0xfffffffffffff800. Proof. apply bv_eq. reflexivity. Qed.

Lemma ring_fsrt_ok : AFakeStack.fsrt_ok m FSB (l_DTV L) (l_TCX L) (l_T L).
Proof.
  pose proof (ART_consts Σ m HA) as (_ & _ & ((K1 & K2 & K3 & K4) & TX) & _).
  destruct (ART_fs Σ m HA) as (FC & _ & _ & _ & TPC & (dtvbeg & Hdb & (AI & RL & DP & D1 & (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8))) & (tb & te & TT) & _).
  unfold ttls_cells in TT. unfold fs_const in FC.
  unfold AFakeStack.fsrt_ok, ARtIc.C_INITED, AFakeStack.R_TLSGA, AFakeStack.TLS_DESC, AFakeStack.TP, AFakeStack.DTV, AFakeStack.C_TSDINIT,
    AFakeStack.TSD, ARtIc.G_CF, ARtIc.C_CF, AFakeStack.G_VERB, AFakeStack.C_VERB, AFakeStack.G_DTLSOFF.
  split; [rewrite <- one8; exact (KBridge.cell_C1 asegs m _ _ (proj1 AI))|].
  split; [k8 RL|].
  split; [k8 (rw_cells_head m _ _ _ G5)|].
  split; [rewrite m2048; pose proof (rw_cells_tail m _ _ _ G5) as H; cbn [csize] in H; k8 H|].
  split; [k8 DP|]. split; [k8 D1|]. split; [k8 TPC|].
  split; [rewrite <- one8; exact (KBridge.cell_C1 asegs m _ _ (proj1 K1))|].
  split; [exact (KBridge.cell_C4 asegs m _ _ (proj1 K2))|].
  split; [k8 K3|]. split; [k8 K4|]. split; [k8 G1|].
  split; [rewrite <- one8; exact (KBridge.cell_C1 asegs m _ _ (proj1 G2))|].
  split; [k8 G3|]. split; [exact (KBridge.cell_C4 asegs m _ _ (proj1 G4))|].
  split; [k8 G6|]. split; [k8 G7|]. split; [k8 TX|].
  split; [exists tb, te; split; [k8 (rw_cells_head m _ _ _ TT)| pose proof (rw_cells_tail m _ _ _ TT) as H; cbn [csize] in H;
          replace (l_T L + 48 + Z.of_nat 8) with (l_T L + 56) in H by lia; k8 H]|].
  split; [exists dtvbeg; split; [k8 G8| exact Hdb]|].
  split; [k8 (rw_cells_head m _ _ _ FC)|].
  pose proof (rw_cells_tail m _ _ _ FC) as H. cbn [csize] in H. replace (l_FSB L + 88 + Z.of_nat 8) with (l_FSB L + 96) in H by lia.
  rewrite <- zero8. exact (KBridge.cell_C1 asegs m _ _ (proj1 H)).
Qed.

(* [comment removed for export] *)
Lemma ring_fsb : 0 < FSB /\ FSB mod 4096 = 0 /\ SEGTOP_A <= FSB /\ FSB + 0xb09000 <= l_ACEIL L
  /\ (FSB + 0xb09000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= FSB) /\ l_ACEIL L + STACK_WIN <= USTACK_TOP
  /\ 0x7fff80000000 - STACK_WIN <= l_ACEIL L.
Proof.
  pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (rta_sp0_range Σ m HA) as Hr. pose proof (rta_sp0_win Σ m HA) as Hw.
  unfold rtA_sp0, l_ACEIL, SEGTOP_A, USTACK_TOP, STACK_WIN in *. repeat split; try assumption; try lia.
Qed.

Lemma ring_fs_wf : AIface.fs_wf FSB.
Proof.
  destruct ring_fsb as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  unfold AIface.fs_wf, AIface.FS_SIZE, ARt.A_IMG_END, AShadow.SB, AShadow.HIMEM_BEG, AShadow.HIMEM_END, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi,
    USTACK_TOP, STACK_WIN in *.
  split; [split; [lia| destruct B5; [left| right]; lia]|]. split; [lia|]. clear - B2. Z.div_mod_to_equations. lia.
Qed.

Lemma grant_T : grant_ok L (l_T L) 4096 /\ apart (l_T L) 4096 FSB 0xb09000.
Proof.
  split; [apply (geo_grant Σ m HA); unfold startup_grants; do 2 right; left; reflexivity|].
  exact (geo_apart Σ m HA 2 5 _ _ ltac:(lia) eq_refl eq_refl).
Qed.
Lemma grant_TCX : grant_ok L (l_TCX L) 0x10000 /\ apart (l_TCX L) 0x10000 FSB 0xb09000.
Proof.
  split; [apply (geo_grant Σ m HA); unfold startup_grants; do 3 right; left; reflexivity|].
  exact (geo_apart Σ m HA 3 5 _ _ ltac:(lia) eq_refl eq_refl).
Qed.
Lemma grant_DTV : grant_ok L (l_DTV L) 4096 /\ apart (l_DTV L) 4096 FSB 0xb09000.
Proof.
  split; [apply (geo_grant Σ m HA); unfold startup_grants; do 4 right; left; reflexivity|].
  exact (geo_apart Σ m HA 4 5 _ _ ltac:(lia) eq_refl eq_refl).
Qed.

Lemma ring_fsrt_wf : AFakeStack.fsrt_wf FSB (l_DTV L) (l_TCX L) (l_T L).
Proof.
  destruct ring_fsb as (B1 & _ & _ & B4 & _ & B6 & _).
  destruct grant_T as ((T1 & _ & T3 & _) & _). destruct grant_TCX as ((C1 & _ & C3 & _) & _). destruct grant_DTV as ((D1 & _ & D3 & _) & _).
  unfold AFakeStack.fsrt_wf, USTACK_TOP, STACK_WIN in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ring_live_apart : forall p n, In (p, n) (live Σ) -> p + n <= FSB \/ FSB + 0xb09000 <= p.
Proof.
  intros p n Hin.
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hi & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(sc & Hs & Hq & Hn' & -> & Y1 & Y5)].
  - pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha.
    pose proof (geo_prb Σ m HA) as (P1 & P2 & _). unfold apart, rb, kUserCap in *.
    assert (C37 : c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). destruct (map_geo Σ m HA k sc Hk) as (_ & _ & Hf & _ & Hroom).
    unfold apart, s_ubeg in *. rewrite <- Hn' in *. unfold R_glue_defs.ru8 in Hroom.
    pose proof (Z.div_mod (s_n sc + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s_n sc + 7) 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ring_live_app : forall p n, In (p, n) (live Σ) -> 0 <= p /\ (p + n <= 0x7fff8000 \/ 0x10007fff8000 <= p).
Proof.
  intros p n Hin. destruct (ring_live_mem p n Hin) as (MR & _).
  unfold AShadow.memrange, AShadow.LOMEM_END, AShadow.HIMEM_BEG, AShadow.HIMEM_END in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ring_frames_hi : forall f k, In (f, k) (frames Σ) -> k <> 0%nat -> FSB + 1085440 <= f /\ f + fs_size k <= FSB + 0xb09000 /\ f mod 64 = 0.
Proof.
  intros f k Hin Hk0. destruct (busy_slot Σ m HA f k Hin) as (Hk & p & Hp & -> & _).
  destruct ring_fsb as (_ & B2 & _).
  destruct Hk as [E|[E|E]]; [contradiction| |]; subst k; unfold frame_addr, NF, fsz, fs_size in *.
  - change (Z.of_nat 2) with 2 in *. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hp.
    change (Z.shiftl 64 2) with 256. split; [lia| split; [lia| clear - B2; Z.div_mod_to_equations; lia]].
  - change (Z.of_nat 6) with 6 in *. change (2 ^ 20) with 1048576. change (2 ^ 6) with 64. change (2 ^ (14 - 6)) with 256 in Hp.
    change (Z.shiftl 64 6) with 4096. split; [lia| split; [lia| clear - B2; Z.div_mod_to_equations; lia]].
Qed.

Lemma ring_geo_ok : ring_geo RTA Σ FSB (l_DTV L) (l_TCX L) (l_T L).
Proof.
  destruct ring_fsb as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct grant_T as ((T1 & _ & T3 & T4 & _) & TA). destruct grant_TCX as ((C1 & _ & C3 & C4 & _) & CA). destruct grant_DTV as ((D1 & _ & D3 & D4 & _) & DA).
  unfold ring_geo, dom_cell, AIface.FS_SIZE, AShadow.SB, AShadow.HIMEM_BEG. cbn [rt_sp0 rt_live rt_frames RTA]. unfold rtA_sp0, rtA_live, rtA_frames.
  unfold l_ACEIL, apart, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  split; [lia|]. split; [exact ring_live_apart|].
  split; [intros f k Hin Hk; destruct (ring_frames_hi f k Hin Hk) as (H1 & H2 & _); split; assumption|].
  repeat split; lia.
Qed.

Lemma ring_apart : no_cls0 (frames Σ) -> forall x : word, AIface.ring_FP FSB x ->
  ~ aclient (live Σ) (frames Σ) (rtA_sp0 Σ - STACK_WIN) (bv_unsigned x).
Proof.
  intros NC x HR HC. destruct ring_fsb as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (RS : AShadow.sha (FSB + 36864) = FSB / 8 + 4608 + 0x7fff8000 /\ 0x7fff8000 <= FSB / 8 + 4608 + 0x7fff8000
               /\ FSB / 8 + 4608 + 0x7fff8000 + 131072 <= 0x10007fff8000).
  { unfold AShadow.sha, AShadow.SB, l_ACEIL, USTACK_TOP, STACK_WIN in *. clear - B1 B2 B4 B6. Z.div_mod_to_equations. lia. }
  destruct RS as (ES & RS1 & RS2).
  assert (HX : (FSB <= bv_unsigned x < FSB + 1085440) \/ (FSB / 8 + 4608 + 0x7fff8000 <= bv_unsigned x < FSB / 8 + 4608 + 0x7fff8000 + 131072)).
  { unfold AIface.ring_FP, LibKit.inr in HR. rewrite ES in HR. clear - HR. lia. }
  clear HR. unfold rtA_sp0, l_ACEIL, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A, USTACK_TOP, STACK_WIN in *.
  destruct HC as [H|[H|[H|[H|H]]]].
  - clear - H HX B4 B7 RS2. lia.
  - pose proof (client_static_range _ H) as CR. unfold SEGTOP_A in CR. clear - CR HX B3 RS1. lia.
  - destruct H as (p & n & Hin & Hp). pose proof (ring_live_apart p n Hin) as A1. pose proof (ring_live_app p n Hin) as (A2 & A3).
    clear - Hp HX A1 A3 RS1 RS2. lia.
  - destruct H as (f & k & Hin & Hf). pose proof (NC f k Hin) as Hk. destruct (ring_frames_hi f k Hin Hk) as (F1 & F2 & _).
    assert (0 < fs_size k) by (destruct (sep_frame Σ m HA f k Hin) as (_ & _ & X); exact X).
    clear - Hf HX F1 F2 B5 RS1 RS2 H. lia.
  - destruct H as (f & k & Hin & Hf). pose proof (NC f k Hin) as Hk. destruct (ring_frames_hi f k Hin Hk) as (F1 & F2 & F3).
    assert (0 < fs_size k) by (destruct (sep_frame Σ m HA f k Hin) as (_ & _ & X); exact X).
    unfold shad, SHB in Hf. clear - Hf HX F1 F2 F3 B1 B2 B4 B5 B6 H. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma filter_no_cls0 : forall frs : list (Z * nat), no_cls0 frs -> List.filter (fun fk => Nat.eqb (snd fk) 0) frs = [].
Proof.
  induction frs as [|[f k] frs IH]; intros NC; [reflexivity|]. cbn [List.filter snd].
  destruct (Nat.eqb_spec k 0) as [E|E]; [exfalso; exact (NC f k ltac:(left; reflexivity) E)|]. apply IH. intros f' k' Hin. apply (NC f' k'). right. exact Hin.
Qed.

Lemma wr_at_pointwise : forall (a n : Z), 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> wview asegs m (wa (a + i)) <> None) -> wr_at asegs m a n.
Proof. intros a n H0 H1 H. split; [exact H0|]. split; [exact H1| exact H]. Qed.

Lemma ring_fs0 : fs_cls_rep FSB 0 (fs0 Σ) m /\ flags_ok 0 (fss_flags (fs0 Σ)).
Proof.
  destruct (ART_fs Σ m HA) as (_ & C0 & _). split; [exact C0|].
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (F0 & _). exact (proj1 F0).
Qed.

Lemma ring_idle : no_cls0 (frames Σ) ->
  (forall i, (i < length (fss_flags (fs0 Σ)))%nat -> nth i (fss_flags (fs0 Σ)) 1 = 0)
  /\ (exists h, 0 <= h < 2 ^ 64 /\ LibKit.cell ACode.ASEGS m FSB 8 (W h)) /\ AShadow.zeros m (FSB + 4096) 16384 /\ AIface.ring_wr m FSB.
Proof.
  intros NC. destruct ring_fs0 as ((CH & CF & CFr) & (FLEN & F01)). destruct ring_fsb as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  change (NF 0) with 16384 in FLEN.
  assert (ZALL : forall i, (i < length (fss_flags (fs0 Σ)))%nat -> nth i (fss_flags (fs0 Σ)) 1 = 0).
  { pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (_ & _ & _ & _ & _ & _ & FCNT & _).
    pose proof (FCNT 0%nat ltac:(left; reflexivity)) as C. cbn [fs_of] in C. rewrite (filter_no_cls0 _ NC) in C. cbn [length] in C.
    intros i Hi. apply nbusy_zero_nth; [exact Hi| lia]. }
  split; [exact ZALL|].
  unfold fs_hint_rep in CH. cbn [Z.eqb] in CH. destruct CH as (h0 & Hh0 & CH). unfold fs_hint in CH. replace (FSB + 8 * 0) with FSB in CH by lia.
  unfold fs_flags in CF. change (fl_base FSB 0) with (FSB + 0x1000 + 0) in CF. replace (FSB + 0x1000 + 0) with (FSB + 4096) in CF by lia.
  destruct CF as (CFb & CFw). rewrite length_map, FLEN in CFw.
  split; [exists h0; split; [exact Hh0| exact (KBridge.cell_C8 asegs m _ _ (proj1 CH))]|].
  split.
  { intros i Hi. pose proof (bytes_offA m (FSB + 4096) _ i CFb ltac:(rewrite length_map, FLEN; unfold SEGTOP_A in B3; right; lia) ltac:(rewrite length_map, FLEN; exact Hi)) as E.
    rewrite E. rewrite nth_error_map_b8 by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id; lia). rewrite ZALL by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id; lia). reflexivity. }
  assert (FRW : forall p, 0 <= p < 16384 -> wr_at asegs m (FSB + 36864 + 64 * p) 64 /\ wr_at asegs m (shad FSB + 4608 + 8 * p) 8).
  { intros p Hp. destruct (CFr p ltac:(change (NF 0) with 16384; exact Hp) ltac:(apply ZALL; apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id; lia)) as ((j1 & R1) & (j2 & R2)).
    rewrite (shad_frame FSB 0 p B2 ltac:(lia) ltac:(lia)) in R2. unfold frame_addr in R1. change (fsz 0) with 64 in *.
    replace (FSB + 0x9000 + 0 * 2 ^ 20 + p * 64) with (FSB + 36864 + 64 * p) in R1 by lia.
    replace (SHB + FSB / 8 + 0x1200 + 0 * 2 ^ 17 + p * (64 / 8)) with (shad FSB + 4608 + 8 * p) in R2 by (unfold shad; change (64 / 8) with 8; lia).
    change (Z.to_nat 64) with 64%nat in R1. change (Z.to_nat (64 / 8)) with 8%nat in R2.
    split; [exact (rw_cells_wr_at asegs m _ _ 64 R1 ltac:(cbn; lia))| exact (rw_cells_wr_at asegs m _ _ 8 R2 ltac:(cbn; lia))]. }
  assert (ESH : AShadow.sha (FSB + 36864) = shad FSB + 4608) by (unfold AShadow.sha, AShadow.SB, shad, SHB; clear - B2; Z.div_mod_to_equations; lia).
  unfold AIface.ring_wr. rewrite ESH.
  split; [exact (KBridge.wr_ok_wr_at asegs m FSB 8 FSB 8 (rw_cells_wr_at asegs m _ _ 8 CH ltac:(cbn; lia)) ltac:(lia) ltac:(lia))|].
  split; [exact (KBridge.wr_ok_wr_at asegs m (FSB + 4096) 16384 (FSB + 4096) 16384 CFw ltac:(lia) ltac:(lia))|].
  split.
  - apply (KBridge.wr_ok_wr_at asegs m (FSB + 36864) 1048576); [| lia| lia]. apply wr_at_pointwise; [lia| unfold l_ACEIL, USTACK_TOP, STACK_WIN in *; lia|].
    intros i Hi. destruct (FRW (i / 64) ltac:(clear - Hi; Z.div_mod_to_equations; lia)) as ((_ & _ & Wv) & _).
    specialize (Wv (i mod 64) ltac:(apply Z.mod_pos_bound; lia)).
    replace (FSB + 36864 + 64 * (i / 64) + i mod 64) with (FSB + 36864 + i) in Wv by (clear; Z.div_mod_to_equations; lia). exact Wv.
  - apply (KBridge.wr_ok_wr_at asegs m (shad FSB + 4608) 131072); [| lia| lia]. apply wr_at_pointwise;
      [unfold shad, SHB; clear - B1; Z.div_mod_to_equations; lia| unfold shad, SHB, l_ACEIL, USTACK_TOP, STACK_WIN in *; clear - B1 B4 B6; Z.div_mod_to_equations; lia|].
    intros i Hi. destruct (FRW (i / 8) ltac:(clear - Hi; Z.div_mod_to_equations; lia)) as (_ & (_ & _ & Wv)).
    specialize (Wv (i mod 8) ltac:(apply Z.mod_pos_bound; lia)).
    replace (shad FSB + 4608 + 8 * (i / 8) + i mod 8) with (shad FSB + 4608 + i) in Wv by (clear; Z.div_mod_to_equations; lia). exact Wv.
Qed.

End Ring.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WR (FSB : Z) : list (Z * Z) :=
  [(FSB, FSB + 8); (FSB + 4096, FSB + 4096 + 16384); (FSB + 36864, FSB + 36864 + 1048576); (shad FSB + 4608, shad FSB + 4608 + 131072)].

Definition in_WRb (FSB x : Z) : bool :=
  ((FSB <=? x) && (x <? FSB + 8)) || ((FSB + 4096 <=? x) && (x <? FSB + 4096 + 16384))
  || ((FSB + 36864 <=? x) && (x <? FSB + 36864 + 1048576)) || ((shad FSB + 4608 <=? x) && (x <? shad FSB + 4608 + 131072)).

Lemma in_WRb_false : forall FSB x, in_WRb FSB x = false <-> outside (WR FSB) x.
Proof.
  intros FSB x. unfold in_WRb, WR. cbn [outside].
  rewrite !Bool.orb_false_iff, !Bool.andb_false_iff, !Z.leb_gt, !Z.ltb_ge. lia.
Qed.

Lemma ring_FP_WR : forall FSB (x : word), FSB mod 4096 = 0 -> (AIface.ring_FP FSB x <-> ~ outside (WR FSB) (bv_unsigned x)).
Proof.
  intros FSB x H. assert (ESH : AShadow.sha (FSB + 36864) = shad FSB + 4608) by (unfold AShadow.sha, AShadow.SB, shad, SHB; clear - H; Z.div_mod_to_equations; lia).
  unfold AIface.ring_FP, LibKit.inr, WR. rewrite ESH. cbn [outside]. lia.
Qed.

(* [comment removed for export] *)
Definition mix (FSB : Z) (m m' : mem) : mem := fun a => if in_WRb FSB (bv_unsigned a) then m a else m' a.

Lemma mix_in : forall FSB (m m' : mem) a, ~ outside (WR FSB) (bv_unsigned a) -> mix FSB m m' a = m a.
Proof. intros FSB m m' a H. unfold mix. destruct (in_WRb FSB (bv_unsigned a)) eqn:E; [reflexivity|]. exfalso. exact (H (proj1 (in_WRb_false _ _) E)). Qed.
Lemma mix_out : forall FSB (m m' : mem) a, outside (WR FSB) (bv_unsigned a) -> mix FSB m m' a = m' a.
Proof. intros FSB m m' a H. unfold mix. rewrite (proj2 (in_WRb_false _ _) H). reflexivity. Qed.

Lemma mix_munch : forall FSB (m m' : mem), munch (WR FSB) (mix FSB m m') m'.
Proof. intros FSB m m' a Ha. symmetry. exact (mix_out FSB m m' a Ha). Qed.

Lemma mix_wmono_l : forall FSB (m m' : mem), wmono asegs m m' -> wmono asegs m (mix FSB m m').
Proof.
  intros FSB m m' WM a Ha. unfold mix. destruct (in_WRb FSB (bv_unsigned a)) eqn:E.
  - rewrite (wview_agree asegs m (fun a0 => if in_WRb FSB (bv_unsigned a0) then m a0 else m' a0) a); [exact Ha| rewrite E; reflexivity].
  - rewrite (wview_agree asegs m' (fun a0 => if in_WRb FSB (bv_unsigned a0) then m a0 else m' a0) a); [exact (WM a Ha)| rewrite E; reflexivity].
Qed.
Lemma mix_wmono_r : forall FSB (m m' : mem), wmono asegs m m' -> wmono asegs (mix FSB m m') m'.
Proof.
  intros FSB m m' WM a Ha. unfold mix in Ha. destruct (in_WRb FSB (bv_unsigned a)) eqn:E.
  - apply WM. rewrite (wview_agree asegs m (fun a0 => if in_WRb FSB (bv_unsigned a0) then m a0 else m' a0) a) in Ha; [exact Ha| rewrite E; reflexivity].
  - rewrite (wview_agree asegs m' (fun a0 => if in_WRb FSB (bv_unsigned a0) then m a0 else m' a0) a) in Ha; [exact Ha| rewrite E; reflexivity].
Qed.

Section Closers.
Variables (Σ : rtsA).
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).

Lemma mix_ART : forall (m m' : mem) sp, ART_A Σ m -> rtA_sp0 Σ - STACK_WIN <= sp ->
  same_off RTA Σ sp (AIface.ring_FP FSB) m m' -> wmono asegs m m' -> ART_A Σ (mix FSB m m').
Proof.
  intros m m' sp HA Hsp SO WM. destruct (ring_fsb Σ m HA) as (_ & B2 & _).
  apply (ART_client_frame Σ m (mix FSB m m') sp HA Hsp); [| exact (mix_wmono_l FSB m m' WM)].
  intros a NA. unfold mix. destruct (in_WRb FSB (bv_unsigned a)) eqn:E; [reflexivity|].
  apply SO; [exact NA|]. intros HR. apply (proj1 (ring_FP_WR FSB a B2)) in HR. exact (HR (proj1 (in_WRb_false _ _) E)).
Qed.

(* [comment removed for export] *)
Lemma ring_but_fs : forall (m1 m' : mem), ART_A Σ m1 -> munch (WR FSB) m1 m' -> wmono asegs m1 m' -> ART_but_fs Σ m'.
Proof.
  intros m1 m' HA MU WM. destruct (ring_fsb Σ m1 HA) as (B1 & B2 & _).
  apply (ART_transport_but_fs ([(FSB, FSB + 0xb09000)] ++ [(shad FSB, shad (FSB + 0xb09000))]) Σ m1 m' HA); [| exact WM|].
  - apply (munch_weaken (WR FSB)); [| exact MU]. intros x Hx. rewrite shad_fsb_end in Hx. unfold WR. cbn [outside app] in *. lia.
  - exact (art_avoid_but_fs_app _ _ Σ (fsb_avoid Σ m1 HA) (fshad_avoid Σ m1 HA)).
Qed.

(* [comment removed for export] *)
Lemma ring_fs_rest : forall (m1 m' : mem), ART_A Σ m1 -> no_cls0 (frames Σ) -> munch (WR FSB) m1 m' -> wmono asegs m1 m' ->
  fs_const FSB m' /\ fs_cls_rep FSB 2 (fs2 Σ) m' /\ fs_cls_rep FSB 6 (fs6 Σ) m' /\ rw_cells asegs m' tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m') /\ (exists tb te, ttls_cells (l_T L) m' tb te)
  /\ fs_busy L (frames Σ) m'.
Proof.
  intros m1 m' HA NC MU WM. destruct (ring_fsb Σ m1 HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (grant_T Σ m1 HA) as ((T1 & _ & T3 & T4 & _) & TA). destruct (grant_DTV Σ m1 HA) as ((D1 & _ & D3 & D4 & _) & DA).
  assert (SH0 : 0x7fff8000 <= shad FSB /\ shad FSB + 0x161200 <= 0x10007fff8000).
  { unfold shad, SHB, l_ACEIL, USTACK_TOP, STACK_WIN in *. clear - B1 B4 B6. Z.div_mod_to_equations. lia. }
  pose proof (ART_wf Σ m1 HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (_ & (FL2 & _) & (FL6 & _) & _).
  destruct FL2 as (FLEN2 & _). destruct FL6 as (FLEN6 & _). change (NF 2) with 4096 in FLEN2. change (NF 6) with 256 in FLEN6.
  destruct (ART_fs Σ m1 HA) as (F1 & _ & F3 & F4 & TP & (dtvbeg & Hdb & (G1 & G2 & G3 & G4 & (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8))) & (tb & te & TT) & FB).
  unfold SEGTOP_A, apart, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  assert (LIT : forall A cs, rw_cells asegs m1 A cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 0xbca000 -> rw_cells asegs m' A cs).
  { intros A cs H H0 H1. apply (rw_cells_transport asegs (WR FSB) m1 m' _ _ H MU WM). unfold WR. cbn [disjoint_from]. clear - H0 H1 B3 SH0. lia. }
  split; [unfold fs_const in *; apply (rw_cells_transport asegs (WR FSB) m1 m' _ _ F1 MU WM); unfold WR; cbn [disjoint_from cells_size csize Nat.add]; clear - SH0 B5; lia|].
  split.
  { apply (fs_cls_rep_transport (WR FSB) FSB 2 _ m1 m' F3 MU WM). split; [| split].
    - unfold WR. cbn [disjoint_from]. clear - SH0 B5. lia.
    - rewrite FLEN2. change (fl_base FSB 2) with (FSB + 0x1000 + 0x6000). unfold WR. cbn [disjoint_from]. clear - SH0 B5. lia.
    - intros p Hp _. change (NF 2) with 4096 in Hp. rewrite (shad_frame FSB 2 p B2 ltac:(lia) ltac:(lia)). unfold frame_addr. change (fsz 2) with 256.
      change (256 / 8) with 32. replace (SHB + FSB / 8) with (shad FSB) by (unfold shad; lia). unfold WR. cbn [disjoint_from]. clear - Hp SH0 B5. lia. }
  split.
  { apply (fs_cls_rep_transport (WR FSB) FSB 6 _ m1 m' F4 MU WM). split; [| split].
    - unfold WR. cbn [disjoint_from]. clear - SH0 B5. lia.
    - rewrite FLEN6. change (fl_base FSB 6) with (FSB + 0x1000 + 0x7e00). unfold WR. cbn [disjoint_from]. clear - SH0 B5. lia.
    - intros p Hp _. change (NF 6) with 256 in Hp. rewrite (shad_frame FSB 6 p B2 ltac:(lia) ltac:(lia)). unfold frame_addr. change (fsz 6) with 4096.
      change (4096 / 8) with 512. replace (SHB + FSB / 8) with (shad FSB) by (unfold shad; lia). unfold WR. cbn [disjoint_from]. clear - Hp SH0 B5. lia. }
  split; [apply (LIT _ _ TP); unfold tpA; cbn; lia|].
  split.
  { exists dtvbeg. split; [exact Hdb|]. unfold tga_cells, dtls_cells, g_real_tls_get_addr, g_dtv_ptr, g_dtv1, g_got_common_flags, g_intercept_tls_get_addr,
      g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls in *.
    split; [apply (LIT _ _ G1); cbn; lia|]. split; [apply (LIT _ _ G2); cbn; lia|]. split; [apply (LIT _ _ G3); cbn; lia|].
    split; [apply (LIT _ _ G4); cbn; lia|].
    split; [apply (LIT _ _ E1); cbn; lia|]. split; [apply (LIT _ _ E2); cbn; lia|]. split; [apply (LIT _ _ E3); cbn; lia|].
    split; [apply (LIT _ _ E4); cbn; lia|]. split; [apply (LIT _ _ E5); cbn; lia|]. split; [apply (LIT _ _ E6); cbn; lia|].
    split; [apply (LIT _ _ E7); cbn; lia|].
    apply (rw_cells_transport asegs (WR FSB) m1 m' _ _ E8 MU WM). unfold WR. cbn [disjoint_from cells_size csize Nat.add]. clear - D1 D3 D4 DA SH0 B5. lia. }
  split.
  { exists tb, te. unfold ttls_cells in *. apply (rw_cells_transport asegs (WR FSB) m1 m' _ _ TT MU WM). unfold WR. cbn [disjoint_from cells_size csize Nat.add].
    clear - T1 T3 T4 TA SH0 B5. lia. }
  unfold fs_busy in *. apply Forall_forall. intros [f k] Hfk. destruct (proj1 (Forall_forall _ _) FB (f, k) Hfk) as (p & Hp & W1 & W2 & Cw). cbn [fst snd] in *.
  exists p. split; [exact Hp|]. split; [exact (wr_at_transport asegs m1 m' _ _ W1 WM)|]. split; [exact (wr_at_transport asegs m1 m' _ _ W2 WM)|].
  destruct (ring_frames_hi Σ m1 HA f k Hfk (NC f k Hfk)) as (H1 & H2 & _).
  apply (rw_cells_transport asegs (WR FSB) m1 m' _ _ Cw MU WM). unfold WR. cbn [disjoint_from cells_size csize Nat.add].
  assert (0 < fs_size k) by (destruct (sep_frame Σ m1 HA f k Hfk) as (_ & _ & X); exact X).
  assert (8 <= fs_size k) by (destruct (busy_slot Σ m1 HA f k Hfk) as ([E|[E|E]] & _); subst k; vm_compute; discriminate).
  clear - H1 H2 SH0 B5 H H0. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_of_zeros : forall (m : mem) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> AShadow.zeros m a (Z.of_nat n) ->
  bytes_at asegs m a (repeat z8 n).
Proof.
  intros m a n H0 H1 HZ. split; [exact H0|]. split; [rewrite repeat_length; exact H1|]. rewrite repeat_length. intros i Hi.
  unfold mrd. change (wa (a + Z.of_nat i)) with (Z_to_bv 64 (a + Z.of_nat i)). rewrite (HZ (Z.of_nat i) ltac:(lia)).
  rewrite nth_error_repeat by exact Hi. reflexivity.
Qed.

Lemma free_frames_wmono : forall (m m' : mem) fl, fs_free_frames FSB 0 m fl -> wmono asegs m m' -> fs_free_frames FSB 0 m' fl.
Proof.
  intros m m' fl H WM p Hp Hf. destruct (H p Hp Hf) as ((j1 & R1) & (j2 & R2)). change (fsz 0) with 64 in *. change (64 / 8) with 8 in *.
  change (Z.to_nat 64) with 64%nat in *. change (Z.to_nat 8) with 8%nat in *.
  pose proof (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 64 R1 ltac:(cbn; lia)) WM) as W1.
  pose proof (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 8 R2 ltac:(cbn; lia)) WM) as W2.
  split; [exact (I_lkit.wr_at_rw_CB m' _ 64 W1 ltac:(lia))| exact (I_lkit.wr_at_rw_CB m' _ 8 W2 ltac:(lia))].
Qed.

(* [comment removed for export] *)
Lemma flags_mem : forall (m' : mem) (fl : list Z), Z.of_nat (length fl) = 16384 ->
  (forall i, 0 <= i < 16384 -> m' (Z_to_bv 64 (FSB + 4096 + i)) = Some (b8 (nth (Z.to_nat i) fl 1))) ->
  wr_at asegs m' (FSB + 4096) 16384 -> 0 <= FSB -> FSB + 0xb09000 <= 2 ^ 47 -> fs_flags FSB 0 m' fl.
Proof.
  intros m' fl HL HM HW H0 H1. unfold fs_flags. change (fl_base FSB 0) with (FSB + 0x1000 + 0). replace (FSB + 0x1000 + 0) with (FSB + 4096) by lia.
  split; [| rewrite length_map, HL; exact HW]. split; [lia|]. split; [rewrite length_map, HL; lia|]. rewrite length_map. intros i Hi.
  unfold mrd. change (wa (FSB + 4096 + Z.of_nat i)) with (Z_to_bv 64 (FSB + 4096 + Z.of_nat i)). rewrite (HM (Z.of_nat i) ltac:(lia)).
  rewrite nth_error_map_b8 by exact Hi. rewrite Nat2Z.id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ring_close_idle : forall (m m' : mem) sp, ART_A Σ m -> no_cls0 (frames Σ) -> rtA_sp0 Σ - STACK_WIN <= sp ->
  same_off RTA Σ sp (AIface.ring_FP FSB) m m' -> StoreOk.mem_grows m m' ->
  (exists h', 0 <= h' < 2 ^ 64 /\ LibKit.cell ACode.ASEGS m' FSB 8 (Z_to_bv 64 h')) -> AShadow.zeros m' (FSB + 4096) 16384 -> ART_A Σ m'.
Proof.
  intros m m' sp HA NC Hsp SO HG (h' & Hh' & HC) HZ.
  pose proof (KBridge.wmono_of_grows asegs m m' HG) as WM.
  pose proof (mix_ART m m' sp HA Hsp SO WM) as HA1. pose proof (mix_munch FSB m m') as MU. pose proof (mix_wmono_r FSB m m' WM) as WM1.
  destruct (ring_fs_rest _ m' HA1 NC MU WM1) as (F1 & F3 & F4 & TP & DT & TT & FB).
  apply (ART_of_but_fs Σ m' (ART_wf Σ m HA) (ring_but_fs _ m' HA1 MU WM1)).
  destruct (ring_fsb Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (ring_fs0 Σ m HA) as ((CH & CF & CFr) & (FLEN & F01)). change (NF 0) with 16384 in FLEN.
  destruct (ring_idle Σ m HA NC) as (ZALL & _ & _ & (RW1 & RW2 & _)).
  unfold fs_rep. split; [exact F1|]. split; [| split; [exact F3| split; [exact F4| split; [exact TP| split; [exact DT| split; [exact TT| exact FB]]]]]].
  split; [| split].
  - unfold fs_hint_rep. cbn [Z.eqb]. exists h'. split; [exact Hh'|]. unfold fs_hint. replace (FSB + 8 * 0) with FSB by lia.
    unfold fs_hint_rep in CH. cbn [Z.eqb] in CH. destruct CH as (h0 & _ & CH). unfold fs_hint in CH. replace (FSB + 8 * 0) with FSB in CH by lia.
    apply rw_C8_of_cell; [lia| unfold l_ACEIL, USTACK_TOP, STACK_WIN in *; lia| exact HC|].
    exact (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 8 CH ltac:(cbn; lia)) WM).
  - apply flags_mem; [exact FLEN| | | lia| unfold l_ACEIL, USTACK_TOP, STACK_WIN in *; lia].
    + intros i Hi. rewrite (HZ i Hi). rewrite ZALL by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id; lia). reflexivity.
    + unfold fs_flags in CF. change (fl_base FSB 0) with (FSB + 0x1000 + 0) in CF. replace (FSB + 0x1000 + 0) with (FSB + 4096) in CF by lia.
      destruct CF as (_ & CFw). rewrite length_map, FLEN in CFw. exact (wr_at_transport asegs m m' _ _ CFw WM).
  - exact (free_frames_wmono m m' _ CFr WM).
Qed.

(* [comment removed for export] *)
Definition fs_push0 (S0 : rtsA) (k f : Z) : rtsA :=
  mkRtsA (lay S0) (pr S0) (ca S0) (ca_init S0) (sec S0) (sec_nres S0) (aw S0) (ql S0) (qg S0) (dep S0)
    (mkFs (fss_hint (fs0 S0)) (upd (fss_flags (fs0 S0)) (Z.to_nat k) 1)) (fs2 S0) (fs6 S0) (ia_init S0) (credit S0) (live S0)
    ((f, 0%nat) :: frames S0).

Lemma push0_wf : forall (m : mem) k, ART_A Σ m -> no_cls0 (frames Σ) -> 0 <= k < 16384 -> (length (frames Σ) < FRAMES_MAX)%nat ->
  rt_wf (fs_push0 Σ k (frame_addr FSB 0 k)).
Proof.
  intros m k HA NC Hk Hlen.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof W6 as (FW0 & FW2 & FW6 & FWr & FND & FLN & FCNT & FHINT).
  destruct (ring_idle Σ m HA NC) as (ZALL & _). destruct FW0 as ((FLEN & F01) & FH & FNB). change (NF 0) with 16384 in FLEN.
  assert (Hpl : (Z.to_nat k < length (fss_flags (fs0 Σ)))%nat) by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id by lia; lia).
  assert (NB0 : nbusy (fss_flags (fs0 Σ)) = 0%nat).
  { pose proof (FCNT 0%nat ltac:(left; reflexivity)) as C. cbn [fs_of] in C. rewrite (filter_no_cls0 _ NC) in C. cbn [length] in C. lia. }
  unfold rt_wf. split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
  split; [| split; [exact W7| split; [exact W8| split; [exact W9| split; [exact W10| exact W11]]]]].
  unfold fs_wf. cbn [fs0 fs2 fs6 frames fs_push0 lay credit].
  split.
  { split; [| split]; cbn [fss_flags fss_hint].
    - apply flags_ok_upd; [split; [exact FLEN| exact F01]| right; reflexivity].
    - exact FH.
    - rewrite (nbusy_upd_set _ _ Hpl (ZALL _ Hpl)), NB0. lia. }
  split; [exact FW2|]. split; [exact FW6|].
  split.
  { apply Forall_cons.
    - cbn [fst snd]. split; [left; reflexivity|]. exists k. split; [change (NF (Z.of_nat 0)) with 16384; exact Hk|]. split; [reflexivity|].
      cbn [fs_of fs0 fs_push0 fss_flags]. apply nth_upd_same. exact Hpl.
    - apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & p2 & Hp2 & Hf2 & Hb2).
      cbn [fst snd] in *. split; [exact Hk2|]. exists p2. split; [exact Hp2|]. split; [exact Hf2|].
      pose proof (NC f2 k2 Hin) as K0. destruct Hk2 as [E|[E|E]]; [contradiction| |]; subst k2; exact Hb2. }
  split.
  { apply NoDup_ListNoDup. constructor; [| apply NoDup_ListNoDup; exact FND]. intros Hin. exact (NC _ _ Hin eq_refl). }
  split; [cbn [length]; unfold FRAMES_MAX in Hlen; lia|].
  split.
  - intros k' Hk'. rewrite filter_cons_class. pose proof (FCNT k' Hk') as C.
    destruct Hk' as [E|[E|E]]; subst k'; cbn [Nat.eqb fs_of fs0 fs2 fs6 fs_push0 fss_flags length].
    + rewrite (nbusy_upd_set _ _ Hpl (ZALL _ Hpl)), NB0. rewrite (filter_no_cls0 _ NC). reflexivity.
    + exact C.
    + exact C.
  - intros k' Hk'. pose proof (FHINT k' Hk') as X. destruct Hk' as [E|[E|E]]; subst k'; exact X.
Qed.

Lemma W_wrap : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma byte_of_cell1 : forall (m' : mem) a (b : byte), 0xbca000 <= a -> a + 1 <= 2 ^ 64 -> LibKit.cell ACode.ASEGS m' a 1 (zxb b) ->
  m' (Z_to_bv 64 a) = Some b.
Proof.
  intros m' a b Ha Hb HC. pose proof (KBridge.bytes_of_cell asegs m' a 1 (zxb b) ltac:(lia) ltac:(lia) HC) as BY.
  change (word_to_le_bytes 1 (zxb b)) with (le1 (zxb b)) in BY. rewrite le1_zxb in BY.
  pose proof (bytes_offA m' a [b] 0 BY ltac:(right; lia) ltac:(cbn; lia)) as E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma ring_close_push : forall (m m' : mem) sp h, ART_A Σ m -> no_cls0 (frames Σ) -> rtA_sp0 Σ - STACK_WIN <= sp ->
  (length (frames Σ) < FRAMES_MAX)%nat ->
  same_off RTA Σ sp (AIface.ring_FP FSB) m m' -> StoreOk.mem_grows m m' ->
  let k := h mod 16384 in let FB := FSB + 36864 + 64 * k in
  LibKit.cell ACode.ASEGS m' FSB 8 (Z_to_bv 64 (h + 1)) -> LibKit.cell ACode.ASEGS m' (FSB + 4096 + k) 1 (Z_to_bv 64 1) ->
  AShadow.zeros m' (FSB + 4096) k -> AShadow.zeros m' (FSB + 4096 + k + 1) (16383 - k) ->
  LibKit.cell ACode.ASEGS m' (FB + 56) 8 (Z_to_bv 64 (FSB + 4096 + k)) ->
  exists Σ', ART_A Σ' m' /\ frames Σ' = (FB, 0%nat) :: frames Σ /\ live Σ' = live Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ
    /\ credit Σ' = credit Σ /\ rtA_allow Σ' = rtA_allow Σ /\ (forall mo, ARTM_A Σ mo -> ARTM_A Σ' mo).
Proof.
  intros m m' sp h HA NC Hsp Hlen SO HG k FB HC1 HCF HZ1 HZ2 HC56.
  assert (Hk : 0 <= k < 16384) by (unfold k; apply Z.mod_pos_bound; lia).
  pose proof (KBridge.wmono_of_grows asegs m m' HG) as WM.
  pose proof (mix_ART m m' sp HA Hsp SO WM) as HA1. pose proof (mix_munch FSB m m') as MU. pose proof (mix_wmono_r FSB m m' WM) as WM1.
  destruct (ring_fs_rest _ m' HA1 NC MU WM1) as (F1 & F3 & F4 & TP & DT & TT & FBS).
  destruct (ring_fsb Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (ring_fs0 Σ m HA) as ((CH & CF & CFr) & (FLEN & F01)). change (NF 0) with 16384 in FLEN.
  destruct (ring_idle Σ m HA NC) as (ZALL & _).
  assert (EFB : FB = frame_addr FSB 0 k) by (unfold FB, frame_addr; change (fsz 0) with 64; lia).
  assert (Hpl : (Z.to_nat k < length (fss_flags (fs0 Σ)))%nat) by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id by lia; lia).
  exists (fs_push0 Σ k FB).
  split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity| split; [reflexivity| split; [reflexivity| intros mo Hmo; exact Hmo]]]]]].
  rewrite EFB. apply (ART_of_but_fs _ m' (push0_wf m k HA NC Hk Hlen)); [exact (ring_but_fs _ m' HA1 MU WM1)|].
  unfold fs_rep. cbn [lay fs0 fs2 fs6 frames fs_push0].
  split; [exact F1|]. split; [| split; [exact F3| split; [exact F4| split; [exact TP| split; [exact DT| split; [exact TT|]]]]]].
  - split; [| split]; cbn [fss_hint fss_flags].
    + unfold fs_hint_rep. cbn [Z.eqb]. exists ((h + 1) mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|]. unfold fs_hint. replace (FSB + 8 * 0) with FSB by lia.
      unfold fs_hint_rep in CH. cbn [Z.eqb] in CH. destruct CH as (h0 & _ & CH). unfold fs_hint in CH. replace (FSB + 8 * 0) with FSB in CH by lia.
      rewrite <- W_wrap. apply rw_C8_of_cell; [lia| unfold l_ACEIL, USTACK_TOP, STACK_WIN in *; lia| exact HC1|].
      exact (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 8 CH ltac:(cbn; lia)) WM).
    + apply flags_mem; [rewrite upd_length; exact FLEN| | | lia| unfold l_ACEIL, USTACK_TOP, STACK_WIN in *; lia].
      * intros i Hi. destruct (Z.eq_dec i k) as [->|NE].
        { rewrite nth_upd_same by exact Hpl. apply byte_of_cell1; [unfold SEGTOP_A in B3; lia| unfold l_ACEIL, USTACK_TOP, STACK_WIN in *; lia|]. exact HCF. }
        rewrite nth_upd_other by (intros E; apply NE; apply Z2Nat.inj; lia). rewrite ZALL by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id; lia).
        destruct (Z_lt_le_dec i k) as [LT|GE]; [exact (HZ1 i ltac:(lia))|].
        pose proof (HZ2 (i - k - 1) ltac:(lia)) as E. replace (FSB + 4096 + k + 1 + (i - k - 1)) with (FSB + 4096 + i) in E by lia. exact E.
      * unfold fs_flags in CF. change (fl_base FSB 0) with (FSB + 0x1000 + 0) in CF. replace (FSB + 0x1000 + 0) with (FSB + 4096) in CF by lia.
        destruct CF as (_ & CFw). rewrite length_map, FLEN in CFw. exact (wr_at_transport asegs m m' _ _ CFw WM).
    + intros p Hp Hf. apply (free_frames_wmono m m' _ CFr WM p Hp). apply ZALL. change (NF 0) with 16384 in Hp. apply Nat2Z.inj_lt. rewrite FLEN, Z2Nat.id; lia.
  - unfold fs_busy. apply Forall_cons; [| exact FBS]. cbn [fst snd]. exists k. split; [reflexivity|].
    destruct (CFr k ltac:(change (NF 0) with 16384; exact Hk) (ZALL _ Hpl)) as ((j1 & R1) & (j2 & R2)).
    change (fs_size 0) with 64. change (fsz 0) with 64 in *. change (64 / 8) with 8 in *. change (Z.to_nat 64) with 64%nat in *. change (Z.to_nat 8) with 8%nat in *.
    pose proof (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 64 R1 ltac:(cbn; lia)) WM) as W1.
    pose proof (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 8 R2 ltac:(cbn; lia)) WM) as W2.
    split; [exact W1|]. split; [exact W2|]. rewrite <- EFB. replace (FB + 64 - 8) with (FB + 56) by lia.
    change (fl_base FSB (Z.of_nat 0)) with (FSB + 0x1000 + 0). replace (FSB + 0x1000 + 0 + k) with (FSB + 4096 + k) by lia.
    apply rw_C8_of_cell; [unfold FB; lia| unfold FB, l_ACEIL, USTACK_TOP, STACK_WIN in *; lia| exact HC56|].
    rewrite <- EFB in W1. apply (wr_at_sub m' FB 64); [exact W1| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma nbusy_pos : forall (fl : list Z) p, nth p fl 0 = 1 -> (1 <= nbusy fl)%nat.
Proof.
  induction fl as [|z r IH]; intros p H; [destruct p; discriminate H|]. destruct p as [|p]; cbn [nth nbusy] in *.
  - subst z. cbn. lia.
  - pose proof (IH p H). destruct (Z.eqb z 0); lia.
Qed.

Lemma nbusy_one : forall (fl : list Z) p, nbusy fl = 1%nat -> nth p fl 0 = 1 -> forall i, (i < length fl)%nat -> i <> p -> nth i fl 1 = 0.
Proof.
  induction fl as [|z r IH]; intros p HN HP i Hi NE; [cbn in Hi; lia|]. cbn [nbusy] in HN. cbn [length] in Hi.
  destruct p as [|p]; cbn [nth] in HP.
  - subst z. cbn in HN. destruct i as [|i]; [contradiction|]. cbn [nth]. apply nbusy_zero_nth; lia.
  - pose proof (nbusy_pos r p HP) as P1. destruct (Z.eqb_spec z 0) as [Ez|Ez]; [| lia].
    destruct i as [|i]; cbn [nth]; [exact Ez|]. apply (IH p); [lia| exact HP| lia| lia].
Qed.

Definition mix1 (fl : Z) (m m' : mem) : mem := fun a => if Z.eqb (bv_unsigned a) fl then m a else m' a.

Lemma ring_view1 : forall (m : mem) FB fr, ART_A Σ m -> frames Σ = (FB, 0%nat) :: fr -> no_cls0 fr ->
  exists k, 0 <= k < 16384 /\ FB = FSB + 36864 + 64 * k
    /\ (forall f j, In (f, j) fr -> FSB + 1085440 <= f /\ f + fs_size j <= FSB + 0xb09000)
    /\ LibKit.cell ACode.ASEGS m (FB + 56) 8 (Z_to_bv 64 (FSB + 4096 + k))
    /\ AShadow.zeros m (FSB + 4096) k /\ AShadow.zeros m (FSB + 4096 + k + 1) (16383 - k)
    /\ LibKit.wr_ok ACode.ASEGS m FB 8 /\ LibKit.wr_ok ACode.ASEGS m (AShadow.sha FB) 8 /\ LibKit.wr_ok ACode.ASEGS m (FSB + 4096 + k) 1
    /\ ~ aclient (live Σ) (frames Σ) (rtA_sp0 Σ - STACK_WIN) (FSB + 4096 + k)
    /\ (forall m' sp, rtA_sp0 Σ - STACK_WIN <= sp -> same_off RTA Σ sp (fun a => LibKit.inr a (FSB + 4096 + k) 1) m m' ->
          StoreOk.mem_grows m m' -> AShadow.zeros m' (FSB + 4096) 16384 ->
          exists Σ', ART_A Σ' m' /\ frames Σ' = fr /\ live Σ' = live Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ
            /\ rtA_allow Σ' = rtA_allow Σ /\ (forall mo, ARTM_A Σ mo -> ARTM_A Σ' mo)).
Proof.
  intros m FB fr HA HF NC. destruct (rel_slot Σ m FB 0 fr HA HF) as (_ & p & Hp & EFB & HB). change (NF (Z.of_nat 0)) with 16384 in Hp.
  change (Z.of_nat 0) with 0 in *. cbn [fs_of] in HB.
  destruct (ring_fsb Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (ring_fs0 Σ m HA) as ((CH & CF & CFr) & (FLEN & F01)). change (NF 0) with 16384 in FLEN.
  assert (Hpl : (Z.to_nat p < length (fss_flags (fs0 Σ)))%nat) by (apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id by lia; lia).
  assert (NB1 : nbusy (fss_flags (fs0 Σ)) = 1%nat).
  { pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (_ & _ & _ & _ & _ & _ & FCNT & _).
    pose proof (FCNT 0%nat ltac:(left; reflexivity)) as C. cbn [fs_of] in C. rewrite HF, filter_cons_class in C. cbn [Nat.eqb] in C.
    rewrite (filter_no_cls0 _ NC) in C. cbn [length] in C. lia. }
  assert (FLM : forall i, 0 <= i < 16384 -> m (Z_to_bv 64 (FSB + 4096 + i)) = Some (b8 (nth (Z.to_nat i) (fss_flags (fs0 Σ)) 1))).
  { intros i Hi. unfold fs_flags in CF. change (fl_base FSB 0) with (FSB + 0x1000 + 0) in CF. replace (FSB + 0x1000 + 0) with (FSB + 4096) in CF by lia.
    destruct CF as (CFb & _).
    rewrite (bytes_offA m (FSB + 4096) _ i CFb ltac:(rewrite length_map, FLEN; unfold SEGTOP_A in B3; right; lia) ltac:(rewrite length_map, FLEN; exact Hi)).
    apply nth_error_map_b8. apply Nat2Z.inj_lt. rewrite FLEN, Z2Nat.id; lia. }
  assert (ZOTH : forall i, 0 <= i < 16384 -> i <> p -> m (Z_to_bv 64 (FSB + 4096 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi NE. rewrite (FLM i Hi). rewrite (nbusy_one _ (Z.to_nat p) NB1 HB); [reflexivity| apply Nat2Z.inj_lt; rewrite FLEN, Z2Nat.id; lia|].
    intros E. apply NE. apply Z2Nat.inj; lia. }
  assert (EFB' : FB = FSB + 36864 + 64 * p) by (rewrite EFB; unfold frame_addr; change (fsz 0) with 64; lia).
  destruct (rta_frame_release_at Σ m FB 0 fr HA HF p ltac:(left; reflexivity) ltac:(exact Hp) EFB HB) as (FLC & NAC & FL0 & FLW & FW & _).
  change (fl_base FSB (Z.of_nat 0)) with (FSB + 0x1000 + 0) in *. replace (FSB + 0x1000 + 0 + p) with (FSB + 4096 + p) in * by lia.
  change (fs_size 0) with 64 in FW. replace (FB + 64 - 8) with (FB + 56) in FW by lia.
  exists p. split; [exact Hp|]. split; [exact EFB'|].
  split.
  { intros f j Hin. assert (Hin' : In (f, j) (frames Σ)) by (rewrite HF; right; exact Hin).
    destruct (ring_frames_hi Σ m HA f j Hin' (NC f j Hin)) as (H1 & H2 & _). split; assumption. }
  split; [exact (KBridge.cell_C8 asegs m _ _ FW)|].
  split; [intros i Hi; apply ZOTH; lia|].
  split; [intros i Hi; replace (FSB + 4096 + p + 1 + i) with (FSB + 4096 + (p + 1 + i)) by lia; apply ZOTH; lia|].
  destruct (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & FBS). unfold fs_busy in FBS. rewrite HF in FBS. apply Forall_cons_iff in FBS. destruct FBS as ((p' & _ & WF & WSH & _) & _).
  cbn [fst snd] in WF, WSH. change (fs_size 0) with 64 in WF, WSH. change (64 / 8) with 8 in WSH.
  split; [exact (KBridge.wr_ok_wr_at asegs m FB 64 FB 8 WF ltac:(lia) ltac:(lia))|].
  split; [exact (KBridge.wr_ok_wr_at asegs m (shad FB) 8 (shad FB) 8 WSH ltac:(lia) ltac:(lia))|].
  split; [exact (KBridge.wr_ok_wr_at asegs m (FSB + 4096 + p) 1 (FSB + 4096 + p) 1 (rw_cells_wr_at asegs m _ _ 1 FLC ltac:(cbn; lia)) ltac:(lia) ltac:(lia))|].
  split.
  { intros [H|H]; [unfold rtA_sp0 in *; lia|]. apply NAC. right. exact H. }
  intros m' sp Hsp SO HG HZ. pose proof (KBridge.wmono_of_grows asegs m m' HG) as WM.
  set (fl := FSB + 4096 + p) in *.
  assert (HA1 : ART_A Σ (mix1 fl m m')).
  { apply (ART_client_frame Σ m (mix1 fl m m') sp HA Hsp).
    - intros a NA. unfold mix1. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|NE]; [reflexivity|]. apply SO; [exact NA|]. unfold LibKit.inr. lia.
    - intros a Ha. unfold mix1. destruct (Z.eqb (bv_unsigned a) fl) eqn:E.
      + rewrite (wview_agree asegs m (fun a0 => if Z.eqb (bv_unsigned a0) fl then m a0 else m' a0) a); [exact Ha| rewrite E; reflexivity].
      + rewrite (wview_agree asegs m' (fun a0 => if Z.eqb (bv_unsigned a0) fl then m a0 else m' a0) a); [exact (WM a Ha)| rewrite E; reflexivity]. }
  destruct (rta_frame_release_at Σ (mix1 fl m m') FB 0 fr HA1 HF p ltac:(left; reflexivity) ltac:(exact Hp) EFB HB) as (_ & _ & _ & _ & _ & REL).
  change (fl_base FSB (Z.of_nat 0)) with (FSB + 0x1000 + 0) in REL. replace (FSB + 0x1000 + 0 + p) with fl in REL by (unfold fl; lia).
  exists (fs_release Σ 0 p fr). apply REL.
  - intros a Ho. cbn [outside] in Ho. unfold mix1. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|NE]; [exfalso; lia| reflexivity].
  - intros a Ha. unfold mix1 in Ha. destruct (Z.eqb (bv_unsigned a) fl) eqn:E.
    + apply WM. rewrite (wview_agree asegs m (fun a0 => if Z.eqb (bv_unsigned a0) fl then m a0 else m' a0) a) in Ha; [exact Ha| rewrite E; reflexivity].
    + rewrite (wview_agree asegs m' (fun a0 => if Z.eqb (bv_unsigned a0) fl then m a0 else m' a0) a) in Ha; [exact Ha| rewrite E; reflexivity].
  - split; [split; [exact (conj I I)|]|].
    + apply (bytes_of_zeros m' fl 1); [unfold fl; lia| unfold fl, l_ACEIL, USTACK_TOP, STACK_WIN in *; lia|].
      intros i Hi. replace (fl + i) with (FSB + 4096 + (p + i)) by (unfold fl; lia). apply HZ. lia.
    + exact (wr_at_transport asegs m m' _ _ (rw_cells_wr_at asegs m _ _ 1 FLC ltac:(cbn; lia)) WM).
Qed.

End Closers.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ring0_ok : ring0_facts RTA.
Proof.
  apply mkR0.
  - intros Σ m HA MI NC. cbn [ART RTA] in HA. cbn [rt_frames RTA] in NC. unfold rtA_frames in NC.
    destruct (ring_idle Σ m HA NC) as (_ & (h & Hh & HC) & HZ & RW).
    exists (l_FSB (lay Σ)), (l_DTV (lay Σ)), (l_TCX (lay Σ)), (l_T (lay Σ)), h.
    split; [unfold liba_rt; split; [exact (ring_rt_ok Σ m HA)| split; [exact (ring_ic_ok Σ m HA MI)| split; [exact (ring_fsrt_ok Σ m HA)|
              split; [exact (ring_fsrt_wf Σ m HA)| split; [exact (ring_uar_on Σ m HA)| exact (ring_fs_wf Σ m HA)]]]]]|].
    split; [exact (ring_geo_ok Σ m HA)|]. split; [exact Hh|]. split; [exact HC|]. split; [exact HZ|]. split; [exact RW|].
    split; [exact (ring_apart Σ m HA NC)|].
    split.
    + intros m' sp Hsp SO HG HH HZ'. exact (ring_close_idle Σ m m' sp HA NC Hsp SO HG HH HZ').
    + intros m' sp Hsp Hlen SO HG. exact (ring_close_push Σ m m' sp h HA NC Hsp Hlen SO HG).
  - intros Σ m FB fr HA HF NC. cbn [ART RTA] in HA. cbn [rt_frames RTA] in HF. unfold rtA_frames in HF.
    destruct (ring_view1 Σ m FB fr HA HF NC) as (k & Hk & EFB & FRH & C56 & ZA & ZB & W1 & W2 & W3 & NAF & REL).
    destruct (ring_fsb Σ m HA) as (_ & _ & _ & B4 & _).
    exists (l_FSB (lay Σ)), k. split; [exact (ring_fs_wf Σ m HA)|]. split; [exact Hk|]. split; [exact EFB|].
    split; [unfold AIface.FS_SIZE; cbn [rt_sp0 RTA]; unfold rtA_sp0, l_ACEIL in *; lia|].
    split; [unfold AIface.FS_SIZE; exact FRH|].
    split; [unfold AIface.FS_SIZE; exact (ring_live_apart Σ m HA)|].
    split; [exact C56|]. split; [exact ZA|]. split; [exact ZB|]. split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [exact NAF|]. exact REL.
  - intros Σ m p n HA Hin. exact (ring_live_mem Σ m HA p n Hin).
  - intros Σ m HA. exact (ring_xn_shadow Σ m HA).
Qed.

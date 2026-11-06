(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout PEnv APrim APrimLem LJ LJU APrimPop APrimPopR APrimSpec2 APrimQ AFrame APrimFrame AFrameM.
Import ListNotations.
Open Scope Z_scope.

Definition gmw (W : list (Z * Z)) (m m' : mem) : Prop := gmunch W m m' /\ wmono asegs m m'.

Lemma gmw_of_munch : forall W m m', munch W m m' -> wmono asegs m m' -> gmw W m m'.
Proof. intros W m m' MU WM. split; [apply gmunch_of_munch; exact MU| exact WM]. Qed.

Lemma rw_cells_transport_g : forall W m m' A cs,
  rw_cells asegs m A cs -> gmw W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros W m m' A cs C [G WM] D. exact (rw_cells_gtransport W m m' A cs C G WM D). Qed.
Lemma u32arr_transport_g : forall W m m' A ws,
  u32arr asegs m A ws -> gmw W m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros W m m' A ws C [G WM] D. exact (u32arr_gtransport W m m' A ws C G WM D). Qed.
Lemma u64arr_transport_g : forall W m m' A ws,
  u64arr asegs m A ws -> gmw W m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros W m m' A ws C [G WM] D. exact (u64arr_gtransport W m m' A ws C G WM D). Qed.
Lemma stk_transport_g : forall W m m' lo hi,
  stk asegs m lo hi -> gmw W m m' -> disjoint_from W lo (hi - lo) -> stk asegs m' lo hi.
Proof. intros W m m' lo hi C [G WM] D. exact (stk_gtransport W m m' lo hi C G WM D). Qed.

Lemma free_chunk_frame_g : forall {HC : HasCeiling} AL W m m' c v,
  free_chunk AL m c v -> gmw W m m' -> 1 <= c <= 31 ->
  disjoint_from W (region AL c + 16 * v) (class_size c) -> disjoint_from W (sh (region AL c + 16 * v)) (class_size c / 8) ->
  free_chunk AL m' c v.
Proof.
  intros HC AL W m m' c v [[j B] S] MU Hc D1 D2. pose proof (class_size_pos c Hc) as CS. split; [exists j|].
  - eapply rw_cells_transport_g; [exact B| exact MU|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact D1.
  - eapply rw_cells_transport_g; [exact S| exact MU|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (pose proof (Z.div_pos (class_size c) 8); lia). exact D2.
Qed.

Ltac frame_cell_g C MU F :=
  eapply rw_cells_transport_g; [exact C| exact MU|
    apply disjoint_from_of_Forall; eapply Forall_impl; [| exact F]; intros [lo' hi'] Hiv'; cbn in Hiv' |- *; lia].

Lemma poison_env_frame_g : forall {HC : HasCeiling} E W m m', poison_env E m -> gmw W m m' -> above_img W -> poison_env E m'.
Proof.
  intros HC E W m m' PE MU F. unfold above_img in F. pe_split PE. unfold poison_env.
  repeat match goal with |- _ /\ _ => split end; try lia.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_g C MU F end.
Qed.
Lemma prim_env_frame_g : forall {HC : HasCeiling} AL W m m', prim_env AL m -> gmw W m m' -> above_img W -> prim_env AL m'.
Proof. intros HC AL W m m' P MU F. unfold above_img in F. unfold prim_env in *. frame_cell_g P MU F. Qed.
Lemma thread_env_frame_g : forall {HC : HasCeiling} L W m m', thread_env L m -> gmw W m m' -> thread_clear L W -> thread_env L m'.
Proof.
  intros HC L W m m' TE MU F. unfold thread_clear in F. te_split TE. unfold thread_env.
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_g C MU F end.
Qed.

Section CF.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Variables (c : Z) (k : pclass).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis WF : pclass_wf c k.
Notation REG := (region AL c).

#[using="HC AO Hc"] Lemma cf_arith_g :
  REG mod 8 = 0 /\ al_space AL + K_REGION <= REG /\ REG + K_REGION <= al_space AL + K_SPACE
  /\ (forall x8, 0 <= x8 -> sh (REG + 8 * x8) = sh REG + x8)
  /\ (forall a, 0 <= a < 2^47 -> sh a < al_space AL)
  /\ al_space AL + K_SPACE + 4096 <= 2^47 /\ 0 <= al_space AL.
Proof.
  pose proof (REG_mod8 AL AO c) as R8. pose proof (region_range AL c Hc) as [R1 R2].
  layout_facts AO 0%nat SPF. destruct SPF as (S1 & S2 & _ & _ & S5 & _ & S7).
  split; [exact R8|]. split; [exact R1|]. split; [exact R2|].
  split; [intros x8 _; apply (sh_off8 _ _ R8)|]. split; [exact S7|]. split; lia.
Qed.

#[using="HC AO Hc WF"] Lemma cls_body_frame_g : forall (W : list (Z * Z)) (m m' : mem),
  cls_body AL c k m -> gmw W m m' -> Forall (cls_miss_body AL c k) W -> cls_body AL c k m'.
Proof.
  intros W m m' (RI & (ws & FA & FL & FX) & ((jt & TL) & TSH) & FCH) MU CM.
  pose proof cf_arith_g as (R8 & R1 & R2 & SHO & SHL & TOP & SP0).
  pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CS16.
  pose proof WF as WF0. unfold pclass_wf in WF0.
  destruct WF0 as (_ & _ & _ & _ & MFA & _ & AU & MUF & MUM & AUS & _ & _ & FB & _).

  assert (EZ : exists z8, class_size c = 8 * z8 /\ 4 <= z8) by (exists (class_size c / 8); Z.div_mod_to_equations; lia). destruct EZ as (z8 & Hz8 & Z4).
  assert (EA : exists a8, p_au k = 8 * a8 /\ 0 <= a8).
  { exists (p_au k / 8). assert (X : p_au k mod 16 = 0).
    { apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (class_size c)); apply Z.mod_divide; lia. }
    Z.div_mod_to_equations. lia. }
  destruct EA as (a8 & Ha8 & A80).
  assert (EM : exists m8, p_mu k = 8 * m8 /\ a8 <= m8) by (exists (p_mu k / 8); Z.div_mod_to_equations; lia). destruct EM as (m8 & Hm8 & M8).
  assert (SZD : class_size c / 8 = z8) by (rewrite Hz8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (TD : (p_mu k - p_au k) / 8 = m8 - a8) by (rewrite Hm8, Ha8; replace (8 * m8 - 8 * a8) with ((m8 - a8) * 8) by lia; apply Z.div_mul; lia).
  assert (SHK : sh (REG + K_REGION) = sh REG + 536870912) by (rewrite <- (SHO 536870912) by lia; reflexivity).

  assert (CHK : forall v, ~ In v (cls_free k) -> 0 <= v -> (16 * v) mod class_size c = 0 -> 16 * v + class_size c <= p_au k ->
                exists v8, 16 * v = 8 * v8 /\ 0 <= v8 /\ v8 + z8 <= a8 /\ sh (REG + 16 * v) = sh REG + v8
                /\ forall x, In x (p_fa k ++ p_chunks k) -> exists x8, 16 * x = 8 * x8 /\ 0 <= x8 /\ x8 + z8 <= a8 /\ (v8 + z8 <= x8 \/ x8 + z8 <= v8)).
  { intros v NF V0 VA VB. exists (2 * v). split; [lia|]. split; [lia|]. split; [lia|].
    split; [replace (16 * v) with (8 * (2 * v)) by lia; apply SHO; lia|].
    intros x Hx. pose proof (proj1 (Forall_forall _ _) FB x Hx) as (X0 & X1 & X2). cbv beta in X0, X1, X2.
    exists (2 * x). split; [lia|]. split; [lia|]. split; [lia|].
    assert (NE : v <> x) by (intros ->; apply NF; exact Hx).
    pose proof (chunks_apart c v x Hc VA X2 NE). lia. }
  unfold cls_miss_body in CM.
  split; [| split; [| split]].
  -
    destruct RI as (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC). exists j8, j64, j88, j96, j104, j112, jpad.
    eapply rw_cells_transport_g; [exact RIC| exact MU|].
    pose proof (rw_cells_bound asegs _ _ _ RIC) as RB. unfold ri_cells in RB |- *. cbn [cells_size csize Nat.add] in RB |- *.
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] (H1 & _). cbn [fst snd] in *. lia.
  -
    exists ws. split; [| split; [exact FL| exact FX]].
    eapply u32arr_transport_g; [exact FA| exact MU|]. rewrite FL.
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] (_ & [[H3 H4]|(v & NF & V0 & VA & VB & [CI|CI])]); cbn [fst snd] in *.
    + unfold fa_base. lia.
    + unfold chunk_iv in CI. cbn [fst snd] in CI. unfold fa_base. lia.
    + unfold chunk_sh_iv in CI. cbn [fst snd] in CI. destruct (CHK v NF V0 VA VB) as (v8 & E8 & V80 & VZ & SHV & _).
      rewrite SHV, SZD in CI. pose proof (SHL (REG + 8 * (v8 + z8)) ltac:(lia)) as X. rewrite SHO in X by lia. unfold fa_base. lia.
  -
    split.
    + exists jt. eapply rw_cells_transport_g; [exact TL| exact MU|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] (_ & [[H3 H4]|(v & NF & V0 & VA & VB & [CI|CI])]); cbn [fst snd] in *.
      * lia.
      * unfold chunk_iv in CI. cbn [fst snd] in CI. lia.
      * unfold chunk_sh_iv in CI. cbn [fst snd] in CI. destruct (CHK v NF V0 VA VB) as (v8 & E8 & V80 & VZ & SHV & _).
        rewrite SHV, SZD in CI. pose proof (SHL (REG + 8 * (v8 + z8)) ltac:(lia)) as X. rewrite SHO in X by lia. lia.
    + eapply rw_cells_transport_g; [exact TSH| exact MU|]. cbn [cells_size csize]. rewrite Nat.add_0_r, TD, Z2Nat.id by lia.
      rewrite Ha8, SHO by lia.
      apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] (_ & [[H3 H4]|(v & NF & V0 & VA & VB & [CI|CI])]); cbn [fst snd] in *.
      * rewrite SHK in H4. lia.
      * unfold chunk_iv in CI. cbn [fst snd] in CI. pose proof (SHL (REG + 8 * m8) ltac:(lia)) as X. rewrite SHO in X by lia. lia.
      * unfold chunk_sh_iv in CI. cbn [fst snd] in CI. destruct (CHK v NF V0 VA VB) as (v8 & E8 & V80 & VZ & SHV & _).
        rewrite SHV, SZD in CI. lia.
  -
    intros x Hx. eapply free_chunk_frame_g; [apply FCH; exact Hx| exact MU| exact Hc| |].
    + apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] (_ & [[H3 H4]|(v & NF & V0 & VA & VB & [CI|CI])]); cbn [fst snd] in *.
      * pose proof (proj1 (Forall_forall _ _) FB x Hx) as (X0 & X1 & _). cbv beta in X0, X1. lia.
      * unfold chunk_iv in CI. cbn [fst snd] in CI. destruct (CHK v NF V0 VA VB) as (v8 & E8 & V80 & VZ & SHV & AP).
        destruct (AP x Hx) as (x8 & EX & X80 & XZ & APX). lia.
      * unfold chunk_sh_iv in CI. cbn [fst snd] in CI. destruct (CHK v NF V0 VA VB) as (v8 & E8 & V80 & VZ & SHV & AP).
        rewrite SHV, SZD in CI. pose proof (SHL (REG + 8 * (v8 + z8)) ltac:(lia)) as X. rewrite SHO in X by lia.
        pose proof (proj1 (Forall_forall _ _) FB x Hx) as (X0 & X1 & _). cbv beta in X0, X1. lia.
    + rewrite SZD.
      apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] (_ & [[H3 H4]|(v & NF & V0 & VA & VB & [CI|CI])]); cbn [fst snd] in *.
      * pose proof (proj1 (Forall_forall _ _) FB x Hx) as (X0 & X1 & X2). cbv beta in X0, X1, X2.
        assert (EX : exists x8, 16 * x = 8 * x8 /\ 0 <= x8 /\ x8 + z8 <= a8) by (exists (2 * x); lia). destruct EX as (x8 & EX & X80 & XZ).
        rewrite EX, SHO by lia. rewrite SHK in H4. lia.
      * unfold chunk_iv in CI. cbn [fst snd] in CI.
        pose proof (proj1 (Forall_forall _ _) FB x Hx) as (X0 & X1 & X2). cbv beta in X0, X1, X2.
        assert (EX : exists x8, 16 * x = 8 * x8 /\ 0 <= x8 /\ x8 + z8 <= a8) by (exists (2 * x); lia). destruct EX as (x8 & EX & X80 & XZ).
        rewrite EX, SHO by lia. pose proof (SHL (REG + 8 * (x8 + z8)) ltac:(lia)) as X. rewrite SHO in X by lia. lia.
      * unfold chunk_sh_iv in CI. cbn [fst snd] in CI. destruct (CHK v NF V0 VA VB) as (v8 & E8 & V80 & VZ & SHV & AP).
        destruct (AP x Hx) as (x8 & EX & X80 & XZ & APX). rewrite SHV, SZD in CI. rewrite EX, SHO by lia. lia.
Qed.

#[using="Type"] Lemma pcl_rep_frame_g : forall (ini : bool) (W : list (Z * Z)) (m m' : mem),
  pcl_rep AL m ini c k -> gmw W m m' ->
  Forall (fun iv : Z * Z => snd iv <= pcl_addr AL c \/ pcl_addr AL c + 80 <= fst iv) W -> pcl_rep AL m' ini c k.
Proof.
  intros ini W m m' (PC & (cs & CA & CL & CX)) MU CM. split.
  - eapply rw_cells_transport_g; [exact PC| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] H2. cbn [fst snd] in *. lia.
  - exists cs. split; [| split; [exact CL| exact CX]].
    eapply u32arr_transport_g; [exact CA| exact MU|]. rewrite CL.
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact CM]. intros [lo' hi'] H2. cbn [fst snd] in *. lia.
Qed.

#[using="HC AO Hc WF"] Lemma cls_rep_frame_g : forall (ini : bool) (W : list (Z * Z)) (m m' : mem),
  cls_rep AL m ini c k -> gmw W m m' -> Forall (cls_miss AL c k) W -> cls_rep AL m' ini c k.
Proof.
  intros ini W m m' (_ & RI & PC & FA & TL & FCH) MU CM.
  destruct (cls_body_frame_g W m m' (conj RI (conj FA (conj TL FCH))) MU) as (RI' & FA' & TL' & FCH').
  { eapply Forall_impl; [| exact CM]. intros iv [_ B]. exact B. }
  split; [exact WF|]. split; [exact RI'|]. split; [| split; [exact FA'| split; [exact TL'| exact FCH']]].
  apply (pcl_rep_frame_g ini W m m' PC MU). eapply Forall_impl; [| exact CM]. intros iv [B _]. exact B.
Qed.
End CF.

Section PF.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Notation THR := (at_thr (al_thread AL)).

#[using="HC AO"] Lemma held_iv_bounds_g : forall P m c0 v0 iv, RPRIM AL P m -> held1 P (c0, v0) ->
  (chunk_iv AL c0 v0 iv \/ chunk_sh_iv AL c0 v0 iv) ->
  1 <= c0 <= 31 /\
  ((region AL c0 <= fst iv /\ snd iv <= region AL c0 + FA_OFF)
   \/ (sh (region AL c0) <= fst iv /\ snd iv <= sh (region AL c0 + FA_OFF))).
Proof.
  intros P m c0 v0 iv (_ & _ & CLS & _) (Hc0 & V0 & V1 & VA & _) CI. cbn [fst snd] in *.
  destruct (CLS c0 Hc0) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _ & AUS & _) & _).
  pose proof (class_size_pos c0 Hc0) as CS. pose proof (class_size_mod16 c0 Hc0) as CS16.
  split; [exact Hc0|]. destruct CI as [CI|CI].
  - left. unfold chunk_iv in CI. lia.
  - right. unfold chunk_sh_iv in CI.
    pose proof (REG_mod8 AL AO c0) as R8.
    assert (E8 : exists v8 z8, 16 * v0 = 8 * v8 /\ class_size c0 = 8 * z8 /\ 0 <= v8 /\ 0 <= z8).
    { exists (2 * v0), (class_size c0 / 8). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
    destruct E8 as (v8 & z8 & E1 & E2 & V80 & Z80).
    assert (SZD : class_size c0 / 8 = z8) by (rewrite E2, Z.mul_comm, Z.div_mul by lia; reflexivity).
    rewrite E1, (sh_off8 _ _ R8), SZD in CI.
    pose proof (sh_le (region AL c0 + 8 * (v8 + z8)) (region AL c0 + FA_OFF) ltac:(lia)) as X. rewrite (sh_off8 _ _ R8) in X. lia.
Qed.

#[using="HC AO"] Theorem RPRIM_frame_g : forall P W m m', RPRIM AL P m -> gmw W m m' -> prim_clear AL P W -> RPRIM AL P m'.
Proof.
  intros P W m m' RP MU PCW. pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)). unfold prim_clear in PCW.
  layout_facts AO 0%nat SPF. destruct SPF as (S1 & S2 & _ & _ & S5 & _ & S7).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_apart_fact AO 0%nat 3%nat LP03.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.

  assert (SHA : 2147450880 <= sh (al_space AL) /\ sh (al_space AL + K_SPACE + 4096) <= 17594333495296 /\ sh (al_space AL + K_SPACE + 4096) < al_space AL).
  { split; [pose proof (sh_le 0 (al_space AL) ltac:(lia)) as X; exact X|].
    split; [pose proof (sh_le (al_space AL + K_SPACE + 4096) (2^47) ltac:(lia)) as X; exact X| apply S7; lia]. }

  assert (GEN : Forall (fun iv : Z * Z =>
            prim_out AL iv
            \/ exists c0, 1 <= c0 <= 31 /\ ((region AL c0 <= fst iv /\ snd iv <= region AL c0 + FA_OFF)
                                            \/ (sh (region AL c0) <= fst iv /\ snd iv <= sh (region AL c0 + FA_OFF)))) W).
  { eapply Forall_impl; [| exact PCW]. intros iv [PO|(c0 & v0 & HH & CI)]; [left; exact PO|].
    right. exists c0. exact (held_iv_bounds_g P m c0 v0 iv RP HH CI). }

  assert (REGS : forall c0, 1 <= c0 <= 31 ->
            al_space AL + K_REGION <= region AL c0 /\ region AL c0 + K_REGION <= al_space AL + K_SPACE
            /\ sh (al_space AL) <= sh (region AL c0) /\ sh (region AL c0 + FA_OFF) <= sh (al_space AL + K_SPACE + 4096)).
  { intros c0 Hc0. pose proof (region_range AL c0 Hc0) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
    split; apply sh_le; lia. }
  split; [exact LEN|]. split; [| split; [| split]].
  -
    unfold prim_env in *. eapply rw_cells_transport_g; [exact PENV| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact GEN].
    intros [lo' hi'] [(_ & _ & _ & P4)|(c0 & Hc0 & B)]; cbn [fst snd] in *; [lia|].
    destruct (REGS c0 Hc0) as (R1 & R2 & R3 & R4). lia.
  -
    intros c Hc. destruct (CLS c Hc) as (WFc & _).
    apply (cls_rep_frame_g AL AO c (get_cls P c) Hc WFc (pr_inited P) W m m' (CLS c Hc) MU).
    eapply Forall_impl; [| exact PCW]. intros [lo' hi'] [PO|(c0 & v0 & HH & CI)].
    + destruct PO as (P1 & P2 & P3 & _). cbn [fst snd] in *. destruct (REGS c Hc) as (R1 & R2 & R3 & R4).
      pose proof (sh_le (region AL c + K_REGION) (al_space AL + K_SPACE + 4096) ltac:(lia)) as X.
      unfold cls_miss, cls_miss_body. cbn [fst snd]. split; [unfold pcl_addr; lia|]. split; [unfold ri_addr, RIB; lia|]. left. lia.
    + destruct (held_iv_bounds_g P m c0 v0 _ RP HH CI) as (Hc0 & B). cbn [fst snd] in B.
      destruct (REGS c0 Hc0) as (Q1 & Q2 & Q3 & Q4). destruct (REGS c Hc) as (R1 & R2 & R3 & R4).
      unfold cls_miss, cls_miss_body. cbn [fst snd].
      split; [unfold pcl_addr; clear - B Q1 Q2 Q3 Q4 SHA T3 T4 LP03 Hc; lia|].
      split; [unfold ri_addr, RIB; clear - B Q1 Q2 Q4 SHA Hc; lia|].
      destruct (Z.eq_dec c0 c) as [->|NE].
      * right. exists v0. destruct HH as (_ & V0 & V1 & VA & NF). cbn [fst snd] in *. repeat split; assumption.
      * left. pose proof (sh_le (region AL c + K_REGION) (al_space AL + K_SPACE + 4096) ltac:(lia)) as X.
        destruct (Z_lt_le_dec c0 c) as [LT|GE].
        -- pose proof (sh_le (region AL c0 + FA_OFF) (region AL c) ltac:(unfold region; lia)) as Y.
           unfold region in *. clear - B Y X LT SHA Q1 Q2 Q3 Q4 R1 R2 R3 R4. lia.
        -- pose proof (sh_le (region AL c + K_REGION) (region AL c0) ltac:(unfold region; lia)) as Y.
           unfold region in *. clear - B Y X GE NE SHA Q1 Q2 Q3 Q4 R1 R2 R3 R4. lia.
  -
    eapply rw_cells_transport_g; [exact STAT| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact GEN].
    intros [lo' hi'] [(_ & _ & P3 & _)|(c0 & Hc0 & B)]; cbn [fst snd] in *; [lia|].
    destruct (REGS c0 Hc0) as (R1 & R2 & R3 & R4). clear - B R1 R2 R3 R4 SHA T3 T4 LP03. lia.
  -
    exists ts. eapply rw_cells_transport_g; [exact TS| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact GEN].
    intros [lo' hi'] [(_ & _ & P3 & _)|(c0 & Hc0 & B)]; cbn [fst snd] in *; [lia|].
    destruct (REGS c0 Hc0) as (R1 & R2 & R3 & R4). clear - B R1 R2 R3 R4 SHA T3 T4 LP03. lia.
Qed.

#[using="HC AO"] Theorem RPRIM_frame_ts_g : forall P W m m', RPRIM AL P m -> gmw W m m' -> prim_clear_ts AL P W ->
  (exists ts', rw_cells asegs m' (THR + TSTATS_OFF) [CB 368 ts']) -> RPRIM AL P m'.
Proof.
  intros P W m m' RP MU PCW TS'. pose proof RP as (LEN & PENV & CLS & STAT & _). unfold prim_clear_ts in PCW.
  layout_facts AO 0%nat SPF. destruct SPF as (S1 & S2 & _ & _ & S5 & _ & S7).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_apart_fact AO 0%nat 3%nat LP03.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.

  assert (SHA : 2147450880 <= sh (al_space AL) /\ sh (al_space AL + K_SPACE + 4096) <= 17594333495296 /\ sh (al_space AL + K_SPACE + 4096) < al_space AL).
  { split; [pose proof (sh_le 0 (al_space AL) ltac:(lia)) as X; exact X|].
    split; [pose proof (sh_le (al_space AL + K_SPACE + 4096) (2^47) ltac:(lia)) as X; exact X| apply S7; lia]. }

  assert (GEN : Forall (fun iv : Z * Z =>
            prim_out AL iv
            \/ (exists c0, 1 <= c0 <= 31 /\ ((region AL c0 <= fst iv /\ snd iv <= region AL c0 + FA_OFF)
                                            \/ (sh (region AL c0) <= fst iv /\ snd iv <= sh (region AL c0 + FA_OFF))))
            \/ (THR + TSTATS_OFF <= fst iv /\ snd iv <= THR + TSTATS_OFF + 368)) W).
  { eapply Forall_impl; [| exact PCW]. intros iv [PO|[(c0 & v0 & HH & CI)|TSI]]; [left; exact PO| | right; right; exact TSI].
    right. left. exists c0. exact (held_iv_bounds_g P m c0 v0 iv RP HH CI). }

  assert (REGS : forall c0, 1 <= c0 <= 31 ->
            al_space AL + K_REGION <= region AL c0 /\ region AL c0 + K_REGION <= al_space AL + K_SPACE
            /\ sh (al_space AL) <= sh (region AL c0) /\ sh (region AL c0 + FA_OFF) <= sh (al_space AL + K_SPACE + 4096)).
  { intros c0 Hc0. pose proof (region_range AL c0 Hc0) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
    split; apply sh_le; lia. }
  split; [exact LEN|]. split; [| split; [| split]].
  -
    unfold prim_env in *. eapply rw_cells_transport_g; [exact PENV| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact GEN].
    intros [lo' hi'] [(_ & _ & _ & P4)|[(c0 & Hc0 & B)|TSI]]; cbn [fst snd] in *; [lia| | clear - TSI T3 T4; lia].
    destruct (REGS c0 Hc0) as (R1 & R2 & R3 & R4). lia.
  -
    intros c Hc. destruct (CLS c Hc) as (WFc & _).
    apply (cls_rep_frame_g AL AO c (get_cls P c) Hc WFc (pr_inited P) W m m' (CLS c Hc) MU).
    eapply Forall_impl; [| exact PCW]. intros [lo' hi'] [PO|[(c0 & v0 & HH & CI)|TSI]].
    + destruct PO as (P1 & P2 & P3 & _). cbn [fst snd] in *. destruct (REGS c Hc) as (R1 & R2 & R3 & R4).
      pose proof (sh_le (region AL c + K_REGION) (al_space AL + K_SPACE + 4096) ltac:(lia)) as X.
      unfold cls_miss, cls_miss_body. cbn [fst snd]. split; [unfold pcl_addr; lia|]. split; [unfold ri_addr, RIB; lia|]. left. lia.
    + destruct (held_iv_bounds_g P m c0 v0 _ RP HH CI) as (Hc0 & B). cbn [fst snd] in B.
      destruct (REGS c0 Hc0) as (Q1 & Q2 & Q3 & Q4). destruct (REGS c Hc) as (R1 & R2 & R3 & R4).
      unfold cls_miss, cls_miss_body. cbn [fst snd].
      split; [unfold pcl_addr; clear - B Q1 Q2 Q3 Q4 SHA T3 T4 LP03 Hc; lia|].
      split; [unfold ri_addr, RIB; clear - B Q1 Q2 Q4 SHA Hc; lia|].
      destruct (Z.eq_dec c0 c) as [->|NE].
      * right. exists v0. destruct HH as (_ & V0 & V1 & VA & NF). cbn [fst snd] in *. repeat split; assumption.
      * left. pose proof (sh_le (region AL c + K_REGION) (al_space AL + K_SPACE + 4096) ltac:(lia)) as X.
        destruct (Z_lt_le_dec c0 c) as [LT|GE].
        -- pose proof (sh_le (region AL c0 + FA_OFF) (region AL c) ltac:(unfold region; lia)) as Y.
           unfold region in *. clear - B Y X LT SHA Q1 Q2 Q3 Q4 R1 R2 R3 R4. lia.
        -- pose proof (sh_le (region AL c + K_REGION) (region AL c0) ltac:(unfold region; lia)) as Y.
           unfold region in *. clear - B Y X GE NE SHA Q1 Q2 Q3 Q4 R1 R2 R3 R4. lia.
    + cbn [fst snd] in TSI. destruct (REGS c Hc) as (R1 & R2 & R3 & R4).
      pose proof (sh_le (region AL c + K_REGION) (al_space AL + K_SPACE + 4096) ltac:(lia)) as X.
      unfold cls_miss, cls_miss_body. cbn [fst snd]. split; [unfold pcl_addr; clear - TSI Hc; lia|].
      split; [unfold ri_addr, RIB; clear - TSI LP03 Hc; lia|]. left. clear - TSI R1 R2 R3 R4 X SHA T3 T4 LP03. lia.
  -
    eapply rw_cells_transport_g; [exact STAT| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_from_of_Forall. eapply Forall_impl; [| exact GEN].
    intros [lo' hi'] [(_ & _ & P3 & _)|[(c0 & Hc0 & B)|TSI]]; cbn [fst snd] in *; [lia| | clear - TSI; lia].
    destruct (REGS c0 Hc0) as (R1 & R2 & R3 & R4). clear - B R1 R2 R3 R4 SHA T3 T4 LP03. lia.
  -
    exact TS'.
Qed.
End PF.

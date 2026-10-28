(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freeA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_anndefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition set_ann (Σ : rtsA) (A : list (Z * Z * Z)) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fs0 Σ) (fsc0 Σ) (fs4 Σ) (fs1 Σ)
         (ia_init Σ) (credit Σ) (live Σ) (frames Σ) A.

Definition W_ann (a len ACEIL usp : Z) : list ivl := [(shad a, shad a + len / 8); (ACEIL, usp)].

Section AnnArt.
Variables (Σ : rtsA) (mX : mem) (elo ehi a len usp : Z) (D : list (Z * nat)) (DS : list nat).
Hypothesis HA : ART_A Σ mX.
Hypothesis He : 0 <= elo /\ elo <= a /\ a + len <= ehi /\ ehi <= 2 ^ 47 /\ 0 <= len.
Hypothesis Husp : l_ACEIL (lay Σ) <= usp <= USTACK_TOP.

Hypothesis E_slot : forall c' i' st, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  p_abeg (l_SB (lay Σ)) c' i' + ClassSize c' <= elo \/ ehi <= p_abeg (l_SB (lay Σ)) c' i'.
Hypothesis E_reg : forall c', 1 <= c' <= 31 ->
  rb (l_SB (lay Σ)) c' + 2 ^ 32 <= elo \/ ehi <= rb (l_SB (lay Σ)) c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c'))).
Hypothesis E_app : forall lo hi, (hi <= l_PRB (lay Σ) \/ l_PRB (lay Σ) + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) -> hi <= elo \/ ehi <= lo.

Hypothesis D_alloc : forall c i, In (c, i) D -> exists n, nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation W := (W_ann a len (l_ACEIL (lay Σ)) usp).

Lemma an_HG : geo_ok Σ. Proof. exact (geo_of_ART Σ mX HA). Qed.

Lemma an_geo : SHB <= shad elo /\ shad elo <= shad a /\ shad a + len / 8 <= shad ehi /\ shad ehi <= 2 ^ 44 + SHB
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47
  /\ 0 < PRB /\ SEGTOP_A <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000.
Proof.
  destruct He as (E0 & E1 & E2 & E3 & E4).
  pose proof (fk_aceil Σ an_HG) as (X1 & X2). pose proof (fk_prb Σ an_HG) as (P0 & P1 & P2 & P3 & P4).
  split; [apply shad_lo; lia|]. split; [apply fk_shad_mono; lia|].
  split; [pose proof (fk_shad_le2 a len ltac:(lia) E4); pose proof (fk_shad_mono (a + len) ehi E2); lia|].
  split; [apply shad_hi; lia|]. repeat split; lia.
Qed.

Local Ltac geo := pose proof an_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
Local Ltac w2 t1 t2 := unfold W_ann; cbn [disjoint_from]; split; [t1 | split; [t2 | exact I]].
Local Ltac kst := unfold SHB, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, USTACK_TOP in *; lia.

Lemma an_img : forall x k, 0x10000 <= x -> x + k <= SEGTOP_A -> disjoint_from (@nil ivl) x k -> disjoint_from W x k.
Proof. intros x k H1 H2 _. geo. w2 ltac:(left; clear - H2 G1 G2; kst) ltac:(left; clear - H2 G8 G9; kst). Qed.

Lemma an_grant_in : forall b gn x k, In (b, gn) (startup_grants L) -> b <= x -> x + k <= b + gn -> disjoint_from W x k.
Proof.
  intros b gn x k Hin H1 H2. geo. pose proof (g_grant Σ an_HG b gn Hin) as (B1 & B2 & B3 & B4 & B5).
  w2 ltac:(destruct B4 as [B4|B4]; [left; clear - H1 H2 B4 G1 G2; kst | right; clear - H1 H2 B4 G3 G4; kst]) ltac:(left; clear - H2 B3; lia).
Qed.

Lemma an_T : forall x k, T <= x -> x + k <= T + 4096 -> disjoint_from (@nil ivl) x k -> disjoint_from W x k.
Proof. intros x k H1 H2 _. apply (an_grant_in T 4096); [unfold startup_grants; right; right; left; reflexivity | lia | lia]. Qed.

Lemma an_grant : forall j b gn x k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= x -> x + k <= b + gn -> disjoint_from W x k.
Proof. intros j b gn x k Hj _ H1 H2. exact (an_grant_in b gn x k (nth_error_In _ _ Hj) H1 H2). Qed.

Lemma an_grant67 : forall j b gn x k, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= x -> x + k <= b + gn -> disjoint_from W x k.
Proof. intros j b gn x k Hj _ H1 H2. exact (an_grant_in b gn x k (nth_error_In _ _ Hj) H1 H2). Qed.

Lemma an_prb_in : forall x k, PRB <= x -> x + k <= PRB + 0x2000011000 -> disjoint_from W x k.
Proof. intros x k H1 H2. apply (an_grant_in PRB 0x2000011000); [unfold startup_grants; left; reflexivity | lia | lia]. Qed.

Lemma an_ris : forall x k, RIS_of SB <= x -> x + k <= RIS_of SB + 4096 -> disjoint_from W x k.
Proof. intros x k H1 H2. geo. apply an_prb_in; unfold RIS_of in *; lia. Qed.

Lemma an_fa : forall c' x k, 1 <= c' <= 31 -> ~ In c' (@nil Z) -> fa SB c' <= x -> x + k <= fa SB c' + kFaCap -> disjoint_from W x k.
Proof.
  intros c' x k Hc' _ H1 H2. geo. assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia).
  apply an_prb_in; unfold fa, rb, kFaCap in *; [clear - Hc' H1 G10; lia | clear - H H2 G11; lia].
Qed.

Lemma an_slot' : forall c' i' st x k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st ->
  p_abeg SB c' i' <= x -> x + k <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W x k.
Proof.
  intros c' i' st x k Hc' Hn' H1 H2. geo. pose proof (fk_slot Σ an_HG c' i' st Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia).
  apply an_prb_in; unfold rb, kUserCap in *; [clear - Hc' H1 Z1 G10; lia | clear - H H2 Z2 Z3 G11; lia].
Qed.
Lemma an_slot : forall c' i' st x k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  p_abeg SB c' i' <= x -> x + k <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W x k.
Proof. intros c' i' st x k Hc' Hn' _ H1 H2. exact (an_slot' c' i' st x k Hc' Hn' H1 H2). Qed.

Lemma an_secmap' : forall k s x k', nth_error (sec Σ) k = Some s -> s_mb s <= x -> x + k' <= s_mb s + smsz (s_n s) -> disjoint_from W x k'.
Proof.
  intros k s x k' Hk H1 H2. geo. pose proof (map_geo Σ mX HA k s Hk) as (_ & (B1 & B2 & B3 & B4 & B5) & _).
  w2 ltac:(destruct B4 as [B4|B4]; [left; clear - H1 H2 B4 G1 G2; kst | right; clear - H1 H2 B4 G3 G4; kst]) ltac:(left; clear - H2 B3; lia).
Qed.
Lemma an_secmap : forall k s x k', nth_error (sec Σ) k = Some s -> ~ In k DS -> s_mb s <= x -> x + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from W x k'.
Proof. intros k s x k' Hk _ H1 H2. exact (an_secmap' k s x k' Hk H1 H2). Qed.

Lemma an_stack : forall x k, usp <= x -> x + k <= USTACK_TOP -> disjoint_from W x k.
Proof. intros x k H1 H2. geo. w2 ltac:(right; clear - H1 G3 G4 G5 Husp; lia) ltac:(right; exact H1). Qed.

Lemma an_shad_slot : forall c' i' st x k, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') D ->
  shad (p_abeg SB c' i') <= x -> x + k <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W x k.
Proof.
  intros c' i' st x k Hc' Hn' HD H1 H2. geo. pose proof (fk_slot Σ an_HG c' i' st Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
  pose proof (E_slot c' i' st Hc' Hn' HD) as Y.
  assert (Ysh : shad (p_abeg SB c' i' + ClassSize c') <= shad elo \/ shad ehi <= shad (p_abeg SB c' i'))
    by (destruct Y as [Y|Y]; [left | right]; apply fk_shad_mono; exact Y).
  assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia).
  pose proof (shad_hi (p_abeg SB c' i' + ClassSize c') ltac:(unfold rb, kUserCap in *; clear - H Z2 Z3 G11 G9 G6; lia)) as Q2.
  w2 ltac:(clear - H1 H2 Ysh G2 G3; lia) ltac:(left; clear - H2 Q2 G5; lia).
Qed.

Lemma an_shad_reg : forall c' x k, 1 <= c' <= 31 -> ~ In c' (@nil Z) ->
  shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= x -> x + k <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W x k.
Proof.
  intros c' x k Hc' _ H1 H2. geo. pose proof (E_reg c' Hc') as Y.
  assert (Ysh : shad (rb SB c' + 2 ^ 32) <= shad elo \/ shad ehi <= shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))))
    by (destruct Y as [Y|Y]; [left | right]; apply fk_shad_mono; exact Y).
  assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia).
  pose proof (shad_hi (rb SB c' + 2 ^ 32) ltac:(unfold rb in *; clear - H G11 G9 G6; lia)) as Q2.
  w2 ltac:(clear - H1 H2 Ysh G2 G3; lia) ltac:(left; clear - H2 Q2 G5; lia).
Qed.

Lemma an_shad_app : forall lo hi x k, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k' s', nth_error (sec Σ) k' = Some s' -> In k' DS -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= x -> x + k <= shad hi -> disjoint_from W x k.
Proof.
  intros lo hi x k H0 H47 Hoff Hds H1 H2. geo. pose proof (E_app lo hi Hoff Hds) as Y.
  assert (Ysh : shad hi <= shad elo \/ shad ehi <= shad lo) by (destruct Y as [Y|Y]; [left | right]; apply fk_shad_mono; exact Y).
  pose proof (shad_hi hi H47) as Q2.
  w2 ltac:(clear - H1 H2 Ysh G2 G3; lia) ltac:(left; clear - H2 Q2 G5; lia).
Qed.

Lemma an_batch : forall i, nth_error (r_st (pr Σ 24)) i = Some CkBatch -> ~ In (24, i) D.
Proof. intros i Hi Hin. destruct (D_alloc 24 i Hin) as (n & Hn). rewrite Hn in Hi. discriminate Hi. Qed.

Lemma an_consts : forall (m' : mem), munch W mX m' -> wmono asegs mX m' -> consts_rep L m'.
Proof.
  intros m' MU WM. apply (consts_rep_frame L mX m' (ART_consts Σ mX HA)); [|exact WM].
  intros x Hx. apply MU. destruct (Z.eq_dec (bv_unsigned x) (T + 0xc60)) as [E|NE].
  - apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply an_T; [lia | lia | exact I].
  - apply (kv_consts Σ W [] [] an_img an_T an_grant); [apply Forall_forall; intros r _; exact I | exact I | exact Hx | exact NE].
Qed.

Lemma an_client : forall x, aclient (live Σ) (frames Σ) usp x -> outside W x.
Proof.
  intros x Hx.
  assert (K : forall x', aclient [] (frames Σ) usp x' -> outside W x').
  { exact (kv_client Σ W D DS [] usp an_HG an_img an_grant an_slot an_shad_app an_secmap an_stack
             ltac:(apply Forall_forall; intros r _; exact I) [] ltac:(intros p n [])). }
  destruct Hx as [H|[H|[H|[H|H]]]].
  - apply K. left; exact H.
  - apply K. right; left; exact H.
  - destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
    destruct (geo_live Σ mX HA p n Hin) as [(c & i & Hc & Hn & -> & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hn' & -> & X1 & X5)].
    + apply (an_slot' c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia].
    + destruct (In_nth_error _ _ Hs) as (k & Hk). pose proof (map_geo Σ mX HA k s Hk) as (_ & (B1 & _) & _ & _ & Hroom).
      apply (an_secmap' k s); [exact Hk | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Hn' in *; lia].
  - apply K. right; right; right; left; exact H.
  - apply K. right; right; right; right; exact H.
Qed.

Lemma an_pchunk : forall (m' : mem) (A' : list (Z * Z * Z)) c i st, munch W mX m' -> wmono asegs mX m' ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  (forall n, st = CkAlloc n -> alook (p_abeg SB c i + rz_size n) n A' = alook (p_abeg SB c i + rz_size n) n (ann Σ)) ->
  pchunk A' SB c i st m'.
Proof.
  intros m' A' c i st MU WM Hc Hn HD HAL. destruct (ART_chunk Σ mX HA) as [P _].
  apply (pchunk_annbr (ann Σ)); [exact HAL|].
  exact (pchunk_transport W _ c i st mX m' (P c i st Hc Hn) MU WM (kv_pchunk Σ W D an_HG an_slot an_shad_slot c i st Hc Hn HD)).
Qed.
Lemma an_schunk : forall (m' : mem) (A' : list (Z * Z * Z)) k s, munch W mX m' -> wmono asegs mX m' ->
  nth_error (sec Σ) k = Some s -> ~ In k DS ->
  alook (s_mb s + 4096 + 2048) (s_n s) A' = alook (s_mb s + 4096 + 2048) (s_n s) (ann Σ) ->
  schunk A' k s m'.
Proof.
  intros m' A' k s MU WM Hk HD HAL. destruct (ART_chunk Σ mX HA) as [_ S].
  apply (schunk_annbr (ann Σ)); [exact HAL|].
  exact (schunk_transport W k s mX m' (S k s Hk) MU WM (kv_schunk Σ W DS an_HG an_shad_app an_secmap k s Hk HD)).
Qed.

Theorem ann_ART : forall (m' : mem) (A' : list (Z * Z * Z)), munch W mX m' -> wmono asegs mX m' ->
  chunk_rep (set_ann Σ A') m' -> ART_A (set_ann Σ A') m'.
Proof.
  intros m' A' MU WM CH.
  pose proof (kv_reg Σ W [] an_HG (ris_of_whole SB W [] an_ris) an_fa an_shad_reg) as KR.
  apply ART_intro; [exact (ART_wf Σ mX HA) | | | | exact CH | | | | | | |];
    cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 ia_init credit live frames ann set_ann].
  - exact (an_consts m' MU WM).
  - intros c Hc. exact (reg_rep_transport W _ c _ mX m' (ART_prim Σ mX HA c Hc) MU WM (KR c Hc ltac:(intros []))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ mX m' (ART_cache Σ mX HA c Hc) MU WM (kv_pclass Σ W [] an_T c Hc I)).
  - exact (sec_rep_transport W Σ mX m' (ART_sec Σ mX HA) MU WM (kv_sec Σ W [] an_HG an_img an_grant ltac:(apply Forall_forall; intros r _; exact I))).
  - exact (quar_rep_transport W Σ mX m' (ART_quar Σ mX HA) MU WM
             (kv_quar Σ W D [] [] an_HG an_img an_T an_slot I ltac:(apply Forall_forall; intros r _; exact I) an_batch
                ltac:(pose proof (ART_wf Σ mX HA) as (_ & _ & _ & _ & HQw & _); exact (proj1 (proj2 (proj2 HQw)))))).
  - pose proof (ART_wf Σ mX HA) as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W L (dep Σ) mX m' (ART_dep Σ mX HA) Hdok MU WM
             (kv_dep Σ W [] an_img ltac:(apply Forall_forall; intros r _; exact I) an_grant67)).
  - exact (fs_rep_transport W Σ mX m' (ART_fs Σ mX HA) MU WM
             (kv_fs Σ W DS [] [] an_HG an_img an_T an_grant an_shad_app ltac:(apply Forall_forall; intros r _; exact I) I)).
  - exact (ia_rep_transport W Σ mX m' (ART_ia Σ mX HA) MU WM (kv_ia W [] an_img ltac:(apply Forall_forall; intros r _; exact I))).
  - exact (shadow_rep_transport W L mX m' (ART_shadow Σ mX HA) MU WM (kv_shadow Σ W DS an_HG an_shad_app)).
  - exact (vis_rep_wmono _ mX m' (ART_vis Σ mX HA) WM).
Qed.

End AnnArt.

End GWIN.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition W_frR (T usp : Z) : list ivl := [(T + 2768, T + 3169); (7325128, 7325132); (6741312, 7269744); (usp - 2352, usp)].
Definition TZ_R (T : Z) : list ivl := [(T + 2768, T + 3169)].
Definition IZ_R : list ivl := [(7325128, 7325132); (6741312, 7269744)].

Section FrR.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation W := (W_frR (l_T (lay Σ)) usp).
#[local] Notation TZ := (TZ_R (l_T (lay Σ))).

Lemma fr_geo : 0 < T /\ T + 4096 <= l_ACEIL L /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T) /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T)
  /\ 0 < PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ SEGTOP_A <= PRB /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ (T + 4096 <= PRB \/ PRB + 0x2000011000 <= T).
Proof.
  pose proof (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (G1 & _ & G3 & G4 & G5).
  pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (P0 & P1 & P2 & P3 & P4). pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (X1 & X2).
  pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. cbn [fst snd] in A02. unfold apart in A02.
  repeat split; try assumption; lia.
Qed.

Ltac frgeo := pose proof fr_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
Ltac frdj := unfold fa, RIS_of in *; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, rb, kUserCap, kFaCap, apart in *; lia.

(* [comment removed for export] *)
Lemma fr_off : forall a n, (a + n <= T \/ T + 4096 <= a) -> (a + n <= 0x10000 \/ SEGTOP_A <= a) -> a + n <= l_ACEIL L -> disjoint_from W a n.
Proof.
  intros a n H1 H2 H3. frgeo. unfold W_frR. cbn [disjoint_from].
  split; [clear - H1; lia|]. split; [clear - H2; frdj|]. split; [clear - H2; frdj|]. split; [clear - H3 Hsp; lia | exact I].
Qed.

Lemma fr_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ_R a n -> disjoint_from W a n.
Proof.
  intros a n H1 H2 HZ. frgeo. cbn [IZ_R disjoint_from] in HZ. destruct HZ as (Z1 & Z2 & _). unfold W_frR. cbn [disjoint_from].
  split; [clear - H1 H2 K4; frdj|]. split; [exact Z1|]. split; [exact Z2|]. split; [clear - H2 K10 Hsp; frdj | exact I].
Qed.

Lemma fr_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Proof.
  intros a n H1 H2 HZ. frgeo. cbn [TZ_R disjoint_from] in HZ. destruct HZ as [HZ _]. unfold W_frR. cbn [disjoint_from].
  split; [exact HZ|]. split; [clear - H1 H2 K4; frdj|]. split; [clear - H1 H2 K4; frdj|]. split; [clear - H2 K2 Hsp; lia | exact I].
Qed.

Lemma fr_apart : forall j j' g1 g2, j <> j' -> nth_error (startup_grants L) j = Some g1 -> nth_error (startup_grants L) j' = Some g2 ->
  apart (fst g1) (snd g1) (fst g2) (snd g2).
Proof.
  intros j j' g1 g2 Hne H1 H2. destruct (Nat.lt_ge_cases j j') as [Hl|Hl]; [exact (geo_apart Σ m HA j j' g1 g2 Hl H1 H2)|].
  pose proof (geo_apart Σ m HA j' j g2 g1 ltac:(lia) H2 H1) as X. unfold apart in *. lia.
Qed.

Lemma fr_grant_ne2 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> j <> 2%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof.
  intros j b gn a n Hj Hj2 H1 H2. pose proof (geo_grant Σ m HA b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  pose proof (fr_apart j 2 (b, gn) (T, 4096) Hj2 Hj eq_refl) as HT1. cbn [fst snd] in HT1. unfold apart in HT1.
  apply fr_off; [clear - H1 H2 HT1; lia | clear - H1 H2 B1 B5; unfold SEGTOP_A in *; lia | clear - H2 B3; lia].
Qed.

Lemma fr_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof. intros j b gn a n Hj Hjr. apply (fr_grant_ne2 j b gn a n Hj). clear - Hjr. lia. Qed.

(* [comment removed for export] *)
Lemma fr_prb : forall a n, PRB <= a -> a + n <= PRB + 0x2000011000 -> disjoint_from W a n.
Proof. intros a n H1 H2. frgeo. apply fr_off; [clear - H1 H2 K12; lia | clear - H1 K7; unfold SEGTOP_A in *; lia | clear - H2 K6; lia]. Qed.

(* [comment removed for export] *)
Lemma fr_shad : forall a n, SHB <= a -> a + n <= 2 ^ 44 + SHB -> disjoint_from W a n.
Proof.
  intros a n H1 H2. frgeo.
  apply fr_off; [clear - H1 H2 K3; frdj | clear - H1; frdj | clear - H2 K10; lia].
Qed.

Lemma fr_ris : forall a n, RIS_of SB <= a -> a + n <= RIS_of SB + 4096 -> disjoint_from W a n.
Proof. intros a n H1 H2. frgeo. apply fr_prb; clear - H1 H2 K8 K9; frdj. Qed.

Lemma fr_fa : forall c a n, 1 <= c <= 31 -> fa SB c <= a -> a + n <= fa SB c + kFaCap -> disjoint_from W a n.
Proof. intros c a n Hc H1 H2. frgeo. apply fr_prb; clear - Hc H1 H2 K8 K9; frdj. Qed.

Lemma fr_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  p_abeg SB c i <= a -> a + n <= p_abeg SB c i + ClassSize c -> disjoint_from W a n.
Proof.
  intros c i st a n Hc Hn _ H1 H2. frgeo. pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i _ Hc Hn) as (Z1 & Z2 & Z3 & Z4).
  apply fr_prb; clear - Hc H1 H2 Z1 Z2 Z3 K8 K9; unfold rb, kUserCap in *; lia.
Qed.

Lemma fr_shad_le : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof. intros lo hi a n H0 H47 H1 H2. pose proof (shad_lo lo H0) as Q1. pose proof (shad_hi hi H47) as Q2. apply fr_shad; lia. Qed.

Lemma fr_shad_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Proof.
  intros c i st a n Hc Hn _ H1 H2. frgeo. pose proof (fk_slot Σ (geo_of_ART Σ m HA) c i _ Hc Hn) as (Z1 & Z2 & Z3 & Z4).
  apply (fr_shad_le (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [| | exact H1 | exact H2];
    clear - Hc Z1 Z2 Z3 K5 K6 K8 K9 K11; unfold rb, kUserCap in *; lia.
Qed.

Lemma fr_shad_reg : forall c a n, 1 <= c <= 31 -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a ->
  a + n <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a n.
Proof.
  intros c a n Hc H1 H2. frgeo.
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (clear - Hc; apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c Hc); lia).
  apply (fr_shad_le (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (rb SB c + 2 ^ 32)); [| | exact H1 | exact H2];
    clear - Hc Hau K5 K6 K8 K9 K11; unfold rb in *; lia.
Qed.

Lemma fr_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= PRB \/ PRB + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k [] -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof. intros lo hi a n H0 H47 _ _ H1 H2. exact (fr_shad_le lo hi a n H0 H47 H1 H2). Qed.

Lemma fr_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof.
  intros k s a n Hk _ H1 H2. pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (Hn' & Y1 & Y3 & Y5 & Yp & _ & YG & _).
  pose proof (proj1 (Forall_forall _ _) YG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as YT.
  cbn [fst snd] in YT. unfold apart in YT.
  apply fr_off; [clear - H1 H2 YT; lia | clear - H1 H2 Y5; unfold SEGTOP_A in *; lia | clear - H2 Y3; lia].
Qed.

Lemma fr_stack : forall a n, usp <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof.
  intros a n H1 H2. frgeo. unfold W_frR. cbn [disjoint_from].
  split; [clear - H1 K2 Hsp; lia|]. split; [clear - H1 K10 Hsp; frdj|]. split; [clear - H1 K10 Hsp; frdj|]. split; [clear - H1; lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma fr_consts : forall x, in_rngs (consts_rngs L) x -> x <> T + 0xc60 -> outside W x.
Proof.
  intros x Hx NE.
  apply (kv_consts Σ W TZ IZ_R fr_img fr_Tz fr_grant); [apply dsjb_all; vm_compute; reflexivity | cbn; split; [lia | exact I] | exact Hx | exact NE].
Qed.

(* [comment removed for export] *)
Theorem frontR_ART : forall m' (iab : bool), munch W m m' -> wmono asegs m m' -> ia_state iab m' -> rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)] ->
  ART_A Σ m'.
Proof.
  intros m' iab MU WM IS TB. pose proof (ART_wf Σ m HA) as Hwf. frgeo.
  assert (HDS : forall k s, nth_error (sec Σ) k = Some s -> ~ In k []) by (intros k s _ []).
  pose proof (kv_reg Σ W [] (geo_of_ART Σ m HA) (ris_of_whole SB W [] fr_ris) (fun c0 a k Hc0 _ => fr_fa c0 a k Hc0)
                (fun c0 a k Hc0 _ => fr_shad_reg c0 a k Hc0)) as KR.
  pose proof (kv_pchunk Σ W [] (geo_of_ART Σ m HA) fr_slot fr_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] (geo_of_ART Σ m HA) fr_shad_app fr_secmap) as KS.
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  - apply (consts_rep_frame L m m' (ART_consts Σ m HA)); [|exact WM].
    pose proof (mp_cells Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UB).
    intros a Ha. destruct (Z.eq_dec (bv_unsigned a) (T + 3168)) as [E|NE].
    + assert (Ea : a = wa (T + 3168)) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned). subst a.
      assert (Hx : T + 3168 + 1 <= img_hull_lo \/ img_hull_hi <= T + 3168) by (clear - K4; unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
      rewrite (fn_byte m' _ _ TB Hx ltac:(clear - K2 K11; lia)), (fn_byte m _ _ UB Hx ltac:(clear - K2 K11; lia)). reflexivity.
    + apply MU. exact (fr_consts _ Ha NE).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (KR c Hc ltac:(intros []))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM
                         (kv_pclass Σ W TZ fr_Tz c Hc ltac:(cbn; split; [unfold pc_addr; lia | exact I]))).
  - destruct (ART_chunk Σ m HA) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (KP c i st Hc Hn ltac:(intros []))).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (KS k s Hk (HDS k s Hk))).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM (kv_sec Σ W IZ_R (geo_of_ART Σ m HA) fr_img fr_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM
             (kv_quar Σ W [] TZ IZ_R (geo_of_ART Σ m HA) fr_img fr_Tz fr_slot ltac:(cbn; split; [unfold qcacheT; lia | exact I])
                ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(intros i' _ [])
                ltac:(destruct Hwf as (_ & _ & _ & _ & (_ & _ & HBt & _) & _); exact HBt))).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM
             (kv_dep Σ W IZ_R fr_img ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros j b gn a n Hj Hjr; apply (fr_grant_ne2 j b gn a n Hj); clear - Hjr; lia))).
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (kv_fs Σ W [] TZ IZ_R (geo_of_ART Σ m HA) fr_img fr_Tz fr_grant fr_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(cbn; split; [lia | exact I]))).
  - exists iab. exact IS.
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (kv_shadow Σ W [] (geo_of_ART Σ m HA) fr_shad_app)).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

(* [comment removed for export] *)
Lemma frontR_client : forall x, aclient (live Σ) (frames Σ) usp x -> outside W x.
Proof.
  intros x Hx. apply (kv_client Σ W [] [] IZ_R usp (geo_of_ART Σ m HA) fr_img fr_grant fr_slot fr_shad_app fr_secmap fr_stack
                        (dsjb_all IZ_R CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live Σ)); [|exact Hx].
  intros p' n' Hin. pose proof (ART_wf Σ m HA) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
  destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
  + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity | intros []].
  + right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|].
    split; [reflexivity | intros []].
Qed.

End FrR.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_asan_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freeA RT_malart RT_maltail RT_malcore_p RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front RT_malsec_front2 RT_malsec_rev RT_malsec_B RT_malsec_T RT_malsec_wf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FKitX.
Variables (Σ : rtsA) (W : list ivl) (TZ IZ : list ivl).
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
Hypothesis HW_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ a n -> disjoint_from W a n.
Hypothesis HW_T : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Hypothesis HW_grantx : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> (i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis HW_fshad : forall a n, shad (l_FSB L) <= a -> a + n <= shad (l_FSB L + 0xb09000) -> disjoint_from W a n.

Lemma kvx_consts : Forall (fun r => disjoint_from IZ (fst r) (snd r - fst r)) CONSTS_LITS -> disjoint_from TZ T 0x30 ->
  forall x, in_rngs (consts_rngs L) x -> x <> T + 0xc60 -> outside W x.
Proof using HW_img HW_T HW_grantx.
  intros HZ HTZ x Hx Hne. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). cbv beta in Hrx.
  destruct (consts_rngs_kind L r Hr) as [Hl|[(H1 & H2)|[Er|(H1 & H2)]]].
  - pose proof (proj1 (Forall_forall _ _) HZ r Hl) as Dr.
    assert (Hrng : 0x10000 <= fst r /\ snd r <= SEGTOP_A) by (unfold CONSTS_LITS in Hl; repeat (destruct Hl as [<-|Hl]; [cbn; unfold SEGTOP_A; lia|]); destruct Hl).
    apply (disjoint_outside W (fst r) (snd r - fst r)); [apply HW_img; [lia | lia | exact Dr] | lia].
  - apply (disjoint_outside W x 1); [apply HW_T; [lia | lia | exact (dsj_sub TZ T 0x30 x 1 HTZ ltac:(lia) ltac:(lia))] | lia].
  - rewrite Er in Hrx. cbn [fst snd] in Hrx. lia.
  - apply (disjoint_outside W x 1); [|lia].
    apply (HW_grantx 3 (l_TCX L) 0x10000); [reflexivity | lia | lia | lia].
Qed.

Lemma fkx_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof using HW_grantx. intros a n H1 H2. exact (HW_grantx 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma kvx_fs_cls : forall k, (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof using HG HW_grantx HW_fshad.
  intros k Hk. pose proof HG as (_ & _ & _ & HF). destruct HF as (F0 & F2 & (F4 & Fc1 & Fc3) & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 Fc1) | exact (proj1 F2) | exact (proj1 Fc3) | exact (proj1 F4)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 1 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 4) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof (g_aceil Σ HG) as (_ & X & _). pose proof (fl_flags_range _ Hc) as (R1 & R2).
  unfold fs_cls_avoid. split; [apply fkx_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
  - rewrite Hlen. apply fkx_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
    split; [apply fkx_fsb; lia|].
    pose proof (fk_shad_le2 (frame_addr (l_FSB L) (Z.of_nat k) p) (fsz (Z.of_nat k)) ltac:(lia) ltac:(lia)) as E.
    pose proof (fk_shad_mono (l_FSB L) (frame_addr (l_FSB L) (Z.of_nat k) p) ltac:(lia)) as E1.
    pose proof (fk_shad_mono (frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k)) (l_FSB L + 0xb09000) ltac:(lia)) as E2.
    apply HW_fshad; lia.
Qed.

Lemma kvx_fs : Forall (fun r => disjoint_from IZ (fst r) (snd r)) fs_lits -> disjoint_from TZ (T + 48) 16 -> fs_avoid W Σ.
Proof using HG HW_img HW_T HW_grantx HW_fshad.
  intros HZ HT. pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply fkx_fsb; lia|].
  split; [exact (kvx_fs_cls 0%nat ltac:(lia))|]. split; [exact (kvx_fs_cls 2%nat ltac:(lia))|]. split; [exact (conj (kvx_fs_cls 4%nat ltac:(lia)) (conj (kvx_fs_cls 1%nat ltac:(lia)) (kvx_fs_cls 3%nat ltac:(lia))))|].
  split.
  { apply Forall_forall. intros r Hr. apply HW_img; [| | exact (proj1 (Forall_forall _ _) HZ r Hr)];
      unfold fs_lits in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
      destruct Hr. }
  split; [apply (HW_grantx 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply HW_T; [lia | lia | exact HT]|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (g_frame Σ HG f k Hin) as (X1 & X2 & X3). apply fkx_fsb; lia.
Qed.
End FKitX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MalSecArt.
Variables (Σ : rtsA) (mA m' : mem) (B n lo P : Z) (D' : depot).
Hypothesis Hn : 64512 < n <= 0x8000000.
Hypothesis HA : ART_A Σ mA.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 2144 <= USTACK_TOP.
Hypothesis WF : rt_wf (mal_sec Σ P n D').
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation PAB := (l_PAB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation msz := (smsz n).
#[local] Notation Σk := (mal_sec Σ P n D').
#[local] Notation W := (W_S Σ B n P).
#[local] Notation DS := [length (sec Σ)].
#[local] Notation TZ := [(l_T (lay Σ) + 2768, l_T (lay Σ) + 3168)].
#[local] Notation IZ := [(INST + 0x70, INST + 0x2d0); (0x743f08, 0xb53f30)].

Lemma ms_geok : geo_ok Σk.
Proof using WF. exact (geo_of_wf Σk WF). Qed.

(* [comment removed for export] *)
Lemma ms_geo :
  SEGTOP_A <= P /\ P + msz <= l_ACEIL L /\ SHB <= shad P /\ shad (P + msz) <= 2 ^ 44 + SHB /\ shad P <= shad (P + msz)
  /\ 2 ^ 44 + SHB + 8 <= l_ACEIL L /\ l_ACEIL L <= B + -16 /\ B + -16 <= 2 ^ 47
  /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ T + 4096 <= l_ACEIL L /\ SEGTOP_A <= PAB /\ PAB + 0x800000 <= l_ACEIL L
  /\ SEGTOP_A <= DNB /\ DNB + 2 ^ 20 <= l_ACEIL L /\ SEGTOP_A <= SSB /\ SSB + 2 ^ 23 <= l_ACEIL L
  /\ INST + 0x2d0 <= 0x743f08.
Proof using Hn HA HG LOW LOR SPT.
  pose proof (sl_geo Σ mA B n lo P Hn HA HG LOW LOR SPT) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14
                                                               & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  pose proof (sl_shad Σ mA B n lo P Hn HA HG LOW LOR SPT) as (H1 & H2 & H3 & H4 & _).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)).
  pose proof (sl_objs Σ mA B n lo P Hn HA HG LOW LOR SPT) as (_ & _ & _ & O4).
  unfold INST, g_instance, USTACK_TOP in *. repeat split; first [exact O4 | lia].
Qed.

(* [comment removed for export] *)
Lemma ms_grant : forall i b gn a k, nth_error (startup_grants L) i = Some (b, gn) -> (i = 0 \/ i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT.
  intros i b gn a k Hi Hir H1 H2. pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  pose proof (geo_grant Σ mA HA b gn (nth_error_In _ _ Hi)) as (B1 & B2 & B3 & B4 & B5).
  pose proof (rv_grant_apart Σ mA P n HA HG b gn (nth_error_In _ _ Hi)) as AP.
  assert (Hj : forall j g, (j = 1 \/ j = 2 \/ j = 6 \/ j = 7)%nat -> nth_error (startup_grants L) j = Some g -> apart b gn (fst g) (snd g)).
  { intros j g Hj Hg. assert (i <> j) by lia. destruct (Nat.lt_ge_cases i j) as [X|X].
    - exact (geo_apart Σ mA HA i j _ _ X Hi Hg).
    - pose proof (geo_apart Σ mA HA j i _ _ ltac:(lia) Hg Hi) as Y. unfold apart in *. cbn [fst snd] in *. lia. }
  pose proof (Hj 1%nat _ ltac:(lia) eq_refl) as A1. pose proof (Hj 2%nat _ ltac:(lia) eq_refl) as A2.
  pose proof (Hj 6%nat _ ltac:(lia) eq_refl) as A6. pose proof (Hj 7%nat _ ltac:(lia) eq_refl) as A7. cbn [fst snd] in A1, A2, A6, A7.
  unfold W_S. cbn [disjoint_from]. unfold apart, SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, INST, g_instance in *.
  split; [clear - AP H1 H2; destruct AP; lia|]. split; [clear - B4 H1 H2 K3 K4; destruct B4; lia|].
  split; [clear - A2 H1 H2; destruct A2; lia|]. split; [clear - B1 B5 H1 H2 K17; destruct B5; lia|].
  split; [clear - B1 B5 H1 H2; destruct B5; lia|]. split; [clear - A6 H1 H2; destruct A6; lia|]. split; [clear - A7 H1 H2; destruct A7; lia|].
  split; [clear - A1 H1 H2; destruct A1; lia|]. split; [clear - B3 H2 K7; lia | exact I].
Qed.

Lemma ms_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from IZ a k -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT.
  intros a k H1 H2 HZ. pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  cbn [disjoint_from] in HZ. destruct HZ as (Z1 & Z2 & _).
  unfold W_S. cbn [disjoint_from]. unfold SEGTOP_A, SHB in *.
  split; [lia|]. split; [lia|]. split; [destruct K9; lia|]. split; [exact Z1|]. split; [exact Z2|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia | exact I].
Qed.

Lemma ms_T : forall a k, T <= a -> a + k <= T + 4096 -> disjoint_from TZ a k -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT.
  intros a k H1 H2 HZ. pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  cbn [disjoint_from] in HZ. destruct HZ as (Z1 & _).
  pose proof (sl_apart Σ mA n P Hn HA HG) as (A1 & _ & _ & _ & _ & _ & _ & A8 & A9 & _ & _ & _ & A13 & _ & _ & _ & _ & _ & _ & A20 & _).
  unfold W_S. cbn [disjoint_from]. unfold apart, SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, INST, g_instance in *.
  split; [clear - A1 H1 H2; destruct A1; lia|]. split; [clear - A20 H1 H2 K3 K4; destruct A20; lia|]. split; [exact Z1|].
  split; [lia|]. split; [lia|]. split; [clear - A8 H1 H2; destruct A8; lia|]. split; [clear - A9 H1 H2; destruct A9; lia|].
  split; [clear - A13 H1 H2; destruct A13; lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma ms_prb : forall a k, PRB <= a -> a + k <= PRB + 0x2000011000 -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT. intros a k H1 H2. exact (ms_grant 0 PRB 0x2000011000 a k eq_refl ltac:(lia) H1 H2). Qed.

Lemma ms_ris : forall a k, RIS_of SB <= a -> a + k <= RIS_of SB + 4096 -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT.
  intros a k H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ mA HA)) as (P0 & P1 & P2 & P3 & P4). unfold RIS_of in *. apply ms_prb; lia.
Qed.

Lemma ms_fa : forall c a k, 1 <= c <= 31 -> ~ In c [] -> fa SB c <= a -> a + k <= fa SB c + kFaCap -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT.
  intros c a k Hc _ H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ mA HA)) as (P0 & P1 & P2 & P3 & P4).
  unfold fa, rb, RIS_of, kFaCap in *. apply ms_prb; lia.
Qed.

Lemma ms_slot : forall c i st a k, 1 <= c <= 31 -> nth_error (r_st (pr Σk c)) i = Some st -> ~ In (c, i) [] ->
  p_abeg SB c i <= a -> a + k <= p_abeg SB c i + ClassSize c -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT WF.
  intros c i st a k Hc Hi _ H1 H2. pose proof (fk_slot Σ (geo_of_ART Σ mA HA) c i st Hc Hi) as (S1 & S2 & S3 & S4).
  pose proof (fk_prb Σ (geo_of_ART Σ mA HA)) as (P0 & P1 & P2 & P3 & P4). unfold rb, kUserCap in *.
  assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. apply ms_prb; lia.
Qed.

(* [comment removed for export] *)
Lemma ms_shad_app0 : forall lo' hi a k, 0 <= lo' -> hi <= 2 ^ 47 ->
  (forall k0 s, nth_error (sec Σk) k0 = Some s -> In k0 DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo') ->
  shad lo' <= a -> a + k <= shad hi -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT.
  intros lo' hi a k H0 H47 HDS H1 H2. pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  assert (Hnew : nth_error (sec Σk) (length (sec Σ)) = Some (sec_new P n)).
  { cbn [mal_sec sec]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  pose proof (HDS _ _ Hnew (or_introl eq_refl)) as Ap. cbn [sec_new s_mb s_n] in Ap.
  assert (Ysh : shad hi <= shad P \/ shad (P + msz) <= shad lo') by (destruct Ap as [Y|Y]; [left | right]; apply fk_shad_mono; exact Y).
  pose proof (shad_lo lo' H0) as Q1. pose proof (shad_hi hi H47) as Q2.
  pose proof (sl_apart Σ mA n P Hn HA HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A17 & A18 & A19 & A20 & _ & A22).
  unfold W_S. cbn [disjoint_from]. unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, INST, g_instance in *.
  split; [clear - A19 H1 H2 Q1 Q2; destruct A19; lia|]. split; [clear - Ysh H1 H2; destruct Ysh; lia|].
  split; [clear - A20 H1 H2 Q1 Q2; destruct A20; lia|]. split; [lia|]. split; [lia|].
  split; [clear - A17 H1 H2 Q1 Q2; destruct A17; lia|]. split; [clear - A18 H1 H2 Q1 Q2; destruct A18; lia|].
  split; [clear - A22 H1 H2 Q1 Q2; destruct A22; lia|]. split; [lia | exact I].
Qed.

Lemma ms_shad_app : forall lo' hi a k, 0 <= lo' -> hi <= 2 ^ 47 -> (hi <= l_PRB (lay Σk) \/ l_PRB (lay Σk) + 0x2000011000 <= lo') ->
  (forall k0 s, nth_error (sec Σk) k0 = Some s -> In k0 DS -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo') ->
  shad lo' <= a -> a + k <= shad hi -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT. intros lo' hi a k H0 H47 _ HDS. exact (ms_shad_app0 lo' hi a k H0 H47 HDS). Qed.

Lemma ms_shad_slot : forall c i st a k, 1 <= c <= 31 -> nth_error (r_st (pr Σk c)) i = Some st -> ~ In (c, i) [] ->
  shad (p_abeg SB c i) <= a -> a + k <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT WF.
  intros c i st a k Hc Hi _ H1 H2. pose proof (fk_slot Σ (geo_of_ART Σ mA HA) c i st Hc Hi) as (S1 & S2 & S3 & S4).
  pose proof (fk_prb Σ (geo_of_ART Σ mA HA)) as (P0 & P1 & P2 & P3 & P4). unfold rb, kUserCap in *.
  pose proof (fk_aceil Σ (geo_of_ART Σ mA HA)) as (X1 & X2).
  assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia.
  apply (ms_shad_app0 (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [lia | lia | | exact H1 | exact H2].
  intros k0 s Hk0 [<-|[]]. cbn [mal_sec sec] in Hk0. rewrite nth_error_app2 in Hk0 by lia. rewrite Nat.sub_diag in Hk0. cbn in Hk0.
  injection Hk0 as <-. cbn [sec_new s_mb s_n].
  pose proof (rv_grant_apart Σ mA P n HA HG PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap. unfold apart in Ap. lia.
Qed.

Lemma ms_shad_reg : forall c a k, 1 <= c <= 31 -> ~ In c [] ->
  shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σk c)))) <= a -> a + k <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT WF.
  intros c a k Hc _ H1 H2. pose proof (fk_prb Σ (geo_of_ART Σ mA HA)) as (P0 & P1 & P2 & P3 & P4).
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; pose proof (ClassSize_range c Hc); lia).
  unfold rb in *. pose proof (fk_aceil Σ (geo_of_ART Σ mA HA)) as (X1 & X2).
  assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia.
  apply (ms_shad_app0 (SB + c * 2 ^ 32 + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (SB + c * 2 ^ 32 + 2 ^ 32)); [lia | lia | | exact H1 | exact H2].
  intros k0 s Hk0 [<-|[]]. cbn [mal_sec sec] in Hk0. rewrite nth_error_app2 in Hk0 by lia. rewrite Nat.sub_diag in Hk0. cbn in Hk0.
  injection Hk0 as <-. cbn [sec_new s_mb s_n].
  pose proof (rv_grant_apart Σ mA P n HA HG PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap. unfold apart in Ap.
  assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma ms_secmap : forall k0 s a k, nth_error (sec Σk) k0 = Some s -> ~ In k0 DS -> s_mb s <= a -> a + k <= s_mb s + smsz (s_n s) ->
  disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT WF.
  intros k0 s a k Hk0 HD H1 H2. pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  assert (Hold : nth_error (sec Σ) k0 = Some s).
  { cbn [mal_sec sec] in Hk0. destruct (Nat.lt_ge_cases k0 (length (sec Σ))) as [X|X]; [rewrite nth_error_app1 in Hk0 by exact X; exact Hk0|].
    exfalso. rewrite nth_error_app2 in Hk0 by exact X. destruct (k0 - length (sec Σ))%nat as [|j] eqn:E; [apply HD; left; lia | cbn in Hk0; destruct j; discriminate]. }
  pose proof (fk_map Σ (geo_of_ART Σ mA HA) k0 s Hold) as (Hn' & Y1 & Y3 & Y5 & Yp & Yf & YG & Yr & Yr2 & _).
  pose proof (proj1 (Forall_forall _ _) YG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as YT.
  pose proof (proj1 (Forall_forall _ _) YG (DNB, 0x100000) ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as YD.
  pose proof (proj1 (Forall_forall _ _) YG (SSB, 0x800000) ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as YS.
  pose proof (proj1 (Forall_forall _ _) YG (PAB, 0x800000) ltac:(unfold startup_grants; right; left; reflexivity)) as YP.
  pose proof (geo_wf Σ mA HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hold)) as (_ & (_ & _ & _ & Y4 & _) & _).
  pose proof HG as (_ & Hap).
  pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
    apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact (nth_error_In _ _ Hold))) as YN.
  unfold secmap in YN. cbn [fst snd] in YN. rewrite !unsigned_lit in YN by (clear - Y1 Y3 K7 K8 Yr Yr2 Hn'; lia).
  cbn [fst snd] in *.
  unfold W_S. cbn [disjoint_from]. unfold apart, SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, INST, g_instance in *.
  split; [clear - YN H1 H2; destruct YN; lia|]. split; [clear - Y4 H1 H2 K3 K4; destruct Y4; lia|].
  split; [clear - YT H1 H2; destruct YT; lia|]. split; [clear - Y5 H1 H2 Hn'; destruct Y5; lia|].
  split; [clear - Y5 H1 H2 Hn'; destruct Y5; lia|]. split; [clear - YD H1 H2; destruct YD; lia|].
  split; [clear - YS H1 H2; destruct YS; lia|]. split; [clear - YP H1 H2; destruct YP; lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma ms_fshad : forall a k, shad (l_FSB L) <= a -> a + k <= shad (l_FSB L + 0xb09000) -> disjoint_from W a k.
Proof using D' Hn HA HG LOW LOR SPT.
  intros a k H1 H2. pose proof (geo_grant Σ mA HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; do 5 right; left; reflexivity))
    as (B1 & _ & B3 & _).
  pose proof (fk_aceil Σ (geo_of_ART Σ mA HA)) as (X1 & X2).
  apply (ms_shad_app (l_FSB L) (l_FSB L + 0xb09000)); [lia | lia | | | exact H1 | exact H2].
  - pose proof (fk_fsb_off Σ (geo_of_ART Σ mA HA)) as X. cbn [lay mal_sec]. exact X.
  - intros k0 s Hk0 [<-|[]]. cbn [mal_sec sec] in Hk0. rewrite nth_error_app2 in Hk0 by lia. rewrite Nat.sub_diag in Hk0. cbn in Hk0.
    injection Hk0 as <-. cbn [sec_new s_mb s_n].
    pose proof (rv_grant_apart Σ mA P n HA HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; do 5 right; left; reflexivity)) as Ap.
    unfold apart in Ap. lia.
Qed.

Lemma ms_frames : forall f k a n', In (f, k) (frames Σ) -> shad f <= a -> a + n' <= shad (f + fs_size k) -> disjoint_from W a n'.
Proof using D' Hn HA HG LOW LOR SPT.
  intros f k a n' Hin H1 H2. destruct (g_frame Σ (geo_of_ART Σ mA HA) f k Hin) as (X1 & X2 & X3).
  pose proof (fk_shad_mono (l_FSB L) f ltac:(lia)). pose proof (fk_shad_mono (f + fs_size k) (l_FSB L + 0xb09000) ltac:(lia)).
  apply ms_fshad; lia.
Qed.

Lemma ms_grantx : forall i b gn a k, nth_error (startup_grants L) i = Some (b, gn) -> (i = 3 \/ i = 4 \/ i = 5)%nat ->
  b <= a -> a + k <= b + gn -> disjoint_from W a k.
Proof using Hn HA HG LOW LOR SPT. intros i b gn a k Hi Hir. apply (ms_grant i b gn a k Hi). lia. Qed.

(* [comment removed for export] *)
Lemma ms_client : forall x, aclient (live Σ) (frames Σ) (B + -16) x -> outside W x.
Proof using D' Hn HA HG LOW LOR SPT WF.
  intros x Hx. pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  destruct Hx as [H|[H|[H|[H|H]]]].
  - apply (disjoint_outside W x 1); [|lia]. unfold W_S. cbn [disjoint_from]. unfold INST, g_instance, SEGTOP_A, SHB in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia | exact I].
  - destruct H as ((lo' & hi' & Hin & Hlh) & Hrt).
    assert (Hx : 0x10000 <= x /\ x + 1 <= SEGTOP_A /\ (x + 1 <= INST + 0x70 \/ INST + 0x2d0 <= x) /\ (x + 1 <= 0x743f08 \/ 0xb53f30 <= x)).
    { unfold CLIENT_STATIC in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
      - assert (~ (0x66e9d8 <= x < 0x66f800)) by lia.
        unfold INST, g_instance, SEGTOP_A. lia.
      - unfold SEGTOP_A, INST, g_instance; lia.
      - unfold SEGTOP_A, INST, g_instance; lia. }
    destruct Hx as (X1 & X2 & X3 & X4).
    apply (disjoint_outside W x 1); [|lia]. apply ms_img; [exact X1 | exact X2|]. cbn [disjoint_from]. split; [exact X3|]. split; [exact X4 | exact I].
  - destruct H as (p & k & Hin & Hpx). apply (disjoint_outside W x 1); [|lia].
    destruct (geo_live Σ mA HA p k Hin) as [(c & i & Hc & Hi & Ep & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hsn & Ep & X1 & X5)].
    + apply (ms_slot c i (CkAlloc k)); [exact Hc | exact Hi | intros [] | lia | lia].
    + destruct (In_nth_error _ _ Hs) as (k0 & Hk0).
      apply (ms_secmap k0 s); [cbn [mal_sec sec]; rewrite nth_error_app1 by (apply nth_error_Some; rewrite Hk0; discriminate); exact Hk0
                              | intros [E|[]]; pose proof (proj1 (nth_error_Some (sec Σ) k0) ltac:(rewrite Hk0; discriminate)); lia
                              | unfold s_ubeg in Ep; lia | unfold s_ubeg in Ep; rewrite Hsn; lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W x 1); [|lia].
    destruct (g_frame Σ (geo_of_ART Σ mA HA) f k Hin) as (Y1 & Y2 & Y3).
    apply (ms_grant 5 (l_FSB L) 0xb09000); [reflexivity | lia | lia | lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W x 1); [|lia]. apply (ms_frames f k x 1 Hin); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ms_schunk : forall (m : mem),
  shdr m P msz (needed2 n) (Z.of_nat (length (sec Σ))) -> stk ctasegs m P (P + msz) -> stk ctasegs m (shad P) (shad (P + msz)) ->
  ahdr m (P + 4096 + 2032) n -> lch m (P + 4096) (P + 4096 + 2032) ->
  bytes_at ctasegs m (shad P) (farun 512) -> bytes_at ctasegs m (shad (P + 4096)) (farun (2048 / 8)) ->
  bytes_at ctasegs m (shad (P + 4096 + 2048)) (ushadow n) ->
  bytes_at ctasegs m (shad (P + 4096 + 2048 + ru8 n)) (farun ((smsz n - 4096 - 2048 - ru8 n) / 8)) ->
  schunk (length (sec Σ)) (sec_new P n) m.
Proof using Hn HA HG.
  intros m HD SK SS HH HL SH1 SH2 US TL. unfold schunk. cbn [sec_new s_mb s_n s_quar].
  pose proof (msec_size n Hn) as (K1 & K2 & K3 & K4). pose proof (rz_size_big n ltac:(lia)) as RZ.
  pose proof (rv_shad Σ mA P n HA HG Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (rv_map Σ mA P n HA HG Hn) as (M1 & M2 & _).
  assert (E1 : needed n + rz_size n = needed2 n) by (unfold needed2; rewrite K4; reflexivity).
  split; [rewrite E1; exact HD|]. split; [exact (stk_wr_at' m _ _ SK)|]. split; [exact HL|]. split; [exact HH|].
  split; [exact SS|].
  split.
  { change ((4096 + 2048) / 8) with 768. replace 768 with (512 + 256) by reflexivity. unfold farun. rewrite Z2Nat.inj_add by lia.
    rewrite repeat_app. apply bytes_at_app. split; [exact SH1|]. rewrite repeat_length. change (Z.of_nat (Z.to_nat 512)) with 512.
    assert (P8 : P mod 8 = 0) by (apply (mod8_of P 4096); [lia | exact M2 | exists 512; reflexivity]).
    rewrite (shad_add8 P 4096 P8 eq_refl) in SH2. change (4096 / 8) with 512 in SH2. exact SH2. }
  split; [exact US | exact TL].
Qed.

Theorem mal_sec_ART : forall (m : mem),
  munch W mA m -> wmono ctasegs mA m -> vis_rep L (shw P n :: rtA_allow Σ) mA ->
  shdr m P msz (needed2 n) (Z.of_nat (length (sec Σ))) -> stk ctasegs m P (P + msz) -> stk ctasegs m (shad P) (shad (P + msz)) ->
  ahdr m (P + 4096 + 2032) n -> lch m (P + 4096) (P + 4096 + 2032) ->
  bytes_at ctasegs m (shad P) (farun 512) -> bytes_at ctasegs m (shad (P + 4096)) (farun (2048 / 8)) ->
  bytes_at ctasegs m (shad (P + 4096 + 2048)) (ushadow n) ->
  bytes_at ctasegs m (shad (P + 4096 + 2048 + ru8 n)) (farun ((smsz n - 4096 - 2048 - ru8 n) / 8)) ->
  sec_core m PAB 0x4000 (Z.of_nat (length (sec Σ)) + 1) -> sec_pad m -> sec_junk m ->
  (exists ws, u64arr ctasegs m PAB ws /\ Z.of_nat (length ws) = 0x4000
              /\ firstn (length (sec Σ) + 1) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ ++ [sec_new P n])) ->
  depot_rep D' (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB m -> hash_of (d_hs D') 1 = hash_of (d_hs (dep Σ)) 1 ->
  ART_A Σk m.
Proof using Hn HA HG LOW LOR SPT WF.
  intros m MU WM VIS HD SK SS HH HL SH1 SH2 US TL SC PAD SJ WS DR Dh.
  pose proof ms_geok as HGk.
  pose proof ms_geo as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  assert (HDS0 : forall k s, nth_error (sec Σ) k = Some s -> ~ In k DS).
  { intros k s Hk [E|[]]. pose proof (proj1 (nth_error_Some (sec Σ) k) ltac:(rewrite Hk; discriminate)). lia. }
  pose proof (kv_reg Σk W [] HGk (ris_of_whole (l_SB (lay Σk)) W [] ms_ris) ms_fa ms_shad_reg) as KR.
  pose proof (kv_pchunk Σk W [] HGk ms_slot ms_shad_slot) as KP.
  pose proof (kv_schunk Σk W DS HGk ms_shad_app ms_secmap) as KS.
  apply ART_intro; [exact WF | | | | | | | | | | |]; cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 fs1 fs3 ia_init credit live frames mal_sec].
  - (* [comment removed for export] *)
    apply (consts_rep_frame L mA m (ART_consts Σ mA HA)); [|exact WM].
    intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
    + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply ms_T; [lia | lia|]. cbn. split; [lia | exact I].
    + apply (kvx_consts Σ W TZ IZ ms_img ms_T ms_grantx); [apply dsjb_all; vm_compute; reflexivity | cbn; split; [lia | exact I]
                                                                                | exact Ha | exact NE].
  - intros c Hc. exact (reg_rep_transport W _ c _ mA m (ART_prim Σ mA HA c Hc) MU WM (KR c Hc ltac:(intros []))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ mA m (ART_cache Σ mA HA c Hc) MU WM
                          (kv_pclass Σk W TZ ms_T c Hc ltac:(cbn; unfold pc_addr; split; [lia | exact I]))).
  - destruct (ART_chunk Σ mA HA) as [Pc Sc]. split.
    + intros c i st Hc Hi. exact (pchunk_transport W _ c i st mA m (Pc c i st Hc Hi) MU WM (KP c i st Hc Hi (fun X => X))).
    + intros k s Hk. cbn [sec] in Hk. destruct (Nat.lt_ge_cases k (length (sec Σ))) as [X|X].
      * rewrite nth_error_app1 in Hk by exact X.
        exact (schunk_transport W k s mA m (Sc k s Hk) MU WM (KS k s ltac:(cbn [mal_sec sec]; rewrite nth_error_app1 by exact X; exact Hk)
                                                                  (HDS0 k s Hk))).
      * rewrite nth_error_app2 in Hk by exact X. destruct (k - length (sec Σ))%nat as [|j] eqn:Ej; [|cbn in Hk; destruct j; discriminate].
        cbn in Hk. injection Hk as <-. replace k with (length (sec Σ)) by lia.
        exact (ms_schunk m HD SK SS HH HL SH1 SH2 US TL).
  - (* [comment removed for export] *)
    pose proof (ART_sec Σ mA HA) as (_ & _ & _ & PG & SRG & _ & NM).
    assert (IMG : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> (a + k <= INST + 0x70 \/ INST + 0x2d0 <= a) ->
                 (a + k <= 0x743f08 \/ 0xb53f30 <= a) -> disjoint_from W a k).
    { intros a k H1 H2 H3 H4. apply ms_img; [exact H1 | exact H2|]. cbn [disjoint_from]. split; [exact H3|]. split; [exact H4 | exact I]. }
    unfold sec_rep, sec_page, sec_range, name_cells in *. destruct NM as (N1 & N2). cbn [lay sec sec_nres mal_sec].
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
    split; [exact SC|]. split; [exact PAD|].
    split; [destruct WS as (ws & W1 & W2 & W3); exists ws; split; [exact W1|]; split; [exact W2|]; rewrite Nat.add_1_r in W3 |- *; exact W3|].
    split; [apply (rw_cells_transport ctasegs _ mA m _ _ PG MU WM); cs_size; apply IMG; unfold i_sec_page, INST, g_instance, SEGTOP_A; lia|].
    split; [apply (rw_cells_transport ctasegs _ mA m _ _ SRG MU WM); cs_size; apply IMG; unfold i_sec_range, INST, g_instance, SEGTOP_A; lia|].
    split; [exact SJ|].
    split; [apply (rw_cells_transport ctasegs _ mA m _ _ N1 MU WM); cs_size; apply IMG; unfold SEGTOP_A, INST, g_instance; lia|].
    apply (rw_cells_transport ctasegs _ mA m _ _ N2 MU WM). cs_size. apply IMG; unfold SEGTOP_A, INST, g_instance; lia.
  - exact (quar_rep_transport W Σ mA m (ART_quar Σ mA HA) MU WM
             (kv_quar Σk W [] TZ IZ HGk ms_img ms_T ms_slot ltac:(cbn; unfold qcacheT, pc_addr; split; [lia | exact I])
                ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(intros i' Hi' []) 
                ltac:(pose proof (ART_wf Σ mA HA) as (_ & _ & _ & _ & HQw & _); exact (proj1 (proj2 (proj2 HQw)))))).
  - unfold dep_rep. rewrite Dh. exact DR.
  - exact (fs_rep_transport W Σ mA m (ART_fs Σ mA HA) MU WM
             (kvx_fs Σ W TZ IZ (geo_of_ART Σ mA HA) ms_img ms_T ms_grantx ms_fshad ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(cbn; split; [lia | exact I]))).
  - exact (ia_rep_transport W Σ mA m (ART_ia Σ mA HA) MU WM (kv_ia W IZ ms_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ mA m (ART_shadow Σ mA HA) MU WM (kv_shadow Σk W DS HGk ms_shad_app)).
  - exact (vis_rep_wmono _ mA m VIS WM).
Qed.

End MalSecArt.

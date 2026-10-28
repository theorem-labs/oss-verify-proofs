(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_asan_malloc R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_maltail RT_freelift RT_malcore_stmt R_unwind_chain RT_sites RT_malloc R_pmalloc1 R_asan_pmalign RT_pmtail RT_pmcore_stmt R_fs_defs R_sec_defs R_tlsgetaddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition W_pm (T usp : Z) : list ivl :=
  [(T + 3168, T + 3169); (7346888, 7346892); (6763072, 7291504); (usp - 2336, usp)].

Section FnSepPm.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp.   (* [comment removed for export] *)
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_pm (l_T (lay Σ)) usp).

Lemma pmfn_Tgrant : grant_ok L T 4096.
Proof. exact (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)). Qed.

Lemma pmfn_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (rta_sp0_win Σ m HA) as X. pose proof (rta_sp0_range Σ m HA) as Y. unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *. lia. Qed.

(* [comment removed for export] *)
Lemma pmfn_off : forall a n, (a + n <= 0x10000 \/ SEGTOP_A <= a) -> a + n <= l_ACEIL L -> (a + n <= T \/ T + 4096 <= a) ->
  disjoint_from W a n.
Proof.
  intros a n H1 H2 H3. clear HA. unfold W_pm, SEGTOP_A in *. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma pmfn_T : forall a n, T <= a -> a + n <= T + 3168 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. pose proof pmfn_Tgrant as (G1 & G2 & G3 & G4 & G5). clear HA. unfold W_pm, SEGTOP_A in *. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma pmfn_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> (a + n <= 6763072 \/ 7291504 <= a) ->
  (a + n <= 7346888 \/ 7346892 <= a) -> disjoint_from W a n.
Proof.
  intros a n H1 H2 H3 H4. pose proof pmfn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof pmfn_aceil as (X & _). clear HA.
  unfold W_pm, SEGTOP_A, SHB in *. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma pmfn_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> i <> 2%nat -> b <= a -> a + n <= b + gn ->
  disjoint_from W a n.
Proof.
  intros i b gn a n Hi Hne H1 H2. pose proof (geo_grant Σ m HA b gn (nth_error_In _ _ Hi)) as (G1 & G2 & G3 & G4 & G5).
  assert (Hap : apart b gn T 4096).
  { destruct (Nat.lt_ge_cases i 2) as [Hl|Hl].
    - exact (geo_apart Σ m HA i 2 (b, gn) (T, 4096) Hl Hi eq_refl).
    - pose proof (geo_apart Σ m HA 2 i (T, 4096) (b, gn) ltac:(lia) eq_refl Hi) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold apart in Hap. apply pmfn_off; unfold SEGTOP_A in *; lia.
Qed.

Lemma pmfn_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (pmfn_grant 0 (l_PRB L) 0x2000011000 a n eq_refl ltac:(lia) H1 H2). Qed.

(* [comment removed for export] *)
Lemma pmfn_shad : forall a n, SHB <= a -> a + n <= 2 ^ 44 + SHB -> disjoint_from W a n.
Proof.
  intros a n H1 H2. pose proof pmfn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof pmfn_aceil as (X & _).
  apply pmfn_off; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia.
Qed.

Lemma pmfn_shad_len : forall x y, 0 <= x -> 0 <= y -> x + y <= 2 ^ 47 -> disjoint_from W (shad x) (Z.max 0 (y / 8)).
Proof. intros x y Hx Hy H. destruct (shad_len x y Hx Hy H) as [X Y]. apply pmfn_shad; lia. Qed.

(* [comment removed for export] *)
Lemma pmfn_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof.
  intros k s a n Hk H1 H2. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & G3 & G4 & G5) & _ & _ & HG).
  pose proof (proj1 (Forall_forall _ _) HG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as Ha.
  cbn [fst snd] in Ha. unfold apart in Ha. apply pmfn_off; unfold SEGTOP_A in *; lia.
Qed.

(* [comment removed for export] *)
Lemma pmfn_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  0 < l_PRB L /\ l_PRB L <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + kUserCap /\ rb SB c + kUserCap <= l_PRB L + 0x2000011000
  /\ l_PRB L + 0x2000011000 <= 2 ^ 47 /\ 32 <= ClassSize c.
Proof.
  intros c i st Hc Hn. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  pose proof pmfn_aceil as (_ & X).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
  unfold p_abeg, rb, kUserCap in *. repeat split; lia.
Qed.

Lemma pmfn_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W T c.
Proof.
  intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  pose proof pmfn_aceil as (_ & X).
  split; [|unfold pclass_avoid, pc_addr; apply pmfn_T; lia].
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
  unfold reg_avoid. split; [|split].
  - apply pmfn_prb; unfold rinfo, RIS_of; lia.
  - apply pmfn_prb; unfold fa, rb, kFaCap, kUserCap in *; lia.
  - apply pmfn_shad_len; unfold rb, kUserCap in *; lia.
Qed.

Lemma pmfn_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof.
  intros c i st Hc Hn. pose proof (pmfn_slot c i st Hc Hn) as (S0 & S1 & S2 & S3 & S4 & S5).
  assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
  { intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
    pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
  unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
  assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
  destruct st as [|n|n|].
  - apply pmfn_shad_len; lia.
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
    split; [apply pmfn_prb; lia|]. split; [intros _; apply pmfn_prb; lia|].
    split.
    + rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
      apply (dsj_sub W (shad AB) (Z.max 0 ((rz_size n + ru8 n) / 8))); [apply pmfn_shad_len; lia | lia|].
      pose proof (div8_add (rz_size n) (ru8 n) ltac:(lia) Hu). lia.
    + apply pmfn_shad_len; lia.
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
    assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
    split; [apply pmfn_prb; lia|]. split; [intros _; apply pmfn_prb; lia|].
    rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
    apply (dsj_sub W (shad AB) (Z.max 0 (S / 8))); [apply pmfn_shad_len; lia | lia|].
    pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as D.
    replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in D by ring. lia.
  - apply pmfn_shad_len; lia.
Qed.

Lemma pmfn_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof.
  intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & _).
  pose proof pmfn_aceil as (_ & X).
  assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
  { unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
  assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
  unfold schunk_avoid.
  split; [apply (pmfn_secmap k s); [exact Hk | lia | lia]|].
  split; [apply (pmfn_secmap k s); [exact Hk | lia | lia]|].
  split; [apply (pmfn_secmap k s); [exact Hk | lia | destruct (s_quar s); lia]|].
  split; [change (Z.max 0 ((4096 + 2048) / 8)) with (Z.max 0 (6144 / 8)); apply pmfn_shad_len; lia|].
  split.
  - apply (dsj_sub W (shad (s_mb s + 4096 + 2048)) (Z.max 0 (ru8 (s_n s) / 8))); [apply pmfn_shad_len; lia | lia|].
    destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply pmfn_shad_len; lia.
Qed.

Lemma pmfn_sec : sec_avoid W Σ.
Proof.
  split.
  - unfold sec_lits. repeat (apply Forall_cons; [cbn [fst snd]; apply pmfn_img; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
      i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]). apply Forall_nil.
  - pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
    apply (pmfn_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma pmfn_quar : quar_avoid W Σ.
Proof.
  split; [unfold qcacheT; apply pmfn_T; lia|].
  split; [repeat (apply Forall_cons; [cbn [fst snd]; apply pmfn_img; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia|]); apply Forall_nil|].
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
  pose proof (pmfn_slot 24 i CkBatch ltac:(lia) Hi) as (_ & S1 & S2 & S3 & _). change (ClassSize 24) with 8192 in *. apply pmfn_prb; lia.
Qed.

Lemma pmfn_dep : dep_avoid W L.
Proof.
  split; [repeat (apply Forall_cons; [cbn [fst snd]; apply pmfn_img; unfold SEGTOP_A; lia|]); apply Forall_nil|].
  split; [apply (pmfn_grant 6 (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
  apply (pmfn_grant 7 (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma fl_flags_range : forall c, (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4) -> 0x1000 <= 0x1000 + flags_off c /\ 0x1000 + flags_off c + NF c <= 0x9000.
Proof. intros c Hc. unfold flags_off, NF. destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia. Qed.

Lemma pmfn_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (pmfn_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma pmfn_fs_cls : forall k, (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (F0 & F2 & (F4 & Fc1 & Fc3) & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; [exact (proj1 F0) | exact (proj1 Fc1) | exact (proj1 F2) | exact (proj1 Fc3) | exact (proj1 F4)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 1 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 4) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof pmfn_aceil as (_ & X). pose proof (fl_flags_range _ Hc) as (R1 & R2).
  unfold fs_cls_avoid. split; [apply pmfn_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia|]. split.
  - rewrite Hlen. apply pmfn_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
    split; [apply pmfn_fsb; lia|]. apply (dsj_sub W (shad (frame_addr (l_FSB L) (Z.of_nat k) p)) (Z.max 0 (fsz (Z.of_nat k) / 8)));
      [apply pmfn_shad_len; lia | lia | pose proof (Z.div_pos (fsz (Z.of_nat k)) 8 ltac:(lia) ltac:(lia)); lia].
Qed.

Lemma pmfn_fs : fs_avoid W Σ.
Proof.
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply pmfn_fsb; lia|].
  split; [exact (pmfn_fs_cls 0%nat ltac:(lia))|]. split; [exact (pmfn_fs_cls 2%nat ltac:(lia))|]. split; [exact (conj (pmfn_fs_cls 4%nat ltac:(lia)) (conj (pmfn_fs_cls 1%nat ltac:(lia)) (pmfn_fs_cls 3%nat ltac:(lia))))|].
  split; [unfold fs_lits; repeat (apply Forall_cons; [cbn [fst snd]; apply pmfn_img; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
      apply Forall_nil|].
  split; [apply (pmfn_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply pmfn_T; lia|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & X3). apply pmfn_fsb; lia.
Qed.

Lemma pmfn_shadow : shadow_avoid W L.
Proof.
  pose proof pmfn_aceil as (X1 & X2). split.
  - apply pmfn_shad_len; unfold SHB in *; lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0xbcacd0) by (unfold SH_RNGS, IMG_HULL, GD_IMG_END, CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply pmfn_shad; unfold shad; [pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)); lia|].
    assert ((snd r - 1) / 8 <= 0xbcacd0 / 8) by (apply Z.div_le_mono; lia). change (0xbcacd0 / 8) with 0x17959a in *. unfold SHB. lia.
Qed.

(* [comment removed for export] *)
Lemma pmfn_consts : forall x, in_rngs (consts_rngs L) x -> x <> T + 3168 -> outside W x.
Proof.
  intros x Hx NE. pose proof pmfn_Tgrant as (G1 & G2 & G3 & G4 & G5).
  pose proof (geo_grant Σ m HA (l_TCX L) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
  pose proof pmfn_aceil as (A1 & A2).
  assert (D : Forall (fun r => disjoint_from [(7346888, 7346892); (6763072, 7291504); (usp - 2336, usp)] (fst r) (snd r - fst r)) (consts_rngs L)).
  { clear Hx NE HA. unfold consts_rngs. unfold_consts. unfold SEGTOP_A, SHB in *.
    repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; refine (conj _ (conj _ (conj _ I))); lia|]). apply Forall_nil. }
  unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). pose proof (proj1 (Forall_forall _ _) D r Hr) as Dr.
  pose proof (disjoint_outside _ _ _ x Dr ltac:(lia)) as O. clear D Dr. cbn [W_pm outside] in *. split; [lia | exact O].
Qed.

(* [comment removed for export] *)
Lemma pmfn_client : forall x, aclient (live Σ) (frames Σ) usp x -> outside W x.
Proof.
  intros x Hx. pose proof pmfn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof pmfn_aceil as (X1 & X2).
  destruct Hx as [H|[H|[H|[H|H]]]].
  - clear HA. unfold W_pm, SEGTOP_A, SHB in *. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - destruct H as ((lo & hi & Hin & Hlh) & _). unfold CLIENT_STATIC in Hin.
    apply (disjoint_outside W lo (hi - lo)); [|lia].
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; apply pmfn_img; unfold SEGTOP_A; lia.
  - destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
    destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hn & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & _ & Hn' & -> & Y1 & Y5)].
    + pose proof (pmfn_slot c i _ Hc Hn) as (_ & S1 & S2 & S3 & _). apply pmfn_prb; lia.
    + destruct (In_nth_error _ _ Hs) as (k & Hk). apply (pmfn_secmap k s); [exact Hk | unfold s_ubeg; lia | rewrite <- Hn' in Y1; unfold s_ubeg; lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
    destruct (sep_frame Σ m HA f k Hin) as (Y1 & Y2 & Y3). apply pmfn_fsb; lia.
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
    destruct (sep_fshad Σ m HA f k Hin) as (Y1 & Y2). apply pmfn_shad; unfold K_HIGH_SHADOW_hi, SHB in *; lia.
Qed.

End FnSepPm.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Front.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp.   (* [comment removed for export] *)
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation W := (W_pm (l_T (lay Σ)) usp).

(* [comment removed for export] *)
Theorem front_ART_pm : forall m', munch [(T + 3168, T + 3169); (usp - 2336, usp)] m m' -> wmono ctasegs m m' ->
  rw_cells ctasegs m' (T + 3168) [C1 (Z_to_bv 8 0)] -> ART_A Σ m'.
Proof using HA Hsp.
  intros m' MU0 WM TB. pose proof (ART_wf Σ m HA) as Hwf.
  assert (MU : munch W m m').
  { eapply (munch_weaken _ _ m m'); [|exact MU0]. intros x Hx. unfold W_pm in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (X1 & _ & _ & X4 & _). split; [exact X1|]. split; [exact X4 | exact I]. }
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  - apply (consts_rep_frame (lay Σ) m m' (ART_consts Σ m HA)); [|exact WM].
    pose proof (mp_cells Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UB).
    pose proof (pmfn_Tgrant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (pmfn_aceil Σ m HA) as (_ & X).
    intros a Ha. destruct (Z.eq_dec (bv_unsigned a) (T + 3168)) as [E|NE].
    + assert (Ea : a = wa (T + 3168)) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned). subst a.
      assert (Hx : T + 3168 + 1 <= img_hull_lo \/ img_hull_hi <= T + 3168) by (unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
      rewrite (fn_byte m' _ _ TB Hx ltac:(lia)), (fn_byte m _ _ UB Hx ltac:(lia)). reflexivity.
    + apply MU. exact (pmfn_consts Σ m usp HA Hsp _ Ha NE).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (proj1 (pmfn_reg Σ m usp HA Hsp c Hc))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM (proj2 (pmfn_reg Σ m usp HA Hsp c Hc))).
  - destruct (ART_chunk Σ m HA) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (pmfn_pchunk Σ m usp HA Hsp c i st Hc Hn)).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (pmfn_schunk Σ m usp HA Hsp k s Hk)).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM (pmfn_sec Σ m usp HA Hsp)).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM (pmfn_quar Σ m usp HA Hsp)).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM (pmfn_dep Σ m usp HA Hsp)).
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (pmfn_fs Σ m usp HA Hsp)).
  - (* [comment removed for export] *)
    pose proof (pmfn_Tgrant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (pmfn_aceil Σ m HA) as (X0 & X). unfold SHB in X0.
    apply (ia_rep_transport _ Σ m m' (ART_ia Σ m HA) MU0 WM). unfold dsjl, ia_lits.
    repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; unfold g_ia_word, IAP, SEGTOP_A in *;
                                split; [destruct G5; lia|]; split; [lia | exact I]|]). apply Forall_nil.
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (pmfn_shadow Σ m usp HA Hsp)).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem) (mp lo : Z)
          (tb : list word) (w : word) (jp : list byte).
#[local] Notation n := 32768.
Hypothesis MST : mat_stable PMc.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x10000 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HMP8 : mp mod 8 = 0.
Hypothesis HCL : forall i, 0 <= i < 8 -> aclient (live Σ) (frames Σ) (bv_unsigned sp) (mp + i).
Hypothesis HWR : wr_at ctasegs m mp 8.
Hypothesis HMPS : mp + 8 <= lo \/ bv_unsigned sp <= mp.
Hypothesis MU1 : munch [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (bv_unsigned sp - 2336, bv_unsigned sp)] m m1.
Hypothesis WM1 : wmono ctasegs m m1.
Hypothesis IC1 : rw_cells ctasegs m1 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells ctasegs m1 (bv_unsigned sp + -80) [CB 8 jp].
Hypothesis IC3 : rw_cells ctasegs m1 (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr ctasegs m1 (bv_unsigned sp + -2128) tb.
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells ctasegs m1 (bv_unsigned sp + -2144) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 w].
Hypothesis IC5 : rw_cells ctasegs m1 (bv_unsigned sp + -2192)
     [C8 (Z_to_bv 64 pm_pc); C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 64); C8 (Z_to_bv 64 32768); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x1c4b2c)].
#[local] Notation usp := (bv_unsigned sp).

Lemma bkp_agree : forall (m' : mem) a k, rt_pres (live Σ) (frames Σ) (usp + -2192) m1 m' -> usp + -2192 <= a -> a + k <= USTACK_TOP ->
  agree_on (fun x => a <= x < a + k) m1 m'.
Proof. intros m' a k P H1 H2 x Hx. apply P. left. lia. Qed.

(* [comment removed for export] *)
Lemma mp_client : forall (Σ' : rtsA) sp', live Σ = live Σ \/ True -> (forall x, in_live (live Σ) x -> in_live (live Σ') x) -> frames Σ' = frames Σ ->
  sp' <= usp -> forall i, 0 <= i < 8 -> aclient (live Σ') (frames Σ') sp' (mp + i).
Proof.
  intros Σ' sp' _ HL HF Hsp i Hi. destruct (HCL i Hi) as [X|[X|[X|[X|X]]]].
  - left. lia.
  - right. left. exact X.
  - right. right. left. exact (HL _ X).
  - right. right. right. left. rewrite HF. exact X.
  - right. right. right. right. rewrite HF. exact X.
Qed.

Theorem back_cps_pm : cps ctasegs (core_post_pm Σ PMc (usp + -2144) gp (Z_to_bv 64 mp) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 pm_pc) (Z_to_bv 64 1)
                                            (Z_to_bv 64 (usp + -2144)) (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 n lo m1)
                                (posix_memalign_post RTA Σ PMc ra sp gp (Z_to_bv 64 0xba93f0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mp lo m).
Proof using MST HA LOW LOR SPT SPA HMP8 HCL HWR HMPS MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5.
  intros TT c2 Hc2 Hk. destruct Hc2 as (Σ' & p & HAST & HL & HF & HS & HCR & Hp0 & Hp64 & HpU).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (LO8 : 0x7fff7f800000 <= lo) by (pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN in *; lia).
  assert (W2 : forall ms, (exists m', ret_st (Z_to_bv 64 0x19c9e4) (Z_to_bv 64 (usp + -2144 + -48)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 mp)
                                      (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 pm_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2144)) (Z_to_bv 64 (usp + -97))
                                      s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
                            /\ ART_A Σ' m' /\ mem_inv ctasegs m' /\ wmono ctasegs m1 m' /\ stk ctasegs m' lo (usp + -2144 + -48)
                            /\ rt_pres (live Σ) (frames Σ) (usp + -2144 + -48) m1 m' /\ wr_at ctasegs m' p n /\ acc ctasegs m' p n) ->
             evt ctasegs (fun ms => exists m'', ret_st ra sp gp (Z_to_bv 64 0xba93f0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m'' ms
                  /\ rt_after RTA Σ' usp lo m m'' /\ rt_pres_ex (rt_live RTA Σ) (rt_frames RTA Σ) usp mp 8 m m''
                  /\ rw_cells ctasegs m'' mp [C8 (Z_to_bv 64 p)]
                  /\ wr_at ctasegs m'' p n /\ acc ctasegs m'' p n) ms).
  { intros ms (m' & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & ->) & ART' & MI' & WM' & ST' & PR' & WR' & AC').
    replace (usp + -2144 + -48) with (usp + -2192) in * by lia.
    rewrite (ret_pc_even 0x19c9e4) by (lia || reflexivity).
    assert (AG : forall a k, usp + -2192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m')
      by (intros a k H1 H2; exact (bkp_agree m' a k PR' H1 H2)).
    assert (TB' : u64arr ctasegs m' (usp + -2128) (ma_dec64 255 (u64s tb))).
    { pose proof (u64arr_rw_ma m1 _ _ TB1) as X. rewrite HTB in X.
      apply ma_rw_cells_u64arr. apply (rw_cells_agree ctasegs m1 m' _ _ X); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM']. }
    (* [comment removed for export] *)
    assert (HWR' : wr_at ctasegs m' mp 8) by exact (wr_at_wmono m m' _ _ HWR (wmono_trans ctasegs _ _ _ WM1 WM')).
    destruct (stk_CB m' mp 8 (RT_facts.wr_at_stk m' mp 8 HWR' ltac:(lia)) ltac:(lia)) as (jmp & CMP).
    assert (HmpB : 0 <= mp /\ mp + 8 <= 2 ^ 64) by (destruct HWR' as (W0 & W1 & _); lia).
    eapply evt_mono.
    { apply (pmalign_B_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pm_pc) (Z_to_bv 64 1) s8 s9 s10 s11 t3 t4 t5 t6
               s0 s1 s2 s3 s4 s5 s6 s7 F' fc' m' p mp lo jmp jp (ma_dec64 255 (u64s tb)) w).
      - unfold USTACK_TOP in HpU. lia.
      - exact Hp64.
      - lia.
      - lia.
      - exact ST'.
      - lia.
      - lia.
      - unfold USTACK_TOP in SPT. lia.
      - exact HMPS.
      - exact CMP.
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC2); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC3); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact TB'.
      - apply ma_dec64_length.
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC4); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree ctasegs m1 m' _ _ IC5); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact MI'. }
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> & MU'' & WM'' & MI'' & CMP'' & ST'').
    exists m''. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'; reflexivity|].
    assert (Hsp' : rtA_sp0 Σ' - STACK_WIN <= usp + -2192) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
    assert (HCL' : forall i, 0 <= i < 8 -> aclient (live Σ') (frames Σ') (usp + -2192) (mp + i)).
    { apply (mp_client Σ' (usp + -2192)); [right; exact I | | exact HF | lia].
      intros x Hx. rewrite HL. unfold in_live in *. destruct Hx as (q & k & Hq & Hr). exists q, k. split; [right; exact Hq | exact Hr]. }
    assert (MUC : munch (W_client Σ' (usp + -2192)) m' m'').
    { eapply (munch_weaken _ _ m' m''); [|exact MU'']. intros x Hx. cbn [outside]. split; [|exact I]. intros Hr.
      apply (W_client_cover Σ' (usp + -2192) x); [|exact Hx].
      replace x with (mp + (x - mp)) by lia. apply HCL'. lia. }
    assert (ART'' : ART_A Σ' m'') by exact (ART_transport _ Σ' m' m'' ART' MUC WM'' (art_avoid_client Σ' m' (usp + -2192) ART' Hsp')).
    split.
    { split; [exact ART''|]. split; [exact MI''|]. split; [exact (wmono_trans ctasegs _ _ _ WM1 (wmono_trans ctasegs _ _ _ WM' WM''))|]. exact ST''. }
    split.
    { intros a Ha Hna. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha.
      rewrite (MU'' a ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (PR' a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])).
      pose proof (pmfn_client Σ m usp HA Hsp0 (bv_unsigned a) Ha) as Ho. unfold W_pm in Ho. cbn [outside] in Ho.
      destruct Ho as (O1 & _ & _ & O4 & _).
      exact (MU1 a ltac:(cbn [outside]; split; [exact O1|]; split; [exact O4 | exact I])). }
    split; [exact CMP''|].
    cbn [rt_live RTA] in HL.
    exact (rta_acc_live Σ' m'' ART'' p n ltac:(rewrite HL; left; reflexivity)). }
  apply (cps_realizes ctasegs _ _ _ c2 (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W2) HAST).
  intros c3 Hc3. apply Hk. exists Σ', p. split; [exact Hc3|].
  cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit.
  split; [exact HL|]. split; [exact HF|]. split; [exact HS|]. split; [exact HCR|]. split; [exact Hp0|]. split; [exact Hp64 | exact HpU].
Qed.

End Back.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rta_pmalign : core_stmt_prim_pm -> posix_memalign_init_contract RTA.
Proof.
  intros CP Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mp lo
    FDO MST Ha0 Ha1 Ha2 Htp Hlen Hcr ART0 MI0 CALL UWOK HMP8 HCL HWR HMPS. subst a0 a1 a2 tp.      (* [comment removed for export] *)
  intros TT cf Hc Hk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0, HCL.
  unfold rtA_live, rtA_frames, rtA_credit in Hlen, Hcr, HCL. unfold PMA_ALIGN, PMA_SIZE in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (HmpB : 0 <= mp /\ mp + 8 <= 2 ^ 64) by (destruct HWR as (W0 & W1 & _); lia).
  (* [comment removed for export] *)
  destruct (site_trace_main m PC_PMALIGN (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) ra s0 sp ltac:(right; right; right; right; left; reflexivity) UWOK ltac:(lia))
    as (ch & tr & CHC & HTR & Htr & Htrl).
  assert (W1 : evt ctasegs (pmalign_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mp (l_T (lay Σ)) lo tr m)
                 (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 mp) (Z_to_bv 64 64) (Z_to_bv 64 32768) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc e_posix_memalign m)).
  { unfold entry_st, e_posix_memalign.
    exact (pmalign_A_spec ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mp
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo ch tr
             ST ltac:(unfold RT_STACK in LOR; lia) HLOH ltac:(unfold USTACK_TOP in SPT; lia) ltac:(lia) ltac:(lia) ltac:(lia) CHC HTR
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl GT1 HT HTl HTT SC UB MI0). }
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0xba93f0) t0 t1 t2 s0 s1 (Z_to_bv 64 mp) (Z_to_bv 64 64) (Z_to_bv 64 32768) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_posix_memalign m) ms ->
                  evt ctasegs (pmalign_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mp (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes ctasegs _ _ _ cf (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold pmalign_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & AFr & J0 & UB1 & ST1).
  set (usp := bv_unsigned sp) in *.
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by (unfold RT_STACK in LOR; lia).
  (* [comment removed for export] *)
  pose proof (front_ART_pm Σ m usp ART0 Hsp0 m1 MU1 WM1 UB1) as ART1.
  assert (Hc2 : ASTA RTA Σ PMc (eq (core_entry_pm Σ (usp + -2144) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc 32768 m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold core_entry_pm.
    replace (usp + -2144 + -176) with (usp + -2320) by lia.
    change (Z.b2z (from_primary 32768)) with 1. change (needed2 32768 + 64) with 33856. change (rz_size 32768) with 1024. reflexivity. }
  assert (ST1' : stk ctasegs m1 lo (usp + -2144 + -176)) by (replace (usp + -2144 + -176) with (usp + -2320) by lia; exact ST1).
  assert (TRC : trc_cells_pm (usp + -2144) tr m1 tb).
  { split; [replace (usp + -2144 + 16) with (usp + -2128) by lia; exact IC4|]. split; [replace (usp + -2144 + 16) with (usp + -2128) by lia; exact TB1 | exact HTB]. }
  assert (AFC : af_cells_pm (usp + -2144) (Z_to_bv 64 mp) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 pm_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2144))
                  (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 m1 j0).
  { split; replace (usp + -2144 + -176) with (usp + -2320) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= usp + -2144 + -176) by (unfold RT_STACK in LOR; lia).
  assert (SPT' : usp + -2144 + 2144 <= USTACK_TOP) by lia.
  assert (SPA' : (usp + -2144) mod 16 = 0).
  { pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q - 134). lia. }
  assert (K : forall c2, core_post_pm Σ PMc (usp + -2144) gp (Z_to_bv 64 mp) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 pm_pc) (Z_to_bv 64 1)
                           (Z_to_bv 64 (usp + -2144)) (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 32768 lo m1 c2 -> realizes ctasegs c2 TT).
  { intros c2 Hc2'. exact (back_cps_pm Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 mp lo (wr_trace tr tb) (Z_to_bv 64 (Z.of_nat (length tr))) jp
                             MST ART0 LOW' ltac:(unfold RT_STACK in LOR; lia) SPT SPA HMP8 HCL HWR HMPS MU1 WM1 IC1 IC2 IC3 TB1
                             ltac:(rewrite wr_trace_length by lia; exact HTB) IC4 IC5 TT c2 Hc2' Hk). }
  exact (CP Σ PMc m1 (usp + -2144) gp (Z_to_bv 64 mp) (Z_to_bv 64 64) (Z_to_bv 64 64) (Z_to_bv 64 63) (Z_to_bv 64 pm_pc) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2144))
           (Z_to_bv 64 (usp + -97)) s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc 32768 lo tr tb j0
           FDO MST ltac:(cbv beta; lia) eq_refl ltac:(lia) Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.

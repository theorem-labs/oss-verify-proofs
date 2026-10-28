(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_asan_free RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malpre R_unwind_chain RT_sites RT_freelift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition W_fc (T usp : Z) : list ivl :=
  [(T + 3168, T + 3169); (7550088, 7550092); (6966272, 7494704); (usp - 2336, usp)].

Section FnSep.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp.   (* [comment removed for export] *)
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_fc (l_T (lay Σ)) usp).

Lemma fc_Tgrant : grant_ok L T 4096.
Proof. exact (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)). Qed.

Lemma fc_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (rta_sp0_win Σ m HA) as X. pose proof (rta_sp0_range Σ m HA) as Y. unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *. lia. Qed.

(* [comment removed for export] *)
Lemma fc_off : forall a n, (a + n <= 0x10000 \/ SEGTOP_A <= a) -> a + n <= l_ACEIL L -> (a + n <= T \/ T + 4096 <= a) ->
  disjoint_from W a n.
Proof.
  intros a n H1 H2 H3. clear HA. unfold W_fc, SEGTOP_A in *. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma fc_T : forall a n, T <= a -> a + n <= T + 3168 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. pose proof fc_Tgrant as (G1 & G2 & G3 & G4 & G5). clear HA. unfold W_fc, SEGTOP_A in *. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma fc_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> (a + n <= 6966272 \/ 7494704 <= a) ->
  (a + n <= 7550088 \/ 7550092 <= a) -> disjoint_from W a n.
Proof.
  intros a n H1 H2 H3 H4. pose proof fc_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fc_aceil as (X & _). clear HA.
  unfold W_fc, SEGTOP_A, SHB in *. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma fc_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> i <> 2%nat -> b <= a -> a + n <= b + gn ->
  disjoint_from W a n.
Proof.
  intros i b gn a n Hi Hne H1 H2. pose proof (geo_grant Σ m HA b gn (nth_error_In _ _ Hi)) as (G1 & G2 & G3 & G4 & G5).
  assert (Hap : apart b gn T 4096).
  { destruct (Nat.lt_ge_cases i 2) as [Hl|Hl].
    - exact (geo_apart Σ m HA i 2 (b, gn) (T, 4096) Hl Hi eq_refl).
    - pose proof (geo_apart Σ m HA 2 i (T, 4096) (b, gn) ltac:(lia) eq_refl Hi) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold apart in Hap. apply fc_off; unfold SEGTOP_A in *; lia.
Qed.

Lemma fc_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (fc_grant 0 (l_PRB L) 0x2000011000 a n eq_refl ltac:(lia) H1 H2). Qed.

(* [comment removed for export] *)
Lemma fc_shad : forall a n, SHB <= a -> a + n <= 2 ^ 44 + SHB -> disjoint_from W a n.
Proof.
  intros a n H1 H2. pose proof fc_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fc_aceil as (X & _).
  apply fc_off; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia.
Qed.

Lemma fc_shad_len : forall x y, 0 <= x -> 0 <= y -> x + y <= 2 ^ 47 -> disjoint_from W (shad x) (Z.max 0 (y / 8)).
Proof. intros x y Hx Hy H. destruct (shad_len x y Hx Hy H) as [X Y]. apply fc_shad; lia. Qed.

(* [comment removed for export] *)
Lemma fc_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof.
  intros k s a n Hk H1 H2. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & G3 & G4 & G5) & _ & _ & HG).
  pose proof (proj1 (Forall_forall _ _) HG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as Ha.
  cbn [fst snd] in Ha. unfold apart in Ha. apply fc_off; unfold SEGTOP_A in *; lia.
Qed.

(* [comment removed for export] *)
Lemma fc_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  0 < l_PRB L /\ l_PRB L <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + kUserCap /\ rb SB c + kUserCap <= l_PRB L + 0x2000011000
  /\ l_PRB L + 0x2000011000 <= 2 ^ 47 /\ 32 <= ClassSize c.
Proof.
  intros c i st Hc Hn. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  pose proof fc_aceil as (_ & X).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
  unfold p_abeg, rb, kUserCap in *. repeat split; lia.
Qed.

Lemma fc_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W T c.
Proof.
  intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  pose proof fc_aceil as (_ & X).
  split; [|unfold pclass_avoid, pc_addr; apply fc_T; lia].
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
  unfold reg_avoid. split; [|split].
  - apply fc_prb; unfold rinfo, RIS_of; lia.
  - apply fc_prb; unfold fa, rb, kFaCap, kUserCap in *; lia.
  - apply fc_shad_len; unfold rb, kUserCap in *; lia.
Qed.

Lemma fc_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof.
  intros c i st Hc Hn. pose proof (fc_slot c i st Hc Hn) as (S0 & S1 & S2 & S3 & S4 & S5).
  assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
  { intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
    pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
  unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
  assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
  destruct st as [|n|n|].
  - apply fc_shad_len; lia.
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
    split; [apply fc_prb; lia|]. split; [intros _; apply fc_prb; lia|].
    split.
    + rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
      apply (dsj_sub W (shad AB) (Z.max 0 ((rz_size n + ru8 n) / 8))); [apply fc_shad_len; lia | lia|].
      pose proof (div8_add (rz_size n) (ru8 n) ltac:(lia) Hu). lia.
    + apply fc_shad_len; lia.
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
    assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
    split; [apply fc_prb; lia|]. split; [intros _; apply fc_prb; lia|].
    rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
    apply (dsj_sub W (shad AB) (Z.max 0 (S / 8))); [apply fc_shad_len; lia | lia|].
    pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as D.
    replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in D by ring. lia.
  - apply fc_shad_len; lia.
Qed.

Lemma fc_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof.
  intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & _).
  pose proof fc_aceil as (_ & X).
  assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
  { unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
  assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
  unfold schunk_avoid.
  split; [apply (fc_secmap k s); [exact Hk | lia | lia]|].
  split; [apply (fc_secmap k s); [exact Hk | lia | lia]|].
  split; [apply (fc_secmap k s); [exact Hk | lia | destruct (s_quar s); lia]|].
  split; [change (Z.max 0 ((4096 + 2048) / 8)) with (Z.max 0 (6144 / 8)); apply fc_shad_len; lia|].
  split.
  - apply (dsj_sub W (shad (s_mb s + 4096 + 2048)) (Z.max 0 (ru8 (s_n s) / 8))); [apply fc_shad_len; lia | lia|].
    destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply fc_shad_len; lia.
Qed.

Lemma fc_sec : sec_avoid W Σ.
Proof.
  split.
  - unfold sec_lits. repeat (apply Forall_cons; [cbn [fst snd]; apply fc_img; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
      i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]). apply Forall_nil.
  - pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
    apply (fc_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma fc_quar : quar_avoid W Σ.
Proof.
  split; [unfold qcacheT; apply fc_T; lia|].
  split; [repeat (apply Forall_cons; [cbn [fst snd]; apply fc_img; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia|]); apply Forall_nil|].
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
  pose proof (fc_slot 24 i CkBatch ltac:(lia) Hi) as (_ & S1 & S2 & S3 & _). change (ClassSize 24) with 8192 in *. apply fc_prb; lia.
Qed.

Lemma fc_dep : dep_avoid W L.
Proof.
  split; [repeat (apply Forall_cons; [cbn [fst snd]; apply fc_img; unfold SEGTOP_A; lia|]); apply Forall_nil|].
  split; [apply (fc_grant 6 (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
  apply (fc_grant 7 (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma fc_flags_range : forall c, (c = 0 \/ c = 2 \/ c = 4) -> 0x1000 <= 0x1000 + flags_off c /\ 0x1000 + flags_off c + NF c <= 0x9000.
Proof. intros c Hc. unfold flags_off, NF. destruct Hc as [ -> | [ -> | -> ] ]; cbn; lia. Qed.

Lemma fc_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (fc_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma fc_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 4)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (F0 & F2 & F4 & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | -> ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 F4)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4) by (destruct Hk as [ -> | [ -> | -> ] ]; cbn; lia).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof fc_aceil as (_ & X). pose proof (fc_flags_range _ Hc) as (R1 & R2).
  unfold fs_cls_avoid. split; [apply fc_fsb; destruct Hc as [ -> | [ -> | -> ] ]; lia|]. split.
  - rewrite Hlen. apply fc_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | -> ] ]; cbn; lia).
    split; [apply fc_fsb; lia|]. apply (dsj_sub W (shad (frame_addr (l_FSB L) (Z.of_nat k) p)) (Z.max 0 (fsz (Z.of_nat k) / 8)));
      [apply fc_shad_len; lia | lia | pose proof (Z.div_pos (fsz (Z.of_nat k)) 8 ltac:(lia) ltac:(lia)); lia].
Qed.

Lemma fc_fs : fs_avoid W Σ.
Proof.
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply fc_fsb; lia|].
  split; [exact (fc_fs_cls 0%nat ltac:(lia))|]. split; [exact (fc_fs_cls 2%nat ltac:(lia))|]. split; [exact (fc_fs_cls 4%nat ltac:(lia))|].
  split; [unfold fs_lits; repeat (apply Forall_cons; [cbn [fst snd]; apply fc_img; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
      apply Forall_nil|].
  split; [apply (fc_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply fc_T; lia|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & X3). apply fc_fsb; lia.
Qed.

Lemma fc_shadow : shadow_avoid W L.
Proof.
  pose proof fc_aceil as (X1 & X2). split.
  - apply fc_shad_len; unfold SHB in *; lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0xbfc730) by (unfold SH_RNGS, IMG_HULL, GD_IMG_END, CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply fc_shad; unfold shad; [pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)); lia|].
    assert ((snd r - 1) / 8 <= 0xbfc730 / 8) by (apply Z.div_le_mono; lia). change (0xbfc730 / 8) with 0x17f8e6 in *. unfold SHB. lia.
Qed.

(* [comment removed for export] *)
Lemma fc_consts : forall x, in_rngs (consts_rngs L) x -> x <> T + 3168 -> outside W x.
Proof.
  intros x Hx NE. pose proof fc_Tgrant as (G1 & G2 & G3 & G4 & G5).
  pose proof (geo_grant Σ m HA (l_TCX L) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
  pose proof fc_aceil as (A1 & A2).
  assert (D : Forall (fun r => disjoint_from [(7550088, 7550092); (6966272, 7494704); (usp - 2336, usp)] (fst r) (snd r - fst r)) (consts_rngs L)).
  { clear Hx NE HA. unfold consts_rngs. unfold_consts. unfold SEGTOP_A, SHB in *.
    repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; refine (conj _ (conj _ (conj _ I))); lia|]). apply Forall_nil. }
  unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). pose proof (proj1 (Forall_forall _ _) D r Hr) as Dr.
  pose proof (disjoint_outside _ _ _ x Dr ltac:(lia)) as O. clear D Dr. cbn [W_fc outside] in *. split; [lia | exact O].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fc_client : forall x, aclient (live Σ) (frames Σ) usp x -> outside W x.
Proof.
  intros x Hx. pose proof fc_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fc_aceil as (X1 & X2).
  destruct Hx as [H|[H|[H|[H|H]]]].
  - clear HA. unfold W_fc, SEGTOP_A, SHB in *. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - destruct H as ((lo & hi & Hin & Hlh) & _). unfold CLIENT_STATIC in Hin.
    apply (disjoint_outside W lo (hi - lo)); [|lia].
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; apply fc_img; unfold SEGTOP_A; lia.
  - destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
    destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hn & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & _ & Hn' & -> & Y1 & Y5)].
    + pose proof (fc_slot c i _ Hc Hn) as (_ & S1 & S2 & S3 & _). apply fc_prb; lia.
    + destruct (In_nth_error _ _ Hs) as (k & Hk). apply (fc_secmap k s); [exact Hk | unfold s_ubeg; lia | rewrite <- Hn' in Y1; unfold s_ubeg; lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
    destruct (sep_frame Σ m HA f k Hin) as (Y1 & Y2 & Y3). apply fc_fsb; lia.
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
    destruct (sep_fshad Σ m HA f k Hin) as (Y1 & Y2). apply fc_shad; unfold K_HIGH_SHADOW_hi, SHB in *; lia.
Qed.

End FnSep.

Section Front.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp.   (* [comment removed for export] *)
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation W := (W_fc (l_T (lay Σ)) usp).

(* [comment removed for export] *)
Theorem cfront_ART : forall m', munch [(T + 3168, T + 3169); (usp - 2336, usp)] m m' -> wmono bsegs m m' ->
  rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)] -> ART_A Σ m'.
Proof using HA Hsp.
  intros m' MU0 WM TB. pose proof (ART_wf Σ m HA) as Hwf.
  assert (MU : munch W m m').
  { eapply (munch_weaken _ _ m m'); [|exact MU0]. intros x Hx. unfold W_fc in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (X1 & _ & _ & X4 & _). split; [exact X1|]. split; [exact X4 | exact I]. }
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  - apply (consts_rep_frame (lay Σ) m m' (ART_consts Σ m HA)); [|exact WM].
    pose proof (mp_cells Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UB).
    pose proof (fc_Tgrant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (fc_aceil Σ m HA) as (_ & X).
    intros a Ha. destruct (Z.eq_dec (bv_unsigned a) (T + 3168)) as [E|NE].
    + assert (Ea : a = wa (T + 3168)) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned). subst a.
      assert (Hx : T + 3168 + 1 <= img_hull_lo \/ img_hull_hi <= T + 3168) by (unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
      rewrite (fn_byte m' _ _ TB Hx ltac:(lia)), (fn_byte m _ _ UB Hx ltac:(lia)). reflexivity.
    + apply MU. exact (fc_consts Σ m usp HA Hsp _ Ha NE).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (proj1 (fc_reg Σ m usp HA Hsp c Hc))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM (proj2 (fc_reg Σ m usp HA Hsp c Hc))).
  - destruct (ART_chunk Σ m HA) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (fc_pchunk Σ m usp HA Hsp c i st Hc Hn)).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (fc_schunk Σ m usp HA Hsp k s Hk)).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM (fc_sec Σ m usp HA Hsp)).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM (fc_quar Σ m usp HA Hsp)).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM (fc_dep Σ m usp HA Hsp)).
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (fc_fs Σ m usp HA Hsp)).
  - (* [comment removed for export] *)
    pose proof (fc_Tgrant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (fc_aceil Σ m HA) as (X0 & X). unfold SHB in X0.
    apply (ia_rep_transport _ Σ m m' (ART_ia Σ m HA) MU0 WM). unfold dsjl, ia_lits.
    repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; unfold g_ia_word, IAP, SEGTOP_A in *;
                                split; [destruct G5; lia|]; split; [lia | exact I]|]). apply Forall_nil.
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (fc_shadow Σ m usp HA Hsp)).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

End Front.

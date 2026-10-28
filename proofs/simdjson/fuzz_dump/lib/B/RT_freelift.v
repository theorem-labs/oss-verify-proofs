(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_asan_free RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malpre R_unwind_gen RT_gentrace.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Lemma fn_seg_rom_off : forall a : word, bv_unsigned a + 1 <= img_hull_lo \/ img_hull_hi <= bv_unsigned a -> seg_rom bsegs a = None.
Proof.
  intros a H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  assert (FS : find_segment bsegs (bv_unsigned a) 1 = None).
  { destruct H as [H|H].
    - apply find_segment_below. exact (forallb_mono_bot bsegs (bv_unsigned a + 1) img_hull_lo H asegs_bot).
    - apply find_segment_above; [pose proof (bv_unsigned_in_range 64 a); lia | exact (forallb_mono_top bsegs img_hull_hi _ H asegs_top)]. }
  rewrite FS. reflexivity.
Qed.

Lemma fn_byte : forall (m : mem) x b, rw_cells bsegs m x [C1 b] -> x + 1 <= img_hull_lo \/ img_hull_hi <= x -> x < 2 ^ 64 ->
  m (wa x) = Some b.
Proof.
  intros m x b [[_ (B0 & B1 & B)] _] Hx Hl. specialize (B 0%nat ltac:(cbn; lia)). cbn in B. rewrite Z.add_0_r in B.
  unfold mrd in B. destruct (m (wa x)) as [b'|] eqn:E; [exact B|].
  rewrite fn_seg_rom_off in B; [discriminate|]. rewrite wa_unsigned by lia. exact Hx.
Qed.

Lemma div8_add : forall x y, 0 <= x -> 0 <= y -> x / 8 + y / 8 <= (x + y) / 8.
Proof. intros x y Hx Hy. Z.div_mod_to_equations. lia. Qed.

Lemma div8_add3 : forall x y z, 0 <= x -> 0 <= y -> 0 <= z -> x / 8 + y / 8 + z / 8 <= (x + y + z) / 8.
Proof. intros x y z Hx Hy Hz. pose proof (div8_add x y Hx Hy). pose proof (div8_add (x + y) z ltac:(lia) Hz). lia. Qed.

Lemma shad_len : forall x y, 0 <= x -> 0 <= y -> x + y <= 2 ^ 47 -> SHB <= shad x /\ shad x + Z.max 0 (y / 8) <= 2 ^ 44 + SHB.
Proof.
  intros x y Hx Hy H. unfold shad. pose proof (div8_add x y Hx Hy) as D. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). assert ((x + y) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Lemma farun_lenZ : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k.
Proof. intros k Hk. unfold farun. rewrite repeat_length. lia. Qed.
Lemma fdrun_lenZ : forall k, 0 <= k -> Z.of_nat (length (fdrun k)) = k.
Proof. intros k Hk. unfold fdrun. rewrite repeat_length. lia. Qed.

Lemma fl_ushadow_len : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = ru8 n / 8.
Proof.
  intros n Hn. unfold ushadow, ru8. rewrite length_app, repeat_length. replace (8 * ((n + 7) / 8) / 8) with ((n + 7) / 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length].
  - pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite E in D. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
    replace (n + 7) with ((n / 8) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
  - pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
    rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). cbn [Z.of_nat Pos.of_succ_nat].
    replace (n + 7) with ((n / 8 + 1) * 8 + (n mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (n mod 8 - 1) 8) by lia. lia.
Qed.

Lemma fl_rz_facts : forall n, rz_size n mod 16 = 0 /\ 16 <= rz_size n.
Proof.
  intros n. unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)).
  split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia].
Qed.

Lemma fl_slot_room : forall c n, 1 <= c <= 31 -> 0 <= n -> rz_size n + n <= ClassSize c ->
  rz_size n + ru8 n <= ClassSize c /\ rz_size n + 16 <= ClassSize c.
Proof.
  intros c n Hc Hn H. pose proof (ClassSize_range c Hc) as (Hcs & Hm). pose proof (fl_rz_facts n) as (R1 & R2).
  assert (Hd : exists k, ClassSize c - rz_size n = 16 * k).
  { exists ((ClassSize c - rz_size n) / 16). pose proof (Z.div_mod (ClassSize c - rz_size n) 16 ltac:(lia)) as D.
    assert ((ClassSize c - rz_size n) mod 16 = 0); [|lia]. rewrite Zminus_mod. rewrite R1.
    replace (ClassSize c mod 16) with 0; [reflexivity|]. symmetry. (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hm; [|lia]; apply (Z.divide_trans 16 32); [exists 2; reflexivity | exact Hm]). }
  destruct Hd as [k Hk]. unfold ru8. split.
  - assert (8 * ((n + 7) / 8) <= 16 * k); [|lia]. assert ((n + 7) / 8 < 2 * k + 1); [|lia]. apply Z.div_lt_upper_bound; lia.
  - destruct (Z_le_dec n 0) as [Hz|Hz].
    + assert (n = 0) by lia. subst n. unfold rz_size, rz_log in *. cbn in *. lia.
    + lia.
Qed.

Definition W_fn (T usp : Z) : list ivl :=
  [(T + 3168, T + 3169); (2124744, 2124748); (1540928, 2069360); (usp - 2288, usp)].

Section FnSep.
Variables (Σ : rtsA) (m : mem) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_fn (l_T (lay Σ)) usp).

Lemma fn_Tgrant : grant_ok L T 4096.
Proof. exact (geo_grant Σ m HA T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)). Qed.

Lemma fn_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof. pose proof (rta_sp0_win Σ m HA) as X. pose proof (rta_sp0_range Σ m HA) as Y. unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *. lia. Qed.

Lemma fn_off : forall a n, (a + n <= 0x10000 \/ SEGTOP_A <= a) -> a + n <= l_ACEIL L -> (a + n <= T \/ T + 4096 <= a) ->
  disjoint_from W a n.
Proof.
  intros a n H1 H2 H3. clear HA. unfold W_fn, SEGTOP_A in *. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma fn_T : forall a n, T <= a -> a + n <= T + 3168 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. pose proof fn_Tgrant as (G1 & G2 & G3 & G4 & G5). clear HA. unfold W_fn, SEGTOP_A in *. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma fn_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> (a + n <= 1540928 \/ 2069360 <= a) ->
  (a + n <= 2124744 \/ 2124748 <= a) -> disjoint_from W a n.
Proof.
  intros a n H1 H2 H3 H4. pose proof fn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fn_aceil as (X & _). clear HA.
  unfold W_fn, SEGTOP_A, SHB in *. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma fn_grant : forall i b gn a n, nth_error (startup_grants L) i = Some (b, gn) -> i <> 2%nat -> b <= a -> a + n <= b + gn ->
  disjoint_from W a n.
Proof.
  intros i b gn a n Hi Hne H1 H2. pose proof (geo_grant Σ m HA b gn (nth_error_In _ _ Hi)) as (G1 & G2 & G3 & G4 & G5).
  assert (Hap : apart b gn T 4096).
  { destruct (Nat.lt_ge_cases i 2) as [Hl|Hl].
    - exact (geo_apart Σ m HA i 2 (b, gn) (T, 4096) Hl Hi eq_refl).
    - pose proof (geo_apart Σ m HA 2 i (T, 4096) (b, gn) ltac:(lia) eq_refl Hi) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold apart in Hap. apply fn_off; unfold SEGTOP_A in *; lia.
Qed.

Lemma fn_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (fn_grant 0 (l_PRB L) 0x2000011000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma fn_shad : forall a n, SHB <= a -> a + n <= 2 ^ 44 + SHB -> disjoint_from W a n.
Proof.
  intros a n H1 H2. pose proof fn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fn_aceil as (X & _).
  apply fn_off; unfold SEGTOP_A, SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia.
Qed.

Lemma fn_shad_len : forall x y, 0 <= x -> 0 <= y -> x + y <= 2 ^ 47 -> disjoint_from W (shad x) (Z.max 0 (y / 8)).
Proof. intros x y Hx Hy H. destruct (shad_len x y Hx Hy H) as [X Y]. apply fn_shad; lia. Qed.

Lemma fn_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof.
  intros k s a n Hk H1 H2. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & G3 & G4 & G5) & _ & _ & HG).
  pose proof (proj1 (Forall_forall _ _) HG (T, 4096) ltac:(unfold startup_grants; right; right; left; reflexivity)) as Ha.
  cbn [fst snd] in Ha. unfold apart in Ha. apply fn_off; unfold SEGTOP_A in *; lia.
Qed.

Lemma fn_slot : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  0 < l_PRB L /\ l_PRB L <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + kUserCap /\ rb SB c + kUserCap <= l_PRB L + 0x2000011000
  /\ l_PRB L + 0x2000011000 <= 2 ^ 47 /\ 32 <= ClassSize c.
Proof.
  intros c i st Hc Hn. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  pose proof fn_aceil as (_ & X).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
  unfold p_abeg, rb, kUserCap in *. repeat split; lia.
Qed.

Lemma fn_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W T c.
Proof.
  intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  pose proof fn_aceil as (_ & X).
  split; [|unfold pclass_avoid, pc_addr; apply fn_T; lia].
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (apply Z.mul_nonneg_nonneg; lia).
  unfold reg_avoid. split; [|split].
  - apply fn_prb; unfold rinfo, RIS_of; lia.
  - apply fn_prb; unfold fa, rb, kFaCap, kUserCap in *; lia.
  - apply fn_shad_len; unfold rb, kUserCap in *; lia.
Qed.

Lemma fn_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof.
  intros c i st Hc Hn. pose proof (fn_slot c i st Hc Hn) as (S0 & S1 & S2 & S3 & S4 & S5).
  assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
  { intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
    pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
  unfold pchunk_avoid. set (AB := p_abeg SB c i) in *. set (S := ClassSize c) in *.
  assert (HS0 : 0 <= S / 8) by (apply Z.div_pos; lia).
  destruct st as [|n|n|].
  - apply fn_shad_len; lia.
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    pose proof (fl_ushadow_len n F2) as U. assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia).
    split; [apply fn_prb; lia|]. split; [intros _; apply fn_prb; lia|].
    split.
    + rewrite length_app, Nat2Z.inj_add, farun_lenZ, U by lia.
      apply (dsj_sub W (shad AB) (Z.max 0 ((rz_size n + ru8 n) / 8))); [apply fn_shad_len; lia | lia|].
      pose proof (div8_add (rz_size n) (ru8 n) ltac:(lia) Hu). lia.
    + apply fn_shad_len; lia.
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (fl_slot_room c n Hc F2 F1) as (R1 & R2). pose proof (fl_rz_facts n) as (R3 & R4).
    assert (Hu : 0 <= ru8 n) by (unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hr8 : 0 <= rz_size n / 8) by (apply Z.div_pos; lia). assert (Hu8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
    assert (Hd8 : 0 <= (S - rz_size n - ru8 n) / 8) by (apply Z.div_pos; lia).
    split; [apply fn_prb; lia|]. split; [intros _; apply fn_prb; lia|].
    rewrite !length_app, !Nat2Z.inj_add, !farun_lenZ, fdrun_lenZ by lia.
    apply (dsj_sub W (shad AB) (Z.max 0 (S / 8))); [apply fn_shad_len; lia | lia|].
    pose proof (div8_add3 (rz_size n) (ru8 n) (S - rz_size n - ru8 n) ltac:(lia) Hu ltac:(lia)) as D.
    replace (rz_size n + ru8 n + (S - rz_size n - ru8 n)) with S in D by ring. lia.
  - apply fn_shad_len; lia.
Qed.

Lemma fn_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof.
  intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & (G1 & G2 & G3 & G4 & G5) & _).
  pose proof fn_aceil as (_ & X).
  assert (Hroom : 6144 + ru8 (s_n s) <= smsz (s_n s)).
  { unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia. }
  assert (Hu : s_n s <= ru8 (s_n s)) by (unfold ru8; pose proof (Z.div_mod (s_n s + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (s_n s + 7) 8 ltac:(lia)); lia).
  unfold schunk_avoid.
  split; [apply (fn_secmap k s); [exact Hk | lia | lia]|].
  split; [apply (fn_secmap k s); [exact Hk | lia | lia]|].
  split; [apply (fn_secmap k s); [exact Hk | lia | destruct (s_quar s); lia]|].
  split; [change (Z.max 0 ((4096 + 2048) / 8)) with (Z.max 0 (6144 / 8)); apply fn_shad_len; lia|].
  split.
  - apply (dsj_sub W (shad (s_mb s + 4096 + 2048)) (Z.max 0 (ru8 (s_n s) / 8))); [apply fn_shad_len; lia | lia|].
    destruct (s_quar s); [rewrite fdrun_lenZ by (apply Z.div_pos; lia) | rewrite (fl_ushadow_len (s_n s)) by lia]; lia.
  - apply fn_shad_len; lia.
Qed.

Lemma fn_sec : sec_avoid W Σ.
Proof.
  split.
  - unfold sec_lits. repeat (apply Forall_cons; [cbn [fst snd]; apply fn_img; unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_page,
      i_sec_range, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance, SEGTOP_A; lia|]). apply Forall_nil.
  - pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
    apply (fn_grant 1 (l_PAB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma fn_quar : quar_avoid W Σ.
Proof.
  split; [unfold qcacheT; apply fn_T; lia|].
  split; [repeat (apply Forall_cons; [cbn [fst snd]; apply fn_img; unfold i_q_global, i_q_cmutex, INST, g_instance, SEGTOP_A; lia|]); apply Forall_nil|].
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
  pose proof (fn_slot 24 i CkBatch ltac:(lia) Hi) as (_ & S1 & S2 & S3 & _). change (ClassSize 24) with 8192 in *. apply fn_prb; lia.
Qed.

Lemma fn_dep : dep_avoid W L.
Proof.
  split; [repeat (apply Forall_cons; [cbn [fst snd]; apply fn_img; unfold SEGTOP_A; lia|]); apply Forall_nil|].
  split; [apply (fn_grant 6 (l_DNB L) 0x100000); [reflexivity | lia | lia | lia]|].
  apply (fn_grant 7 (l_SSB L) 0x800000); [reflexivity | lia | lia | lia].
Qed.

Lemma fl_flags_range : forall c, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1 \/ c = 3 \/ c = 2) -> 0x1000 <= 0x1000 + flags_off c /\ 0x1000 + flags_off c + NF c <= 0x9000.
Proof. intros c Hc. unfold flags_off, NF. destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia. Qed.

Lemma fn_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof. intros a n H1 H2. exact (fn_grant 5 (l_FSB L) 0xb09000 a n eq_refl ltac:(lia) H1 H2). Qed.

Lemma fn_fs_cls : forall k, (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (F0 & F2 & F4 & Fc1 & Fc3 & Fc2 & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 F4) | exact (proj1 Fc1) | exact (proj1 Fc3) | exact (proj1 Fc2)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 5 \/ Z.of_nat k = 0 \/ Z.of_nat k = 4 \/ Z.of_nat k = 1 \/ Z.of_nat k = 3 \/ Z.of_nat k = 2) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof fn_aceil as (_ & X). pose proof (fl_flags_range _ Hc) as (R1 & R2).
  unfold fs_cls_avoid. split; [apply fn_fsb; destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; lia|]. split.
  - rewrite Hlen. apply fn_fsb; unfold fl_base; lia.
  - intros p Hp _. pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (A1 & A2). unfold kFakeStackSize in A2.
    assert (Hfz : 0 < fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
    split; [apply fn_fsb; lia|]. apply (dsj_sub W (shad (frame_addr (l_FSB L) (Z.of_nat k) p)) (Z.max 0 (fsz (Z.of_nat k) / 8)));
      [apply fn_shad_len; lia | lia | pose proof (Z.div_pos (fsz (Z.of_nat k)) 8 ltac:(lia) ltac:(lia)); lia].
Qed.

Lemma fn_fs : fs_avoid W Σ.
Proof.
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split; [apply fs_gavoid_of_fsb; intros; apply fn_fsb; lia|].
  split; [exact (fn_fs_cls 5%nat ltac:(lia))|]. split; [exact (fn_fs_cls 0%nat ltac:(lia))|]. split; [exact (fn_fs_cls 4%nat ltac:(lia))|]. split; [exact (fn_fs_cls 1%nat ltac:(lia))|]. split; [exact (fn_fs_cls 3%nat ltac:(lia))|]. split; [exact (fn_fs_cls 2%nat ltac:(lia))|].
  split; [unfold fs_lits; repeat (apply Forall_cons; [cbn [fst snd]; apply fn_img; unfold tpA, g_real_tls_get_addr, g_dtv_ptr, g_dtv1,
      g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; lia|]);
      apply Forall_nil|].
  split; [apply (fn_grant 4 (l_DTV L) 4096); [reflexivity | lia | lia | lia]|].
  split; [apply fn_T; lia|].
  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & X3). apply fn_fsb; lia.
Qed.

Lemma fn_shadow : shadow_avoid W L.
Proof.
  pose proof fn_aceil as (X1 & X2). split.
  - apply fn_shad_len; unfold SHB in *; lia.
  - apply Forall_forall. intros r Hr.
    assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0x6ccd58) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply fn_shad; unfold shad; [pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)); lia|].
    assert ((snd r - 1) / 8 <= 0x6ccd58 / 8) by (apply Z.div_le_mono; lia). change (0x6ccd58 / 8) with 891307 in *. unfold SHB. lia.
Qed.

Lemma fn_consts : forall x, in_rngs (consts_rngs L) x -> x <> T + 3168 -> outside W x.
Proof.
  intros x Hx NE. pose proof fn_Tgrant as (G1 & G2 & G3 & G4 & G5).
  pose proof (geo_grant Σ m HA (l_TCX L) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
  pose proof fn_aceil as (A1 & A2).
  assert (D : Forall (fun r => disjoint_from [(2124744, 2124748); (1540928, 2069360); (usp - 2288, usp)] (fst r) (snd r - fst r)) (consts_rngs L)).
  { clear Hx NE HA. unfold consts_rngs. unfold_consts. unfold SEGTOP_A, SHB in *.
    repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; refine (conj _ (conj _ (conj _ I))); lia|]). apply Forall_nil. }
  unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hrx). pose proof (proj1 (Forall_forall _ _) D r Hr) as Dr.
  pose proof (disjoint_outside _ _ _ x Dr ltac:(lia)) as O. clear D Dr. cbn [W_fn outside] in *. split; [lia | exact O].
Qed.

Theorem fn_ART : forall m', munch W m m' -> wmono bsegs m m' -> ia_state true m' -> rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)] ->
  ART_A Σ m'.
Proof.
  intros m' MU WM IS TB. pose proof (ART_wf Σ m HA) as Hwf.
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  -
    apply (consts_rep_frame L m m' (ART_consts Σ m HA)); [|exact WM].
    pose proof (mp_cells Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UB).
    pose proof fn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fn_aceil as (_ & X).
    intros a Ha. destruct (Z.eq_dec (bv_unsigned a) (T + 3168)) as [E|NE].
    + assert (Ea : a = wa (T + 3168)) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned). subst a.
      assert (Hx : T + 3168 + 1 <= img_hull_lo \/ img_hull_hi <= T + 3168) by (unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
      rewrite (fn_byte m' _ _ TB Hx ltac:(lia)), (fn_byte m _ _ UB Hx ltac:(lia)). reflexivity.
    + apply MU. exact (fn_consts _ Ha NE).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (proj1 (fn_reg c Hc))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM (proj2 (fn_reg c Hc))).
  - destruct (ART_chunk Σ m HA) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (fn_pchunk c i st Hc Hn)).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (fn_schunk k s Hk)).
  - exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM fn_sec).
  - exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM fn_quar).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM fn_dep).
  - exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM fn_fs).
  - exists true. exact IS.
  - exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM fn_shadow).
  - exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

Lemma fn_client : forall x, aclient (live Σ) (frames Σ) usp x -> outside W x.
Proof.
  intros x Hx. pose proof fn_Tgrant as (G1 & G2 & G3 & G4 & G5). pose proof fn_aceil as (X1 & X2).
  destruct Hx as [H|[H|[H|[H|H]]]].
  - clear HA. unfold W_fn, SEGTOP_A, SHB in *. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - destruct H as ((lo & hi & Hin & Hlh) & _). unfold CLIENT_STATIC in Hin.
    apply (disjoint_outside W lo (hi - lo)); [|lia].
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; apply fn_img; unfold SEGTOP_A; lia.
  - destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W p n); [|lia].
    destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hn & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & _ & Hn' & -> & Y1 & Y5)].
    + pose proof (fn_slot c i _ Hc Hn) as (_ & S1 & S2 & S3 & _). apply fn_prb; lia.
    + destruct (In_nth_error _ _ Hs) as (k & Hk). apply (fn_secmap k s); [exact Hk | unfold s_ubeg; lia | rewrite <- Hn' in Y1; unfold s_ubeg; lia].
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W f (fs_size k - 8)); [|lia].
    destruct (sep_frame Σ m HA f k Hin) as (Y1 & Y2 & Y3). apply fn_fsb; lia.
  - destruct H as (f & k & Hin & Hfx). apply (disjoint_outside W (shad f) (shad (f + fs_size k) - shad f)); [|lia].
    destruct (sep_fshad Σ m HA f k Hin) as (Y1 & Y2). apply fn_shad; unfold K_HIGH_SHADOW_hi, SHB in *; lia.
Qed.

End FnSep.

Lemma fl_ASTA_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Theorem rta_free_null : free_null_contract RTA.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> -> ART0 MI0 CALL UWOK.
  intros TT cf Hc Hk. cbn [ART rt_frames rt_live rt_sp0 RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0 in *.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & _ & _ & AI & MCS & _ & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & _ & _ & GT5).
  pose proof (geo_grant Σ m ART0 (l_TCX (lay Σ)) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (GX1 & _ & _ & _ & GX5).
  destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  set (usp := bv_unsigned sp) in *.
  destruct (ART_ia Σ m ART0) as (b & IS).
  destruct (art_trace_main Σ m free_pc ra s0 sp ART0 ltac:(unfold l_ACEIL, RT_STACK in *; lia) UWOK ltac:(unfold free_pc; lia))
    as (ch & tr & CHC & TR & _ & _).
  assert (W1 : evt bsegs (free_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_T (lay Σ)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)).
  { apply (free_null_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b ch tr);
      try assumption; unfold RT_STACK, USTACK_TOP, img_hull_lo, img_hull_hi, SEGTOP_A in *; lia. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hk. unfold free_null_post in Hc1.
  apply AST_exI in Hc1 as [t0' Hc1]. apply AST_exI in Hc1 as [t1' Hc1]. apply AST_exI in Hc1 as [t2' Hc1]. apply AST_exI in Hc1 as [a0' Hc1].
  exists a0'. unfold icpt_postF, ASTA in *. eapply AST_conseq; [exact Hc1| |auto]. intros ms PO.
  destruct PO as (u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m' & -> & MU & WM & MI & IS' & TB & ST').
  exists m'. split; [do 15 eexists; reflexivity|].
  assert (Hsp : l_ACEIL (lay Σ) + 0xF000 <= usp) by (unfold l_ACEIL, RT_STACK in *; lia).
  split; [split; [|split; [exact MI | split; [exact WM | exact ST']]]|].
  - cbn [ART RTA]. exact (fn_ART Σ m usp ART0 Hsp m' MU WM IS' TB).
  - split; [|exact I]. intros a Ha _. apply MU. exact (fn_client Σ m usp ART0 Hsp _ (aclient_vis _ _ _ _ _ Ha)).
Qed.

End GWIN.

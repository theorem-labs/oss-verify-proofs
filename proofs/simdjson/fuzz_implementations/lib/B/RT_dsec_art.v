(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_led R_prim_kit RT_drain_kit RT_dsec_fkit RT_dsec_kit RT_dsec_geo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition IZ_S : list ivl :=
  [(i_sec_mutex, i_sec_mutex + 4); (i_sec_nres + 8, i_sec_nres + 16); (i_sec_sorted, i_sec_sorted + 40); (i_gstat_alloc, i_gstat_alloc + 16)].

Lemma IZ_S_in : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) IZ_S.
Proof. unfold IZ_S, i_sec_mutex, i_sec_nres, i_sec_sorted, i_gstat_alloc, INST, g_instance, SEGTOP_A. repeat constructor; cbn; lia. Qed.

Definition schunk_avoid_nh (W : list ivl) (s : secst) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  disjoint_from W mb 24 /\ disjoint_from W AB 16 /\ disjoint_from W M (if s_quar s then 24 else 16)
  /\ disjoint_from W (shad mb) (Z.max 0 ((4096 + 2048) / 8))
  /\ disjoint_from W (shad (AB + 2048)) (Z.of_nat (length (if s_quar s then fdrun (ru8 n / 8) else ushadow n)))
  /\ disjoint_from W (shad (AB + 2048 + ru8 n)) (Z.max 0 ((msz - 4096 - 2048 - ru8 n) / 8)).

Lemma schunk_transport_nh : forall W {AN : list (Z * Z * Z)} k k' s (m m' : mem), schunk AN k s m -> munch W m m' -> wmono bsegs m m' ->
  schunk_avoid_nh W s -> rw_cells bsegs m' (s_mb s + 24) [C8 (Z_to_bv 64 (Z.of_nat k'))] -> schunk AN k' s m'.
Proof.
  intros W AN k k' s m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6) HI. unfold schunk in *.
  destruct H as (Hs & Wr & Hl & Hh & S & B1 & B2 & B3).
  split.
  { unfold shdr in *.
    apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 (s_mb s)); C8 (Z_to_bv 64 (smsz (s_n s))); C8 (Z_to_bv 64 (needed (s_n s) + rz_size (s_n s)))]
                                   [C8 (Z_to_bv 64 (Z.of_nat k))])) in Hs.
    destruct Hs as (Hs & _).
    change [C8 (Z_to_bv 64 (s_mb s)); C8 (Z_to_bv 64 (smsz (s_n s))); C8 (Z_to_bv 64 (needed (s_n s) + rz_size (s_n s))); C8 (Z_to_bv 64 (Z.of_nat k'))]
      with ([C8 (Z_to_bv 64 (s_mb s)); C8 (Z_to_bv 64 (smsz (s_n s))); C8 (Z_to_bv 64 (needed (s_n s) + rz_size (s_n s)))] ++ [C8 (Z_to_bv 64 (Z.of_nat k'))]).
    apply rwc_app. split; [apply (rw_cells_transport bsegs W m m' _ _ Hs MU WM); cbn [cells_size csize Nat.add Z.of_nat]; exact A1|].
    cbn [cells_size csize Nat.add Z.of_nat]. exact HI. }
  split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (lch_transport W m m' _ _ Hl MU WM A2)|].
  split; [destruct (s_quar s); [exact (qhdr3_transport W m m' _ _ Hh MU WM A3) | exact (ahdr_transport W m m' _ _ Hh MU WM A3)]|].
  split; [exact (stk_wmono m m' _ _ S WM)|].
  split; [apply (bytes_at_transport bsegs W m m' _ _ B1 MU); rewrite farun_len; exact A4|].
  split; [apply (bytes_at_transport bsegs W m m' _ _ B2 MU); destruct (s_quar s); [exact A5 | rewrite ushadowA_len; exact A5]|].
  apply (bytes_at_transport bsegs W m m' _ _ B3 MU). rewrite farun_len. exact A6.
Qed.

Lemma dsj1 : forall V a n, dsjb V a n = true -> disjoint_from V a n.
Proof. intros V a n H. exact (proj1 (Forall_forall _ _) (dsjb_all' V [(a, n)] ltac:(cbn; rewrite H; reflexivity)) (a, n) (or_introl eq_refl)). Qed.

Section DsArt.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (k : nat) (s lst : secst) (TZ : list ivl) (zlo zhi : Z) (ws : list word).
Hypothesis HG : geo_ok Σ.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hlst : nth_error (sec Σ) (length (sec Σ) - 1) = Some lst.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis HTZd : disjoint_from TZ (l_T (lay Σ)) 0x50 /\ disjoint_from TZ (l_T (lay Σ) + 48) 16 /\ disjoint_from TZ (l_T (lay Σ) + 0xc60) 1
  /\ (forall c', 1 <= c' <= 31 -> disjoint_from TZ (pc_addr (l_T (lay Σ)) c') 80) /\ disjoint_from TZ (qcacheT (l_T (lay Σ))) 32.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW : Forall (dzoneP Σ [] [] [k; (length (sec Σ) - 1)%nat] TZ IZ_S [] zlo zhi) W.
Hypothesis HA : ARTc Σ m.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation NS := (length (sec Σ)).

Lemma da_HD : forall c i, In (c, i) ([] : list (Z * nat)) -> 1 <= c <= 31 /\ exists st, nth_error (r_st (pr Σ c)) i = Some st.
Proof. intros c i []. Qed.
Lemma da_HDC : forall c, In c ([] : list Z) -> 1 <= c <= 31.
Proof. intros c []. Qed.

Lemma da_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ_S a n -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_img Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_Tz Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 3 \/ j = 4 \/ j = 5 \/ j = 8)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dp_grant_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma da_grant67 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dp_grant_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma da_ris : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> rinfo (RIS_of SB) c' <= a -> a + n <= rinfo (RIS_of SB) c' + 120 -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_ris_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_fa : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> fa SB c' <= a -> a + n <= fa SB c' + kFaCap -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_fa_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') [] ->
  p_abeg SB c' i' <= a -> a + n <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_slot_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_shad_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') [] ->
  shad (p_abeg SB c' i') <= a -> a + n <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_shad_slot_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_shad_reg : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + n <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_shad_reg_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k0 s0, nth_error (sec Σ) k0 = Some s0 -> In k0 [k; (NS - 1)%nat] -> hi <= s_mb s0 \/ s_mb s0 + smsz (s_n s0) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_shad_app_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> ~ In k0 [k; (NS - 1)%nat] -> s_mb s0 <= a ->
  a + n <= s_mb s0 + smsz (s_n s0) -> disjoint_from W a n.
Proof using HG HTZ Hzlo HW. exact (dp_secmap_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo W HW). Qed.
Lemma da_stack : forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof using HG HTZ Hzlo Hzlh HW. exact (dp_stack_hw Σ [] [] _ TZ IZ_S [] zlo zhi HG da_HD da_HD da_HDC IZ_S_in HTZ Hzlo Hzlh W HW). Qed.

Lemma da_consts : consts_rep L m'.
Proof using HG HTZ HTZd Hzlo HW HA MU WM.
  destruct HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  apply (consts_rep_frame L m m' (proj1 HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply da_Tz; [lia | lia | exact Z3].
  + apply (kw_consts Σ W TZ IZ_S da_img da_Tz da_grant); [apply dsjb_all; vm_compute; reflexivity | exact Z1 | exact Ha | exact NE].
Qed.

Theorem ds_artc :
  sec_core m' (l_PAB L) (sec_nres Σ) (Z.of_nat NS - 1) -> sec_pad m' -> sec_junk m' ->
  u64arr bsegs m' (l_PAB L) (upd ws k (Z_to_bv 64 (s_mb lst))) -> Z.of_nat (length ws) = sec_nres Σ ->
  firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σ) ->
  ((k < NS - 1)%nat -> schunk_avoid_nh W lst /\ rw_cells bsegs m' (s_mb lst + 24) [C8 (Z_to_bv 64 (Z.of_nat k))]) ->
  ARTc (recs Σ k) m'.
Proof using HG Hk Hlst HTZ HTZd Hzlo HW HA Hdep HQB MU WM.
  intros HSC HSP HSJ HWS HWl HWf HLST. pose proof HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof da_consts as HC'.
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kw_reg Σ W [] HG da_ris da_fa da_shad_reg) as KR.
  pose proof (kw_pchunk Σ W [] HG da_slot da_shad_slot) as KP.
  pose proof (kw_schunk Σ W [k; (NS - 1)%nat] HG da_shad_app da_secmap) as KS.
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  pose proof HG as (_ & _ & HSW & _). pose proof HSW as (SW1 & SW2 & SW3 & _).
  assert (Hnres : sec_nres Σ = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
  apply ARTc_intro.
  - exact HC'.
  - intros c' Hc'. exact (reg_rep_transport W _ c' _ m m' (A2 c' Hc') MU WM (KR c' Hc' (fun X => X))).
  - intros c' Hc'. exact (pclass_rep_transport W _ c' _ _ m m' (A3 c' Hc') MU WM (kw_pclass Σ W TZ da_Tz c' Hc' (Z4 c' Hc'))).
  - destruct A4 as [P Sc]. split.
    + intros c' i' st0 Hc' Hn'. exact (pchunk_transport W _ c' i' st0 m m' (P c' i' st0 Hc' Hn') MU WM (KP c' i' st0 Hc' Hn' (fun X => X))).
    + intros j' t Hj'. cbn [recs set_sec sec] in Hj'. destruct (swap_remove_nth k (sec Σ) j' t Hkl Hj') as (Nt & Hlt).
      destruct (Nat.eqb_spec j' k) as [->|Hne].
      * rewrite Hlst in Nt. injection Nt as <-. destruct (HLST Hlt) as (AV & HI).
        exact (schunk_transport_nh W _ k lst m m' (Sc _ lst Hlst) MU WM AV HI).
      * exact (schunk_transport W j' t m m' (Sc j' t Nt) MU WM (KS j' t Nt ltac:(intros [E|[E|[]]]; [exact (Hne (eq_sym E)) | lia]))).
  - pose proof A5 as (_ & _ & _ & SPG & SRG & _ & NMC).
    unfold sec_rep. cbn [recs set_sec sec sec_nres lay].
    rewrite (swap_remove_length k (sec Σ) Hkl).
    split; [rewrite Nat2Z.inj_sub by lia; exact HSC|]. split; [exact HSP|].
    split.
    { exists (upd ws k (Z_to_bv 64 (s_mb lst))). split; [exact HWS|]. split; [rewrite upd_length; exact HWl|].
      apply (ds_upd_prefix (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σ) ws k lst HWf); [|exact Hkl | exact Hlst].
      rewrite Hnres in HWl. clear - HWl SW1. unfold SEC_MAX in *. lia. }
    unfold sec_page, sec_range, name_cells in *. destruct NMC as (NM1 & NM2).
    split; [apply (rw_cells_transport bsegs W m m' _ _ SPG MU WM); cbn [cells_size csize Nat.add Z.of_nat];
            apply da_img; [unfold i_sec_page, INST, g_instance; lia | unfold i_sec_page, INST, g_instance, SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity]|].
    split; [apply (rw_cells_transport bsegs W m m' _ _ SRG MU WM); cbn [cells_size csize Nat.add Z.of_nat];
            apply da_img; [unfold i_sec_range, INST, g_instance; lia | unfold i_sec_range, INST, g_instance, SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity]|].
    split; [exact HSJ|].
    split; [apply (rw_cells_transport bsegs W m m' _ _ NM1 MU WM); cbn [cells_size csize Nat.add Z.of_nat];
            apply da_img; [lia | unfold SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity]|].
    apply (rw_cells_transport bsegs W m m' _ _ NM2 MU WM); cbn [cells_size csize Nat.add Z.of_nat];
      apply da_img; [lia | unfold SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity].
  - exact (quar_rep_transport W Σ m m' A6 MU WM
             (kw_quar Σ W [] TZ IZ_S HG da_img da_Tz da_slot Z5 ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' []) HQB)).
  - exact (dep_rep_transport W _ _ m m' A7 Hdep MU WM (kw_dep Σ W IZ_S da_img ltac:(apply dsjb_all'; vm_compute; reflexivity) da_grant67)).
  - exact (fs_rep_transport W Σ m m' A8 MU WM (kw_fs Σ W [k; (NS - 1)%nat] TZ IZ_S HG da_img da_Tz da_grant da_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) Z2)).
  - exact (ia_rep_transport W Σ m m' A9 MU WM (kw_ia W IZ_S da_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' A10 MU WM (kw_shadow Σ W [k; (NS - 1)%nat] HG da_shad_app)).
  - exact (vis_rep_wmono _ m m' A11 WM).
Qed.

End DsArt.

Lemma outside_Forall : forall W x, outside W x <-> Forall (fun iv => ~ (fst iv <= x < snd iv)) W.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; split; intros H.
  - constructor. - exact I.
  - destruct H as (H1 & H2). constructor; [exact H1 | apply IH; exact H2].
  - inversion H as [|? ? H1 H2]; subst. split; [exact H1 | apply IH; exact H2].
Qed.
Lemma outside_perm : forall W W' x, Permutation W W' -> outside W x -> outside W' x.
Proof. intros W W' x HP H. apply outside_Forall. apply (Permutation_Forall HP). apply outside_Forall. exact H. Qed.
Lemma munch_perm : forall W W' (m m' : mem), Permutation W W' -> munch W m m' -> munch W' m m'.
Proof. intros W W' m m' HP MU x Hx. apply MU. exact (outside_perm W' W _ (Permutation_sym HP) Hx). Qed.

Lemma dzoneP_mono_DS : forall Σ D DSH DS DS' TZ IZ DC zlo zhi W, (forall x, In x DS -> In x DS') ->
  Forall (dzoneP Σ D DSH DS TZ IZ DC zlo zhi) W -> Forall (dzoneP Σ D DSH DS' TZ IZ DC zlo zhi) W.
Proof.
  intros Σ D DSH DS DS' TZ IZ DC zlo zhi W HI HW. eapply Forall_impl; [|exact HW]. intros iv Hz.
  destruct Hz as [X|[X|[X|[X|[X|[X|[X|[(k0 & s0 & Hk0 & X)|[(k0 & s0 & Hk0 & X)|[X|X]]]]]]]]]].
  - left; exact X. - right; left; exact X. - do 2 right; left; exact X. - do 3 right; left; exact X.
  - do 4 right; left; exact X. - do 5 right; left; exact X. - do 6 right; left; exact X.
  - do 7 right; left. exists k0, s0. split; [exact (HI k0 Hk0) | exact X].
  - do 8 right; left. exists k0, s0. split; [exact (HI k0 Hk0) | exact X].
  - do 9 right; left; exact X. - do 10 right; exact X.
Qed.

Section DsCli.
Variables (Σ : rtsA) (W0 : list ivl) (k : nat) (s lst : secst) (TZ : list ivl) (zlo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis Hlst : In lst (sec Σ).
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW0 : Forall (dzoneP Σ [] [] [k] TZ IZ_S [] zlo zhi) W0.
Hypothesis Hlive : live_wf Σ.
#[local] Notation L := (lay Σ).

Lemma ds_client : forall x, aclient (live Σ) (frames Σ) zhi x -> outside (W0 ++ [(s_mb lst + 24, s_mb lst + 32)]) x.
Proof using HG Hk Hq Hlst HTZ Hzlo Hzlh HW0 Hlive.
  intros x Hx. apply outside_app; [|cbn [outside]; split; [|exact I]].
  - pose proof (dp_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    destruct Hx as [H|[H|[H|[H|H]]]].
    + apply (disjoint_outside W0 x 1); [|lia].
      apply (dp_stack_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo Hzlh W0 HW0); lia.
    + destruct H as ((lo0 & hi0 & Hin & Hlh) & Hnrt).
      assert (Hx : 0x184450 <= x < 0x186318 \/ 0x6abfd0 <= x < 0x6bbfd0 \/ 0x6bbfd0 <= x < 0x6dfdd8).
      { unfold CLIENT_STATIC in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply (disjoint_outside W0 x 1); [|lia].
      apply (dp_img Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0);
        [lia | unfold SEGTOP_A; lia|].
      unfold IZ_S, i_sec_mutex, i_sec_nres, i_sec_sorted, i_gstat_alloc, INST, g_instance. cbn [disjoint_from].
      repeat split; try exact I; lia.
    + destruct H as (p & n & Hin & Hpx). apply (disjoint_outside W0 p n); [|lia].
      destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c & i & Hc & Hn & ->)|(t & Ht & Htq & Htn & ->)].
      * pose proof (dp_slot_in Σ HG c i _ Hc Hn) as (S1 & S2 & S3 & S4 & S5 & S6).
        assert (Hfit : rz_size n + n <= ClassSize c /\ 0 <= n).
        { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
          pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
          pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
        pose proof (fl_rz_facts n) as (R1 & R2).
        apply (dp_slot_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 c i (CkAlloc n));
          [exact Hc | exact Hn | intros [] | unfold p_ubeg; lia | unfold p_ubeg; lia].
      * destruct (In_nth_error _ _ Ht) as (kt & Hkt).
        pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
        pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
        apply (dp_secmap_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 kt t);
          [exact Hkt | | unfold s_ubeg; lia | unfold s_ubeg; rewrite <- Htn; lia].
        intros [E|[]]. subst kt. rewrite Hk in Hkt. injection Hkt as <-. rewrite Hq in Htq. discriminate.
    + destruct H as (f & k0 & Hin & Hfx). apply (disjoint_outside W0 f (fs_size k0 - 8)); [|lia].
      destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
      apply (dp_grant_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 5 (l_FSB L) 0xb09000);
        [reflexivity | lia | lia | lia].
    + destruct H as (f & k0 & Hin & Hfx). apply (disjoint_outside W0 (shad f) (shad (f + fs_size k0) - shad f)); [|lia].
      destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
      pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
      pose proof (g_apart Σ HG 0 5 _ _ ltac:(lia) eq_refl eq_refl) as A05. cbn [fst snd] in A05. unfold apart in A05.
      apply (dp_shad_app_hw Σ [] [] [k] TZ IZ_S [] zlo zhi HG (da_HD Σ) (da_HD Σ) da_HDC IZ_S_in HTZ Hzlo W0 HW0 f (f + fs_size k0));
        [lia | lia | lia | | lia | lia].
      intros k' s' Hk' _. pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
      pose proof (proj1 (Forall_forall _ _) SW4 s' (nth_error_In _ _ Hk')) as (_ & _ & _ & X & _). unfold apart in X. lia.
  -
    pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
    pose proof (proj1 (Forall_forall _ _) SW4 lst Hlst) as ((Ln1 & _) & (LG1 & _ & LG3 & LG4 & LG5) & LGP & LGF & _).
    pose proof (smsz_big (s_n lst) ltac:(lia)) as Lbig. unfold apart in LGP, LGF.
    pose proof (dp_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    destruct Hx as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
    + clear - Hs Hzlo Hzlh LG3 Lbig Ln1. lia.
    + destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hx LG5 Lbig Ln1; unfold SEGTOP_A in *; lia.
    + destruct Hl as (p & n & Hin & Hx). destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Htq & Htn & Ep)].
      * pose proof (dp_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
        assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
        { pose proof HG as (_ & HR & _). destruct HR as (HR & _).
          pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
          pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
        pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx. clear - Hx S1 S2 G7 LGP Hfit R1 R2 Lbig Ln1. lia.
      * subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
        destruct (Z.eq_dec (s_mb t) (s_mb lst)) as [E|NE]; [clear - Hx E; lia|].
        destruct (In_nth_error _ _ Ht) as (jt & Hjt). destruct (In_nth_error _ _ Hlst) as (jl & Hjl).
        assert (Hne : jt <> jl) by (intros ->; rewrite Hjl in Hjt; injection Hjt as ->; exact (NE eq_refl)).
        pose proof (SW5 jt jl t lst Hjt Hjl Hne) as A. unfold apart in A.
        pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
        clear - Hx A Lbig Tbig Ln1 Tn1. lia.
    + destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3). clear - Hx Y1 Y2 Y3 LGF Lbig Ln1. lia.
    + destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
      pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
      pose proof (dp_shad_rng f ltac:(lia)) as X1. pose proof (dp_shad_rng (f + fs_size k0) ltac:(lia)) as X2.
      clear - Hx X1 X2 LG4 Lbig Ln1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

End DsCli.

End GWIN.

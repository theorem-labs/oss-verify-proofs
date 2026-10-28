(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qdorec R_qcbrec RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art2 RT_drain_geo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition W_QCB (AB M n T C : Z) : list ivl :=
  [(AB, AB + 8); (M, M + 4); (shad (M + 16), shad (M + 16) + ru8 n / 8); (T + 2840, T + 2856); (C - 224, C - 112)].
Definition TZ_ST (T : Z) : list ivl := [(T + 2768, T + 3168)].

Lemma wr_at_stk : forall (m : mem) a n, wr_at bsegs m a n -> img_hull_hi <= a -> a + n <= 2 ^ 64 -> stk bsegs m a (a + n).
Proof.
  intros m a n (Ha & Hn & H) Hi Hb. split; [lia|]. split; [lia|]. intros x Hx.
  pose proof (H (x - a) ltac:(lia)) as X. replace (a + (x - a)) with x in X by lia. split; [exact X|].
  unfold mrd. unfold wview in X. destruct (m (wa x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply X. rewrite find_segment_above; [reflexivity| rewrite wa_unsigned by lia; lia|].
  rewrite wa_unsigned by lia. apply (forallb_mono_top bsegs img_hull_hi); [lia | exact asegs_top].
Qed.

Lemma stk_within : forall (m : mem) lo hi a b, stk bsegs m lo hi -> lo <= a -> b <= hi -> 0 <= a -> stk bsegs m a b.
Proof. intros m lo hi a b (H1 & H2 & H) Ha Hb Ha0. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

Lemma dq_farun_add : forall a b, 0 <= a -> 0 <= b -> farun (a + b) = farun a ++ farun b.
Proof. intros a b Ha Hb. unfold farun. rewrite Z2Nat.inj_add by lia. apply repeat_app. Qed.

Lemma qp_wdisj : forall AB M n T C lo ACEIL x k,
  SHB <= x -> 0 <= k -> x + k <= 2 ^ 44 + SHB -> 2 ^ 44 + SHB <= AB -> AB <= M ->
  (T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) -> 2 ^ 44 + SHB <= ACEIL -> ACEIL <= lo -> lo <= C - 224 ->
  (x + k <= shad (M + 16) \/ shad (M + 16) + ru8 n / 8 <= x) ->
  disjoint_from (W_QCB AB M n T C) x k.
Proof.
  intros AB M n T C lo ACEIL x k H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. unfold W_QCB. cbn [disjoint_from].
  repeat split; unfold SHB in *; lia.
Qed.

Section QCBP.
Variables (Σ : rtsA) (m : mem) (C lo c : Z) (i : nat) (n : Z)
  (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HG : geo_ok Σ.
Hypothesis HA : ARTc Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some (CkQuar n).
Hypothesis CBP : rw_cells bsegs m (C - 104) [C8 (Z_to_bv 64 (l_T (lay Σ) + 208))].
Hypothesis ST : stk bsegs m lo (C - 112).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= C - 112.
Hypothesis HC47 : C + 32 <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation S := (ClassSize c).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).

Lemma qp_fit : 1 <= c <= 30 /\ 1 <= n /\ rz_size n + ru8 n <= S /\ 16 <= rz_size n /\ rz_size n mod 16 = 0 /\ n <= ru8 n
  /\ ru8 n mod 8 = 0 /\ 32 <= S /\ S mod 32 = 0 /\ S <= 65536 /\ (Z.of_nat i + 1) * S <= r_muser (pr Σ c) <= kUserCap.
Proof using HG Hc Hi.
  clear - HG Hc Hi. destruct HG as (_ & (HR & _) & _). pose proof (HR c Hc) as (W1 & _ & W3 & _ & _ & _ & _ & _ & _ & W10 & W11).
  pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi)) as (Hn1 & Hfit & Hcid). cbv beta iota in Hn1, Hfit, Hcid.
  pose proof (fl_rz_facts n) as (R1 & R2). pose proof (fl_slot_room c n Hc ltac:(lia) Hfit) as (R3 & R4).
  pose proof (ClassSize_range c Hc) as ((S1 & S2) & S3).
  assert (Hlt : (i < length (r_st (pr Σ c)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert ((Z.of_nat i + 1) * S <= Z.of_nat (length (r_st (pr Σ c))) * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hru : n <= ru8 n /\ ru8 n mod 8 = 0).
  { unfold ru8. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
    split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }

  assert (Hneed : 1 <= needed n <= 65536).
  { unfold needed, rounded. rewrite (Z.max_l n 1) by lia. destruct (Z_le_gt_dec 8 n) as [H8|H8].
    - rewrite Z.max_l by lia. change (8 * ((n + 7) / 8)) with (ru8 n). lia.
    - rewrite Z.max_r by lia. change (8 * ((8 + 7) / 8)) with 8. lia. }
  pose proof (ClassID_props (needed n) Hneed) as (K1 & _). rewrite <- Hcid in K1.
  unfold kUserCap in *. repeat split; try lia.
Qed.

Definition qcb_ms : machine_state :=
  MS (mkR (Z_to_bv 64 0x61120) (Z_to_bv 64 (C - 112)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 (C - 104)) (Z_to_bv 64 M)
          a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 qcbrec_entry) fc None m (seg_rom bsegs).

Definition qcb_out : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
    ms = MS (mkR (Z_to_bv 64 0x61120) (Z_to_bv 64 (C - 112)) gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 (Z_to_bv 64 (T + 208))
                 (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 AB) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 cdealloc_entry) fc None m1 (seg_rom bsegs)
    /\ ARTc (set_st Σ c i CkIdle) m1 /\ munch (W_QCB AB M n T C) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
    /\ stk bsegs m1 lo (C - 112) /\ rt_pres (live Σ) (frames Σ) (C - 112) m m1.

Lemma qp_slot : l_PRB L <= AB /\ AB + S <= SB + 2 ^ 37 /\ SEGTOP_A <= l_PRB L /\ AB mod 16 = 0 /\ 0 <= AB
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ SB + 2 ^ 37 + 4096 <= l_ACEIL L.
Proof using HG Hc Hi.
  clear - HG Hc Hi. pose proof (dk_slot_in Σ HG c i _ Hc Hi) as (S1 & S2 & _).
  pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  pose proof (ClassSize_range c Hc) as (_ & Hm).
  assert (AB mod 16 = 0).
  { unfold p_abeg. apply Z.mod_divide in P3; [|lia]. apply Z.mod_divide in Hm; [|lia]. destruct P3 as (q1 & E1). destruct Hm as (q2 & E2).
    rewrite E1. replace (q1 * 2 ^ 16 + c * 2 ^ 32 + Z.of_nat i * ClassSize c) with ((q1 * 4096 + c * 2 ^ 28 + Z.of_nat i * q2 * 2) * 16) by (rewrite E2; ring).
    apply Z.mod_mul. lia. }
  repeat split; lia.
Qed.

Theorem qcbp_evt : evt bsegs qcb_out qcb_ms.
Proof using HG HA Hc Hi CBP ST HLO HLO2 HC47 MI Hlive Hdep HQB.
  pose proof qp_fit as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  pose proof qp_slot as (P1 & P2 & P3 & P4 & P5 & G1 & G2 & G3). unfold SHB in G1.
  pose proof (dg_ok Σ HG) as (HT & HSB & TSEP).
  pose proof HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (dg_consts L m A1) as (IC & MMG & TC & PS & STS & UB). destruct IC as (IC1 & IC2).

  pose proof (A2 c Hc) as (RL & RC & RT & RF & RS1 & RB & RS2).
  unfold ri_core in RC.
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 (Z.of_nat (length (r_fl (pr Σ c))))); C8 (Z_to_bv 64 (r_mfa (pr Σ c)));
                                    C8 (Z_to_bv 64 (ClassSize c * Z.of_nat (length (r_st (pr Σ c))))); C8 (Z_to_bv 64 0)]
                                   [C8 (Z_to_bv 64 (r_muser (pr Σ c))); C8 (Z_to_bv 64 0)])) in RC.
  destruct RC as (_ & RC). apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 (r_muser (pr Σ c)))] [C8 (Z_to_bv 64 0)])) in RC.
  destruct RC as (RMU & _). cbn [cells_size csize Nat.add Z.of_nat] in RMU. unfold rinfo, RIS_of in RMU.

  pose proof (proj1 A4 c i (CkQuar n) Hc Hi) as (WR & (b1 & ctx & fid & Hb1 & QH) & LC & SH).
  apply (proj1 (rwc_app bsegs m _ [C1 (Z_to_bv 8 3); C1 b1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] [C8 ctx; C8 fid])) in QH.
  destruct QH as (QH & _).

  assert (Hsh : shad (M + 16) = shad AB + rz_size n / 8).
  { replace (M + 16) with (AB + rz_size n) by lia. apply shad_add8'; [apply (mod8_of _ 16 ltac:(lia) P4); exists 2; reflexivity |].
    apply (mod8_of _ 16 ltac:(lia) F5). exists 2; reflexivity. }
  pose proof (dk_slot_in Σ HG c i _ Hc Hi) as (_ & _ & Q3 & Q4 & Q5 & Q6).
  assert (Hsh2 : shad (M + 16) + ru8 n / 8 <= shad (AB + S)).
  { rewrite Hsh. pose proof (fk_shad_le AB (rz_size n) (ru8 n) P5 ltac:(lia) ltac:(lia)) as X.
    pose proof (fk_shad_mono (AB + rz_size n + ru8 n) (AB + S) ltac:(lia)). lia. }
  assert (STsh : stk bsegs m (shad (M + 16)) (shad (M + 16) + ru8 n / 8)).
  { apply (stk_within m _ _ _ _ RS2).
    - rewrite Hsh. pose proof (fk_shad_mono (rb SB c) AB Q3). pose proof (Z.div_pos (rz_size n) 8 ltac:(lia) ltac:(lia)). lia.
    - pose proof (fk_shad_mono (AB + S) (rb SB c + 2 ^ 32) ltac:(unfold kUserCap in *; lia)). lia.
    - rewrite Hsh. unfold shad, SHB. pose proof (Z.div_pos AB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (rz_size n) 8 ltac:(lia) ltac:(lia)). lia. }
  destruct (stk_CB m (shad (M + 16)) (ru8 n / 8) STsh ltac:(apply Z.div_pos; lia)) as (shj & SHJ).

  destruct (fl_two_c8 m (T + 2840) ltac:(apply (stk_within m _ _ _ _ STS); [lia | lia | pose proof HT as (X & _); lia])) as (rfw & rfdw & STW).
  rewrite <- (Z_to_bv_bv_unsigned rfw), <- (Z_to_bv_bv_unsigned rfdw) in STW.
  assert (Hd : rz_size n - 16 = 0 \/ 16 <= rz_size n - 16).
  { apply Z.mod_divide in F5; [|lia]. destruct F5 as (q & Eq). lia. }
  assert (Hb1r : 0 <= bv_unsigned b1 < 256) by (pose proof (bv_unsigned_in_range 8 b1) as X; unfold bv_modulus in X; cbn in X; lia).
  assert (EM : M = l_SB L + c * 2 ^ 32 + Z.of_nat i * ClassSize c + (rz_size n - 16)) by (unfold p_abeg; lia).
  assert (EAB : AB = l_SB L + c * 2 ^ 32 + Z.of_nat i * ClassSize c) by reflexivity.
  rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b1) in QH. rewrite EM in QH.
  rewrite EM, EAB in LC. rewrite EM in SHJ.
  replace (rinfo (RIS_of (l_SB L)) c + 16 + 32) with (l_SB L + 2 ^ 37 + 128 * c + 48) in RMU by (unfold rinfo, RIS_of; lia).
  unfold qcb_ms. rewrite EM.
  eapply evt_mono; [apply (qcbrec_prim_spec (Z_to_bv 64 0x61120) (Z_to_bv 64 (C - 112)) gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (l_ACEIL L) (l_SB L) c (Z.of_nat i) (rz_size n - 16)
                             (r_muser (pr Σ c)) n (bv_unsigned b1) (l_TCX L) T (bv_unsigned rfw) (bv_unsigned rfdw) (T + 208) (C - 104) lo shj);
                    rewrite ?unsigned_lit by lia|].
  1: lia. 1: lia. 1: exact Hd. 1: lia. 1: unfold kUserCap in F12; lia. 1: exact IC1. 1: exact RMU. 1: exact HSB.
  1: { rewrite <- EAB. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact P4]|].
       apply Z.divide_sub_r; [apply Z.mod_divide; [lia | exact F5] | exists 1; reflexivity]. }
  1: lia. 1: exact Hb1r. 1: exact QH. 1: intros Hd0; apply LC; lia. 1: exact SHJ. 1: exact PS. 1: exact TC. 1: exact TSEP.
  1: exact STW. 1: exact CBP. 1: pose proof HT as (X1 & _ & X3 & X4 & _); lia. 1: lia. 1: lia. 1: exact ST. 1: lia. 1: exact HLO. 1: lia. 1: lia.
  1: exact MI.
  intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ((QA1 & QA2 & QA3) & LCH') & ST1).
  rewrite unsigned_lit in MU1, ST1 by lia.
  assert (MU : munch (W_QCB AB M n T C) m m1).
  { eapply munch_weaken; [|exact MU1]. unfold W_QCB, qcbrec_prim_W, qcb_W. rewrite <- EAB, <- EM. replace (C - 112 - 112) with (C - 224) by lia.
    intros x Hx. exact Hx. }
  clear MU1.
  exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m1. split; [reflexivity|].

  assert (Hm8 : 8 <= ru8 n) by (unfold ru8; assert (1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia); lia).
  pose proof (Z.div_pos (rz_size n) 8 ltac:(lia) ltac:(lia)) as Hrz8.
  assert (CERT : Forall (dzone Σ [(c, i)] [(c, i)] [] (TZ_ST T) [] [] lo (C - 112)) (W_QCB AB M n T C)).
  { unfold W_QCB. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    - right; right; left. exists c, i. split; [left; reflexivity|]. cbn [fst snd]. lia.
    - right; right; left. exists c, i. split; [left; reflexivity|]. cbn [fst snd]. lia.
    - right; right; right; left. exists c, i. split; [left; reflexivity|]. cbn [fst snd]. split; lia.
    - right; left. exists (T + 2768, T + 3168). split; [left; reflexivity | cbn; lia].
    - do 9 right. cbn. lia. }
  assert (HTZ : Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_ST T)) by (unfold TZ_ST; repeat constructor; cbn; lia).
  assert (HTZd : disjoint_from (TZ_ST T) T 0x50 /\ disjoint_from (TZ_ST T) (T + 48) 16 /\ disjoint_from (TZ_ST T) (T + 0xc60) 1
            /\ (forall c', 1 <= c' <= 31 -> disjoint_from (TZ_ST T) (pc_addr T c') 80) /\ disjoint_from (TZ_ST T) (qcacheT T) 32).
  { unfold TZ_ST, pc_addr, qcacheT. cbn [disjoint_from]. split; [split; [lia | exact I]|]. split; [split; [lia | exact I]|].
    split; [split; [lia | exact I]|]. split; [intros c' Hc'; split; [lia | exact I] | split; [lia | exact I]]. }

  assert (HCH : pchunk (ann Σ) SB c i CkIdle m1).
  { unfold pchunk. split; [apply wr_at_stk; [exact (wr_at_wmono m m1 _ _ WR WM1) | unfold img_hull_hi, SEGTOP_A in *; lia | lia]|].
    unfold pshadow_idle. unfold pshadow_quar in SH.
    assert (HR8 : rz_size n mod 8 = 0) by (apply (mod8_of _ 16 ltac:(lia) F5); exists 2; reflexivity).
    assert (HS8 : ClassSize c mod 8 = 0) by (apply (mod8_of _ 32 ltac:(lia) F9); exists 4; reflexivity).
    pose proof (Z.div_mod (rz_size n) 8 ltac:(lia)) as DR. pose proof (Z.div_mod (ru8 n) 8 ltac:(lia)) as DU.
    pose proof (Z.div_mod (ClassSize c) 8 ltac:(lia)) as DS.
    assert (E3 : (ClassSize c - rz_size n - ru8 n) / 8 = ClassSize c / 8 - rz_size n / 8 - ru8 n / 8).
    { clear - DR DU DS HR8 F7 HS8.
      replace (ClassSize c - rz_size n - ru8 n) with ((ClassSize c / 8 - rz_size n / 8 - ru8 n / 8) * 8) by lia. apply Z.div_mul. lia. }
    assert (K8 : 0 <= rz_size n / 8 /\ 0 <= ru8 n / 8 /\ 0 <= (ClassSize c - rz_size n - ru8 n) / 8
                 /\ rz_size n / 8 + ru8 n / 8 + (ClassSize c - rz_size n - ru8 n) / 8 = ClassSize c / 8).
    { clear - DR DU DS HR8 F7 HS8 E3 F3 F4 Hm8. rewrite E3. lia. }
    destruct K8 as (K1 & K2 & K3 & K4).
    pose proof (shad_len AB S ltac:(lia) ltac:(lia) ltac:(lia)) as (SL1 & SL2).
    assert (KAB : 2 ^ 44 + SHB <= AB).
    { clear - HSB EAB Hc. destruct HSB as (X1 & _).
      pose proof (Z.mul_nonneg_nonneg (Z.of_nat i) (ClassSize c) (Nat2Z.is_nonneg i)
        ltac:(pose proof (ClassSize_range c Hc) as ((? & ?) & ?); lia)). unfold kHighShadowEnd, SHB in *. lia. }
    assert (KT : T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T).
    { clear - TSEP. destruct TSEP as (_ & _ & _ & _ & _ & _ & _ & X & _). unfold kHighShadowEnd, SHB in *. lia. }
    assert (KC : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= lo /\ lo <= C - 224 /\ AB <= M).
    { clear - G1 HLO HLO2 F4. unfold SHB. lia. }
    destruct KC as (KC1 & KC2 & KC3 & KC4).
    apply (proj1 (bytes_at_app bsegs m _ _ _)) in SH. destruct SH as (SH1 & SH2).
    apply (proj1 (bytes_at_app bsegs m _ _ _)) in SH2. destruct SH2 as (_ & SH3).
    rewrite farun_lenZ, fdrun_lenZ in SH3 by assumption.
    assert (SH1' : bytes_at bsegs m1 (shad AB) (farun (rz_size n / 8))).
    { apply (bytes_at_transport bsegs (W_QCB AB M n T C) m m1 _ _ SH1 MU). rewrite farun_lenZ by assumption.
      apply (qp_wdisj AB M n T C lo (l_ACEIL L)); try assumption.
      - clear - SL2 K1 K2 K3 K4. lia.
      - left. rewrite Hsh. lia. }
    assert (SH3' : bytes_at bsegs m1 (shad AB + rz_size n / 8 + ru8 n / 8) (farun ((ClassSize c - rz_size n - ru8 n) / 8))).
    { apply (bytes_at_transport bsegs (W_QCB AB M n T C) m m1 _ _ SH3 MU). rewrite farun_lenZ by assumption.
      apply (qp_wdisj AB M n T C lo (l_ACEIL L)); try assumption.
      - clear - SL1 K1 K2. lia.
      - clear - SL2 K1 K2 K3 K4. lia.
      - right. rewrite Hsh. lia. }
    assert (SHU : bytes_at bsegs m1 (shad AB + rz_size n / 8) (farun (ru8 n / 8))).
    { destruct QA2 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      replace (shad AB + rz_size n / 8) with (shad (l_SB L + c * 2 ^ 32 + Z.of_nat i * ClassSize c + (rz_size n - 16) + 16)); [exact Hb|].
      rewrite <- EM. exact Hsh. }
    rewrite <- K4. rewrite (dq_farun_add (rz_size n / 8 + ru8 n / 8)) by (clear - K1 K2 K3; lia).
    rewrite (dq_farun_add (rz_size n / 8)) by assumption. rewrite <- app_assoc.
    apply (proj2 (bytes_at_app bsegs m1 _ _ _)). split; [exact SH1'|]. rewrite farun_lenZ by assumption.
    apply (proj2 (bytes_at_app bsegs m1 _ _ _)). split; [exact SHU|]. rewrite farun_lenZ by assumption. exact SH3'. }
  split; [exact (artc_chunk Σ m m1 (W_QCB AB M n T C) c i (CkQuar n) CkIdle (TZ_ST T) lo (C - 112) HG Hc Hi ltac:(discriminate)
                   HTZ HTZd HLO CERT HA Hdep HQB MU WM1 HCH)|].
  split; [exact MU|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
  exact (client_chunk Σ m m1 (W_QCB AB M n T C) c i (CkQuar n) (TZ_ST T) lo (C - 112) HG Hc Hi ltac:(intros n' E; discriminate E)
           HTZ HLO ltac:(lia) CERT Hlive MU).
Qed.

End QCBP.

End GWIN.

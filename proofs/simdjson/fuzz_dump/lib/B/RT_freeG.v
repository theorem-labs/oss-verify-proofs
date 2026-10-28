(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Definition enq_post (Σ2 : rtsA) (live0 : list (Z * Z)) (frames0 : list (Z * nat)) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 : word) (m' : mem),
    ms = enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
    /\ ARTc Σ2 m' /\ rt_wfx Σ2 /\ rt_count Σ2 /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (bv_unsigned sp + -2208)
    /\ rt_pres live0 frames0 (bv_unsigned sp) m m'
    /\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ2) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x805b0)
         w0 w1 w2 w3 w4 w5 s6.

Theorem app_wfx : forall (Σ : rtsA) (m : mem) c i n D' (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)), ART_A Σ m -> 1 <= c <= 31 ->
  nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) -> dep_step (dep Σ) D' ->
  ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)] -> (length ents < 1021)%nat ->
  rt_wfx (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D')
                (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])]))
  /\ rt_count (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D')
                (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])).
Proof.
  intros Σ m c i n D' pre j0 ents HA Hc Hn HDok HDinv HQL HL.
  pose proof (free_p_wf Σ m c i n D' HA Hc Hn HDok HDinv) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RC).
  pose proof (new_ent_fresh Σ m c i n HA Hc Hn) as FR.
  destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). cbn [ql qg pr lay sec free_p] in Q1, Q2, Q3, Q4, Q5, Q8.
  unfold qents in Q6, Q7, FR. cbn [ql qg free_p] in Q6, Q7. rewrite HQL in Q1, Q3, Q4, Q5, Q6, Q7, Q8, FR. rewrite qents_app in Q6, Q7, FR.
  split.
  { split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split.
  { unfold quar_wfx. cbn [set_ql ql qg pr lay free_p]. split.
    { rewrite qbytes_app_ent; cbn [snd]. pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10' & _).
      pose proof (proj1 (Forall_forall _ _) W10' _ (nth_error_In _ _ Hn)) as (X & X1 & _). cbv beta iota in X, X1. pose proof (ClassSize_range c Hc) as (X2 & _).
      pose proof (rz_facts n) as (_ & X3). clear - Q1 X X1 X2 X3. unfold QMAX_L in *. lia. }
    split; [exact Q2|].
    split; [rewrite Forall_app in Q3 |- *; destruct Q3 as [Q3a Q3b]; rewrite Forall_app in Q3a |- *; destruct Q3a as [Q3a Q3c]; split; [split; [exact Q3a|]|exact Q3b];
            inversion Q3c as [|? ? X _]; subst; constructor; [exact X | constructor]|].
    split; [rewrite !map_app in Q4 |- *; cbn [map fst] in Q4 |- *; exact Q4|].
    split; [rewrite Forall_app in Q5 |- *; destruct Q5 as [Q5a Q5b]; rewrite Forall_app in Q5a |- *; destruct Q5a as [Q5a Q5c]; split; [split; [exact Q5a|]|exact Q5b];
            constructor; [cbn [snd]; rewrite length_app; cbn [length]; lia | constructor]|].
    unfold qents. cbn [set_ql ql qg]. rewrite qents_app_snoc. split; [|split].
    - rewrite Forall_app in Q6 |- *. destruct Q6 as [Q6a Q6b]. rewrite Forall_app in Q6b. destruct Q6b as [Q6b Q6c].
      split; [exact Q6a|]. rewrite Forall_app. split; [exact Q6b|]. constructor; [|exact Q6c].
      left. exists c, i. split; [exact Hc|]. cbn [snd fst pr free_p set_ql]. destruct (Z.eqb_spec c c) as [_|X]; [|exfalso; apply X; reflexivity].
      unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck, Nat.eqb_refl.
      rewrite (proj2 (Nat.ltb_lt _ _) (proj1 (nth_error_Some _ _) ltac:(rewrite Hn; discriminate))). split; reflexivity.
    - rewrite !map_app in Q7 |- *. cbn [map fst] in Q7 |- *. rewrite !map_app in FR. rewrite app_assoc in Q7, FR |- *. apply nodup_insert; [exact Q7 | exact FR].
    - intros c' i' Hc' Hi'. destruct (Q8 c' i' Hc' Hi') as (Ec & Hin). split; [exact Ec|]. rewrite !map_app in Hin |- *. cbn [map fst] in Hin |- *. exact Hin. }
  split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. exact W11. }

  destruct RC as (RC1 & RC2). unfold qents in RC1, RC2. rewrite HQL, qents_app in RC1, RC2. split.
  - intros c' i' n' Hc' Hi'. unfold qents. cbn [set_ql ql qg lay free_p] in *. rewrite qents_app_snoc.
    destruct (fp_st Σ c i n Hc c' i' _ Hi') as [(-> & -> & E)|(Hne & Hi0)].
    + injection E as ->. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    + pose proof (RC1 c' i' n' Hc' Hi0) as X. rewrite !in_app_iff in X |- *. cbn [In]. tauto.
  - intros s Hs Hq. unfold qents. cbn [set_ql ql qg sec free_p] in *. rewrite qents_app_snoc.
    pose proof (RC2 s Hs Hq) as X. rewrite !in_app_iff in X |- *. cbn [In]. tauto.
Qed.

Section App2.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n : Z) (tr : list Z) (pre : list (Z * list (Z * Z))) (j0 : nat) (ents : list (Z * Z)) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HQL : ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some CkBatch.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis HL : (length ents < 1021)%nat.
Hypothesis Dok : depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis Dinv : dep_step (dep Σ) (fst (depot_put (dep Σ) tr)).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))).
#[local] Notation Σ2 := (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
                                (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])).

Lemma app_enq : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
    (F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
  bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv bsegs m4 -> wmono bsegs m m4 ->
  stk bsegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
  rt_pres (live_remove (p_abeg SB c i + rz_size n) (live Σ)) (frames Σ) usp m m4 ->
  icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x805b0) (Z_to_bv 64 usp)
    (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 ->
  evt bsegs (enq_post Σ2 (live_remove (p_abeg SB c i + rz_size n) (live Σ)) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR (Z_to_bv 64 0x5d53c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
             (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208))
             (Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom bsegs)).
Proof.
  intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
    Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
  pose proof (ART_wf Σ m HA) as HW0. pose proof (geo_of_wf Σ HW0) as HG.
  pose proof (se_geo Σ j0 j0 CkBatch CkBatch HG Hj0 Hj0) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  assert (Hn1 : 1 <= n <= 2 ^ 16).
  { pose proof HG as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (X & X1 & _). cbv beta iota in X, X1. pose proof (ClassSize_range c Hc) as (X2 & _).
    pose proof (rz_facts n) as (_ & X3). clear - X X1 X2 X3; lia. }
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
  pose proof (qwf_ql Σ (proj1 (proj1 (rt_wf_split Σ) HW0))) as QWF. rewrite HQL in QWF.
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & (Q1 & _) & _).
  pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT.
  rewrite HQL, <- qbytes_eq in Q1.
  eapply evt_mono.
  { apply (qenq_app_spec (Z_to_bv 64 0x5d53c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
             a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
             (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4
             (T + 80) (T + 208) (usp + -2128) M n SB lo pre b0 ents);
      try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP.
    all: try (clear - Hn1; lia).
    all: try exact ST4.
    all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
    all: try (clear - K13; lia). all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
    all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
    all: clear - Q1 Hn1; unfold QMAX_L in *; lia. }
  intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & _ & ST5).
  rewrite (unsigned_lit (usp + -2208)) in MU5, ST5 by exact RSP. rewrite (ret_pc_even 0x5d53c) by (first [reflexivity | lia]).
  assert (MWa : munch [(T + 80, T + 112); (b0, b0 + 8192); (usp - 2400, usp)] m4 m5).
  { lazymatch type of MU5 with munch ?W5 _ _ => apply (munch_weaken W5 _ m4 m5); [clear - Hsp; solve_sub_fp | exact MU5] end. }
  unfold enq_post. exists (Z_to_bv 64 0x5d53c), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2128)),
    (Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 usp), (Z_to_bv 64 (M + 16)), (Z_to_bv 64 0x80540), (Z_to_bv 64 1),
    (Z_to_bv 64 (usp + -2128)), (Z_to_bv 64 (usp + -81)), m5.
  split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
  split; [exact (app_ART Σ c i n _ pre j0 ents usp HW0 Hc Hn HQL Hj0 Hsp m4 m5 _ ART4 MWa WM5 QR5 Dok)|].
  destruct (app_wfx Σ m c i n _ pre j0 ents HA Hc Hn Dok Dinv HQL HL) as (WX & WC).
  split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM5)|].
  split; [rewrite Esp; exact ST5|].
  split.
  { rewrite Esp. intros a Ha. rewrite (MWa a); [exact (RP4 a Ha)|].
    assert (HO : outside (W_E (l_T (lay Σ)) b0 b0 usp) (bv_unsigned a)).
    { apply (kv_client Σ _ [(24, j0); (24, j0)] [] [] usp HG
               (se_img Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
               (se_slot Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
               (se_secmap Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
               ltac:(apply Forall_forall; intros; exact I) (live_remove (p_abeg SB c i + rz_size n) (live Σ))); [|exact Ha].
      intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
      pose proof HW0 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
      + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
        intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
      + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
        split; [reflexivity | intros []]. }
    revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
    split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
  split.
  { rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). cbn [disjoint_from].
    clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
  rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport bsegs _ m4 m5 _ _ FR4 MU5 WM5).
  cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End App2.

End GWIN.

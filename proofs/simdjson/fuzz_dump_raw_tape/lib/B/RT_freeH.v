(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma rw_cells_agree : forall (m m' : mem) A cs, rw_cells bsegs m A cs ->
  (forall a : word, A <= bv_unsigned a < A + Z.of_nat (cells_size cs) -> m' a = m a) -> wmono bsegs m m' -> rw_cells bsegs m' A cs.
Proof.
  intros m m' A cs H Hag WM. pose proof (rw_cells_bound bsegs m A cs H) as (B0 & B1).
  apply (rw_cells_transport bsegs [(0, A); (A + Z.of_nat (cells_size cs), 2 ^ 64)] m m' _ _ H); [| exact WM |].
  - intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
    apply Hag. lia.
  - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma u64arr_agree : forall (m m' : mem) A ws, u64arr bsegs m A ws ->
  (forall a : word, A <= bv_unsigned a < A + 8 * Z.of_nat (length ws) -> m' a = m a) -> wmono bsegs m m' -> u64arr bsegs m' A ws.
Proof.
  intros m m' A ws H Hag WM. pose proof (u64arr_bound bsegs m A ws H) as (B0 & B1).
  apply (u64arr_transport bsegs [(0, A); (A + 8 * Z.of_nat (length ws), 2 ^ 64)] m m' _ _ H); [| exact WM |].
  - intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
    apply Hag. lia.
  - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma geo_of_wfx : forall Σ, rt_wfx Σ -> geo_ok Σ.
Proof. intros Σ (H1 & H2 & _ & H4 & _ & H6 & _). exact (conj H1 (conj H2 (conj H4 H6))). Qed.

Lemma aclient_split : forall (Σ : rtsA) (live0 : list (Z * Z)) usp x, geo_ok Σ -> l_ACEIL (lay Σ) + 0x10000 <= usp ->
  (forall p n, In (p, n) live0 ->
      (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg (l_SB (lay Σ)) c i n)
      \/ (exists k s, nth_error (sec Σ) k = Some s /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s)) ->
  aclient live0 (frames Σ) usp x -> outside [(l_ACEIL (lay Σ), usp)] x.
Proof.
  intros Σ live0 usp x HG Hsp HL Hx.
  pose proof (Z.le_refl (l_ACEIL (lay Σ))) as HR.
  apply (kv_client Σ [(l_ACEIL (lay Σ), usp)] [] [] [] usp HG (sk_img Σ _ usp HG HR) (sk_grant Σ _ usp HG HR)
           (sk_slot Σ _ usp HG HR) (sk_shad_app Σ _ usp HG HR) (sk_secmap Σ _ usp HG HR)
           ltac:(intros a n H1 H2; cbn [disjoint_from]; split; [lia | exact I]) ltac:(apply Forall_forall; intros; exact I) live0); [| exact Hx].
  - intros p n Hin. destruct (HL p n Hin) as [(c & i & Hc & Hn & ->)|(k & s & Hk & Hq & Hsn & ->)]; [left | right].
    + exists c, i. split; [exact Hc|]. split; [exact Hn|]. split; [reflexivity | intros []].
    + exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|]. split; [reflexivity | intros []].
Qed.

Section Fin.
Hypothesis DRAIN : drain_stmt.

Theorem fin_from_enq : forall (Σ Σ2 : rtsA) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo p : Z) T cf,
  fdfs_only PMc -> mat_stable PMc ->
  live Σ2 = live_remove p (live Σ) -> frames Σ2 = frames Σ -> lay Σ2 = lay Σ -> credit Σ2 = credit Σ -> ann Σ2 = ann Σ ->
  l_ACEIL (lay Σ) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ2) (enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (fun mo => ARTM_A Σ2 mo /\ PMc mo) cf ->
  (forall c', free_postF RTA fc Σ PMc ra sp gp (Z_to_bv 64 0x6abde8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m c' -> realizes bsegs c' T) ->
  realizes bsegs cf T.
Proof.
  intros Σ Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p T cf FDO MST EL EF ELY EC EAN HLO HLO2 Husp Hc Hk.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ2) + 0x10000 <= usp) by (rewrite ELY; clear - HLO HLO2; lia).
  destruct (Z_le_gt_dec (RT_state.qbytes (ql Σ2)) 0x100000) as [HBY|HBY].
  -
    assert (W1 : forall ms, enq_post Σ2 (live Σ2) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms ->
      evt bsegs (fun ms' => exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                   ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
                   /\ ART_A Σ2 m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo usp
                   /\ rt_pres (live Σ2) (frames Σ) usp m m') ms).
    { intros ms P. destruct P as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
                                  & w0 & w1 & w2 & w3 & w4 & w5 & m5 & -> & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
      pose proof (geo_of_wfx Σ2 WX5) as HG2.
      eapply evt_mono; [apply (ret_tail Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
                                  t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 _ _ F fc m5 lo HG2 ART5 WX5 WC5 HBY MI5 ST5 ltac:(rewrite ELY; exact HLO)
                                  HLO2 Husp ICF5 FR5)|].
      intros ms' P'. destruct P' as (v & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m' & -> & ART' & MI' & WM' & ST' & MU').
      exists v, z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, m'. split; [reflexivity|].
      split; [exact ART'|]. split; [exact MI'|]. split; [exact (wmono_trans bsegs _ _ _ WM5 WM')|]. split; [exact ST'|].
      intros a Ha. rewrite (MU' a); [exact (RP5 a Ha)|].
      pose proof (ART_wf Σ2 m' ART') as HW2. pose proof HW2 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      pose proof (aclient_split Σ2 (live Σ2) usp (bv_unsigned a) HG2 Hsp
                    ltac:(intros p0 n0 Hin; destruct (V3 p0 n0 Hin) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|];
                          right; destruct (In_nth_error _ _ Hs) as (k & Hk'); exists k, s; split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]])
                    ltac:(rewrite EF; exact Ha)) as HO.
      cbn [outside] in HO |- *. clear - HO Hsp. split; [lia | exact I]. }
    apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W1) Hc).
    intros c1 Hc1. apply Hk. apply AST_exI in Hc1 as [v Hc1].
    exists Σ2, v. split; [|split; [(cbn [rt_live RTA]; unfold rtA_live; etransitivity; [|apply vis_live_remove]; rewrite EAN, EL; reflexivity) | split; [exact EF | split; [unfold rt_sp0, RTA, rtA_sp0; cbn; rewrite ELY; reflexivity | exact EC]]]].
    unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo H; exact H].
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & ART' & MI' & WM' & ST' & RP').
    exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
    split; [split; [exact ART' | split; [exact MI' | exact ST']]|]. exact (rt_pres_vis _ _ _ _ _ _ RP').
  -
    destruct Hc as (Hmc & HP & HPM & HZ).
    destruct HP as (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2' & s3' & s4' & s5' & t3 & t4 & t5 & t6
                    & w0 & w1 & w2 & w3 & w4 & w5 & m5 & E5 & ART5 & WX5 & WC5 & MI5 & WM5 & ST5 & RP5 & ICF5 & FR5).
    assert (Hc' : ASTA RTA Σ2 PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
                                             (Z_to_bv 64 (l_T (lay Σ2) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' (Z_to_bv 64 0x100000)
                                             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x5db88) fc None m5 (seg_rom bsegs))) cf).
    { split; [exact Hmc|]. split; [unfold enq_ret_st in E5; exact (eq_sym E5)|]. split; [exact HPM | exact HZ]. }
    apply (DRAIN Σ2 PMc ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5 lo usp
             w0 w1 w2 w3 w4 w5 s6 FDO MST ART5 WX5 WC5 ltac:(clear - HBY; lia) FR5 ST5 ltac:(rewrite ELY; exact HLO) ltac:(clear - HLO2; lia)
             ltac:(clear - Husp; unfold USTACK_TOP in *; lia) MI5 T cf Hc').
    intros c2 (Σ' & Hc2 & EL' & EF' & ELY' & EC' & EAN').
    assert (W2 : forall ms, (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
           ms = MS (mkR (Z_to_bv 64 0x80bd4) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
                        a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x80bd4) fc None m' (seg_rom bsegs)
           /\ ART_A Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2128)
           /\ rt_pres (live Σ2) (frames Σ2) (usp + -2128) m5 m') ms ->
      evt bsegs (fun ms' => exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                                   (m' : mem),
                   ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                 t3' t4' t5' t6') F' (ret_pc ra) fc None m' (seg_rom bsegs)
                   /\ ART_A Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
                   /\ rt_pres (live Σ') (frames Σ) usp m m') ms).
    { intros ms P. destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & m6 & -> & ART6 & MI6 & ST6 & RP6).
      assert (AG : forall a : word, usp - 2128 <= bv_unsigned a < usp -> m6 a = m5 a).
      { intros a Ha. apply RP6. left. clear - Ha Husp. unfold USTACK_TOP in *. lia. }
      destruct ICF5 as (FRs & (jp & FRp) & FRt & (wsb & TB & HTB) & (w & FRb)).
      pose proof (rw_cells_agree_nw bsegs m5 m6 _ _ FRs ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia)) as FRs6.
      pose proof (rw_cells_agree_nw bsegs m5 m6 _ _ FRp ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia)) as FRp6.
      pose proof (rw_cells_agree_nw bsegs m5 m6 _ _ FRt ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia)) as FRt6.
      pose proof (rw_cells_agree_nw bsegs m5 m6 _ _ FRb ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia)) as FRb6.
      pose proof (u64arr_agree_nw bsegs m5 m6 _ _ TB ltac:(intros a Ha; apply AG; rewrite HTB in Ha; cbn in Ha; lia)) as TB6.
      replace (Z_to_bv 64 (usp + -2128)) with (Z_to_bv 64 (bv_unsigned sp + -2128)) by reflexivity.
      eapply evt_mono.
      { apply (free_B_spec ra sp gp (Z_to_bv 64 tpA) y0 y1 y2 w0 w1 y3 y4 y5 y6 y7 y8 y9 y10 w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 y11 y12 y13 y14
                 (Z_to_bv 64 0x80bd4) s0 s1 s2 s3 s4 s5 F' fc m6 lo wsb w jp); try assumption.
        all: try (clear - HLO2; lia). all: try (pose proof (geo_of_ART Σ' m6 ART6) as HGx; pose proof (fk_aceil Σ' HGx) as (X1 & _);
                                               rewrite ELY', ELY in X1; clear - X1 HLO; unfold SHB in *; lia). }
      intros ms P7. destruct P7 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m7 & -> & MU7 & WM7 & MI7 & ST7).
      pose proof (ART_wf Σ' m6 ART6) as HW'. pose proof (geo_of_wf Σ' HW') as HG'.
      assert (HA' : l_ACEIL (lay Σ') <= usp - 2128) by (rewrite ELY', ELY; clear - HLO HLO2; lia).
      exists z3, z0, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, F', m7. split; [reflexivity|].
      split.
      { apply c_ART; [exact HW'|]. apply (ARTc_stack Σ' (usp - 2128) usp HG' HA' m6 m7 (ART_c _ _ ART6) MU7 WM7).
        - destruct HW' as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
        - destruct HW' as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK. }
      split; [exact MI7|]. split; [exact ST7|].
      intros a Ha. pose proof HW' as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
      assert (HO : outside [(l_ACEIL (lay Σ'), usp)] (bv_unsigned a)).
      { apply (aclient_split Σ' (live Σ') usp _ HG' ltac:(rewrite ELY', ELY; clear - HLO HLO2; lia)); [|rewrite EF', EF; exact Ha].
        intros p0 n0 Hin. destruct (V3 p0 n0 Hin) as [X|(s & Hs & Hq & Hsn & ->)]; [left; exact X|].
        right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk' | split; [exact Hq | split; [exact Hsn | reflexivity]]]. }
      rewrite (MU7 a) by (cbn [outside] in HO |- *; clear - HO HA'; split; [lia | exact I]).
      rewrite (RP6 a) by (rewrite EL' in Ha; destruct Ha as [Ha|Ha]; [left; unfold USTACK_TOP in *; lia | right; rewrite EF; exact Ha]).
      exact (RP5 a ltac:(rewrite EL' in Ha; exact Ha)). }
    apply (cps_realizes bsegs _ _ _ c2 (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W2) Hc2).
    intros c3 Hc3. apply Hk. apply AST_exI in Hc3 as [v Hc3].
    exists Σ', v. split; [|split; [(cbn [rt_live RTA]; unfold rtA_live; etransitivity; [|apply vis_live_remove]; rewrite EAN', EAN, EL', EL; reflexivity) | split; [exact (eq_trans EF' EF) | split; [unfold rt_sp0, RTA, rtA_sp0; cbn; rewrite ELY', ELY; reflexivity | exact (eq_trans EC' EC)]]]].
    unfold ASTA. eapply AST_conseq; [exact Hc3| |intros mo H; exact H].
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m' & -> & ART' & MI' & ST' & RP').
    exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F'; reflexivity|].
    split; [split; [exact ART' | split; [exact MI' | exact ST']]|]. exact (rt_pres_vis _ _ _ _ _ _ RP').
Qed.

End Fin.

Theorem rta_free_app2 : drain_stmt -> forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x6abde8 ->
  ART_A Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo -> unwind_ok ra s0 sp ->
  1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)] -> nth_error (r_st (pr Σ 24)) j0 = Some CkBatch -> (length ents < 1021)%nat ->
  cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_postF RTA fc Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
  intros DRAIN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n pre j0 ents
    FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HQL Hj0 HL.
  intros TT cf Hc0 Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
    evt bsegs (fun ms => exists tr : list Z,
      enq_post (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
                       (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])]))
               (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms) ms).
  { intros ms <-.
    eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                             ART0 MI0 CALL UWOK Hc Hn)|].
    intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
    destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
    eapply evt_mono; [apply (app_enq Σ m c i n tr pre j0 ents usp ART0 Hc Hn HQL Hj0 Hsp HL Dok Dinv
                               ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
                               eq_refl ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4)|].
    intros ms P. exists tr. exact P. }
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
  intros c1 Hc1. apply AST_exI in Hc1 as [tr Hc1].
  apply (fin_from_enq DRAIN Σ (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
                               (pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])]))
           PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (p_ubeg (l_SB (lay Σ)) c i n) TT c1 FDO MST
           eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp); [|exact Hk].
  eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP). split; [|exact HP].
  apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_fp; exact Hc | exact HM].
Qed.

End GWIN.

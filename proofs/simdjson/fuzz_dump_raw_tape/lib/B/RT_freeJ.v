(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma fl_hit_w : forall {Y} (f : Z -> Y) (l : list Z) (chs : list Y), l <> [] -> firstn (length l) chs = map f l ->
  nth_error chs (length l - 1) = Some (f (last l 0)).
Proof.
  intros Y f l. induction l as [|x l IH]; intros chs Hne H; [exfalso; exact (Hne eq_refl)|].
  destruct chs as [|y chs]; [discriminate H|]. cbn [length firstn map] in H. injection H as Hy H.
  destruct l as [|x' l]; [cbn; rewrite Hy; reflexivity|].
  pose proof (IH chs ltac:(discriminate) H) as X. replace (length (x' :: l) - 1)%nat with (length l) in X by (cbn; lia).
  change (S (S (length l)) - 1)%nat with (S (length l)). cbn [nth_error last]. exact X.
Qed.

Lemma fl_hit_addr : forall SB c j, 0 <= j -> 0 <= j * ClassSize c < 2 ^ 32 -> ClassSize c mod 16 = 0 ->
  chunk_addr SB c (cpw c j) = p_abeg SB c (Z.to_nat j).
Proof.
  intros SB c j Hj Hr Hm. unfold chunk_addr, cpw, cptr, p_abeg. rewrite Z2Nat.id by exact Hj.
  assert (Hd : 0 <= j * ClassSize c / 16 < 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite unsigned_lit by lia. rewrite Z.mod_small by lia.
  assert (E : j * ClassSize c = 16 * (j * ClassSize c / 16)).
  { apply Z.div_exact; [lia|]. rewrite Z.mul_comm. rewrite <- Zmult_mod_idemp_l. rewrite Hm. reflexivity. }
  lia.
Qed.

Lemma firstn_snoc_map : forall {Y} (f : Z -> Y) (l : list Z) x (chs : list Y), firstn (length (l ++ [x])) chs = map f (l ++ [x]) ->
  firstn (length l) chs = map f l.
Proof.
  intros Y f l x chs H. rewrite length_app in H. cbn [length] in H. rewrite map_app in H.
  assert (E : firstn (length l) (firstn (length l + 1) chs) = firstn (length l) (map f l ++ map f [x])) by (rewrite H; reflexivity).
  rewrite firstn_firstn, Nat.min_l in E by lia. rewrite firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r in E.
  assert (E2 : firstn (length l) (map f l) = map f l) by (clear; induction l as [|a l IH]; [reflexivity | cbn; f_equal; exact IH]).
  rewrite E2 in E. exact E.
Qed.

Lemma fl_nodup_app_not_in : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros A l1 l2 x H H1 H2. apply in_split in H1 as (a & b & ->). rewrite <- app_assoc in H. cbn [app] in H.
  apply (NoDup_remove_2 _ _ _ H). apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

Lemma fl_CB_of_stk : forall (m : mem) a (k : nat), stk bsegs m a (a + Z.of_nat k) -> exists bs, rw_cells bsegs m a [CB k bs].
Proof.
  intros m a k St. destruct (stk_bytes bsegs m a (a + Z.of_nat k) St ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [split|].
  - cbn. split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct St as (S0 & S1 & Sw). split; [lia|]. split; [lia|].
    intros j Hj. exact (proj1 (Sw (a + j) ltac:(lia))).
Qed.

Lemma qenq_post_weaken : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32) W W' Q bs lo (m : mem)
    (P : mem -> Prop) ms,
  sub_fp W W' -> qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W Q bs lo m P ms ->
  qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W' Q bs lo m P ms.
Proof.
  intros until ms. intros HS (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & R).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
  split; [exact (munch_weaken _ _ _ _ HS MU) | exact R].
Qed.

Lemma pop24_st : forall Σ1 cal jB c' i' st, nth_error (r_st (pr (pop24 Σ1 cal jB) c')) i' = Some st ->
  (c' = 24 /\ i' = jB /\ st = CkBatch) \/ ((c' <> 24 \/ i' <> jB) /\ nth_error (r_st (pr Σ1 c')) i' = Some st).
Proof.
  intros Σ1 cal jB c' i' st H. cbn [pr pop24] in H. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|right; split; [left; exact Hcc | exact H]].
  unfold upd_reg in H. cbn [r_st] in H. rewrite nth_error_upd_ck in H. destruct (Nat.eqb_spec jB i') as [<-|Hii].
  - destruct (Nat.ltb_spec jB (length (r_st (pr Σ1 24)))); [injection H as <-; left; tauto | discriminate].
  - right. split; [right; intros E; exact (Hii (eq_sym E)) | exact H].
Qed.

Lemma fp_other : forall Σ c i n p D' c' i', (c' <> c \/ i' <> i) ->
  nth_error (r_st (pr (free_p Σ c i n p D') c')) i' = nth_error (r_st (pr Σ c')) i'.
Proof.
  intros Σ c i n p D' c' i' Hne. cbn [pr free_p]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|reflexivity].
  unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec i i') as [<-|Hii]; [|reflexivity].
  destruct Hne as [X|X]; exfalso; apply X; reflexivity.
Qed.

Section New.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (D' : depot) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D').
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Let HG : geo_ok Σ := geo_of_wf Σ HW0.

Lemma nw_jB : nth_error (r_st (pr Σ 24)) jB = Some CkIdle.
Proof using HW0 HCA.
  clear - HW0 HCA. pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & R3 & _). destruct (R3 24 ltac:(lia)) as (_ & _ & C3).
  rewrite HCA in C3. pose proof (proj1 (Forall_forall _ _) C3 (Z.of_nat jB) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & X).
  rewrite Nat2Z.id in X. exact X.
Qed.

Lemma nw_notD : ~ In (c, i) [(24, j0); (24, jB)].
Proof using HW0 HCA Hn Hj0 Hvar.
  pose proof nw_jB as HjB. clear - Hn Hj0 Hvar HjB. intros [E|[E|[]]]; injection E as <- <-.
  - rewrite Hn in Hj0. injection Hj0 as <-. destruct Hvar as [(_ & X)|(X & _)]; discriminate X.
  - rewrite HjB in Hn. discriminate Hn.
Qed.

Theorem new_ART : forall (m4 m' : mem), ARTc Σ1 m4 -> munch W m4 m' -> wmono bsegs m4 m' ->
  qcache_rep m' (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) -> pclass_rep T 24 (ca_init Σ) cal m' ->
  depot_ok D' (l_DNB L) (l_SSB L) (l_ACEIL L) -> ARTc (enq_new Σ1 cal jB M n) m'.
Proof.
  intros m4 m' ART4 MW WM QT PC24 Dok.
  pose proof nw_jB as HjB. pose proof nw_notD as ND.
  pose proof (se_img Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWi. pose proof (se_Tz Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWt.
  pose proof (se_grant Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWg. pose proof (se_ris Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWr.
  pose proof (se_fa Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWf. pose proof (se_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWs.
  pose proof (se_shad_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWss. pose proof (se_shad_reg Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsr.
  pose proof (se_shad_app Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWsa. pose proof (se_secmap Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) as HWm.
  pose proof (se_geo Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  assert (RA : forall c', 1 <= c' <= 31 -> reg_avoid W SB c' (pr Σ1 c')).
  { intros c' Hc'. cbn [pr free_p]. pose proof (kv_reg Σ W [] HG (ris_of_whole _ W [] HWr) (fun c0 a k Hc0 _ => HWf c0 a k Hc0)
                                                 (fun c0 a k Hc0 _ => HWsr c0 a k Hc0) c' Hc' ltac:(intros [])) as X.
    destruct (Z.eqb_spec c' c) as [->|_]; [exact (reg_avoid_upd _ _ _ _ _ _ X) | exact X]. }
  destruct ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
  apply ARTc_intro.
  -
    cbn [enq_new pop24 set_ql lay free_p] in *.
    apply (consts_rep_frame L m4 m' CR); [|exact WM]. intros a Ha. apply MW.
    destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
    + rewrite E. unfold W_E. cbn [outside]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 ATP Hsp. unfold rb, kUserCap in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (kv_consts Σ W (TZ_E T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_E; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
  -
    intros c' Hc'. pose proof (PR c' Hc') as X. cbn [enq_new pop24 set_ql lay pr] in X |- *. cbn [lay free_p] in X |- *.
    destruct (Z.eqb_spec c' 24) as [->|Hcc].
    + exact (reg_rep_transport W _ 24 _ m4 m' (reg_rep_upd _ _ _ jB CkBatch m4 X) MW WM (reg_avoid_upd _ _ _ _ _ _ (RA 24 ltac:(lia)))).
    + exact (reg_rep_transport W _ c' _ m4 m' X MW WM (RA c' Hc')).
  -
    intros c' Hc'. pose proof (CA c' Hc') as X. cbn [enq_new pop24 set_ql lay pr ca ca_init free_p] in X |- *.
    destruct (Z.eqb_spec c' 24) as [->|Hcc]; [exact PC24|].
    apply (pclass_rep_transport W _ c' _ _ m4 m' X MW WM). apply (kv_pclass Σ W (TZ_E T) HWt c' Hc').
    unfold TZ_E, pc_addr, cacheT. cbn [disjoint_from]. clear - Hc' Hcc. repeat split; try exact I; lia.
  -
    destruct CH as [P Sc]. split.
    + intros c' i' st Hc' Hn'. cbn [enq_new set_ql lay free_p] in Hn' |- *.
      destruct (pop24_st Σ1 cal jB c' i' st Hn') as [(-> & -> & ->)|(Hne & Hn1)].
      *
        pose proof (P 24 jB CkIdle ltac:(lia) ltac:(rewrite (fp_other Σ c i n _ D' 24 jB); [exact HjB|];
                                                   destruct (Z.eq_dec 24 c) as [E|E]; [right; intros ->; rewrite <- E, HjB in Hn; discriminate Hn | left; exact E]))
          as X.
        cbn [lay free_p pchunk] in X |- *. destruct X as (_ & X).
        apply (@pchunk_transport W [] _ 24 jB CkBatch m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
        change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp jB CkIdle HjB).
      * pose proof (P c' i' st Hc' Hn1) as X. cbn [lay free_p] in X, Hn1 |- *.
        destruct (fp_st Σ c i n Hc c' i' st Hn1) as [(-> & -> & ->)|(Hne' & Hn0)].
        -- apply (pchunk_transport W _ c i _ m4 m' X MW WM). apply (kv_pchunk_gen Σ W [(24, j0); (24, jB)] HG HWs HWss c i (CkAlloc n) (CkQuar n) Hc Hn ND).
           intros n' [E|E]; [discriminate E|]. injection E as <-. pose proof HG as (_ & HR & _). destruct HR as (HR & _).
           pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
           pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as Y. cbv beta iota in Y. clear - Y; lia.
        -- assert (HD : (c' = 24 /\ i' = j0) \/ ~ In (c', i') [(24, j0); (24, jB)]).
           { destruct (Z.eq_dec c' 24) as [->|X1]; [destruct (Nat.eq_dec i' j0) as [->|X2]; [left; split; reflexivity|]|].
             - right. intros Hin. destruct Hin as [E|[E|[]]]; injection E as E; [exact (X2 (eq_sym E))|].
               destruct Hne as [Y|Y]; [exact (Y eq_refl) | exact (Y (eq_sym E))].
             - right. intros Hin. apply X1. destruct Hin as [E|[E|[]]]; injection E; auto. }
           destruct HD as [(-> & ->)|Hnin].
           ++
              rewrite Hj0 in Hn0. injection Hn0 as Est. destruct Hvar as [(E & _)|(E0 & _)]; [destruct Hne as [Y|Y]; [exfalso; exact (Y eq_refl) | exfalso; exact (Y E)]|].
              rewrite <- Est, E0 in X |- *.
              apply (pchunk_transport W _ 24 j0 _ m4 m' X MW WM). unfold pchunk_avoid. change (ClassSize 24) with 8192.
              change (Z.max 0 (8192 / 8)) with 1024. exact (se_shad_des Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp j0 st0 Hj0).
           ++ apply (pchunk_transport W _ c' i' _ m4 m' X MW WM). exact (kv_pchunk Σ W _ HG HWs HWss c' i' st Hc' Hn0 Hnin).
    + intros k s Hk. cbn [enq_new pop24 set_ql sec free_p] in Hk |- *.
      apply (schunk_transport W k s m4 m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
  -
    cbn [enq_new pop24 set_ql] in *.
    exact (sec_rep_transport W _ m4 m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
  -
    cbn [enq_new pop24 set_ql ql qg lay free_p] in *.
    destruct QR as (_ & (QG & CG) & MX). split; [exact QT|]. split.
    + split; [apply (rw_cells_transport bsegs W m4 m' _ _ QG MW WM); cbn [cells_size csize Nat.add]; apply HWi; [unfold i_q_global, INST, g_instance; lia | unfold i_q_global, INST, g_instance, SEGTOP_A; lia | exact I]|].
      apply (qchain_transport W m4 m' _ CG MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & QN & _) & _).
      apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) QB b ltac:(apply in_or_app; right; exact Hb)) as (j & Hj & Eb). rewrite Eb.
      assert (HjjB : j <> jB) by (intros ->; rewrite HjB in Hj; discriminate Hj).
      assert (Hjj0 : j <> j0).
      { intros ->. destruct Hvar as [(E & _)|(_ & Hin)]; [exact (HjjB E)|].
        rewrite map_app in QN. apply NoDup_ListNoDup in QN. apply (fl_nodup_app_not_in _ _ _ QN Hin). rewrite <- Eb. apply in_map. exact Hb. }
      apply (HWs 24 j CkBatch); [lia | exact Hj | | lia | change (ClassSize 24) with 8192; lia].
      intros [E|[E|[]]]; injection E as E; [exact (Hjj0 (eq_sym E)) | exact (HjjB (eq_sym E))].
    + apply (rw_cells_transport bsegs W m4 m' _ _ MX MW WM). cbn [cells_size csize Nat.add].
      apply HWi; [unfold i_q_cmutex, INST, g_instance; lia | unfold i_q_cmutex, INST, g_instance, SEGTOP_A; lia | exact I].
  -
    cbn [enq_new pop24 set_ql lay dep free_p] in *.
    exact (dep_rep_transport W L D' m4 m' DR Dok MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I)
             (se_grant67 Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp))).
  -
    cbn [enq_new pop24 set_ql free_p] in *.
    exact (fs_rep_transport W _ m4 m' FR MW WM (kv_fs Σ W [] (TZ_E T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
             ltac:(unfold TZ_E; cbn; repeat split; try exact I; lia))).
  - cbn [enq_new pop24 set_ql free_p] in *. exact (ia_rep_transport W _ m4 m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
  - cbn [enq_new pop24 set_ql lay free_p] in *. exact (shadow_rep_transport W _ m4 m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
  - exact (vis_rep_wmono _ m4 m' VIS WM).
Qed.

End New.

Section New2.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n : Z) (tr : list Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
  \/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Dok : depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis Dinv : dep_step (dep Σ) (fst (depot_put (dep Σ) tr)).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))).
#[local] Notation Σ2 := (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
                          (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Lemma new_enq : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word)
    (F : bvmap 5 word) (fc : bv 32) (m4 : mem) (lo : Z),
  bv_unsigned sp = usp -> ARTc Σ1 m4 -> mem_inv bsegs m4 -> wmono bsegs m m4 ->
  stk bsegs m4 lo (usp + -2208) -> l_ACEIL L <= lo -> lo + 0x10000 <= usp -> usp + 16 <= USTACK_TOP ->
  rt_pres (live_remove (p_abeg SB c i + rz_size n) (live Σ)) (frames Σ) usp m m4 ->
  icpt_frame m4 usp ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m4 (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x80bd4) (Z_to_bv 64 usp)
    (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0x80b64) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 ->
  evt bsegs (enq_post Σ2 (live_remove (p_abeg SB c i + rz_size n) (live Σ)) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR (Z_to_bv 64 0x5db88) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
             (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208))
             (Z_to_bv 64 M) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m4 (seg_rom bsegs)).
Proof.
  intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F fc m4 lo
    Esp ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4.
  pose proof (ART_wf Σ m HA) as HW0. pose proof (geo_of_wf Σ HW0) as HG.
  pose proof (nw_jB Σ cal jB HW0 HCA) as HjB.
  pose proof (se_geo Σ j0 jB st0 CkIdle HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  pose proof (g_grant Σ HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & _).
  pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  assert (Hn1 : 1 <= n <= 2 ^ 16).
  { pose proof HG as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (X & X1 & _). cbv beta iota in X, X1. pose proof (ClassSize_range c Hc) as (X2 & _).
    pose proof (rz_facts n) as (_ & X3). clear - X X1 X2 X3; lia. }
  assert (RSP : 0 <= usp + -2208 < 2 ^ 64) by (clear - Hsp Husp K15; unfold USTACK_TOP, SHB in *; lia).
  pose proof ART4 as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).

  destruct (new_wfx Σ1 cal jB c i n (free_p_wf Σ m c i n _ HA Hc Hn Dok Dinv) (pend_free_p Σ m c i n _ _ HA Hc Hn) HCA) as (WX & WC).
  pose proof (qwf_ql_x _ WX) as QWF. cbn [enq_new set_ql ql pop24 lay free_p] in QWF.
  pose proof HW0 as (_ & _ & _ & _ & (Q1 & _) & _). rewrite <- qbytes_eq in Q1.

  assert (Hinit : ca_init Σ = true).
  { destruct (ca_init Σ) eqn:E; [reflexivity|]. pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & _ & R4 & _).
    rewrite (R4 E 24) in HCA. destruct cal; discriminate HCA. }
  assert (Hcnt : 1 <= Z.of_nat (length (cal ++ [Z.of_nat jB])) <= 16).
  { pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & R3 & _). destruct (R3 24 ltac:(lia)) as (C1 & _). rewrite HCA in C1.
    pose proof (MaxCount_range 24 ltac:(lia)) as (MC & _). rewrite length_app in C1 |- *. cbn [length] in C1 |- *. clear - C1 MC. lia. }
  pose proof (CA 24 ltac:(lia)) as PC. cbn [ca ca_init free_p lay] in PC. rewrite HCA, Hinit in PC. destruct PC as (PCC & chs & ARR & Hlen & Hpre).
  change (ClassSize 24) with 8192 in PCC.
  assert (Hw : nth_error chs (Z.to_nat (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1)) = Some (cpw 24 (Z.of_nat jB))).
  { pose proof (fl_hit_w (cpw 24) (cal ++ [Z.of_nat jB]) chs ltac:(destruct cal; discriminate) Hpre) as X. rewrite last_last in X.
    replace (Z.to_nat (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1)) with (length (cal ++ [Z.of_nat jB]) - 1)%nat by (clear; rewrite length_app; cbn [length]; lia).
    exact X. }
  assert (HAB : chunk_addr SB 24 (cpw 24 (Z.of_nat jB)) = bB).
  { rewrite fl_hit_addr; [rewrite Nat2Z.id; reflexivity | lia | | reflexivity]. change (ClassSize 24) with 8192. clear - K9 K10. unfold p_abeg, rb, kUserCap in *.
    change (ClassSize 24) with 8192 in *. lia. }
  pose proof (MaxCount_range 24 ltac:(lia)) as (MC1 & _).

  assert (NC : exists stj jb, qnew_cells m4 T SB (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb).
  { destruct CR as (CI & _ & _ & _ & _ & _ & _ & ICR). pose proof ICR as STS. do 31 (apply proj2 in STS). apply proj1 in STS.
    cbn [lay free_p] in STS. destruct (stk_split bsegs m4 (T + 2768) (T + 2784) (T + 3168) STS ltac:(lia)) as [_ STS1].
    destruct (stk_split bsegs m4 (T + 2784) (T + 2784 + 8) (T + 3168) STS1 ltac:(lia)) as [STS2 _].
    destruct (fl_c8_of_stk m4 (T + 2784) STS2) as (stj & HST).
    destruct CH as (P & _). pose proof (P 24 jB CkIdle ltac:(lia) ltac:(rewrite (fp_other Σ c i n _ _ 24 jB); [exact HjB|];
        destruct (Z.eq_dec 24 c) as [E|E]; [right; intros ->; rewrite <- E, HjB in Hn; discriminate Hn | left; exact E])) as PB.
    cbn [pchunk lay free_p] in PB. destruct PB as (PB & _). change (ClassSize 24) with 8192 in PB.
    destruct (fl_CB_of_stk m4 bB 8192 PB) as (jb & HJB).
    exists stj, jb. unfold qnew_cells. split; [exact PCC|]. split; [exact ARR|]. split; [exact HST|].
    split; [cbn [lay free_p] in CI; destruct CI as (CI & _); exact (proj1 (proj1 (rwc_app bsegs m4 i_spacebeg [C8 (Z_to_bv 64 SB)] _) CI))|].
    rewrite HAB. exact HJB. }
  destruct NC as (stj & jb & NC).

  eapply (evt_mono bsegs (qenq_post (Z_to_bv 64 0x5db88) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80))
                            (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
                            s7 s8 s9 s10 s11 F fc
                            [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                             (b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] (qcacheT T) (ql Σ ++ [(bB, [(M, n)])]) lo m4
                            (fun m' => qnew_after m' T SB (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs))).
  { destruct Hvar as [(E1 & E2 & HQL)|(E1 & pre & ents0 & HQL & HL0)].
    - pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT.
      eapply evt_mono.
      { apply (qenq_new_hit_empty_spec (Z_to_bv 64 0x5db88) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 (T + 80)) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
                 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4 T (usp + -2128) M n SB lo
                 (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb);
          try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
        all: try (clear - Hn1; lia). all: try (clear - MC1; lia).
        all: try (clear - P3; unfold p_abeg; apply Z.mod_divide in P3; [|lia]; destruct P3 as [q Hq]; rewrite Hq;
                  replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat jB * ClassSize 24) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat jB) * 8192)
                    by (change (ClassSize 24) with 8192; ring); apply Z.mod_mul; lia).
        all: try (clear - K9 K10; unfold r24, rb, kUserCap in *; lia).
        all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
        all: try (clear - T5; unfold SEGTOP_A in *; lia).
        all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
        all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
        all: try exact ST4.
        all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
      intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL.
      eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp.
    - pose proof QR as (QT & _). cbn [ql lay free_p] in QT. rewrite HQL in QT. rewrite HQL in QWF, Q1.
      rewrite <- app_assoc in QWF. cbn [app] in QWF.
      eapply evt_mono.
      { apply (qenq_new_hit_full_spec (Z_to_bv 64 0x5db88) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 (T + 80)) a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 M)
                 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m4 T (usp + -2128) M n SB lo
                 (Z.of_nat (length (cal ++ [Z.of_nat jB]))) (MaxCount 24) chs (cpw 24 (Z.of_nat jB)) stj jb pre b0 ents0);
          try assumption; rewrite ?(unsigned_lit (usp + -2208)) by exact RSP; rewrite ?HAB.
        all: try (clear - Hn1; lia). all: try (clear - MC1; lia).
        all: try (clear - Q1 Hn1; unfold QMAX_L in *; lia).
        all: try (clear - ATP K5 K6 K11; unfold r24, rb, kUserCap in *; lia).
        all: try (clear - T5; unfold SEGTOP_A in *; lia).
        all: try (clear - K1 K5; lia). all: try (clear - HLO2; lia).
        all: try (clear - K14 HLO; lia). all: try (clear - K4 K6 HLO; unfold r24; lia).
        all: try exact ST4. all: try exact QWF.
        all: clear - Hsp Husp K16; unfold USTACK_TOP in *; lia. }
      intros ms P. rewrite (unsigned_lit (usp + -2208)) in P by exact RSP. rewrite HAB in P. rewrite HQL, <- app_assoc. cbn [app].
      eapply qenq_post_weaken; [|exact P]. clear; solve_sub_fp. }
  intros ms5 P5. destruct P5 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m5 & -> & MU5 & WM5 & MI5 & QR5 & NA5 & ST5).
  rewrite (ret_pc_even 0x5db88) by (first [reflexivity | lia]).
  destruct NA5 as (NA1 & NA2 & _).
  assert (HSUB : sub_fp [(qcacheT T, qcacheT T + 32); (pc_addr T 24, pc_addr T 24 + 4); (cstat_alloc T, cstat_alloc T + 8);
                         (b0, b0 + 8192); (bB, bB + 8192); (usp + -2208 - 64, usp + -2208)] W).
  { clear - Hsp. unfold W_E, qcacheT, pc_addr, cstat_alloc. solve_sub_fp. }
  assert (PC5 : pclass_rep T 24 (ca_init Σ) cal m5).
  { rewrite Hinit. split.
    - replace (Z.of_nat (length (cal ++ [Z.of_nat jB])) - 1) with (Z.of_nat (length cal)) in NA1 by (clear; rewrite length_app; cbn [length]; lia).
      change (ClassSize 24) with 8192. exact NA1.
    - exists chs. split; [exact NA2|]. split; [exact Hlen|]. exact (firstn_snoc_map (cpw 24) cal (Z.of_nat jB) chs Hpre). }
  assert (Hvar' : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In b0 (map fst (ql Σ)))).
  { destruct Hvar as [(E1 & E2 & _)|(E1 & pre & ents0 & HQL & _)]; [left; split; assumption|]. right. split; [exact E1|].
    rewrite HQL, map_app. apply in_or_app. right. left. reflexivity. }
  unfold enq_post. exists (Z_to_bv 64 0x5db88), x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, (Z_to_bv 64 n), (Z_to_bv 64 (usp + -2128)),
    (Z_to_bv 64 (T + 208)), (Z_to_bv 64 M), x11, x12, x13, x14, (Z_to_bv 64 usp), (Z_to_bv 64 (M + 16)), (Z_to_bv 64 0x80b64), (Z_to_bv 64 1),
    (Z_to_bv 64 (usp + -2128)), (Z_to_bv 64 (usp + -81)), m5.
  split; [unfold enq_ret_st; rewrite Esp; reflexivity|].
  split; [exact (new_ART Σ c i n _ cal jB j0 st0 usp HW0 Hc Hn HCA Hj0 Hvar' Hsp m4 m5 ART4 (munch_weaken _ _ _ _ HSUB MU5) WM5 QR5 PC5 Dok)|].
  split; [exact WX|]. split; [exact WC|]. split; [exact MI5|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM5)|].
  split; [rewrite Esp; rewrite (unsigned_lit (usp + -2208)) in ST5 by exact RSP; exact ST5|].
  split.
  { rewrite Esp. intros a Ha. rewrite (MU5 a); [exact (RP4 a Ha)|]. apply HSUB.
    apply (kv_client Σ _ [(24, j0); (24, jB)] [] [] usp HG
             (se_img Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_grant Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
             (se_slot Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_shad_app Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
             (se_secmap Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp) (se_stack Σ j0 jB st0 CkIdle usp HG Hj0 HjB Hsp)
             ltac:(apply Forall_forall; intros; exact I) (live_remove (p_abeg SB c i + rz_size n) (live Σ))); [|exact Ha].
    intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
    pose proof HW0 as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
    destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
    + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
      intros [E|[E|[]]]; injection E as <- <-; [rewrite Hj0 in Hn'; injection Hn' as Est; destruct Hvar' as [(_ & X)|(X & _)]; rewrite X in Est; discriminate Est
                                               | rewrite HjB in Hn'; discriminate Hn'].
    + right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
      split; [reflexivity | intros []]. }
  split.
  { rewrite Esp. apply (icpt_frame_transport _ m4 m5 usp ra s0 s1 s2 s3 s4 s5 ICF MU5 WM5). unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from].
    clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia. }
  rewrite Esp. unfold qput_frame in FR4 |- *. apply (rw_cells_transport bsegs _ m4 m5 _ _ FR4 MU5 WM5).
  unfold qcacheT, pc_addr, cstat_alloc. cbn [disjoint_from cells_size csize Nat.add]. clear - K4 K5 K6 K7 K8 K9 K10 K11 K12 K14 Hsp. unfold rb, kUserCap in *. repeat split; try exact I; lia.
Qed.

End New2.

End GWIN.

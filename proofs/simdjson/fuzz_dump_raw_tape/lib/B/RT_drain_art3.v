(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_kit RT_drain_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Definition set_rc (Σ : rtsA) (c : Z) (r : regst) (l : list Z) : rtsA :=
  mkRtsA (lay Σ) (updf (pr Σ) c r) (updf (ca Σ) c l) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fsc0 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ) (ann Σ).

Lemma cdeal_set_rc : forall Σ c i, cdealΣ Σ c i = set_rc Σ c (cdeal_reg c (pr Σ c) (ca Σ c)) (cdeal_ca c i (ca Σ c)).
Proof. reflexivity. Qed.

Lemma set_rc_pr_same : forall Σ c r l, pr (set_rc Σ c r l) c = r.
Proof. intros. unfold set_rc. cbn [pr]. apply updf_same. Qed.
Lemma set_rc_pr_other : forall Σ c r l c', c' <> c -> pr (set_rc Σ c r l) c' = pr Σ c'.
Proof. intros. unfold set_rc. cbn [pr]. apply updf_other. exact H. Qed.
Lemma set_rc_ca_same : forall Σ c r l, ca (set_rc Σ c r l) c = l.
Proof. intros. unfold set_rc. cbn [ca]. apply updf_same. Qed.
Lemma set_rc_ca_other : forall Σ c r l c', c' <> c -> ca (set_rc Σ c r l) c' = ca Σ c'.
Proof. intros. unfold set_rc. cbn [ca]. apply updf_other. exact H. Qed.
Lemma set_rc_fields : forall Σ c r l, lay (set_rc Σ c r l) = lay Σ /\ ca_init (set_rc Σ c r l) = ca_init Σ /\ sec (set_rc Σ c r l) = sec Σ
  /\ sec_nres (set_rc Σ c r l) = sec_nres Σ /\ aw (set_rc Σ c r l) = aw Σ /\ ql (set_rc Σ c r l) = ql Σ /\ qg (set_rc Σ c r l) = qg Σ
  /\ dep (set_rc Σ c r l) = dep Σ /\ fs0 (set_rc Σ c r l) = fs0 Σ /\ fsc0 (set_rc Σ c r l) = fsc0 Σ /\ fs4 (set_rc Σ c r l) = fs4 Σ
  /\ credit (set_rc Σ c r l) = credit Σ /\ live (set_rc Σ c r l) = live Σ /\ frames (set_rc Σ c r l) = frames Σ.
Proof. intros. repeat split; reflexivity. Qed.
Lemma set_rc_allow : forall Σ c r l, rtA_allow (set_rc Σ c r l) = rtA_allow Σ.
Proof. reflexivity. Qed.

Lemma reg_rep_ureg' : forall SB c r i st (m : mem), reg_rep SB c r m -> reg_rep SB c (ureg r i st) m.
Proof. intros SB c r i st m H. unfold reg_rep, ureg in *. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length. exact H. Qed.

Lemma reg_rep_ureg_inv : forall SB c r i st (m : mem), reg_rep SB c (ureg r i st) m -> reg_rep SB c r m.
Proof. intros SB c r i st m H. unfold reg_rep, ureg in *. cbn [r_muser r_mfa r_st r_fl] in H. rewrite upd_length in H. exact H. Qed.

Lemma set_st_pr_same' : forall Σ c i st, pr (set_st Σ c i st) c = ureg (pr Σ c) i st.
Proof. intros. unfold set_st. cbn [pr]. apply updf_same. Qed.
Lemma set_st_pr_other' : forall Σ c i st c', c' <> c -> pr (set_st Σ c i st) c' = pr Σ c'.
Proof. intros. unfold set_st. cbn [pr]. apply updf_other. exact H. Qed.

Lemma recp_set_rc : forall Σ c i, recp Σ c i = set_rc (set_st Σ c i CkIdle) c (cdeal_reg c (pr (set_st Σ c i CkIdle) c) (ca Σ c))
                                                    (cdeal_ca c i (ca Σ c)).
Proof. reflexivity. Qed.

Section ArtK.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (c : Z) (i0 : nat) (st0 : ckst) (TZ : list ivl) (zlo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi0 : nth_error (r_st (pr Σ c)) i0 = Some st0.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis HTZd : disjoint_from TZ (l_T (lay Σ)) 0x50 /\ disjoint_from TZ (l_T (lay Σ) + 48) 16 /\ disjoint_from TZ (l_T (lay Σ) + 0xc60) 1
  /\ (forall c', 1 <= c' <= 31 -> c' <> c -> disjoint_from TZ (pc_addr (l_T (lay Σ)) c') 80) /\ disjoint_from TZ (qcacheT (l_T (lay Σ))) 32.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW : Forall (dzone Σ [] [] [] TZ [] [c] zlo zhi) W.
Hypothesis HA : ARTc (set_st Σ c i0 CkIdle) m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma ak_HD : forall c' i', In (c', i') ([] : list (Z * nat)) -> 1 <= c' <= 31 /\ exists st0, nth_error (r_st (pr Σ c')) i' = Some st0.
Proof. intros c' i' []. Qed.
Lemma ak_HDC : forall c', In c' [c] -> 1 <= c' <= 31.
Proof using Hc. intros c' [<-|[]]. exact Hc. Qed.
Lemma ak_IZ : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) ([] : list ivl).
Proof. constructor. Qed.

Lemma ak_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from [] a n -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_img Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_Tz Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma ak_grant67 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma ak_ris : forall c' a n, 1 <= c' <= 31 -> ~ In c' [c] -> rinfo (RIS_of SB) c' <= a -> a + n <= rinfo (RIS_of SB) c' + 120 -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_ris_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_fa : forall c' a n, 1 <= c' <= 31 -> ~ In c' [c] -> fa SB c' <= a -> a + n <= fa SB c' + kFaCap -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_fa_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') ([] : list (Z * nat)) ->
  p_abeg SB c' i' <= a -> a + n <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_slot_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_shad_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') ([] : list (Z * nat)) ->
  shad (p_abeg SB c' i') <= a -> a + n <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_shad_slot_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_shad_reg : forall c' a n, 1 <= c' <= 31 -> ~ In c' [c] -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + n <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_shad_reg_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k [] -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_shad_app_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof using HG Hc HTZ Hzlo HW. exact (dk_secmap_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo W HW). Qed.
Lemma ak_stack : forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof using HG Hc HTZ Hzlo Hzlh HW. exact (dk_stack_hw Σ [] [] [] TZ [] [c] zlo zhi HG ak_HD ak_HD ak_HDC ak_IZ HTZ Hzlo Hzlh W HW). Qed.

Lemma ak_consts : consts_rep L m'.
Proof using HG Hc HTZ HTZd Hzlo HW HA MU WM.
  destruct HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  apply (consts_rep_frame L m m' (proj1 HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply ak_Tz; [lia | lia | exact Z3].
  + apply (kv_consts Σ W TZ [] ak_img ak_Tz ak_grant); [apply dsjb_all; vm_compute; reflexivity | exact Z1 | exact Ha | exact NE].
Qed.

Lemma ak_reg_other : forall c', 1 <= c' <= 31 -> c' <> c -> reg_rep SB c' (pr Σ c') m'.
Proof using HG Hc HTZ Hzlo HW HA MU WM.
  intros c' Hc' Hne. pose proof (kv_reg Σ W [c] HG ak_ris ak_fa ak_shad_reg) as KR.
  pose proof (proj1 (proj2 HA) c' Hc') as X. rewrite (set_st_pr_other' Σ c i0 CkIdle c' Hne) in X.
  exact (reg_rep_transport W _ c' _ m m' X MU WM (KR c' Hc' ltac:(intros [E|[]]; exact (Hne (eq_sym E))))).
Qed.

Theorem artc_rc : forall (r : regst) (l : list Z), r_st r = upd (r_st (pr Σ c)) i0 CkIdle ->
  reg_rep SB c r m' -> pclass_rep T c (ca_init Σ) l m' -> ARTc (set_rc (set_st Σ c i0 CkIdle) c r l) m'.
Proof using HG Hc Hi0 HTZ HTZd Hzlo HW HA Hdep HQB MU WM.
  intros r l Est HR HP. destruct HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kv_pchunk Σ W [] HG ak_slot ak_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] HG ak_shad_app ak_secmap) as KS.
  apply ARTc_intro.
  - exact ak_consts.
  - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    + rewrite set_rc_pr_same. exact HR.
    + rewrite (set_rc_pr_other _ c r l c' Hne), (set_st_pr_other' Σ c i0 CkIdle c' Hne). exact (ak_reg_other c' Hc' Hne).
  - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    + rewrite set_rc_ca_same. exact HP.
    + rewrite (set_rc_ca_other _ c r l c' Hne).
      exact (pclass_rep_transport W _ c' _ _ m m' (A3 c' Hc') MU WM (kv_pclass Σ W TZ ak_Tz c' Hc' (Z4 c' Hc' Hne))).
  - destruct A4 as [P Sc]. split.
    + intros c' i' st1 Hc' Hn'. destruct (Z.eq_dec c' c) as [->|Hne].
      * rewrite set_rc_pr_same, Est in Hn'.
        assert (Hn0 : nth_error (r_st (pr (set_st Σ c i0 CkIdle) c)) i' = Some st1) by (rewrite set_st_pr_same'; unfold ureg; cbn [r_st]; exact Hn').
        apply (pchunk_transport W _ c i' st1 m m' (P c i' st1 Hc Hn0) MU WM).
        rewrite nth_upd_ck in Hn'. destruct (Nat.eqb_spec i0 i') as [<-|Hii].
        -- destruct (Nat.ltb_spec i0 (length (r_st (pr Σ c)))); [|discriminate]. injection Hn' as <-.
           exact (kv_pchunk_gen Σ W [] HG ak_slot ak_shad_slot c i0 st0 CkIdle Hc Hi0 (fun X => X) ltac:(intros n [E|E]; discriminate E)).
        -- exact (KP c i' st1 Hc Hn' (fun X => X)).
      * rewrite (set_rc_pr_other _ c r l c' Hne) in Hn'.
        apply (pchunk_transport W _ c' i' st1 m m' (P c' i' st1 Hc' Hn') MU WM).
        rewrite (set_st_pr_other' Σ c i0 CkIdle c' Hne) in Hn'. exact (KP c' i' st1 Hc' Hn' (fun X => X)).
    + intros k s Hk. exact (schunk_transport W k s m m' (Sc k s Hk) MU WM (KS k s Hk (fun X => X))).
  - exact (sec_rep_transport W Σ m m' A5 MU WM (kv_sec Σ W [] HG ak_img ak_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_transport W Σ m m' A6 MU WM
             (kv_quar Σ W [] TZ [] HG ak_img ak_Tz ak_slot Z5 ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' []) HQB)).
  - exact (dep_rep_transport W _ _ m m' A7 Hdep MU WM (kv_dep Σ W [] ak_img ltac:(apply dsjb_all'; vm_compute; reflexivity) ak_grant67)).
  - exact (fs_rep_transport W Σ m m' A8 MU WM (kv_fs Σ W [] TZ [] HG ak_img ak_Tz ak_grant ak_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) Z2)).
  - exact (ia_rep_transport W Σ m m' A9 MU WM (kv_ia W [] ak_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' A10 MU WM (kv_shadow Σ W [] HG ak_shad_app)).
  - exact (vis_rep_wmono _ m m' A11 WM).
Qed.

Theorem client_rc : rt_pres (live Σ) (frames Σ) zhi m m'.
Proof using HG Hc HTZ Hzlo Hzlh HW Hlive MU.
  intros a Ha. apply MU. apply (kv_client Σ W [] [] [] zhi HG ak_img ak_grant ak_slot ak_shad_app ak_secmap ak_stack
                        (dsjb_all [] CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live Σ)); [|exact Ha].
  intros p n Hin. destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(s & Hs & Hq & Hsn & Ep)].
  - left. exists c', i'. split; [exact Hc'|]. split; [exact Hn|]. split; [exact Ep | intros []].
  - right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|]. split; [exact Ep | intros []].
Qed.

End ArtK.

Lemma dzone_DC_nil : forall Σ D DSH DS TZ IZ DC zlo zhi iv, dzone Σ D DSH DS TZ IZ [] zlo zhi iv -> dzone Σ D DSH DS TZ IZ DC zlo zhi iv.
Proof.
  intros Σ D DSH DS TZ IZ DC zlo zhi iv H. unfold dzone in *.
  destruct H as [H|[H|[H|[H|[(c & [] & _)|[(c & [] & _)|[(c & [] & _)|[H|[H|H]]]]]]]]].
  - left; exact H. - right; left; exact H. - right; right; left; exact H. - right; right; right; left; exact H.
  - do 7 right; left; exact H. - do 8 right; left; exact H. - do 9 right; exact H.
Qed.

Lemma Forall_dzone_DC_nil : forall Σ D DSH DS TZ IZ DC zlo zhi W, Forall (dzone Σ D DSH DS TZ IZ [] zlo zhi) W ->
  Forall (dzone Σ D DSH DS TZ IZ DC zlo zhi) W.
Proof. intros. eapply Forall_impl; [|exact H]. intros iv. apply dzone_DC_nil. Qed.

Section ArtK0.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (TZ : list ivl) (zlo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis HW : Forall (dzone Σ [] [] [] TZ [] [] zlo zhi) W.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma ak0_HDC : forall c', In c' ([] : list Z) -> 1 <= c' <= 31.
Proof. intros c' []. Qed.

Lemma ak0_reg : forall c, 1 <= c <= 31 -> reg_rep (l_SB (lay Σ)) c (pr Σ c) m -> reg_rep (l_SB (lay Σ)) c (pr Σ c) m'.
Proof using HG HTZ Hzlo HW MU WM.
  intros c Hc HR0.
  pose proof (kv_reg Σ W [] HG (dk_ris_hw Σ [] [] [] TZ [] [] zlo zhi HG (ak_HD Σ) (ak_HD Σ) ak0_HDC ak_IZ HTZ Hzlo W HW)
                (dk_fa_hw Σ [] [] [] TZ [] [] zlo zhi HG (ak_HD Σ) (ak_HD Σ) ak0_HDC ak_IZ HTZ Hzlo W HW)
                (dk_shad_reg_hw Σ [] [] [] TZ [] [] zlo zhi HG (ak_HD Σ) (ak_HD Σ) ak0_HDC ak_IZ HTZ Hzlo W HW)) as KR.
  exact (reg_rep_transport W _ c _ m m' HR0 MU WM (KR c Hc (fun X => X))).
Qed.

End ArtK0.

End GWIN.

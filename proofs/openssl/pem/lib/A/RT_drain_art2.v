(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_kit RT_drain_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma reg_rep_ureg : forall SB c r i st (m : mem), reg_rep SB c r m -> reg_rep SB c (ureg r i st) m.
Proof. intros SB c r i st m H. unfold reg_rep, ureg in *. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length. exact H. Qed.

Lemma set_st_pr_same : forall Σ c i st, pr (set_st Σ c i st) c = ureg (pr Σ c) i st.
Proof. intros. unfold set_st. cbn [pr]. apply updf_same. Qed.
Lemma set_st_pr_other : forall Σ c i st c', c' <> c -> pr (set_st Σ c i st) c' = pr Σ c'.
Proof. intros. unfold set_st. cbn [pr]. apply updf_other. exact H. Qed.

Section ArtC.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (c : Z) (i : nat) (st st' : ckst) (TZ : list ivl) (zlo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hnb : st <> CkBatch.
Hypothesis Hna : forall n, st <> CkAlloc n.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis HTZd : disjoint_from TZ (l_T (lay Σ)) 0x30 /\ disjoint_from TZ (l_T (lay Σ) + 48) 16 /\ disjoint_from TZ (l_T (lay Σ) + 0xc60) 1
  /\ (forall c', 1 <= c' <= 31 -> disjoint_from TZ (pc_addr (l_T (lay Σ)) c') 80) /\ disjoint_from TZ (qcacheT (l_T (lay Σ))) 32.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW : Forall (dzone Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi) W.
Hypothesis HA : ARTc Σ m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma ac_HD : forall c' i', In (c', i') [(c, i)] -> 1 <= c' <= 31 /\ exists st0, nth_error (r_st (pr Σ c')) i' = Some st0.
Proof using Hc Hi. intros c' i' [E|[]]. injection E as <- <-. split; [exact Hc | exists st; exact Hi]. Qed.
Lemma ac_HDC : forall c', In c' [] -> 1 <= c' <= 31.
Proof. intros c' []. Qed.
Lemma ac_IZ : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) ([] : list ivl).
Proof. constructor. Qed.

#[local] Notation DK := (dzone Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi).
Lemma ac_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from [] a n -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_img Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_Tz Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma ac_grant67 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma ac_ris : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> rinfo (RIS_of SB) c' <= a -> a + n <= rinfo (RIS_of SB) c' + 120 -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_ris_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_fa : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> fa SB c' <= a -> a + n <= fa SB c' + kFaCap -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_fa_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') [(c, i)] ->
  p_abeg SB c' i' <= a -> a + n <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_slot_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_shad_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') [(c, i)] ->
  shad (p_abeg SB c' i') <= a -> a + n <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_shad_slot_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_shad_reg : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + n <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_shad_reg_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k [] -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_shad_app_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo HW. exact (dk_secmap_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo W HW). Qed.
Lemma ac_stack : forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof using HG Hc Hi HTZ Hzlo Hzlh HW. exact (dk_stack_hw Σ [(c, i)] [(c, i)] [] TZ [] [] zlo zhi HG ac_HD ac_HD ac_HDC ac_IZ HTZ Hzlo Hzlh W HW). Qed.

Lemma ac_consts : consts_rep L m'.
Proof using HG Hc Hi HTZ HTZd Hzlo HW HA MU WM.
  destruct HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  apply (consts_rep_frame L m m' (proj1 HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply ac_Tz; [lia | lia | exact Z3].
  + apply (kv_consts Σ W TZ [] ac_img ac_Tz ac_grant); [apply dsjb_all; vm_compute; reflexivity | exact Z1 | exact Ha | exact NE].
Qed.

Theorem artc_chunk : pchunk SB c i st' m' -> ARTc (set_st Σ c i st') m'.
Proof using HG Hc Hi Hnb HTZ HTZd Hzlo HW HA Hdep HQB MU WM.
  intros HCH. destruct HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kv_reg Σ W [] HG ac_ris ac_fa ac_shad_reg) as KR.
  pose proof (kv_pchunk Σ W [(c, i)] HG ac_slot ac_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] HG ac_shad_app ac_secmap) as KS.
  apply ARTc_intro.
  - exact ac_consts.
  - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    + rewrite set_st_pr_same. apply reg_rep_ureg. exact (reg_rep_transport W _ c _ m m' (A2 c Hc) MU WM (KR c Hc (fun X => X))).
    + rewrite (set_st_pr_other Σ c i st' c' Hne). exact (reg_rep_transport W _ c' _ m m' (A2 c' Hc') MU WM (KR c' Hc' (fun X => X))).
  - intros c' Hc'. exact (pclass_rep_transport W _ c' _ _ m m' (A3 c' Hc') MU WM (kv_pclass Σ W TZ ac_Tz c' Hc' (Z4 c' Hc'))).
  - destruct A4 as [P Sc]. split.
    + intros c' i' st0 Hc' Hn'. destruct (Z.eq_dec c' c) as [->|Hne].
      * rewrite set_st_pr_same in Hn'. unfold ureg in Hn'. cbn [r_st] in Hn'. rewrite nth_upd_ck in Hn'. destruct (Nat.eqb_spec i i') as [<-|Hii].
        -- destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [injection Hn' as <-; exact HCH | discriminate].
        -- exact (pchunk_transport W _ c i' st0 m m' (P c i' st0 Hc Hn') MU WM (KP c i' st0 Hc Hn' ltac:(intros [E|[]]; injection E as E2; exact (Hii E2)))).
      * rewrite (set_st_pr_other Σ c i st' c' Hne) in Hn'.
        exact (pchunk_transport W _ c' i' st0 m m' (P c' i' st0 Hc' Hn') MU WM (KP c' i' st0 Hc' Hn' ltac:(intros [E|[]]; injection E as E1 E2; exact (Hne (eq_sym E1))))).
    + intros k s Hk. exact (schunk_transport W k s m m' (Sc k s Hk) MU WM (KS k s Hk (fun X => X))).
  - exact (sec_rep_transport W Σ m m' A5 MU WM (kv_sec Σ W [] HG ac_img ac_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_transport W Σ m m' A6 MU WM
             (kv_quar Σ W [(c, i)] TZ [] HG ac_img ac_Tz ac_slot Z5 ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' [E|[]]; injection E as E1 E2; subst c; rewrite <- E2, Hi in Hi'; injection Hi' as Hi'; exact (Hnb Hi'))
                HQB)).
  - exact (dep_rep_transport W _ _ m m' A7 Hdep MU WM (kv_dep Σ W [] ac_img ltac:(apply dsjb_all'; vm_compute; reflexivity) ac_grant67)).
  - exact (fs_rep_transport W Σ m m' A8 MU WM (kv_fs Σ W [] TZ [] HG ac_img ac_Tz ac_grant ac_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) Z2)).
  - exact (ia_rep_transport W Σ m m' A9 MU WM (kv_ia W [] ac_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' A10 MU WM (kv_shadow Σ W [] HG ac_shad_app)).
  - exact (vis_rep_wmono _ m m' A11 WM).
Qed.

Theorem client_chunk : rt_pres (live Σ) (frames Σ) zhi m m'.
Proof using HG Hc Hi Hna HTZ Hzlo Hzlh HW Hlive MU.
  intros a Ha. apply MU. apply (kv_client Σ W [(c, i)] [] [] zhi HG ac_img ac_grant ac_slot ac_shad_app ac_secmap ac_stack
                        (dsjb_all [] CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live Σ)); [|exact Ha].
  intros p n Hin. destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(s & Hs & Hq & Hsn & Ep)].
  - left. exists c', i'. split; [exact Hc'|]. split; [exact Hn|]. split; [exact Ep|]. intros [E|[]]. injection E as <- <-.
    rewrite Hi in Hn. injection Hn as Hn. exact (Hna n Hn).
  - right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|]. split; [exact Ep | intros []].
Qed.

End ArtC.

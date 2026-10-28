(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition IZ_Q : list ivl := [(i_q_cmutex, i_q_cmutex + 4); (i_q_global, i_q_global + 32)].

Lemma IZ_Q_in : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) IZ_Q.
Proof. unfold IZ_Q, i_q_cmutex, i_q_global, INST, g_instance, SEGTOP_A. repeat constructor; cbn; lia. Qed.

Definition zn_eq_dec : forall x y : Z * nat, {x = y} + {x <> y}.
Proof. decide equality; [apply Nat.eq_dec | apply Z.eq_dec]. Defined.

Section ArtQ.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (D : list (Z * nat)) (TZ : list ivl) (zlo zhi : Z) (l g : list batch).
Hypothesis HG : geo_ok Σ.
Hypothesis HD : forall c i, In (c, i) D -> c = 24 /\ nth_error (r_st (pr Σ 24)) i = Some CkBatch.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis HTZd : disjoint_from TZ (l_T (lay Σ)) 0x50 /\ disjoint_from TZ (l_T (lay Σ) + 48) 16 /\ disjoint_from TZ (l_T (lay Σ) + 0xc60) 1
  /\ (forall c, 1 <= c <= 31 -> disjoint_from TZ (pc_addr (l_T (lay Σ)) c) 80).
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW : Forall (dzone Σ D [] [] TZ IZ_Q [] zlo zhi) W.
Hypothesis HA : ARTc Σ m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma aq_HD : forall c i, In (c, i) D -> 1 <= c <= 31 /\ exists st, nth_error (r_st (pr Σ c)) i = Some st.
Proof using HD. intros c i H. destruct (HD c i H) as (-> & X). split; [lia | exists CkBatch; exact X]. Qed.
Lemma aq_HDSH : forall c i, In (c, i) [] -> 1 <= c <= 31 /\ exists st, nth_error (r_st (pr Σ c)) i = Some st.
Proof. intros c i []. Qed.
Lemma aq_HDC : forall c, In c [] -> 1 <= c <= 31.
Proof. intros c []. Qed.

#[local] Ltac hw := first [ exact IZ_Q_in | exact HTZ | exact HG | exact aq_HD | exact aq_HDSH | exact aq_HDC | exact Hzlo | exact Hzlh | exact HW ].

Lemma aq_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from IZ_Q a n -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_img Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from TZ a n -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_Tz Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma aq_grant67 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW j b gn a n Hj). lia.
Qed.
Lemma aq_ris : forall c a n, 1 <= c <= 31 -> ~ In c [] -> rinfo (RIS_of SB) c <= a -> a + n <= rinfo (RIS_of SB) c + 120 -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_ris_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_fa : forall c a n, 1 <= c <= 31 -> ~ In c [] -> fa SB c <= a -> a + n <= fa SB c + kFaCap -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_fa_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  p_abeg SB c i <= a -> a + n <= p_abeg SB c i + ClassSize c -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_slot_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_shad_slot0 : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW.
  intros c i st a n Hc Hn H1 H2. exact (dk_shad_slot_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW c i st a n Hc Hn (fun X => X) H1 H2).
Qed.
Lemma aq_shad_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) D ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. intros c i st a n Hc Hn _. exact (aq_shad_slot0 c i st a n Hc Hn). Qed.
Lemma aq_shad_reg : forall c a n, 1 <= c <= 31 -> ~ In c [] -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= a ->
  a + n <= shad (rb SB c + 2 ^ 32) -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_shad_reg_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k [] -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_shad_app_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof using HG HD HTZ Hzlo HW. exact (dk_secmap_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo W HW). Qed.
Lemma aq_stack : forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof using HG HD HTZ Hzlo Hzlh HW. exact (dk_stack_hw Σ D [] [] TZ IZ_Q [] zlo zhi HG aq_HD aq_HDSH aq_HDC IZ_Q_in HTZ Hzlo Hzlh W HW). Qed.

Lemma aq_consts : consts_rep L m'.
Proof using HG HD HTZ HTZd Hzlo HW HA MU WM.
  destruct HTZd as (Z1 & Z2 & Z3 & Z4).
  apply (consts_rep_frame L m m' (proj1 HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply aq_Tz; [lia | lia | exact Z3].
  + apply (kv_consts Σ W TZ IZ_Q aq_img aq_Tz aq_grant); [apply dsjb_all; vm_compute; reflexivity | exact Z1 | exact Ha | exact NE].
Qed.

Theorem artc_q : quar_rep (set_q Σ l g) m' -> ARTc (set_q Σ l g) m'.
Proof using HG HD HTZ HTZd Hzlo HW HA Hdep MU WM.
  intros HQ. destruct HTZd as (Z1 & Z2 & Z3 & Z4).
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kv_reg Σ W [] HG aq_ris aq_fa aq_shad_reg) as KR.
  pose proof (kv_pchunk Σ W D HG aq_slot aq_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] HG aq_shad_app aq_secmap) as KS.
  apply ARTc_intro; cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 ia_init credit live frames ann set_q].
  - exact aq_consts.
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (A2 c Hc) MU WM (KR c Hc (fun X => X))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (A3 c Hc) MU WM (kv_pclass Σ W TZ aq_Tz c Hc (Z4 c Hc))).
  - destruct A4 as [P Sc]. split.
    + intros c i st Hc Hn. destruct (in_dec zn_eq_dec (c, i) D) as [HDi|HDi].
      * destruct (HD c i HDi) as (-> & Hb). rewrite Hn in Hb. injection Hb as ->.
        apply (pchunk_transport W _ 24 i CkBatch m m' (P 24 i CkBatch Hc Hn) MU WM).
        unfold pchunk_avoid. pose proof (fk_slot Σ HG 24 i CkBatch Hc Hn) as (S1 & S2 & S3 & S4).
        change (ClassSize 24) with 8192 in *. rewrite Z.max_r by lia.
        apply (aq_shad_slot0 24 i CkBatch _ _ Hc Hn); [lia|].
        pose proof (fk_shad_le2 (p_abeg SB 24 i) 8192 ltac:(unfold rb in *; pose proof (fk_prb Σ HG); lia) ltac:(lia)). change (ClassSize 24) with 8192. lia.
      * exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (KP c i st Hc Hn HDi)).
    + intros k s Hk. exact (schunk_transport W k s m m' (Sc k s Hk) MU WM (KS k s Hk (fun X => X))).
  - exact (sec_rep_transport W Σ m m' A5 MU WM (kv_sec Σ W IZ_Q HG aq_img aq_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact HQ.
  - exact (dep_rep_transport W _ _ m m' A7 Hdep MU WM (kv_dep Σ W IZ_Q aq_img ltac:(apply dsjb_all'; vm_compute; reflexivity) aq_grant67)).
  - exact (fs_rep_transport W Σ m m' A8 MU WM (kv_fs Σ W [] TZ IZ_Q HG aq_img aq_Tz aq_grant aq_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) Z2)).
  - exact (ia_rep_transport W Σ m m' A9 MU WM (kv_ia W IZ_Q aq_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' A10 MU WM (kv_shadow Σ W [] HG aq_shad_app)).
  - exact (vis_rep_wmono _ m m' A11 WM).
Qed.

Theorem client_q : rt_pres (live Σ) (frames Σ) zhi m m'.
Proof using HG HD HTZ Hzlo Hzlh HW Hlive MU.
  intros a Ha. apply MU. apply (kv_client Σ W D [] IZ_Q zhi HG aq_img aq_grant aq_slot aq_shad_app aq_secmap aq_stack
                        (dsjb_all IZ_Q CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live Σ)); [|exact Ha].
  intros p n Hin. destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c & i & Hc & Hn & Ep)|(s & Hs & Hq & Hsn & Ep)].
  - left. exists c, i. split; [exact Hc|]. split; [exact Hn|]. split; [exact Ep|]. intros HDi. destruct (HD c i HDi) as (-> & Hb). rewrite Hn in Hb. discriminate.
  - right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|]. split; [exact Ep | intros []].
Qed.

End ArtQ.

End GWIN.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_kit RT_drain_ldefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Section ArtS.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (zlo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HWs : Forall (fun iv => zlo <= fst iv /\ snd iv <= zhi) W.
Hypothesis HA : ARTc Σ m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma as_HW : Forall (dzone Σ [] [] [] [] [] [] zlo zhi) W.
Proof using HWs. eapply Forall_impl; [|exact HWs]. intros iv H. do 9 right. exact H. Qed.

Lemma as_HD : forall c' i', In (c', i') ([] : list (Z * nat)) -> 1 <= c' <= 31 /\ exists st0, nth_error (r_st (pr Σ c')) i' = Some st0.
Proof. intros c' i' []. Qed.
Lemma as_HDC : forall c', In c' ([] : list Z) -> 1 <= c' <= 31.
Proof. intros c' []. Qed.
Lemma as_IZ : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) ([] : list ivl).
Proof. constructor. Qed.
Lemma as_TZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) ([] : list ivl).
Proof. constructor. Qed.

Lemma as_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from [] a n -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_img Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from [] a n -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_Tz Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hzlo HWs.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW j b gn a n Hj). lia.
Qed.
Lemma as_grant67 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hzlo HWs.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW j b gn a n Hj). lia.
Qed.
Lemma as_ris : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> rinfo (RIS_of SB) c' <= a -> a + n <= rinfo (RIS_of SB) c' + 120 -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_ris_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_fa : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> fa SB c' <= a -> a + n <= fa SB c' + kFaCap -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_fa_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') ([] : list (Z * nat)) ->
  p_abeg SB c' i' <= a -> a + n <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_slot_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_shad_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') ([] : list (Z * nat)) ->
  shad (p_abeg SB c' i') <= a -> a + n <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_shad_slot_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_shad_reg : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + n <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_shad_reg_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_shad_app : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k s, nth_error (sec Σ) k = Some s -> In k [] -> hi <= s_mb s \/ s_mb s + smsz (s_n s) <= lo) ->
  shad lo <= a -> a + n <= shad hi -> disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_shad_app_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_secmap : forall k s a n, nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= a -> a + n <= s_mb s + smsz (s_n s) ->
  disjoint_from W a n.
Proof using HG Hzlo HWs. exact (dk_secmap_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo W as_HW). Qed.
Lemma as_stack : forall a n, zhi <= a -> a + n <= USTACK_TOP -> disjoint_from W a n.
Proof using HG Hzlo Hzlh HWs. exact (dk_stack_hw Σ [] [] [] [] [] [] zlo zhi HG as_HD as_HD as_HDC as_IZ as_TZ Hzlo Hzlh W as_HW). Qed.

Lemma as_consts : consts_rep L m'.
Proof using HG Hzlo HWs HA MU WM.
  apply (consts_rep_frame L m m' (proj1 HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply as_Tz; [lia | lia | exact I].
  + apply (kv_consts Σ W [] [] as_img as_Tz as_grant); [apply dsjb_all; vm_compute; reflexivity | exact I | exact Ha | exact NE].
Qed.

Theorem artc_stk : ARTc Σ m'.
Proof using HG Hzlo HWs HA Hdep HQB MU WM.
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kv_reg Σ W [] HG as_ris as_fa as_shad_reg) as KR.
  pose proof (kv_pchunk Σ W [] HG as_slot as_shad_slot) as KP.
  pose proof (kv_schunk Σ W [] HG as_shad_app as_secmap) as KS.
  apply ARTc_intro.
  - exact as_consts.
  - intros c' Hc'. exact (reg_rep_transport W _ c' _ m m' (A2 c' Hc') MU WM (KR c' Hc' (fun X => X))).
  - intros c' Hc'. exact (pclass_rep_transport W _ c' _ _ m m' (A3 c' Hc') MU WM (kv_pclass Σ W [] as_Tz c' Hc' I)).
  - destruct A4 as [P Sc]. split.
    + intros c' i' st0 Hc' Hn'. exact (pchunk_transport W _ c' i' st0 m m' (P c' i' st0 Hc' Hn') MU WM (KP c' i' st0 Hc' Hn' (fun X => X))).
    + intros k s Hk. exact (schunk_transport W k s m m' (Sc k s Hk) MU WM (KS k s Hk (fun X => X))).
  - exact (sec_rep_transport W Σ m m' A5 MU WM (kv_sec Σ W [] HG as_img as_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_transport W Σ m m' A6 MU WM
             (kv_quar Σ W [] [] [] HG as_img as_Tz as_slot I ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' []) HQB)).
  - exact (dep_rep_transport W _ _ m m' A7 Hdep MU WM (kv_dep Σ W [] as_img ltac:(apply dsjb_all'; vm_compute; reflexivity) as_grant67)).
  - exact (fs_rep_transport W Σ m m' A8 MU WM (kv_fs Σ W [] [] [] HG as_img as_Tz as_grant as_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) I)).
  - exact (ia_rep_transport W Σ m m' A9 MU WM (kv_ia W [] as_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' A10 MU WM (kv_shadow Σ W [] HG as_shad_app)).
  - exact (vis_rep_wmono _ m m' A11 WM).
Qed.

Theorem client_stk : rt_pres (live Σ) (frames Σ) zhi m m'.
Proof using HG Hzlo Hzlh HWs Hlive MU.
  intros a Ha. apply MU. apply (kv_client Σ W [] [] [] zhi HG as_img as_grant as_slot as_shad_app as_secmap as_stack
                        (dsjb_all [] CLIENT_STATIC ltac:(vm_compute; reflexivity)) (live Σ)); [|exact Ha].
  intros p n Hin. destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(s & Hs & Hq & Hsn & Ep)].
  - left. exists c', i'. split; [exact Hc'|]. split; [exact Hn|]. split; [exact Ep | intros []].
  - right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|]. split; [exact Ep | intros []].
Qed.

Theorem av_stk : dl_av Σ zhi W.
Proof using HG Hzlo Hzlh HWs.
  split.
  - intros ib a n Hib H1 H2. exact (as_slot 24 ib CkBatch a n ltac:(lia) Hib (fun X => X) H1 H2).
  - exact as_stack.
Qed.

End ArtS.

End GWIN.

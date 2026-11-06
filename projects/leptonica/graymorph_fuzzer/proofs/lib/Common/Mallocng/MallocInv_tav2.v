(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_ameta_iface MallocInv_tryavail MallocInv_free MallocInv_actw MallocInv_act MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_tav_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tavrel_trans : forall A B C sc, tavrel A B sc -> tavrel B C sc -> tavrel A C sc.
Proof using Type. pu_keep tt.
  intros A B C sc [L1 Ar1 Pg1 Mb1 Xm1 F1 Bk1 Ac1 Sb1 Cx1 G1 Gb1 O1 Ob1 D1] [L2 Ar2 Pg2 Mb2 Xm2 F2 Bk2 Ac2 Sb2 Cx2 G2 Gb2 O2 Ob2 D2].
  constructor; try congruence.
  - intros c Hc. rewrite (Ac2 c Hc). apply Ac1. exact Hc.
  - intros x Hx. apply Sb1. apply Sb2. exact Hx.
  - intros k Hv H1 H2. rewrite (Cx2 k Hv H1 H2). apply Cx1; assumption.
  - intros x mtx aibx slx Hx Hr. destruct (G2 x mtx aibx slx Hx Hr) as (mt1 & aib1 & Hx1 & Hr1 & W1 & M1).
    destruct (G1 x mt1 aib1 slx Hx1 Hr1) as (mt0 & aib0 & Hx0 & Hr0 & W0 & M0). exists mt0, aib0. repeat split; auto; congruence.
  - intros x mt0 aib0 slx Hx Hr. destruct (Gb1 x mt0 aib0 slx Hx Hr) as (mt1 & aib1 & Hx1 & Hr1 & W1 & M1).
    destruct (Gb2 x mt1 aib1 slx Hx1 Hr1) as (mtx & aibx & Hxx & Hrx & Wx & Mx). exists mtx, aibx. repeat split; auto; congruence.
  - intros x mt0 Hx Hng. apply O2; [apply O1; assumption | exact Hng].
  - intros x mtx Hx Hng. apply Ob1; [apply Ob2; assumption | exact Hng].
  - intros x. rewrite (D2 x). apply D1.
Qed.

Lemma tavrel_of_tkeep : forall A A' sc, tkeep A A' sc ->
  a_mblocks A' = a_mblocks A -> a_xmaps A' = a_xmaps A -> a_brk_lo A' = a_brk_lo A ->
  (forall x, In x (a_active A' sc) -> In x (a_active A sc)) ->
  tavrel A A' sc.
Proof using Type. pu_keep tt.
  intros A A' sc TK Emb Exm Ebk Hsub. pose proof TK as [L1 Ar1 F1 P1 N1 G1 K1 T1 X1]. constructor; auto.
  - intros k Hv Hk Hnh. apply X1; [exact Hv | exact Hk | intros i ->; exact (Hnh I)].
  - intros x mtx aibx slx Hx Hr. destruct (K1 x mtx Hx) as (mt & Hmx & [E | (Hg & Hg' & W & M & SL)]).
    + subst mtx. exists mt, aibx. auto.
    + destruct Hg as (aib0 & sl0 & Hr0). exists mt, aib0. rewrite (SL _ _ _ _ Hr0 Hr). auto.
  - intros x mt0 aib0 slx Hx Hr. destruct (G1 x mt0 aib0 slx Hx Hr) as (mt' & aib' & Hx' & Hr' & W & M). exists mt', aib'. auto.
  - intros x mt0 Hx Hng. apply N1; [exact Hx|]. intros (aib & sl & Hr). exact (Hng aib sl Hr).
  - intros x mtx Hx Hng. destruct (K1 x mtx Hx) as (mt & Hmx & [E | (Hg & (aib & sl & Hr) & _)]); [subst mtx; exact Hmx | exfalso; exact (Hng aib sl Hr)].
  - exact (tk_dom A A' sc TK).
Qed.

(* [comment removed for export] *)
Lemma tavrel_heur : forall A c' sc, (forall k, ctx_heur k \/ c' k = a_ctx A k) -> tavrel A (set_ctx A c') sc.
Proof using Type. pu_keep tt.
  intros A c' sc Hc. constructor; try reflexivity; try tauto.
  - intros k _ _ Hnh. cbn. destruct (Hc k) as [H | H]; [exfalso; exact (Hnh H) | exact H].
  - intros x mtx aibx slx Hx Hr. exists mtx, aibx. auto.
  - intros x mt0 aib0 slx Hx Hr. exists mt0, aib0. auto.
Qed.

(* [comment removed for export] *)
Lemma tavrel_acA : forall B sc m rest mt aib sl, WF B -> 0 <= sc < 48 -> a_active B sc = m :: rest ->
  a_meta B m = Some mt -> mt_role mt = RGroup aib sl -> mt_avail mt = 0 ->
  tavrel B (acA B m mt aib sl) sc.
Proof using Type. pu_keep tt.
  intros B sc m rest mt aib sl HW Hsc Hact Hm Hr Hav0. constructor; try reflexivity; try tauto.
  - intros x mtx aibx slx Hx Hrx. destruct (acA_meta_inv B m mt aib sl x mtx Hx) as [(-> & ->) | (Hne & Hx')].
    + exists mt, aib. cbn in Hrx. injection Hrx as <- <-. split; [exact Hm|]. split; [exact Hr|]. split; [symmetry; apply ac_mt_w32 | symmetry; apply ac_mt_mem].
    + exists mtx, aibx. auto.
  - intros x mt0 aib0 slx Hx Hrx. destruct (Z.eq_dec x m) as [-> | Hne].
    + rewrite Hm in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
      exists (ac_mt mt aib sl), aib. split; [apply acA_meta_same|]. split; [reflexivity|]. split; [symmetry; apply ac_mt_w32 | symmetry; apply ac_mt_mem].
    + exists mt0, aib0. rewrite (acA_meta_other B m mt aib sl x Hne). auto.
  - intros x mt0 Hx Hng. destruct (Z.eq_dec x m) as [-> | Hne]; [exfalso; rewrite Hm in Hx; injection Hx as <-; exact (Hng aib sl Hr)|].
    rewrite (acA_meta_other B m mt aib sl x Hne). exact Hx.
  - intros x mtx Hx Hng. destruct (acA_meta_inv B m mt aib sl x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [exfalso; exact (Hng aib sl eq_refl) | exact Hx'].
  - exact (dom_acA B m mt aib sl Hm Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma addr_bounce_lock : forall d, 0 <= d < 2^64 -> at_ (v_add A_LOCK (Z_to_bv 64 d)) 888 = Z_to_bv 64 (caddr (KBounce d)).
Proof using Type. pu_keep tt. intros d Hd. rewrite A_LOCK_eq, v_add_Z, at_Z. f_equal. cbn. unfold C_BOUNCE. lia. Qed.

(* [comment removed for export] *)
Lemma mod4096_div64 : forall w, 0 <= w -> (w mod 4096) / 64 = (w / 64) mod 64.
Proof using Type. pu_keep tt.
  intros w Hw. pose proof (Z.div_mod w 4096 ltac:(lia)) as E. pose proof (Z.mod_pos_bound w 4096 ltac:(lia)) as B.
  set (r := w mod 4096) in *. set (a := w / 4096) in *.
  assert (E1 : w / 64 = a * 64 + r / 64).
  { rewrite E at 1. replace (4096 * a + r) with (a * 64 * 64 + r) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  rewrite E1. rewrite Z.add_comm, Z.mod_add by lia. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma w32_sc : forall w, 0 <= w < 2^32 -> v_srli (v_slli (w32 w) 52) 58 = Z_to_bv 64 (w_sc w).
Proof using Type. pu_keep tt.
  intros w Hw. rewrite w32_eq. pose proof (sx32_range w) as Hs.
  rewrite v_slli_Z by lia. rewrite <- (ZZ_mod (sx32 w * 2 ^ 52)).
  rewrite v_srli_Z by (pose proof (Z.mod_pos_bound (sx32 w * 2 ^ 52) (2^64)); lia). f_equal.
  change (2^64) with (2^12 * 2^52). rewrite Z.mul_mod_distr_r by lia.
  change (2^58) with (2^6 * 2^52). rewrite Z.div_mul_cancel_r by lia.
  change (2^12) with 4096. change (2^6) with 64. unfold w_sc.
  assert (E : sx32 w mod 4096 = w mod 4096).
  { pose proof (sx32_eqmod w) as E32. rewrite (Z.mod_small w (2^32)) in E32 by lia.
    pose proof (Z.div_mod (sx32 w) (2^32) ltac:(lia)) as D. rewrite E32 in D. rewrite D.
    replace (2 ^ 32 * (sx32 w / 2 ^ 32) + w) with (w + (1048576 * (sx32 w / 2 ^ 32)) * 4096) by lia.
    apply Z.mod_add. lia. }
  rewrite E. apply mod4096_div64. lia.
Qed.

Lemma w_sc_mod32 : forall w, 0 <= w -> w_sc (w mod 2 ^ 32) = w_sc w.
Proof using Type. pu_keep tt.
  intros w Hw. unfold w_sc. pose proof (Z.div_mod w (2^32) ltac:(lia)) as D. pose proof (Z.mod_pos_bound w (2^32) ltac:(lia)) as B.
  set (r := w mod 2 ^ 32) in *. rewrite D at 1.
  replace (2 ^ 32 * (w / 2 ^ 32) + r) with (w / 2 ^ 32 * 67108864 * 64 + r) by lia.
  rewrite Z.div_add_l by lia. replace (w / 2 ^ 32 * 67108864 + r / 64) with (r / 64 + (w / 2 ^ 32 * 1048576) * 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rep_read_low4 : forall A m a v, WF A -> Rep A m -> has A (FCT a 8 v) -> 0 <= v ->
  exists bs, rdn ml_segs m (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat /\ bytes_le_to_Z bs = v mod 2 ^ 32.
Proof using MLok. pu_keep (MLok).
  intros A m a v HW HR Hf Hv.
  destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
  destruct (rdn_of_mbytes m 4 a (fun k => byte_of v k) ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & Hlen & Hnth).
  { intros k Hk. apply (rep_facts A m HR). exists (FCT a 8 v). split; [exact Hf|]. unfold fbyte. cbn [f_a f_n f_v]. split; [lia|]. f_equal. lia. }
  exists bs. split; [exact Hbs|]. split; [exact Hlen|].
  replace (2 ^ 32) with (2 ^ (8 * Z.of_nat (length bs))) by (rewrite Hlen; reflexivity).
  apply bytes_le_to_Z_of_bytes; [exact Hv|]. intros k Hk. rewrite Hnth by lia. reflexivity.
Qed.

Lemma ts_lw_fact8 : forall {R : Type} A s a v (k : word -> M R) (P : R -> mstate -> Prop),
  WF A -> Rep A (ms_mem s) -> WIN s -> has A (FCT a 8 v) -> 0 <= v ->
  tsafe (k (w32 v) s) P ->
  tsafe ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
Proof using MLok. pu_keep (MLok).
  intros R A s a v k P HW HR HWIN Hf Hv Hk.
  destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
  destruct (rep_read_low4 A (ms_mem s) a v HW HR Hf Hv) as (bs & Hrd & Hl & Hval).
  eapply ts_lw; [apply acc_ok_heap; [exact HWIN | llia | llia | llia] | exact Hrd |].
  rewrite (le_val_Z bs (v mod 2^32) Hval). rewrite v_lw_w32 by (pose proof (Z.mod_pos_bound v (2^32)); lia). rewrite w32_mod. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TavAct.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D B s1.
  Variables (sc m2 : Z) (rest : list Z) (mt2 : meta_rec) (aib2 : Z) (sl2 : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active B sc = m2 :: rest.
  Hypothesis Hm2 : a_meta B m2 = Some mt2.
  Hypothesis Hr2 : mt_role mt2 = RGroup aib2 sl2.
  Hypothesis Hav0 : mt_avail mt2 = 0.
  (* [comment removed for export] *)
  Hypothesis Hnz : mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1) <> 0.
  Implicit Types (P : R -> mstate -> Prop).

  Let B' := acA B m2 mt2 aib2 sl2.

  Theorem ts_tav_activate : forall (K : option (word * word) -> M R) P,
    (forall s' Bf, II sp0 argv envp cb D Bf s' -> ntframe B s1 s' -> tavrel B Bf sc ->
       a_active Bf sc = m2 :: rest -> a_meta Bf m2 = Some (ac_mt mt2 aib2 sl2) ->
       tsafe (K (Some (Z_to_bv 64 m2, w32 (ac_av mt2 aib2))) s') P) ->
    tsafe ((x <- (am3 <- m_lw (at_ (Z_to_bv 64 m2) 24) ;; massert (is0 am3) ;;
                  mp3 <- m_ld (at_ (Z_to_bv 64 m2) 16) ;;
                  ab <- m_lbu (at_ mp3 8) ;;
                  let act2 := v_sllw (wlit 2) ab in
                  massert (is0 (v_andi (at_ (Z_to_bv 64 m2) 28) 3)) ;;
                  fr4 <- m_lw (at_ (Z_to_bv 64 m2) 28) ;;
                  m_sw (at_ (Z_to_bv 64 m2) 28) (v_and fr4 (v_subw w0 act2)) ;;
                  let mask := v_and fr4 (v_addiw act2 (-1)) in
                  m_sw (at_ (Z_to_bv 64 m2) 24) mask ;;
                  massert (negb (is0 mask)) ;;
                  wx <- m_lw (at_ (Z_to_bv 64 m2) 32) ;;
                  let d := v_addi (v_srli (v_slli wx 52) 58) (-7) in
                  (if c_ltu (wlit 31) d then mret tt
                   else b <- m_lbu (at_ (v_add A_LOCK d) 888) ;;
                        if is0 b then mret tt
                        else m_sb (at_ (v_add A_LOCK d) 888) (v_addi b (-1))) ;;
                  mret (Some (Z_to_bv 64 m2, mask))) ;; K x) s1) P.
  Proof using HII Hact Hav0 Hm2 Hnz Hr2 Hsc MLok. pu_keep (HII, Hact, Hav0, Hm2, Hnz, Hr2, Hsc, MLok).
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0. ceil.
    pose proof (meta_facts B m2 mt2 HW Hm2) as (M1 & M2 & M3 & M4 & Mdom).
    destruct (wf_grp B HW m2 mt2 aib2 sl2 Hm2 Hr2) as (Hw32 & _ & _ & Hlen & Hav & Hfr & _ & Haib & _ & Haibl & _ & Hal16 & Hmem & Hfit & Hce & _).
    pose proof (w_last_range (mt_w32 mt2)) as Hlr. change (w_last (mt_w32 mt2)) with (mt_last mt2) in Hlr.
    assert (Hc32 : 2 ^ mt_cnt mt2 <= 2 ^ 32) by (unfold mt_cnt; apply Z.pow_le_mono_r; llia).
    pose proof (Z.mod_pos_bound aib2 32 ltac:(lia)) as Hk.
    pose proof (ac_masks B HW sc m2 rest mt2 aib2 sl2 Hsc Hact Hm2 Hr2 Hav0) as (A1 & A2 & A3 & A4 & A5 & A6).
    assert (Hk1 : 0 < 2 ^ (aib2 mod 32 + 1) <= 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. change (m2 + 24) with (m2 + moff FAvail).
    eapply (ts_lw_metaW B HW s1 (ms_mem s1) [] m2 mt2 FAvail); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FAvail) with (mt_avail mt2); llia |].
    change (mt_f mt2 FAvail) with (mt_avail mt2). rewrite Hav0. apply ts_assoc. apply ts_assert; [reflexivity|].
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. change (m2 + 16) with (m2 + moff FMem).
    eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m2 mt2 FMem); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FMem) with (mt_mem mt2); llia |].
    change (mt_f mt2 FMem) with (mt_mem mt2).
    apply ts_assoc. rewrite at_Z.
    eapply (ts_lbu_factw B HW s1 (ms_mem s1) [] (mt_mem mt2 + 8) aib2); [exact RW0 | exact HWIN | | apply wfree_range_nil | llia |].
    { right; right; right. exists m2, mt2, aib2, sl2. split; [exact Hm2|]. split; [exact Hr2|]. left. right. left. reflexivity. }
    cbv zeta. rewrite !v_sllw_2 by llia.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite !at_Z. apply ts_assert.
    { rewrite v_andi_Z by llia. rewrite is0_Z by (pose proof (Z.land_nonneg (m2 + 28) 3); pose proof (land_le_left (m2 + 28) 3); llia).
      change 3 with (2^2 - 1). rewrite land_ones_low by llia. apply Z.eqb_eq. change (2^2) with 4.
      replace (m2 + 28) with ((m2 / 8 * 2 + 7) * 4) by (pose proof (Z.div_mod m2 8 ltac:(lia)); lia). apply Z_mod_mult. }
    apply ts_assoc. change (m2 + 28) with (m2 + moff FFreed).
    eapply (ts_lw_metaW B HW s1 (ms_mem s1) [] m2 mt2 FFreed); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FFreed) with (mt_freed mt2); llia |].
    change (mt_f mt2 FFreed) with (mt_freed mt2). cbn [moff].
    rewrite (act_mask_hi (mt_freed mt2) (aib2 mod 32)) by llia.
    (* [comment removed for export] *)
    rewrite v_addiw_w32. rewrite <- (w32_mod (2 ^ (aib2 mod 32 + 1) + -1)).
    assert (Emask : Z.land (mt_freed mt2) ((2 ^ (aib2 mod 32 + 1) + -1) mod 2 ^ 32) = ac_av mt2 aib2).
    { rewrite Z.mod_small by lia. replace (2 ^ (aib2 mod 32 + 1) + -1) with (Z.ones (aib2 mod 32 + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
      rewrite Z.land_ones by lia. reflexivity. }
    rewrite v_and_w32 by (pose proof (Z.mod_pos_bound (2 ^ (aib2 mod 32 + 1) + -1) (2^32)); lia). rewrite Emask.
    apply ts_assoc. unfold m_sw at 1.
    eapply (ts_st_domW B HW s1 (ms_mem s1) [] 4 (m2 + 28)); [exact RW0 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |].
    intros m1 RW1. rewrite u_w32 in RW1. change (Z.of_nat 4) with 4 in RW1.
    apply ts_assoc. unfold m_sw at 1.
    eapply (ts_st_domW B HW (upd s1 m1 (ms_vm s1)) (ms_mem s1) _ 4 (m2 + 24)); [exact RW1 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |].
    intros mm RW2. rewrite u_w32 in RW2. change (Z.of_nat 4) with 4 in RW2. cbn [upd ms_vm ms_lo ms_hi].
    (* [comment removed for export] *)
    pose proof (WF_acA B HW sc m2 rest mt2 aib2 sl2 Hsc Hact Hm2 Hr2 Hav0) as HW'. fold B' in HW'.
    set (ws := [FCT (m2 + 24) 4 (sx32 (ac_av mt2 aib2)); FCT (m2 + 28) 4 (sx32 (mt_freed mt2 - mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1)))]) in RW2.
    assert (WO : writes_ok B ws).
    { unfold ws. apply (writes_ok_meta B _ m2 mt2 24 4 _ HW); [| exact Hm2 | lia | lia].
      apply (writes_ok_meta B [] m2 mt2 28 4 _ HW (writes_ok_nil B) Hm2); lia. }
    assert (HR' : Rep B' mm).
    { apply (repw_commit2 B B' (ms_mem s1) ws mm HW' RW2).
      - intros f Hf. destruct (has_acA B m2 mt2 aib2 sl2 Hm2 Hr2 f Hf) as [H | [-> | ->]]; [left; exact H | right | right]; cbn [f_a f_n]; intros x Hx.
        + apply (wlook_cov_some ws (FCT (m2 + 24) 4 (sx32 (ac_av mt2 aib2))) x); [left; reflexivity | cbn [f_a f_n]; lia].
        + eapply (wlook_cov_some ws _ x); [right; left; reflexivity | cbn [f_a f_n]; unfold ac_fr, ac_av; lia].
      - intros x b Hw. left. unfold ws in Hw.
        destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw). destruct Hin as [<- | [<- | []]]; cbn [f_a f_n] in Hxw.
        + rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. cbn [f_v f_a].
          exists m2, (ac_mt mt2 aib2 sl2), FAvail. split; [apply acA_meta_same|]. cbn [moff mlen]. split; [lia|].
          rewrite ac_mt_f. apply byte_of_sx32. lia.
        + rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. cbn [f_v f_a].
          exists m2, (ac_mt mt2 aib2 sl2), FFreed. split; [apply acA_meta_same|]. cbn [moff mlen]. split; [lia|].
          rewrite ac_mt_f. unfold ac_fr, ac_av. apply byte_of_sx32. lia.
      - intros x Hx. apply (proj1 (dom_acA B m2 mt2 aib2 sl2 Hm2 Hr2 x)). exact Hx. }
    set (s2 := upd s1 mm (ms_vm s1)).
    assert (HII2 : II sp0 argv envp cb D B' s2).
    { apply II_intro.
      - exact (IS_commit sp0 argv envp cb B B' s1 ws mm HI RW2 WO HW' HR').
      - cbn [ms_vm upd s2]. apply (VMok_acA B m2 mt2 aib2 sl2 Hm2 Hr2). exact (ii_vm HII).
      - apply (AvOK_transfer B B' (ii_av HII)); try reflexivity. intros x mt' Hx Hrl.
        destruct (acA_meta_inv B m2 mt2 aib2 sl2 x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
      - apply (UsOK_transfer B B' (ii_us HII)); [reflexivity | intros; reflexivity | intros c x; apply (meta_usage_acA B m2 mt2 aib2 sl2 Hm2 Hr2)].
      - apply (deads_transfer B B' D (ii_dd HII)). intros x. split.
        + intros (mt' & Hx & Hrl). destruct (acA_meta_inv B m2 mt2 aib2 sl2 x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
        + intros (mt0 & Hx & Hrl). exists mt0. destruct (Z.eq_dec x m2) as [-> | Hne].
          * rewrite Hm2 in Hx. injection Hx as <-. rewrite Hr2 in Hrl. discriminate.
          * unfold B'. rewrite (acA_meta_other B m2 mt2 aib2 sl2 x Hne). auto. }
    pose proof (ntframe_commit B s1 ws mm HW RW2 WO) as NF2. fold s2 in NF2.
    pose proof (tavrel_acA B sc m2 rest mt2 aib2 sl2 HW Hsc Hact Hm2 Hr2 Hav0) as TV2. fold B' in TV2.
    assert (Hm2' : a_meta B' m2 = Some (ac_mt mt2 aib2 sl2)) by apply acA_meta_same.
    pose proof (ii_is HII2) as HI2. pose proof HI2 as [_ HR2 _ HWIN2 _ _].
    (* [comment removed for export] *)
    apply ts_assoc. apply ts_assert.
    { rewrite is0_w32. rewrite Z.mod_small by lia. apply (proj2 (Bool.negb_true_iff _)). apply Z.eqb_neq. unfold ac_av in *. exact Hnz. }
    (* [comment removed for export] *)
    apply ts_assoc. rewrite ?at_Z.
    pose proof (repw_init B' mm HW' HR') as RW3.
    assert (Hfw : has B' (FCT (m2 + 32) 8 (mt_w32 mt2))).
    { right; right; left. exists m2, (ac_mt mt2 aib2 sl2), FW32. split; [exact Hm2'|]. cbn [moff mlen]. rewrite <- (ac_mt_w32 mt2 aib2 sl2). reflexivity. }
    eapply (ts_lw_fact8 B' s2 (m2 + 32) (mt_w32 mt2)); [exact HW' | exact HR2 | exact HWIN2 | exact Hfw | llia |].
    cbv zeta.
    rewrite <- (w32_mod (mt_w32 mt2)). rewrite (w32_sc (mt_w32 mt2 mod 2 ^ 32)) by (pose proof (Z.mod_pos_bound (mt_w32 mt2) (2^32)); lia).
    rewrite w_sc_mod32 by lia. change (w_sc (mt_w32 mt2)) with (mt_sc mt2). rewrite v_addi_Z.
    pose proof (w_sc_range (mt_w32 mt2)) as Hscr. change (w_sc (mt_w32 mt2)) with (mt_sc mt2) in Hscr.
    destruct (Z.lt_ge_cases (mt_sc mt2) 7) as [Hlt7 | Hge7].
    { (* [comment removed for export] *)
      rewrite <- (ZZ_mod (mt_sc mt2 + -7)). unfold wlit. rewrite c_ltu_Z by (pose proof (Z.mod_pos_bound (mt_sc mt2 + -7) (2^64)); lia).
      replace ((mt_sc mt2 + -7) mod 2 ^ 64) with (2^64 + (mt_sc mt2 - 7)) by (apply (Z.mod_unique_pos _ _ (-1)); lia).
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply ts_assoc. apply ts_bind_ret. apply ts_bind_ret.
      apply (HK s2 B'); [exact HII2 | exact NF2 | exact TV2 | exact Hact | exact Hm2']. }
    destruct (Z.lt_ge_cases 38 (mt_sc mt2)) as [Hgt38 | Hle38].
    { (* [comment removed for export] *)
      unfold wlit. rewrite c_ltu_Z by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply ts_assoc. apply ts_bind_ret. apply ts_bind_ret.
      apply (HK s2 B'); [exact HII2 | exact NF2 | exact TV2 | exact Hact | exact Hm2']. }
    unfold wlit. rewrite c_ltu_Z by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    set (i := mt_sc mt2 + -7). assert (Hi : 0 <= i < 32) by (unfold i; lia). assert (Hcv : cvalid (KBounce i)) by exact Hi.
    apply ts_assoc. apply ts_assoc. rewrite (addr_bounce_lock i) by lia.
    eapply (ts_lbu_ctxW_m B' HW' s2 mm [] (KBounce i)); [exact RW3 | exact HWIN2 | exact Hcv | reflexivity | apply wfree_range_nil |].
    pose proof (wf_ctx_nonneg B' HW' (KBounce i)) as Hb0. pose proof (Z.mod_pos_bound (a_ctx B' (KBounce i)) 256 ltac:(lia)) as Hb.
    set (b := a_ctx B' (KBounce i) mod 256) in *.
    destruct (Z.eq_dec b 0) as [Eb | Nb].
    { rewrite Eb. change (is0 (Z_to_bv 64 0)) with true. cbv iota. apply ts_bind_ret. apply ts_bind_ret.
      apply (HK s2 B'); [exact HII2 | exact NF2 | exact TV2 | exact Hact | exact Hm2']. }
    rewrite is0_Z by lia. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Nb). rewrite v_addi_Z.
    eapply (ts_sb_ctxW B' s2 mm [] (KBounce i)); [exact RW3 | exact HWIN2 | exact Hcv | reflexivity |].
    intros m3 RW4. rewrite uZ in RW4 by lia. cbn [ms_vm upd s2].
    (* [comment removed for export] *)
    set (c' := cupd (a_ctx B') (KBounce i) (b - 1)).
    assert (Hc : forall k, ctx_heur k \/ c' k = a_ctx B' k).
    { intros k. unfold c', cupd. destruct (cslot_eq_dec k (KBounce i)) as [-> | Hne]; [left; exact I | right; reflexivity]. }
    assert (Hnn : forall k, 0 <= c' k).
    { intros k. unfold c', cupd. destruct (cslot_eq_dec k (KBounce i)); [lia | apply (wf_ctx_nonneg B' HW')]. }
    pose proof (WF_ctx_heur B' HW' c' Hc Hnn) as HW''.
    assert (HR'' : Rep (set_ctx B' c') m3).
    { apply (commit_heur B' c' mm _ m3 HW' Hc Hnn RW4).
      - intros x bb Hw. destruct (wlook_some_cov _ _ _ Hw) as (w & [<- | []] & Hxw). cbn [f_a f_n] in Hxw.
        rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia). injection Hw as <-. cbn [f_v f_a].
        exists (KBounce i). split; [exact Hcv|]. cbn [clen]. split; [lia|]. unfold c'. rewrite cupd_same.
        replace (b + -1) with (b - 1) by lia. reflexivity.
      - intros k Hkv Hne x Hx. unfold c', cupd in Hne. destruct (cslot_eq_dec k (KBounce i)) as [-> | Hne']; [| exfalso; exact (Hne eq_refl)].
        cbn [clen] in Hx. apply (wlook_cov_some _ (FCT (caddr (KBounce i)) 1 (b + -1)) x); [left; reflexivity | cbn [f_a f_n]; lia]. }
    apply ts_bind_ret.
    apply (HK (upd s2 m3 (ms_vm s2)) (set_ctx B' c')).
    - apply II_intro.
      + apply (IS_commit sp0 argv envp cb B' (set_ctx B' c') s2 _ m3 HI2 RW4); [apply (writes_ok_ctx B' [] (KBounce i) _ HW' (writes_ok_nil B') Hcv) | exact HW'' | exact HR''].
      + cbn [ms_vm upd]. apply (VMok_ctx_heur B' c' Hc). exact (ii_vm HII2).
      + apply (AvOK_transfer B' _ (ii_av HII2)); try reflexivity. intros x mt' Hx Hrl; exists mt'; auto.
      + apply (UsOK_transfer B' _ (ii_us HII2)); try reflexivity; intros; reflexivity.
      + apply (deads_transfer B' _ D (ii_dd HII2)). intros x. reflexivity.
    - apply (ntframe_trans B B' s1 s2); [exact NF2 | | | reflexivity].
      + exact (ntframe_commit B' s2 _ m3 HW' RW4 (writes_ok_ctx B' [] (KBounce i) _ HW' (writes_ok_nil B') Hcv)).
      + intros x [Hcx | Hd]; [left; exact Hcx | right]. apply (proj1 (dom_acA B m2 mt2 aib2 sl2 Hm2 Hr2 x)). exact Hd.
    - apply (tavrel_trans B B' _ sc TV2). apply tavrel_heur. exact Hc.
    - exact Hact.
    - cbn. exact Hm2'.
  Qed.
End TavAct.

End WithLayout.

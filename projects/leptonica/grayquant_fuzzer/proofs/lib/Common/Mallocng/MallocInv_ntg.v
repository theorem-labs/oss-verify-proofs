(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf5 MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_tryavail MallocInv_ameta_base MallocInv_ameta_iface
  MallocInv_vmops MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_nt1 MallocInv_ntok MallocInv_usage MallocInv_ntfm MallocInv_ntd MallocInv_vmfree.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CtxStores.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  Lemma ts_st_ctxrW : forall s (m0 : word -> option byte) ws n a v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> CTX <= a -> a + Z.of_nat n <= CTX_END ->
    (forall m', RepW A m0 (FCT a (Z.of_nat n) (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof using MLok. pu_keep (MLok).
    intros s m0 ws n a v k P RW HWIN Hlo Hhi Hk. pose proof layout_nums as LN. unfold CTX, CTX_END in *. ceil.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWIN | lia | lia | lia].
    - apply st_zone_ctx; unfold CTX, CTX_END; lia.
    - apply store_ok_ctx; unfold CTX_END; lia.
    - apply Hk. apply repw_store; [exact RW | lia | lia | unfold wzone, CTX, CTX_END; cbn [f_a f_n]; lia].
  Qed.
End CtxStores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma writes_ok_ctxr : forall A ws, WF A ->
  (forall w x, In w ws -> f_a w <= x < f_a w + f_n w -> exists k, cvalid k /\ caddr k <= x < caddr k + clen k) ->
  writes_ok A ws.
Proof using MLok. pu_keep (MLok).
  intros A ws HW H w x Hin Hx. destruct (H w x Hin Hx) as (k & Hk & Hkx).
  exact (writes_ok_ctx A [] k 0 HW (writes_ok_nil A) Hk _ x (or_introl eq_refl) Hkx).
Qed.

Lemma commit_heur : forall A c' m0 ws m, WF A ->
  (forall k, ctx_heur k \/ c' k = a_ctx A k) -> (forall k, 0 <= c' k) ->
  RepW A m0 ws m ->
  (forall x b, wlook ws x = Some b -> exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (c' k) (x - caddr k)) ->
  (forall k, cvalid k -> c' k <> a_ctx A k -> forall x, caddr k <= x < caddr k + clen k -> wlook ws x <> None) ->
  Rep (set_ctx A c') m.
Proof using MLok. pu_keep (MLok).
  intros A c' m0 ws m HW Hc Hnn RW Hw Hch.
  pose proof (WF_ctx_heur A HW c' Hc Hnn) as HW'.
  assert (Esec : c' KSecret = a_ctx A KSecret) by (destruct (Hc KSecret) as [H | H]; [destruct H | exact H]).
  apply (repw_commit2 A (set_ctx A c') m0 ws m HW' RW).
  - intros f Hf. destruct (has_set_ctx A c' f Hf) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hm | Hg]]]].
    + destruct (Z.eq_dec (c' k) (a_ctx A k)) as [E | NE].
      * left. rewrite E. left. exists k. auto.
      * right. cbn [f_a f_n]. exact (Hch k Hk NE).
    + left. right; left. exact Har.
    + left. rewrite Esec. right; left. exists pg. auto.
    + left. right; right; left. exact Hm.
    + left. right; right; right. exact Hg.
  - intros x b Hx. destruct (Hw x b Hx) as (k & Hk & Hkx & ->). right; left. exists k. auto.
  - intros x Hx. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_ori_negZ : forall a i, 0 <= a < 2^64 -> - 2^64 <= i < 0 ->
  v_ori (Z_to_bv 64 a) i = Z_to_bv 64 (Z.lor a (2^64 + i)).
Proof using Type. pu_keep tt.
  intros a i Ha Hi. unfold v_ori. rewrite uZ by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace (i mod 2^64) with (2^64 + i); [reflexivity|].
  symmetry. rewrite <- (Z.mod_add i 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lxor_ones64 : forall W, 0 <= W < 2^64 -> Z.lxor W (2^64 - 1) = 2^64 - 1 - W.
Proof using Type. pu_keep tt.
  intros W HW. change (2^64 - 1) with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; [| lia |].
  2:{ destruct (Z.eq_dec W 0) as [-> | Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  symmetry. apply Z.sub_nocarry_ldiff.
  apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, Z.testbit_ones_nonneg by lia.
  destruct (Z.lt_ge_cases i 64) as [H | H].
  - rewrite (proj2 (Z.ltb_lt i 64) H). cbn. apply andb_false_r.
  - assert (TB : Z.testbit W i = false).
    { apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|]. apply Z.lt_le_trans with (2^64); [lia|]. apply Z.pow_le_mono_r; lia. }
    rewrite TB. reflexivity.
Qed.

Lemma lor_high32 : forall X, 0 <= X < 2^64 -> Z.lor X (2^64 - 32) = 2^64 - 32 + X mod 32.
Proof using Type. pu_keep tt.
  intros X HX. pose proof (Z.mod_pos_bound X 32 ltac:(lia)) as Hm.
  assert (E : Z.lor X (2^64 - 32) = Z.lor (X mod 32) (2^64 - 32)).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
    assert (TB : Z.testbit (2^64 - 32) i = ((5 <=? i) && (i <? 64))%bool).
    { replace (2^64 - 32) with (Z.ones 59 * 2^5) by reflexivity.
      destruct (Z.lt_ge_cases i 5) as [H5 | H5].
      - rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
      - rewrite Z.mul_pow2_bits, Z.testbit_ones by lia. replace (5 <=? i) with true by (symmetry; apply Z.leb_le; lia).
        replace (0 <=? i - 5) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
        destruct (Z.lt_ge_cases i 64); [rewrite !(proj2 (Z.ltb_lt _ _)) by lia | rewrite !(proj2 (Z.ltb_ge _ _)) by lia]; reflexivity. }
    rewrite TB. change 32 with (2^5).
    destruct (Z.lt_ge_cases i 5) as [H5 | H5].
    - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    - rewrite Z.mod_pow2_bits_high by lia. replace (5 <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb orb].
      destruct (Z.lt_ge_cases i 64) as [H64 | H64].
      + rewrite (proj2 (Z.ltb_lt _ _) H64). rewrite Bool.orb_true_r. reflexivity.
      + rewrite (proj2 (Z.ltb_ge _ _) H64). rewrite Bool.orb_false_r.
        apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|]. apply Z.lt_le_trans with (2^64); [lia|]. apply Z.pow_le_mono_r; lia. }
  rewrite E.
  assert (D : Z.land (X mod 32) (2^64 - 32) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (2^64 - 32) with (Z.ones 59 * 2^5) by reflexivity. change 32 with (2^5).
    destruct (Z.lt_ge_cases i 5) as [H5 | H5].
    + rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). lia.
Qed.

(* [comment removed for export] *)
Lemma usage_sub_word : forall U W, 0 <= U < 2^64 -> 0 <= W < 2^64 -> W mod 32 + 1 <= U ->
  v_add (Z_to_bv 64 U) (v_ori (v_xori (Z_to_bv 64 W) (-1)) (-32)) = Z_to_bv 64 (U - (W mod 32 + 1)).
Proof using Type. pu_keep tt.
  intros U W HU HW Hc. pose proof (Z.mod_pos_bound W 32 ltac:(lia)) as Hm.
  rewrite v_xori_negZ by lia. replace (2^64 + -1) with (2^64 - 1) by lia. rewrite lxor_ones64 by lia.
  rewrite v_ori_negZ by lia. replace (2^64 + -32) with (2^64 - 32) by lia. rewrite lor_high32 by lia.
  rewrite v_add_Z. rewrite <- ZZ_mod. f_equal.
  replace (2^64 - 1 - W) with ((31 - W mod 32) + (2^59 - 1 - W / 32) * 32) by (pose proof (Z.div_mod W 32 ltac:(lia)); lia).
  rewrite Z.mod_add, (Z.mod_small (31 - W mod 32)) by lia.
  replace (U + (2 ^ 64 - 32 + (31 - W mod 32))) with ((U - (W mod 32 + 1)) + 1 * 2^64) by lia.
  rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma addr_ctx_off : forall d, at_ A_CTX d = Z_to_bv 64 (CTX + d).
Proof using MLok. pu_keep (MLok). intros d. rewrite at_ctx. f_equal. unfold CTX. lia. Qed.
Lemma caddr_KSeq : caddr KSeq = CTX + 912. Proof using Type. pu_keep tt. cbn. unfold C_SEQ, CTX. lia. Qed.
Lemma caddr_KUseq : forall j, caddr (KUseq j) = CTX + 848 + j. Proof using Type. pu_keep tt. intros j. cbn. unfold C_USEQ, CTX. lia. Qed.
Lemma caddr_KUsage : forall c, caddr (KUsage c) = CTX + 464 + 8 * c. Proof using Type. pu_keep tt. intros c. cbn. unfold C_USAGE, CTX. lia. Qed.

Section CtxSteps.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  (* [comment removed for export] *)
  Lemma ts_lbu_ctxW_m : forall s (m0 : word -> option byte) ws ck (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 1 -> wfree_range ws (caddr ck) 1 ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck mod 256)) s) P ->
    tsafe ((y <- m_lbu (Z_to_bv 64 (caddr ck)) ;; k y) s) P.
  Proof using HW MLok. pu_keep (HW, MLok).
    intros s m0 ws ck k P RW HWIN Hck Hlen Hfree Hk.
    pose proof (ctx_slot_range ck Hck) as (C1 & C2 & C3). unfold CTX_END in *. pose proof layout_nums as LN. ceil.
    pose proof (wf_ctx_nonneg A HW ck) as Hv.
    destruct (repw_read_fact A m0 ws (ms_mem s) (caddr ck) 1 (a_ctx A ck) RW) as (bs & Hrd & Hl & Hval);
      [change (Z.of_nat 1) with 1; left; exists ck; rewrite <- Hlen; auto | exact Hfree | lia | cbn; lia | exact Hv |].
    destruct bs as [|b [|]]; try (cbn in Hl; lia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWIN | lia | lia | cbn; lia] | exact Hrd |].
    rewrite bytes_le_single in Hval. rewrite Hval. change (2 ^ (8 * Z.of_nat 1)) with 256. exact Hk.
  Qed.

  Lemma ts_nt_usage : forall s (m0 : word -> option byte) ws ma mb W sc (K : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> a_meta A ma = Some mb -> mt_w32 mb = W -> 0 <= W < 2^64 -> 0 <= sc < 64 ->
    wfree_range ws (ma + 32) 8 ->
    (sc < 48 -> wfree_range ws (caddr (KUsage sc)) 8 /\ W mod 32 + 1 <= a_ctx A (KUsage sc) < 2^64) ->
    (48 <= sc -> tsafe (K (Z_to_bv 64 W) s) P) ->
    (sc < 48 -> forall m', RepW A m0 (FCT (caddr (KUsage sc)) 8 (a_ctx A (KUsage sc) - (W mod 32 + 1)) :: ws) m' ->
       tsafe (K (Z_to_bv 64 W) (upd s m' (ms_vm s))) P) ->
    tsafe ((w3 <- nt_usage (Z_to_bv 64 ma) (Z_to_bv 64 W) (Z_to_bv 64 sc) ;; K w3) s) P.
  Proof using HW MLok. pu_keep (HW, MLok).
    intros s m0 ws ma mb W sc K P RW HWIN Hma HWm HW64 Hsc Hfree Hus Kbig Ksmall.
    pose proof (meta_facts A ma mb HW Hma) as (M1 & M2 & M3 & M4 & _). ceil.
    unfold nt_usage. unfold wlit. rewrite c_ltu_Z by llia.
    destruct (Z.ltb_spec 47 sc) as [Hbig | Hsmall].
    - apply ts_bind_ret. apply Kbig. lia.
    - destruct (Hus ltac:(lia)) as [Hfree2 HU]. pose proof (Z.mod_pos_bound W 32 ltac:(lia)) as Hm.
      pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (C1 & C2 & C3). cbn [clen] in C2, C3.
      cbv zeta. rewrite (addr_usage sc) by lia. reassoc.
      eapply (ts_ld_ctxfW A HW s m0 ws (KUsage sc)); [exact RW | exact HWIN | cbn; lia | reflexivity | exact Hfree2 |].
      reassoc. rewrite usage_sub_word by lia.
      eapply (ts_sd_ctxW A s m0 ws (KUsage sc)); [exact RW | exact HWIN | cbn; lia | reflexivity |].
      intros m' RW'. rewrite uZ in RW' by lia.
      rewrite at_Z. change (ma + 32) with (ma + moff FW32).
      eapply (ts_ld_metaW A HW _ m0 _ ma mb FW32); [exact RW' | exact HWIN | exact Hma | reflexivity | | change (mt_f mb FW32) with (mt_w32 mb); lia |].
      { cbn [moff]. apply wfree_range_cons; [cbn [f_a f_n]; llia | exact Hfree]. }
      change (mt_f mb FW32) with (mt_w32 mb). rewrite HWm. apply (Ksmall ltac:(lia) m' RW').
  Qed.

  (* [comment removed for export] *)
  Definition seq_writes (d sq : Z) (reset : bool) : list fct :=
    (if (0 <=? d) && (d <=? 31) then [FCT (caddr (KUseq d)) 1 sq] else []) ++
    [FCT (caddr KSeq) 1 sq] ++
    (if reset then [FCT (CTX + 872) 8 0; FCT (CTX + 864) 8 0; FCT (CTX + 856) 8 0; FCT (CTX + 848) 8 0] else []).
  Definition reset_writes (reset : bool) : list fct :=
    if reset then [FCT (CTX + 872) 8 0; FCT (CTX + 864) 8 0; FCT (CTX + 856) 8 0; FCT (CTX + 848) 8 0] else [].

  Lemma ts_seq_next : forall s (m0 : word -> option byte) ws (K : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> wfree_range ws (caddr KSeq) 1 ->
    (forall s1 (sq : Z) (reset : bool), 1 <= sq <= 256 ->
       RepW A m0 (reset_writes reset ++ ws) (ms_mem s1) -> WIN s1 -> ms_vm s1 = ms_vm s -> ms_lo s1 = ms_lo s -> ms_hi s1 = ms_hi s ->
       tsafe (K (Z_to_bv 64 sq) s1) P) ->
    tsafe ((sq <- m_seq_next A_CTX ;; K sq) s) P.
  Proof using HW MLok. pu_keep (HW, MLok).
    intros s m0 ws K P RW HWIN Hfree HK. pose proof layout_nums as LN. ceil.
    pose proof (ctx_slot_range KSeq I) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    unfold m_seq_next. reassoc. rewrite (addr_ctx_off 912), <- caddr_KSeq.
    eapply (ts_lbu_ctxW_m s m0 ws KSeq); [exact RW | exact HWIN | exact I | reflexivity | exact Hfree |].
    set (old := a_ctx A KSeq mod 256). pose proof (Z.mod_pos_bound (a_ctx A KSeq) 256 ltac:(lia)) as Hold. fold old in Hold.
    unfold wlit. rewrite c_eq_Z by lia.
    destruct (Z.eqb_spec old 255) as [E255 | N255].
    - reassoc. rewrite (addr_ctx_off 848).
      eapply (ts_st_ctxrW A s m0 ws 8 (CTX + 848)); [exact RW | exact HWIN | lia | unfold CTX_END, CTX; cbn; lia |]. intros m1 RW1. change (bv_unsigned w0) with 0 in RW1.
      reassoc. rewrite (addr_ctx_off 856).
      eapply (ts_st_ctxrW A _ m0 _ 8 (CTX + 856)); [exact RW1 | exact HWIN | lia | unfold CTX_END, CTX; cbn; lia |]. intros m2 RW2. change (bv_unsigned w0) with 0 in RW2.
      reassoc. rewrite (addr_ctx_off 864).
      eapply (ts_st_ctxrW A _ m0 _ 8 (CTX + 864)); [exact RW2 | exact HWIN | lia | unfold CTX_END, CTX; cbn; lia |]. intros m3 RW3. change (bv_unsigned w0) with 0 in RW3.
      reassoc. rewrite (addr_ctx_off 872).
      eapply (ts_st_ctxrW A _ m0 _ 8 (CTX + 872)); [exact RW3 | exact HWIN | lia | unfold CTX_END, CTX; cbn; lia |]. intros m4 RW4. change (bv_unsigned w0) with 0 in RW4.
      apply ts_bind_ret. change (Z.of_nat 8) with 8 in RW4.
      apply (HK (upd s m4 (ms_vm s)) 1 true ltac:(lia)); [exact RW4 | exact HWIN | reflexivity | reflexivity | reflexivity].
    - apply ts_bind_ret. rewrite v_addi_Z.
      apply (HK s (old + 1) false ltac:(lia)); [exact RW | exact HWIN | reflexivity | reflexivity | reflexivity].
  Qed.
End CtxSteps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma IS_restate : forall sp0 argv envp cb A A' s, IS sp0 argv envp cb A s -> WF A' -> Rep A' (ms_mem s) -> IS sp0 argv envp cb A' s.
Proof using Type. pu_keep tt. intros sp0 argv envp cb A A' s [W R C Wn E G] HW' HR'. constructor; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wfind Hw :=
  first [ rewrite wlook_hit in Hw by (cbn [f_a f_n f_v caddr]; unfold C_SEQ, C_USEQ, C_USAGE, CTX in *; lia)
        | rewrite wlook_skip in Hw by (cbn [f_a f_n f_v caddr]; unfold C_SEQ, C_USEQ, C_USAGE, CTX in *; lia); wfind Hw
        | lazymatch type of Hw with wlook (?w :: _) ?x = _ =>
            let a := eval cbv [f_a caddr C_SEQ C_USEQ C_USAGE CTX] in (f_a w) in
            let n := eval cbv [f_n] in (f_n w) in
            destruct (Z.lt_ge_cases x a); [ wfind Hw | destruct (Z.lt_ge_cases x (a + n)); wfind Hw ]
          end ].

Section FgRoot.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A1 : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D A1 s1.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A1 ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hidle : forall j st, nth_error slots j = Some st -> st = SIdle \/ st = STaken.
  Hypothesis Hnotact : forall c, ~ In ma (a_active A1 c).
  Hypothesis Hml : 0 < mt_maplen mt.

  Let W := mt_w32 mt.
  Let sc := mt_sc mt.
  Let cnt := mt_cnt mt.
  Let mem := mt_mem mt.
  Let L := grp_map_len mt.
  Let A2 := disA A1 ma mt.

  Lemma GW : WF A1. Proof using HII. pu_keep (HII). exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma Ggrp : 0 <= W < 2^64 /\ (sc < 48 \/ (sc = 63 /\ mt_last mt = 0 /\ 0 < mt_maplen mt)) /\ 1 <= cnt <= 32 /\ cnt = W mod 32 + 1 /\
    mem mod 16 = 0 /\ 0x1000 <= mem /\ page_aligned mem /\ heap_range mem (mem + L) /\ 16 <= L /\ L = mt_maplen mt * 4096 /\ 0 <= sc < 64.
  Proof using HII Hma Hml Hr. pu_keep (HII, Hma, Hml, Hr).
    destruct (wf_grp A1 GW ma mt aib slots Hma Hr) as (H1 & _ & H3 & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hmem & Hfit & Hce & Hpg).
    destruct (Hpg Hml) as [Hpal Hhr]. pose proof (w_last_range (mt_w32 mt)) as Hl. pose proof (w_sc_range (mt_w32 mt)) as Hs.
    replace (mt_maplen mt =? 0) with false in Hfit by (symmetry; apply Z.eqb_neq; lia).
    pose proof (stride_ge16 mt ltac:(lia) H3) as HS.
    assert (Hcs : 16 <= mt_cnt mt * mt_stride mt) by (unfold mt_cnt, mt_last in *; nia).
    unfold W, sc, cnt, mem, L in *. unfold mt_cnt, mt_last, mt_sc, grp_map_len, w_last in *.
    split; [lia|]. split; [exact H3|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact Hpal|]. split; [exact Hhr|].
    split; [lia|]. split; [reflexivity | lia].
  Qed.

  Lemma HW2 : WF A2.
  Proof using HII Hidle Hma Hml Hnotact Hr. pu_keep (HII, Hidle, Hma, Hml, Hnotact, Hr). exact (WF_dissolve_root A1 GW ma mt aib slots Hma Hr Hml Hidle Hnotact). Qed.
  Lemma A2_ma : a_meta A2 ma = Some (mtD mt). Proof using A1. pu_keep (A1). apply dis_meta_same. Qed.
  Lemma mtD_f : forall fl, mt_f (mtD mt) fl = mt_f mt fl. Proof using Type. pu_keep tt. intros fl. unfold mtD. apply mt_f_MT. Qed.

  Lemma meta_usage_A2 : forall c x, meta_usage A2 c x = if Z.eq_dec x ma then 0 else meta_usage A1 c x.
  Proof using mt. pu_keep (mt).
    intros c x. unfold meta_usage. destruct (Z.eq_dec x ma) as [-> | Hne].
    - unfold A2. rewrite (dis_meta_same A1 ma mt). reflexivity.
    - unfold A2, disA. cbn [a_meta]. unfold aupd. destruct (Z.eq_dec x ma); [contradiction | reflexivity].
  Qed.

  Lemma usage_of_A2 : forall c, usage_of A2 c = usage_of A1 c - (if c =? sc then cnt else 0).
  Proof using HII Hma Hr L W mem. pu_keep (HII, Hma, Hr, L, W, mem).
    intros c. pose proof GW as HW.
    destruct (proj1 (wf_meta_dom A1 HW ma) ltac:(rewrite Hma; discriminate)) as (pg0 & k0 & Hpg0 & Hk0 & Ema).
    apply (usage_of_point A1 A2 c ma pg0 k0 _ HW eq_refl Hpg0 Hk0 Ema).
    - intros x Hx. rewrite meta_usage_A2. destruct (Z.eq_dec x ma); [contradiction | reflexivity].
    - rewrite meta_usage_A2. destruct (Z.eq_dec ma ma); [| contradiction]. unfold meta_usage. rewrite Hma, Hr.
      change (mt_sc mt) with sc. change (mt_cnt mt) with cnt. destruct (Z.eqb_spec sc c) as [<- | Hne].
      + rewrite Z.eqb_refl. lia.
      + rewrite (proj2 (Z.eqb_neq c sc) ltac:(intros E; apply Hne; symmetry; exact E)). lia.
  Qed.

  Lemma usage_now : sc < 48 -> a_ctx A1 (KUsage sc) = usage_of A1 sc /\ cnt <= usage_of A1 sc < 2^47.
  Proof using A2 HII Hidle Hma Hml Hnotact Hr L W mem. pu_keep (A2, HII, Hidle, Hma, Hml, Hnotact, Hr, L, W, mem).
    intros Hsc. pose proof Ggrp as (_ & _ & Hc & _ & _ & _ & _ & _ & _ & _ & Hs). pose proof (ii_us HII sc ltac:(lia)) as HU.
    pose proof (usage_of_range A2 sc HW2) as R2. rewrite (usage_of_A2 sc), Z.eqb_refl in R2.
    pose proof (usage_of_range A1 sc GW). split; [exact HU | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dis_nodom : forall x, dom A2 x -> ~ (mem <= x < mem + L).
  Proof using HII Hma Hml Hr W cnt sc. pu_keep (HII, Hma, Hml, Hr, W, cnt, sc).
    intros x Hd Hx. pose proof GW as HW.
    destruct Hd as [(pg & Hpg & Hpx) | [(y & mty & aiby & sly & Hy & Hry & Hmly & Hyx) | (pg & Hpg & Hpx)]].
    - destruct (wf_disj_area_grp A1 HW pg ma mt aib slots Hpg Hma Hr Hml); unfold mem, L in *; lia.
    - destruct (dis_group_inv A1 ma mt y mty aiby sly Hy Hry) as [Hy0 Hne].
      destruct (wf_disj_grp_grp A1 HW y mty aiby sly ma mt aib slots Hy0 Hry Hmly Hma Hr Hml Hne); unfold mem, L in *; lia.
    - destruct (wf_disj_page_grp A1 HW pg ma mt aib slots Hpg Hma Hr Hml); unfold mem, L in *; lia.
  Qed.

  Lemma dis_fact_avoid : forall f x, has A2 f -> f_a f <= x < f_a f + f_n f -> ~ (mem <= x < mem + L).
  Proof using HII Hidle Hma Hml Hnotact Hr MLok W cnt sc. pu_keep (HII, Hidle, Hma, Hml, Hnotact, Hr, MLok, W, cnt, sc).
    intros f x Hf Hx Hr'. pose proof GW as HW. pose proof Ggrp as (_ & _ & _ & _ & _ & _ & _ & Hhr & _). unfold heap_range in Hhr.
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - destruct Hc as (k & Hk & ->). cbn [f_a f_n] in Hx. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). pose proof layout_nums. unfold CTX_END in *. lia.
    - destruct Har as (pg & Hpg & ->). cbn [f_a f_n] in Hx. apply (dis_nodom x); [| exact Hr']. left. exists pg. split; [exact Hpg | lia].
    - destruct Hm as (y & mty & fl & Hy & ->). cbn [f_a f_n] in Hx. pose proof (mfield_range fl) as Hfl.
      assert (Hy1 : a_meta A1 y <> None).
      { destruct (dis_meta_inv A1 ma mt y mty Hy) as [(-> & _) | (_ & H)]; [rewrite Hma | rewrite H]; discriminate. }
      destruct (proj1 (wf_meta_dom A1 HW y) Hy1) as (pg & k & Hpg & Hk & ->). pose proof (meta_addr_range pg k Hk).
      apply (dis_nodom x); [| exact Hr']. left. exists pg. split; [exact Hpg | lia].
    - pose proof (has_grp_where A2 HW2 f Hg) as ((y & mty & aiby & sly & Hy & Hry & Hlo & Hhi) & Hn).
      destruct (dis_group_inv A1 ma mt y mty aiby sly Hy Hry) as [Hy0 Hne].
      destruct (dis_clear A1 HW ma mt aib slots Hma Hr Hml Hidle y mty aiby sly Hy0 Hry Hne) as [DC | DC]; unfold mem, L in *; [| lia].
      (* [comment removed for export] *)
      destruct (wf_grp_root A1 HW y mty aiby sly Hy0 Hry) as (r & mtr & aibr & slr & Hmr & Hrr & Hmlr & Hrlo & Hrhi & Hrself).
      destruct (Z.eq_dec r ma) as [-> | Hrne].
      + rewrite Hma in Hmr. injection Hmr as <-. pose proof (stride_ge16 mty ltac:(pose proof (proj1 (wf_grp A1 HW y mty aiby sly Hy0 Hry)); lia) (proj1 (proj2 (proj2 (wf_grp A1 HW y mty aiby sly Hy0 Hry))))).
        unfold gext_lo, gext_hi in *. pose proof (w_last_range (mt_w32 mty)). unfold mt_cnt, mt_last in *. nia.
      + destruct (wf_disj_grp_grp A1 HW r mtr aibr slr ma mt aib slots Hmr Hrr Hmlr Hma Hr Hml Hrne); lia.
  Qed.

  Lemma A2_IS : IS sp0 argv envp cb A2 s1 /\ Rep A2 (ms_mem s1).
  Proof using HII Hidle Hma Hml Hnotact Hr. pu_keep (HII, Hidle, Hma, Hml, Hnotact, Hr).
    pose proof (Rep_disA A1 ma mt Hma (ms_mem s1) (is_rep _ _ _ _ _ _ (ii_is HII))) as HR2.
    split; [exact (IS_restate sp0 argv envp cb A1 A2 s1 (ii_is HII) HW2 HR2) | exact HR2].
  Qed.

  Lemma ma_notin_D : ~ In ma D.
  Proof using HII Hma Hr. pu_keep (HII, Hma, Hr).
    intros Hin. destruct (proj2 (ii_dd HII ma) Hin) as (mtx & Hx & Hrl). rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrl. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma ctx_avoid : forall k x, cvalid k -> caddr k <= x < caddr k + clen k -> ~ (mem <= x < mem + L).
  Proof using HII Hma Hml Hr MLok W cnt sc. pu_keep (HII, Hma, Hml, Hr, MLok, W, cnt, sc).
    intros k x Hk Hx Hr'. pose proof Ggrp as (_ & _ & _ & _ & _ & _ & _ & Hhr & _). unfold heap_range in Hhr.
    pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). pose proof layout_nums. unfold CTX_END in *. lia.
  Qed.
  Lemma meta_avoid : forall y x, a_meta A2 y <> None -> y <= x < y + 40 -> ~ (mem <= x < mem + L).
  Proof using HII Hma Hml Hr W cnt sc. pu_keep (HII, Hma, Hml, Hr, W, cnt, sc).
    intros y x Hy Hx. pose proof GW as HW.
    assert (Hy1 : a_meta A1 y <> None).
    { unfold A2, disA in Hy. cbn [a_meta] in Hy. unfold aupd in Hy. destruct (Z.eq_dec y ma) as [-> | Hne]; [rewrite Hma; discriminate | exact Hy]. }
    destruct (proj1 (wf_meta_dom A1 HW y) Hy1) as (pg & k & Hpg & Hk & ->). pose proof (meta_addr_range pg k Hk).
    apply dis_nodom. left. exists pg. split; [exact Hpg | lia].
  Qed.

  Theorem ts_nt_fg_root : forall rec (K : word * word -> M R) P,
    (forall s' A', II sp0 argv envp cb D A' s' -> ntframe A1 s1 s' -> fgrel A1 A' ma ->
       nt_res A1 A' (ms_vm s1) (Z_to_bv 64 mem, Z_to_bv 64 L) ->
       tsafe (K (Z_to_bv 64 mem, Z_to_bv 64 L) s') P) ->
    tsafe ((r <- nt_fg rec (Z_to_bv 64 ma) ;; K r) s1) P.
  Proof using A2 HII Hidle Hma Hml Hnotact Hr MLok W cnt sc. pu_keep (A2, HII, Hidle, Hma, Hml, Hnotact, Hr, MLok, W, cnt, sc).
    intros rec K P HK. pose proof GW as HW. pose proof HW2 as HWA2. destruct A2_IS as [HIS2 HR2].
    pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof Ggrp as (HW64 & Hsc & Hcnt & Ecnt & Hal16 & Hmem & Hpal & Hhr & HL16 & EL & Hsc64).
    pose proof Hhr as Hhr'. unfold heap_range in Hhr'.
    pose proof (meta_facts A1 ma mt HW Hma) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof (repw_init A2 (ms_mem s1) HWA2 HR2) as RW0.
    pose proof A2_ma as Hma2.
    unfold nt_fg. reassoc. rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_metaW A2 HWA2 s1 (ms_mem s1) [] ma (mtD mt) FW32); [exact RW0 | exact HWIN | exact Hma2 | reflexivity | apply wfree_range_nil | rewrite mtD_f; change (mt_f mt FW32) with W; lia |].
    rewrite mtD_f. change (mt_f mt FW32) with W. cbv zeta. unfold W. rewrite (wsc_eq mt) by lia. fold W. change (mt_sc mt) with sc.
    reassoc.
    (* [comment removed for export] *)
    assert (TAIL : forall s2 ws,
      RepW A2 (ms_mem s1) ws (ms_mem s2) -> WIN s2 -> ms_vm s2 = ms_vm s1 -> ms_lo s2 = ms_lo s1 -> ms_hi s2 = ms_hi s1 ->
      ((ws = [] /\ 48 <= sc) \/ (ws = [FCT (caddr (KUsage sc)) 8 (usage_of A1 sc - cnt)] /\ sc < 48)) ->
      tsafe ((r <- (if negb (is0 (v_srli (Z_to_bv 64 W) 12)) then nt_fg_root (Z_to_bv 64 ma) (Z_to_bv 64 sc) else nt_fg_nested rec (Z_to_bv 64 ma)) ;; K r) s2) P).
    2:{ eapply (ts_nt_usage A2 HWA2 s1 (ms_mem s1) [] ma (mtD mt) W sc); [exact RW0 | exact HWIN | exact Hma2 | unfold mt_w32; rewrite mtD_f; reflexivity | lia | lia | apply wfree_range_nil | | |].
        - intros Hsc48. destruct (usage_now Hsc48) as [EU HU]. split; [apply wfree_range_nil|]. change (a_ctx A2 (KUsage sc)) with (a_ctx A1 (KUsage sc)). rewrite EU. lia.
        - intros Hsc48. apply (TAIL s1 [] RW0 HWIN eq_refl eq_refl eq_refl). left. auto.
        - intros Hsc48 m' RW'. apply (TAIL (upd s1 m' (ms_vm s1)) _ RW' HWIN eq_refl eq_refl eq_refl). right.
          destruct (usage_now Hsc48) as [EU HU]. change (a_ctx A2 (KUsage sc)) with (a_ctx A1 (KUsage sc)). rewrite EU. split; [reflexivity | exact Hsc48]. }
    intros s2 wsu RWu HWIN2 Hvm2 Hlo2 Hhi2 Hwsu.
    assert (Hwsu_free : forall a n, (a + n <= caddr (KUsage sc) \/ caddr (KUsage sc) + 8 <= a) -> wfree_range wsu a n).
    { intros a n Ha. destruct Hwsu as [(-> & _) | (-> & _)]; [apply wfree_range_nil | apply wfree_range_cons; [cbn [f_a f_n]; lia | apply wfree_range_nil]]. }
    unfold W. rewrite (wmaplen_eq mt) by lia. rewrite is0_Z by (pose proof (maplen_nonneg mt ltac:(lia)); unfold mt_maplen, w_maplen in *; split; [lia | apply Z.div_lt_upper_bound; lia]).
    replace (mt_maplen mt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    unfold nt_fg_root. reassoc.
    pose proof (ctx_slot_range KSeq I) as (S1 & S2 & S3). pose proof (ctx_slot_range (KUsage sc)) as SU. pose proof layout_nums as LN.
    eapply (ts_seq_next A2 HWA2 s2 (ms_mem s1) wsu); [exact RWu | exact HWIN2 | apply Hwsu_free; cbn [caddr clen]; unfold C_SEQ, C_USAGE; lia |].
    intros s3 sq reset Hsq RW3 HWIN3 Hvm3 Hlo3 Hhi3.
    set (d := sc - 7).
    (* [comment removed for export] *)
    assert (REST : forall s4 ws4, RepW A2 (ms_mem s1) ws4 (ms_mem s4) -> WIN s4 -> ms_vm s4 = ms_vm s1 -> ms_lo s4 = ms_lo s1 -> ms_hi s4 = ms_hi s1 ->
      ws4 = seq_writes d sq reset ++ wsu ->
      tsafe ((r <- (w4 <- m_ld (at_ (Z_to_bv 64 ma) 32) ;;
                    base <- m_ld (at_ (Z_to_bv 64 ma) 16) ;;
                    m_free_meta (at_ A_CTX 16) (Z_to_bv 64 ma) ;;
                    mret (base, v_and w4 PAGEMASK)) ;; K r) s4) P).
    2:{ reassoc. rewrite (addr_ctx_off 912), <- caddr_KSeq.
        eapply (ts_sb_ctxW A2 s3 (ms_mem s1) _ KSeq); [exact RW3 | exact HWIN3 | exact I | reflexivity |]. intros m4 RW4. rewrite uZ in RW4 by lia.
        reassoc. rewrite v_addi_Z. unfold wlit.
        destruct (Z.lt_ge_cases sc 7) as [H7 | H7].
        - rewrite <- (ZZ_mod (sc + -7)). rewrite c_ltu_Z by (pose proof (Z.mod_pos_bound (sc + -7) (2^64)); lia).
          replace (31 <? (sc + -7) mod 2 ^ 64) with true.
          2:{ symmetry. apply Z.ltb_lt. replace (sc + -7) with (-(7 - sc)) by lia. rewrite Z.mod_opp_l_nz by lia. rewrite Z.mod_small by lia. lia. }
          apply ts_bind_ret. apply (REST (upd s3 m4 (ms_vm s3)) _ RW4 HWIN3); [cbn; rewrite Hvm3; exact Hvm2 | cbn; rewrite Hlo3; exact Hlo2 | cbn; rewrite Hhi3; exact Hhi2 |].
          unfold seq_writes, reset_writes, d. replace (0 <=? sc - 7) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
        - rewrite c_ltu_Z by lia. destruct (Z.ltb_spec 31 (sc + -7)) as [H38 | H38].
          + apply ts_bind_ret. apply (REST (upd s3 m4 (ms_vm s3)) _ RW4 HWIN3); [cbn; rewrite Hvm3; exact Hvm2 | cbn; rewrite Hlo3; exact Hlo2 | cbn; rewrite Hhi3; exact Hhi2 |].
            unfold seq_writes, reset_writes, d. replace (sc - 7 <=? 31) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. reflexivity.
          + rewrite addr_useq.
            eapply (ts_sb_ctxW A2 _ (ms_mem s1) _ (KUseq (sc + -7))); [exact RW4 | exact HWIN3 | cbn; lia | reflexivity |]. intros m5 RW5. rewrite uZ in RW5 by lia.
            apply (REST (upd (upd s3 m4 (ms_vm s3)) m5 (ms_vm (upd s3 m4 (ms_vm s3)))) _ RW5 HWIN3); [cbn; rewrite Hvm3; exact Hvm2 | cbn; rewrite Hlo3; exact Hlo2 | cbn; rewrite Hhi3; exact Hhi2 |].
            unfold seq_writes, reset_writes, d. replace (0 <=? sc - 7) with true by (symmetry; apply Z.leb_le; lia).
            replace (sc - 7 <=? 31) with true by (symmetry; apply Z.leb_le; lia). cbn [andb app]. replace (sc + -7) with (sc - 7) by lia. reflexivity. }
    intros s4 ws3 RW4 HWIN4 Hvm4 Hlo4 Hhi4 Ews3.
    (* [comment removed for export] *)
    set (c' := fun k => match k with
      | KSeq => sq
      | KUseq j => if (j =? d) && ((0 <=? d) && (d <=? 31)) then sq else if reset && ((0 <=? j) && (j <=? 31)) then 0 else a_ctx A2 k
      | KUsage c => if (c =? sc) && (sc <? 48) then usage_of A1 sc - cnt else a_ctx A2 k
      | _ => a_ctx A2 k end).
    set (A3 := set_ctx A2 c').
    assert (Hheur : forall k, ctx_heur k \/ c' k = a_ctx A2 k) by (intros k; destruct k; cbn; auto).
    assert (Hnn : forall k, 0 <= c' k).
    { intros k. pose proof (wf_ctx_nonneg A2 HWA2 k). destruct k; cbn [c']; try lia.
      - destruct ((i =? sc) && (sc <? 48))%bool eqn:E; [| lia]. apply andb_prop in E. destruct E as [_ E]. apply Z.ltb_lt in E. destruct (usage_now E). lia.
      - destruct ((i =? d) && ((0 <=? d) && (d <=? 31)))%bool; [lia|]. destruct (reset && ((0 <=? i) && (i <=? 31)))%bool; lia. }
    pose proof (WF_ctx_heur A2 HWA2 c' Hheur Hnn) as HW3. fold A3 in HW3.
    assert (INws : forall w, In w ws3 ->
      (w = FCT (caddr (KUseq d)) 1 sq /\ 0 <= d <= 31) \/ w = FCT (caddr KSeq) 1 sq \/
      (reset = true /\ exists m4, (m4 = 0 \/ m4 = 8 \/ m4 = 16 \/ m4 = 24) /\ w = FCT (CTX + 848 + m4) 8 0) \/
      (w = FCT (caddr (KUsage sc)) 8 (usage_of A1 sc - cnt) /\ sc < 48)).
    { intros w Hw. rewrite Ews3 in Hw. unfold seq_writes in Hw. rewrite !in_app_iff in Hw.
      destruct Hw as [[Hw | [Hw | Hw]] | Hw].
      - destruct ((0 <=? d) && (d <=? 31))%bool eqn:E; [| destruct Hw]. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct Hw as [<- | []]. left. auto.
      - destruct Hw as [<- | []]. right; left. reflexivity.
      - destruct reset; [| destruct Hw]. right; right; left. split; [reflexivity|].
        destruct Hw as [<- | [<- | [<- | [<- | []]]]]; [exists 24 | exists 16 | exists 8 | exists 0]; split; try lia; f_equal; lia.
      - right; right; right. destruct Hwsu as [(-> & _) | (-> & Hs)]; [destruct Hw | destruct Hw as [<- | []]; auto]. }
    assert (WO3 : writes_ok A2 ws3).
    { apply (writes_ok_ctxr A2 ws3 HWA2). intros w x Hw Hx.
      destruct (INws w Hw) as [(-> & Hd) | [-> | [(Er & m4 & Hm4 & ->) | (-> & Hs)]]]; cbn [f_a f_n caddr] in Hx; unfold C_USEQ, C_SEQ, C_USAGE, CTX in Hx.
      - exists (KUseq d). cbn. unfold C_USEQ. split; [lia | lia].
      - exists KSeq. cbn. unfold C_SEQ. split; [exact I | lia].
      - exists (KUseq (x - (CTX + 848))). cbn. unfold C_USEQ, CTX. split; lia.
      - exists (KUsage sc). cbn. unfold C_USAGE. split; [lia | lia]. }
    assert (LOOK : forall x b, wlook ws3 x = Some b -> exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (c' k) (x - caddr k)).
    { intros x b Hw. rewrite Ews3 in Hw. unfold seq_writes in Hw.
      pose proof (ctx_slot_range (KUsage sc)) as SUr.
      assert (CS : caddr KSeq = LOCKA + 920) by (cbn; unfold C_SEQ; lia).
      assert (CU : forall j, caddr (KUseq j) = LOCKA + 856 + j) by (intros j; cbn; unfold C_USEQ; lia).
      assert (CG : forall c, caddr (KUsage c) = LOCKA + 472 + 8 * c) by (intros c; cbn; unfold C_USAGE; lia).
      assert (ECTX : CTX = LOCKA + 8) by (unfold CTX; lia).
      (* [comment removed for export] *)
      assert (STEPD : wlook wsu x = Some b -> exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (c' k) (x - caddr k)).
      { intros Hd0. destruct Hwsu as [(Ewsu & Hs48) | (Ewsu & Hs48)]; rewrite Ewsu in Hd0; [discriminate Hd0|].
        destruct (wlook_some_cov _ _ _ Hd0) as (w & [<- | []] & Hxw). cbn [f_a f_n] in Hxw.
        rewrite wlook_hit in Hd0 by (cbn [f_a f_n]; lia). injection Hd0 as <-. cbn [f_v f_a].
        exists (KUsage sc). cbn [clen c']. rewrite Z.eqb_refl, (proj2 (Z.ltb_lt sc 48) Hs48). cbn [andb]. split; [cbn; lia | split; [lia | reflexivity]]. }
      (* [comment removed for export] *)
      assert (STEPC : (((0 <=? d) && (d <=? 31))%bool = false \/ x <> caddr (KUseq d)) ->
                wlook (reset_writes reset ++ wsu) x = Some b -> exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (c' k) (x - caddr k)).
      { intros HxD Hc0. unfold reset_writes in Hc0. destruct reset.
        - cbn [app] in Hc0.
          destruct (Z.lt_ge_cases x (CTX + 848)) as [Hlo | Hlo]; [| destruct (Z.lt_ge_cases x (CTX + 880)) as [Hhi | Hhi]].
          + do 4 (rewrite wlook_skip in Hc0 by (cbn [f_a f_n]; lia)). exact (STEPD Hc0).
          + (* [comment removed for export] *)
            assert (Hb0 : b = 0).
            { destruct (Z.lt_ge_cases x (CTX + 872)); [destruct (Z.lt_ge_cases x (CTX + 864)); [destruct (Z.lt_ge_cases x (CTX + 856))|]|];
                repeat (rewrite wlook_skip in Hc0 by (cbn [f_a f_n]; lia)); rewrite wlook_hit in Hc0 by (cbn [f_a f_n]; lia);
                injection Hc0 as <-; cbn [f_v]; apply byte_of_zero. }
            subst b. exists (KUseq (x - (CTX + 848))). rewrite CU. cbn [clen c']. split; [cbn; lia|]. split; [lia|].
            replace ((x - (CTX + 848) =? d) && ((0 <=? d) && (d <=? 31)))%bool with false.
            2:{ symmetry. destruct HxD as [E | Hne]; [rewrite E; apply andb_false_r|]. rewrite CU in Hne. apply andb_false_intro1. apply Z.eqb_neq. lia. }
            replace (0 <=? x - (CTX + 848)) with true by (symmetry; apply Z.leb_le; lia).
            replace (x - (CTX + 848) <=? 31) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite byte_of_zero. reflexivity.
          + do 4 (rewrite wlook_skip in Hc0 by (cbn [f_a f_n]; lia)). exact (STEPD Hc0).
        - cbn [app] in Hc0. exact (STEPD Hc0). }
      (* [comment removed for export] *)
      assert (STEPB : (((0 <=? d) && (d <=? 31))%bool = false \/ x <> caddr (KUseq d)) ->
                wlook (FCT (caddr KSeq) 1 sq :: reset_writes reset ++ wsu) x = Some b -> exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (c' k) (x - caddr k)).
      { intros HxD Hb0. destruct (Z.eq_dec x (caddr KSeq)) as [-> | Hne].
        - rewrite wlook_hit in Hb0 by (cbn [f_a f_n]; lia). injection Hb0 as <-. cbn [f_v f_a]. exists KSeq. cbn [clen c']. split; [exact I|]. split; [lia | reflexivity].
        - rewrite wlook_skip in Hb0 by (cbn [f_a f_n]; lia). exact (STEPC HxD Hb0). }
      (* [comment removed for export] *)
      change ((if (0 <=? d) && (d <=? 31) then [FCT (caddr (KUseq d)) 1 sq] else []) ++ [FCT (caddr KSeq) 1 sq] ++ reset_writes reset)
        with ((if (0 <=? d) && (d <=? 31) then [FCT (caddr (KUseq d)) 1 sq] else []) ++ ([FCT (caddr KSeq) 1 sq] ++ reset_writes reset)) in Hw || idtac.
      destruct ((0 <=? d) && (d <=? 31))%bool eqn:Ed.
      - cbn [app] in Hw. rewrite <- app_assoc in Hw || idtac. cbn [app] in Hw.
        destruct (Z.eq_dec x (caddr (KUseq d))) as [-> | Hne].
        + rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia). injection Hw as <-. cbn [f_v f_a]. exists (KUseq d).
          apply andb_prop in Ed. destruct Ed as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
          cbn [clen c']. rewrite Z.eqb_refl. replace (0 <=? d) with true by (symmetry; apply Z.leb_le; lia). replace (d <=? 31) with true by (symmetry; apply Z.leb_le; lia).
          cbn [andb]. split; [cbn; lia|]. split; [lia | reflexivity].
        + rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia). apply (STEPB (or_intror Hne)). exact Hw.
      - cbn [app] in Hw. rewrite <- app_assoc in Hw || idtac. apply (STEPB (or_introl eq_refl)). exact Hw. }
    assert (HR3 : Rep A3 (ms_mem s4)).
    { apply (commit_heur A2 c' (ms_mem s1) ws3 (ms_mem s4) HWA2 Hheur Hnn RW4 LOOK).
      (* [comment removed for export] *)
      intros k Hk Hne x Hx.
        assert (CV : forall a n v, In (FCT a n v) ws3 -> a <= x < a + n -> wlook ws3 x <> None).
        { intros a n v Hin Hax. apply (wlook_cov_some ws3 (FCT a n v) x Hin). cbn [f_a f_n]. exact Hax. }
        rewrite Ews3 in CV |- *. destruct k; cbn [c'] in Hne; try (exfalso; exact (Hne eq_refl)); cbn [caddr clen] in Hx.
        + (* [comment removed for export] *) apply (CV (caddr KSeq) 1 sq); [| cbn [caddr]; lia]. unfold seq_writes. rewrite !in_app_iff. left. right. left. left. reflexivity.
        + (* [comment removed for export] *) destruct ((i =? sc) && (sc <? 48))%bool eqn:E; [| exfalso; exact (Hne eq_refl)].
          apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. subst i.
          apply (CV (caddr (KUsage sc)) 8 (usage_of A1 sc - cnt)); [| cbn [caddr]; lia].
          rewrite in_app_iff. right. destruct Hwsu as [(-> & Hs) | (-> & Hs)]; [lia | left; reflexivity].
        + (* [comment removed for export] *) cbn in Hk.
          destruct ((i =? d) && ((0 <=? d) && (d <=? 31)))%bool eqn:E.
          * apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. subst i.
            apply (CV (caddr (KUseq d)) 1 sq); [| cbn [caddr]; lia]. unfold seq_writes. rewrite E2. rewrite !in_app_iff. left. left. left. reflexivity.
          * destruct (reset && ((0 <=? i) && (i <=? 31)))%bool eqn:E2; [| exfalso; exact (Hne eq_refl)].
            apply andb_prop in E2. destruct E2 as [Er _].
            assert (Hm4 : exists m4, (m4 = 0 \/ m4 = 8 \/ m4 = 16 \/ m4 = 24) /\ CTX + 848 + m4 <= x < CTX + 848 + m4 + 8).
            { unfold C_USEQ, CTX in *. destruct (Z.lt_ge_cases i 8); [exists 0 | destruct (Z.lt_ge_cases i 16); [exists 8 | destruct (Z.lt_ge_cases i 24); [exists 16 | exists 24]]]; lia. }
            destruct Hm4 as (m4 & Hm4 & Hxm). apply (CV (CTX + 848 + m4) 8 0); [| lia].
            unfold seq_writes. rewrite Er. rewrite !in_app_iff. left. right. right. cbn.
            destruct Hm4 as [-> | [-> | [-> | ->]]]; [right; right; right; left | right; right; left | right; left | left]; f_equal; lia. }
    (* [comment removed for export] *)
    pose proof (IS_commit sp0 argv envp cb A2 A3 s1 ws3 (ms_mem s4) HIS2 RW4 WO3 HW3 HR3) as HIS3.
    assert (Es4 : upd s1 (ms_mem s4) (ms_vm s1) = s4) by (destruct s4; unfold upd; cbn in *; subst; reflexivity).
    rewrite Es4 in HIS3.
    pose proof (ntframe_commit A2 s1 ws3 (ms_mem s4) HWA2 RW4 WO3) as HF3. rewrite Es4 in HF3.
    assert (A3_meta : forall x, a_meta A3 x = a_meta A2 x) by (intros x; reflexivity).
    assert (HU3 : forall c, usage_of A3 c = usage_of A2 c).
    { intros c. apply usage_of_ext; [reflexivity|]. intros x. unfold meta_usage. rewrite A3_meta. reflexivity. }
    assert (HII3 : II sp0 argv envp cb (ma :: D) A3 s4).
    { apply II_intro; [exact HIS3 | | | |].
      - rewrite Hvm4. unfold A3. apply (VMok_ctx_heur A2 c' Hheur). unfold A2. apply (VMok_disA A1 ma mt Hma). exact (ii_vm HII).
      - apply (AvOK_transfer A1 A3 (ii_av HII)); [reflexivity | reflexivity |].
        intros x mt' Hx Hrl. rewrite A3_meta in Hx. destruct (dis_meta_inv A1 ma mt x mt' Hx) as [(-> & ->) | (Hne & Hx0)]; [cbn in Hrl; discriminate | exists mt'; auto].
      - intros c Hc. rewrite HU3, usage_of_A2. change (a_ctx A3 (KUsage c)) with (c' (KUsage c)). cbn [c'].
        destruct (Z.eqb_spec c sc) as [-> | Hne].
        + rewrite (proj2 (Z.ltb_lt sc 48) ltac:(lia)). cbn [andb]. rewrite ?Z.eqb_refl. destruct (usage_now ltac:(lia)) as [EU _]. lia.
        + cbn [andb]. rewrite ?(proj2 (Z.eqb_neq c sc) Hne). rewrite ?(proj2 (Z.eqb_neq sc c) ltac:(intros E; apply Hne; symmetry; exact E)). change (a_ctx A2 (KUsage c)) with (a_ctx A1 (KUsage c)). rewrite (ii_us HII c Hc). lia.
      - intros x. rewrite A3_meta. split.
        + intros (mt' & Hx & Hrl). destruct (dis_meta_inv A1 ma mt x mt' Hx) as [(-> & ->) | (Hne & Hx0)]; [left; reflexivity | right].
          apply (proj1 (ii_dd HII x)). exists mt'. auto.
        + intros [<- | Hin]; [exists (mtD mt); split; [exact Hma2 | reflexivity] |].
          destruct (proj2 (ii_dd HII x) Hin) as (mt' & Hx & Hrl). exists mt'. split; [| exact Hrl].
          apply (dis_old A1 ma mt x mt' Hx). intros ->. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrl. discriminate. }
    pose proof (is_rep _ _ _ _ _ _ HIS3) as HR3'. pose proof (is_wf _ _ _ _ _ _ HIS3) as HW3'.
    (* [comment removed for export] *)
    rewrite !at_Z. change (ma + 32) with (ma + moff FW32).
    assert (Hma3 : a_meta A3 ma = Some (mtD mt)) by (rewrite A3_meta; exact Hma2).
    reassoc. eapply (ts_ld_meta A3 HW3'); [exact HR3' | exact HWIN4 | exact Hma3 | reflexivity | rewrite mtD_f; change (mt_f mt FW32) with W; lia |].
    rewrite mtD_f. change (mt_f mt FW32) with W. reassoc. change (ma + 16) with (ma + moff FMem).
    eapply (ts_ld_meta A3 HW3'); [exact HR3' | exact HWIN4 | exact Hma3 | reflexivity | rewrite mtD_f; change (mt_f mt FMem) with mem; lia |].
    rewrite mtD_f. change (mt_f mt FMem) with mem. reassoc.
    (* [comment removed for export] *)
    apply (ts_free_meta sp0 argv envp cb D A3 s4 ma (mtD mt) HII3 ma_notin_D Hma3 eq_refl).
    intros s5 HII5 HF5. apply ts_ret' || apply ts_bind_ret.
    rewrite PAGEMASK_eq, v_and_Z, land_pagemask by lia. change (W / 4096) with (mt_maplen mt). replace (4096 * mt_maplen mt) with L by lia.
    set (A4 := fmA A3 ma (a_freelist A3) (hd ma (a_freelist A3)) (last (a_freelist A3) ma)) in HII5.
    pose proof (fmrel sp0 argv envp cb D A3 s4 ma (mtD mt) HII3 Hma3 eq_refl) as (L5 & Ar5 & P5 & B5 & X5 & Ac5 & C5 & G5 & Gi5 & D5). fold A4 in L5, Ar5, P5, B5, X5, Ac5, C5, G5, Gi5, D5.
    assert (OWN21 : forall x, owned_of A2 x -> owned_of A1 x) by (intros x [Hx | Hx]; [left; exact Hx | right; exact (dom_disA A1 ma mt x Hx)]).
    assert (HF15 : ntframe A1 s1 s5).
    { apply (ntframe_trans A1 A3 s1 s4 s5); [| exact HF5 | exact OWN21 | reflexivity].
      apply (ntframe_trans A1 A2 s1 s1 s4 (ntframe_refl A1 s1) HF3 OWN21 eq_refl). }
    pose proof (ii_vm HII5) as HV5. rewrite (nf_vm _ _ _ HF5), Hvm4 in HV5.
    apply (HK s5 A4 HII5 HF15).
    - (* [comment removed for export] *) constructor.
      + exact L5. + exact Ar5. + exact P5. + exact B5.
      + intros k Hk. rewrite C5 by (destruct k; cbn in Hk; try discriminate; try (intros c; discriminate); destruct Hk).
        change (a_ctx A3 k) with (c' k). destruct k; cbn [c']; try reflexivity; destruct Hk.
      + intros c Hc. rewrite Ac5. reflexivity.
      + intros x mtx aibx slx Hx Hrx. pose proof (Gi5 x mtx aibx slx Hx Hrx) as Hx3. rewrite A3_meta in Hx3.
        destruct (dis_group_inv A1 ma mt x mtx aibx slx Hx3 Hrx) as [Hx1 Hne]. split; [exact Hne|]. exists mtx, slx. auto 10.
      + intros x Hx. apply (dom_disA A1 ma mt x). apply D5. exact Hx.
      + exists [ma]. unfold A4. rewrite fmA_freelist. reflexivity.
    - (* [comment removed for export] *)
      right. exists mem, L. split; [reflexivity|]. split; [lia|]. split; [exact Hpal|]. split; [rewrite EL; apply Z_mod_mult|]. split; [exact Hhr|].
      destruct (vm_grp A1 (ms_vm s1) (ii_vm HII) ma mt aib slots Hma Hr Hml) as [Hin1 Hrf1]. fold mem L in Hin1, Hrf1.
      split; [rewrite X5; reflexivity|]. split; [exact Hin1|].
      split. { intros x. split.
        - intros Hx. destruct (dom_disA_back A1 ma mt Hma x Hx) as [Hd | Hrg]; [left; apply D5; exact Hd | right; exact Hrg].
        - intros [Hx | Hx]; [apply (dom_disA A1 ma mt x); apply D5; exact Hx | right; left; exists ma, mt, aib, slots; auto]. }
      split. { intros x Hx Hd. apply (dis_nodom x); [apply D5; exact Hd | exact Hx]. }
      split. { intros f x Hf Hfx.
        destruct (has_fmA A3 HW3' ma (mtD mt) (a_freelist A3) _ _ Hma3 eq_refl eq_refl eq_refl eq_refl f Hf) as [Hf3 | [-> | [(fld & ->) | (_ & Hc)]]].
        - destruct (has_set_ctx A2 c' f Hf3) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hm | Hg]]]].
          + apply (ctx_avoid k x Hk). exact Hfx.
          + apply (dis_fact_avoid f x); [right; left; exact Har | exact Hfx].
          + cbn [f_a f_n] in Hfx. apply (dis_nodom x). left. exists pg. split; [exact Hpg | lia].
          + apply (dis_fact_avoid f x); [right; right; left; exact Hm | exact Hfx].
          + apply (dis_fact_avoid f x); [right; right; right; exact Hg | exact Hfx].
        - cbn [f_a f_n] in Hfx. apply (ctx_avoid KFmh x I). cbn [clen]. exact Hfx.
        - cbn [f_a f_n] in Hfx. pose proof (mfield_range fld). apply (meta_avoid ma x); [rewrite Hma2; discriminate | lia].
        - assert (FL : forall y, In y (a_freelist A3) -> a_meta A2 y <> None).
          { intros y Hy. destruct (proj1 (wf_fl_mem A3 HW3' y) Hy) as (mty & Hmy & _). rewrite A3_meta in Hmy. rewrite Hmy. discriminate. }
          destruct Hc as [-> | ->]; cbn [f_a f_n] in Hfx.
          + assert (Hy : a_meta A2 (hd ma (a_freelist A3)) <> None).
            { destruct (a_freelist A3) as [|y l]; cbn [hd]; [unfold A2; rewrite (dis_meta_same A1 ma mt); discriminate | apply FL; left; reflexivity]. }
            exact (meta_avoid _ x Hy ltac:(lia)).
          + assert (Hy : a_meta A2 (last (a_freelist A3) ma) <> None).
            { destruct (list_eq_dec Z.eq_dec (a_freelist A3) []) as [El | El]; [rewrite El; cbn; rewrite aupd_same; discriminate | apply FL; apply last_In_ne; exact El]. }
            exact (meta_avoid _ x Hy ltac:(lia)). }
      split. { apply WF_set_xmaps. exact (is_wf _ _ _ _ _ _ (ii_is HII5)). }
      apply (VMok_munmap_xmap A4 (ms_vm s1) mem L (a_xmaps A1) (is_wf _ _ _ _ _ _ (ii_is HII5)) HV5); [rewrite X5; reflexivity | lia | lia | lia | exact Hin1 | exact Hrf1 |].
      intros x Hx Hd. apply (dis_nodom x); [apply D5; exact Hd | exact Hx].
  Qed.
End FgRoot.

End WithLayout.

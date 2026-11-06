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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_steps MallocInv_repw MallocInv_sc3 MallocInv_ntq MallocInv_aspieces MallocInv_wf7.
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

(* [comment removed for export] *)
Definition heap_bytes (a n : Z) : Prop := 0x1000 <= a /\ a + n <= alloc_ceiling /\ (a + n <= IMG_LO \/ IMG_HI <= a).

Section StepsM.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  (* [comment removed for export] *)
  Lemma ts_st_mapw : forall s (m0 : word -> option byte) ws n a v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> (0 < n)%nat -> heap_bytes a (Z.of_nat n) ->
    (forall j, 0 <= j < Z.of_nat n -> m0 (Z_to_bv 64 (a + j)) <> None) ->
    (forall m', RepW A m0 (FCT a (Z.of_nat n) (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof using MLok. pu_keep (MLok).
    intros s m0 ws n a v k P HR HWn Hn (Ha & Hc & Hi) Hm Hk. ceil.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWn | lia | lia | lia].
    - apply st_zone_heap; lia.
    - apply store_ok_of_all; [rewrite uZ by lia; lia|]. intros y Hy. rewrite uZ in Hy by lia. unfold wview.
      pose proof (rw_mapped A m0 ws (ms_mem s) HR y) as M.
      specialize (M ltac:(replace y with (Z_to_bv 64 (a + (bv_unsigned y - a))) by (rewrite <- (Z_to_bv_bv_unsigned 64 y) at 2; f_equal; lia); apply Hm; lia)).
      destruct (ms_mem s y); [discriminate | exfalso; exact (M eq_refl)].
    - apply Hk. apply repw_store; [exact HR | lia | lia | unfold wzone; cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lbu_mapw : forall s (m0 : word -> option byte) ws a (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> heap_bytes a 1 -> m0 (Z_to_bv 64 a) <> None ->
    (forall b, 0 <= b < 256 -> tsafe (k (Z_to_bv 64 b) s) P) ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof using Type. pu_keep tt.
    intros s m0 ws a k P HR HWn (Ha & Hc & Hi) Hm Hk. ceil.
    pose proof (rw_mapped A m0 ws (ms_mem s) HR (Z_to_bv 64 a) Hm) as M.
    destruct (ms_mem s (Z_to_bv 64 a)) as [b|] eqn:E; [| exfalso; exact (M eq_refl)].
    eapply (ts_lbu a b).
    - apply acc_ok_heap; [exact HWn | lia | lia | lia].
    - rewrite rdn1_eq, E. reflexivity.
    - apply Hk. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. lia.
  Qed.
End StepsM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wfree_range_sub : forall ws a n a' n', wfree_range ws a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wfree_range ws a' n'.
Proof using Type. pu_keep tt.
  intros ws a n a' n' H Ha Hn Hn'. unfold wfree_range in *. eapply Forall_impl; [| exact H]. cbn. intros w Hw. lia.
Qed.

Lemma caddr_usage : forall sc, caddr (KUsage sc) = LOCKA + 8 * sc + 472.
Proof using Type. pu_keep tt. intros sc. cbn. unfold C_USAGE. lia. Qed.
Lemma caddr_active : forall sc, caddr (KActive sc) = LOCKA + 8 * sc + 88.
Proof using Type. pu_keep tt. intros sc. cbn. unfold C_ACTIVE. lia. Qed.

Section Tail.
  Context {R : Type}.
  Variables (A : astate) (m : Z) (md : meta_rec) (sc cnt aidx p Wm : Z).
  Hypothesis HW : WF A.
  Hypothesis Hm : a_meta A m = Some md.
  Hypothesis Hprev : mt_f md FPrev = 0.
  Hypothesis Hnext : mt_f md FNext = 0.
  Hypothesis HWm : mt_f md FW32 = Wm.
  Hypothesis HWm_rng : 0 <= Wm < 2^62.
  Hypothesis HWm_pg : Wm mod 4096 = 0.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact0 : a_ctx A (KActive sc) = 0.
  Hypothesis Hcnt : 1 <= cnt <= 32.
  Hypothesis Haidx : 0 <= aidx <= cnt - 1.
  Hypothesis Hus : a_ctx A (KUsage sc) + cnt < 2^63.
  Hypothesis Hp : heap_bytes p 16.
  Hypothesis Hpm : p + 16 <= m \/ m + 40 <= p.

  (* [comment removed for export] *)
  Definition tail_ws (ab av1 fr av2 : Z) : list fct :=
    [FCT (caddr (KActive sc)) 8 m; FCT (m + 8) 8 m; FCT m 8 m;
     FCT (m + 24) 4 av2;
     FCT (m + 32) 8 (iw32 Wm sc cnt);
     FCT (p + 8) 1 (Z.lor aidx (Z.land ab 224)); FCT p 8 m;
     FCT (m + 16) 8 p;
     FCT (m + 28) 4 fr; FCT (m + 24) 4 av1;
     FCT (caddr (KUsage sc)) 8 (a_ctx A (KUsage sc) + cnt)].


  Theorem ts_as_tail : forall s (m0 : word -> option byte) ws (K : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s ->
    (forall j, 0 <= j < 16 -> m0 (Z_to_bv 64 (p + j)) <> None) ->
    wfree_range ws m 16 -> wfree_range ws (m + 32) 8 ->
    wfree_range ws (caddr (KUsage sc)) 8 -> wfree_range ws (caddr (KActive sc)) 8 ->
    (forall m' ab av1 fr av2, 0 <= ab < 256 ->
       av1 mod 2^32 = 2^(aidx + 1) - 1 -> fr mod 2^32 = ifr cnt aidx -> av2 mod 2^32 = iav cnt aidx ->
       0 <= av1 -> 0 <= fr -> 0 <= av2 ->
       RepW A m0 (tail_ws ab av1 fr av2 ++ ws) m' ->
       tsafe (K (Z_to_bv 64 0) (upd s m' (ms_vm s))) P) ->
    tsafe ((r <- as_tail (Z_to_bv 64 sc) (Z_to_bv 64 m) (Z_to_bv 64 p) (Z_to_bv 64 aidx) (Z_to_bv 64 cnt)
                        (Z_to_bv 64 (LOCKA + 8 * sc)) (Z_to_bv 64 (caddr (KActive sc))) ;; K r) s) P.
  Proof using HW HWm HWm_pg HWm_rng Hact0 Haidx Hcnt Hm Hnext Hp Hpm Hprev Hsc Hus MLok. pu_keep (HW, HWm, HWm_pg, HWm_rng, Hact0, Haidx, Hcnt, Hm, Hnext, Hp, Hpm, Hprev, Hsc, Hus, MLok).
    intros s m0 ws K P RW HWIN Hmap Hf16 Hf32 Hfus Hfact HK.
    pose proof (meta_facts A m md HW Hm) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS.
    pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (U1 & U2 & U3). cbn [clen] in U2, U3.
    pose proof (ctx_slot_range (KActive sc) ltac:(cbn; lia)) as (C1 & C2 & C3). cbn [clen] in C2, C3. unfold CTX_END in U2, C2.
    pose proof (wf_ctx_nonneg A HW (KUsage sc)) as Hus0. pose proof (caddr_usage sc) as CU. pose proof (caddr_active sc) as CA.
    destruct Hp as (P1 & P2 & P3).
    pose proof (masks_facts cnt aidx Hcnt Haidx) as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
    pose proof (pow2_le32 (aidx + 1) ltac:(lia)) as Hp2. rewrite (iav_eq cnt aidx Hcnt Haidx) in *.
    assert (Hm64 : 0 <= m < 2^64) by lia. assert (Hp64 : 0 <= p < 2^64) by lia.
    unfold as_tail.
    (* [comment removed for export] *)
    rewrite !(at_Z m), !(at_Z (LOCKA + 8 * sc)), <- (caddr_usage sc). reassoc.
    eapply (ts_ld_ctxfW A HW s m0 ws (KUsage sc)); [exact RW | exact HWIN | cbn; lia | reflexivity | exact Hfus |].
    reassoc. rewrite (v_add_Z (a_ctx A (KUsage sc)) cnt).
    eapply (ts_sd_ctxW A s m0 ws (KUsage sc)); [exact RW | exact HWIN | cbn; lia | reflexivity |]. intros m1 RW1. rewrite uZ in RW1 by lia.
    (* [comment removed for export] *)
    reassoc. unfold m_sw at 1.
    eapply (ts_st_domW A HW _ m0 _ 4 (m + 24)); [exact RW1 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |]. intros m2 RW2.
    set (av1 := bv_unsigned (v_addi (v_sllw (wlit 2) (Z_to_bv 64 aidx)) (-1))) in RW2.
    assert (Hav1 : av1 mod 2^32 = 2^(aidx+1) - 1) by (unfold av1; apply tail_av_word; lia).
    pose proof (u64_range (v_addi (v_sllw (wlit 2) (Z_to_bv 64 aidx)) (-1))) as Hav1r. fold av1 in Hav1r.
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_lw_wrw A _ m0 _ (m + 24) av1); [exact RW2 | exact HWIN | lia | lia | lia | |].
    { intros j Hj. rewrite wlook_hit by (cbn [f_a f_n]; lia). cbn [f_v f_a]. do 2 f_equal. lia. }
    rewrite <- (w32_mod av1), Hav1.
    (* [comment removed for export] *)
    reassoc. unfold m_sw at 1.
    eapply (ts_st_domW A HW _ m0 _ 4 (m + 28)); [exact RW2 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |]. intros m3 RW3.
    set (fr := bv_unsigned (v_add (v_sllw (wlit 2) (v_addi (Z_to_bv 64 cnt) (-1))) (v_xori (w32 (2 ^ (aidx + 1) - 1)) (-1)))) in RW3.
    assert (Hfr : fr mod 2^32 = ifr cnt aidx) by (unfold fr; rewrite (ifr_eq cnt aidx Hcnt Haidx); apply tail_fr_word; lia).
    pose proof (u64_range (v_add (v_sllw (wlit 2) (v_addi (Z_to_bv 64 cnt) (-1))) (v_xori (w32 (2 ^ (aidx + 1) - 1)) (-1)))) as Hfrr. fold fr in Hfrr.
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_sd_metaW A HW _ m0 _ m md 16); [exact RW3 | exact HWIN | exact Hm | lia | lia |]. intros m4 RW4. rewrite uZ in RW4 by lia.
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_st_mapw A _ m0 _ 8 p); [exact RW4 | exact HWIN | lia | split; [| split]; lia | intros j Hj; apply Hmap; lia |]. intros m5 RW5.
    rewrite uZ in RW5 by lia. change (Z.of_nat 8) with 8 in RW5.
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_ld_wrw A _ m0 _ (m + 16) p); [exact RW5 | exact HWIN | lia | lia | lia | |].
    { intros j Hj. rewrite wlook_skip by (cbn [f_a f_n]; lia). rewrite wlook_hit by (cbn [f_a f_n]; lia). cbn [f_v f_a]. do 2 f_equal. lia. }
    (* [comment removed for export] *)
    reassoc. rewrite !(at_Z p).
    eapply (ts_lbu_mapw A _ m0); [exact RW5 | exact HWIN | split; [| split]; lia | apply Hmap; lia |]. intros ab Hab.
    (* [comment removed for export] *)
    reassoc. destruct (tail_aib_word ab aidx Hab ltac:(lia)) as (Eaib & Haibr & Haibm). rewrite Eaib. unfold m_sb at 1.
    eapply (ts_st_mapw A _ m0 _ 1 (p + 8)); [exact RW5 | exact HWIN | lia | split; [| split]; lia | intros j Hj; rewrite <- Z.add_assoc; apply Hmap; lia |]. intros m6 RW6.
    rewrite uZ in RW6 by lia. change (Z.of_nat 1) with 1 in RW6.
    (* [comment removed for export] *)
    reassoc. change (m + 32) with (m + moff FW32) at 1.
    eapply (ts_ld_metaW A HW _ m0 _ m md FW32); [exact RW6 | exact HWIN | exact Hm | reflexivity | | rewrite HWm; lia |].
    { cbn [moff]. repeat (apply wfree_range_cons; [cbn [f_a f_n]; lia|]). exact Hf32. }
    rewrite HWm.
    (* [comment removed for export] *)
    reassoc. rewrite tail_w32_word by lia.
    replace (4096 * (Wm / 4096)) with Wm by (rewrite (Z_div_exact_full_2 Wm 4096) at 1 by lia; lia).
    eapply (ts_sd_metaW A HW _ m0 _ m md 32); [exact RW6 | exact HWIN | exact Hm | lia | lia |]. intros m7 RW7.
    rewrite uZ in RW7 by (unfold iw32 in *; lia). replace (Wm + 64 * sc + 32 + (cnt - 1)) with (iw32 Wm sc cnt) in RW7 by reflexivity.
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_lw_wrw A _ m0 _ (m + 24) av1); [exact RW7 | exact HWIN | lia | lia | lia | |].
    { intros j Hj. do 5 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). cbn [f_v f_a]. do 2 f_equal. lia. }
    rewrite <- (w32_mod av1), Hav1.
    (* [comment removed for export] *)
    reassoc. unfold m_sw at 1.
    eapply (ts_st_domW A HW _ m0 _ 4 (m + 24)); [exact RW7 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |]. intros m8 RW8.
    set (av2 := bv_unsigned (v_addi (w32 (2 ^ (aidx + 1) - 1)) (-1))) in RW8.
    assert (Hav2 : av2 mod 2^32 = 2^(aidx+1) - 2) by (unfold av2; rewrite tail_avdec_word by lia; lia).
    pose proof (u64_range (v_addi (w32 (2 ^ (aidx + 1) - 1)) (-1))) as Hav2r. fold av2 in Hav2r.
    (* [comment removed for export] *)
    reassoc. change (m + 8) with (m + moff FNext) at 1.
    eapply (ts_ld_metaW A HW _ m0 _ m md FNext); [exact RW8 | exact HWIN | exact Hm | reflexivity | | rewrite Hnext; lia |].
    { cbn [moff]. repeat (apply wfree_range_cons; [cbn [f_a f_n]; lia|]). eapply wfree_range_sub; [exact Hf16 | lia | lia | lia]. }
    rewrite Hnext. reassoc. apply ts_assert; [reflexivity|].
    (* [comment removed for export] *)
    reassoc. replace (Z_to_bv 64 m) with (Z_to_bv 64 (m + moff FPrev)) at 1 by (cbn [moff]; f_equal; lia).
    eapply (ts_ld_metaW A HW _ m0 _ m md FPrev); [exact RW8 | exact HWIN | exact Hm | reflexivity | | rewrite Hprev; lia |].
    { cbn [moff]. repeat (apply wfree_range_cons; [cbn [f_a f_n]; lia|]). eapply wfree_range_sub; [exact Hf16 | lia | lia | lia]. }
    rewrite Hprev. reassoc. apply ts_assert; [reflexivity|].
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_ld_ctxfW A HW _ m0 _ (KActive sc)); [exact RW8 | exact HWIN | cbn; lia | reflexivity | |].
    { repeat (apply wfree_range_cons; [cbn [f_a f_n]; lia|]). exact Hfact. }
    rewrite Hact0. rewrite is0_Z by lia. cbn [Z.eqb].
    reassoc. reassoc. replace (Z_to_bv 64 m) with (Z_to_bv 64 (m + 0)) at 1 by (f_equal; lia).
    eapply (ts_sd_metaW A HW _ m0 _ m md 0); [exact RW8 | exact HWIN | exact Hm | lia | lia |]. intros m9 RW9. rewrite uZ in RW9 by lia. rewrite Z.add_0_r in RW9.
    reassoc.
    eapply (ts_sd_metaW A HW _ m0 _ m md 8); [exact RW9 | exact HWIN | exact Hm | lia | lia |]. intros m10 RW10. rewrite uZ in RW10 by lia.
    eapply (ts_sd_ctxW A _ m0 _ (KActive sc)); [exact RW10 | exact HWIN | cbn; lia | reflexivity |]. intros m11 RW11. rewrite uZ in RW11 by lia.
    apply ts_bind_ret. change w0 with (Z_to_bv 64 0).
    apply (HK m11 ab av1 fr av2 Hab Hav1 Hfr); [rewrite Hav2; reflexivity | lia | lia | lia |].
    exact RW11.
  Qed.
End Tail.

End WithLayout.

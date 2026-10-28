(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjStage2 SjLeaves SjNumber SjTape SjTapeInv SjTapeTile SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout F_memset Sj_iface Sj_kit Sj_new Sj_h_kit Sj_stage2_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_iface Sj_stage2_defs Sj_stage2_exit Sj_stage2_docend
  Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numr_defs Sj_stage2_numr Sj_stage2_rootkit
  Sj_stage2_entry Sj_stage2_adapt.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section RootArm.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma root_del_call : forall (E : s2env) LB B cap s1 p CP c (POST : unit -> PState -> machine_state -> Prop) (X : list (Z * Z)) m
      nxt sl sc (RA : Z) xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      (F : bvmap 5 word) (fc : bv 32) (m5 : mem) errv,
    env_ok E -> env_heap E LB B cap ->
    X = s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E) ->
    RHEAP s1 ((p, CP, c) :: LB) (e_m0 E) -> rauxv_ok (e_m0 E) B -> rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] ->
    lx_pres LB (bv_unsigned (e_sp E)) X m (e_m0 E) ->
    e_lo E <= e_SP E - RFREE_STACK ->
    0 <= RA < 2^64 -> RA mod 2 = 0 -> cells_size sl = 80%nat ->
    MEMI E nxt sl sc fc m5 ->
    (forall s2' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m6,
        MEMI (s2_rebase E m6) nxt sl sc fc m6 ->
        RHEAP s2' LB m6 -> rauxv_ok m6 B -> rw_cells usegs m6 LX_ERRNO [C4 errv] ->
        ps_fa s2' = ps_fa s1 -> ps_so s2' = ps_so s1 ->
        lx_pres LB (bv_unsigned (e_sp E)) X m m6 ->
        evt usegs (POST tt s2')
          (S2R E RA (Z_to_bv 64 RA) yt0 yt1 yt2 xs0 xs1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F fc m6)) ->
    implM usegs (del lops p) s1 POST
      (S2R E SJ_OPDEL_ARR (Z_to_bv 64 RA) xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 CP) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m5).
  Proof using HF.
    intros E LB B cap s1 p CP c POST X m nxt sl sc RA xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
           F fc m5 errv OK EH -> HEAP AUX ERR PRES HLO HRA HRA2 HSL HMEM K.
    pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & ST & _).
    pose proof (ok_room _ OK) as HRM. unfold S2_STACK in HRM.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ok_glo _ OK) as G.
    assert (EH' : env_heap E ((p, CP, c) :: LB) B cap).
    { apply env_heap_cons; [exact EH|]. intros a Ha.
      pose proof (LH_block_range _ _ _ _ HEAP (or_introl eq_refl)) as (_ & _ & _ & BC & _). cbn [blk_addr blk_size fst snd] in *. lia. }
    assert (HEAP5 : RHEAP s1 ((p, CP, c) :: LB) m5) by (eapply s2_heap_frame; [exact EH'| exact HEAP| exact MU| exact WM]).
    assert (AUX5 : rauxv_ok m5 B) by (eapply s2_auxv_frame; [exact OK| exact EH| exact AUX| exact MU| exact WM]).
    assert (ERR5 : rw_cells usegs m5 LX_ERRNO [C4 errv]).
    { eapply (s2_static_frame E LB B cap _ _ LX_ERRNO); [exact OK| exact EH| | | exact ERR| exact MU| exact WM];
        unfold LX_ERRNO, RATP; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (PRES5 : lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) m m5).
    { eapply lx_pres_trans; [exact PRES| eapply s2_lx_pres_munch; [exact OK| exact EH| exact MU| exact WM]]. }
    rewrite (eh_tp _ _ _ _ EH).
    eapply implM_post_evt.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := e_lo E) (LB := (p, CP, c) :: LB) (A := CP) (n := c);
        [exact HEAP5 | left; reflexivity | exact AUX5 | destruct (eh_B _ _ _ _ EH); lia | exact ST | exact (eh_ceil _ _ _ _ EH) | exact HLO
        | exact ERR5 | exact MI | lia]. }
    cbv beta. intros [] s2' ms' PO. unfold free_postZ in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
    assert (ND : List.NoDup (map blk_id ((p, CP, c) :: LB))) by (eapply LH_nodup; exact HEAP5).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact HRA2]).
    rewrite <- (eh_tp _ _ _ _ EH).
    eapply (K s2'); [ | exact HEAP6 | exact AUX6 | exact ERR6 | exact FA6 | exact SO6 | ].
    - eapply (MEMI_rebase_agree _ E nxt sl sc fc m5 m6 (agree_of_heap_pres _ _ _ _ HP6)); [ | exact HSL | exact HMEM | exact MI6 | exact ST6].
      intros a Ha. eapply s2_region_client; [exact OK| exact EH| exact Ha].
    - eapply lx_pres_trans; [exact PRES5|]. apply lx_pres_of_heap_pres.
      eapply rheap_pres_weaken; [exact HP6| lia| auto].
  Qed.

  Lemma root_tail_exit : forall E LB B cap s s' m errv err x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    env_ok E -> env_heap E LB B cap ->
    RHEAP s' LB (e_m0 E) -> rauxv_ok (e_m0 E) B -> rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] ->
    lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) m (e_m0 E) ->
    ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    s2_errok E err ->
    MEMX E fc m1 ->
    evt usegs (flat_post E LB B cap s m tt s')
      (S2R E 0x4be14 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 err) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m1).
  Proof.
    intros until m1. intros OK EH HEAP AUX ERR PRES FA SO HERR HMX.
    eapply evt_mono; [eapply (s2_exit E OK); [exact HERR| exact HMX]|].
    intros ms' HP. eapply s2_post_conv; eassumption.
  Qed.

  Lemma tape_ok_rootnum : forall h v r, num_word v -> tape_ok (zupd ([h; v; r] ++ [tword t_root 0]) (Z.to_nat 0) (tword t_root (3 + 1))) ([] ++ []).
  Proof.
    intros h v r Hv. unfold tape_ok.
    change (tape_wfS (Tf [tword t_root (3 + 1); v; r; tword t_root 0]) (Tf []) 0 ck_any 4).
    unfold tape_wfS. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
    apply elemS_scalar. right. left. split; [reflexivity|]. split; [exact Hv| reflexivity].
  Qed.

  Lemma root_tail_doc : forall E LB B cap s s' m errv h0 v r xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j56 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    env_ok E -> env_heap E LB B cap ->
    RHEAP s' LB (e_m0 E) -> rauxv_ok (e_m0 E) B -> rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] ->
    lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) m (e_m0 E) ->
    ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    is_numstart (e_tok E 0) = true ->
    e_tws E = [h0; v; r] -> num_word v -> e_sbs E = [] ->
    MEMI E (e_nxt0 E) (DSL E j0 j8 j16 j24 j32 j56 j72) [] fc m1 ->
    evt usegs (flat_post E LB B cap s m tt s')
      (S2R E 0x47028 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof.
    intros until m1. intros OK EH HEAP AUX ERR PRES FA SO HNUM ETWS Hv ESBS HMEM.
    assert (KX : forall tws sbs, exit_k (s2_ghost E tws sbs) (s2_post E)).
    { intros tws sbs. unfold exit_k. intros. eapply (s2_exit (s2_ghost E tws sbs)); [apply env_ok_ghost; exact OK | eassumption | eassumption]. }
    assert (HI : Inv (e_bs E) (e_idxs E) DocEnd (mkst 1 0 3 0 [])).
    { eapply step_inv; [exact (ok_s1 _ OK) | exact (st_doc _ _ (s0) _ _ (v_number _ _ DocEnd s0 HNUM)) | apply Inv_s0; exact (ok_s1 _ OK)]. }
    eapply evt_mono; [eapply (seg_doc_end E OK (s2_post E) (mkst 1 0 3 0 [])); [exact HI| exact HMEM| cbn [W]; rewrite ETWS; reflexivity | apply KX |]|].
    { unfold docend_env, gpatch, gapp. cbn [e_tws e_sbs s2_ghost W]. rewrite ETWS, ESBS. apply tape_ok_rootnum. exact Hv. }
    intros ms' HP. eapply s2_post_conv; eassumption.
  Qed.

  Section Sites.
    Variables (E : s2env) (LB : list block) (B cap : Z) (s s1 : PState) (p : bptr) (CP c : Z) (m : mem) (errv : word).
    Hypothesis OK : env_ok E.
    Hypothesis EH : env_heap E LB B cap.
    Hypothesis HEAP : RHEAP s1 ((p, CP, c) :: LB) (e_m0 E).
    Hypothesis AUX : rauxv_ok (e_m0 E) B.
    Hypothesis ERR : rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv].
    Hypothesis PRES : lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) m (e_m0 E).
    Hypothesis HLO : e_lo E <= e_SP E - RFREE_STACK.
    Hypothesis FA : ps_fa s1 = ps_fa s.
    Hypothesis SO : ps_so s1 = ps_so s.
    Hypothesis HNUM : is_numstart (e_tok E 0) = true.
    Variable h0 : Z.
    Hypothesis ETWS : e_tws E = [h0].
    Hypothesis ESBS : e_sbs E = [].
    Notation Q2 := (fun ms => implM usegs (del lops p) s1 (flat_post E LB B cap s m) ms).
    Notation J10 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 := [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9].

    Lemma root_k_errA : rdel_errA_k E CP Q2.
    Proof using HF OK EH HEAP AUX ERR PRES HLO FA SO.
      unfold rdel_errA_k. intros until m1. intros HMX. apply evt_done. cbv beta.
      destruct HMX as (nxt & sc & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & HMEM).
      unfold implM. iprefix. step. step. ihere. to_implM.
      eapply (root_del_call E LB B cap s1 p CP c _ _ m nxt (J10 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9) sc 0x43998);
        [exact OK | exact EH | reflexivity | exact HEAP | exact AUX | exact ERR | exact PRES | exact HLO | lia | reflexivity | reflexivity | exact HMEM | ].
      intros s2' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m6 HMEM6 HEAP6 AUX6 ERR6 FA6 SO6 PRES6. cbv beta.
      step. step.
      eapply (root_tail_exit (s2_rebase E m6) LB B cap s s2' m errv 9);
        [apply env_ok_rebase; exact OK | apply env_heap_rebase; exact EH | exact HEAP6 | exact AUX6 | exact ERR6 | exact PRES6 | congruence | congruence | left; lia | ].
      exists nxt, sc, j0, j1, j2, j3, j4, j5, j6, j7, j8, j9. exact HMEM6.
    Qed.

    Lemma root_k_errB : rdel_errB_k E CP Q2.
    Proof using HF OK EH HEAP AUX ERR PRES HLO FA SO.
      unfold rdel_errB_k. intros until m1. intros HCODE HMX. apply evt_done. cbv beta.
      destruct HMX as (nxt & sc & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & HMEM).
      unfold implM. iprefix. step. step. ihere. to_implM.
      eapply (root_del_call E LB B cap s1 p CP c _ _ m nxt (J10 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9) sc 0x46df0);
        [exact OK | exact EH | reflexivity | exact HEAP | exact AUX | exact ERR | exact PRES | exact HLO | lia | reflexivity | reflexivity | exact HMEM | ].
      intros s2' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m6 HMEM6 HEAP6 AUX6 ERR6 FA6 SO6 PRES6. cbv beta.
      step. step.
      eapply (root_tail_exit (s2_rebase E m6) LB B cap s s2' m errv code);
        [apply env_ok_rebase; exact OK | apply env_heap_rebase; exact EH | exact HEAP6 | exact AUX6 | exact ERR6 | exact PRES6 | congruence | congruence | exact HCODE | ].
      exists nxt, sc, j0, j1, j2, j3, j4, j5, j6, j7, j8, j9. exact HMEM6.
    Qed.

    Lemma root_k_fin0 : forall v r, num_word v -> rdel_fin0_k (gapp E [v; r] []) CP Q2.
    Proof using HF OK EH HEAP AUX ERR PRES HLO FA SO HNUM h0 ETWS ESBS.
      intros v r Hv. unfold rdel_fin0_k. intros until m1. intros HMEM. apply evt_done. cbv beta.
      unfold implM. iprefix. step. step. ihere. to_implM.
      eapply (root_del_call (gapp E [v; r] []) LB B cap s1 p CP c _ _ m (e_nxt0 E) (DSL (gapp E [v; r] []) j0 j8 j16 j24 j32 j56 j72) [] 0x4701c);
        [apply env_ok_gapp; exact OK | apply env_heap_ghost; exact EH | reflexivity | exact HEAP | exact AUX | exact ERR | exact PRES | exact HLO | lia | reflexivity | reflexivity | exact HMEM | ].
      intros s2' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m6 HMEM6 HEAP6 AUX6 ERR6 FA6 SO6 PRES6. cbv beta.
      step. step. if_true.
      eapply (root_tail_doc (s2_rebase (gapp E [v; r] []) m6) LB B cap s s2' m errv h0 v r);
        [apply env_ok_rebase; apply env_ok_gapp; exact OK | apply env_heap_rebase; apply env_heap_ghost; exact EH | exact HEAP6 | exact AUX6 | exact ERR6 | exact PRES6
        | congruence | congruence | exact HNUM
        | cbn [e_tws s2_rebase gapp s2_ghost]; rewrite ETWS; reflexivity | exact Hv | cbn [e_sbs s2_rebase gapp s2_ghost]; rewrite ESBS; reflexivity | exact HMEM6].
    Qed.

    Lemma root_k_fin9 : rdel_fin9_k E CP Q2.
    Proof using HF OK EH HEAP AUX ERR PRES HLO FA SO.
      unfold rdel_fin9_k. intros until m1. intros HCODE HMX. apply evt_done. cbv beta.
      destruct HMX as (nxt & sc & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & HMEM).
      unfold implM. iprefix. step. step. ihere. to_implM.
      eapply (root_del_call E LB B cap s1 p CP c _ _ m nxt (J10 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9) sc 0x4701c);
        [exact OK | exact EH | reflexivity | exact HEAP | exact AUX | exact ERR | exact PRES | exact HLO | lia | reflexivity | reflexivity | exact HMEM | ].
      intros s2' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m6 HMEM6 HEAP6 AUX6 ERR6 FA6 SO6 PRES6. cbv beta.
      step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. step.
      eapply (root_tail_exit (s2_rebase E m6) LB B cap s s2' m errv code);
        [apply env_ok_rebase; exact OK | apply env_heap_rebase; exact EH | exact HEAP6 | exact AUX6 | exact ERR6 | exact PRES6 | congruence | congruence | left; lia | ].
      exists nxt, sc, j0, j1, j2, j3, j4, j5, j6, j7, j8, j9. exact HMEM6.
    Qed.

    Lemma root_k_fin9g : forall v r, rdel_fin9_k (gapp E [v; r] []) CP Q2.
    Proof using HF OK EH HEAP AUX ERR PRES HLO FA SO.
      intros v r. unfold rdel_fin9_k. intros until m1. intros HCODE HMX. apply evt_done. cbv beta.
      destruct HMX as (nxt & sc & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & HMEM).
      unfold implM. iprefix. step. step. ihere. to_implM.
      eapply (root_del_call (gapp E [v; r] []) LB B cap s1 p CP c _ _ m nxt (J10 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9) sc 0x4701c);
        [apply env_ok_gapp; exact OK | apply env_heap_ghost; exact EH | reflexivity | exact HEAP | exact AUX | exact ERR | exact PRES | exact HLO | lia | reflexivity | reflexivity | exact HMEM | ].
      intros s2' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m6 HMEM6 HEAP6 AUX6 ERR6 FA6 SO6 PRES6. cbv beta.
      step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. step.
      eapply (root_tail_exit (s2_rebase (gapp E [v; r] []) m6) LB B cap s s2' m errv code);
        [apply env_ok_rebase; apply env_ok_gapp; exact OK | apply env_heap_rebase; apply env_heap_ghost; exact EH | exact HEAP6 | exact AUX6 | exact ERR6 | exact PRES6 | congruence | congruence | left; lia | ].
      exists nxt, sc, j0, j1, j2, j3, j4, j5, j6, j7, j8, j9. exact HMEM6.
    Qed.
  End Sites.

  Lemma root_front : forall (E : s2env) LB B cap s c t errv h0,
    env_ok E -> env_heap E LB B cap -> e_tws E = [h0] -> e_sbs E = [] ->
    RHEAP s LB (e_m0 E) -> rauxv_ok (e_m0 E) B -> rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] ->
    rw_cells usegs (e_m0 E) SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)] ->
    e_lo E <= e_SP E - SJ_OPNEW_STACK ->
    e_lo E + 368 + NUMU_STACK <= bv_unsigned (e_sp E) ->
    slowfu_stmt_g usegs 0x5f104 0x110000 -> pffu_stmt_g usegs 0x5f1b4 0x110000 ->
    is_numstart (e_tok E 0) = true ->
    c = e_len E - e_off E 0 + 64 ->
    t = skipn (Z.to_nat (e_off E 0)) (e_bs E) ->
    rootprim_k E (fun ms => implM usegs (mbind (newnt lops c) (fun r => del lops r)) s (flat_post E LB B cap s (e_m0 E)) ms) 0x43874.
  Proof using HM HF.
    intros E LB B cap s c t errv h0 OK EH ETWS ESBS HEAP AUX ERR GOT HLO HROOM HSLOWF HPFF HNUM Ec Et.
    unfold rootprim_k. intros until m1. intros HMEM. apply evt_done. cbv beta.
    pose proof HMEM as (FRM & FR & IMPL & DOCC & IDXA & BUFRO & TAPEW & SBUFW & _ & _ & MI & MU & WM & ST & _).
    pose proof (ok_room _ OK) as HRM. unfold S2_STACK in HRM.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ok_glo _ OK) as G. pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    pose proof (off_range _ _ (ok_s1 _ OK) 0 ltac:(pose proof (n_pos _ _ (ok_s1 _ OK)); lia)) as HOFF.
    pose proof (ok_this _ OK) as T1. pose proof (ok_idx _ OK) as T2. pose proof (ok_buf _ OK) as T3.
    assert (HEAP1 : RHEAP s LB m1) by (eapply s2_heap_frame; [exact EH| exact HEAP| exact MU| exact WM]).
    assert (AUX1 : rauxv_ok m1 B) by (eapply s2_auxv_frame; [exact OK| exact EH| exact AUX| exact MU| exact WM]).
    assert (ERR1 : rw_cells usegs m1 LX_ERRNO [C4 errv]).
    { eapply (s2_static_frame E LB B cap _ _ LX_ERRNO); [exact OK| exact EH| | | exact ERR| exact MU| exact WM];
        unfold LX_ERRNO, RATP; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (GOT1 : rw_cells usegs m1 SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)]).
    { eapply (s2_static_frame E LB B cap _ _ SJ_GOT_NOTHROW); [exact OK| exact EH| | | exact GOT| exact MU| exact WM];
        unfold SJ_GOT_NOTHROW; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (PRES1 : lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) (e_m0 E) m1)
      by (eapply s2_lx_pres_munch; [exact OK| exact EH| exact MU| exact WM]).
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT1. unfold impl_cells in IMPL.
    rewrite (eh_tp _ _ _ _ EH).
    unfold implM. iprefix.
    ngrun_to 0x7bb48%Z.
    assert (RL : blen t = e_len E - e_off E 0) by (rewrite Et; apply blen_skipn; exact HOFF).
    assert (TOK : bytes_ok t) by (rewrite Et; apply bytes_ok_skipn; exact (ok_bytes _ OK)).
    replace (e_len E + - e_off E 0 + 64) with c by lia.
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := e_lo E) (q := e_SP E) (n := c);
        [exact HEAP1 | exact AUX1 | destruct (eh_B _ _ _ _ EH); lia | exact ST | exact (eh_ceil _ _ _ _ EH) | exact HLO | exact ERR1 | exact MI | lia | lia]. }
    cbv beta. intros p s1 ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & CP & junk
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA1 & SO1 & BR & HEAP2 & BLK).
    replace (ret_pc (Z_to_bv 64 276640)) with (Z_to_bv 64 276640) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof BR as (CPpos & _ & _ & CPC & CPS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CPC.
    pose proof (eh_ceil _ _ _ _ EH) as CEIL. destruct (eh_B _ _ _ _ EH) as (SPB & B63 & _).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG12.
    assert (BUFRO2 : bytes_at usegs m2 (e_BUF E) (padded_bytes (e_bs E))).
    { eapply bytes_at_agree; [exact AG12| exact BUFRO|]. intros a Ha. eapply s2_region_client; [exact OK| exact EH|].
      do 4 right; left. rewrite padded_bytes_blen in Ha. lia. }
    assert (IDXA2 : u32arr usegs m2 (e_IDX E) (e_iws E)).
    { eapply u32arr_agree; [exact AG12| exact IDXA|]. intros a Ha. eapply s2_region_client; [exact OK| exact EH|]. do 3 right; left. lia. }
    pose proof (blen_nonneg t) as RL0.
    replace (Z.to_nat c) with (Z.to_nat (blen t) + 64)%nat in BLK by lia.
    apply rk_CB_split2 in BLK. destruct BLK as [COPYA PAD]. rewrite Z2Nat.id in PAD by lia.

    assert (DJ : forall a, s2_region E a -> ~ (CP <= a < CP + c)).
    { intros a HR Hc. destruct (s2_region_client E LB B cap OK EH a HR) as [H|[H|H]].
      - clear - H Hc CPC CEIL HLO. unfold SJ_OPNEW_STACK, RMALLOC_STACK in HLO. lia.
      - clear - H Hc CPS. lia.
      - exact (LH_head_disj _ _ _ _ _ _ HEAP2 a H Hc). }
    assert (DJX : forall a, lx_client LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) a -> ~ (CP <= a < CP + c)).
    { intros a [_ HC] Hc. destruct HC as [H|[H|[H _]]].
      - clear - H Hc CPC CEIL HRM. lia.
      - exact (LH_head_disj _ _ _ _ _ _ HEAP2 a H Hc).
      - clear - H Hc CPS. lia. }
    pose proof (idx_read E OK m2 0 IDXA2 ltac:(pose proof (n_pos _ _ (ok_s1 _ OK)); lia)) as RD2. rewrite Z.mul_0_r, Z.add_0_r in RD2.
    unfold implM. iprefix.

    nstep. if_cases K1; zify_cond K1; [|exfalso; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    ngrun_to 0xcfe78%Z. clear RD2.
    replace (e_len E + - e_off E 0) with (blen t) by lia.
    eapply evt_cut.
    { eapply (memcpy_callZ) with (Dst := CP) (Src := e_BUF E + e_off E 0) (N := blen t) (src := zbytes t) (junk := firstn (Z.to_nat (blen t)) junk);
        [ rewrite Et; apply padded_src; [exact BUFRO2| exact HOFF] | rewrite zbytes_length; unfold blen; rewrite Nat2Z.id; reflexivity | exact COPYA
        | | lia | lia | lia | exact MI2 ].
      destruct (eh_buf _ _ _ _ EH) as (b & Hb & Hb1 & Hb2). destruct b as [[pb Ab] nb].
      pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 Hb) as SEPB. cbn [blk_addr blk_size fst snd] in *. clear - SEPB Hb1 Hb2 RL HOFF Ec RL0. lia. }
    intros ms' PO. unfold memcpy_postZ in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3 & -> & MU3 & WM3 & MI3 & COPYB & _).
    replace (ret_pc (Z_to_bv 64 276672)) with (Z_to_bv 64 276672) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (PAD3 : rw_cells usegs m3 (CP + blen t) [CB 64 (skipn (Z.to_nat (blen t)) junk)]).
    { eapply rw_cells_transport; [exact PAD| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia| exact I]. }
    assert (IDXA3 : u32arr usegs m3 (e_IDX E) (e_iws E)).
    { eapply u32arr_agree; [exact (agree_on_of_munch _ _ _ MU3 WM3)| exact IDXA2|]. intros a Ha. cbn [outside]. split; [| exact I].
      assert (HRa : s2_region E a) by (do 3 right; left; lia). pose proof (DJ a HRa). lia. }
    pose proof (idx_read E OK m3 0 IDXA3 ltac:(pose proof (n_pos _ _ (ok_s1 _ OK)); lia)) as RD3. rewrite Z.mul_0_r, Z.add_0_r in RD3.

    ngrun_to 0xd03f8%Z. clear RD3.
    replace (e_len E + - e_off E 0) with (blen t) by lia.
    eapply evt_cut.
    { eapply (memset_callZ) with (D := CP + blen t) (C := 32) (N := 64) (junk := skipn (Z.to_nat (blen t)) junk); [exact PAD3| exact MI3| lia| lia| lia| lia]. }
    intros ms' PO. unfold memset_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & PAD4).
    replace (ret_pc (Z_to_bv 64 276708)) with (Z_to_bv 64 276708) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    change (Z.to_nat 64) with 64%nat in PAD4.
    assert (COPYB4 : rw_cells usegs m4 CP [CB (Z.to_nat (blen t)) (zbytes t)]).
    { eapply rw_cells_transport; [exact COPYB| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia| exact I]. }
    pose proof (crs_assemble m4 CP t COPYB4 PAD4) as CPRO4.

    assert (AG14 : agree_on (s2_region E) m1 m4).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AG12| intros a Ha; eapply s2_region_client; eassumption]|].
      eapply agree_on_trans.
      - eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU3 WM3)|]. intros a Ha. cbn [outside]. split; [pose proof (DJ a Ha); lia| exact I].
      - eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU4 WM4)|]. intros a Ha. cbn [outside]. split; [pose proof (DJ a Ha); lia| exact I]. }
    assert (ST4 : stk usegs m4 (e_lo E) (e_SP E)).
    { eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]| exact MU4| exact WM4|];
        cbn [disjoint_from]; (split; [lia| exact I]). }
    assert (MEMI4 : MEMI (s2_rebase E m4) (e_nxt0 E) (RSL E j0 j8 j16 j24 j32 j72) [] fc m4).
    { eapply (MEMI_rebase_agree (s2_region E) E _ _ _ _ m1 m4 AG14); [intros a Ha; exact Ha | reflexivity | exact HMEM | exact MI4 | exact ST4]. }

    assert (HEAP4 : RHEAP s1 ((p, CP, c) :: LB) m4).
    { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU3| exact WM3|]| exact MU4| exact WM4|].
      - constructor; [eapply (W_ok_block _ (p, CP, c)); [left; reflexivity| cbn; lia| cbn; lia]| constructor].
      - constructor; [eapply (W_ok_block _ (p, CP, c)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]| exact MU4| exact WM4|].
      - constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - CPC CPS CEIL HRM SPB RL0 Ec RL; lia| constructor].
      - constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - CPC CPS CEIL HRM SPB RL0 Ec RL; lia| constructor]. }
    assert (ERR4 : rw_cells usegs m4 LX_ERRNO [C4 errv2]).
    { eapply rw_cells_transport; [eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]| exact MU4| exact WM4|];
        unfold LX_ERRNO, RATP; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; (split; [clear - CPS RL0 Ec RL; lia| exact I]). }
    assert (PRES4 : lx_pres LB (bv_unsigned (e_sp E)) (s2_X (e_THIS E) (e_TAPE E) (e_SBUF E) (e_OC E) (e_IA E) (e_tcap E) (e_scap E)) (e_m0 E) m4).
    { eapply lx_pres_trans; [exact PRES1|].
      eapply lx_pres_trans; [apply lx_pres_of_heap_pres; eapply rheap_pres_weaken; [exact HP| lia| auto]|].
      eapply lx_pres_trans.
      - eapply lx_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha HC. cbn [outside]. split; [pose proof (DJX a HC); lia| exact I].
      - eapply lx_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha HC. cbn [outside]. split; [pose proof (DJX a HC); lia| exact I]. }
    assert (CPSEP : cp_sep (s2_rebase E m4) CP t).
    { unfold cp_sep. cbn [s2_rebase e_TAPE e_tcap]. destruct (eh_tape _ _ _ _ EH) as (b & Hb & Hb1 & Hb2). destruct b as [[pb Ab] nb].
      pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 Hb) as SEPB. cbn [blk_addr blk_size fst snd] in *. clear - SEPB Hb1 Hb2 Ec RL. lia. }
    assert (OK4 : env_ok (s2_rebase E m4)) by (apply env_ok_rebase; exact OK).
    assert (EH4 : env_heap (s2_rebase E m4) LB B cap) by (apply env_heap_rebase; exact EH).
    assert (HLO4 : e_lo E <= e_SP E - RFREE_STACK) by (unfold SJ_OPNEW_STACK, RMALLOC_STACK, RFREE_STACK in *; lia).
    ihere. to_implM. rewrite <- (eh_tp _ _ _ _ EH).
    eapply implM_evt.
    { eapply (rootnum_walk (s2_rebase E m4) OK4 CP t TOK ltac:(lia) ltac:(cbn [s2_rebase e_lo]; lia) CPSEP ltac:(lia) HSLOWF HPFF HROOM
                (fun ms => implM usegs (del lops p) s1 (flat_post (s2_rebase E m4) LB B cap s (e_m0 E)) ms)
                ltac:(cbn [e_tws s2_rebase]; rewrite ETWS; reflexivity)
                (root_k_errA (s2_rebase E m4) LB B cap s s1 p CP c (e_m0 E) errv2 OK4 EH4 HEAP4 AUX4 ERR4 PRES4 HLO4 FA1 SO1)
                (root_k_errB (s2_rebase E m4) LB B cap s s1 p CP c (e_m0 E) errv2 OK4 EH4 HEAP4 AUX4 ERR4 PRES4 HLO4 FA1 SO1)
                (root_k_fin0 (s2_rebase E m4) LB B cap s s1 p CP c (e_m0 E) errv2 OK4 EH4 HEAP4 AUX4 ERR4 PRES4 HLO4 FA1 SO1 HNUM h0 ETWS ESBS)
                (root_k_fin9 (s2_rebase E m4) LB B cap s s1 p CP c (e_m0 E) errv2 OK4 EH4 HEAP4 AUX4 ERR4 PRES4 HLO4 FA1 SO1)
                (root_k_fin9g (s2_rebase E m4) LB B cap s s1 p CP c (e_m0 E) errv2 OK4 EH4 HEAP4 AUX4 ERR4 PRES4 HLO4 FA1 SO1));
        [exact MEMI4 | exact CPRO4]. }
    intros ms' H. exact H.
  Qed.
End RootArm.

Theorem stage2t_rootnum_proof :
  rmalloc_stmt -> rfree_stmt -> slowfu_stmt_g usegs 0x5f104 0x110000 -> pffu_stmt_g usegs 0x5f1b4 0x110000 -> stage2t_rootnum_stmt.
Proof.
  intros HM HF HSLOWF HPFF. unfold stage2t_rootnum_stmt.
  intros ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv
         THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws cap tcap scap nxt docv dcap p12 p28 p50 c RC
         HS1 HBOK HLEN HIWS HTC1 HTC2 HSC1 HSC2 HIWL HHEAP HAUX HSPB HB63 HST HCEIL HGT HLO HSP16 HERR HMI HFRM HGOT
         RTHIS RIDX RBUF RTAPE RSBUF ROC RIA HPD HDOC1 HDOC2 ALTHIS ALDOC ALIDX ALTAPE ALOC HIMPL HDOCC HIDXA HBUFRO HTAPEW HSBUFW HOCA HIAA.
  assert (HROOMZ : lo + 368 + 2608 <= bv_unsigned sp) by (unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK in HLO; lia).
  destruct (stk_carve usegs m lo (bv_unsigned sp) 368 HST ltac:(lia)) as [ST' [junk FRJ]].
  apply (rw_cells_split_CB usegs m _ [] 368 junk [] [80; 184; 104]%nat) in FRJ; [|reflexivity].
  cbn [mk_CB_cells app] in FRJ.
  lazymatch type of FRJ with rw_cells _ _ _ [CB 80 ?jlo; CB 184 ?j80; CB 104 ?jhi] =>
    set (E := mkS2Env ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws tcap scap
                      (wz SJ_DPI_VPTR) p12 nxt p28 (wz cap) p50 dcap j80 m [] [])
  end.
  pose proof (region_below s LB m THIS 96 lo HHEAP RTHIS HCEIL ltac:(lia)) as BTHIS.
  pose proof (region_below s LB m IDX _ lo HHEAP RIDX HCEIL ltac:(lia)) as BIDX.
  pose proof (region_below s LB m BUF _ lo HHEAP RBUF HCEIL ltac:(pose proof (blen_nonneg bs); lia)) as BBUF.
  pose proof (region_below s LB m TAPE _ lo HHEAP RTAPE HCEIL ltac:(pose proof (blen_nonneg bs); lia)) as BTAPE.
  pose proof (region_below s LB m SBUF _ lo HHEAP RSBUF HCEIL ltac:(pose proof (blen_nonneg bs); lia)) as BSBUF.
  pose proof (region_below s LB m OC 8192 lo HHEAP ROC HCEIL ltac:(lia)) as BOC.
  pose proof (region_below s LB m IA 1024 lo HHEAP RIA HCEIL ltac:(lia)) as BIA.
  assert (OK : Sj_stage2_defs.env_ok E).
  { destruct (pd7 _ _ _ _ _ _ _ HPD) as ((D12 & D13 & D14 & D15 & D16 & D17) & (D23 & D24 & D25 & D26 & D27) & (D34 & D35 & D36 & D37) & (D45 & D46 & D47) & (D56 & D57) & D67).
    unfold GLOBALS_TOP in HGT.
    subst E. constructor; cbn [Sj_stage2_defs.e_bs Sj_stage2_defs.e_idxs Sj_stage2_defs.e_iws Sj_stage2_defs.e_tcap Sj_stage2_defs.e_scap Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp Sj_stage2_defs.e_THIS Sj_stage2_defs.e_DOC Sj_stage2_defs.e_IDX Sj_stage2_defs.e_BUF Sj_stage2_defs.e_TAPE Sj_stage2_defs.e_SBUF Sj_stage2_defs.e_OC Sj_stage2_defs.e_IA]; unfold S2_LEN_MAX, S2_STACK.
    - exact HS1.
    - exact HBOK.
    - exact HLEN.
    - clear - HTC1 HTC2. lia.
    - clear - HSC1 HSC2. lia.
    - exact HIWS.
    - exact HGT.
    - clear - HROOMZ. lia.
    - clear - BTHIS. lia.
    - clear - HDOC1 HDOC2 HB63. lia.
    - clear - BIDX. lia.
    - clear - BBUF. lia.
    - clear - BTAPE. lia.
    - clear - BSBUF. lia.
    - clear - BOC. lia.
    - clear - BIA. lia.
    - exact ALTHIS.
    - exact ALDOC.
    - exact ALIDX.
    - exact ALTAPE.
    - exact ALOC.
    - exact HSP16.
    - clear - D12. unfold ivl_disj in D12. cbn [fst snd] in D12. lia.
    - clear - D13. unfold ivl_disj in D13. cbn [fst snd] in D13. lia.
    - clear - D14. unfold ivl_disj in D14. cbn [fst snd] in D14. lia.
    - clear - D15. unfold ivl_disj in D15. cbn [fst snd] in D15. lia.
    - clear - D16. unfold ivl_disj in D16. cbn [fst snd] in D16. lia.
    - clear - D17. unfold ivl_disj in D17. cbn [fst snd] in D17. lia.
    - clear - D24. unfold ivl_disj in D24. cbn [fst snd] in D24. lia.
    - clear - D34. unfold ivl_disj in D34. cbn [fst snd] in D34. lia.
    - clear - D45. unfold ivl_disj in D45. cbn [fst snd] in D45. lia.
    - clear - D46. unfold ivl_disj in D46. cbn [fst snd] in D46. lia.
    - clear - D47. unfold ivl_disj in D47. cbn [fst snd] in D47. lia.
    - clear - D25. unfold ivl_disj in D25. cbn [fst snd] in D25. lia.
    - clear - D35. unfold ivl_disj in D35. cbn [fst snd] in D35. lia.
    - clear - D56. unfold ivl_disj in D56. cbn [fst snd] in D56. lia.
    - clear - D57. unfold ivl_disj in D57. cbn [fst snd] in D57. lia.
    - clear - D26. unfold ivl_disj in D26. cbn [fst snd] in D26. lia.
    - clear - D36. unfold ivl_disj in D36. cbn [fst snd] in D36. lia.
    - clear - D67. unfold ivl_disj in D67. cbn [fst snd] in D67. lia.
    - clear - D27. unfold ivl_disj in D27. cbn [fst snd] in D27. lia.
    - clear - D37. unfold ivl_disj in D37. cbn [fst snd] in D37. lia. }
  destruct (tape_img_init E m HTAPEW HSBUFW ltac:(clear - BTAPE; subst E; cbn; lia) ltac:(clear - BSBUF; subst E; cbn; lia)
              ltac:(clear - HTC1; subst E; cbn; pose proof (blen_nonneg bs); lia) ltac:(clear - HSC1 HSC2; subst E; cbn; pose proof (blen_nonneg bs); lia)) as [h0 TIMG].
  assert (HM0 : Sj_stage2_entry.MEM0 (s2_ghost E [h0] []) docv fc m).
  { unfold Sj_stage2_entry.MEM0. revert TIMG. subst E. intros TIMG. cbn [Sj_stage2_defs.e_m0 Sj_stage2_defs.e_THIS Sj_stage2_defs.e_DOC Sj_stage2_defs.e_IDX Sj_stage2_defs.e_BUF
      Sj_stage2_defs.e_TAPE Sj_stage2_defs.e_SBUF Sj_stage2_defs.e_OC Sj_stage2_defs.e_IA Sj_stage2_defs.e_bs Sj_stage2_defs.e_iws Sj_stage2_defs.e_tcap
      Sj_stage2_defs.e_scap Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp Sj_stage2_defs.e_j80 Sj_stage2_defs.e_tws Sj_stage2_defs.e_sbs s2_ghost].
    split; [exact HFRM|]. split; [reflexivity|]. split; [exact HIMPL|]. split; [exact HDOCC|]. split; [exact HIDXA|]. split; [exact HBUFRO|].
    split; [exact HTAPEW|]. split; [exact HSBUFW|]. split; [exact HOCA|]. split; [exact HIAA|]. split; [exact HMI|].
    split; [exact ST'|]. split; [eexists _, _; exact FRJ | exact TIMG]. }
  assert (EH : env_heap E LB B cap).
  { subst E. constructor; cbn [Sj_stage2_defs.e_tp Sj_stage2_defs.e_vptr Sj_stage2_defs.e_capv Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp Sj_stage2_defs.e_DOC
      Sj_stage2_defs.e_THIS Sj_stage2_defs.e_IDX Sj_stage2_defs.e_BUF Sj_stage2_defs.e_TAPE Sj_stage2_defs.e_SBUF Sj_stage2_defs.e_OC Sj_stage2_defs.e_IA
      Sj_stage2_defs.e_bs Sj_stage2_defs.e_iws Sj_stage2_defs.e_tcap Sj_stage2_defs.e_scap].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact HCEIL.
    - clear - HSPB HB63 HDOC2. lia.
    - intros a (b & Hb & Hr). pose proof (LH_block_range s LB m b HHEAP Hb) as (_ & _ & _ & P3 & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in P3. clear - P3 Hr. lia.
    - exact RTHIS.
    - exact RIDX.
    - exact RBUF.
    - exact RTAPE.
    - exact RSBUF.
    - exact ROC.
    - exact RIA.
    - clear - BTHIS. lia.
    - clear - BTAPE. lia.
    - clear - BSBUF. lia.
    - clear - BOC. lia.
    - clear - BIA. lia. }
  assert (HNUM : is_numstart (tok bs idxs 0) = true /\ c = blen bs - off bs idxs 0 + 64).
  { unfold SjAlloc.root_copy in RC. cbn [Z.eqb andb] in RC.
    destruct idxs as [|i0 rest]; [pose proof (n_pos _ _ HS1) as NP; unfold n in NP; cbn in NP; lia|].
    cbn [hd] in RC. unfold tok, off, ext. change (Z.to_nat 0) with 0%nat. cbn [app nth].
    unfold is_numstart, is_digit, c_minus. unfold SjAlloc.is_numstart_b in RC.
    lazymatch type of RC with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate RC] end.
    split; [reflexivity| inversion RC; reflexivity]. }
  destruct HNUM as [HNUM Ec].
  eapply implM_evt.
  { eapply (seg_entry_num (s2_ghost E [h0] []) (env_ok_ghost _ _ _ OK) (fun ms => implM usegs (mbind (newnt lops c) (fun r => del lops r)) s (flat_post E LB B cap s (Sj_stage2_defs.e_m0 E)) ms)
              docv t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m HM0 HNUM).
    eapply (root_front HM HF (s2_ghost E [h0] []) LB B cap s c (skipn (Z.to_nat (off bs idxs 0)) bs) errv h0 (env_ok_ghost _ _ _ OK) (env_heap_ghost _ _ _ _ _ _ EH) eq_refl eq_refl);
      [exact HHEAP | exact HAUX | exact HERR | exact HGOT | | | exact HSLOWF | exact HPFF | exact HNUM | exact Ec | reflexivity].
    - subst E. cbn [Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp s2_ghost]. unfold SJ_S2_STACK, SJ_S2_FRAMES, SJ_OPNEW_STACK, RMALLOC_STACK in *. clear - HLO. lia.
    - subst E. cbn [Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp s2_ghost]. unfold NUMU_STACK. clear - HROOMZ. lia. }
  intros ms' H. exact H.
Qed.

Theorem stage2t_of_contracts :
  rmalloc_stmt -> rfree_stmt -> slowfu_stmt_g usegs 0x5f104 0x110000 -> pffu_stmt_g usegs 0x5f1b4 0x110000 -> stage2t_stmt.
Proof.
  intros HM HF HSLOWF HPFF. apply (stage2t_of_walk HSLOWF HPFF). exact (stage2t_rootnum_proof HM HF HSLOWF HPFF).
Qed.

Theorem stage2_of_contracts :
  rmalloc_stmt -> rfree_stmt -> slowfu_stmt_g usegs 0x5f104 0x110000 -> pffu_stmt_g usegs 0x5f1b4 0x110000 -> stage2_stmt.
Proof.
  intros HM HF HSLOWF HPFF. apply stage2_of_stage2t. exact (stage2t_of_contracts HM HF HSLOWF HPFF).
Qed.
End WithCeiling0.


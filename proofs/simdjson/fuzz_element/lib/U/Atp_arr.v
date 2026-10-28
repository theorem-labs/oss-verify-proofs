(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Arr.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.

  Lemma atp_arr : atp_arr_stmt E d.
  Proof.
    unfold atp_arr_stmt. intros until jo.
    intros AI PAT TY NXT CLOSE TILES I0 EN ELN NODE QN NB NO OUT QO OD OB HEAP AUX QD ST LO Q16 ERR MI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    unfold arr_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP, ATP_ARR in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    pose proof (munch_refl [(q - 160, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 160, q); (out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (PTRF : Forall (fun c => 0 <= c < 256) ptr).
    { destruct PAT as (pre & Ep & _). rewrite Ep in P1. apply Forall_app in P1. tauto. }
    assert (PL : zlength ptr <= zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & _). rewrite Ep. unfold zlength. rewrite length_app. lia. }
    assert (PP : 0 <= P /\ P + zlength ptr = ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength. rewrite length_app. lia. }
    assert (ZLR : 0 <= zlength ptr < 2^64) by (unfold zlength in *; lia).
    hide AI.
    unfold implM. iprefix.

    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step. step. hstep. hstep.
    name_mem m1.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -80 + Z.of_nat 8) with (q + -72) in FR by lia.
    apply (proj1 (rw_cells_app _ _ [_; _; _] _)) in FR. destruct FR as [FRREC FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -72 + Z.of_nat 24) with (q + -48) in FR by lia.
    apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRSV FRHI]. cbn [cells_size csize Nat.add] in FRHI.
    replace (q + -48 + Z.of_nat 16) with (q + -32) in FRHI by lia.
    apply (rw_cells_split_CB usegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
    assert (AI1 : AINV E m1).
    { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    destruct AI1 as (TAPEB & SBUFB & PTRB & DOCC).
    assert (PTRB1 : bytes_at usegs m1 P (map (Z_to_bv 8) ptr)).
    { destruct PAT as (pre & Ep & EP). pose proof PTRB as X. rewrite Ep, map_app in X.
      apply (bytes_at_skipn _ _ _ (length (map (Z_to_bv 8) pre))) in X; [| rewrite length_app; lia].
      rewrite skipn_app, skipn_all, Nat.sub_diag, length_map in X. cbn [skipn] in X. rewrite EP. unfold zlength. exact X. }
    assert (HEAP1 : RHEAP s (ae_LB E) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }

    assert (EPI : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x32 pv lv : word) (m2 : mem) (ja jj : list byte) (s' : PState),
      rw_cells usegs m2 (q + -80) [CB 8 ja] -> rw_cells usegs m2 (q + -72) [CB 24 jj] -> rw_cells usegs m2 (q + -48) [C8 pv; C8 lv] ->
      rw_cells usegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -80) -> (exists errv' : word, rw_cells usegs m2 LX_ERRNO [C4 errv']) ->
      rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m m2 -> out_rec E m2 out ->
      evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s')
        (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 s3 s4 s5 s6 s7 s8 s9 s10 s11 x29 x30 x31 x32)
            F (Z_to_bv 64 0x3f5d4) fc None m2 (seg_rom usegs))).
    { intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x32 pv lv m2 ja jj s' EFR0 EFRREC EFRSV EFRHI EMI EST EERR EAUX EFA ESO EHEAP EPRES EOUT.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as EMU. pose proof (wmono_refl usegs m2) as EWM.
      do 4 step. step.
      release_frame EFR0 EST (q + -72). release_frame EFRREC EST (q + -48). release_frame EFRSV EST (q + -32). release_frame EFRHI EST q.
      step.
      apply evt_done. unfold hpost. do 15 eexists. exists m2. split; [reflexivity|].
      split; [exact EMI|]. split; [exact EST|]. split; [exact EERR|]. split; [exact EAUX|]. split; [exact EFA|]. split; [exact ESO|].
      unfold lvl_R. split; [exact EHEAP|]. split; [exact EPRES| exact EOUT]. }

    assert (WE8 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x32 pv lv : word) (code : Z) (m2 : mem) (jj oa ob oc od : list byte),
      rw_cells usegs m2 (q + -80) [CB 8 (take 8 junk)] -> rw_cells usegs m2 (q + -72) [CB 24 jj] -> rw_cells usegs m2 (q + -48) [C8 pv; C8 lv] ->
      rw_cells usegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -80) -> rw_cells usegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 160, q); (out, out + 24)] m m2 -> wmono usegs m m2 -> 0 < code < 64 ->
      evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 code) x11 x12 x13 x14 x15 x16 x17
                 x28 s3 s4 s5 s6 s7 s8 s9 s10 s11 x29 x30 x31 x32)
            F (Z_to_bv 64 0x3f480) fc None m2 (seg_rom usegs))).
    { intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x32 pv lv code m2 jj oa ob oc od WFR0 WFRREC WFRSV WFRHI WOUT WMI WST WERR MU3 WM3 CR.
      rewrite ELX in WERR.
      hstep. hstep. hstep. step. name_mem m3.
      lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into WOUT3 end.
      eapply EPI; [exact WFR0| exact WFRREC| exact WFRSV| exact WFRHI| exact WMI| exact WST| exists errv; rewrite ELX; exact WERR| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI].
      - exists (Z_to_bv 64 0), 0, code, od. split; [exact WOUT3|]. split; [lia|]. intros C0. exfalso. lia. }
    assert (W2C : forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x32 pv lv : word) (code : Z) (m2 : mem) (jj oa ob oc od : list byte),
      rw_cells usegs m2 (q + -80) [CB 8 (take 8 junk)] -> rw_cells usegs m2 (q + -72) [CB 24 jj] -> rw_cells usegs m2 (q + -48) [C8 pv; C8 lv] ->
      rw_cells usegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -80) -> rw_cells usegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 160, q); (out, out + 24)] m m2 -> wmono usegs m m2 -> 0 < code < 64 ->
      evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 node) x10 (Z_to_bv 64 code) x12 x13 x14 x15 x16 x17
                 x28 s3 s4 s5 s6 s7 s8 s9 s10 s11 x29 x30 x31 x32)
            F (Z_to_bv 64 0x3f5c4) fc None m2 (seg_rom usegs))).
    { intros x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 x32 pv lv code m2 jj oa ob oc od WFR0 WFRREC WFRSV WFRHI WOUT WMI WST WERR MU3 WM3 CR.
      rewrite ELX in WERR.
      step. if_lia. hstep. hstep. hstep. name_mem m3.
      lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into WOUT3 end.
      eapply EPI; [exact WFR0| exact WFRREC| exact WFRSV| exact WFRHI| exact WMI| exact WST| exists errv; rewrite ELX; exact WERR| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI].
      - exists (Z_to_bv 64 0), 0, code, od. split; [exact WOUT3|]. split; [lia|]. intros C0. exfalso. lia. }
    destruct (rw_cells_forget _ _ _ _ FRREC) as [jrec FRREC']. cbn [cells_size csize Nat.add] in FRREC'.

    step. if_cases K0; zify_cond K0.
    {
      step. if_lia. step. step. hstep. hstep. hstep. step. name_mem m3. stop_now.
      lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
      eapply EPI; [exact FR0| exact FRREC'| exact FRSV| exact FRHI| exact MI| exact ST| exists errv; rewrite ELX; exact ERR| | reflexivity| reflexivity| | |].
      + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
      + exists (Z_to_bv 64 (ae_DOC E)), i, 0. eexists. split; [exact OUT3|]. split; [lia|]. intros _. split; [reflexivity|]. split; [exact I0| exact ELN]. }
    destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
    destruct BP as [E0|BP']; [exfalso; rewrite E0 in PL; unfold zlength in PL; cbn in PL; lia|].
    pose proof (in_blocks_range _ _ _ _ _ HEAP BP' ltac:(unfold zlength; lia)) as PRANGE.
    pose proof (zbytes_read1 m1 P (c0 :: ptr0) 0 PTRB1 ltac:(rewrite zlength_cons; lia)) as RD0. change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    step. if_lia. astep. astep. step. if_cases K1; zify_cond K1.
    {
      step. if_lia. astep. stop_now. eapply WE8; [exact FR0| exact FRREC'| exact FRSV| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| lia]. }
    subst c0.
    assert (LENM : Z.of_nat (length (map (Z_to_bv 8) (47 :: ptr0))) = zlength ptr0 + 1) by (unfold zlength; rewrite length_map; cbn [length]; lia).

    astep. astep. astep. step.
    eapply substr_cps with (SV := q + -48) (A := P) (n := zlength ptr0 + 1) (pos := 1) (RA := 0x3f428);
      [exact FRSV| lia| lia| lia| | lia| lia| reflexivity| lia| reflexivity|].
    { match goal with |- _ < bv_unsigned ?w => let v := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with v end. lia. }
    intros ya3 ya4 ya5. replace (zlength ptr0 + 1 - 1) with (zlength ptr0) by lia.

    step. hstep. hstep. astep. name_mem m2.
    lazymatch goal with H : bytes_at usegs m2 P _ |- _ => rename H into PTRB2 end.
    step. if_cases K2; zify_cond K2.
    {
      stop_now. eapply W2C; [exact FR0| exact FRREC'| exact FRSV| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| lia]. }
    destruct ptr0 as [|c1 ptr1]; [exfalso; rewrite zlength_nil in K2; lia|].
    assert (C1R : 0 <= c1 < 256) by (inversion PTRF as [|? ? _ X]; inversion X; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr1) as ZL1.
    pose proof (zbytes_read1 m2 P (47 :: c1 :: ptr1) 1 PTRB2 ltac:(rewrite !zlength_cons; lia)) as RD1.
    change (nth (Z.to_nat 1) (47 :: c1 :: ptr1) 0) with c1 in RD1.

    assert (ROC : ro_cells usegs m2 0x14028 [CB 8 [Z_to_bv 8 205; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204]]).
    { apply (ro_cells_image usegs m2); [exact MI| vm_compute; reflexivity| lia| cbn; lia]. }
    set (KK := fun ms' : machine_state => impl usegs (at_node usegs) (atp_walk lops (ptr_segs (47 :: c1 :: ptr1)) s)
                (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms').
    change (evt usegs KK) with (evt usegs (fun ms' => KK ms')).
    assert (RB1 : bytes_at usegs m2 (P + 1) (map (Z_to_bv 8) (c1 :: ptr1))).
    { pose proof (bytes_at_skipn _ _ _ 1 PTRB2 ltac:(cbn; lia)) as X. exact X. }
    assert (RF1 : Forall (fun c => 0 <= c < 256) (c1 :: ptr1)) by (inversion PTRF; assumption).

    assert (AT9F8 : forall (x12 x13 : word),
      evt usegs KK
        (MS (mkR (Z_to_bv 64 0x3f428) (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 22)
                 x12 x13 ya4 ya5 a6 a7 (Z_to_bv 64 (zlength ptr1 + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3f490) fc None m2 (seg_rom usegs))).
    { intros x12 x13.
      do 3 astep. astep. replace (0 <? P + 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      astep. step. step. astep. astep. astep. step. step.

      assert (AXERR : forall (code : Z) (xa2 xa3 xt3 xt4 xt5 xt6 xs2 : word), 0 < code < 64 ->
        evt usegs KK (MS (mkR (Z_to_bv 64 0x3f428) (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 48) (Z_to_bv 64 out) (Z_to_bv 64 node)
                             (Z_to_bv 64 (P + 1)) (Z_to_bv 64 code) xa2 xa3 (Z_to_bv 64 (- (zlength ptr1 + 1))) (Z_to_bv 64 1) (Z_to_bv 64 47) (Z_to_bv 64 14757395258967641293)
                             xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                        F (Z_to_bv 64 0x3f5c4) fc None m2 (seg_rom usegs))).
      { intros code xa2_ xa3_ xt3_ xt4_ xt5_ xt6_ xs2_ CODE. subst KK. stop_now.
        eapply W2C; [exact FR0| exact FRREC'| | exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| exact CODE]. eassumption. }

      assert (AXTOK : forall (tok : Z) (xa2 xa3 xt3 xt4 xt5 xt6 : word),
        0 <= tok <= zlength ptr1 + 1 -> (forall j, (j < Z.to_nat tok)%nat -> nth j (c1 :: ptr1) 0 <> 47) ->
        ((tok < zlength ptr1 + 1 /\ nth (Z.to_nat tok) (c1 :: ptr1) 0 = 47) \/ tok = zlength ptr1 + 1) ->
        evt usegs KK (MS (mkR (Z_to_bv 64 0x3f428) (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 48) (Z_to_bv 64 out) (Z_to_bv 64 node)
                             (Z_to_bv 64 (P + 1)) (Z_to_bv 64 22) xa2 xa3 (Z_to_bv 64 (- (zlength ptr1 + 1))) (Z_to_bv 64 1) (Z_to_bv 64 47) (Z_to_bv 64 14757395258967641293)
                             (Z_to_bv 64 tok) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                        F (Z_to_bv 64 0x3f52c) fc None m2 (seg_rom usegs))).
      { intros tok xa2_ xa3_ xt3_ xt4_ xt5_ xt6_ TOK NOSL2 DISJ.

        apply (rw_cells_split_CB usegs _ _ [] 24 jrec [] [8;8;8]%nat) in FRREC'; [|reflexivity]. cbn [mk_CB_cells app] in FRREC'.
        step. step. hstep. hstep. step. step. step. name_mem m3.
        lazymatch goal with H : rw_cells usegs m3 (q + -72) _ |- _ => rename H into FRREC3 end.
        apply (proj1 (rw_cells_app _ _ [_; _] _)) in FRREC3. destruct FRREC3 as [N2C REC3]. cbn [cells_size csize Nat.add] in REC3.
        replace (q + -72 + Z.of_nat 16) with (q + -56) in REC3 by lia.
        assert (HEAP3 : RHEAP s (ae_LB E) m3).
        { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        assert (AI3 : AINV E m3).
        { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
          - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
          - intros a Ha. cbn [outside]. lia. }
        pose proof AI3 as (TAPEB3 & SBUFB3 & PTRB3 & DOCC3).
        call (arrat_spec E OK d);
          [exact N2C| lia| lia| exact TAPEB3| exact DOCC3| unfold ty; exact TY| exact NXT| exact TILES| exact I0| exact EN| exact OUT| lia| lia
          | exact HEAP3| exact ST| lia| apply Z.le_refl| exact MI| lia| lia|].
        name_mem m4.
        lazymatch goal with H : stk usegs m4 _ _ |- _ => rename H into ST4 end.
        lazymatch goal with H : rw_cells usegs m4 out _ |- _ => rename H into OUT4 end.
        lazymatch goal with H : _ \/ _ |- _ => rename H into RES4 end.
        lazymatch goal with H : mem_inv usegs m4 |- _ => rename H into MI4 end.
        assert (HEAP4 : RHEAP s (ae_LB E) m4).
        { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        assert (AUX4 : rauxv_ok m4 (ae_B E)).
        { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        assert (PRES4 : lx_pres (ae_LB E) q [(out, out + 24)] m m4) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
        assert (REC4 : exists jj, rw_cells usegs m4 (q + -72) [CB 24 jj]).
        { pose proof REC3 as REC3'. replace (q + -56) with (q + -72 + Z.of_nat 16) in REC3' by lia.
          pose proof (proj2 (rw_cells_app _ _ [_; _] _) (conj N2C REC3')) as X.
          cbn [app] in X. destruct (rw_cells_forget _ _ _ _ X) as [j4 X']. cbn [cells_size csize Nat.add] in X'. exists j4. exact X'. }
        destruct RES4 as [(-> & -> & IT0 & (j' & EL' & JE))|(-> & -> & ->)].
        2:{
            step. if_lia. astep. astep. step. if_false. step. if_true.
            destruct REC4 as [jj REC4]. subst KK. stop_now.
            eapply EPI; [exact FR0| exact REC4| exact FRSV| exact FRHI| exact MI4| exact ST4| exists errv; rewrite ELX; exact ERR| exact AUX4| reflexivity| reflexivity| exact HEAP4| exact PRES4|].
            exists (Z_to_bv 64 0), 0, 19. eexists. split; [exact OUT4|]. split; [lia|]. intros C0. exfalso. lia. }

        lazymatch type of EL' with elem _ _ _ _ _ ?itv _ => rename itv into it end.
        pose proof (elem_lt _ _ _ _ _ _ _ EL') as IJ'.
        step. if_lia. astep. astep. step. if_false. step. if_false. step. step. if_cases KR; zify_cond KR.
        {
          destruct REC4 as [jj REC4]. subst KK. stop_now.
          eapply EPI; [exact FR0| exact REC4| exact FRSV| exact FRHI| exact MI4| exact ST4| exists errv; rewrite ELX; exact ERR| exact AUX4| reflexivity| reflexivity| exact HEAP4| exact PRES4|].
          exists (Z_to_bv 64 (ae_DOC E)), it, 0. eexists. split; [exact OUT4|]. split; [lia|]. intros _. split; [reflexivity|]. split; [exact IT0|]. exists d, j'. exact EL'. }

        destruct DISJ as [(TL & SL)|X]; [| exfalso; lia].
        assert (TN : (Z.to_nat tok < length (c1 :: ptr1))%nat) by (unfold zlength in *; cbn [length] in *; lia).
        destruct (seg_split (c1 :: ptr1) (Z.to_nat tok) ltac:(lia) NOSL2) as [E1 E2].
        rewrite (skipn_cons_nth _ _ TN), SL in E1, E2.
        set (r := skipn (S (Z.to_nat tok)) (c1 :: ptr1)) in *.
        change (take_seg (47 :: r)) with (@nil Z) in E1. change (drop_seg (47 :: r)) with (47 :: r) in E2. rewrite app_nil_r in E1.
        assert (ZR : zlength (47 :: r) = zlength ptr1 + 1 - tok).
        { subst r. rewrite zlength_cons, zlength_skipn by (cbn [length] in *; lia). rewrite zlength_cons. lia. }
        assert (PAT2 : ptr_at E (P + 1 + tok) (47 :: r)).
        { pose proof (ptr_at_skip E P (47 :: c1 :: ptr1) (S (Z.to_nat tok)) PAT ltac:(cbn [length] in *; lia)) as X.
          change (skipn (S (Z.to_nat tok)) (47 :: c1 :: ptr1)) with (skipn (Z.to_nat tok) (c1 :: ptr1)) in X.
          rewrite (skipn_cons_nth _ _ TN), SL in X. fold r in X. replace (P + Z.of_nat (S (Z.to_nat tok))) with (P + 1 + tok) in X by lia. exact X. }
        assert (AI4 : AINV E m4).
        { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
          - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
          - intros a Ha. cbn [outside]. lia. }

        astep. astep. step. step.
        eapply substr_cps with (SV := q + -48) (A := P + 1) (n := zlength ptr1 + 1) (pos := tok) (RA := 0x3f574);
          [exact FRSV| lia| lia| lia| | lia| lia| reflexivity| lia| reflexivity|].
        { match goal with |- _ < bv_unsigned ?w => let v := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with v end. lia. }
        intros yb3 yb4 yb5.

        step. step. astep. astep. step. if_false. step. if_false. astep. step. step.
        apply (proj1 (rw_cells_app _ _ [_; _] _)) in OUT4. destruct OUT4 as [NODE2 OUTHI]. cbn [cells_size csize Nat.add] in OUTHI.
        replace (out + Z.of_nat 16) with (out + 16) in OUTHI by lia.
        replace (Z_to_bv 64 (zlength ptr1 + 1 - tok)) with (Z_to_bv 64 (zlength (47 :: r))) by (f_equal; lia).
        destruct REC4 as [jrec4 REC4].
        subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m)).
        rewrite (ptr_segs_unfold (c1 :: ptr1)), E1, E2. cbv iota. apply implM_atp_walk_plain.
        pose proof HELEM as HE. unfold atp_elem_stmt in HE.
        eapply implM_post_evt.
        { eapply (HE (47 :: r) it j') with (jo := jrec4);
            [exact AI4| exact PAT2| exact EL'| exact IT0| lia| exact NODE2| lia| lia| lia| exact REC4| lia| lia| lia
            | exact HEAP4| exact AUX4| lia| exact ST4| unfold elem_need, ATP_LEAFX, RMALLOC_STACK; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI4]. }
        cbv beta. intros [] s' ms' PO. unfold hpost in PO.
        destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & -> & MI5 & ST5 & [errv5 ERR5] & AUX5 & FA5 & SO5 & RR).
        unfold lvl_R in RR. destruct RR as (HEAP5 & PRES5 & OUTC).
        replace (ret_pc (Z_to_bv 64 0x3f598)) with (Z_to_bv 64 0x3f598) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ PRES5) as AG5.
        apply (rw_cells_agree _ _ _ _ _ AG5) in FR0; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG5) in FRSV; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG5) in FRHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG5) in NODE2; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG5) in OUTHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
        rewrite ELX in ERR5.
        pose proof (munch_refl [(q - 160, q); (out, out + 24)]%Z m5) as MU5. pose proof (wmono_refl usegs m5) as WM5.
        destruct OUTC as (r0' & j'' & code' & jn' & OUTC & CR' & OIMP).
        pose proof (bv_unsigned_in_range 64 r0') as R0R.

        step. step. astep. astep. hstep. hstep. step. if_lia. hstep. step. name_mem m6.
        lazymatch goal with H : rw_cells usegs m6 out _ |- _ => rename H into NODE6 end.
        lazymatch goal with H : rw_cells usegs m6 (out + 16) _ |- _ => rename H into OUTHI6 end.
        lazymatch goal with H : rw_cells usegs m6 (q + -72) _ |- _ => rename H into OUTC6 end.
        lazymatch goal with H : mem_inv usegs m6 |- _ => rename H into MI6 end.
        lazymatch goal with H : stk usegs m6 _ _ |- _ => rename H into ST6 end.
        lazymatch goal with H : munch _ m5 m6 |- _ => rename H into MU6 end.
        lazymatch goal with H : wmono usegs m5 m6 |- _ => rename H into WM6 end.
        destruct (rw_cells_forget _ _ _ _ OUTC6) as [jj OUTC']. cbn [cells_size csize Nat.add] in OUTC'.
        pose proof (proj2 (rw_cells_app _ _ [_; _] _) (conj NODE6 ltac:(cbn [cells_size csize Nat.add]; replace (out + Z.of_nat 16) with (out + 16) by lia; exact OUTHI6))) as OUT6.
        cbn [app] in OUT6.
        eapply EPI; [exact FR0| exact OUTC'| exact FRSV| exact FRHI| exact MI6| exact ST6| exists errv5; rewrite ELX; exact ERR5| | exact FA5| exact SO5| | |].
        - eapply rauxv_ok_frame; [exact AUX5| exact MU6| exact WM6|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
        - eapply LH_frame; [exact HEAP5| exact MU6| exact WM6|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
        - eapply lx_pres_trans; [exact PRES4|]. eapply lx_pres_trans; [| eapply lx_pres_of_munch; [exact MU6| exact WM6| exact CLI]].
          eapply lx_pres_sub; [exact PRES5| lia| intros b Hb; exact Hb|].
          intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| lia].
        - exists r0', j'', code'. eexists. split; [exact OUT6|]. split; [exact CR'| exact OIMP]. }
      eapply evt_eq; [| eapply (arr_digit_loop KK m2 F fc (c1 :: ptr1) (P + 1) (zlength ptr1 + 1) (- (zlength ptr1 + 1)) (q + -80)
                                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ RB1 RF1 ltac:(rewrite zlength_cons; reflexivity) ltac:(lia)
                                  ltac:(unfold zlength in *; cbn [length] in *; lia) ltac:(lia) MI AXERR AXTOK (S (length (c1 :: ptr1))) 0)];
        [atp_st_eq| lia| unfold zlength; cbn [length]; lia| intros j Hj; lia]. }

    astep. step. if_cases K3; zify_cond K3.
    { eapply evt_eq; [| eapply AT9F8]; [atp_st_eq]. }
    astep. astep. step. if_cases K4; zify_cond K4.
    all: first [ eapply evt_eq; [| eapply AT9F8]; [atp_st_eq]
               | step; if_lia; astep; step; subst KK; stop_now; eapply WE8; [exact FR0| exact FRREC'| eassumption| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| lia] ].
  Qed.
End Arr.
End WithCeiling0.

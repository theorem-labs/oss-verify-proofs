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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu.
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

Section Elem.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HOBJ : forall d', d = S d' -> atp_obj_stmt E d'.
  Hypothesis HARR : forall d', d = S d' -> atp_arr_stmt E d'.

  Lemma atp_elem : atp_elem_stmt E d.
  Proof.
    unfold atp_elem_stmt. intros until jo.
    intros AI PAT EL I0 JN NODE QN NB NO OUT QO OD OB HEAP AUX QD ST LO Q16 ERR MI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    unfold elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP, ATP_ELEM in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (munch_refl [(q - 80, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide AI.
    unfold implM. iprefix.
    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 5 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unhide AI.
    assert (AI1 : AINV E m1).
    { eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (blocks_below _ _ _ _ HEAP Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    hide AI. destruct AI1 as (TAPEB & SBUFB & PTRB & DOCC).

    step. step. if_lia. step. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false.
    step. step. step. step. step.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) ltac:(destruct WF as (_ & ? & _); lia)) as TIR.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := i) (RA := 0x3db14);
      [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. astep. astep.
    assert (PTRB1 : bytes_at usegs m1 P (map (Z_to_bv 8) ptr)).
    { destruct PAT as (pre & Ep & EP). pose proof PTRB as X. rewrite Ep, map_app in X.
      apply (bytes_at_skipn _ _ _ (length (map (Z_to_bv 8) pre))) in X; [| rewrite length_app; lia].
      rewrite skipn_app, skipn_all, Nat.sub_diag, length_map in X. cbn [skipn] in X. rewrite EP. unfold zlength. exact X. }
    assert (PTRF : Forall (fun c => 0 <= c < 256) ptr).
    { destruct PAT as (pre & Ep & _). rewrite Ep in P1. apply Forall_app in P1. tauto. }
    assert (PL : zlength ptr <= zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & _). rewrite Ep. unfold zlength. rewrite length_app. lia. }
    assert (PP : 0 <= P /\ P + zlength ptr = ae_PTR E + zlength (ae_p1 E)).
    { destruct PAT as (pre & Ep & EP). rewrite EP, Ep. unfold zlength. rewrite length_app. lia. }
    assert (HEAP1 : RHEAP s (ae_LB E) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m)).

    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -64 + Z.of_nat 8) with (q + -56) in FR by lia.
    apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRLO FRHI]. cbn [cells_size csize Nat.add] in FRHI.
    replace (q + -56 + Z.of_nat 16) with (q + -40) in FRHI by lia.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 80, q); (out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }

    assert (EPI : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) (m2 : mem) (ja jj : list byte) (s' : PState),
      rw_cells usegs m2 (q + -64) [CB 8 ja] -> rw_cells usegs m2 (q + -56) [CB 16 jj] -> rw_cells usegs m2 (q + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -64) -> (exists errv' : word, rw_cells usegs m2 LX_ERRNO [C4 errv']) ->
      rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m m2 -> out_rec E m2 out ->
      evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s')
        (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3dc20) fc None m2 (seg_rom usegs))).
    { intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m2 ja jj s' EFR0 EFRLO EFRHI EMI EST EERR EAUX EFA ESO EHEAP EPRES EOUT.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as EMU. pose proof (wmono_refl usegs m2) as EWM.
      do 5 step. step.
      release_frame EFR0 EST (q + -56). release_frame EFRLO EST (q + -40). release_frame EFRHI EST q.
      step.
      apply evt_done. unfold hpost. do 15 eexists. exists m2. split; [reflexivity|].
      split; [exact EMI|]. split; [exact EST|]. split; [exact EERR|]. split; [exact EAUX|]. split; [exact EFA|]. split; [exact ESO|].
      unfold lvl_R. split; [exact EHEAP|]. split; [exact EPRES| exact EOUT]. }

    assert (W3 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (code : Z) (m2 : mem) (ja oa ob oc od : list byte) (pv lv : word),
      rw_cells usegs m2 (q + -64) [CB 8 ja] -> rw_cells usegs m2 (q + -56) [C8 pv; C8 lv] -> rw_cells usegs m2 (q + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      mem_inv usegs m2 -> stk usegs m2 (ae_lo E) (q + -64) -> rw_cells usegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 80, q); (out, out + 24)] m m2 -> wmono usegs m m2 -> 0 < code < 64 ->
      evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 code) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 node) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3dc14) fc None m2 (seg_rom usegs))).
    { intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 code m2 ja oa ob oc od pv lv WFR0 WFRLO WFRHI WOUT WMI WST WERR MU3 WM3 CR.
      rewrite ELX in WERR.
      hstep. hstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      destruct (rw_cells_forget _ _ _ _ WFRLO) as [jj WFRLO']. cbn [cells_size csize Nat.add] in WFRLO'.
      eapply EPI; [exact WFR0| exact WFRLO'| exact WFRHI| exact WMI| exact WST| exists errv; rewrite ELX; exact WERR| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        apply W_ok_stack; cbn; lia.
      - eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI].
      - exists (Z_to_bv 64 0), 0, code, od. split; [exact WOUT|]. split; [lia|]. intros C0. exfalso. lia. }

    lazymatch goal with |- implM _ _ _ ?Q ?ms =>
      assert (SCALAR : ttype (Tf (ae_tws E) i) <> t_arr -> ttype (Tf (ae_tws E) i) <> t_obj -> evt usegs (Q tt s) ms) end.
    { intros NE1 NE2. cbv beta. unfold t_arr, t_obj in NE1, NE2.
      apply (rw_cells_split_CB usegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
      assert (TTR : 0 <= ttype (Tf (ae_tws E) i) < 256) by (unfold ttype; lia).

      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      astep. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K.

      assert (ZLR : 0 <= zlength ptr < 2^64) by (unfold zlength in *; lia).
      step. if_cases K0; zify_cond K0.
      -
        step. if_lia.
        step. step. hstep. hstep. hstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        destruct (rw_cells_forget _ _ _ _ FRLO) as [jj FRLO']. cbn [cells_size csize Nat.add] in FRLO'.
        eapply EPI; [exact FR0| exact FRLO'| exact FRHI| exact MI| exact ST| exists errv; rewrite ELX; exact ERR| | reflexivity| reflexivity| | |].
        + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
        + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
        + eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
        + lazymatch goal with H : rw_cells usegs m3 out _ |- _ => rename H into OUT3 end.
          exists (Z_to_bv 64 (ae_DOC E)), i, 0. eexists. split; [exact OUT3|]. split; [lia|]. intros _. split; [reflexivity|]. split; [exact I0|]. exists d, j. exact EL.
      -
        destruct ptr as [|c0 ptr']; [exfalso; apply K0; reflexivity|].
        assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
        assert (ZL : zlength (c0 :: ptr') = zlength ptr' + 1) by (unfold zlength; cbn [length]; lia).
        assert (ZL0 : 0 <= zlength ptr') by (unfold zlength; lia).
        assert (P0' : 0 < P).
        { destruct BP as [E0|BP']; [exfalso; rewrite E0 in PL; unfold zlength in PL; cbn in PL; lia|].
          pose proof (in_blocks_range _ _ _ _ _ HEAP BP' ltac:(unfold zlength; lia)). lia. }
        assert (PLO : P + zlength (c0 :: ptr') <= ae_lo E).
        { destruct BP as [E0|BP']; [exfalso; rewrite E0 in PL; unfold zlength in PL; cbn in PL; lia|].
          pose proof (in_blocks_range _ _ _ _ _ HEAP BP' ltac:(unfold zlength; lia)). lia. }
        assert (LENM : Z.of_nat (length (map (Z_to_bv 8) (c0 :: ptr'))) = zlength (c0 :: ptr')) by (unfold zlength; rewrite length_map; reflexivity).
        hstep. hstep. step. if_lia.
        name_mem m1b.
        lazymatch goal with H : bytes_at usegs m1b P _ |- _ => rename H into PTRB2 end.
        lazymatch goal with H : mem_inv usegs m1b |- _ => rename H into MI1b end.
        pose proof (zbytes_read1 m1b P (c0 :: ptr') 0 PTRB2 ltac:(lia)) as RD0. cbn [Z.to_nat nth] in RD0. rewrite Z.add_0_r in RD0.
        astep. astep. step. if_cases K1; zify_cond K1.
        +
          step. if_lia. astep.
          eapply W3; [exact FR0| exact FRLO| exact FRHI| exact OUT| exact MI1b| exact ST| rewrite ELX; exact ERR| exact MU| exact WM| lia].
        +
          astep. astep. astep. step.
          call svfind_spec; [exact FRLO| lia| lia| exact PTRB2| exact LENM| lia| exact PLO| lia| exact ST| lia| exact MI1b|].
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
          lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
          lazymatch goal with H : rw_cells usegs m2 (q + -56) _ |- _ => rename H into FRLO2 end.
          lazymatch goal with H : stk usegs m2 _ _ |- _ => rename H into ST2 end.
          pose proof (svfind_res_range (zlength (c0 :: ptr')) 126 (map (Z_to_bv 8) (c0 :: ptr')) ltac:(lia)) as SVR.
          set (r := svfind_res (zlength (c0 :: ptr')) 126 (map (Z_to_bv 8) (c0 :: ptr'))) in *.

          assert (A20 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (av : Z),
            evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
              (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 av) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (zlength (c0 :: ptr'))) (Z_to_bv 64 node) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x3dbe4) fc None m2 (seg_rom usegs))).
          { intros. step. if_lia. astep. step.
            eapply W3; [exact FR0| exact FRLO2| exact FRHI| exact OUT| exact MI2| exact ST2| exact ERR| exact MU| exact WM| lia]. }

          assert (A22 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (av : Z),
            evt usegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
              (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 av) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (zlength (c0 :: ptr'))) (Z_to_bv 64 node) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x3dc0c) fc None m2 (seg_rom usegs))).
          { intros. step. if_lia. astep.
            eapply W3; [exact FR0| exact FRLO2| exact FRHI| exact OUT| exact MI2| exact ST2| exact ERR| exact MU| exact WM| lia]. }

          astep. step. if_cases K2; zify_cond K2; rewrite ?land64_mod in K2; try apply A20; [idtac].
          assert (RR : 0 <= r < zlength (c0 :: ptr')).
          { destruct SVR as [SV1|SV1]; [exfalso; apply K2; rewrite SV1; reflexivity| exact SV1]. }

          step. astep. step. if_cases K3; zify_cond K3; try apply A22; [idtac].

          step. step. if_lia. astep. astep. step. if_lia. step. if_lia.
          pose proof (zbytes_read1 m2 P (c0 :: ptr') (r + 1) ltac:(assumption) ltac:(lia)) as RD1.
          pose proof (Forall_nth_Z _ (c0 :: ptr') (Z.to_nat (r + 1)) PTRF ltac:(unfold zlength in *; lia)) as C1R. cbv beta in C1R.
          replace (r + 1 + P) with (P + (r + 1)) by lia.
          astep. astep. astep. step. if_cases K5; zify_cond K5; first [apply A22 | apply A20]. }

    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    destruct (elem_view_of (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any (fun c cv H => H) HSN d i j EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e c Ed TY Ej NXT CLOSE TILES|d' e c Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    - apply implM_atp_walk_stop. apply SCALAR; unfold t_true, t_false, t_null, t_arr, t_obj in *; lia.
    - apply implM_atp_walk_stop. apply SCALAR; unfold t_i64, t_u64, t_dbl, t_arr, t_obj in *; lia.
    - apply implM_atp_walk_stop. apply SCALAR; unfold t_str, t_arr, t_obj in *; lia.
    -
      clear SCALAR W3. unfold implM. iprefix.
      rewrite TY. unfold t_arr. step. if_cases K; zify_cond K; try (exfalso; lia); [idtac]. clear K.

      step. step. hstep. hstep. step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (AI2 : AINV E m2).
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      assert (HEAP2 : RHEAP s (ae_LB E) m2).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX2 : rauxv_ok m2 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES2 : lx_pres (ae_LB E) q [(out, out + 24)] m m2) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      ihere. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m)).
      eapply implM_post_evt.
      { eapply (HARR d' Ed) with (e := e) (c := c);
          [exact AI2| exact PAT| exact TY| exact NXT| exact CLOSE| exact TILES| exact I0| lia| exists d, j; exact EL| exact FRLO| lia| lia| lia| exact OUT| lia| exact OD| exact OB
          | exact HEAP2| exact AUX2| lia| exact ST| unfold arr_need, elem_need, ATP_LEAFX, RMALLOC_STACK; subst d; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
      cbv beta. intros [] s' ms' PO. unfold hpost in PO.
      destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & OUT3).
      replace (ret_pc (Z_to_bv 64 0x3db78)) with (Z_to_bv 64 0x3db78) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRLO; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU4. pose proof (wmono_refl usegs m3) as WM4.
      step.
      destruct (rw_cells_forget _ _ _ _ FRLO) as [jj FRLO']. cbn [cells_size csize Nat.add] in FRLO'.
      assert (OUT3' : out_rec E m3 out) by exact OUT3.
      eapply EPI; [exact FR0| exact FRLO'| exact FRHI| exact MI3| exact ST3| exact ERR3| exact AUX3| exact FA3| exact SO3| exact HEAP3| | exact OUT3'].
      eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_weaken; [exact PRES3| lia| intros b Hb; exact Hb| intros a Ha; exact Ha].
    -
      clear SCALAR W3. unfold implM. iprefix.
      rewrite TY. unfold t_obj. step. if_cases K; zify_cond K; try (exfalso; lia); [idtac]. clear K.
      astep. step. if_cases K; zify_cond K; try (exfalso; lia); [idtac]. clear K.
      step. step. hstep. hstep. step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (AI2 : AINV E m2).
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      assert (HEAP2 : RHEAP s (ae_LB E) m2).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX2 : rauxv_ok m2 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES2 : lx_pres (ae_LB E) q [(out, out + 24)] m m2) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      ihere. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m)).
      eapply implM_post_evt.
      { eapply (HOBJ d' Ed) with (e := e) (c := c);
          [exact AI2| exact PAT| exact TY| exact NXT| exact CLOSE| exact TILES| exact I0| lia| exists d, j; exact EL| exact FRLO| lia| lia| lia| exact OUT| lia| exact OD| exact OB
          | exact HEAP2| exact AUX2| lia| exact ST| unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK; subst d; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
      cbv beta. intros [] s' ms' PO. unfold hpost in PO.
      destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & OUT3).
      replace (ret_pc (Z_to_bv 64 0x3db50)) with (Z_to_bv 64 0x3db50) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRLO; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU4. pose proof (wmono_refl usegs m3) as WM4.
      step.
      destruct (rw_cells_forget _ _ _ _ FRLO) as [jj FRLO']. cbn [cells_size csize Nat.add] in FRLO'.
      assert (OUT3' : out_rec E m3 out) by exact OUT3.
      eapply EPI; [exact FR0| exact FRLO'| exact FRHI| exact MI3| exact ST3| exact ERR3| exact AUX3| exact FA3| exact SO3| exact HEAP3| | exact OUT3'].
      eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_weaken; [exact PRES3| lia| intros b Hb; exact Hb| intros a Ha; exact Ha].
  Qed.
End Elem.
End WithCeiling0.

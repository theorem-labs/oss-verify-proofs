(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_arrl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
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
    intros AI PAT TY NXT CLOSE TILES I0 EN NODE QN NB NO OUT QO OD OB HEAP AUX QD ST LO Q16 ERR MI.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    unfold arr_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP, ATP_ARR in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    pose proof (munch_refl [(q - 48, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 48, q); (out, out + 24)] a).
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

    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 48 junk [] [24;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step.
    name_mem m1.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FRLO FRHI]. cbn [cells_size csize Nat.add] in FRHI.
    replace (q + -48 + Z.of_nat 24) with (q + -24) in FRHI by lia.
    apply (rw_cells_split_CB psegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
    assert (AI1 : AINV E m1).
    { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    destruct AI1 as (TAPEB & SBUFB & PTRB & DOCC).
    assert (PTRB1 : bytes_at psegs m1 P (map (Z_to_bv 8) ptr)).
    { destruct PAT as (pre & Ep & EP). pose proof PTRB as X. rewrite Ep, map_app in X.
      apply (bytes_at_skipn _ _ _ (length (map (Z_to_bv 8) pre))) in X; [| rewrite length_app; lia].
      rewrite skipn_app, skipn_all, Nat.sub_diag, length_map in X. cbn [skipn] in X. rewrite EP. unfold zlength. exact X. }

    assert (EPI : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m2 : mem) (jj : list byte) (s' : PState),
      rw_cells psegs m2 (q + -48) [CB 24 jj] -> rw_cells psegs m2 (q + -24) [C8 s1; C8 s0; C8 ra] ->
      mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -48) -> (exists errv' : word, rw_cells psegs m2 LX_ERRNO [C4 errv']) ->
      rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m m2 -> (exists j, rw_cells psegs m2 out [CB 24 j]) ->
      evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s')
        (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3e120) fc None m2 (seg_rom psegs))).
    { intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 jj s' EFRLO EFRHI EMI EST EERR EAUX EFA ESO EHEAP EPRES EOUT.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as EMU. pose proof (wmono_refl psegs m2) as EWM.
      do 3 step. step.
      release_frame EFRLO EST (q + -24). release_frame EFRHI EST q.
      step.
      apply evt_done. unfold hpost. do 15 eexists. exists m2. split; [reflexivity|].
      split; [exact EMI|]. split; [exact EST|]. split; [exact EERR|]. split; [exact EAUX|]. split; [exact EFA|]. split; [exact ESO|].
      unfold lvl_R. split; [exact EHEAP|]. split; [exact EPRES| exact EOUT]. }

    assert (W70 : forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (code : Z) (m2 : mem) (oa ob oc od : list byte),
      rw_cells psegs m2 (q + -48) [CB 24 (take 24 junk)] -> rw_cells psegs m2 (q + -24) [C8 s1; C8 s0; C8 ra] ->
      rw_cells psegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -48) -> rw_cells psegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 48, q); (out, out + 24)] m m2 -> wmono psegs m m2 -> 0 <= code < 64 ->
      evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) x9 (Z_to_bv 64 code) x11 x12 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3e114) fc None m2 (seg_rom psegs))).
    { intros x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 code m2 oa ob oc od WFRLO WFRHI WOUT WMI WST WERR MU3 WM3 CR.
      rewrite ELX in WERR.
      hstep. hstep. hstep. name_mem m3.
      eapply EPI; [exact WFRLO| exact WFRHI| exact WMI| exact WST| exists errv; rewrite ELX; exact WERR| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI].
      - destruct (rw_cells_forget _ _ _ _ WOUT) as [j' WOUT']. cbn [cells_size csize Nat.add] in WOUT'. exists j'. exact WOUT'. }

    assert (W30 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word) (code : Z) (m2 : mem) (oa ob oc od : list byte),
      rw_cells psegs m2 (q + -48) [CB 24 (take 24 junk)] -> rw_cells psegs m2 (q + -24) [C8 s1; C8 s0; C8 ra] ->
      rw_cells psegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -48) -> rw_cells psegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 48, q); (out, out + 24)] m m2 -> wmono psegs m m2 -> 0 <= code < 64 ->
      evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) x9 x10 x11 x12 x13 (Z_to_bv 64 code) x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3e0d4) fc None m2 (seg_rom psegs))).
    { intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 code m2 oa ob oc od WFRLO WFRHI WOUT WMI WST WERR MU3 WM3 CR.
      rewrite ELX in WERR.
      hstep. hstep. hstep. step. name_mem m3.
      eapply EPI; [exact WFRLO| exact WFRHI| exact WMI| exact WST| exists errv; rewrite ELX; exact WERR| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI].
      - destruct (rw_cells_forget _ _ _ _ WOUT) as [j' WOUT']. cbn [cells_size csize Nat.add] in WOUT'. exists j'. exact WOUT'. }

    step. if_cases K0; zify_cond K0.
    {
      step. step. hstep. hstep. hstep. step. name_mem m3. stop_now.
      eapply EPI; [exact FRLO| exact FRHI| exact MI| exact ST| exists errv; rewrite ELX; exact ERR| | reflexivity| reflexivity| | |].
      + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
      + destruct (rw_cells_forget _ _ _ _ OUT) as [j' OUT']. cbn [cells_size csize Nat.add] in OUT'. exists j'. exact OUT'. }
    destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
    pose proof (zbytes_read1 m1 P (c0 :: ptr0) 0 PTRB1 ltac:(rewrite zlength_cons; lia)) as RD0. change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    astep. astep. step. if_cases K1; zify_cond K1.
    {
      astep. step. stop_now. eapply W70; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| lia]. }
    subst c0.

    astep. astep. step. if_cases K2; zify_cond K2.
    {
      stop_now. eapply W30; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| lia]. }
    destruct ptr0 as [|c1 ptr1]; [exfalso; rewrite zlength_nil in K2; lia|].
    assert (C1R : 0 <= c1 < 256) by (inversion PTRF as [|? ? _ X]; inversion X; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr1) as ZL1.
    pose proof (zbytes_read1 m1 P (47 :: c1 :: ptr1) 1 PTRB1 ltac:(rewrite !zlength_cons; lia)) as RD1.
    change (nth (Z.to_nat 1) (47 :: c1 :: ptr1) 0) with c1 in RD1.

    assert (ROC : ro_cells psegs m1 0x14028 [CB 8 [Z_to_bv 8 205; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204]]).
    { apply (ro_cells_image psegs m1); [exact MI| vm_compute; reflexivity| lia| cbn; lia]. }

    assert (AT634 : forall (x10 x15 : word),
      evt psegs (fun ms' => impl psegs (at_node psegs) (atp_walk lops (ptr_segs (47 :: c1 :: ptr1)) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms')
        (MS (mkR ra (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 out) s1 x10 (Z_to_bv 64 node) (Z_to_bv 64 (P + 1))
                 (Z_to_bv 64 (zlength ptr1 + 1 + 1)) (Z_to_bv 64 22) x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3dfd8) fc None m1 (seg_rom psegs))).
    { intros x10 x15.
      do 11 astep. step.
      assert (RB1 : bytes_at psegs m1 (P + 1) (map (Z_to_bv 8) (c1 :: ptr1))).
      { pose proof (bytes_at_skipn _ _ _ 1 PTRB1 ltac:(cbn; lia)) as X. exact X. }
      assert (RF1 : Forall (fun c => 0 <= c < 256) (c1 :: ptr1)) by (inversion PTRF; assumption).
      destruct BP as [E0|BP']; [exfalso; rewrite E0 in PL; unfold zlength in PL; cbn in PL; lia|].
      pose proof (in_blocks_range _ _ _ _ _ HEAP BP' ltac:(unfold zlength; lia)) as PRANGE.
      set (KK := fun ms' : machine_state => impl psegs (at_node psegs) (atp_walk lops (ptr_segs (47 :: c1 :: ptr1)) s)
                  (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) (snd p))) ms').
      change (evt psegs KK) with (evt psegs (fun ms' => KK ms')).

      assert (A19 : forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m2 : mem) (oa ob oc od : list byte),
        rw_cells psegs m2 (q + -48) [CB 24 (take 24 junk)] -> rw_cells psegs m2 (q + -24) [C8 s1; C8 s0; C8 ra] ->
        rw_cells psegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
        mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -48) -> rw_cells psegs m2 LX_ERRNO [C4 errv] ->
        munch [(q - 48, q); (out, out + 24)] m m2 -> wmono psegs m m2 ->
        evt psegs KK
          (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) x9 (Z_to_bv 64 (zlength ptr1 + 1)) x11 x12 x13 x14 x15 x16 x17
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x3e110) fc None m2 (seg_rom psegs))).
      { intros. subst KK. astep. stop_now. eapply W70; [eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| lia]. }

      assert (AXERR : forall (code : Z) (xs1 xa3 xa5 xa6 xt5 xt6 : word), 0 <= code < 64 ->
        evt psegs KK (MS (mkR ra (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) (Z_to_bv 64 (1 + - (zlength ptr1 + 2))) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 9)
                             (Z_to_bv 64 out) xs1 (Z_to_bv 64 (zlength ptr1 + 1)) (Z_to_bv 64 node) (Z_to_bv 64 (P + 1)) xa3 (Z_to_bv 64 code) xa5 xa6 (Z_to_bv 64 47)
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 10) (Z_to_bv 64 48) xt5 xt6)
                        F (Z_to_bv 64 0x3e0d4) fc None m1 (seg_rom psegs))).
      { intros code xs1_ xa3_ xa5_ xa6_ xt5_ xt6_ CODE. subst KK. stop_now.
        eapply W30; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| exact CODE]. }

      assert (AXTOK : forall (tok c3 : Z) (xs1 xa5 xa6 xt5 xt6 : word),
        0 <= tok <= zlength ptr1 + 1 -> (forall j, (j < Z.to_nat tok)%nat -> nth j (c1 :: ptr1) 0 <> 47) ->
        ((c3 = 47 /\ tok < zlength ptr1 + 1 /\ nth (Z.to_nat tok) (c1 :: ptr1) 0 = 47) \/ (c3 <> 47 /\ tok = zlength ptr1 + 1)) -> 0 <= c3 < 256 ->
        evt psegs KK (MS (mkR ra (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) (Z_to_bv 64 (1 + - (zlength ptr1 + 2))) (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 9)
                             (Z_to_bv 64 out) xs1 (Z_to_bv 64 (zlength ptr1 + 1)) (Z_to_bv 64 node) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 c3) (Z_to_bv 64 tok) xa5 xa6 (Z_to_bv 64 47)
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 10) (Z_to_bv 64 48) xt5 xt6)
                        F (Z_to_bv 64 0x3e07c) fc None m1 (seg_rom psegs))).
      { intros tok c3 xs1_ xa5_ xa6_ xt5_ xt6_ TOK NOSL2 DISJ C3R.
        pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
        unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_arr; lia) ltac:(unfold t_arr; lia)) as TIR.

        step. step. step. astep. astep. step. astep. astep. rewrite TY. unfold t_arr.

        astep. astep. step. step. if_false. astep. astep. astep. astep. step. if_true.

        astep. astep. astep. astep. astep. step. step. if_false. astep. astep. rewrite land32_tnext by lia. rewrite NXT.

        assert (AFOUND : forall (it j' : Z) (xs1 xa5 xt5 xt6 : word),
          elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' -> 0 <= it -> j' <= e ->
          evt psegs KK (MS (mkR ra (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 out) xs1
                               (Z_to_bv 64 (zlength ptr1 + 1)) (Z_to_bv 64 it) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 c3) (Z_to_bv 64 tok) xa5 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 (ae_TAPE E))
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt5 xt6)
                          F (Z_to_bv 64 0x3e1b4) fc None m1 (seg_rom psegs))).
        { intros it j' xs1' xa5' xt5' xt6' EL' IT0 JE.

          astep. hstep. hstep. hstep. name_mem m2.
          assert (HEAP2 : RHEAP s (ae_LB E) m2).
          { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
          assert (AUX2 : rauxv_ok m2 (ae_B E)).
          { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
          assert (PRES2 : lx_pres (ae_LB E) q [(out, out + 24)] m m2) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
          step. if_cases KR; zify_cond KR.
          {
            subst KK. stop_now.
            eapply EPI; [exact FRLO| exact FRHI| exact MI| exact ST| exists errv; rewrite ELX; exact ERR| exact AUX2| reflexivity| reflexivity| exact HEAP2| exact PRES2|].
            destruct (rw_cells_forget _ _ _ _ OUT) as [j2 OUT']. cbn [cells_size csize Nat.add] in OUT'. exists j2. exact OUT'. }

          destruct DISJ as [(_ & TL & SL)|(X & _)]; [| exfalso; exact (X KR)].
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
          assert (AI2 : AINV E m2).
          { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
            - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
            - intros a Ha. cbn [outside]. lia. }
          apply (proj1 (rw_cells_app _ _ [_; _] _)) in OUT. destruct OUT as [NODE2 OUTHI]. cbn [cells_size csize Nat.add] in OUTHI.
          replace (out + Z.of_nat 16) with (out + 16) in OUTHI by lia.
          pose proof (elem_lt _ _ _ _ _ _ _ EL') as IJ'.

          astep. astep. step. step. step.
          replace (Z_to_bv 64 (zlength ptr1 + 1 - tok)) with (Z_to_bv 64 (zlength (47 :: r))) by (f_equal; lia).
          subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m)).
          rewrite (ptr_segs_unfold (c1 :: ptr1)), E1, E2. cbv iota. apply implM_atp_walk_plain.
          pose proof HELEM as HE. unfold atp_elem_stmt in HE.
          eapply implM_post_evt.
          { eapply (HE (47 :: r) it j') with (jo := take 24 junk);
              [exact AI2| exact PAT2| exact EL'| exact IT0| lia| exact NODE2| lia| lia| lia| exact FRLO| lia| lia| lia
              | exact HEAP2| exact AUX2| lia| exact ST| unfold elem_need, ATP_LEAFX, RMALLOC_STACK; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
          cbv beta. intros [] s' ms' PO. unfold hpost in PO.
          destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MI3 & ST3 & [errv3 ERR3] & AUX3 & FA3 & SO3 & RR).
          unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & [jc OUTC]).
          replace (ret_pc (Z_to_bv 64 0x3e1dc)) with (Z_to_bv 64 0x3e1dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
          apply (rw_cells_agree _ _ _ _ _ AG3) in FRHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG3) in NODE2; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG3) in OUTHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
          rewrite ELX in ERR3.
          pose proof (munch_refl [(q - 48, q); (out, out + 24)]%Z m3) as MU3. pose proof (wmono_refl psegs m3) as WM3.
          apply (rw_cells_split_CB psegs _ _ [] 24 jc [] [8;8;4;4]%nat) in OUTC; [|reflexivity]. cbn [mk_CB_cells app] in OUTC.

          step. step. step. hstep. hstep. hstep. step. name_mem m4.
          destruct (rw_cells_forget _ _ _ _ OUTC) as [jj OUTC']. cbn [cells_size csize Nat.add] in OUTC'.
          assert (OUT4 : exists j, rw_cells psegs m4 out [CB 24 j]).
          { pose proof (proj2 (rw_cells_app _ _ [_; _] _) (conj NODE2 ltac:(cbn [cells_size csize Nat.add]; replace (out + Z.of_nat 16) with (out + 16) by lia; exact OUTHI))) as X.
            cbn [app] in X. destruct (rw_cells_forget _ _ _ _ X) as [j4 X']. cbn [cells_size csize Nat.add] in X'. exists j4. exact X'. }
          eapply EPI; [exact OUTC'| exact FRHI| exact MI3| exact ST3| exists errv3; rewrite ELX; exact ERR3| | exact FA3| exact SO3| | | exact OUT4].
          - eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
          - eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
          - eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_trans; [| eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI]].
            eapply lx_pres_sub; [exact PRES3| lia| intros b Hb; exact Hb|].
            intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| lia]. }
        astep. step. if_cases KE; zify_cond KE.
        all: first [ eapply A19; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM]
                   | idtac ].

        do 9 astep.
        eapply evt_eq; [| eapply (arr_iter_loop E OK d KK m1 F fc e c (q + -48) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TAPEB EN MI AFOUND
                                   ltac:(intros; eapply A19; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM])
                                   (S (Z.to_nat (e - (i + 1)))) (i + 1) c)];
          [atp_st_eq| exact TILES| exact KE| lia| lia]. }

      eapply evt_eq; [| eapply (arr_digit_loop KK m1 F fc (c1 :: ptr1) (P + 1) (zlength ptr1 + 1) (1 + - (zlength ptr1 + 2)) (q + -48)
                                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RB1 RF1 ltac:(rewrite zlength_cons; reflexivity) ltac:(lia)
                                  ltac:(unfold zlength in *; cbn [length] in *; lia) ltac:(lia) MI AXERR AXTOK (S (length (c1 :: ptr1))) 0)];
        [atp_st_eq| lia| unfold zlength; cbn [length]; lia| intros j Hj; lia]. }

    astep. astep. step. if_cases K3; zify_cond K3.
    { eapply evt_eq; [| eapply AT634]; [atp_st_eq]. }
    astep. astep. step. if_cases K4; zify_cond K4.
    all: first [ eapply evt_eq; [| eapply AT634]; [atp_st_eq]
               | astep; stop_now; eapply W70; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| exact ERR| exact MU| exact WM| lia] ].
  Qed.
End Arr.
End WithCeiling0.

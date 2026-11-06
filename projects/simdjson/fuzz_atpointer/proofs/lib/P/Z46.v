(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Z9o Z44.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
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
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    unfold elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP, ATP_ELEM in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (ELX : LX_ERRNO = 563116) by reflexivity. rewrite ELX in ERR.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (munch_refl [(q - 48, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    hide AI.
    unfold implM. iprefix.
    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 4 step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unhide AI.
    assert (AI1 : AINV E m1).
    { eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (blocks_below _ _ _ _ HEAP Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    hide AI. destruct AI1 as (TAPEB & SBUFB & PTRB & DOCC).

    step. step. step.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) ltac:(destruct WF as (_ & ? & _); lia)) as TIR.
    astep. astep. step. astep.

    astep. step.
    assert (PTRB1 : bytes_at psegs m1 P (map (Z_to_bv 8) ptr)).
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

    apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRLO FRHI]. cbn [cells_size csize Nat.add] in FRHI.
    replace (q + -48 + Z.of_nat 16) with (q + -32) in FRHI by lia.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 48, q); (out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }

    assert (EPI : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) (m2 : mem) (jj : list byte) (s' : PState),
      rw_cells psegs m2 (q + -48) [CB 16 jj] -> rw_cells psegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -48) -> (exists errv' : word, rw_cells psegs m2 LX_ERRNO [C4 errv']) ->
      rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m m2 -> (exists j, rw_cells psegs m2 out [CB 24 j]) ->
      evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s')
        (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x275d8) fc None m2 (seg_rom psegs))).
    { intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 m2 jj s' EFRLO EFRHI EMI EST EERR EAUX EFA ESO EHEAP EPRES EOUT.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as EMU. pose proof (wmono_refl psegs m2) as EWM.
      do 4 step. step.
      release_frame EFRLO EST (q + -32). release_frame EFRHI EST q.
      step.
      apply evt_done. unfold hpost. do 15 eexists. exists m2. split; [reflexivity|].
      split; [exact EMI|]. split; [exact EST|]. split; [exact EERR|]. split; [exact EAUX|]. split; [exact EFA|]. split; [exact ESO|].
      unfold lvl_R. split; [exact EHEAP|]. split; [exact EPRES| exact EOUT]. }

    assert (W3 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (code lenr : Z) (m2 : mem) (ja jb oa ob oc od : list byte),
      rw_cells psegs m2 (q + -48) [CB 8 ja; CB 8 jb] -> rw_cells psegs m2 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells psegs m2 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -48) -> rw_cells psegs m2 LX_ERRNO [C4 errv] ->
      munch [(q - 48, q); (out, out + 24)] m m2 -> wmono psegs m m2 -> 0 <= code < 64 ->
      evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
        (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 code) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 lenr) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x275cc) fc None m2 (seg_rom psegs))).
    { intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 code lenr m2 ja jb oa ob oc od WFRLO WFRHI WOUT WMI WST WERR MU3 WM3 CR.
      rewrite ELX in WERR.
      hstep. hstep. hstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      destruct (rw_cells_forget _ _ _ _ WFRLO) as [jj WFRLO']. cbn [cells_size csize Nat.add] in WFRLO'.
      eapply EPI; [exact WFRLO'| exact WFRHI| exact WMI| exact WST| exists errv; rewrite ELX; exact WERR| | reflexivity| reflexivity| | |].
      - eapply rauxv_ok_frame; [exact AUX| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
          apply W_ok_stack; cbn; lia.
      - eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI].
      - destruct (rw_cells_forget _ _ _ _ WOUT) as [j' WOUT']. cbn [cells_size csize Nat.add] in WOUT'. exists j'. exact WOUT'. }

    lazymatch goal with |- implM _ _ _ ?Q ?ms =>
      assert (SCALAR : ttype (Tf (ae_tws E) i) <> t_arr -> ttype (Tf (ae_tws E) i) <> t_obj -> evt psegs (Q tt s) ms) end.
    { intros NE1 NE2. cbv beta. unfold t_arr, t_obj in NE1, NE2.
      apply (rw_cells_split_CB psegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.
      assert (TTR : 0 <= ttype (Tf (ae_tws E) i) < 256) by (unfold ttype; lia).

      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      astep. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K.

      assert (ZLR : 0 <= zlength ptr < 2^64) by (unfold zlength in *; lia).
      step. if_cases K0; zify_cond K0.
      -
        step. step. hstep. hstep. hstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        destruct (rw_cells_forget _ _ _ _ FRLO) as [jj FRLO']. cbn [cells_size csize Nat.add] in FRLO'.
        eapply EPI; [exact FRLO'| exact FRHI| exact MI| exact ST| exists errv; rewrite ELX; exact ERR| | reflexivity| reflexivity| | |].
        + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
        + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
        + eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
        + destruct (rw_cells_forget _ _ _ _ OUT) as [j' OUT']. cbn [cells_size csize Nat.add] in OUT'. exists j'. exact OUT'.
      -
        destruct ptr as [|c0 ptr']; [exfalso; apply K0; reflexivity|].
        assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
        assert (ZL : zlength (c0 :: ptr') = zlength ptr' + 1) by (unfold zlength; cbn [length]; lia).
        assert (ZL0 : 0 <= zlength ptr') by (unfold zlength; lia).
        pose proof (zbytes_read1 m1 P (c0 :: ptr') 0 PTRB1 ltac:(lia)) as RD0. cbn [Z.to_nat nth] in RD0. rewrite Z.add_0_r in RD0.
        astep. astep. step. if_cases K1; zify_cond K1.
        +
          astep. eapply W3; [exact FRLO| exact FRHI| exact OUT| exact MI| exact ST| rewrite ELX; exact ERR| exact MU| exact WM| lia].
        +
          astep. step. step.
          assert (P0' : 0 < P).
          { destruct BP as [E0|BP']; [exfalso; rewrite E0 in PL; unfold zlength in PL; cbn in PL; lia|].
            pose proof (in_blocks_range _ _ _ _ _ HEAP BP' ltac:(unfold zlength; lia)). lia. }
          step. call memchr_spec.
          1:{ rewrite unsigned_lit by lia. exact PTRB1. }
          1:{ rewrite !unsigned_lit by lia. unfold memchr_ok. change (126 mod 256) with 126.
              destruct (find_byte 126 (firstn (Z.to_nat (zlength (c0 :: ptr'))) (map (Z_to_bv 8) (c0 :: ptr')))); rewrite length_map; [left|]; unfold zlength; lia. }
          1:{ assumption. }
          rewrite !unsigned_lit by lia. change (126 mod 256) with 126. unfold memchr_res.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
          lazymatch goal with H : mem_inv psegs m2 |- _ => rename H into MI2 end.

          assert (A20 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (av lenr : Z),
            evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
              (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 av) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 lenr) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x275a8) fc None m2 (seg_rom psegs))).
          { intros. astep. step. eapply W3; [exact FRLO| exact FRHI| exact OUT| exact MI2| exact ST| exact ERR| exact MU| exact WM| lia]. }

          assert (A22 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (av lenr : Z),
            evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m) s)
              (MS (mkR x1 (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 P) (Z_to_bv 64 av) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 lenr) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x275c8) fc None m2 (seg_rom psegs))).
          { intros. astep. eapply W3; [exact FRLO| exact FRHI| exact OUT| exact MI2| exact ST| exact ERR| exact MU| exact WM| lia]. }
          destruct (find_byte 126 (firstn (Z.to_nat (zlength (c0 :: ptr'))) (map (Z_to_bv 8) (c0 :: ptr')))) as [ix|] eqn:FB.
          * pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_map in Hl.
            assert (IXR : 0 <= Z.of_nat ix < zlength (c0 :: ptr')) by (unfold zlength in *; lia).

            step. if_cases K2; zify_cond K2; try (exfalso; lia); [idtac]. clear K2.
            astep. astep. step. if_cases K3; zify_cond K3; try apply A20; [idtac].

            astep. step. if_cases K4; zify_cond K4; try apply A22; [idtac].

            astep.
            pose proof (zbytes_read1 m2 P (c0 :: ptr') (Z.of_nat ix + 1) PTRB1 ltac:(lia)) as RD1.
            pose proof (Forall_nth_Z _ (c0 :: ptr') (Z.to_nat (Z.of_nat ix + 1)) PTRF ltac:(unfold zlength in *; lia)) as C1R. cbv beta in C1R.
            astep. astep. astep. step. if_cases K5; zify_cond K5; first [apply A22 | apply A20].
          *
            step. if_cases K2; zify_cond K2; try (exfalso; lia); [idtac]. apply A20. }

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
          [exact AI2| exact PAT| exact TY| exact NXT| exact CLOSE| exact TILES| exact I0| lia| exact FRLO| lia| lia| lia| exact OUT| lia| exact OD| exact OB
          | exact HEAP2| exact AUX2| lia| exact ST| unfold arr_need, elem_need, ATP_LEAFX, RMALLOC_STACK; subst d; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
      cbv beta. intros [] s' ms' PO. unfold hpost in PO.
      destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & OUT3).
      replace (ret_pc (Z_to_bv 64 0x27558)) with (Z_to_bv 64 0x27558) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRLO; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU4. pose proof (wmono_refl psegs m3) as WM4.
      step.
      destruct (rw_cells_forget _ _ _ _ FRLO) as [jj FRLO']. cbn [cells_size csize Nat.add] in FRLO'.
      eapply EPI; [exact FRLO'| exact FRHI| exact MI3| exact ST3| exact ERR3| exact AUX3| exact FA3| exact SO3| exact HEAP3| | exact OUT3].
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
          [exact AI2| exact PAT| exact TY| exact NXT| exact CLOSE| exact TILES| exact I0| lia| exact FRLO| lia| lia| lia| exact OUT| lia| exact OD| exact OB
          | exact HEAP2| exact AUX2| lia| exact ST| unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK; subst d; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
      cbv beta. intros [] s' ms' PO. unfold hpost in PO.
      destruct PO as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & OUT3).
      replace (ret_pc (Z_to_bv 64 0x27530)) with (Z_to_bv 64 0x27530) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRLO; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FRHI; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU4. pose proof (wmono_refl psegs m3) as WM4.
      step.
      destruct (rw_cells_forget _ _ _ _ FRLO) as [jj FRLO']. cbn [cells_size csize Nat.add] in FRLO'.
      eapply EPI; [exact FRLO'| exact FRHI| exact MI3| exact ST3| exact ERR3| exact AUX3| exact FA3| exact SO3| exact HEAP3| | exact OUT3].
      eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_weaken; [exact PRES3| lia| intros b Hb; exact Hb| intros a Ha; exact Ha].
  Qed.
End Elem.
End WithCeiling0.

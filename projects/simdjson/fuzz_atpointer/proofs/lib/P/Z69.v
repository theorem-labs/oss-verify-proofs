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
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Z9o Z44 Z66 Z6f.
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

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.

  Lemma obj_noesc : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (out node i e c P L0 L sl : Z) (rest0 : list Z) (k : list Z) (REST : list (list Z)) (m0 m1 : mem) (ja js j4 jo : list byte)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    rw_cells psegs m1 (q + -224) [CB 72 ja] -> rw_cells psegs m1 (q + -152) [CB 24 js] ->
    rw_cells psegs m1 (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] ->
    rw_cells psegs m1 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells psegs m1 out [CB 24 jo] -> q <= out -> out + 24 <= ae_B E -> q <= ae_DOC E -> (out + 24 <= ae_DOC E \/ ae_DOC E + 24 <= out) ->
    AINV E m1 -> rw_cells psegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_B E ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    bytes_at psegs m1 (P + 1) (map (Z_to_bv 8) rest0) -> zlength rest0 = L0 -> k = firstn (Z.to_nat L) rest0 -> 0 <= L <= L0 -> L0 < 2^40 ->
    0 <= P -> P + 1 + L0 <= alloc_ceiling ->
    ((sl = 18446744073709551615 /\ REST = []) \/
     (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl)) ->
    RHEAP s (ae_LB E) m1 -> rauxv_ok m1 (ae_B E) -> stk psegs m1 (ae_lo E) (q + -224) -> ae_lo E <= q - obj_need d -> q mod 16 = 0 ->
    (exists errv' : word, rw_cells psegs m1 LX_ERRNO [C4 errv']) -> mem_inv psegs m1 ->
    lx_pres (ae_LB E) q [(out, out + 24)] m0 m1 ->
    implM psegs (atp_walk lops (k :: REST)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (P + 1)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sl) x19 (Z_to_bv 64 node) (Z_to_bv 64 L) x22 x23 x24 x25 (Z_to_bv 64 out) (Z_to_bv 64 L0) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2818c) fc None m1 (seg_rom psegs)).
  Proof.
    intros until x31. intros SCR STRS REC FRB OUTR QO OB QD OD AI NODE QN NB TY NXT TILES I0 EN KEYB ZL0 EK LL0 L040 P0 PCEIL RC HEAP AUX ST LO Q16 ERR MI PRES.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP PP0 [CEIL GLO] B63 [DL DB]].
    unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP in *. unfold obj_saved in FRB.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct ERR as [errv ERR]. assert (ELX : LX_ERRNO = 563116) by reflexivity. rewrite ELX in ERR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (aenv_ranges E s m1 OK HEAP) as (TR & SR & PR).
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 224, q); (out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    pose proof (munch_refl [(q - 224, q); (out, out + 24)]%Z m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    hide AI. hide KEYB. pose proof AI as AI1. unhide AI1. destruct AI1 as (TAPEB & SBUFB & PTRB & DOCC).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_obj; lia) ltac:(unfold t_obj; lia)) as TIR.
    unfold implM. iprefix.

    step. step. step. astep. astep. step. astep. rewrite TY. unfold t_obj. astep. astep. astep. step. if_false.

    astep. astep. astep. astep. step. if_true. astep. astep. astep. astep. astep. step. if_false. astep. astep.
    rewrite land32_tnext by lia. rewrite NXT. step.

    astep. astep.
    set (KK := fun ms' : machine_state => impl psegs (at_node psegs) (atp_walk lops (k :: REST) s)
                (epost (fun p => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) (snd p))) ms') in *.

    assert (NF : forall (m2 : mem) (ja2 : list byte) (z1 z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z25 z28 z29 z30 z31 : word),
      rw_cells psegs m2 (q + -224) [CB 72 ja2] -> rw_cells psegs m2 (q + -152) [CB 24 js] ->
      rw_cells psegs m2 (q + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 j4] ->
      rw_cells psegs m2 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> rw_cells psegs m2 out [CB 24 jo] ->
      RHEAP s (ae_LB E) m2 -> rauxv_ok m2 (ae_B E) -> stk psegs m2 (ae_lo E) (q + -224) -> mem_inv psegs m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 ->
      rw_cells psegs m2 LX_ERRNO [C4 errv] ->
      evt psegs KK (MS (mkR z1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) z5 z6 z7 (Z_to_bv 64 0) z9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
                          z18 z19 z20 z21 z22 z23 (Z_to_bv 64 20) z25 (Z_to_bv 64 out) (Z_to_bv 64 L0) z28 z29 z30 z31)
                     F (Z_to_bv 64 0x28348) fc None m2 (seg_rom psegs))).
    { intros m2 ja2 z1 z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z25 z28 z29 z30 z31 SCR2 STRS2 REC2 FRB2 OUTR2 HEAP2 AUX2 ST2 MI2 PRES2 ERR2.
      unfold obj_saved in FRB2. rewrite ELX in ERR2.
      pose proof (munch_refl [(q - 128, q - 104)]%Z m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.

      hstep. hstep. hstep. step. if_false. step. name_mem m3.
      subst KK. stop_now.
      pose proof (rw_cells_join _ _ _ _ _ SCR2 STRS2 ltac:(cbn [cells_size csize Nat.add]; lia)) as FRA. cbn [app] in FRA.
      destruct (rw_cells_forget _ _ _ _ FRA) as [ja3 FRA']. cbn [cells_size csize Nat.add] in FRA'.
      apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC2. destruct REC2 as [RA RB]. cbn [cells_size csize Nat.add] in RB.
      apply rec_tail_merge in RB.
      pose proof (rw_cells_join _ _ _ _ _ RA RB ltac:(cbn [cells_size csize Nat.add]; lia)) as REC3. cbn [app] in REC3.
      pose proof (rec_recast _ _ _ _ _ REC3 eq_refl) as REC'. cbn [cbytes] in REC'.
      assert (CLI2 : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 128, q - 104)] a).
      { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      eapply (obj_out E OK); [exact FRA'| exact REC'| unfold obj_saved; exact FRB2| exact OUTR2| exact QO| exact OB| exact MI2| exact ST2| lia| exists errv; rewrite ELX; exact ERR2
                     | | reflexivity| reflexivity| | ].
      - eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      - eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU2| exact WM2| exact CLI2]. }
    step. if_cases KEM; zify_cond KEM.
    2:{
      astep. astep. step. subst KK.
      eapply NF; [exact SCR| exact STRS| exact REC| unfold obj_saved; exact FRB| exact OUTR| exact HEAP| exact AUX| exact ST| exact MI| exact PRES| rewrite ELX; exact ERR]. }

    apply (rw_cells_split_CB psegs _ _ [] 72 ja [] [8;8;8;8;8;8;8;8;8]%nat) in SCR; [|reflexivity]. cbn [mk_CB_cells app] in SCR.
    hstep. step. hstep. hstep. astep. astep. hstep. step. astep. astep. astep. astep. hstep. astep. astep. astep. astep. name_mem m2.

    assert (HEAP2 : RHEAP s (ae_LB E) m2).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 (ae_B E)).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES2 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m2).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    assert (AI2 : AINV E m2).
    { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
      - intros a Ha. cbn [outside]. lia. }
    try clear TAPEB; try clear SBUFB; try clear PTRB; try clear DOCC. pose proof AI2 as (TAPEB & SBUFB & PTRB & DOCC).
    assert (KEYB2 : bytes_at psegs m2 (P + 1) (map (Z_to_bv 8) rest0)).
    { unhide KEYB. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact KEYB|]. intros a Ha. rewrite length_map in Ha. unfold zlength in ZL0. cbn [outside]. lia. }
    pose proof (bytes_at_firstn _ _ _ (Z.to_nat L) KEYB2) as KEYL. rewrite firstn_map, <- EK in KEYL.
    lazymatch goal with H : rw_cells psegs m2 (q + -224) _ |- _ => rename H into SCR2 end.
    pose proof SCR2 as M64. apply (proj1 (rw_cells_app _ _ [_; _; _; _; _; _; _; _] _)) in M64. destruct M64 as [_ M64]. cbn [cells_size csize Nat.add] in M64.
    lazymatch type of M64 with rw_cells _ _ ?a _ => replace a with (q + -224 + 64) in M64 by lia end.
    eapply evt_eq; [| eapply (obj_key_loop1 E OK d KK m2 F fc e (q + -224) (P + 1) L (map (Z_to_bv 8) k) gp _ _ _ _ _ _ _ _ _ _
                               TAPEB SBUFB KEYL ltac:(rewrite length_map, EK, firstn_length_le by (unfold zlength in ZL0; lia); lia) ltac:(lia) ltac:(lia) M64 EN MI SR)
                        with (n := S (Z.to_nat (e - (i + 1)))) (it := i + 1) (c' := c)];
      [atp_st_eq| | | exact TILES| exact KEM| lia| lia].
    -
      intros it j' w1 wa0 wa1 wa2 wa3 wa4 w23 STR EL IT0 ITE.
      pose proof (munch_refl [(q - 128, q - 104)]%Z m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
      astep. astep. step. step. step. step. step.
      hstep. hstep. hstep. step. if_true. name_mem m3.
      subst KK. apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
      apply implM_atp_walk_plain.
      apply (rw_cells_merge psegs _ _ [] [_; _; _; _; _; _; _; _; _] []) in SCR2. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR2.
      apply (proj1 (rw_cells_app _ _ [_; _] _)) in REC. destruct REC as [NODE' RT]. cbn [cells_size csize Nat.add] in RT.
      replace (q + -128 + Z.of_nat 16) with (q + -112) in RT by lia.
      assert (AI3 : AINV E m3).
      { eapply AINV_agree; [exact AI2| eapply agree_on_of_munch; [exact MU2| exact WM2]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      assert (CLI2 : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 128, q - 104)] a).
      { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
      eapply (obj_found E OK d HELEM ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s s out P L0 sl (it + 1) j' REST m0 m3);
        [exact SCR2| exact STRS| exact NODE'| exact RT| unfold obj_saved; exact FRB| exact OUTR| exact QO| exact OB| exact QD| exact AI3| exact EL| lia| lia| exact RC| lia
        | | | exact ST| unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK; lia| exact Q16| exists errv; rewrite ELX; exact ERR| exact MI| reflexivity| reflexivity| ].
      + eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU2| exact WM2| exact CLI2].
    -
      intros w1 w8 wa0 wa1 wa2 wa3 wa4 w23.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
      astep. astep. step. step. step. step. astep. step.
      apply (rw_cells_merge psegs _ _ [] [_; _; _; _; _; _; _; _; _] []) in SCR2. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SCR2.
      eapply NF; [exact SCR2| exact STRS| exact REC| unfold obj_saved; exact FRB| exact OUTR| exact HEAP2| exact AUX2| exact ST| exact MI| exact PRES2| rewrite ELX; exact ERR].
  Qed.
End Obj.
End WithCeiling0.

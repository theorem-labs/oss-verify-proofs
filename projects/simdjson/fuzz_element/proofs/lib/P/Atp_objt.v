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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs.
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

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Definition obj_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rec_recast : forall m A (w0 w1 : word) (c2 : cell),
  rw_cells psegs m A [C8 w0; C8 w1; c2] -> csize c2 = 8%nat -> rw_cells psegs m A [CB 8 (le8 w0); CB 8 (le8 w1); CB 8 (cbytes c2)].
Proof.
  intros m A w0 w1 c2 H Hc. pose proof H as [[W _] _].
  eapply rw_cells_recast; [exact H| | reflexivity| cbn [cells_size csize]; rewrite Hc; reflexivity].
  cbn [cells_wf cell_wf] in W |- *. rewrite !length_le8. destruct c2; cbn in Hc, W |- *; try lia; tauto.
Qed.

Lemma rec_tail_merge : forall m A (e : word) (j : list byte) rest,
  rw_cells psegs m A (C4 e :: CB 4 j :: rest) -> rw_cells psegs m A (CB 8 (le4 e ++ j) :: rest).
Proof.
  intros m A e j rest H. pose proof H as [[W _] _]. cbn [cells_wf cell_wf] in W.
  eapply rw_cells_recast; [exact H| | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity| cbn [cells_size csize]; reflexivity].
  cbn [cells_wf cell_wf]. rewrite length_app, length_le4. split; [lia| tauto].
Qed.

Lemma rw_cells_join : forall m A B cs1 cs2,
  rw_cells psegs m A cs1 -> rw_cells psegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells psegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app _ _ _ _)). split; assumption. Qed.

Section Obj.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.

  Lemma obj_epi : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s s' : PState) (out : Z) (m0 m2 : mem) (ja : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells psegs m2 (q + -224) [CB 120 ja] -> rw_cells psegs m2 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -224) -> ae_lo E <= q - 224 -> (exists errv' : word, rw_cells psegs m2 LX_ERRNO [C4 errv']) ->
    rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 -> (exists j, rw_cells psegs m2 out [CB 24 j]) ->
    evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) s')
      (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3df3c) fc None m2 (seg_rom psegs)).
  Proof.
    intros until x31. intros FRA FRB MI ST LO ERR AUX FA SO HEAP PRES OUT.
    unfold obj_saved in FRB.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    do 13 step. step.
    release_frame FRA ST (q + -104). release_frame FRB ST q.
    step.
    apply evt_done. unfold hpost. do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact FA|]. split; [exact SO|].
    unfold lvl_R. split; [exact HEAP|]. split; [exact PRES| exact OUT].
  Qed.

  Lemma obj_out : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s s' : PState) (out : Z) (m0 m2 : mem) (ja r0 r1 r2 jo : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
    rw_cells psegs m2 (q + -224) [CB 96 ja] -> rw_cells psegs m2 (q + -128) [CB 8 r0; CB 8 r1; CB 8 r2] ->
    rw_cells psegs m2 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells psegs m2 out [CB 24 jo] -> q <= out -> out + 24 <= ae_B E ->
    mem_inv psegs m2 -> stk psegs m2 (ae_lo E) (q + -224) -> ae_lo E <= q - 224 -> (exists errv' : word, rw_cells psegs m2 LX_ERRNO [C4 errv']) ->
    rauxv_ok m2 (ae_B E) -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    RHEAP s' (ae_LB E) m2 -> lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 ->
    evt psegs (hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0) s')
      (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               (Z_to_bv 64 out) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x3df24) fc None m2 (seg_rom psegs)).
  Proof.
    intros until x31. intros FRA REC FRB OUT QO OB MI ST LO ERR AUX FA SO HEAP PRES. unfold obj_saved in FRB.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    unfold GLOBALS_TOP in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct ERR as [errv ERR]. assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    pose proof (munch_refl [(out, out + 24)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [clear - HX; lia| exact I]. }
    apply (rw_cells_split_CB psegs _ _ [] 24 jo [] [8;8;8]%nat) in OUT; [|reflexivity]. cbn [mk_CB_cells app] in OUT.

    step. step. step. hstep. hstep. hstep. name_mem m3.
    pose proof (rw_cells_join _ _ _ _ _ FRA REC ltac:(cbn [cells_size csize Nat.add]; lia)) as FRA'. cbn [app] in FRA'. destruct (rw_cells_forget _ _ _ _ FRA') as [ja' FRA'']. cbn [cells_size csize Nat.add] in FRA''.
    eapply obj_epi; [exact FRA''| unfold obj_saved; exact FRB| exact MI| exact ST| exact LO| exists errv; rewrite ELX; exact ERR| | exact FA| exact SO| | |].
    - eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
    - eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
    - eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
    - destruct (rw_cells_forget _ _ _ _ OUT) as [j' OUT']. cbn [cells_size csize Nat.add] in OUT'. exists j'. exact OUT'.
  Qed.

  Lemma obj_found : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s s' : PState) (out P L0 sl vj j' : Z) (REST : list (list Z)) (m0 m2 : mem) (ja jo' j4 jo : list byte)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x28 x29 x30 x31 : word),
    rw_cells psegs m2 (q + -224) [CB 72 ja] -> rw_cells psegs m2 (q + -152) [CB 24 jo'] ->
    rw_cells psegs m2 (q + -128) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 vj)] -> rw_cells psegs m2 (q + -112) [C4 (Z_to_bv 64 0); CB 4 j4] ->
    rw_cells psegs m2 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells psegs m2 out [CB 24 jo] -> q <= out -> out + 24 <= ae_B E -> q <= ae_DOC E ->
    AINV E m2 -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' -> 0 <= vj -> j' <= ae_n E - 1 ->
    ((sl = 18446744073709551615 /\ REST = []) \/
     (0 <= sl < L0 /\ exists r, REST = ptr_segs (47 :: r) /\ ptr_at E (P + 1 + sl) (47 :: r) /\ zlength (47 :: r) = L0 - sl)) -> 0 <= L0 < 2^62 ->
    RHEAP s' (ae_LB E) m2 -> rauxv_ok m2 (ae_B E) -> stk psegs m2 (ae_lo E) (q + -224) -> ae_lo E <= q - obj_need d -> q mod 16 = 0 ->
    (exists errv' : word, rw_cells psegs m2 LX_ERRNO [C4 errv']) -> mem_inv psegs m2 -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    lx_pres (ae_LB E) q [(out, out + 24)] m0 m2 ->
    implM psegs (atp_walk lops REST) s'
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0))
      (MS (mkR x1 (Z_to_bv 64 (q + -224)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (P + 1)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sl) x19 x20 x21 x22 x23 (Z_to_bv 64 0) x25 (Z_to_bv 64 out) (Z_to_bv 64 L0) x28 x29 x30 x31)
          F (Z_to_bv 64 0x3deec) fc None m2 (seg_rom psegs)).
  Proof.
    intros until x31. intros FRA0 OUT' NODE' RT FRB OUTR QO OB QD AI EL VJ0 JN RC L062 HEAP AUX ST LO Q16 ERR MI FA SO PRES.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, GLOBALS_TOP in *. unfold obj_saved in FRB.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct ERR as [errv ERR]. assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) q [(out, out + 24)] a -> outside [(q - 224, q); (out, out + 24)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    unfold implM. iprefix.

    astep. step. if_cases KS; zify_cond KS; rewrite ?land64_mod in KS.
    {
      destruct RC as [[_ ->]|[SL _]]; [| exfalso; lia].
      stop_now.
      pose proof (rec_tail_merge _ _ _ _ _ RT) as RT'.
      pose proof (rw_cells_join _ _ _ _ _ NODE' RT' ltac:(cbn [cells_size csize Nat.add]; lia)) as REC0. cbn [app] in REC0.
      pose proof (rec_recast _ _ _ _ _ REC0 eq_refl) as REC. cbn [cbytes] in REC.
      pose proof (rw_cells_join _ _ _ _ _ FRA0 OUT' ltac:(cbn [cells_size csize Nat.add]; lia)) as FRA1. cbn [app] in FRA1.
      destruct (rw_cells_forget _ _ _ _ FRA1) as [ja1 FRA]. cbn [cells_size csize Nat.add] in FRA.
      eapply obj_out; [exact FRA| exact REC| unfold obj_saved; exact FRB| exact OUTR| exact QO| exact OB| exact MI| exact ST| lia| exists errv; rewrite ELX; exact ERR
                     | exact AUX| exact FA| exact SO| exact HEAP| exact PRES]. }
    destruct RC as [[SL _]|(SL & r & -> & PAT' & ZL)]; [exfalso; lia|].

    step. if_lia. astep. astep. astep. astep. step.
    replace (Z_to_bv 64 (L0 - sl)) with (Z_to_bv 64 (zlength (47 :: r))) by (f_equal; lia).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ'.
    apply evt_done. to_implM_at (fun _ : unit => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m0)).
    pose proof HELEM as HE. unfold atp_elem_stmt in HE.
    eapply implM_post_evt.
    { eapply (HE (47 :: r) vj j') with (jo := jo');
        [exact AI| exact PAT'| exact EL| exact VJ0| lia| exact NODE'| lia| lia| lia| exact OUT'| lia| lia| lia
        | exact HEAP| exact AUX| lia| exact ST| unfold elem_need, ATP_LEAFX, RMALLOC_STACK; lia| clear - Q16; lia| rewrite ELX; exact ERR| exact MI]. }
    cbv beta. intros [] s'' ms'' PO. unfold hpost in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MI3 & ST3 & [errv3 ERR3] & AUX3 & FA3 & SO3 & RR).
    unfold lvl_R in RR. destruct RR as (HEAP3 & PRES3 & [jc OUTC]).
    replace (ret_pc (Z_to_bv 64 0x3df0c)) with (Z_to_bv 64 0x3df0c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRA0; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in NODE'; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in RT; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRB; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG3) in OUTR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    rewrite ELX in ERR3.
    pose proof (munch_refl [(q - 224, q); (out, out + 24)]%Z m3) as MU3. pose proof (wmono_refl psegs m3) as WM3.
    apply (rw_cells_split_CB psegs _ _ [] 24 jc [] [8;8;4;4]%nat) in OUTC; [|reflexivity]. cbn [mk_CB_cells app] in OUTC.

    step. step. step. hstep. hstep. hstep. name_mem m4.

    destruct (rw_cells_forget _ _ _ _ OUTC) as [jj OUTC']. cbn [cells_size csize Nat.add] in OUTC'.
    pose proof (rw_cells_join _ _ _ _ _ FRA0 OUTC' ltac:(cbn [cells_size csize Nat.add]; lia)) as FRA1. cbn [app] in FRA1.
    destruct (rw_cells_forget _ _ _ _ FRA1) as [ja1 FRA]. cbn [cells_size csize Nat.add] in FRA.
    pose proof (rec_tail_merge _ _ _ _ _ RT) as RT'.
    pose proof (rw_cells_join _ _ _ _ _ NODE' RT' ltac:(cbn [cells_size csize Nat.add]; lia)) as REC0. cbn [app] in REC0.
    pose proof (rec_recast _ _ _ _ _ REC0 eq_refl) as REC. cbn [cbytes] in REC.
    assert (PRES4 : lx_pres (ae_LB E) q [(out, out + 24)] m0 m4).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_trans; [| eapply lx_pres_of_munch; [exact MU3| exact WM3| exact CLI]].
      eapply lx_pres_sub; [exact PRES3| lia| intros b Hb; exact Hb|].
      intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| lia]. }
    eapply obj_out; [exact FRA| exact REC| unfold obj_saved; exact FRB| exact OUTR| exact QO| exact OB| exact MI3| exact ST3| lia| exists errv3; rewrite ELX; exact ERR3
                   | | rewrite FA3; exact FA| rewrite SO3; exact SO| | exact PRES4].
    - eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
    - eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
  Qed.

End Obj.
End WithCeiling0.

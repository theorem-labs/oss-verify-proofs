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

Definition ATP_ROOT_STACK : Z := 286900.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition atp_root_post (E : aenv) (sp0 : Z) (m : mem) (s s' : PState) (m' : mem) : Prop :=
  RHEAP s' (ae_LB E) m' /\ lx_pres (ae_LB E) sp0 [(sp0, sp0 + 24); (sp0 + 176, sp0 + 192)] m m'
  /\ mem_inv psegs m' /\ stk psegs m' (ae_lo E) sp0 /\ (exists errv' : word, rw_cells psegs m' LX_ERRNO [C4 errv'])
  /\ rauxv_ok m' (ae_B E) /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  /\ (exists j, rw_cells psegs m' sp0 [CB 24 j]) /\ (exists j, rw_cells psegs m' (sp0 + 176) [CB 16 j]).

Definition atp_root_stmt (E : aenv) : Prop :=
  forall (A : Type) (k : unit -> M PState A) (Q : A -> PState -> machine_state -> Prop)
         (sp0 V : Z) (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (errv : word) (jo jn : list byte),
    AINV E m ->
    rw_cells psegs m (sp0 + 24) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 1)] ->
    rw_cells psegs m (sp0 + 128) [C8 (Z_to_bv 64 V)] ->
    rw_cells psegs m (V + 16) [C8 (Z_to_bv 64 (ae_PTR E)); C8 (Z_to_bv 64 (zlength (ae_p1 E)))] -> in_blocks (ae_LB E) V 32 ->
    rw_cells psegs m sp0 [CB 24 jo] -> rw_cells psegs m (sp0 + 176) [CB 16 jn] ->
    sp0 + 24 <= ae_DOC E -> (ae_DOC E + 24 <= sp0 + 176 \/ sp0 + 192 <= ae_DOC E) -> sp0 + 192 <= ae_B E ->
    RHEAP s (ae_LB E) m -> rauxv_ok m (ae_B E) ->
    stk psegs m (ae_lo E) sp0 -> ae_lo E <= sp0 - ATP_ROOT_STACK -> sp0 mod 16 = 0 ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
    (forall (s' : PState) (m' : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       atp_root_post E sp0 m s s' m' ->
       implM psegs (k tt) s' Q
         (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x2735c) fc None m' (seg_rom psegs))) ->
    implM psegs (mbind (atp_walk lops (ptr_segs (ae_p1 E))) k) s Q
      (MS (mkR ra (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x273a8) fc None m (seg_rom psegs)).

Section Root.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Hypothesis HOBJ : atp_obj_stmt E (Nat.pred TAPE_MAX_DEPTH).
  Hypothesis HARR : atp_arr_stmt E (Nat.pred TAPE_MAX_DEPTH).

  Lemma atp_root_cps : atp_root_stmt E.
  Proof.
    unfold atp_root_stmt. intros until jn.
    intros AI RES VEC STR1 VB OUT NODE OD ND NB HEAP AUX ST LO Q16 ERR MI HK.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    unfold ATP_ROOT_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= ae_lo E) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [ELR NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (ELX : LX_ERRNO = 563116) by reflexivity. rewrite ELX in ERR.
    pose proof (in_blocks_range _ _ _ _ _ HEAP VB ltac:(lia)) as VR.
    assert (BLB : forall a, in_block (ae_LB E) a -> a < alloc_ceiling) by (intros a Ha; exact (proj2 (blocks_below _ _ _ _ HEAP Ha))).
    pose proof (munch_refl [(sp0, sp0 + 24); (sp0 + 176, sp0 + 192)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof AI as AI0. destruct AI0 as (TAPEB & SBUFB & PTRB & DOCC). hide AI.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ ELR ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (Tf (ae_tws E) 1) < 256) by (unfold ttype; lia).
    unfold implM. iprefix.

    step. step. step. step. astep. astep. step. step. step. astep.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client (ae_LB E) sp0 [(sp0, sp0 + 24); (sp0 + 176, sp0 + 192)] a ->
                  outside [(sp0, sp0 + 24); (sp0 + 176, sp0 + 192)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. clear - HX. lia. }
    assert (PAT : ptr_at E (ae_PTR E) (ae_p1 E)) by (exists []; split; [reflexivity| unfold zlength; cbn; lia]).
    destruct (elem_view_of (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any (fun c cv H => H) HSN TAPE_MAX_DEPTH 1 _ ELR ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e c Ed TY Ej NXT CLOSE TILES|d' e c Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    1-3: assert (NE : ttype (Tf (ae_tws E) 1) <> 91 /\ ttype (Tf (ae_tws E) 1) <> 123)
           by (unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str in TY; lia).
    1-3: astep; step; if_cases K1; zify_cond K1; try (exfalso; lia); [idtac]; astep; step; if_cases K2; zify_cond K2; try (exfalso; lia); [idtac];
         apply evt_done; to_implM; apply implM_atp_walk_stop_k; apply HK;
         unfold atp_root_post; (split; [exact HEAP|]); (split; [apply lx_pres_refl|]); (split; [exact MI|]); (split; [exact ST|]);
         (split; [exists errv; rewrite ELX; exact ERR|]); (split; [exact AUX|]); (split; [reflexivity|]); (split; [reflexivity|]);
         (split; [exists jo; exact OUT| exists jn; exact NODE]).
    -
      replace d' with (Nat.pred TAPE_MAX_DEPTH) in * by (rewrite Ed; reflexivity).
      rewrite TY. unfold t_arr. astep. step. if_true.
      apply (rw_cells_split_CB psegs _ _ [] 16 jn [] [8;8]%nat) in NODE; [|reflexivity]. cbn [mk_CB_cells app] in NODE.
      hstep. hstep. step. step. step. name_mem m1.
      assert (AI1 : AINV E m1).
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      assert (HEAP1 : RHEAP s (ae_LB E) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres (ae_LB E) sp0 [(sp0, sp0 + 24); (sp0 + 176, sp0 + 192)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      apply evt_done. to_implM. eapply implM_bind.
      { eapply (HARR (ae_p1 E) 1 e c sp0 sp0 (sp0 + 176) (ae_PTR E)) with (jo := jo);
          [exact AI1| exact PAT| exact TY| exact NXT| exact CLOSE| exact TILES| lia| lia| exact NODE| lia| lia| lia| exact OUT| lia| lia| lia
          | exact HEAP1| exact AUX1| lia| exact ST| unfold arr_need, elem_need, ATP_LEAFX, RMALLOC_STACK, TAPE_MAX_DEPTH; cbn [Nat.pred]; lia| exact Q16| rewrite ELX; exact ERR| exact MI]. }
      cbv beta. intros [] s' ms' PO. unfold hpost in PO.
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP2 & PRES2 & OUT2).
      replace (ret_pc (Z_to_bv 64 0x2740c)) with (Z_to_bv 64 0x2740c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
      apply (rw_cells_agree _ _ _ _ _ AG2) in NODE; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
      unfold implM. iprefix. step. apply evt_done. apply HK.
      unfold atp_root_post. split; [exact HEAP2|]. split.
      { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_weaken; [exact PRES2| lia| intros b Hb; exact Hb| intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; lia]. }
      split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact OUT2|].
      destruct (rw_cells_forget _ _ _ _ NODE) as [j' NODE']. cbn [cells_size csize Nat.add] in NODE'. exists j'. exact NODE'.
    -
      replace d' with (Nat.pred TAPE_MAX_DEPTH) in * by (rewrite Ed; reflexivity).
      rewrite TY. unfold t_obj. astep. step. if_false. astep. step. if_false.
      apply (rw_cells_split_CB psegs _ _ [] 16 jn [] [8;8]%nat) in NODE; [|reflexivity]. cbn [mk_CB_cells app] in NODE.
      hstep. hstep. step. step. step. name_mem m1.
      assert (AI1 : AINV E m1).
      { unhide AI. eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
        - intros a Ha. pose proof (BLB a Ha). cbn [outside]. lia.
        - intros a Ha. cbn [outside]. lia. }
      assert (HEAP1 : RHEAP s (ae_LB E) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 (ae_B E)).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres (ae_LB E) sp0 [(sp0, sp0 + 24); (sp0 + 176, sp0 + 192)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      apply evt_done. to_implM. eapply implM_bind.
      { eapply (HOBJ (ae_p1 E) 1 e c sp0 sp0 (sp0 + 176) (ae_PTR E)) with (jo := jo);
          [exact AI1| exact PAT| exact TY| exact NXT| exact CLOSE| exact TILES| lia| lia| exact NODE| lia| lia| lia| exact OUT| lia| lia| lia
          | exact HEAP1| exact AUX1| lia| exact ST| unfold obj_need, elem_need, ATP_LEAFX, RMALLOC_STACK, TAPE_MAX_DEPTH; cbn [Nat.pred]; lia| exact Q16| rewrite ELX; exact ERR| exact MI]. }
      cbv beta. intros [] s' ms' PO. unfold hpost in PO.
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP2 & PRES2 & OUT2).
      replace (ret_pc (Z_to_bv 64 0x273f4)) with (Z_to_bv 64 0x273f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
      apply (rw_cells_agree _ _ _ _ _ AG2) in NODE; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
      unfold implM. iprefix. step. apply evt_done. apply HK.
      unfold atp_root_post. split; [exact HEAP2|]. split.
      { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_weaken; [exact PRES2| lia| intros b Hb; exact Hb| intros a Ha; cbn [rin_ivs fst snd] in Ha |- *; lia]. }
      split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact OUT2|].
      destruct (rw_cells_forget _ _ _ _ NODE) as [j' NODE']. cbn [cells_size csize Nat.add] in NODE'. exists j'. exact NODE'.
  Qed.
End Root.
End WithCeiling0.

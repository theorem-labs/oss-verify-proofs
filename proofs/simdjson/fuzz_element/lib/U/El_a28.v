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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_arrl El_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Atp_kitu El_acc_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Str_tac.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section A28.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition at_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo OUT : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(q - 144, q); (OUT, OUT + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
      /\ (exists (w0 w1 ew : word) od, rw_cells usegs m' OUT [C8 w0; C8 w1; C4 ew; CB 4 od]).

  Ltac fin_at := apply evt_done; unfold at_post; do 16 eexists;
    split; [atp_st_eq_goal|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption| do 4 eexists; eassumption].

  Lemma at_spec : forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node OUT idx lo : Z) (jo : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m ->
    rw_cells usegs m OUT [CB 24 jo] -> ae_lo E <= OUT -> OUT + 24 <= ae_B E -> (OUT + 24 <= node \/ node + 16 <= OUT) ->
    (OUT + 24 <= ae_DOC E \/ ae_DOC E + 16 <= OUT) -> ae_lo E <= node -> node + 16 <= ae_B E -> 0 <= idx < 2^64 ->
    stk usegs m lo q -> ae_lo E <= lo -> lo <= q - 144 -> q <= OUT -> q <= node -> q <= ae_DOC E ->
    evt usegs (at_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OUT m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 node) (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_AT) fc None m (seg_rom usegs)).
  Proof.
    intros until jo. intros AI ROOT HEAP MI OUTC O0 O1 ONODE ODOC N0 N1 IDX ST LOLO LOQ QO QN QD.
    destruct (acc_facts E OK s m HEAP) as ((T0 & TH & T8) & (S0 & SH) & (NR & SNR) & (CEIL & DB & B63 & D8) & TIR & EL).
    pose proof alloc_ceiling_range as CR.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _ _].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof HEAP as HEAP0. hide HEAP0. clear HEAP.
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_AT. clear PTRB SBUFB.
    pose proof (length_map (Z_to_bv 64) (ae_tws E)) as LMT.
    pose proof (munch_refl [(q - 144, q); (OUT, OUT + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    apply (rw_cells_split_CB usegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUTC; [|reflexivity]. cbn [mk_CB_cells app] in OUTC.

    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8; 8; 8; 4; 4; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step.
    astep. step. if_lia.
    step. zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
    step. astep. step. step. acc_tix E 0x3dc7c.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDB.
    astep. step. step. if_cases K; zify_cond K.
    - step. if_lia. step. lstep. lstep. lstep.
      astep. astep. astep. astep. step. release_frame FR ST q. step. fin_at.
    - rewrite ?a_u8_small in K by lia.
      destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN TAPE_MAX_DEPTH 1 (ae_n E - 1) EL ltac:(lia) ltac:(lia))
        as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES];
        pose proof TY as TYc; unfold ty in TYc;
        unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in TYc; try lia.
      pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TILES) as TLE.
      astep. astep. lstep. lstep. lstep. step. step. step. step.
      apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
      replace (q + -64 + Z.of_nat 8) with (q + -56) in FR by lia.
      apply (proj1 (rw_cells_app _ _ [_; _] _)) in FR. destruct FR as [FRN FR]. cbn [cells_size csize Nat.add] in FR.
      replace (q + -56 + Z.of_nat 16) with (q + -40) in FR by lia.
      name_mem mc. unhide HEAP0.
      assert (HP1 : RHEAP s (ae_LB E) mc).
      { eapply LH_frame; [exact HEAP0| exact MU| exact WM|]. constructor; [apply W_ok_stack; lia|]. constructor; [apply W_ok_stack; lia| constructor]. }
      try replace (q + -64 + 8) with (q + -56) by lia.
      eapply evt_cut.
      { eapply (arrat_spec E OK d'); [exact FRN| lia| lia| exact TAPEB| exact DOCC| exact TY| exact NXT| exact TILES| lia| lia
          | exact OUTC| lia| lia| exact HP1| exact ST| lia| lia| exact MI| lia| lia]. }
      intros ms' PO. unfold arrat_post in PO.
      destruct PO as (y0 & y1 & y2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & y3 & y4 & y5 & y6 & m2 & r0 & it & code & -> & MU2 & WM2 & MI2 & ST2 & OUT2 & RES2).
      acc_tr FR0 MU2 WM2. acc_tr FRN MU2 WM2.
      acc_ret 0x3dcac FR MU WM MI HP1 ST MU2 WM2 MI2 RES2 ST2.
      step. astep. astep. astep. astep. step.
      release_frame FR0 ST (q + -56). release_frame FRN ST (q + -40). release_frame FR ST q. step. fin_at.
  Qed.
End A28.
End WithCeiling0.

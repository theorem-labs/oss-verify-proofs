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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_arrl El_defs.
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
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section A28.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma at_iter_loop : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (d : nat) (e spv OUT DOC : Z)
      (x1 x3 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt5 xt6 : word),
    bytes_at psegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> e + 1 <= ae_n E - 1 -> mem_inv psegs m ->
    (forall (it j' : Z) (xa2 xt2 xt3 xt4 : word),
       elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt2 x8 x9
                          (Z_to_bv 64 OUT) (Z_to_bv 64 (ae_TAPE E)) xa2 (Z_to_bv 64 DOC) (Z_to_bv 64 it) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295)
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x3c8c4) fc None m (seg_rom psegs))) ->
    (forall (xa2 xa4 xt2 xt3 xt4 : word),
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt2 x8 x9
                          (Z_to_bv 64 OUT) (Z_to_bv 64 (ae_TAPE E)) xa2 (Z_to_bv 64 DOC) xa4 (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295)
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x3c828) fc None m (seg_rom psegs))) ->
    forall (n : nat) (it c' : Z) (xa2 xt2 xt3 xt4 : word),
      tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt2 x8 x9
                         (Z_to_bv 64 OUT) (Z_to_bv 64 (ae_TAPE E)) xa2 (Z_to_bv 64 DOC) (Z_to_bv 64 it) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295)
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x3c868) fc None m (seg_rom psegs)).
  Proof.
    intros K m F fc d e spv OUT DOC x1 x3 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt5 xt6 TAPEB EN MI XFOUND XNF.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' xa2 xt2 xt3 xt4 TI NE I0 FUEL.
    { pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (array_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & EL & IJ & AFT & TI').

    astep. step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact EL| exact I0| lia]. }
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E it) < 256) by (unfold ttype; lia).

    astep. astep. step. astep.

    assert (NEXT : forall (pc : Z) (xt3' xt4' : word), (pc = 0x3c898 \/ pc = 0x3c8b0 \/ pc = 0x3c8bc) ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) (Z_to_bv 64 (ae_T E it)) x8 x9
                         (Z_to_bv 64 OUT) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (bv_unsigned xa2 + -1)) (Z_to_bv 64 DOC) (Z_to_bv 64 j') (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295)
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt3' xt4' xt5 xt6)
                    F (Z_to_bv 64 pc) fc None m (seg_rom psegs))).
    { intros pc xt3' xt4' [-> |[-> | ->]]; (step; if_cases KL; zify_cond KL;
        [ eapply (IH j' (c' - 1)); [exact TI'| exact KL| lia| lia]
        | step; apply XNF ]). }

    astep.
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d it j' EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (NEXT 0x3c8bc)]; [atp_st_eq| do 2 right; reflexivity]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (NEXT 0x3c898)]; [atp_st_eq| left; reflexivity]).
    -
      unfold t_str in TY. rewrite TY.
      step. if_true. astep.
      eapply evt_eq; [| eapply (NEXT 0x3c8bc)]; [atp_st_eq| do 2 right; reflexivity].
    -
      unfold t_arr in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. astep.
      rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0x3c8b0)]; [atp_st_eq| right; left; reflexivity].
    -
      unfold t_obj in TY. rewrite TY.
      step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. astep.
      rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0x3c8b0)]; [atp_st_eq| right; left; reflexivity].
  Qed.

  Definition at_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (OUT : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(OUT, OUT + 24)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ (exists (w0 w1 ew : word) od, rw_cells psegs m' OUT [C8 w0; C8 w1; C4 ew; CB 4 od]).

  Ltac fin_at := apply evt_done; unfold at_post; do 15 eexists; eexists;
    split; [cbv delta [mkR]; reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption| do 4 eexists; eassumption].

  Lemma at_spec : forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node OUT idx : Z) (jo : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv psegs m ->
    rw_cells psegs m OUT [CB 24 jo] -> ae_lo E <= OUT -> OUT + 24 <= ae_B E -> (OUT + 24 <= node \/ node + 16 <= OUT) ->
    (OUT + 24 <= ae_DOC E \/ ae_DOC E + 16 <= OUT) -> ae_lo E <= node -> node + 16 <= ae_B E -> 0 <= idx < 2^64 ->
    evt psegs (at_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc OUT m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OUT) (Z_to_bv 64 node) (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_AT) fc None m (seg_rom psegs)).
  Proof.
    intros until jo. intros AI ROOT HEAP MI OUTC O0 O1 ONODE ODOC N0 N1 IDX.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    assert (LO0 : 0 <= ae_lo E) by (unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_AT.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(OUT, OUT + 24)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.

    step. step. step. astep. astep.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.

    astep. astep. astep.
    apply (rw_cells_split_CB psegs _ _ [] 24 jo [] [8;8;4;4]%nat) in OUTC; [|reflexivity]. cbn [mk_CB_cells app] in OUTC.
    zstep. if_cases HK; zify_cond HK.
    -
      astep. hstep. hstep. hstep. step. fin_at.
    -
      destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN TAPE_MAX_DEPTH 1 (ae_n E - 1) EL ltac:(lia) ltac:(lia))
        as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY;
        unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in TY; try lia.
      pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TILES) as TLE.

      astep. astep. astep. rewrite land32_tnext by lia. rewrite NXT. astep.
      replace (e2 + 1 + -1) with e2 by lia.
      zstep. if_cases HK2; zify_cond HK2.
      +
        do 9 astep.
        unshelve (eapply evt_eq; [| eapply (at_iter_loop (at_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc OUT m) m F fc d' e2 q OUT (ae_DOC E)
                                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TAPEB ltac:(lia) MI _ _ (Z.to_nat (e2 - 2) + 1)%nat 2 c2 _ _ _ _ TILES
                                   ltac:(lia) ltac:(lia) ltac:(lia))]); try atp_st_eq.

        all: intros.
        all: first [ hstep; hstep; hstep; step; fin_at | astep; astep; hstep; hstep; hstep; step; fin_at ].
      +
        astep. astep. hstep. hstep. hstep. step. fin_at.
  Qed.
End A28.
End WithCeiling0.

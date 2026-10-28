(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_loop_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length]; lia]
  | |- _ => reflexivity
  end.

Ltac lit_pc :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
       end).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable D : nat.
  Variable f : nat.
  Hypothesis OK : senv_ok E.
  Hypothesis AV : aval_stmt E Q D f.
  Hypothesis OPA : open_stmt E Q D f false.
  Hypothesis OPO : open_stmt E Q D f true.
  Hypothesis PSTR : str_stmt.
  Hypothesis PI64 : i64_stmt.
  Hypothesis PU64 : u64_stmt.
  Hypothesis PDBL : dbl_stmt.
  Hypothesis PTRUE : true_stmt.
  Hypothesis PFALSE : false_stmt.
  Hypothesis PNULL : null_stmt.

  Notation REST := (rest_ok (e_T E) (e_S E) (e_sn E)).
  Notation ESC := (Z_to_bv 64 PJ_ESC_TAB).
  Notation LBS := (Z_to_bv 64 PJ_LIT_BS).
  Notation LQU := (Z_to_bv 64 PJ_LIT_QU).

  Lemma av_K_of : forall (d0 : nat) (ks : list bool) (i2 c2 : Z) (isobj : list byte) (pc bound : Z),
    av_pc_ok pc -> e_j E - i2 <= Z.of_nat f -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    REST d0 ks i2 c2 (e_j E) (e_c' E) -> 2 <= i2 -> 0 <= c2 -> bound <= 41 * (i2 - 1) + 6 * c2 + 2 ->
    av_K E Q ESC LBS LQU isobj pc (i2 - 1) (Z.of_nat (length ks)) bound.
  Proof using AV.
    intros d0 ks i2 c2 isobj pc bound HPC HF0 HD HL KR HR HI HC HB. unfold av_K.
    intros st' s' m' F' fc' spill' xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ACC HS3.
    eapply (AV pc d0 ks i2 c2 isobj st'); try eassumption. lia.
  Qed.

  Lemma disp_proof : disp_stmt E Q D (S f).
  Proof using OK AV OPA OPO PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL.
    unfold disp_stmt.
    intros d0 ks i i2 c c2 isobj st s m F fc spill xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HD HL KR HEL HR HI HC HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ [DD1 DD2] _ [J1 J2] [CC1 CC2] [D8 T8]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof (ser_view_of _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as V.
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    assert (WR : 0 <= e_T E i < 2^64).
    { destruct V as [Hw _ _|Hw _ _|l Hw _ _ _ _|d' e n _ Hw _ _ _ _|d' e n _ Hw _ _ _ _];
        try (destruct Hw as [Hw|[Hw|Hw]]); (eapply ttype_range; [exact Hw|]);
        unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj; lia. }
    set (w := e_T E i) in *. unfold SjTape.ty in V. fold w in V.
    assert (TYR : 0 <= ttype w < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RDT. fold w in RDT.

    gtrap. gtrap. step. step. step.
    eapply tape_ref_call; [exact DOCC| exact T8| lia| lia| lia| lia| reflexivity|].

    step. zstep. rewrite ?unsigned_lit by lia. rewrite shr56_ttype. step. zstep.
    clear RDT DOCC.
    assert (EW : tword (ttype w) (tval w) = w).
    { unfold tword, ttype, tval. pose proof (Z.div_mod w (2^56) ltac:(lia)). lia. }
    set (t := ttype w) in *.
    remember (41 * (i - 1) + 6 * c + 3) as A eqn:EA.

    assert (VT : (t = t_true /\ i2 = i + 1 /\ c2 = c) \/ (t = t_false /\ i2 = i + 1 /\ c2 = c) \/ (t = t_null /\ i2 = i + 1 /\ c2 = c)
              \/ (t = t_i64 /\ i2 = i + 2 /\ c2 = c) \/ (t = t_u64 /\ i2 = i + 2 /\ c2 = c) \/ (t = t_dbl /\ i2 = i + 2 /\ c2 = c)
              \/ (t = t_str /\ i2 = i + 1 /\ exists l, tval w = c /\ str_at (e_S E) (e_sn E) c l /\ c2 = c + l + 5)
              \/ (t = t_arr /\ exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (e_T E e) = t_arr_end
                               /\ tilesS (elemS (e_T E) (e_S E) (e_sn E) ck_any d') (i + 1) e n c c2)
              \/ (t = t_obj /\ exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (e_T E e) = t_obj_end
                               /\ tilesS (fieldS (e_T E) (e_S E) (e_sn E) (elemS (e_T E) (e_S E) (e_sn E) ck_any d')) (i + 1) e n c c2)).
    { destruct V as [Hw Ej Ec|Hw Ej Ec|l Hw Hv Ej Hs Ec|d' e n Ed Hw Ej Hn He Ht|d' e n Ed Hw Ej Hn He Ht].
      - destruct Hw as [Hw|[Hw|Hw]]; tauto.
      - destruct Hw as [Hw|[Hw|Hw]]; tauto.
      - do 6 right. left. split; [exact Hw|]. split; [exact Ej|]. exists l. auto.
      - do 7 right. left. split; [exact Hw|]. exists d', e, n. auto.
      - do 8 right. split; [exact Hw|]. exists d', e, n. auto. }
    clear V. unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in VT.
    assert (ES : bv_signed (Z_to_bv 64 t) = t) by (apply SFModel.signed_of_Z; lia).

    assert (KAV : forall pc N, av_pc_ok pc -> A + N <= 41 * (i2 - 1) + 6 * c2 + 2 -> av_K E Q ESC LBS LQU isobj pc (i2 - 1) (Z.of_nat (length ks)) (A + N)).
    { intros pc N HPC HB. eapply (av_K_of d0 ks i2 c2 isobj pc (A + N)); try eassumption; lia. }
    ser_close HSMC OK.

    step. if_cases K0; zify_cond K0; rewrite ?ES in K0.
    2:{
        zstep. step. step. if_cases K1; zify_cond K1.
        -
          rewrite ?unsigned_lit in K1 by lia.
          assert (VO : t = 123 /\ exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (e_T E e) = t_obj_end
                         /\ tilesS (fieldS (e_T E) (e_S E) (e_sn E) (elemS (e_T E) (e_S E) (e_sn E) ck_any d')) (i + 1) e n c c2)
            by (destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; split; [lia| exact H2]).
          destruct VO as (Et & d' & e & n & Ed & Ej & Hn & He & Ht). subst d0 i2.
          ser_open HSMC OK. step. step. step. ser_close HSMD OK.
          if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].
          eapply evt_eq; [| eapply (OPO d' ks i e n c c2 isobj (mkSb buf size cap blk fuel) s _ F fc spill)];
            [pj_st_eq| lia| exact HD| exact HL| exact KR| unfold SjTape.ty; fold w; fold t; unfold t_obj; lia| exact Hn| exact He| exact Ht| exact HR| lia| lia
            | exact HSMD| exact FRM| cbn [sb_size]; lia].
        -
          rewrite ?unsigned_lit in K1 by lia.
          assert (VJ : (t = 108 /\ i2 = i + 2 /\ c2 = c) \/ (t = 110 /\ i2 = i + 1 /\ c2 = c) \/ (t = 116 /\ i2 = i + 1 /\ c2 = c) \/ (t = 117 /\ i2 = i + 2 /\ c2 = c)).
          { destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; destruct H2 as (d' & e & n & H2); lia. }
          clear VT. clearbody t.
          destruct VJ as [(Et & Ei & Ec)|[(Et & Ei & Ec)|[(Et & Ei & Ec)|(Et & Ei & Ec)]]]; subst t i2 c2.
          all: ser_open HSMC OK.
          all: zstep; step; zstep; zstep; step; zstep; step; step; lit_pc.
          all: ser_close HSMD OK.
          +
            pose proof (KAV PJ_AV0 20 ltac:(left; reflexivity) ltac:(lia)) as KA. replace (i + 2 - 1) with (i + 1) in KA by lia.
            eapply evt_eq; [| eapply (PI64 E Q ESC LBS LQU spill isobj (mkSb buf size cap blk fuel) s _ F fc i (Z.of_nat (length ks)) A)];
              [pj_st_eq| exact OK| exact HSMD| exact FRM| lia| lia| cbn [sb_size]; lia| lia| exact KA].
          +
            pose proof (KAV PJ_AV0 4 ltac:(left; reflexivity) ltac:(lia)) as KA. replace (i + 1 - 1) with i in KA by lia.
            eapply evt_eq; [| eapply (PNULL E Q ESC LBS LQU spill isobj (mkSb buf size cap blk fuel) s _ F fc i (Z.of_nat (length ks)) A)];
              [pj_st_eq| exact OK| exact HSMD| exact FRM| cbn [sb_size]; lia| lia| exact KA].
          +
            pose proof (KAV PJ_AV0 4 ltac:(left; reflexivity) ltac:(lia)) as KA. replace (i + 1 - 1) with i in KA by lia.
            eapply evt_eq; [| eapply (PTRUE E Q ESC LBS LQU spill isobj (mkSb buf size cap blk fuel) s _ F fc i (Z.of_nat (length ks)) A)];
              [pj_st_eq| exact OK| exact HSMD| exact FRM| cbn [sb_size]; lia| lia| exact KA].
          +
            pose proof (KAV PJ_AV0 20 ltac:(left; reflexivity) ltac:(lia)) as KA. replace (i + 2 - 1) with (i + 1) in KA by lia.
            eapply evt_eq; [| eapply (PU64 E Q ESC LBS LQU spill isobj (mkSb buf size cap blk fuel) s _ F fc i (Z.of_nat (length ks)) A)];
              [pj_st_eq| exact OK| exact HSMD| exact FRM| lia| lia| cbn [sb_size]; lia| lia| exact KA]. }

    step. step. if_cases K1; zify_cond K1; rewrite ?ES in K1.
    -
      step. step. if_cases K2; zify_cond K2.
      +
        rewrite ?unsigned_lit in K2 by lia.
        assert (EI : i2 = i + 2 /\ c2 = c) by (destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; destruct H2 as (d' & e & n & H2); lia).
        pose proof (KAV PJ_AV0 27 ltac:(left; reflexivity) ltac:(lia)) as KA. replace (i2 - 1) with (i + 1) in KA by lia.
        replace (Z_to_bv 64 t) with (Z_to_bv 64 100) by (f_equal; lia).
        eapply evt_eq; [| eapply (PDBL E Q ESC LBS LQU spill isobj (mkSb buf size cap blk fuel) s _ F fc i (Z.of_nat (length ks)) A)];
          [pj_st_eq| exact OK| exact HSMC| exact FRM| lia| lia| cbn [sb_size]; lia| lia| exact KA].
      +
        rewrite ?unsigned_lit in K2 by lia.
        step. step. if_cases K3; zify_cond K3.
        * exfalso. rewrite ?unsigned_lit in K3 by lia.
          destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; destruct H2 as (d' & e & n & H2); lia.
        * rewrite ?unsigned_lit in K3 by lia.
          assert (EI : i2 = i + 1 /\ c2 = c) by (destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; destruct H2 as (d' & e & n & H2); lia).
          pose proof (KAV PJ_AV1 5 ltac:(right; reflexivity) ltac:(lia)) as KA. replace (i2 - 1) with i in KA by lia.
          eapply evt_eq; [| eapply (PFALSE E Q ESC LBS LQU spill isobj (mkSb buf size cap blk fuel) s _ F fc i (Z.of_nat (length ks)) A)];
            [pj_st_eq| exact OK| exact HSMC| exact FRM| cbn [sb_size]; lia| lia| exact KA].
    -
      step. step. if_cases K2; zify_cond K2.
      +
        rewrite ?unsigned_lit in K2 by lia.
        assert (VS : i2 = i + 1 /\ exists l, tval w = c /\ str_at (e_S E) (e_sn E) c l /\ c2 = c + l + 5)
          by (destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; [exact H2| destruct H2 as (d' & e & n & H2); lia ..]).
        destruct VS as (Ej & l & Hv & Hs & Ec). pose proof Hs as (_ & L0 & _).
        pose proof (KAV PJ_AV1 (2 + 6 * l) ltac:(right; reflexivity) ltac:(lia)) as KA. replace (i2 - 1) with i in KA by lia.
        assert (EWS : w = tword t_str c) by (rewrite <- EW; fold t; rewrite Hv; f_equal; unfold t_str; lia).
        replace (Z_to_bv 64 t) with (Z_to_bv 64 34) by (f_equal; lia).
        eapply evt_eq; [| eapply (PSTR E Q spill isobj (mkSb buf size cap blk fuel) s _ F fc i c l (Z.of_nat (length ks)) A)];
          [pj_st_eq| exact OK| exact HSMC| exact FRM| lia| unfold SjTape.ty; fold w; exact EWS| exact Hs| cbn [sb_size]; lia| lia| exact KA].
      +
        rewrite ?unsigned_lit in K2 by lia.
        step. step. if_cases K3; zify_cond K3.
        { exfalso. rewrite ?unsigned_lit in K3 by lia.
          destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; destruct H2 as (d' & e & n & H2); lia. }
        rewrite ?unsigned_lit in K3 by lia.
        assert (VA : t = 91 /\ exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (e_T E e) = t_arr_end
                       /\ tilesS (elemS (e_T E) (e_S E) (e_sn E) ck_any d') (i + 1) e n c c2).
        { destruct VT as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; destruct H as (H1 & H2); try lia; try (destruct H2 as (d' & e & n & H2); lia).
          all: try (destruct H2 as (_ & l & H2); lia). split; [lia| exact H2]. }
        destruct VA as (Et & d' & e & n & Ed & Ej & Hn & He & Ht). subst d0 i2.
        ser_open HSMC OK. step. step. step. ser_close HSMD OK.
        if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|].
        eapply evt_eq; [| eapply (OPA d' ks i e n c c2 isobj (mkSb buf size cap blk fuel) s _ F fc spill)];
          [pj_st_eq| lia| exact HD| exact HL| exact KR| unfold SjTape.ty; fold w; fold t; unfold t_arr; lia| exact Hn| exact He| exact Ht| exact HR| lia| lia
          | exact HSMD| exact FRM| cbn [sb_size]; lia].
  Qed.
End Proofs.
End WithCeiling0.

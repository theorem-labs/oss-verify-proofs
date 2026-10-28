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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require F_printf_core_common.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_cont_kit Pj_ser_objk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_ser_objA_a Pj_ser_objA_b Pj_ser_objA_c Pj_ser_objB_a Pj_ser_objB_b Pj_ser_objB_c Pj_ser_arr.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac gnz := zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1%Z; zstep; if_false.

Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length]; lia]
  | |- _ => reflexivity
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable d : nat.
  Hypothesis SER : ser_stmt d.
  Variable E : senv.
  Hypothesis OK : senv_ok E.
  Notation Q := (cont_Q E).
  Notation e := (e_j E - 1).
  Notation c2 := (e_c' E).
  Notation ELEM := (elemS (e_T E) (e_S E) (e_sn E) ck_any d).
  Notation FIELD := (fieldS (e_T E) (e_S E) (e_sn E) (elemS (e_T E) (e_S E) (e_sn E) ck_any d)).
  Notation ESCW := (Z_to_bv 64 PJ_ESC_TAB).
  Notation NET := (Z_to_bv 64 PJ_NE_TAB).
  Notation NNET := (Z_to_bv 64 NNETZ).
  Notation LITBSW := (Z_to_bv 64 LITBSZ).
  Notation LITQUW := (Z_to_bv 64 LITQUZ).
  Notation NSP97 := (Z_to_bv 64 (18446744073709551726 - e_q E)).
  Notation DOCW := (Z_to_bv 64 (e_DOC E)).

  Lemma fieldS_lt : forall a b u v, FIELD a b u v -> a < b.
  Proof. intros a b u v (c1 & _ & H). pose proof (elemS_lt _ _ _ _ _ _ _ _ _ H). lia. Qed.
  Lemma fieldS_cur : forall a b u v, FIELD a b u v -> u <= v /\ (u <= e_sn E -> v <= e_sn E).
  Proof.
    intros a b u v (c1 & (l & _ & Hs & Hc) & H). pose proof Hs as (H0 & Hl & Hb & _).
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ H). lia.
  Qed.

  Lemma obj_close_byte : forall (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 : word) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88) st s m -> frm0 fc -> sb_size st + 1 <= 41 * (e_j E - 1) + 6 * e_c' E + 2 -> sb_size st + 1 <= sb_cap st ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3ffa8 xra xt0 xt1 xt2 (Z_to_bv 64 (sb_size st)) (Z_to_bv 64 (sb_size st + 1)) xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using OK.
    intros v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 st s m F fc xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HSM FRM ACC ROOM.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. obj_open HSM OK.

    step. zstep. step. gtrap. gnz. gtrap.

    try (replace (size + buf)%Z with (buf + size)%Z by lia).
    step. step. pj_store_done.
    obj_close HSM2 OK.
    pose proof (SBINV_of_CERM _ _ _ _ _ _ HSM2) as INV.
    pose proof (SBINV_cap_pos _ _ _ _ INV) as CAP64.
    pose proof HSM2 as [HR0 _].
    pose proof HR0 as (HEAP & AUX & PRES & _ & _ & _ & (errv & ERR) & FA & SO & PURE).
    obj_open HSM2 OK.

    do 13 step. step.
    release_frame FRA ST (e_q E + -112).
    pose proof (stk_merge usegs _ _ _ _ ST FRT ltac:(lia)) as ST'. clear ST FRT. rename ST' into ST.
    release_frame FRS ST (e_q E).
    step.
    apply evt_done. unfold sgoal, sb_ch. cbn [ch_fuel ch_cap ch_blk fst snd sb_fuel sb_cap sb_blk].
    apply implM_pj_part_stop; [lia|].
    apply evt_done. unfold cont_Q, ser_post.
    do 15 eexists. exists F, fc. eexists. exists errv, (mkSb buf (size + 1) cap blk fuel).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact FRM|].
    split; [exact FA|]. split; [exact SO|]. split; [reflexivity|]. split; [exact HEAP|]. split; [exact INV|].
    split; [unfold sb_acc; cbn [sb_size]; lia| exact PRES].
  Qed.

  Lemma obj_end : forall (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 : word) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88) st s m -> frm0 fc -> sb_size st + 1 <= 41 * (e_j E - 1) + 6 * e_c' E + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3ff84 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HSM FRM ACC.
    pose proof (senv_out E OK) as OUTB.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. obj_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK.
      eapply (obj_close_byte _ _ _ _ _ _ _ _ _ _ _ _ (mkSb buf size cap blk fuel)); [exact HSM2| exact FRM| cbn [sb_size]; lia| cbn [sb_size sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := obj_frame E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3ffa0);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      obj_open HSM4 OK.

      step. zstep.
      obj_close HSM5 OK.
      eapply (obj_close_byte _ _ _ _ _ _ _ _ _ _ _ _ (sb_grown (mkSb buf size cap blk fuel) b' NEW (2 * cap)));
        [exact HSM5| exact FRM| unfold sb_grown; cbn [sb_size]; lia| unfold sb_grown; cbn [sb_size sb_cap]; lia].
  Qed.

  Hypothesis STK : e_lo E <= e_q E - cont_need d.
  Variable v0 : word.

  Definition obj_loop_stmt (f : nat) : Prop :=
    forall (x cx n : Z) (xv48 xv72 : word) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs6 xs10 xt3 xt4 xt5 xt6 : word),
      e - x <= Z.of_nat f -> x < e -> tilesS FIELD x e n cx c2 -> 2 <= x -> 0 <= cx ->
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) xv48 (Z_to_bv 64 M56) NSP97 xv72 ESCW LITQUW) st s m -> frm0 fc -> sb_acc st x cx ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3f970 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) xs6 (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).

  Lemma obj_done : forall (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (cx n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    tilesS FIELD e e n cx c2 -> 2 <= e -> (OBM E w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88) st s m -> frm0 fc -> sb_acc st e cx ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3ff84 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 cx n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HT HE HSM FRM ACC.
    pose proof (tilesS_diag _ fieldS_lt _ _ _ _ HT) as EC.
    unfold sb_acc in ACC.
    eapply obj_end; [exact HSM| exact FRM| lia].
  Qed.

  Lemma obj_after_loop : forall (f : nat), obj_loop_stmt f ->
    forall (x x' c1 cx' n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs10 xt3 xt4 xt5 xt6 : word),
      e - x' <= Z.of_nat f -> ELEM (x + 1) x' c1 cx' ->
      x' <= e -> tilesS FIELD x' e n cx' c2 -> 2 <= x -> 0 <= c1 ->
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> frm0 fc -> sb_acc st x' cx' ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3ff18 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (x + 1)) xs2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) xs6 (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros f KL x x' c1 cx' n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs10 xt3 xt4 xt5 xt6 HF0 HEL HXE HT HX HC1 HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof (elemS_word _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as WR.
    pose proof (elemS_after _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as CL. unfold ae_next in CL.
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    assert (NEXT : x' <> e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3f970 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 (x')) ys6 (Z_to_bv 64 34) NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m)).
    { intros NE yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6.
      eapply (KL x' cx' n (Z_to_bv 64 (x + 1)) (Z_to_bv 64 x) st s m F fc); try eassumption; lia. }
    assert (DONE : x' = e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3ff84 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 F fc m)).
    { intros EE yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6. subst x'.
      eapply (obj_done _ _ _ _ _ _ _ _ _ _ _ _ cx' n st s m F fc); try eassumption; lia. }
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. obj_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read7_mu E _ _ _ _ (x + 1) OK HREF MU WM ltac:(lia) WR) as RD7.
    pose proof (tape_read_mu E _ _ _ _ (x + 1) OK HREF MU WM ltac:(lia)) as RDT.
    set (w := e_T E (x + 1)) in *.
    set (t := ttype w) in *.
    assert (TR : 0 <= t < 256) by (subst t; unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    zstep. pjnorm. zstep. step. step.
    if_cases K; zify_cond K.
    -
      assert (K' : 32 < ae_u t) by exact K.
      assert (EX : x' = x + 2) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).
      zstep. step. step. rewrite <- EX.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| apply DONE; lia].
    - assert (K' : ae_u t <= 32) by exact K.

      step. zstep. zstep. step.
      if_cases K2; zify_cond K2.
      + assert (K2' : ae_num t = 0) by exact K2.

        step. zstep. zstep. step.
        if_cases K3; zify_cond K3.
        * assert (K3' : ae_cont t = 0) by exact K3.
          assert (EX : x' = x + 2) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

          zstep. step. step. rewrite <- EX.
          if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| apply DONE; lia].
        * assert (K3' : ae_cont t <> 0) by exact K3.
          assert (EX : x' = Z.land w 4294967295) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

          step. step. step.
          eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].
          zstep. step. zstep. step. step. step. rewrite <- EX.
          if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| apply DONE; lia].
      + assert (K2' : ae_num t <> 0) by exact K2.
        assert (EX : x' = x + 3) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

        zstep. step. step. step. rewrite <- EX.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| apply DONE; lia].
  Qed.

  Lemma obj_loop : forall f, obj_loop_stmt f.
  Proof using HM HF SER OK STK.
    induction f as [|f IH]; unfold obj_loop_stmt;
      intros x cx n xv48 xv72 st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs6 xs10 xt3 xt4 xt5 xt6 HF0 HXE HT HX HCX HSM FRM ACC; [lia|].
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    destruct (tilesS_next _ fieldS_lt _ _ _ _ _ HT ltac:(lia)) as (x' & cx' & HFLD & HXE' & HT').
    pose proof HFLD as (c1 & (l & HTW & HSTR & EC1) & HEL).
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & CUR2).
    pose proof (tilesS_cur _ (e_sn E) fieldS_cur _ _ _ _ _ HT') as (CUR' & _).
    unfold sb_acc in ACC.
    subst c1.

    assert (FLD : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) xv48 (Z_to_bv 64 M56) NSP97 xv72 ESCW LITQUW) st5 s5 m5 -> sb_size st5 <= 41 * (x - 1) + 6 * cx + 3 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3f9c0 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) ys6 (Z_to_bv 64 34) NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6 HSM5 ACC5.
      eapply (ob_head HM HF d SER E OK STK v0 x cx l x' cx' F fc FRM);
        [lia| lia| exact HTW| exact HSTR| exact HEL| lia| lia| | exact HSM5| lia].
      intros st' s' m' F' fc' zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs6 zs10 zt3 zt4 zt5 zt6 HSM' FRM' ACC'.
      eapply (obj_after_loop f IH x x' (cx + l + 5) cx' (n - 1) st'); try eassumption; lia. }

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) xv48 (Z_to_bv 64 M56) NSP97 xv72 ESCW LITQUW) st5 s5 m5 -> sb_size st5 = sb_size st -> sb_size st + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3f994 yra yt0 yt1 yt2 (Z_to_bv 64 (sb_size st)) (Z_to_bv 64 (sb_size st + 1)) ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) ys6 (Z_to_bv 64 34) NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_env OK. obj_open HSM5 OK.

      step. zstep. step. gtrap. gnz. gtrap. step. step. pj_store_done.
      obj_close HSM6 OK.
      eapply (FLD (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. obj_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply (TAIL (mkSb buf size cap blk fuel)); [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3f98c);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      obj_open HSM4 OK.

      step. zstep.
      obj_close HSM5 OK.
      eapply (TAIL (sb_grown (mkSb buf size cap blk fuel) b' NEW (2 * cap))); [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Variables (v8 v16 : word).

  Lemma obj_after_first : forall (x x' c1 cx' n : Z) (xv64 xv72 : word) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs10 xt3 xt4 xt5 xt6 : word),
    ELEM (x + 1) x' c1 cx' -> x' <= e -> tilesS FIELD x' e n cx' c2 -> 2 <= x -> 0 <= c1 ->
    (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 ESCW LITQUW) st s m -> frm0 fc -> sb_acc st x' cx' ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3f8bc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (x + 1)) xs2 xs3 DOCW xs5 xs6 xs7 NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK.
    intros x x' c1 cx' n xv64 xv72 st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs10 xt3 xt4 xt5 xt6 HEL HXE HT HX HC1 HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof (elemS_word _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as WR.
    pose proof (elemS_after _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as CL. unfold ae_next in CL.
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. obj_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read7_mu E _ _ _ _ (x + 1) OK HREF MU WM ltac:(lia) WR) as RD7.
    pose proof (tape_read4_mu E _ _ _ _ (x + 1) OK HREF MU WM ltac:(lia)) as RD4.
    set (w := e_T E (x + 1)) in *.
    set (t := ttype w) in *.
    assert (TR : 0 <= t < 256) by (subst t; unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

    assert (OUT : forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 ys6 ys7 ys10 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (OST E 0x3f92c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 DOCW (Z_to_bv 64 (x')) ys6 ys7 NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m)).
    { intros yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys3 ys6 ys7 ys10 yt3 yt4 yt5 yt6.

      step. step.
      if_cases KE; zify_cond KE; pjnorm_in KE.
      - obj_close HSM2 OK. subst x'.
        eapply (obj_done _ _ _ _ _ _ _ _ _ _ _ _ cx' n (mkSb buf size cap blk fuel)); [exact HT| lia| exact HSM2| exact FRM| exact ACC].
      -
        step. zstep. step. step. step. step. zstep. hstep. zstep. unot. hstep. zstep. hstep. zstep. zstep. hstep.
        try (lazymatch goal with FRA : rw_cells _ _ _ ?cs |- _ =>
          lazymatch cs with context [C8 (Z_to_bv 64 (18446744073709551615 - ?a))] =>
            replace (18446744073709551615 - a) with (18446744073709551726 - e_q E) in FRA by lia end end).
        obj_close HSM2 OK.
        eapply (obj_loop (Z.to_nat (e - x')) x' cx' n _ _ (mkSb buf size cap blk fuel)); [lia| lia| exact HT| lia| lia| exact HSM2| exact FRM| exact ACC]. }

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    zstep. pjnorm. zstep. step. step.
    if_cases K; zify_cond K.
    - assert (K' : 32 < ae_u t) by exact K.
      assert (EX : x' = x - 1 + 3) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

      step. zstep. rewrite <- EX. apply OUT.
    - assert (K' : ae_u t <= 32) by exact K.

      step. zstep. zstep. zstep. step.
      if_cases K2; zify_cond K2.
      + assert (K2' : ae_num t = 0) by exact K2.

        step. zstep. zstep. zstep. zstep. step.
        if_cases K3; zify_cond K3.
        * assert (K3' : ae_cont t = 0) by exact K3.
          assert (EX : x' = x - 1 + 3) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

          step. zstep. rewrite <- EX. apply OUT.
        * assert (K3' : ae_cont t <> 0) by exact K3.
          assert (EX : x' = Z.land w 4294967295) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).
          rewrite land_low32 in EX.

          step. step. step.
          eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].
          zstep. rewrite (zx32_tnext w WR). step. rewrite <- EX. apply OUT.
      + assert (K2' : ae_num t <> 0) by exact K2.
        assert (EX : x' = x - 1 + 4) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

        step. zstep. step. rewrite <- EX. apply OUT.
  Qed.

  Lemma obj_first : forall (i c n : Z) (v24 v32 v40 v48 v56 v64 v72 v80 v88 : word) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    ty (e_T E) i = t_obj -> tnext (e_T E i) = e + 1 -> tilesS FIELD (i + 1) e n c c2 -> 1 <= i -> 0 <= c ->
    (OBM E v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88) st s m -> frm0 fc -> sb_acc1 st i c -> sb_size st + 1 <= sb_cap st ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3f244 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 DOCW xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 i) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK.
    intros i c n v24 v32 v40 v48 v56 v64 v72 v80 v88 st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HTY HNX HT HI HC HSM FRM ACC ROOM.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ [D1 D2] _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (tilesS_le _ fieldS_lt _ _ _ _ _ HT) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) fieldS_cur _ _ _ _ _ HT) as (LCC & _).
    assert (WR : 0 <= e_T E i < 2^64) by (eapply ttype_range; [exact HTY| unfold t_obj; lia]).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    unfold sb_acc1 in ACC. unfold SjTape.ty, t_obj in HTY.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. obj_open HSM OK.

    step. step. zstep. zstep. step. gtrap. gnz. gtrap.

    step. step. pj_store_done. gtrap. zstep. rewrite (land7_mod8_0 (e_DOC E) AL1). zstep. if_false.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read7_mu E _ _ _ _ i OK HREF MU WM ltac:(lia) WR) as RD7.
    pose proof (tape_read4_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RD4.
    set (w := e_T E i) in *.

    zstep. step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    zstep. pjnorm. rewrite HTY. zstep. step. step. step.
    if_cases K; zify_cond K; [exfalso; cbn in K; lia| clear K].

    step. zstep. zstep. zstep. step.
    if_cases K; zify_cond K; [clear K| exfalso; cbn in K; lia].

    step. zstep. zstep. zstep. zstep. step. step.
    if_cases K; zify_cond K; [exfalso; cbn in K; lia| clear K].

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].
    zstep. rewrite (zx32_tnext w WR). fold w in HNX. rewrite HNX.

    zstep. replace (e + 1 + -1) with e by lia. step. step.
    obj_close HSM2 OK.
    if_cases KE; zify_cond KE; pjnorm_in KE.
    -
      rewrite KE in HT.
      pose proof (tilesS_diag _ fieldS_lt _ _ _ _ HT) as EC.
      eapply (obj_end _ _ _ _ _ _ _ _ _ _ _ _ (mkSb buf (size + 1) cap blk fuel)); [exact HSM2| exact FRM| cbn [sb_size]; lia].
    -
      destruct (tilesS_next _ fieldS_lt _ _ _ _ _ HT ltac:(lia)) as (x' & cx' & HFLD & HXE' & HT').
      pose proof HFLD as (c1 & (l & HTW & HSTR & EC1) & HEL).
      pose proof HSTR as (C0 & L0 & CL & _).
      pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
      pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & CUR2).
      pose proof (tilesS_cur _ (e_sn E) fieldS_cur _ _ _ _ _ HT') as (CUR' & _).
      subst c1.
      eapply evt_eq; [| eapply (oa_head HM HF d SER E OK STK v0 v8 v16 (i + 1) c l x' cx' F fc FRM) with (st := mkSb buf (size + 1) cap blk fuel)];
        [pj_st_eq| lia| lia| exact HTW| exact HSTR| exact HEL| lia| lia| | exact HSM2| cbn [sb_size]; lia].
      intros st' s' m' F' fc' xv64' xv72' zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs5 zs6 zs7 zs10 zt3 zt4 zt5 zt6 HSM' FRM' ACC'.
      eapply evt_eq; [| eapply (obj_after_first (i + 1) x' (c + l + 5) cx' (n - 1) xv64' xv72' st')];
        [pj_st_eq| exact HEL| lia| exact HT'| lia| lia| exact HSM'| exact FRM'| exact ACC'].
  Qed.

End Proofs.

Section Entry.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable d : nat.
  Hypothesis SER : ser_stmt d.
  Variable E : senv.
  Hypothesis OK : senv_ok E.
  Hypothesis STK : e_lo E <= e_q E - cont_need d.
  Notation Q := (cont_Q E).
  Notation e := (e_j E - 1).
  Notation c2 := (e_c' E).
  Notation FIELD := (fieldS (e_T E) (e_S E) (e_sn E) (elemS (e_T E) (e_S E) (e_sn E) ck_any d)).

  Lemma obj_entry : forall (i c n : Z) (st : sbst) (F : bvmap 5 word) (fc : bv 32) (errv : word)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    RHEAP (e_ps0 E) (sbblocks st ++ e_LB0 E) (e_m0 E) -> rauxv_ok (e_m0 E) (e_B E) ->
    stk usegs (e_m0 E) (e_lo E) (e_q E) ->
    rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] -> mem_inv usegs (e_m0 E) -> frm0 fc ->
    SBINV (e_m0 E) (e_SB E) (e_len E) st ->
    DOCREP (e_m0 E) (e_LB0 E) (e_DOC E) (e_TAPE E) (e_SBUF E) (e_len E) (e_tws E) (e_sbs E) ->
    ty (e_T E) i = t_obj -> tnext (e_T E i) = e + 1 -> tilesS FIELD (i + 1) e n c c2 -> 1 <= i -> 0 <= c ->
    sb_acc1 st i c ->
    evt usegs (sgoal E Q (sb_ch st) (e_ps0 E))
        (MS (mkR (e_ra E) (Z_to_bv 64 (e_q E)) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 (e_s0 E) (e_s1 E)
                 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
                 (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
            F (Z_to_bv 64 PJ_APPEND_OBJ) fc None (e_m0 E) (seg_rom usegs)).
  Proof using HM HF SER OK STK.
    intros i c n st F fc errv t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           HEAP AUX ST ERR MI FRM INV DOCR HTY HNX HT HI HC ACC.
    pose proof (senv_out E OK) as OUTB.
    pose proof (tilesS_le _ (fieldS_lt d E) _ _ _ _ _ HT) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (fieldS_cur d E) _ _ _ _ _ HT) as (LCC & _).
    pose proof DOCR as (DOCC & TAPEB & SBUFB & _).
    assert (HREF : SREF E st (e_ps0 E) (e_m0 E)).
    { unfold SREF. split; [exact HEAP|]. split; [exact AUX|]. split; [apply lx_pres_refl|]. split; [exact TAPEB|]. split; [exact SBUFB|].
      split; [exact DOCC|]. split; [exists errv; exact ERR|]. split; [reflexivity|]. split; [reflexivity|].
      eapply sb_pure_of_SBINV; exact INV. }
    pose proof (sb_pure_ranges E st OK ltac:(eapply sb_pure_of_SBINV; exact INV)) as (R0 & R1 & R2 & R3 & _).
    pose proof INV as (SV & SZ & (bs & BUF) & (ji & INL) & _).
    assert (BUFS : stk usegs (e_m0 E) (sb_buf st) (sb_buf st + sb_cap st)).
    { pose proof (stk_of_rw_cells usegs _ _ _ BUF) as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
    assert (INLS : stk usegs (e_m0 E) (e_SB E) (e_SB E + 64)).
    { pose proof (stk_of_rw_cells usegs _ _ _ INL) as S. cbn [cells_size csize Nat.add] in S. exact S. }
    clear BUF INL bs ji.
    pose proof (munch_refl (serW E st) (e_m0 E)) as MU. pose proof (wmono_refl usegs (e_m0 E)) as WM. unfold serW in MU.
    unfold PJ_APPEND_OBJ.
    destruct st as [buf size cap blk fuel]. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in *.
    unfold sb_acc1 in ACC. cbn [sb_size] in ACC.
    ser_env OK.
    remember (e_m0 E) as m0 eqn:EM0.

    step.
    carve_frame 104%nat ST. rename FR into FRS.
    apply (rw_cells_split_CB usegs _ _ [] 104 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FRS; [|reflexivity]. cbn [mk_CB_cells app] in FRS.
    repeat match type of FRS with context [CB 8 ?b] => tryif is_var b then fail else (let j := fresh "js" in set (j := b) in FRS; clearbody j) end.
    clear junk.
    destruct (stk_split usegs _ _ (e_q E + -112) _ ST ltac:(lia)) as [ST' FRT]. clear ST. rename ST' into ST.
    carve_frame 96%nat ST. rename FR into FRA.
    apply (rw_cells_split_CB usegs _ _ [] 96 junk [] [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FRA; [|reflexivity]. cbn [mk_CB_cells app] in FRA.
    apply rw_cells_c8ify in FRA. cbn [map c8c Nat.eqb] in FRA.
    repeat match type of FRA with context [le_bytes_to_word ?b] => let j := fresh "v" in set (j := le_bytes_to_word b) in FRA; clearbody j end.
    clear junk.

    do 13 step. step. step. step. step. zstep. step. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK.
      eapply evt_eq; [| eapply (obj_first HM HF d SER E OK STK _ _ _ i c n _ _ _ _ _ _ _ _ _ (mkSb buf size cap blk fuel) (e_ps0 E) _ F fc)];
        [pj_st_eq| exact HTY| exact HNX| exact HT| exact HI| exact HC| exact HSM2| exact FRM| unfold sb_acc1; cbn [sb_size]; lia| cbn [sb_size sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3f244);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      eapply evt_eq; [| eapply (obj_first HM HF d SER E OK STK _ _ _ i c n _ _ _ _ _ _ _ _ _ (sb_grown (mkSb buf size cap blk fuel) b' NEW (2 * cap)) s' _ F fc)];
        [pj_st_eq| exact HTY| exact HNX| exact HT| exact HI| exact HC| exact HSM4| exact FRM| unfold sb_acc1, sb_grown; cbn [sb_size]; lia| unfold sb_grown; cbn [sb_size sb_cap]; lia].
  Qed.

End Entry.

Theorem obj_proof : rmalloc_stmt -> rfree_stmt -> forall d, ser_stmt d -> cont_stmt true d.
Proof.
  intros HM HF d SER. unfold cont_stmt.
  intros ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 q lo B errv SB len st DOC TAPE SBUF tws sbs i e n c c'
         HEAP AUX QB B63 ST CEIL GLO LO ERR MI FRM QSB SBB QDOC DOCB SEP HLEN INV DOCR AL1 AL2 HTY HNX HTE HT HI HE HC HC' ACC.
  set (E := mkSE LB0 lo B q SB DOC TAPE SBUF len tws sbs (e + 1) c' ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s).
  pose proof (tilesS_le _ (itemS_lt (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) true d) _ _ _ _ _ HT) as (LIE & _).
  pose proof (tilesS_cur _ (Z.of_nat (length sbs)) (itemS_cur (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) true d) _ _ _ _ _ HT) as (LCC & _).
  assert (OK : senv_ok E).
  { pose proof DOCR as (_ & _ & _ & WF & SBS & TSZ & SSZ & OKT & OKS).
    unfold cont_need, ser_need in LO.
    constructor; cbn [E e_LB0 e_lo e_B e_q e_SB e_DOC e_TAPE e_SBUF e_len e_tws e_sbs e_j e_c']; try assumption; try lia. }
  assert (STK : e_lo E <= e_q E - cont_need d) by exact LO.
  replace e with (e + 1 - 1) in HT, HNX by lia.
  unfold implM. apply impl_from_evt.
  change (evt usegs (sgoal E (cont_Q E) (sb_ch st) (e_ps0 E))
            (MS (mkR (e_ra E) (Z_to_bv 64 (e_q E)) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 (e_s0 E) (e_s1 E)
                     (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
                     (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
                F (Z_to_bv 64 PJ_APPEND_OBJ) fc None (e_m0 E) (seg_rom usegs))).
  exact (obj_entry HM HF d SER E OK STK i c n st F fc errv t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HEAP AUX ST ERR MI FRM INV DOCR HTY HNX HT HI HC ACC).
Qed.

Theorem cont_of_ser : rmalloc_stmt -> rfree_stmt -> forall k d, ser_stmt d -> cont_stmt k d.
Proof. intros HM HF [|] d SER; [apply obj_proof| apply arr_proof]; assumption. Qed.

End WithCeiling0.

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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_cont_kit.
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

Definition arr_saved (E : senv) : list cell :=
  [C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E); C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Notation AST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (Z_to_bv 64 (e_q E + -80)) (e_gp E) (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E))
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (e_s9 E) (e_s10 E) (e_s11 E) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition arr_frame (E : senv) (m : mem) : Prop := rw_cells usegs m (e_q E + -80) (arr_saved E).
Notation ARM E := (CERM E (e_q E + -80) (arr_frame E)).

Lemma arr_frame_local : forall E, frame_local E (e_q E + -80) (arr_frame E).
Proof.
  intros E m m' AG H. unfold arr_frame in *. eapply rw_cells_agree; [exact AG| exact H|].
  intros a Ha. unfold arr_saved in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. lia.
Qed.

Ltac arr_open HM OK := cont_open HM OK; match goal with H : arr_frame _ _ |- _ => unfold arr_frame, arr_saved in H end.
Ltac arr_close HM OK := lazymatch type of OK with senv_ok ?E => cont_close (e_q E + -80) (arr_frame E) HM OK end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable d : nat.
  Hypothesis SER : ser_stmt d.
  Variable E : senv.
  Hypothesis OK : senv_ok E.
  Notation Q := (cont_Q E).

  Lemma arr_close_byte : forall (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
    ARM E st s m -> frm0 fc -> sb_size st + 1 <= 41 * (e_j E - 1) + 6 * e_c' E + 2 -> sb_size st + 1 <= sb_cap st ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (AST E 0x3f184 xra xt0 xt1 xt2 (Z_to_bv 64 (sb_size st)) (Z_to_bv 64 (sb_size st + 1)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using OK.
    intros st s m F fc xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 HSM FRM ACC ROOM.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. arr_open HSM OK.

    step. zstep. step. gtrap.

    zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

    try (replace (size + buf)%Z with (buf + size)%Z by lia).
    step. step. pj_store_done.
    arr_close HSM2 OK.
    pose proof (SBINV_of_CERM _ _ _ _ _ _ HSM2) as INV.
    pose proof (SBINV_cap_pos _ _ _ _ INV) as CAP64.
    pose proof HSM2 as [HR0 _].
    pose proof HR0 as (HEAP & AUX & PRES & _ & _ & _ & (errv & ERR) & FA & SO & PURE).
    arr_open HSM2 OK.

    do 10 step. step.
    release_frame HFRP ST (e_q E).
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

  Lemma arr_end : forall (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
    ARM E st s m -> frm0 fc -> sb_size st + 1 <= 41 * (e_j E - 1) + 6 * e_c' E + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (AST E 0x3f160 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 HSM FRM ACC.
    pose proof (senv_out E OK) as OUTB.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. arr_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. arr_close HSM2 OK.
      eapply (arr_close_byte (mkSb buf size cap blk fuel)); [exact HSM2| exact FRM| cbn [sb_size]; lia| cbn [sb_size sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      arr_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -80) (FRP := arr_frame E) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3f17c);
        [exact OK| lia| apply arr_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      arr_open HSM4 OK.

      step. zstep.
      arr_close HSM5 OK.
      eapply (arr_close_byte (sb_grown (mkSb buf size cap blk fuel) b' NEW (2 * cap))); [exact HSM5| exact FRM| unfold sb_grown; cbn [sb_size]; lia| unfold sb_grown; cbn [sb_size sb_cap]; lia].
  Qed.

  Hypothesis STK : e_lo E <= e_q E - cont_need d.
  Notation e := (e_j E - 1).
  Notation c2 := (e_c' E).
  Notation ELEM := (elemS (e_T E) (e_S E) (e_sn E) ck_any d).

  Definition arr_loop_stmt (f : nat) : Prop :=
    forall (x cx n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      e - x <= Z.of_nat f -> x < e -> tilesS ELEM x e n cx c2 -> 2 <= x -> 0 <= cx ->
      ARM E st s m -> frm0 fc -> sb_acc st x cx ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f0a4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 x) (Z_to_bv 64 44) (Z_to_bv 64 e) (Z_to_bv 64 32)
               (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt3 xt4 xt5 xt6 F fc m).

  Lemma arr_done : forall (cx n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
    tilesS ELEM e e n cx c2 -> 2 <= e -> ARM E st s m -> frm0 fc -> sb_acc st e cx ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (AST E 0x3f160 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros cx n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 HT HE HSM FRM ACC.
    pose proof (tilesS_diag _ (elemS_lt (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ HT) as EC.
    unfold sb_acc in ACC.
    eapply arr_end; [exact HSM| exact FRM| lia].
  Qed.

  Lemma arr_setup : forall (f : nat), arr_loop_stmt f ->
    forall (x cx n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
      e - x <= Z.of_nat f -> x < e -> tilesS ELEM x e n cx c2 -> 2 <= x -> 0 <= cx ->
      ARM E st s m -> frm0 fc -> sb_acc st x cx ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f080 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 x) xs3 (Z_to_bv 64 e) xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 F fc m).
  Proof using OK.
    intros f KL x cx n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6
           HF0 HXE HT HX HCX HSM FRM ACC.

    step. step. step. step. step. zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply (KL x cx n st s m F fc)]; [pj_st_eq| eassumption ..].
  Qed.

  Lemma arr_after_loop : forall (f : nat), arr_loop_stmt f ->
    forall (x x' cx cx' n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      e - x' <= Z.of_nat f -> ELEM x x' cx cx' ->
      x' <= e -> tilesS ELEM x' e n cx' c2 -> 2 <= x -> 0 <= cx ->
      ARM E st s m -> frm0 fc -> sb_acc st x' cx' ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f100 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 x) (Z_to_bv 64 44) (Z_to_bv 64 e) (Z_to_bv 64 32)
               (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros f KL x x' cx cx' n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HF0 HEL HXE HT HX HCX HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof (elemS_word _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as WR.
    pose proof (elemS_after _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as CL. unfold ae_next in CL.
    pose proof HSM as [HR0 _].
    pose proof (cont_ranges _ _ _ _ OK HR0) as (TP0 & TP1 & _ & _).

    assert (NEXT : x' <> e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f0a4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 x') (Z_to_bv 64 44) (Z_to_bv 64 e) (Z_to_bv 64 32)
               (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) yt3 yt4 yt5 yt6 F fc m)).
    { intros NE yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6.
      eapply (KL x' cx' n st s m F fc); try eassumption; lia. }
    assert (DONE : x' = e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f160 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 (Z_to_bv 64 44) (Z_to_bv 64 e) (Z_to_bv 64 32)
               (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) yt3 yt4 yt5 yt6 F fc m)).
    { intros EE yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 yt3 yt4 yt5 yt6. subst x'.
      eapply (arr_done cx' n st s m F fc); try eassumption; lia. }
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. arr_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read7_mu E _ _ _ _ x OK HREF MU WM ltac:(lia) WR) as RD7.
    pose proof (tape_read_mu E _ _ _ _ x OK HREF MU WM ltac:(lia)) as RDT.
    set (w := e_T E x) in *.
    set (t := ttype w) in *.
    assert (TR : 0 <= t < 256) by (subst t; unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    zstep. pjnorm. zstep. step.
    if_cases K; zify_cond K.
    -
      assert (K' : 32 < ae_u t) by exact K.
      assert (EX : x' = x + 1) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

      zstep. step. rewrite <- EX.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| apply DONE; lia].
    - assert (K' : ae_u t <= 32) by exact K.

      zstep. zstep. step.
      if_cases K2; zify_cond K2.
      + assert (K2' : ae_num t = 0) by exact K2.

        zstep. zstep. step.
        if_cases K3; zify_cond K3.
        * assert (K3' : ae_cont t = 0) by exact K3.
          assert (EX : x' = x + 1) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

          zstep. step. rewrite <- EX.
          if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| apply DONE; lia].
        * assert (K3' : ae_cont t <> 0) by exact K3.
          assert (EX : x' = Z.land w 4294967295) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

          step. step. step.
          eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].
          zstep. zstep. step. rewrite <- EX.
          if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| step; apply DONE; lia].
      + assert (K2' : ae_num t <> 0) by exact K2.
        assert (EX : x' = x + 2) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

        zstep. step. rewrite <- EX.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| step; apply DONE; lia].
  Qed.

  Lemma arr_after_first : forall (f : nat), arr_loop_stmt f ->
    forall (x x' cx cx' n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
      e - x' <= Z.of_nat f -> ELEM x x' cx cx' ->
      x' <= e -> tilesS ELEM x' e n cx' c2 -> 2 <= x -> 0 <= cx ->
      ARM E st s m -> frm0 fc -> sb_acc st x' cx' ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f00c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (x - 1)) (Z_to_bv 64 x) (Z_to_bv 64 e) xs5 xs6 xs7 xs8
               xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK.
    intros f KL x x' cx cx' n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6
           HF0 HEL HXE HT HX HCX HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof (elemS_word _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as WR.
    pose proof (elemS_after _ _ _ SN _ _ _ _ _ HEL ltac:(lia) ltac:(lia)) as CL. unfold ae_next in CL.
    pose proof HSM as [HR0 _].
    pose proof (cont_ranges _ _ _ _ OK HR0) as (TP0 & TP1 & _ & _).
    assert (NEXT : x' <> e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys5 ys6 ys7 ys8 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f080 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 x') ys3 (Z_to_bv 64 e) ys5 ys6 ys7 ys8 yt3 yt4 yt5 yt6 F fc m)).
    { intros NE yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys5 ys6 ys7 ys8 yt3 yt4 yt5 yt6.
      eapply (arr_setup f KL x' cx' n st s m F fc); try eassumption; lia. }
    assert (DONE : x' = e -> forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 yt3 yt4 yt5 yt6,
      evt usegs (sgoal E Q (sb_ch st) s)
          (AST E 0x3f160 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 yt3 yt4 yt5 yt6 F fc m)).
    { intros EE yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 yt3 yt4 yt5 yt6. subst x'.
      eapply (arr_done cx' n st s m F fc); try eassumption; lia. }
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. arr_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read7_mu E _ _ _ _ x OK HREF MU WM ltac:(lia) WR) as RD7.
    pose proof (tape_read4_mu E _ _ _ _ x OK HREF MU WM ltac:(lia)) as RD4.
    set (w := e_T E x) in *.
    set (t := ttype w) in *.
    assert (TR : 0 <= t < 256) by (subst t; unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    zstep. pjnorm. zstep. step. step.
    if_cases K; zify_cond K.
    - assert (K' : 32 < ae_u t) by exact K.
      assert (EX : x' = x - 1 + 2) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

      zstep. step. rewrite <- EX.
      if_cases KE; zify_cond KE; pjnorm_in KE; [apply DONE; lia| apply NEXT; lia].
    - assert (K' : ae_u t <= 32) by exact K.

      step. zstep. zstep. zstep. step.
      if_cases K2; zify_cond K2.
      + assert (K2' : ae_num t = 0) by exact K2.

        step. zstep. zstep. zstep. zstep. step.
        if_cases K3; zify_cond K3.
        * assert (K3' : ae_cont t = 0) by exact K3.
          assert (EX : x' = x - 1 + 2) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

          zstep. step. rewrite <- EX.
          if_cases KE; zify_cond KE; pjnorm_in KE; [apply DONE; lia| apply NEXT; lia].
        * assert (K3' : ae_cont t <> 0) by exact K3.
          assert (EX : x' = Z.land w 4294967295) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).
          rewrite land_low32 in EX.

          step. step. step.
          eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].
          zstep. rewrite (zx32_tnext w WR). step. rewrite <- EX.
          if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| step; apply DONE; lia].
      + assert (K2' : ae_num t <> 0) by exact K2.
        assert (EX : x' = x - 1 + 3) by (destruct CL as [(C1 & C2)|[(C1 & C2 & C3 & C4)|[(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]]]; lia).

        zstep. step. rewrite <- EX.
        if_cases KE; zify_cond KE; pjnorm_in KE; [apply NEXT; lia| step; apply DONE; lia].
  Qed.

  Lemma arr_loop : forall f, arr_loop_stmt f.
  Proof using HM HF SER OK STK.
    induction f as [|f IH]; unfold arr_loop_stmt;
      intros x cx n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HF0 HXE HT HX HCX HSM FRM ACC; [lia|].
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    destruct (tilesS_next _ (elemS_lt (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT ltac:(lia)) as (x' & cx' & HEL & HXE' & HT').
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof (tilesS_cur _ (e_sn E) (elemS_cur (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT') as (CUR' & _).
    unfold sb_acc in ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      ARM E st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (AST E 0x3f0c8 yra yt0 yt1 yt2 (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 x) (Z_to_bv 64 44) (Z_to_bv 64 e) (Z_to_bv 64 32)
               (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      arr_open HSM5 OK.

      step. zstep. step. gtrap.

      zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. pj_store_done. step. step. step. step.
      arr_close HSM6 OK.
      eapply (cont_call_ser d E Q (e_q E + -80) (arr_frame E) (mkSb buf5 (size + 1) cap5 blk5 fuel5) s5 _ x x' cx cx' 0x3f100);
        [exact SER| exact OK| lia| apply arr_frame_local| exact HSM6| exact FRM| unfold cont_need in STK; lia| exact HEL| lia| lia| lia| lia
        | unfold sb_acc1; cbn [sb_size]; lia| lia| reflexivity|].
      intros st' s' m' F' fc' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM' FRM' ACC'.
      eapply (arr_after_loop f IH x x' cx cx' (n - 1) st'); try eassumption; lia. }
    arr_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. arr_close HSM2 OK. eapply (TAIL (mkSb buf size cap blk fuel)); [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      arr_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -80) (FRP := arr_frame E) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3f0c0);
        [exact OK| lia| apply arr_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      arr_open HSM4 OK.

      step. zstep.
      arr_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma arr_head : forall (i c n : Z) (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
    ty (e_T E) i = t_arr -> tnext (e_T E i) = e + 1 -> tilesS ELEM (i + 1) e n c c2 -> 1 <= i -> 0 <= c ->
    ARM E st s m -> frm0 fc -> sb_acc1 st i c -> sb_size st + 1 <= sb_cap st ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (AST E 0x3ef48 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 xs4 xs5 xs6 xs7 xs8
             xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK.
    intros i c n st s m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6
           HTY HNX HT HI HC HSM FRM ACC ROOM.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ [D1 D2] _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (tilesS_le _ (elemS_lt (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (elemS_cur (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT) as (LCC & _).
    assert (WR : 0 <= e_T E i < 2^64) by (eapply ttype_range; [exact HTY| unfold t_arr; lia]).
    pose proof HSM as [HR0 _].
    pose proof (cont_ranges _ _ _ _ OK HR0) as (TP0 & TP1 & _ & _).
    unfold sb_acc1 in ACC. unfold SjTape.ty, t_arr in HTY.
    destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
    ser_env OK. arr_open HSM OK.

    step. step. zstep. zstep. step. gtrap.

    zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

    step. step. pj_store_done.

    gtrap. zstep. rewrite (land7_mod8_0 (e_DOC E) AL1). zstep. if_false.
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

    zstep. step.
    arr_close HSM2 OK.
    if_cases KE; zify_cond KE; pjnorm_in KE.
    -
      rewrite KE in HT.
      pose proof (tilesS_diag _ (elemS_lt (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ HT) as EC.
      eapply (arr_end (mkSb buf (size + 1) cap blk fuel)); [exact HSM2| exact FRM| cbn [sb_size]; lia].
    -
      destruct (tilesS_next _ (elemS_lt (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT ltac:(lia)) as (x' & cx' & HEL & HXE' & HT').
      pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
      pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
      pose proof (tilesS_cur _ (e_sn E) (elemS_cur (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT') as (CUR' & _).
      step. step. step. step.
      eapply (cont_call_ser d E Q (e_q E + -80) (arr_frame E) (mkSb buf (size + 1) cap blk fuel) s _ (i + 1) x' c cx' 0x3f00c);
        [exact SER| exact OK| lia| apply arr_frame_local| exact HSM2| exact FRM| unfold cont_need in STK; lia| exact HEL| lia| lia| lia| lia
        | unfold sb_acc1; cbn [sb_size]; lia| lia| reflexivity|].
      intros st' s' m' F' fc' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM' FRM' ACC'.
      eapply evt_eq; [| eapply (arr_after_first (Z.to_nat (e - x')) (arr_loop _) (i + 1) x' c cx' (n - 1) st')];
        [pj_st_eq| lia| exact HEL| lia| exact HT'| lia| lia| exact HSM'| exact FRM'| exact ACC'].
  Qed.

  Lemma arr_entry : forall (i c n : Z) (st : sbst) (F : bvmap 5 word) (fc : bv 32) (errv : word)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    RHEAP (e_ps0 E) (sbblocks st ++ e_LB0 E) (e_m0 E) -> rauxv_ok (e_m0 E) (e_B E) ->
    stk usegs (e_m0 E) (e_lo E) (e_q E) ->
    rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] -> mem_inv usegs (e_m0 E) -> frm0 fc ->
    SBINV (e_m0 E) (e_SB E) (e_len E) st ->
    DOCREP (e_m0 E) (e_LB0 E) (e_DOC E) (e_TAPE E) (e_SBUF E) (e_len E) (e_tws E) (e_sbs E) ->
    ty (e_T E) i = t_arr -> tnext (e_T E i) = e + 1 -> tilesS ELEM (i + 1) e n c c2 -> 1 <= i -> 0 <= c ->
    sb_acc1 st i c ->
    evt usegs (sgoal E Q (sb_ch st) (e_ps0 E))
        (MS (mkR (e_ra E) (Z_to_bv 64 (e_q E)) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 (e_s0 E) (e_s1 E)
                 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
                 (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
            F (Z_to_bv 64 PJ_APPEND_ARR) fc None (e_m0 E) (seg_rom usegs)).
  Proof using HM HF SER OK STK.
    intros i c n st F fc errv t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           HEAP AUX ST ERR MI FRM INV DOCR HTY HNX HT HI HC ACC.
    pose proof (senv_out E OK) as OUTB.
    pose proof (tilesS_le _ (elemS_lt (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT) as (LIE & _).
    pose proof (tilesS_cur _ (e_sn E) (elemS_cur (e_T E) (e_S E) (e_sn E) ck_any d) _ _ _ _ _ HT) as (LCC & _).
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
    unfold PJ_APPEND_ARR.
    destruct st as [buf size cap blk fuel]. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in *.
    unfold sb_acc1 in ACC. cbn [sb_size] in ACC.
    ser_env OK.
    remember (e_m0 E) as m0 eqn:EM0.

    step.
    carve_frame 80%nat ST. rename FR into FRS.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FRS; [|reflexivity]. cbn [mk_CB_cells app] in FRS.
    repeat match type of FRS with context [CB 8 ?b] => tryif is_var b then fail else (let j := fresh "js" in set (j := b) in FRS; clearbody j) end.
    clear junk.

    do 10 step. step. step. step. step. zstep. step. step.
    assert (HFRP : arr_frame E _) by exact FRS. clear FRS.
    if_cases K; zify_cond K.
    - pjnorm_in K. arr_close HSM2 OK.
      eapply evt_eq; [| eapply (arr_head i c n (mkSb buf size cap blk fuel) (e_ps0 E) _ F fc)];
        [pj_st_eq| exact HTY| exact HNX| exact HT| exact HI| exact HC| exact HSM2| exact FRM| unfold sb_acc1; cbn [sb_size]; lia| cbn [sb_size sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      arr_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -80) (FRP := arr_frame E) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3ef48);
        [exact OK| lia| apply arr_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      eapply evt_eq; [| eapply (arr_head i c n (sb_grown (mkSb buf size cap blk fuel) b' NEW (2 * cap)) s' _ F fc)];
        [pj_st_eq| exact HTY| exact HNX| exact HT| exact HI| exact HC| exact HSM4| exact FRM| unfold sb_acc1, sb_grown; cbn [sb_size]; lia| unfold sb_grown; cbn [sb_size sb_cap]; lia].
  Qed.

End Proofs.

Theorem arr_proof : rmalloc_stmt -> rfree_stmt -> forall d, ser_stmt d -> cont_stmt false d.
Proof.
  intros HM HF d SER. unfold cont_stmt.
  intros ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 q lo B errv SB len st DOC TAPE SBUF tws sbs i e n c c'
         HEAP AUX QB B63 ST CEIL GLO LO ERR MI FRM QSB SBB QDOC DOCB SEP HLEN INV DOCR AL1 AL2 HTY HNX HTE HT HI HE HC HC' ACC.
  set (E := mkSE LB0 lo B q SB DOC TAPE SBUF len tws sbs (e + 1) c' ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s).
  pose proof (tilesS_le _ (itemS_lt (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) false d) _ _ _ _ _ HT) as (LIE & _).
  pose proof (tilesS_cur _ (Z.of_nat (length sbs)) (itemS_cur (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) false d) _ _ _ _ _ HT) as (LCC & _).
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
                F (Z_to_bv 64 PJ_APPEND_ARR) fc None (e_m0 E) (seg_rom usegs))).
  exact (arr_entry HM HF d SER E OK STK i c n st F fc errv t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HEAP AUX ST ERR MI FRM INV DOCR HTY HNX HT HI HC ACC).
Qed.

End WithCeiling0.

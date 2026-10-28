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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable D : nat.
  Variable f : nat.
  Hypothesis OK : senv_ok E.
  Hypothesis KX : exit_K E Q.
  Hypothesis KH : head_stmt E Q D f.

  Notation REST := (rest_ok (e_T E) (e_S E) (e_sn E)).
  Notation TM := (Z_to_bv 64 PJ_TMASK).
  Notation RB := (Z_to_bv 64 PJ_RBR56).

  Lemma ends_loop : forall (ks : list bool) (d0 : nat) (i2 c2 : Z) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
      (F : bvmap 5 word) (fc : bv 32) (spill : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    ks <> [] -> e_j E - i2 <= Z.of_nat f -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    REST d0 ks i2 c2 (e_j E) (e_c' E) -> 1 <= i2 -> 0 <= c2 ->
    SERMC E spill isobj st s m -> frm0 fc -> sb_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3ed24 i2 (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK KX KH.
    induction ks as [|k ks IH]; intros d0 i2 c2 isobj st s m F fc spill xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
      NE HF0 HD HL15 KR HR HI2 HC2 HSM FRM ACC; [congruence|]. clear NE.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ [DD1 DD2] _ [J1 J2] [CC1 CC2] [D8 T8]].
    pose proof WF as ((N1 & N2) & SN & _).
    pose proof (senv_out E OK) as OUTB.
    pose proof (rest_ok_lt _ _ _ _ _ _ _ _ _ _ HR) as LTJ.
    pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (_ & LEC & _).
    pose proof (rest_ok_word _ _ _ SN _ _ _ _ _ _ _ HR ltac:(lia) ltac:(lia)) as WR.
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    set (w := e_T E i2) in *.
    assert (TYR : 0 <= ttype w < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.

    assert (TAIL : forall (pc : Z) (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      (pc = 0x3ed88 /\ ttype w = t_arr_end) \/ (pc = 0x3edcc /\ ttype w = t_obj_end) ->
      SERMC E spill isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E pc i2 (Z.succ (Z.of_nat (length ks))) TM RB yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros pc st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HPC HSM5 ESZ ROOM.
      assert (HEND : ttype w = t_arr_end \/ ttype w = t_obj_end) by (destruct HPC as [[_ H]|[_ H]]; [left| right]; exact H).
      pose proof (rest_ok_end _ _ _ SN _ _ _ _ _ _ _ HR ltac:(lia) ltac:(lia) HEND) as HR'.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.
      destruct HPC as [[-> _]|[-> _]].

      all: step; step; zstep; zstep; step; gtrap; zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1%Z; gtrap; gtrap.

      1: step; pj_store_done; step.
      2: step; step; pj_store_done.

      all: zstep; zstep; step.
      all: ser_close HSM6 OK.
      all: if_cases K9; zify_cond K9.
      1,3: pjnorm_in K9;
        eapply evt_eq; [| eapply (IH (S d0) (i2 + 1) c2 isobj (mkSb buf5 (size + 1) cap5 blk5 fuel5))];
          [pj_st_eq| destruct ks; [cbn in K9; lia| discriminate]| lia| lia| lia| eapply kinds_rel_pop; exact KR| exact HR'| lia| lia
          | exact HSM6| exact FRM| cbn [sb_size]; lia].
      all: pjnorm_in K9;   step;
        (assert (ks = []) by (destruct ks; [reflexivity| cbn [length] in K9; lia])); subst ks;
        destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR') as [EJ EC];
        (eapply (KX (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| exact FRM| cbn [sb_size]; lia]). }

    assert (CLOSE : forall (yra ya0 ya1 ya2 ya3 ya4 : word),
      (ttype w = t_arr_end \/ ttype w = t_obj_end) ->
      evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (LST E 0x3ed54 i2 (Z.succ (Z.of_nat (length ks))) TM RB yra xt0 xt1 xt2 ya0 ya1 ya2 ya3 ya4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m)).
    { intros yra ya0 ya1 ya2 ya3 ya4 HEND.
      pose proof HSM as HSM0. ser_open HSM OK.
      pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
      pose proof (tape_read_mu E _ _ _ _ i2 OK HREF MU WM ltac:(lia)) as RDT. fold w in RDT.

      step. step. step. eapply tape_ref_call; [exact DOCC| exact T8| lia| lia| lia| lia| reflexivity|].
      step. step. step. zstep. unfold PJ_TMASK. rewrite (land_tmask w) by lia. zstep.
      clear RDT DOCC.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall pc, (pc = 0x3ed7c /\ ttype w = t_arr_end) \/ (pc = 0x3edc0 /\ ttype w = t_obj_end) -> cap < size + 1 ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
            (LST E pc i2 (Z.succ (Z.of_nat (length ks))) TM RB (Z_to_bv 64 0x3ed60) xt0 xt1 xt2 (Z_to_bv 64 (size + 1)) (Z_to_bv 64 cap) (Z_to_bv 64 size)
                 (Z_to_bv 64 (ttype w * 72057594037927936)) (Z_to_bv 64 0) xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc mm)) end.
      { intros pc HPC KC.
        destruct HPC as [[-> HE]|[-> HE]].
        all: zstep; pjnorm; step; step.
        all: ser_close HSM3 OK.
        1: eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3ed88); [exact OK| exact HSM3| | lia| reflexivity|].
        3: eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3edcc); [exact OK| exact HSM3| | lia| reflexivity|].
        1,3: eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3); cbn [sb_cap]; lia.
        all: intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        1: eapply (TAIL 0x3ed88); [left; split; [reflexivity| exact HE]| exact HSM4| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
        1: eapply (TAIL 0x3edcc); [right; split; [reflexivity| exact HE]| exact HSM4| reflexivity| unfold sb_grown; cbn [sb_cap]; lia]. }

      step. if_cases K1; zify_cond K1.
      -
        unfold PJ_RBK56 in K1. pjnorm_in K1.
        assert (HE : ttype w = t_obj_end) by (unfold t_arr_end, t_obj_end in *; lia).
        step. if_cases K2; zify_cond K2.
        + pjnorm_in K2. ser_close HSM2 OK.
          eapply evt_eq; [| eapply (TAIL 0x3edcc)]; [pj_st_eq| right; split; [reflexivity| exact HE]| exact HSM2| reflexivity| cbn [sb_cap]; lia].
        + pjnorm_in K2. eapply evt_eq; [| eapply (GROWN 0x3edc0); [right; split; [reflexivity| exact HE]| lia]]. pj_st_eq.
      -
        unfold PJ_RBK56 in K1. pjnorm_in K1.
        assert (HE : ttype w = t_arr_end) by (unfold t_arr_end, t_obj_end in *; lia).
        step. if_cases K2; zify_cond K2.
        + pjnorm_in K2. ser_close HSM2 OK.
          eapply evt_eq; [| eapply (TAIL 0x3ed88)]; [pj_st_eq| left; split; [reflexivity| exact HE]| exact HSM2| reflexivity| cbn [sb_cap]; lia].
        + pjnorm_in K2. eapply evt_eq; [| eapply (GROWN 0x3ed7c); [left; split; [reflexivity| exact HE]| lia]]. pj_st_eq. }

    pose proof HSM as HSM0.
    ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ i2 OK HREF MU WM ltac:(lia)) as RDT. fold w in RDT.

    step. step. step. eapply tape_ref_call; [exact DOCC| exact T8| lia| lia| lia| lia| reflexivity|].
    step. zstep. unfold PJ_TMASK. rewrite (land_tmask w) by lia. step.
    if_cases K1; zify_cond K1.
    {   unfold PJ_RBK56 in K1. pjnorm_in K1. ser_close HSM1 OK.
      eapply evt_eq; [| eapply CLOSE; left; unfold t_arr_end; lia]. pj_st_eq. }
    unfold PJ_RBK56 in K1. pjnorm_in K1.

    step. step. step. eapply tape_ref_call; [exact DOCC| exact T8| lia| lia| lia| lia| reflexivity|].
    step. zstep. rewrite (land_tmask w) by lia. step.
    clear RDT DOCC.
    if_cases K3; zify_cond K3.
    -
      unfold PJ_RBR56 in K3. pjnorm_in K3.
      assert (NA : SjTape.ty (e_T E) i2 <> t_arr_end) by (unfold SjTape.ty, t_arr_end; fold w; lia).
      assert (NO : SjTape.ty (e_T E) i2 <> t_obj_end) by (unfold SjTape.ty, t_obj_end; fold w; lia).
      destruct (rest_ok_item (e_T E) (e_S E) (e_sn E) SN d0 k ks i2 c2 (e_j E) (e_c' E) HR NA NO)
        as (i3 & c3 & HIT & HR3).
      step. step. ser_close HSM1 OK.
      eapply evt_eq; [| eapply (KH d0 (k :: ks) i2 i3 c2 c3 true isobj (mkSb buf size cap blk fuel))];
        [pj_st_eq| lia| cbn [length]; lia| cbn [length]; lia| exact KR| exact HIT| exact HR3| discriminate| lia| lia
        | exact HSM1| exact FRM| cbn [sb_size]; lia].
    -   unfold PJ_RBR56 in K3. pjnorm_in K3. ser_close HSM1 OK.
      eapply evt_eq; [| eapply CLOSE; right; unfold t_obj_end; lia]. pj_st_eq.
  Qed.

  Lemma aval_proof : aval_stmt E Q D f.
  Proof using HM HF OK KX KH.
    unfold aval_stmt.
    intros pc d0 ks i2 c2 isobj st s m F fc spill xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           HPC HS3 HF0 HD HL15 KR HR HI2 HC2 HSM FRM ACC.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof WF as ((N1 & N2) & SN & _).
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.

    assert (AV1 : evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
        (LST E PJ_AV1 (i2 - 1) (Z.of_nat (length ks)) TM RB xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m)).
    { unfold PJ_AV1. step. if_cases K9; zify_cond K9.
      -
        assert (ks = []) by (destruct ks; [reflexivity| cbn [length] in K9; lia]). subst ks.
        destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR) as [EJ EC].
        eapply (KX (mkSb buf size cap blk fuel)); [exact HSM| exact FRM| cbn [sb_size]; lia].
      - destruct ks as [|k ks']; [cbn [length] in K9; lia|].
        pose proof (rest_ok_lt _ _ _ _ _ _ _ _ _ _ HR) as LTJ0.
        zstep.
        eapply evt_eq; [| eapply (ends_loop (k :: ks') d0 i2 c2 isobj (mkSb buf size cap blk fuel))];
          [pj_st_eq| discriminate| exact HF0| exact HD| exact HL15| exact KR| exact HR| lia| lia| exact HSM| exact FRM| cbn [sb_size]; lia]. }
    destruct HPC as [-> | ->].
    -
      unfold PJ_AV0. ser_open HSM OK. step. eapply evt_eq; [| exact AV1]. pj_st_eq.
    - destruct HS3 as [HS3| ->]; [exfalso; unfold PJ_AV0, PJ_AV1 in HS3; lia|]. exact AV1.
  Qed.

End Proofs.
End WithCeiling0.

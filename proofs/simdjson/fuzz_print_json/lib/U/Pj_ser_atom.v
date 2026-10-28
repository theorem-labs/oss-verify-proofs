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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Sj_num_kit.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma null_proof : null_stmt.
  Proof.
    unfold null_stmt, atom_stmt.
    intros E Q e64 e72 e80 spill isobj st s m F fc i dp A xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 OK HSM FRM ACC BUD HK.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in ACC.
    ser_env OK.

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E e64 e72 e80 spill isobj st5 s5 m5 -> sb_size st5 = size -> size + 4 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E 0x3e614 i dp (Z_to_bv 64 (size + 4)) (Z_to_bv 64 PJ_RBR56) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step. zstep. gtrap.

      zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).
      step. step. pj_store_done. step. step. pj_store_done. step. step. pj_store_done. step. pj_store_done.

      step. gtrap.

      step. step.
      ser_close HSM6 OK.
      eapply (HK (mkSb buf5 (size + 4) cap5 blk5 fuel5) _ _ _ _ spill); [exact HSM6| exact FRM| cbn [sb_size]; lia| left; reflexivity]. }
    ser_open HSM OK.

    step. zstep. zstep. gtrap.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      ser_close HSM2 OK.
      eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - rewrite ?unsigned_lit in K by lia.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 4) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (LST E 0x3e60c i dp (Z_to_bv 64 (size + 4)) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e614); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ _ _ (size + 4) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + 4)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Lemma false_proof : false_stmt.
  Proof.
    unfold false_stmt, atom_stmt.
    intros E Q e64 e72 e80 spill isobj st s m F fc i dp A xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 OK HSM FRM ACC BUD HK.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in ACC.
    ser_env OK.

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E e64 e72 e80 spill isobj st5 s5 m5 -> sb_size st5 = size -> size + 5 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (LST E 0x3e444 i dp (Z_to_bv 64 (size + 5)) (Z_to_bv 64 PJ_RBR56) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      assert (PU5 : sb_pure E (mkSb buf5 size cap5 blk5 fuel5)) by (apply HSM5).
      pose proof (sb_pure_ranges E _ OK PU5) as (_ & _ & _ & _ & RIMG). cbn [sb_buf sb_cap] in RIMG.
      ser_open HSM5 OK.

      step. step. zstep. gtrap.

      zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).
      step. zstep. step. step. step.
      ser_close HSM6 OK.
      eapply (ser_copy E Q e64 e72 e80 spill isobj (mkSb buf5 size cap5 blk5 fuel5) s5) with (Src := 0x10298) (n := 5) (rpc := 0x3e478);
        [exact OK | exact HSM6 | | lia | cbn [sb_size sb_cap]; lia | lia | lia | cbn [sb_buf sb_size]; lia | lia | reflexivity | ].
      { destruct (Sj_num_kit.image_readable_b usegs m5 5 0x10298 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB).
        exists tb. split; [exact TB| rewrite TBL; reflexivity]. }
      intros m7 zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM7.
      ser_open HSM7 OK.

      gtrap. step. gtrap. step. step.

      step. step. step. step.
      ser_close HSM8 OK.
      eapply (HK (mkSb buf5 (size + 5) cap5 blk5 fuel5)); [exact HSM8| exact FRM| cbn [sb_size]; lia| right; reflexivity]. }
    ser_open HSM OK.

    step. zstep. zstep. gtrap.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      ser_close HSM2 OK.
      eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - rewrite ?unsigned_lit in K by lia.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 5) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (LST E 0x3e43c i dp (Z_to_bv 64 (size + 5)) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e444); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ _ _ (size + 5) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + 5)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

End Proofs.
End WithCeiling0.

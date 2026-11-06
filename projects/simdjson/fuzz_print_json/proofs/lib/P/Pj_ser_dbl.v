(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_num_defs Pj_ser_ncalls.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
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
  Hypothesis HTC : tochars_stmt.

  Lemma dbl_proof : dbl_stmt.
  Proof.
    unfold dbl_stmt.
    intros E Q esc spill isobj st s m F fc i dp A xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 OK HSM FRM I1 I2 ACC BUD HK.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in ACC.
    ser_env OK.
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    ser_open HSM OK.

    zstep. zstep. pjnorm. zstep.
    pose proof (tape_read_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia)) as RD.
    step.
    clear RD.

    step. step. step.
    ser_close HSM1 OK.
    eapply (ser_tochars E Q esc spill isobj (mkSb buf size cap blk fuel) s) with (rpc := 0x3e370);
      [exact HTC | exact OK | exact HSM1 | exact FRM | lia | reflexivity | ].
    intros m2 e F2 fc2 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM2 FRM2 HE.
    set (n := e - (e_q E + -164)).
    assert (HN : 1 <= n <= 27) by (unfold n; lia).

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (spill5 : word) (yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      SERM E esc spill5 isobj st5 s5 m5 -> sb_size st5 = size -> size + n <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (LST E 0x3e3a4 (i + 1) dp (Z_to_bv 64 (n + size)) yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 n) (Z_to_bv 64 e) xs8 zt3 zt4 zt5 zt6 F2 fc2 m5)).
    { intros st5 s5 m5 spill5 yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      zstep. step.
      if_cases K; zify_cond K.
      { exfalso. rewrite ?unsigned_lit in K by lia. lia. }

      step. step. zstep. zstep. step. step.
      ser_close HSM6 OK.
      eapply (ser_copy E Q esc spill5 isobj (mkSb buf5 size cap5 blk5 fuel5) s5) with (fpc := MEMMOVE_T2) (Src := e_q E + -164) (n := n) (rpc := 0x3e3c4);
        [right; reflexivity | exact OK | exact HSM6 | | lia | cbn [sb_size sb_cap]; lia | lia | lia | cbn [sb_buf sb_size]; lia | lia | reflexivity | ].
      { eapply (frt_src E esc spill5 isobj _ s5 m5); [exact HSM6 | lia | lia | lia]. }
      intros m7 wt0 wt1 wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM7.
      ser_open HSM7 OK.

      step. step. step.
      ser_close HSM8 OK.
      eapply (HK (mkSb buf5 (n + size) cap5 blk5 fuel5)); [exact HSM8| exact FRM2| cbn [sb_size]; lia| right; reflexivity]. }
    ser_open HSM2 OK.

    step. step. step. zstep. zstep. zstep. step.
    replace (e + - (e_q E + -164)) with n by (unfold n; lia).
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      ser_close HSM3 OK.
      eapply evt_eq; [| eapply (TAIL (mkSb buf size cap blk fuel)); [exact HSM3| reflexivity| cbn [sb_cap]; lia]].
      nst_eq.
    - rewrite ?unsigned_lit in K by lia.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (n + size) ->
        evt psegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (LST E 0x3e39c (i + 1) dp (Z_to_bv 64 (n + size)) (Z_to_bv 64 0x3e370) yt0 yt1 yt2 ya0 (Z_to_bv 64 z) ya2 ya3 ya4 ya5 ya6 ya7
               (Z_to_bv 64 n) (Z_to_bv 64 e) xs8 yt3 yt4 yt5 yt6 F2 fc2 m2)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e3a4); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ (n + size) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b NEW zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (n + size)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

End Proofs.
End WithCeiling0.

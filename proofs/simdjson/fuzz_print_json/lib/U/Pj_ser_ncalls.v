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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_num_defs Pj_itoa.
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

Lemma ser_tochars : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  tochars_stmt ->
  senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (n : Z) (F' : bvmap 5 word) (fc' : bv 32) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E e64 e72 e80 spill isobj st s m' -> frm0 fc' -> 1 <= n <= 27 ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 (e_q E + -144 + n)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F' fc' m')) ->
  evt usegs (sgoal E Q (sb_ch st) s)
      (SST E TC_ENTRY (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_q E + -144)) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros E Q e64 e72 e80 spill isobj st s m rpc F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         HTC OK HSM FRM RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  set (NB := e_q E + -144) in *.
  destruct (stk_CB usegs m _ _ FRT ltac:(unfold NB; lia)) as (junk & NBC). replace (Z.to_nat (e_q E + -104 - NB)) with 40%nat in NBC by (unfold NB; lia).
  eapply evt_cut.
  { eapply (HTC (Z_to_bv 64 rpc) (e_gp E) (Z_to_bv 64 RATP)) with (q := e_q E + -256) (lo := e_lo E) (NB := NB) (junk := junk);
      [exact ST | unfold TC_STACK; lia | unfold GLOBALS_TOP; lia | exact MI | exact FRM | unfold NB; lia | unfold NB; lia | exact NBC]. }
  cbv beta. intros ms' PO. unfold tochars_post in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & F' & fc' & m' & e & nb
                  & -> & MU' & WM' & MI' & ST' & FRM' & HE & NBC').
  rewrite (ret_pc_even rpc RP0 RP2).
  replace e with (e_q E + -144 + (e - NB)) by (unfold NB; lia).
  apply HK; [| exact FRM' | lia].
  unfold TC_STACK in MU'.
  split.
  - eapply (SREF_munch_stack E st s m m' OK HR); [| exact WM'].
    eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside] in Hx |- *. unfold NB. split; [lia|]. split; [lia| exact I].
  - eapply (SCUR_after E e64 e72 e80 spill isobj st m m' _ NB (NB + 40) OK PURE HC MU' WM' MI'); [| unfold NB; lia | lia | unfold NB; lia | | exact ST'].
    + intros a Ha. cbn [outside] in Ha |- *. split; [lia|]. split; [lia| exact I].
    + pose proof (stk_of_rw_cells usegs _ _ _ NBC') as SM. cbn [cells_size csize Nat.add] in SM. change (Z.of_nat 40) with 40 in SM. exact SM.
Qed.

Lemma ser_itoa : forall (entry : Z) (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (v rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  entry = PJ_ITOA_U \/ entry = PJ_ITOA_S ->
  senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> 0 <= v < 2^64 ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (n : Z) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E e64 e72 e80 spill isobj st s m' -> 1 <= n <= 20 ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 (e_q E + -144 + n)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
  evt usegs (sgoal E Q (sb_ch st) s)
      (SST E entry (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_q E + -144)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros entry E Q e64 e72 e80 spill isobj st s m v rpc F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         HE OK HSM HV RP0 RP2 HK.
  assert (IT : itoa_stmt entry) by (destruct HE as [-> | ->]; [exact itoa_u_proof| exact itoa_s_proof]).
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  set (NB := e_q E + -144) in *.
  destruct (stk_split usegs m _ (NB + 20) _ FRT ltac:(unfold NB; lia)) as [OUTS _].
  eapply evt_cut.
  { eapply (IT (Z_to_bv 64 rpc) (e_gp E) (Z_to_bv 64 RATP)) with (q := e_q E + -256) (lo := e_lo E);
      [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact MI | unfold NB; lia | unfold NB; lia | exact OUTS | exact HV]. }
  cbv beta. intros ms' PO. unfold itoa_post in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & n
                  & -> & MU' & WM' & MI' & ST' & OUTS' & HN).
  rewrite (ret_pc_even rpc RP0 RP2).
  replace (NB + n) with (e_q E + -144 + n) by (unfold NB; lia).
  apply HK; [| exact HN].
  split.
  - eapply (SREF_munch_stack E st s m m' OK HR); [| exact WM'].
    eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside] in Hx |- *. unfold NB. split; [lia|]. split; [lia| exact I].
  - eapply (SCUR_after E e64 e72 e80 spill isobj st m m' _ NB (NB + 20) OK PURE HC MU' WM' MI'); [| unfold NB; lia | lia | unfold NB; lia | exact OUTS' | exact ST'].
    intros a Ha. cbn [outside] in Ha |- *. split; [lia|]. split; [lia| exact I].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma num_tail : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
         (st : sbst) (s : PState) (m : mem) (F : bvmap 5 word) (fc : bv 32) (il dp A N n : Z)
         (xs3 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
    1 <= n <= N -> N <= 27 -> sb_size st <= A -> A + N <= PJ_OUTMAX (e_len E) ->
    av_K E Q e64 e72 e80 isobj PJ_AV0 il dp (A + N) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E PJ_NUMTAIL il dp xs3 (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 (Z_to_bv 64 (e_q E + -144 + n)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).
  Proof.
    intros E Q e64 e72 e80 spill isobj st s m F fc il dp A N n xs3 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           OK HSM FRM HN HNN ACC BUD HK.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in ACC.
    ser_env OK. unfold PJ_NUMTAIL.

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      SERM E e64 e72 e80 spill isobj st5 s5 m5 -> sb_size st5 = size -> size + n <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3ec7c yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 il) (Z_to_bv 64 (size + n)) (Z_to_bv 64 (e_q E + -144 + n)) (Z_to_bv 64 dp)
               (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (e_q E + -160)) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 107) zt3 zt4 zt5 zt6 F fc m5)).
    { intros st5 s5 m5 yra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step. zstep. gtrap.

      zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

      zstep. step. step.
      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).
      ser_close HSM6 OK.
      eapply (ser_copyh E Q e64 e72 e80 spill isobj (mkSb buf5 size cap5 blk5 fuel5) s5) with (Src := e_q E + -144) (n := n) (rpc := 0x3eca8);
        [exact OK | exact HSM6 | | lia | cbn [sb_size sb_cap]; lia | lia | lia | cbn [sb_buf sb_size]; lia | lia | lia | reflexivity | ].
      { eapply (frt_src E e64 e72 e80 spill isobj _ s5 m5); [exact HSM6 | lia | lia | lia]. }
      intros m7 wt0 wt1 wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM7.
      ser_open HSM7 OK.

      step. step. step.
      ser_close HSM8 OK.
      eapply (HK (mkSb buf5 (size + n) cap5 blk5 fuel5)); [exact HSM8| exact FRM| cbn [sb_size]; lia| left; reflexivity]. }
    ser_open HSM OK.

    step. step. step. zstep. zstep. zstep. step.
    try (replace (size + - (e_q E + -144) + (e_q E + -144 + n))%Z with (size + n)%Z by lia).
    if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      ser_close HSM3 OK.
      eapply evt_eq; [| eapply (TAIL (mkSb buf size cap blk fuel)); [exact HSM3| reflexivity| cbn [sb_cap]; lia]].
      pj_st_eq.
    - rewrite ?unsigned_lit in K by lia.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + n) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3ec74 xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) (Z_to_bv 64 (e_q E + -144)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 il) (Z_to_bv 64 (size + n))
               (Z_to_bv 64 (e_q E + -144 + n)) (Z_to_bv 64 dp) (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (e_q E + -160)) (Z_to_bv 64 PJ_RBR56)
               (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 107) xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3ec7c); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ _ _ (size + n) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b NEW zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply evt_eq; [| eapply (GROWN (size + n)); lia]. pj_st_eq.
      + pjnorm_in K2.   step. eapply evt_eq; [| eapply (GROWN (2 * cap)); lia]. pj_st_eq.
  Qed.
End Proofs.

End WithCeiling0.

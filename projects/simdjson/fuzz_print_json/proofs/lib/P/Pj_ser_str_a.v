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
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls.
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

  Variable E : senv.
  Variable Q : @chst bptr -> PState -> machine_state -> Prop.
  Variable isobj : list byte.
  Variables (i dp c l A : Z).
  Variable F : bvmap 5 word.
  Variable fc : bv 32.
  Hypothesis FRM : frm0 fc.
  Hypothesis OK : senv_ok E.
  Hypothesis HSTR : str_at (e_S E) (e_sn E) c l.
  Hypothesis BUD : A + (2 + 6 * l) <= PJ_OUTMAX (e_len E).
  Hypothesis HK : av_K E Q (Z_to_bv 64 PJ_ESC_TAB) isobj 0x3e5e0 i dp (A + (2 + 6 * l)).

  Notation ESC := (Z_to_bv 64 PJ_ESC_TAB).
  Notation SPILL := (Z_to_bv 64 c).
  Notation DATA := (e_SBUF E + c + 4).

  Lemma str_close : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs7 xs8 xs10 xt3 xt4 xt5 xt6 : word),
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * l ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e52c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 xs4 (Z_to_bv 64 (sb_size st))
             (Z_to_bv 64 (e_q E + -200)) xs7 xs8 (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs7 xs8 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e54c yra yt0 yt1 yt2 (Z_to_bv 64 (size + 1)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) xs3 xs4 (Z_to_bv 64 size)
               (Z_to_bv 64 (e_q E + -200)) xs7 xs8 (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step. zstep. step. pj_store_done. step. step. step.
      ser_close HSM6 OK.
      eapply (HK (mkSb buf5 (size + 1) cap5 blk5 fuel5) _ _ _ _ SPILL); [exact HSM6| exact FRM| cbn [sb_size]; lia| left; reflexivity]. }
    ser_open HSM OK.

    step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      ser_close HSM3 OK.
      eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3e544); [exact OK| exact HSM3| | lia| reflexivity|].
      { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      ser_open HSM4 OK.

      step. zstep.
      ser_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma str_close0 : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs7 xs8 xs10 xt3 xt4 xt5 xt6 : word),
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * l ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e528 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 xs4 xs5
             (Z_to_bv 64 (e_q E + -200)) xs7 xs8 (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs7 xs8 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK.

    step.
    eapply (str_close (mkSb buf size cap blk fuel)); [exact HSM0| cbn [sb_size]; lia].
  Qed.

  Definition esc_bot_K (t : Z) : Prop :=
    forall (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 : word),
      SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * (t + 1) ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E 0x3e0f8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).

  Lemma esc_bslash : forall (t : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 : word),
    esc_bot_K t -> 0 <= t < l ->
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e0b8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
             (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 KB HT HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 2 <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e0e4 yra yt0 yt1 yt2 (Z_to_bv 64 size) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. step. pj_store_done. step. pj_store_done. step.
      ser_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 2) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
        evt psegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3e0d8 xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e0e0); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ (size + 2) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        ser_open HSM4 OK.

        step.
        ser_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + 2)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Lemma esc_quote : forall (t : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 : word),
    esc_bot_K t -> 0 <= t < l ->
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e078 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
             (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 KB HT HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 2 <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e0a4 yra yt0 yt1 yt2 (Z_to_bv 64 size) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. step. pj_store_done. step. pj_store_done. step. step.
      ser_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 2) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
        evt psegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3e098 xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e0a0); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ (size + 2) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        ser_open HSM4 OK.

        step.
        ser_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + 2)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Lemma esc_plain : forall (t : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 : word),
    esc_bot_K t -> 0 <= t < l ->
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e1bc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
             (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 KB HT HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e1e0 yra yt0 yt1 yt2 (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step. zstep. step. pj_store_done. step.
      ser_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      ser_close HSM3 OK.
      eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3e1d8); [exact OK| exact HSM3| | lia| reflexivity|].
      { eapply (ser_req_ok2 E _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      ser_open HSM4 OK.

      step. zstep.
      ser_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma esc_ctl : forall (t b : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs10 xt3 xt4 xt5 xt6 : word),
    esc_bot_K t -> 0 <= t < l -> 0 <= b <= 31 ->
    SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3e10c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 b) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
             (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros t b st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs10 xt3 xt4 xt5 xt6 KB HT HB HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof (esc_len_range b ltac:(lia)) as LR. rewrite <- esc_len_byte in LR.
    set (n := esc_byte (8 * b)) in *.

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERM E ESC SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + n <= sb_cap st5 ->
      evt psegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e194 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 n) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 (size + n))
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. if_cases KZ; zify_cond KZ; [exfalso; pjnorm_in KZ; lia| clear KZ].

      step. step. zstep. zstep. step. step.
      ser_close HSM6 OK.
      eapply (ser_copy E Q ESC SPILL isobj (mkSb buf5 size cap5 blk5 fuel5) s5 _ 0xc4f08 (e_q E + -176) n 0x3e1b0);
        [left; reflexivity| exact OK| exact HSM6| eapply frt_src; [exact HSM6| lia| lia| lia]| lia| cbn [sb_size sb_cap]; lia| lia| lia
        | cbn [sb_buf sb_size]; lia| lia| reflexivity|].
      intros m7 zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM7.
      ser_open HSM7 OK.

      step. step. step.
      ser_close HSM8 OK.
      eapply (KB (mkSb buf5 (size + n) cap5 blk5 fuel5)); [exact HSM8| cbn [sb_size]; lia]. }
    ser_open HSM OK. unfold PJ_ESC_TAB in *.

    zstep. pjnorm. step. zstep.
    pose proof (esc_read m (8 * b + 0) MI ltac:(lia)) as RD0. pose proof (esc_read m (8 * b + 1) MI ltac:(lia)) as RD1.
    pose proof (esc_read m (8 * b + 2) MI ltac:(lia)) as RD2. pose proof (esc_read m (8 * b + 3) MI ltac:(lia)) as RD3.
    pose proof (esc_read m (8 * b + 4) MI ltac:(lia)) as RD4. pose proof (esc_read m (8 * b + 5) MI ltac:(lia)) as RD5.
    pose proof (esc_read m (8 * b + 6) MI ltac:(lia)) as RD6. pose proof (esc_read m (8 * b + 7) MI ltac:(lia)) as RD7.
    unfold PJ_ESC_TAB in RD0, RD1, RD2, RD3, RD4, RD5, RD6, RD7. rewrite Z.add_0_r in RD0. fold n in RD0.

    step. step. step. step. step. step. step. step. step. step.

    step. step. step. step. step. step. step. step. step.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let j := fresh "jw" in set (j := Z_to_bv 64 (Z.lor x y)); clearbody j end.
    pose proof (esc_byte_range (8 * b)) as NR. fold n in NR.
    pjnorm.

    zstep. step.
    step. pj_store_done. step. pj_store_done. step. pj_store_done.
    step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 ya2 ya3 ya4 ya5 ya6 : word), z = Z.max (2 * cap) (size + n) ->
        evt psegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3e18c xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) ya2 ya3 ya4 ya5 ya6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 n) (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 (size + n))
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc mm)) end.
      { intros z ya0 ya2 ya3 ya4 ya5 ya6 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3e194); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ (size + n) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        eapply TAIL; [exact HSM4| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + n)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Definition esc_head_stmt (f : nat) : Prop :=
    forall (t : Z) (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 : word),
      l - t <= Z.of_nat f -> 0 <= t < l ->
      SERM E ESC SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E 0x3e06c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 (Z_to_bv 64 (DATA + t)) (Z_to_bv 64 92)
               (Z_to_bv 64 (e_q E + -200)) xs7 (Z_to_bv 64 (DATA + l)) (Z_to_bv 64 dp) xs10 (Z_to_bv 64 34) xt3 xt4 xt5 xt6 F fc m).

  Lemma esc_bot : forall f, esc_head_stmt f -> forall t, 0 <= t < l -> l - t <= Z.of_nat (S f) -> esc_bot_K t.
  Proof using HM HF OK HSTR BUD HK FRM.
    intros f IH t HT HF0. unfold esc_bot_K.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    pose proof (ser_ranges _ _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof HSTR as (C0 & L0 & CL & _).

    zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K.
      replace (Z_to_bv 64 (e_SBUF E + c + 4 + t + 1)) with (Z_to_bv 64 (DATA + (t + 1))) by (f_equal; lia).
      eapply IH; [lia| lia| exact HSM| lia].
    - pjnorm_in K.

      step.
      eapply str_close0; [exact HSM| lia].
  Qed.

  Lemma esc_head : forall f, esc_head_stmt f.
  Proof using HM HF OK HSTR BUD HK FRM.
    induction f as [|f IH]; unfold esc_head_stmt;
      intros t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs10 xt3 xt4 xt5 xt6 HF0 HT HSM ACC; [lia|].
    pose proof (esc_bot f IH t HT HF0) as KB.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (S_range E (c + 4 + t) OK) as BR. set (b := e_S E (c + 4 + t)) in *.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + t) OK HREF MU WM ltac:(lia)) as RD. fold b in RD.
    replace (e_SBUF E + (c + 4 + t)) with (DATA + t) in RD by lia.

    zstep. pjnorm. step.
    if_cases K1; zify_cond K1.
    - eapply (esc_bslash t (mkSb buf size cap blk fuel)); [exact KB| lia| exact HSM0| cbn [sb_size]; lia].
    -
      step. if_cases K2; zify_cond K2.
      +
        step. step. if_cases K3; zify_cond K3.
        * eapply (esc_plain t (mkSb buf size cap blk fuel)); [exact KB| lia| exact HSM0| cbn [sb_size]; lia].
        * pjnorm_in K3. eapply (esc_ctl t b (mkSb buf size cap blk fuel)); [exact KB| lia| lia| exact HSM0| cbn [sb_size]; lia].
      + eapply (esc_quote t (mkSb buf size cap blk fuel)); [exact KB| lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

End Proofs.
End WithCeiling0.

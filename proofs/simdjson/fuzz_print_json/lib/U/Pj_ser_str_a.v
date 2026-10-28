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

Lemma land255_uw : forall y, Z.land (bv_unsigned (Z_to_bv 64 y)) 255 = Z.land y 255.
Proof.
  intros y. rewrite Z_to_bv_unsigned. unfold bv_wrap. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia| unfold bv_modulus; apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ 56). reflexivity.
Qed.
Lemma land255_shl : forall y k, 8 <= k -> Z.land (Z.shiftl y k) 255 = 0.
Proof.
  intros y k Hk. rewrite Z.shiftl_mul_pow2 by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  replace (2 ^ k) with (2 ^ (k - 8) * 2 ^ 8) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.
Lemma land255_zxb : forall x, 0 <= x < 256 -> Z.land (bv_unsigned (zxb (Z_to_bv 8 x))) 255 = x.
Proof.
  intros x Hx. unfold zxb.
  assert (E8 : bv_unsigned (Z_to_bv 8 x) = x) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
  rewrite E8, unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma land255_b8 : forall x, 0 <= x < 256 -> Z.land (bv_unsigned (Z_to_bv 8 x)) 255 = x.
Proof.
  intros x Hx. assert (E8 : bv_unsigned (Z_to_bv 8 x) = x) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
  rewrite E8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Ltac land255_simpl :=
  repeat first [rewrite land255_zxb by lia | rewrite land255_b8 by lia | rewrite land255_uw | rewrite Z.land_lor_distr_l | rewrite land255_shl by lia | rewrite Z.lor_0_l | rewrite Z.lor_0_r].

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
  Hypothesis HK : av_K E Q (Z_to_bv 64 PJ_ESC_TAB) (Z_to_bv 64 PJ_LIT_BS) (Z_to_bv 64 PJ_LIT_QU) isobj PJ_AV1 i dp (A + (2 + 6 * l)).

  Notation DATA := (e_SBUF E + c + 4).
  Notation SPILL := (Z_to_bv 64 DATA).

  Lemma str_close : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * l ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3ecb8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (sb_size st)) xs4 (Z_to_bv 64 dp)
             (Z_to_bv 64 PJ_RBK56) xs7 (Z_to_bv 64 PJ_RBR56) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3ecd8 yra yt0 yt1 yt2 (Z_to_bv 64 (size + 1)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 size) xs4 (Z_to_bv 64 dp)
               (Z_to_bv 64 PJ_RBK56) xs7 (Z_to_bv 64 PJ_RBR56) xs9 xs10 xs11 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. step. zstep. step. step. step. step.

      gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap. gtrap. step. step. pj_store_done.

      step.
      ser_close HSM6 OK.
      eapply (HK (mkSb buf5 (size + 1) cap5 blk5 fuel5) _ _ _ _ SPILL); [exact HSM6| exact FRM| cbn [sb_size]; lia| right; reflexivity]. }
    ser_open HSM OK.

    step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      ser_close HSM3 OK.
      eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3ecd0); [exact OK| exact HSM3| | lia| reflexivity|].
      { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      ser_open HSM4 OK.

      step. zstep.
      ser_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma str_close0 : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * l ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3ecb4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) xs3 xs4 (Z_to_bv 64 dp)
             (Z_to_bv 64 PJ_RBK56) xs7 (Z_to_bv 64 PJ_RBR56) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HSM ACC.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK.

    step.
    eapply (str_close (mkSb buf size cap blk fuel)); [exact HSM0| cbn [sb_size]; lia].
  Qed.

  Definition esc_bot_K (k t : Z) : Prop :=
    forall (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 : word),
      SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * (t + 1) ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (SST E 0x3eae0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) xs9 SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m).

  Lemma esc_bslash : forall (k t : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    esc_bot_K k t -> 0 <= k <= t -> t < l ->
    SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3ea70 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
             (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 92) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros k t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 KB HK0 HT HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 2 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3eaa8 yra yt0 yt1 yt2 (Z_to_bv 64 size) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 92) SPILL (Z_to_bv 64 k) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap. step. step. pj_store_done. step. pj_store_done. step. gtrap. step. step.
      ser_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 2) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.

    step. zstep. unfold PJ_LIT_BS. gtrap.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3ea9c xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 92) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3eaa4); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ _ _ (size + 2) OK HSM3); cbn [sb_cap]; lia. }
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

  Lemma esc_quote : forall (k t : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    esc_bot_K k t -> 0 <= k <= t -> t < l ->
    SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3ea0c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
             (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 34) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros k t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 KB HK0 HT HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 2 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3ea44 yra yt0 yt1 yt2 (Z_to_bv 64 size) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 34) SPILL (Z_to_bv 64 k) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap. step. step. pj_store_done. step. step. step. pj_store_done. step. gtrap. step. step.
      ser_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 2) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.

    step. zstep. unfold PJ_LIT_QU. gtrap.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3ea38 xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 (size + 2)) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 34) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m)).
      { intros z ya0 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3ea40); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ _ _ (size + 2) OK HSM3); cbn [sb_cap]; lia. }
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

  Lemma esc_plain : forall (k t b : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    esc_bot_K k t -> 0 <= k <= t -> t < l -> 0 <= b < 256 ->
    SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3ebd8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
             (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 b) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros k t b st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 KB HK0 HT HB HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3ebfc yra yt0 yt1 yt2 (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 b) SPILL (Z_to_bv 64 k) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap. gtrap. step. pj_store_done. step.
      ser_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      ser_close HSM3 OK.
      eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3ebf4); [exact OK| exact HSM3| | lia| reflexivity|].
      { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      ser_open HSM4 OK.

      step. zstep.
      ser_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma esc_ctl : forall (k t b : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    esc_bot_K k t -> 0 <= k <= t -> t < l -> 0 <= b <= 31 ->
    SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E 0x3eb00 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
             (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 b) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD FRM.
    intros k t b st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 KB HK0 HT HB HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof (esc_len_range b ltac:(lia)) as LR. rewrite <- esc_len_byte in LR.
    set (n := esc_byte (8 * b)) in *.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + n <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3ebac yra yt0 yt1 yt2 ya0 ya1 (Z_to_bv 64 size) ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 (size + n)) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 n) SPILL (Z_to_bv 64 k) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap. zstep. zstep. step.
      replace (Z_to_bv 64 (size + buf5)) with (Z_to_bv 64 (buf5 + size)) by (f_equal; lia).
      ser_close HSM6 OK.
      eapply (ser_copyh E Q _ _ _ SPILL isobj (mkSb buf5 size cap5 blk5 fuel5) s5 _ (e_q E + -143) n 0x3ebd4);
        [exact OK| exact HSM6| eapply frt_src; [exact HSM6| lia| lia| lia]| lia| cbn [sb_size sb_cap]; lia| lia| lia
        | cbn [sb_buf sb_size]; lia| lia| lia| reflexivity|].
      intros m7 zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM7.
      ser_open HSM7 OK.

      step. step. step.
      ser_close HSM8 OK.
      eapply (KB (mkSb buf5 (size + n) cap5 blk5 fuel5)); [exact HSM8| cbn [sb_size]; lia]. }
    ser_open HSM OK. unfold PJ_ESC_TAB in *.
    pose proof (esc_read m (8 * b + 0) MI ltac:(lia)) as RD0. pose proof (esc_read m (8 * b + 1) MI ltac:(lia)) as RD1.
    pose proof (esc_read m (8 * b + 2) MI ltac:(lia)) as RD2. pose proof (esc_read m (8 * b + 3) MI ltac:(lia)) as RD3.
    pose proof (esc_read m (8 * b + 4) MI ltac:(lia)) as RD4. pose proof (esc_read m (8 * b + 5) MI ltac:(lia)) as RD5.
    pose proof (esc_read m (8 * b + 6) MI ltac:(lia)) as RD6. pose proof (esc_read m (8 * b + 7) MI ltac:(lia)) as RD7.
    unfold PJ_ESC_TAB in RD0, RD1, RD2, RD3, RD4, RD5, RD6, RD7. rewrite Z.add_0_r in RD0. fold n in RD0.

    zstep. pjnorm. step. zstep. gtrap. step. zstep.

    do 22 step. step.
    lazymatch goal with |- context [Z_to_bv 64 (Z.land ?X 255)] => replace (Z.land X 255) with n by (symmetry; land255_simpl; reflexivity) end.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?X ?Y)] => set (recw := Z_to_bv 64 (Z.lor X Y)); clearbody recw end.
    pose proof (esc_byte_range (8 * b)) as NR. fold n in NR.

    step. pj_store_done. step. gtrap. step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 ya3 ya4 ya5 : word), z = Z.max (2 * cap) (size + n) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (SST E 0x3eba0 xra xt0 xt1 xt2 ya0 (Z_to_bv 64 z) (Z_to_bv 64 size) ya3 ya4 ya5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 (size + n)) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 n) SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc mm)) end.
      { intros z ya0 ya3 ya4 ya5 EZ.

        step. step.
        ser_close HSM3 OK.
        eapply (ser_grow HM HF) with (z := z) (rpc := 0x3eba8); [exact OK| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_ok E _ _ _ _ _ _ _ _ (size + n) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
        ser_open HSM4 OK.

        step.
        ser_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + n)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Definition esc_head_stmt (k : Z) (f : nat) : Prop :=
    forall (t : Z) (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 : word),
      l - t <= Z.of_nat f -> k <= t < l -> 0 <= k ->
      SERMC E SPILL isobj st s m -> sb_size st <= A + 1 + 6 * t ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (SST E 0x3e9ec xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 i) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 (l - (t - k))) (Z_to_bv 64 dp)
               (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (DATA + (t - k))) (Z_to_bv 64 PJ_RBR56) xs9 SPILL (Z_to_bv 64 k) xt3 xt4 xt5 xt6 F fc m).

  Lemma esc_bot : forall k f, esc_head_stmt k f -> forall t, k <= t < l -> 0 <= k -> l - t <= Z.of_nat (S f) -> esc_bot_K k t.
  Proof using HM HF OK HSTR BUD HK FRM.
    intros k f IH t HT HK0 HF0. unfold esc_bot_K.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 HSM ACC.
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof HSTR as (C0 & L0 & CL & _).

    zstep. zstep. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K.
      replace (Z_to_bv 64 (e_SBUF E + c + 4 + (t - k) + 1)) with (Z_to_bv 64 (DATA + (t + 1 - k))) by (f_equal; lia).
      replace (Z_to_bv 64 (l - (t - k) - 1)) with (Z_to_bv 64 (l - (t + 1 - k))) by (f_equal; lia).
      eapply IH; [lia| lia| lia| exact HSM| lia].
    - pjnorm_in K.

      step.
      eapply str_close0; [exact HSM| lia].
  Qed.

  Lemma esc_head : forall k f, esc_head_stmt k f.
  Proof using HM HF OK HSTR BUD HK FRM.
    intros k. induction f as [|f IH]; unfold esc_head_stmt;
      intros t st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 HF0 HT HK0 HSM ACC; [lia|].
    pose proof (esc_bot k f IH t HT HK0 HF0) as KB.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (S_range E (c + 4 + t) OK) as BR. set (b := e_S E (c + 4 + t)) in *.
    pose proof HSM as HSM0. pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM0) as (_ & _ & SB0 & SB1).
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. ser_open HSM OK.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + t) OK HREF MU WM ltac:(lia)) as RD. fold b in RD.
    replace (e_SBUF E + (c + 4 + t)) with (DATA + t) in RD by lia.

    zstep. pjnorm. replace (e_SBUF E + c + 4 + (t - k) + k) with (DATA + t) by lia. replace (k + (e_SBUF E + c + 4 + (t - k))) with (DATA + t) by lia.
    gtrap.
    zstep. pjnorm. replace (e_SBUF E + c + 4 + (t - k) + k) with (DATA + t) by lia.
    zstep. pjnorm. step. step.
    if_cases K1; zify_cond K1.
    - pjnorm_in K1. rewrite K1. eapply (esc_bslash k t (mkSb buf size cap blk fuel)); [exact KB| lia| lia| exact HSM0| cbn [sb_size]; lia].
    -
      step. step. if_cases K2; zify_cond K2.
      +
        gtrap. step. step. if_cases K3; zify_cond K3.
        * pjnorm_in K3. eapply (esc_plain k t b (mkSb buf size cap blk fuel)); [exact KB| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
        * pjnorm_in K3. eapply (esc_ctl k t b (mkSb buf size cap blk fuel)); [exact KB| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
      + pjnorm_in K2. rewrite K2. eapply (esc_quote k t (mkSb buf size cap blk fuel)); [exact KB| lia| lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

End Proofs.
End WithCeiling0.

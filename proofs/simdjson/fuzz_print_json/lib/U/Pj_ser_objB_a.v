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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_cont_kit Pj_ser_objk.
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

Local Ltac gbuf := gtrap; zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1%Z; zstep; if_false.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable d : nat.
  Hypothesis SER : ser_stmt d.
  Variable E : senv.
  Hypothesis OK : senv_ok E.
  Hypothesis STK : e_lo E <= e_q E - cont_need d.
  Notation Q := (cont_Q E).
  Notation e := (e_j E - 1).
  Variable v0 : word.

  Variables (x c l x1 cx : Z).
  Variable F : bvmap 5 word.
  Variable fc : bv 32.
  Hypothesis FRM : frm0 fc.
  Hypothesis HX : 2 <= x /\ x + 1 < x1 <= e.
  Hypothesis HC : 0 <= c.
  Hypothesis HT : e_T E x = tword t_str c.
  Hypothesis HSTR : str_at (e_S E) (e_sn E) c l.
  Hypothesis HEL : elemS (e_T E) (e_S E) (e_sn E) ck_any d (x + 1) x1 (c + l + 5) cx.
  Hypothesis HCX : cx <= e_sn E.
  Notation A := (41 * (x - 1) + 6 * c + 3).
  Hypothesis BUD : A + (3 + 6 * l) <= PJ_OUTMAX (e_len E).
  Notation ESCW := (Z_to_bv 64 PJ_ESC_TAB).
  Notation NET := (Z_to_bv 64 PJ_NE_TAB).
  Notation NNET := (Z_to_bv 64 NNETZ).
  Notation LITBSW := (Z_to_bv 64 LITBSZ).
  Notation LITBS2W := (Z_to_bv 64 LITBS2Z).
  Notation LITQUW := (Z_to_bv 64 LITQUZ).
  Notation LITQU2W := (Z_to_bv 64 LITQU2Z).
  Notation NSP97 := (Z_to_bv 64 (18446744073709551726 - e_q E)).
  Notation DOCW := (Z_to_bv 64 (e_DOC E)).
  Notation SBUFW := (Z_to_bv 64 (e_SBUF E)).
  Notation DATA := (e_SBUF E + c + 4).

  Hypothesis HK : forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs10 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st' s' m' -> frm0 fc' -> sb_acc st' x1 cx ->
    evt usegs (sgoal E Q (sb_ch st') s') (OST E 0x3ff18 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (x + 1)) xs2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) xs6 (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F' fc' m').

  Lemma ob_colon : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs6 xs10 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 2 + 6 * l ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3feb4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) xs6 (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD HK.
    intros st s m  xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs6 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ _ _ [J1 J2] [CC1 CC2] _].
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof HSTR as (C0 & L0 & CL & _).
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3fed8 yra yt0 yt1 yt2 (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 (Z_to_bv 64 92) DOCW (Z_to_bv 64 x) ys6 (Z_to_bv 64 34) NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys1 ys2 ys6 ys10 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. step. step.

      gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. step. pj_store_done.

      step. step. step. step.
      obj_close HSM6 OK.
      eapply (cont_call_ser d E Q (e_q E + -208) (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) (mkSb buf5 (size + 1) cap5 blk5 fuel5) s5 _ (x + 1) x1 (c + l + 5) cx 0x3ff18);
        [exact SER| exact OK| lia| apply obj_frame_local| exact HSM6| exact FRM| unfold cont_need in STK; lia| exact HEL| lia| lia| lia| exact HCX
        | unfold sb_acc1; cbn [sb_size]; lia| lia| reflexivity|].
      intros st' s' m' F' fc' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM' FRM' ACC'.
      eapply HK; [exact HSM'| exact FRM'| exact ACC']. }
    obj_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW)) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3fed0);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      obj_open HSM4 OK.

      step. zstep.
      obj_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma ob_close : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs10 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * l ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3fe64 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sb_size st)) xs2 (Z_to_bv 64 92) xs4 xs5 xs6 (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD HK.
    intros st s m  xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys6 ys10 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3fe84 yra yt0 yt1 yt2 (Z_to_bv 64 (size + 1)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 size) ys2 (Z_to_bv 64 92) ys4 ys5 ys6 (Z_to_bv 64 34) NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys4 ys5 ys6 ys10 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. step. step. step.

      gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. pj_store_done.
      obj_close HSM6 OK.
      eapply (ob_colon (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia].
    }
    obj_open HSM OK.

    step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW)) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3fe7c);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      obj_open HSM4 OK.

      step. zstep.
      obj_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma ob_close0 : forall (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs4 xs5 xs6 xs10 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * l ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3fe60 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 (Z_to_bv 64 92) xs4 xs5 xs6 (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD HK.
    intros st s m  xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs1 xs2 xs4 xs5 xs6 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. obj_open HSM OK.

    step.
    eapply (ob_close (mkSb buf size cap blk fuel)); [exact HSM0| cbn [sb_size]; lia].
  Qed.

  Definition ob_bot_K (k u : Z) : Prop :=
    forall (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * (k + u + 1) ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3fd08 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).

  Lemma ob_bslash : forall (k u : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
    ob_bot_K k u -> 0 <= k -> 0 <= u -> k + u < l ->
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * (k + u) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3fca4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD.
    intros k u st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 KB HK0 HU HKU HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st5 s5 m5 -> sb_size st5 = size -> size + 2 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3fcd8 yra yt0 yt1 yt2 (Z_to_bv 64 size) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET (Z_to_bv 64 (size + 2)) LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.
      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).

      step. pj_store_done. step. pj_store_done.

      step. gtrap. step.
      obj_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 2) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    obj_open HSM OK.

    zstep. gtrap.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word), z = Z.max (2 * cap) (size + 2) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (OST E 0x3fccc yra yt0 yt1 yt2 ya0 (Z_to_bv 64 z) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET (Z_to_bv 64 (size + 2)) LITBSW yt3 yt4 yt5 yt6 F fc mm)) end.
      { intros z yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EZ.

        step. step.
        obj_close HSM3 OK.
        eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW)) (st := mkSb buf size cap blk fuel) (z := z) (rpc := 0x3fcd4);
          [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (cont_req_ok E _ _ _ _ _ (size + 2) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
        obj_open HSM4 OK.

        step.
        obj_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + 2)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Lemma ob_quote : forall (k u : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
    ob_bot_K k u -> 0 <= k -> 0 <= u -> k + u < l ->
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * (k + u) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3fc44 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD.
    intros k u st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 KB HK0 HU HKU HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st5 s5 m5 -> sb_size st5 = size -> size + 2 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3fc7c yra yt0 yt1 yt2 (Z_to_bv 64 size) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET (Z_to_bv 64 (size + 2)) LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.
      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).

      step. pj_store_done. step. pj_store_done. step.

      step. gtrap. step.
      obj_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 2) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    obj_open HSM OK.

    step. zstep. gtrap.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word), z = Z.max (2 * cap) (size + 2) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (OST E 0x3fc70 yra yt0 yt1 yt2 ya0 (Z_to_bv 64 z) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET (Z_to_bv 64 (size + 2)) LITBSW yt3 yt4 yt5 yt6 F fc mm)) end.
      { intros z yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EZ.

        step. step.
        obj_close HSM3 OK.
        eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW)) (st := mkSb buf size cap blk fuel) (z := z) (rpc := 0x3fc78);
          [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (cont_req_ok E _ _ _ _ _ (size + 2) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
        obj_open HSM4 OK.

        step.
        obj_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + 2)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Lemma ob_plain : forall (k u : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
    ob_bot_K k u -> 0 <= k -> 0 <= u -> k + u < l ->
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * (k + u) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3fe10 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD.
    intros k u st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 KB HK0 HU HKU HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys10 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3fe34 yra yt0 yt1 yt2 (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET ys10 LITBSW yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 ys10 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. pj_store_done. step.
      obj_close HSM6 OK.
      eapply (KB (mkSb buf5 (size + 1) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia]. }
    obj_open HSM OK.

    step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW)) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3fe2c);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      obj_open HSM4 OK.

      step. zstep.
      obj_close HSM5 OK.
      eapply TAIL; [exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

  Lemma ob_ctl : forall (k u b : Z) (st : sbst) (s : PState) (m : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    ob_bot_K k u -> 0 <= k -> 0 <= u -> k + u < l -> 0 <= b <= 31 ->
    (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * (k + u) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3fd28 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET (Z_to_bv 64 b) LITBSW xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD.
    intros k u b st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 KB HK0 HU HKU HB HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof (esc_len_range b ltac:(lia)) as LR. rewrite <- esc_len_byte in LR.
    set (n := esc_byte (8 * b)) in *.

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st5 s5 m5 -> sb_size st5 = size -> size + n <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3fdd8 yra yt0 yt1 yt2 ya0 ya1 (Z_to_bv 64 size) ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) LITBSW NET NNET (Z_to_bv 64 n) (Z_to_bv 64 (size + n)) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

      zstep. zstep. step.
      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).
      obj_close HSM6 OK.
      eapply (cont_copyh E Q (e_q E + -208) (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) (mkSb buf5 size cap5 blk5 fuel5) s5 _ (e_q E + -111) n 0x3fe00);
        [exact OK| lia| apply obj_frame_local| exact HSM6
        | eapply (obj_frt_src E); [exact HSM6| lia| lia| lia]
        | lia| cbn [sb_size sb_cap]; lia| lia| lia| cbn [sb_buf sb_size]; lia| lia| lia| reflexivity|].
      intros m7 zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM7.
      obj_open HSM7 OK.

      step. step. step. step.
      obj_close HSM8 OK.
      eapply (KB (mkSb buf5 (size + n) cap5 blk5 fuel5)); [exact HSM8| cbn [sb_size]; lia]. }
    obj_open HSM OK. unfold PJ_ESC_TAB in *.

    zstep. pjnorm. step. zstep. unot. gtrap. step. zstep.
    pose proof (esc_read m (8 * b + 0) MI ltac:(lia)) as RD0. pose proof (esc_read m (8 * b + 1) MI ltac:(lia)) as RD1.
    pose proof (esc_read m (8 * b + 2) MI ltac:(lia)) as RD2. pose proof (esc_read m (8 * b + 3) MI ltac:(lia)) as RD3.
    pose proof (esc_read m (8 * b + 4) MI ltac:(lia)) as RD4. pose proof (esc_read m (8 * b + 5) MI ltac:(lia)) as RD5.
    pose proof (esc_read m (8 * b + 6) MI ltac:(lia)) as RD6. pose proof (esc_read m (8 * b + 7) MI ltac:(lia)) as RD7.
    unfold PJ_ESC_TAB in RD0, RD1, RD2, RD3, RD4, RD5, RD6, RD7. rewrite Z.add_0_r in RD0. fold n in RD0.
    pose proof (esc_byte_range (8 * b)) as NR. fold n in NR.
    pose proof (esc_byte_range (8 * b + 1)) as NR1. pose proof (esc_byte_range (8 * b + 2)) as NR2. pose proof (esc_byte_range (8 * b + 3)) as NR3.
    pose proof (esc_byte_range (8 * b + 4)) as NR4. pose proof (esc_byte_range (8 * b + 5)) as NR5. pose proof (esc_byte_range (8 * b + 6)) as NR6.
    pose proof (esc_byte_range (8 * b + 7)) as NR7.

    zstep. zstep. zstep. zstep. pjnorm. zstep. zstep. zstep. zstep. zstep. zstep. pjnorm. zstep.

    zstep. zstep. pjnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

    zstep.
    lazymatch goal with |- context [Z_to_bv 64 (Z.land ?rr 255)] => replace (Z.land rr 255) with n by (symmetry; low_byte; reflexivity) end.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?uu ?vv)] => let j := fresh "jw" in set (j := Z_to_bv 64 (Z.lor uu vv)); clearbody j end.

    step. pj_store_done. step. gtrap.

    step. step. step. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word), z = Z.max (2 * cap) (size + n) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (OST E 0x3fdcc yra yt0 yt1 yt2 ya0 (Z_to_bv 64 z) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) LITBSW NET NNET (Z_to_bv 64 n) (Z_to_bv 64 (size + n)) yt3 yt4 yt5 yt6 F fc mm)) end.
      { intros z yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EZ.

        step. step.
        obj_close HSM3 OK.
        eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW)) (st := mkSb buf size cap blk fuel) (z := z) (rpc := 0x3fdd4);
          [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (cont_req_ok E _ _ _ _ _ (size + n) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
        obj_open HSM4 OK.

        step.
        obj_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + n)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Definition ob_head_stmt (f : nat) : Prop :=
    forall (k u : Z) (st : sbst) (s : PState) (m : mem)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
      l - (k + u) <= Z.of_nat f -> 0 <= k -> 0 <= u -> k + u < l ->
      (OBM E v0 (Z_to_bv 64 M32M1) (Z_to_bv 64 M32P1) (Z_to_bv 64 M4020) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) NSP97 (Z_to_bv 64 x) ESCW LITQUW) st s m -> sb_size st <= A + 1 + 6 * (k + u) ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3fc2c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 DATA) (Z_to_bv 64 92) (Z_to_bv 64 (l - u)) (Z_to_bv 64 (DATA + u)) (Z_to_bv 64 k) (Z_to_bv 64 34) NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F fc m).

  Lemma ob_bot : forall f, ob_head_stmt f -> forall k u, 0 <= k -> 0 <= u -> k + u < l -> l - (k + u) <= Z.of_nat (S f) -> ob_bot_K k u.
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD HK.
    intros f IH k u HK0 HU HKU HF0. unfold ob_bot_K.
    intros st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 HSM ACC.
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof HSTR as (C0 & L0 & CL & _).

    zstep. zstep. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K.
      eapply evt_eq; [| eapply (IH k (u + 1) st)]; [pj_st_eq| lia| lia| lia| lia| exact HSM| lia].
    - pjnorm_in K.

      step.
      eapply ob_close0; [exact HSM| lia].
  Qed.

  Lemma ob_esc_head : forall f, ob_head_stmt f.
  Proof using HM HF SER OK STK FRM HX HC HSTR HEL HCX BUD HK.
    induction f as [|f IH]; unfold ob_head_stmt;
      intros k u st s m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 HF0 HK0 HU HKU HSM ACC; [lia|].
    pose proof (ob_bot f IH k u HK0 HU HKU HF0) as KB.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof (S_range E (c + 4 + (k + u)) OK) as BR. set (b := e_S E (c + 4 + (k + u))) in *.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. obj_open HSM OK.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + (k + u)) OK HREF MU WM ltac:(lia)) as RD. fold b in RD.
    replace (e_SBUF E + (c + 4 + (k + u))) with (DATA + u + k) in RD by lia.

    zstep. gtrap. zstep. zstep. pjnorm. step.
    if_cases K1; zify_cond K1.
    - eapply (ob_bslash k u (mkSb buf size cap blk fuel)); [exact KB| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
    -
      step.
      if_cases K2; zify_cond K2.
      +
        gtrap. step. step. if_cases K3; zify_cond K3.
        * eapply (ob_plain k u (mkSb buf size cap blk fuel)); [exact KB| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
        * pjnorm_in K3. eapply (ob_ctl k u b (mkSb buf size cap blk fuel)); [exact KB| lia| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
      + eapply (ob_quote k u (mkSb buf size cap blk fuel)); [exact KB| lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

End Proofs.
End WithCeiling0.

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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_cont_kit Pj_ser_objk Pj_ser_objA_a.
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
  Variables (v0 v8 v16 : word).

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

  Hypothesis HK : forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xv64 xv72 : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs10 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 ESCW LITQUW) st' s' m' -> frm0 fc' -> sb_acc st' x1 cx ->
    evt usegs (sgoal E Q (sb_ch st') s') (OST E 0x3f8bc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (x + 1)) xs2 xs3 DOCW xs5 xs6 xs7 NET NNET xs10 LITBSW xt3 xt4 xt5 xt6 F' fc' m').

  Notation oa_close := (Pj_ser_objA_a.oa_close HM HF d SER E OK STK v0 v8 v16 x c l x1 cx F fc FRM HX HC HSTR HEL HCX BUD HK).
  Notation oa_esc_head := (Pj_ser_objA_a.oa_esc_head HM HF d SER E OK STK v0 v8 v16 x c l x1 cx F fc FRM HX HC HSTR HEL HCX BUD HK).

  Lemma oa_copy : forall (k : Z) (st : sbst) (s : PState) (m : mem) (xv64 xv72 xv80 xv88 : word)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    0 <= k <= l ->
    (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st s m -> sb_size st <= A + 1 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3f518 xra xt0 xt1 xt2 (Z_to_bv 64 (18446744073709551615 - DATA)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) xs3 (Z_to_bv 64 (e_SBUF E + c)) xs5 xs6 (Z_to_bv 64 k) NET NNET xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HT HSTR HEL HCX BUD HK.
    intros k st s m xv64 xv72 xv80 xv88 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 HKL HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).

    assert (FIN : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st5 s5 m5 -> sb_size st5 = size -> size + k <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3f574 yra yt0 yt1 yt2 (Z_to_bv 64 (DATA + k)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) (Z_to_bv 64 (size + k)) DOCW ys5 ys6 (Z_to_bv 64 k) NET NNET ys10 ys11 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. zstep. zstep. zstep. zstep. hstep. zstep. hstep. step.
      if_cases K; zify_cond K.
      - pjnorm_in K. obj_close HSM6 OK.
        eapply (oa_close (mkSb buf5 (size + k) cap5 blk5 fuel5)); [exact HSM6| cbn [sb_size]; lia].
      - pjnorm_in K.

        zstep. step. zstep. step. zstep. hstep. zstep. unot. hstep. step. step.
        try (lazymatch goal with FRA : rw_cells _ _ _ ?cs |- _ =>
          lazymatch cs with context [C8 (Z_to_bv 64 (18446744073709551615 - ?a))] =>
            replace (18446744073709551615 - a) with (18446744073709551726 - e_q E) in FRA by lia end end).
        obj_close HSM6 OK.
        eapply evt_eq; [| eapply (oa_esc_head (Z.to_nat (l - k)) k 0 (mkSb buf5 (size + k) cap5 blk5 fuel5))];
          [pj_st_eq| lia| lia| lia| lia| exact HSM6| cbn [sb_size]; lia]. }

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st5 s5 m5 -> sb_size st5 = size -> size + k <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3f54c yra yt0 yt1 yt2 ya0 ya1 (Z_to_bv 64 size) ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) (Z_to_bv 64 (size + k)) DOCW ys5 ys6 (Z_to_bv 64 k) NET NNET ys10 ys11 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      pose proof (cont_sep _ _ _ _ _ _ OK HSM5) as (_ & SEP).
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap sb_buf] in ESZ, ROOM, SEP. subst size5.
      obj_open HSM5 OK.

      step. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

      zstep. step. step.
      try (replace (size + buf5)%Z with (buf5 + size)%Z by lia).
      obj_close HSM6 OK.
      eapply (cont_copyh E Q (e_q E + -208) (obj_frame E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) (mkSb buf5 size cap5 blk5 fuel5) s5 _ DATA k 0x3f574);
        [exact OK| lia| apply obj_frame_local| exact HSM6
        | replace DATA with (e_SBUF E + (c + 4)) by lia; eapply (cont_sbuf_src E _ _ _ _ _ (c + 4) k OK HSM6); lia
        | lia| cbn [sb_size sb_cap]; lia| lia| lia| cbn [sb_buf sb_size]; lia| lia| lia| reflexivity|].
      intros m7 zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM7.
      eapply FIN; [exact HSM7| reflexivity| cbn [sb_cap]; lia]. }
    obj_open HSM OK.

    gtrap. step. step. zstep. step. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply TAIL; [exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GROWN : forall (z : Z) (yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 : word), z = Z.max (2 * cap) (size + k) ->
        evt usegs (sgoal E Q (sb_ch (mkSb buf size cap blk fuel)) s)
          (OST E 0x3f540 yra yt0 yt1 yt2 ya0 (Z_to_bv 64 z) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) (Z_to_bv 64 (size + k)) DOCW ys5 ys6 (Z_to_bv 64 k) NET NNET ys10 ys11 yt3 yt4 yt5 yt6 F fc mm)) end.
      { intros z yra yt0 yt1 yt2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 EZ.

        step. step.
        obj_close HSM3 OK.
        eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88)) (st := mkSb buf size cap blk fuel) (z := z) (rpc := 0x3f548);
          [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
        { rewrite EZ. eapply (cont_req_ok E _ _ _ _ _ (size + k) OK HSM3); cbn [sb_cap]; lia. }
        intros s' m' bq NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
        obj_open HSM4 OK.

        step.
        obj_close HSM5 OK.
        eapply TAIL; [exact HSM5| reflexivity|].
        unfold sb_grown. cbn [sb_cap]. rewrite EZ. lia. }
      if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (GROWN (size + k)). lia.
      + pjnorm_in K2.   step. eapply (GROWN (2 * cap)). lia.
  Qed.

  Definition oa_tail_stmt (f : nat) : Prop :=
    forall (k : Z) (st : sbst) (s : PState) (m : mem) (xv64 xv72 xv80 xv88 : word)
           (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 : word),
      l - k <= Z.of_nat f -> 0 <= k < l ->
      (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st s m -> sb_size st <= A + 1 ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3f4f4 xra xt0 xt1 xt2 (Z_to_bv 64 (18446744073709551615 - DATA)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) xs3 (Z_to_bv 64 (e_SBUF E + c)) xs5 xs6 (Z_to_bv 64 k) NET NNET xs10 xs11 xt3 xt4 xt5 xt6 F fc m).

  Lemma oa_tail_loop : forall f, oa_tail_stmt f.
  Proof using HM HF SER OK STK FRM HX HC HT HSTR HEL HCX BUD HK.
    induction f as [|f IH]; unfold oa_tail_stmt;
      intros k st s m xv64 xv72 xv80 xv88 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 HF0 HKL HSM ACC; [lia|].
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof (S_range E (c + 4 + k) OK) as BR. set (b := e_S E (c + 4 + k)) in *.
    pose proof (ne_val_range b) as VR.
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK. obj_open HSM OK. unfold PJ_NE_TAB in *.
    pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + k) OK HREF MU WM ltac:(lia)) as RD. fold b in RD.
    replace (e_SBUF E + (c + 4 + k)) with (DATA + k) in RD by lia.
    pose proof (ne_read m b MI ltac:(lia)) as RT. unfold PJ_NE_TAB in RT.

    gtrap. zstep. zstep. pjnorm. zstep. zstep. pjnorm. step.
    if_cases K1; zify_cond K1.
    - eapply (oa_copy k (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
    -
      zstep. step. if_cases K2; zify_cond K2.
      + pjnorm_in K2. eapply (IH (k + 1) (mkSb buf size cap blk fuel)); [lia| lia| exact HSM0| cbn [sb_size]; lia].
      + pjnorm_in K2.   step.
        eapply (oa_copy l (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

  Lemma oa_tail : forall (k : Z) (st : sbst) (s : PState) (m : mem) (xv64 xv72 xv80 xv88 : word)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    0 <= k <= l ->
    (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st s m -> sb_size st <= A + 1 ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3f4f0 xra xt0 xt1 xt2 (Z_to_bv 64 (18446744073709551615 - DATA)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) xs3 (Z_to_bv 64 (e_SBUF E + c)) xs5 xs6 (Z_to_bv 64 k) NET NNET xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HT HSTR HEL HCX BUD HK.
    intros k st s m xv64 xv72 xv80 xv88 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 HKL HSM ACC.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).

    step. if_cases K; zify_cond K.
    - pjnorm_in K. eapply oa_copy; [lia| exact HSM| exact ACC].
    - pjnorm_in K. eapply (oa_tail_loop (Z.to_nat (l - k))); [lia| lia| exact HSM| exact ACC].
  Qed.

  Definition oa_scan8_stmt (f : nat) : Prop :=
    forall (r : Z) (st : sbst) (s : PState) (m : mem) (xv64 xv72 xv80 xv88 : word)
           (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word),
      l - 8 * r < Z.of_nat f -> 0 <= r -> 8 * r <= l ->
      (OBM E v0 v8 v16 (Z_to_bv 64 (x - 1)) DOCW (Z_to_bv 64 e) (Z_to_bv 64 (x + 1)) (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st s m -> sb_size st <= A + 1 ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (OST E 0x3f408 xra xt0 xt1 xt2 (Z_to_bv 64 (18446744073709551615 - DATA)) (Z_to_bv 64 (8 * r)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 l) (Z_to_bv 64 DATA) xs3 (Z_to_bv 64 (e_SBUF E + c)) xs5 xs6 xs7 NET NNET xs10 xs11 xt3 xt4 xt5 xt6 F fc m).

  Lemma oa_scan8 : forall f, oa_scan8_stmt f.
  Proof using HM HF SER OK STK FRM HX HC HT HSTR HEL HCX BUD HK.
    induction f as [|f IH]; unfold oa_scan8_stmt;
      intros r st s m xv64 xv72 xv80 xv88 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 HF0 HR0 HRL HSM ACC; [lia|].
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (_ & _ & SB0 & SB1).
    pose proof HSM as HSM0.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.

    step. zstep. step. if_cases K; zify_cond K.
    - pjnorm_in K. eapply (oa_tail (8 * r) (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
    - pjnorm_in K.
      ser_env OK. obj_open HSM OK. unfold PJ_NE_TAB in *.
      pose proof (S_range E (c + 4 + 8 * r + 0) OK) as BR0. set (b0 := e_S E (c + 4 + 8 * r + 0)) in *. pose proof (ne_val_range b0) as VR0.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 0) OK HREF MU WM ltac:(lia)) as RD0. fold b0 in RD0.
      pose proof (ne_read m b0 MI ltac:(lia)) as RT0. unfold PJ_NE_TAB in RT0.
      pose proof (S_range E (c + 4 + 8 * r + 1) OK) as BR1. set (b1 := e_S E (c + 4 + 8 * r + 1)) in *. pose proof (ne_val_range b1) as VR1.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 1) OK HREF MU WM ltac:(lia)) as RD1. fold b1 in RD1.
      pose proof (ne_read m b1 MI ltac:(lia)) as RT1. unfold PJ_NE_TAB in RT1.
      pose proof (S_range E (c + 4 + 8 * r + 2) OK) as BR2. set (b2 := e_S E (c + 4 + 8 * r + 2)) in *. pose proof (ne_val_range b2) as VR2.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 2) OK HREF MU WM ltac:(lia)) as RD2. fold b2 in RD2.
      pose proof (ne_read m b2 MI ltac:(lia)) as RT2. unfold PJ_NE_TAB in RT2.
      pose proof (S_range E (c + 4 + 8 * r + 3) OK) as BR3. set (b3 := e_S E (c + 4 + 8 * r + 3)) in *. pose proof (ne_val_range b3) as VR3.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 3) OK HREF MU WM ltac:(lia)) as RD3. fold b3 in RD3.
      pose proof (ne_read m b3 MI ltac:(lia)) as RT3. unfold PJ_NE_TAB in RT3.
      pose proof (S_range E (c + 4 + 8 * r + 4) OK) as BR4. set (b4 := e_S E (c + 4 + 8 * r + 4)) in *. pose proof (ne_val_range b4) as VR4.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 4) OK HREF MU WM ltac:(lia)) as RD4. fold b4 in RD4.
      pose proof (ne_read m b4 MI ltac:(lia)) as RT4. unfold PJ_NE_TAB in RT4.
      pose proof (S_range E (c + 4 + 8 * r + 5) OK) as BR5. set (b5 := e_S E (c + 4 + 8 * r + 5)) in *. pose proof (ne_val_range b5) as VR5.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 5) OK HREF MU WM ltac:(lia)) as RD5. fold b5 in RD5.
      pose proof (ne_read m b5 MI ltac:(lia)) as RT5. unfold PJ_NE_TAB in RT5.
      pose proof (S_range E (c + 4 + 8 * r + 6) OK) as BR6. set (b6 := e_S E (c + 4 + 8 * r + 6)) in *. pose proof (ne_val_range b6) as VR6.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 6) OK HREF MU WM ltac:(lia)) as RD6. fold b6 in RD6.
      pose proof (ne_read m b6 MI ltac:(lia)) as RT6. unfold PJ_NE_TAB in RT6.
      pose proof (S_range E (c + 4 + 8 * r + 7) OK) as BR7. set (b7 := e_S E (c + 4 + 8 * r + 7)) in *. pose proof (ne_val_range b7) as VR7.
      pose proof (sbuf_read_mu E _ _ _ _ (c + 4 + 8 * r + 7) OK HREF MU WM ltac:(lia)) as RD7. fold b7 in RD7.
      pose proof (ne_read m b7 MI ltac:(lia)) as RT7. unfold PJ_NE_TAB in RT7.

      gtrap. zstep. zstep. pjnorm. gtrap. gtrap.

      zstep. pjnorm. gtrap. zstep. gtrap.

      zstep. pjnorm. gtrap. zstep. gtrap.

      zstep. pjnorm. gtrap. zstep. gtrap.

      zstep. pjnorm. gtrap. zstep. gtrap.

      zstep. pjnorm. gtrap. zstep. gtrap.

      zstep. pjnorm. gtrap. zstep. gtrap.

      zstep. pjnorm. gtrap.

      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. pjnorm.

      step. step. step. step. step. step. step. step.
      if_cases K1; zify_cond K1.
      + replace (Z_to_bv 64 (8 * r + 8)) with (Z_to_bv 64 (8 * (r + 1))) by (f_equal; lia).
        eapply (IH (r + 1) (mkSb buf size cap blk fuel)); [lia| lia| lia| exact HSM0| cbn [sb_size]; lia].
      + eapply (oa_tail (8 * r) (mkSb buf size cap blk fuel)); [lia| exact HSM0| cbn [sb_size]; lia].
  Qed.

End Proofs.
End WithCeiling0.

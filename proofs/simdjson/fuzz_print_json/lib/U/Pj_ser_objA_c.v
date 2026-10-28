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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_cont_kit Pj_ser_objk Pj_ser_objA_a Pj_ser_objA_b.
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

  Notation oa_scan8 := (Pj_ser_objA_b.oa_scan8 HM HF d SER E OK STK v0 v8 v16 x c l x1 cx F fc FRM HX HC HT HSTR HEL HCX BUD HK).

  Lemma oa_head : forall (st : sbst) (s : PState) (m : mem) (xv24 xv32 xv48 xv56 xv64 xv72 xv80 xv88 : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    (OBM E v0 v8 v16 xv24 xv32 (Z_to_bv 64 e) xv48 xv56 xv64 xv72 xv80 xv88) st s m -> sb_size st <= A ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (OST E 0x3f2fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 DOCW xs2 (Z_to_bv 64 x) xs4 xs5 xs6 (Z_to_bv 64 (x - 1)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF SER OK STK FRM HX HC HT HSTR HEL HCX BUD HK.
    intros st s m xv24 xv32 xv48 xv56 xv64 xv72 xv80 xv88 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof OK as [WF _ _ _ _ _ _ _ _ _ _ [D1 D2] _ [J1 J2] [CC1 CC2] [AL1 AL2]].
    pose proof HSTR as (C0 & L0 & CL & LE & _).
    pose proof (cont_rangesC _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & SB0 & SB1).
    pose proof (S_range E c OK) as BR0. pose proof (S_range E (c + 1) OK) as BR1.
    pose proof (S_range E (c + 2) OK) as BR2. pose proof (S_range E (c + 3) OK) as BR3.
    unfold le32 in LE.
    set (b0 := e_S E c) in *. set (b1 := e_S E (c + 1)) in *. set (b2 := e_S E (c + 2)) in *. set (b3 := e_S E (c + 3)) in *.
    pose proof (tword_range t_str c ltac:(unfold t_str; lia) ltac:(lia)) as TR.
    assert (EA : Z.land (Z.land (tword t_str c) 18446744073709551615) 72057594037927935 = c).
    { rewrite pj_land64 by lia. rewrite land_mask56 by lia. apply tval_tword. lia. }
    assert (EA' : Z.land (tword t_str c) 72057594037927935 = c).
    { rewrite land_mask56 by lia. apply tval_tword. lia. }

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya3 ya4 ya5 ya6 ya7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 : word),
      (OBM E v0 v8 v16 xv24 DOCW (Z_to_bv 64 e) xv48 (Z_to_bv 64 M56) xv64 xv72 xv80 xv88) st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (OST E 0x3f3a4 yra yt0 yt1 yt2 ya0 (Z_to_bv 64 size) (Z_to_bv 64 (size + 1)) ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 b0) (Z_to_bv 64 DATA) (Z_to_bv 64 b1) (Z_to_bv 64 (e_SBUF E + c)) (Z_to_bv 64 b2) (Z_to_bv 64 b3) (Z_to_bv 64 (x - 1)) ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya3 ya4 ya5 ya6 ya7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      obj_open HSM5 OK.

      step. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false. gtrap.

      step. step. step. pj_store_done.

      zstep. zstep. zstep. step. zstep. step. zstep. zstep. unot. zstep.

      zstep. zstep. zstep. zstep. unot.
      assert (EL : Z.lor (Z.lor (Z.land (Z.shiftl b3 24) 18446744073709551615) (Z.land (Z.shiftl b2 16) 18446744073709551615))
                         (Z.lor (Z.land (Z.shiftl b1 8) 18446744073709551615) b0) = l).
      { rewrite !pj_land64 by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite lor4_le32 by lia. lia. }
      rewrite !EL.
      replace (x - 1 + 2) with (x + 1) in FRA by lia.
      obj_close HSM6 OK.
      eapply evt_eq; [| eapply (oa_scan8 (S (Z.to_nat l)) 0 (mkSb buf5 (size + 1) cap5 blk5 fuel5) _ _ xv64 xv72 xv80 xv88)];
        [pj_st_eq| lia| lia| lia| exact HSM6| cbn [sb_size]; lia]. }
    obj_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ x OK HREF MU WM ltac:(lia)) as RDT. rewrite HT in RDT.

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    step. gtrap. step. step. zstep. hstep. zstep. rewrite ?EA, ?EA'. zstep. zstep. gtrap. gtrap.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC2.
    pose proof (tape_read_mu E _ _ _ _ x OK HREF MU WM ltac:(lia)) as RDT2. rewrite HT in RDT2.

    step. step. step.
    eapply tape_ref_call; [exact DOCC2| exact AL2| lia| lia| lia| lia| reflexivity|].

    step. step. step. zstep. rewrite ?EA, ?EA'. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

    step. gtrap.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (sbuf_read_mu E _ _ _ _ (c + 0) OK HREF MU WM ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0; fold b0 in RD0;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 1) OK HREF MU WM ltac:(lia)) as RD1; fold b1 in RD1;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 2) OK HREF MU WM ltac:(lia)) as RD2; fold b2 in RD2;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 3) OK HREF MU WM ltac:(lia)) as RD3; fold b3 in RD3 end.

    step. step. zstep. zstep. zstep. zstep. pjnorm. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. obj_close HSM2 OK. eapply evt_eq; [| eapply TAIL]; [pj_st_eq| exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      obj_close HSM3 OK.
      eapply (cont_grow HM HF) with (fb := e_q E + -208) (FRP := (obj_frame E v0 v8 v16 xv24 DOCW (Z_to_bv 64 e) xv48 (Z_to_bv 64 M56) xv64 xv72 xv80 xv88)) (st := mkSb buf size cap blk fuel) (z := 2 * cap) (rpc := 0x3f39c);
        [exact OK| lia| apply obj_frame_local| exact HSM3| | lia| reflexivity|].
      { eapply (cont_req_ok2 E _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 HSM4.
      obj_open HSM4 OK.

      step. zstep.
      obj_close HSM5 OK.
      eapply evt_eq; [| eapply TAIL]; [pj_st_eq| exact HSM5| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.

End Proofs.
End WithCeiling0.

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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_str_a Pj_ser_str_b.
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
  Variable isobj : list byte.
  Variables (i dp c l A : Z).
  Variable F : bvmap 5 word.
  Variable fc : bv 32.
  Hypothesis FRM : frm0 fc.
  Hypothesis OK : senv_ok E.
  Hypothesis HSTR : str_at (e_S E) (e_sn E) c l.
  Hypothesis BUD : A + (2 + 6 * l) <= PJ_OUTMAX (e_len E).
  Hypothesis HK : av_K E Q (Z_to_bv 64 PJ_ESC_TAB) (Z_to_bv 64 PJ_LIT_BS) (Z_to_bv 64 PJ_LIT_QU) isobj PJ_AV1 i dp (A + (2 + 6 * l)).
  Hypothesis HI : 1 <= i < e_n E.
  Hypothesis HT : e_T E i = tword t_str c.

  Notation DATA := (e_SBUF E + c + 4).
  Notation SPILL := (Z_to_bv 64 DATA).
  Notation NET := (Z_to_bv 64 PJ_NE_TAB).

  Notation str_scan8 := (Pj_ser_str_b.str_scan8 HM HF E Q isobj i dp c l A F fc FRM OK HSTR BUD HK).

  Lemma str_head : forall (st : sbst) (s : PState) (m : mem) (spill0 : word)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERMC E spill0 isobj st s m -> sb_size st <= A ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3e780 i dp NET (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 (Z_to_bv 64 34) (Z_to_bv 64 34) xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).
  Proof using HM HF OK HSTR BUD HK FRM HI HT.
    intros st s m spill0 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM ACC.
    destruct st as [buf size cap blk fuel]. cbn [sb_size] in *.
    ser_env OK.
    pose proof OK as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AL1 AL2]].
    pose proof HSTR as (C0 & L0 & CL & LE & _).
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & SB0 & SB1).
    pose proof (S_range E c OK) as BR0. pose proof (S_range E (c + 1) OK) as BR1.
    pose proof (S_range E (c + 2) OK) as BR2. pose proof (S_range E (c + 3) OK) as BR3.
    unfold le32 in LE.
    set (b0 := e_S E c) in *. set (b1 := e_S E (c + 1)) in *. set (b2 := e_S E (c + 2)) in *. set (b3 := e_S E (c + 3)) in *.
    pose proof (tword_range t_str c ltac:(unfold t_str; lia) ltac:(lia)) as TR.
    assert (EA : Z.land (Z.land (tword t_str c) 18446744073709551615) 72057594037927935 = c).
    { rewrite pj_land64 by lia. rewrite land_mask56 by lia. apply tval_tword. lia. }
    assert (EA' : Z.land (tword t_str c) 72057594037927935 = c).
    { rewrite land_mask56 by lia. apply tval_tword. lia. }

    assert (TAIL : forall (st5 : sbst) (s5 : PState) (m5 : mem) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
      SERMC E SPILL isobj st5 s5 m5 -> sb_size st5 = size -> size + 1 <= sb_cap st5 ->
      evt usegs (sgoal E Q (sb_ch st5) s5)
          (SST E 0x3e818 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 i) NET (Z_to_bv 64 b0) (Z_to_bv 64 dp)
               (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (e_SBUF E + c)) (Z_to_bv 64 PJ_RBR56) (Z_to_bv 64 b1) (Z_to_bv 64 b2) (Z_to_bv 64 b3) yt3 yt4 yt5 yt6 F fc m5)).
    { intros st5 s5 m5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM5 ESZ ROOM.
      destruct st5 as [buf5 size5 cap5 blk5 fuel5]. cbn [sb_size sb_cap] in ESZ, ROOM. subst size5.
      ser_open HSM5 OK.

      step. step. zstep. zstep. step. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap. gtrap.

      step. step. step. pj_store_done.

      zstep. zstep. zstep. zstep. zstep. zstep.
      assert (EL : Z.lor (Z.lor (Z.land (Z.shiftl b3 24) 18446744073709551615) (Z.land (Z.shiftl b2 16) 18446744073709551615))
                         (Z.lor (Z.land (Z.shiftl b1 8) 18446744073709551615) b0) = l).
      { rewrite !pj_land64 by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite lor4_le32 by lia. lia. }
      rewrite !EL.

      step. zstep. unot.
      ser_close HSM6 OK.
      eapply evt_eq; [| eapply (str_scan8 (S (Z.to_nat l)) 0 (mkSb buf5 (size + 1) cap5 blk5 fuel5))];
        [pj_st_eq| lia| lia| lia| exact HSM6| cbn [sb_size]; lia]. }
    ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RDT. rewrite HT in RDT.

    step. step. step.
    eapply tape_ref_call; [exact DOCC| exact AL2| lia| lia| lia| lia| reflexivity|].

    step. gtrap. step. step. zstep. rewrite ?EA, ?EA'. zstep. zstep. gtrap. gtrap.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC2.
    pose proof (tape_read_mu E _ _ _ _ i OK HREF MU WM ltac:(lia)) as RDT2. rewrite HT in RDT2.

    step. step. step.
    eapply tape_ref_call; [exact DOCC2| exact AL2| lia| lia| lia| lia| reflexivity|].

    step. step. step. zstep. rewrite ?EA, ?EA'. zstep. gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. gtrap.

    replace (Z_to_bv 64 (c + e_SBUF E + 4)) with SPILL by (f_equal; lia).
    step. gtrap.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (sbuf_read_mu E _ _ _ _ (c + 0) OK HREF MU WM ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0; fold b0 in RD0;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 1) OK HREF MU WM ltac:(lia)) as RD1; fold b1 in RD1;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 2) OK HREF MU WM ltac:(lia)) as RD2; fold b2 in RD2;
      pose proof (sbuf_read_mu E _ _ _ _ (c + 3) OK HREF MU WM ltac:(lia)) as RD3; fold b3 in RD3 end.

    step. step. zstep. zstep. zstep. zstep. pjnorm. zstep. step.
    if_cases K; zify_cond K.
    - pjnorm_in K. ser_close HSM2 OK. eapply evt_eq; [| eapply TAIL]; [pj_st_eq| exact HSM2| reflexivity| cbn [sb_cap]; lia].
    - pjnorm_in K.

      zstep. pjnorm. step. step.
      ser_close HSM3 OK.
      eapply (ser_grow HM HF) with (z := 2 * cap) (rpc := 0x3e818); [exact OK| exact HSM3| | lia| reflexivity|].
      { eapply (ser_req_ok2 E _ _ _ _ _ _ _ _ OK HSM3). cbn [sb_cap]. lia. }
      intros s' m' b' NEW yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4.
      eapply evt_eq; [| eapply TAIL]; [pj_st_eq| exact HSM4| reflexivity| unfold sb_grown; cbn [sb_cap]; lia].
  Qed.
End Proofs.

  Theorem str_proof : rmalloc_stmt -> rfree_stmt -> str_stmt.
  Proof.
    intros HM HF. unfold str_stmt.
    intros E Q spill isobj st s m F fc i c l dp A xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 OK HSM FRM HI HT HSTR ACC BUD HK.
    eapply (str_head HM HF E Q isobj i dp c l A F fc FRM OK HSTR BUD HK HI HT); [exact HSM| exact ACC].
  Qed.

End WithCeiling0.

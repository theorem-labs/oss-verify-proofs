(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition ATP_TIX_A : Z := 0xaf58c.

Lemma tix_shr61' : forall i, 0 <= i < 2^60 -> Z.shiftr (i + 1152921504606846976) 61 = 0.
Proof. intros i Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma le8_nth7 : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma u64s_read7 : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.
Lemma tape_read_type : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7 by (rewrite length_map; lia).
  rewrite <- le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Section ArrLeaves.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma tix_cps : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (sp i RA : Z)
      (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    AINV_A E m -> 0 <= i < ae_n E ->
    shb_cells m -> (forall m', munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    stk bsegs m (ae_lo E) sp -> ae_lo E + 16 <= sp -> sp <= ae_hi E -> sp mod 16 = 0 -> mem_inv bsegs m ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (xa1 xa3 xa4 : word), munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) sp ->
       evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (ae_TAPE E + 8 * i)) xa1 (wz (ae_TAPE E)) xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (ae_DOC E)) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATP_TIX_A) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros AI IR [G1 G2] SHZD ST LO HI S16 MI RA0 RA2 HK.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold ATP_TIX_A, SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof AI as (_ & _ & _ & DOCC & _).
    pose proof (munch_refl [(sp + -16, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step.

    chk0 SHZD (ae_DOC E). step. if_false.
    step. astep. astep.

    astep. astep.
    replace (0 <? ae_TAPE E) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (ae_TAPE E + 8 * i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    step. if_false.

    astep. astep. astep. astep. rewrite tix_shr61' by lia. step. if_false.

    step. if_dead1 by IR TS. step. if_dead1 by TS. astep. step. if_dead1 by T16 IR TS.

    step. step. release_frame FR ST sp. step.
    name_mem m1. replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply HK; [exact MU| exact WM| exact MI1| exact ST1].
  Qed.
End ArrLeaves.

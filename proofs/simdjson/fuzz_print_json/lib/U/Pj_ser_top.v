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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require F_printf_core_common.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_loop_defs Pj_ser_ends Pj_ser_disp Pj_ser_head Pj_ser_loop Pj_ser_open Pj_cont_kit Pj_ser_num Pj_ser_true.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ser_Q (E : senv) : @chst bptr -> PState -> machine_state -> Prop :=
  ser_post (e_ra E) (e_q E) (e_gp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E)
           (e_ps0 E) (e_LB0 E) (e_lo E) (e_B E) (e_SB E) (e_len E) (e_j E) (e_c' E) (e_m0 E).

Lemma ser_epilogue : forall E, senv_ok E -> exit_K E (ser_Q E).
Proof.
  intros E OK. unfold exit_K.
  intros st s m F fc e64 e72 e80 spill isobj xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         HSM FRM ACC.
  pose proof (SBINV_of_SERM _ _ _ _ _ _ _ _ _ HSM) as INV.
  pose proof (SBINV_cap_pos _ _ _ _ INV) as CAP64.
  pose proof HSM as [HR0 _].
  pose proof HR0 as (HEAP & AUX & PRES & _ & _ & _ & (errv & ERR) & FA & SO & PURE).
  destruct st as [buf size cap blk fuel]. cbn [sb_size sb_cap] in *.
  ser_env OK. ser_open HSM OK.

  do 13 step. step.
  release_frame FRA ST (e_q E + -160).
  pose proof (u8arr_stk _ _ _ FRI) as SI. rewrite FRIL in SI.
  replace (e_q E + -160 + Z.of_nat 16) with (e_q E + -144) in SI by lia.
  pose proof (stk_merge usegs _ _ _ _ ST SI ltac:(lia)) as ST1.
  pose proof (stk_merge usegs _ _ _ _ ST1 FRT ltac:(lia)) as ST2.
  release_frame FRS ST2 (e_q E).
  step.
  apply evt_done. unfold sgoal, sb_ch. cbn [ch_fuel ch_cap ch_blk fst snd sb_fuel sb_cap sb_blk].
  apply implM_pj_part_stop; [lia|].
  apply evt_done. unfold ser_Q, ser_post.
  do 15 eexists. exists F, fc, m, errv, (mkSb buf size cap blk fuel).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MI|]. split; [exact ST2|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact FRM|].
  split; [exact FA|]. split; [exact SO|]. split; [reflexivity|]. split; [exact HEAP|]. split; [exact INV|].
  split; [unfold sb_acc; cbn [sb_size]; lia| exact PRES].
Qed.

Lemma ser_entry : forall (E : senv) (D : nat) (st : sbst) (F : bvmap 5 word) (fc : bv 32) (errv : word) (i c : Z)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  senv_ok E ->
  RHEAP (e_ps0 E) (sbblocks st ++ e_LB0 E) (e_m0 E) -> rauxv_ok (e_m0 E) (e_B E) ->
  stk usegs (e_m0 E) (e_lo E) (e_q E) ->
  rw_cells usegs (e_m0 E) LX_ERRNO [C4 errv] -> mem_inv usegs (e_m0 E) -> frm0 fc ->
  SBINV (e_m0 E) (e_SB E) (e_len E) st ->
  DOCREP (e_m0 E) (e_LB0 E) (e_DOC E) (e_TAPE E) (e_SBUF E) (e_len E) (e_tws E) (e_sbs E) ->
  elemS (e_T E) (e_S E) (e_sn E) ck_any D i (e_j E) c (e_c' E) -> 1 <= i -> 0 <= c ->
  sb_acc1 st i c ->
  (forall f, head_stmt E (ser_Q E) D f) ->
  evt usegs (sgoal E (ser_Q E) (sb_ch st) (e_ps0 E))
      (MS (mkR (e_ra E) (Z_to_bv 64 (e_q E)) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 (e_s0 E) (e_s1 E)
               (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_APPEND_ELEM) fc None (e_m0 E) (seg_rom usegs)).
Proof.
  intros E D st F fc errv i c t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6
         OK HEAP AUX ST ERR MI FRM INV DOCR HEL HI HC ACC KH.
  pose proof DOCR as (DOCC & TAPEB & SBUFB & _).
  pose proof OK as [_ _ _ _ _ _ _ _ _ _ _ [D1 D2] _ _ _ [AL1 AL2]].
  assert (HREF : SREF E st (e_ps0 E) (e_m0 E)).
  { unfold SREF. split; [exact HEAP|]. split; [exact AUX|]. split; [apply lx_pres_refl|]. split; [exact TAPEB|]. split; [exact SBUFB|].
    split; [exact DOCC|]. split; [exists errv; exact ERR|]. split; [reflexivity|]. split; [reflexivity|].
    eapply sb_pure_of_SBINV; exact INV. }
  pose proof (sb_pure_ranges E st OK ltac:(eapply sb_pure_of_SBINV; exact INV)) as (R0 & R1 & R2 & R3 & _).
  pose proof INV as (SV & SZ & (bs & BUF) & (ji & INL) & _).
  assert (BUFS : stk usegs (e_m0 E) (sb_buf st) (sb_buf st + sb_cap st)).
  { pose proof (stk_of_rw_cells usegs _ _ _ BUF) as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
  assert (INLS : stk usegs (e_m0 E) (e_SB E) (e_SB E + 64)).
  { pose proof (stk_of_rw_cells usegs _ _ _ INL) as S. cbn [cells_size csize Nat.add] in S. exact S. }
  clear BUF INL bs ji.
  pose proof (munch_refl (serW E st) (e_m0 E)) as MU. pose proof (wmono_refl usegs (e_m0 E)) as WM. unfold serW in MU.
  unfold PJ_APPEND_ELEM.
  destruct st as [buf size cap blk fuel]. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in *.
  unfold sb_acc1 in ACC. cbn [sb_size] in ACC.
  ser_env OK.
  remember (e_m0 E) as m0 eqn:EM0.

  step.
  carve_frame 104%nat ST. rename FR into FRS.
  apply (rw_cells_split_CB usegs _ _ [] 104 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FRS; [|reflexivity]. cbn [mk_CB_cells app] in FRS.
  repeat match type of FRS with context [CB 8 ?b] => tryif is_var b then fail else (let j := fresh "js" in set (j := b) in FRS; clearbody j) end.
  clear junk.
  destruct (stk_split usegs _ _ (e_q E + -144) _ ST ltac:(lia)) as [ST' FRT]. clear ST. rename ST' into ST.
  carve_frame 16%nat ST. rename FR into FRI0.
  assert (FRIL : length junk = 16%nat) by (destruct FRI0 as [[[HL _] _] _]; exact HL).
  pose proof (u8arr_of_rw_cells usegs _ _ _ _ FRI0) as FRI. clear FRI0.
  carve_frame 96%nat ST. rename FR into FRA.
  apply (rw_cells_split_CB usegs _ _ [] 96 junk0 [] [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FRA; [|reflexivity]. cbn [mk_CB_cells app] in FRA.
  repeat match type of FRA with context [CB 8 ?b] => tryif is_var b then fail else (let j := fresh "ja" in set (j := b) in FRA; clearbody j) end.
  clear junk0.
  eapply (F_printf_core_common.cb8_c8_in _ _ [_] _) in FRA. cbn [app] in FRA.
  eapply (F_printf_core_common.cb8_c8_in _ _ [_;_;_;_;_;_;_;_] _) in FRA. cbn [app] in FRA.
  eapply (F_printf_core_common.cb8_c8_in _ _ [_;_;_;_;_;_;_;_;_] _) in FRA. cbn [app] in FRA.
  eapply (F_printf_core_common.cb8_c8_in _ _ [_;_;_;_;_;_;_;_;_;_] _) in FRA. cbn [app] in FRA.
  repeat match type of FRA with context [le_bytes_to_word ?b] => let j := fresh "v" in set (j := le_bytes_to_word b) in FRA; clearbody j end.

  do 13 step.

  do 6 step.

  pose proof (u8arr_store_ok usegs _ (e_q E + -160) junk 0 (wa (e_q E + -160 + 0)) FRI ltac:(lia) eq_refl) as SOK1.
  rewrite Z.add_0_r in SOK1.
  step.
  first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0] | idtac].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u8arr_write usegs mm (e_q E + -160) junk 0 (Z_to_bv 8 0) FRI ltac:(lia)) as FRI' end.
  rewrite Z.add_0_r in FRI'. change (Z.to_nat 0) with 0%nat in FRI'.
  store_done.
  rewrite <- (upd_length junk 0 (Z_to_bv 8 0)) in FRIL. rename FRI' into FRI.

  zstep. zstep. zstep. rewrite (land7_mod8_0 (e_DOC E) AL1). zstep. unz. step. step. step. step.

  zstep. zstep. hstep. zstep. hstep. zstep. hstep.

  zstep. unot. hstep. zstep. unot. hstep. zstep. hstep. hstep.
  try (lazymatch goal with FRA : rw_cells _ _ _ ?cs |- _ =>
    lazymatch cs with context [C8 (Z_to_bv 64 (18446744073709551615 - (e_q E + -160)))] =>
      replace (18446744073709551615 - (e_q E + -160)) with (18446744073709551775 - e_q E) in FRA by lia end end).
  try (lazymatch goal with FRA : rw_cells _ _ _ ?cs |- _ =>
    lazymatch cs with context [C8 (Z_to_bv 64 (18446744073709551615 - (e_q E + -143)))] =>
      replace (18446744073709551615 - (e_q E + -143)) with (18446744073709551758 - e_q E) in FRA by lia end end).
  assert (JL : length junk = 16%nat) by (rewrite upd_length in FRIL; exact FRIL).
  ser_close HSMH OK.
  eapply evt_eq; [| eapply (KH (Z.to_nat (e_j E - i)) D [] i (e_j E) c (e_c' E) false (upd junk 0 (Z_to_bv 8 0)) (mkSb buf size cap blk fuel)
                              (e_ps0 E) _ F fc)];
    [pj_st_eq| lia| cbn [length]; lia| cbn [length]; lia| | exact HEL| apply rest_nil| reflexivity| exact HI| exact HC| exact HSMH| exact FRM| cbn [sb_size]; lia].
  split; [apply nth_error_upd_same; lia| intros j k Hj; destruct j; discriminate Hj].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Hypothesis PSTR : str_stmt.
  Hypothesis PKEY : key_stmt.

  Theorem ser_of_rec : forall D, rec_ok D -> ser_stmt D.
  Proof using HM HF PSTR PKEY.
    intros D REC. unfold ser_stmt.
    intros ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 q lo B errv SB len st DOC TAPE SBUF tws sbs i j c c'
           HEAP AUX QB B63 ST CEIL GLO LO ERR MI FRM QSB SBB QDOC DOCB SEP HLEN INV DOCR AL1 AL2 HEL HI HJ HC HC' ACC.
    set (E := mkSE LB0 lo B q SB DOC TAPE SBUF len tws sbs j c' ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    assert (OK : senv_ok E).
    { pose proof DOCR as (_ & _ & _ & WF & SBS & TSZ & SSZ & OKT & OKS).
      unfold ser_need in LO.
      constructor; cbn [E e_LB0 e_lo e_B e_q e_SB e_DOC e_TAPE e_SBUF e_len e_tws e_sbs e_j e_c']; try assumption; try lia. }
    assert (STK : e_lo E <= e_q E - ser_need D) by exact LO.
    pose proof (Pj_ser_num.num_arms HM HF) as (PI64 & PU64 & PDBL & PNULL & PFALSE).
    unfold implM. apply impl_from_evt.
    change (evt usegs (sgoal E (ser_Q E) (sb_ch st) (e_ps0 E))
              (MS (mkR (e_ra E) (Z_to_bv 64 (e_q E)) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 (e_s0 E) (e_s1 E)
                       (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
                       (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
                  F (Z_to_bv 64 PJ_APPEND_ELEM) fc None (e_m0 E) (seg_rom usegs))).
    eapply (ser_entry E D st F fc errv i c t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 OK HEAP AUX ST ERR MI FRM INV DOCR HEL HI HC ACC).
    clearbody E.
    intros f.
    eapply (loop_closed HM HF E (ser_Q E) D OK (ser_epilogue E OK)); try assumption.
    - intros f0 k KH AV. exact (open_proof HM HF E (ser_Q E) D f0 OK (ser_epilogue E OK) KH REC STK k).
    - exact (Pj_ser_true.true_proof HM HF).
  Qed.

End Proofs.
End WithCeiling0.

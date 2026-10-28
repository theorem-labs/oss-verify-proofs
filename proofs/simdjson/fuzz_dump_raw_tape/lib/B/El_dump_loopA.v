(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA El_esc_ifaceA El_dump_kitA El_dump_body1A El_dump_body2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Loop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Variable D : dctx.
Hypothesis DOK : dctx_ok D.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis IUL : ins_ul_cpsA RT PMc.
Hypothesis IU : ins_u_cpsA RT PMc.
Hypothesis IL : ins_l_cpsA RT PMc.
Hypothesis INSD : ins_d_cpsA RT PMc.
Hypothesis ESC : esc_cpsA RT PMc.
Hypothesis CRB : EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n (d_E D) + EL_DUMP_CSB * ae_sn (d_E D) <= d_cr D.

Notation GI := (GINVA RT (d_G D) 0x1002 0 FILLOK).
Notation n := (ae_n (d_E D)).
Notation T := (ae_T (d_E D)).
Notation S := (ae_S (d_E D)).
Notation sn := (ae_sn (d_E D)).
Notation KLOOP := (KLOOPA RT PMc D).

Let WFS : tape_wfS T S sn ck_any n. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DOK)))))). Qed.
Let NR : 2 < n < 2^32. Proof. exact (proj1 WFS). Qed.
Let HSN : 0 <= sn < 2^56. Proof. exact (proj1 (proj2 WFS)). Qed.

Lemma dump_scalarA : forall (i j c c' : Z) (K : config -> Prop),
  scalarS T S sn i j c c' -> 1 <= i -> j <= n - 1 -> 0 <= c -> c <= sn -> KLOOP K j c' -> KLOOP K i c.
Proof using AF RC RC2 FDO MST DOK PUT IUL IU IL INSD ESC CRB WFS NR HSN.
  intros i j c c' K SC I1 JN C0 CS HK. unfold KLOOPA. intros Σ m k sv1 sv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc GI0 FRM K0 KB.
  destruct SC as [(-> & TY & ->)|[(-> & TY & ->)|(-> & STR)]].
  - assert (TR : 0 <= T i < 2^64) by (destruct TY as [E|[E|E]]; rewrite E; apply tword_range; unfold t_true, t_false, t_null; lia).
    eapply (dump_headA RT AF PMc FDO MST D DOK PUT IUL CRB K i); [exact GI0| exact FRM| lia| exact TR| exact K0| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - KB I1 JN CS C0; lia|].
    intros. eapply (dump_atomA RT AF PMc FDO MST D DOK PUT CRB K i c); [eassumption| eassumption| lia| lia| exact TY| exact HK| clear - K0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB I1; lia| clear - C0 CS; lia].
  - assert (TR : 0 <= T i < 2^64) by (destruct TY as [E|[E|E]]; rewrite E; apply tword_range; unfold t_i64, t_u64, t_dbl; lia).
    eapply (dump_headA RT AF PMc FDO MST D DOK PUT IUL CRB K i); [exact GI0| exact FRM| lia| exact TR| exact K0| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - KB I1 JN CS C0; lia|].
    intros. destruct TY as [E|[E|E]].
    + eapply (dump_numA RT AF PMc FDO MST D DOK PUT IUL IL CRB K i c); [eassumption| eassumption| lia| lia| left; exact E| exact HK| clear - K0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB I1; lia| clear - C0 CS; lia].
    + eapply (dump_numA RT AF PMc FDO MST D DOK PUT IUL IL CRB K i c); [eassumption| eassumption| lia| lia| right; exact E| exact HK| clear - K0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB I1; lia| clear - C0 CS; lia].
    + eapply (dump_numdA RT AF PMc FDO MST D DOK PUT INSD CRB K i c); [eassumption| eassumption| lia| lia| exact E| exact HK| clear - K0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB I1; lia| clear - C0 CS; lia].
  - destruct STR as (l & TI & SA & ->). pose proof (str_at_bounds _ _ (proj2 HSN) _ _ SA) as (O0 & L0 & OL & _ & O56).
    assert (TR : 0 <= T i < 2^64) by (rewrite TI; apply tword_range; unfold t_str; lia).
    eapply (dump_headA RT AF PMc FDO MST D DOK PUT IUL CRB K i); [exact GI0| exact FRM| lia| exact TR| exact K0| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - KB I1 JN CS C0; lia|].
    intros. eapply (dump_strA RT AF PMc FDO MST D DOK PUT ESC CRB K i c l); [eassumption| eassumption| lia| lia| exact TI| exact SA| exact HK| clear - K0; lia| clear - KB; lia].
Qed.

Lemma tilesS_kloopA : forall (P : Z -> Z -> Z -> Z -> Prop) (K : config -> Prop) (it e cnt c c' : Z),
  (forall a b x y, P a b x y -> a < b) -> (forall a b x y, P a b x y -> x <= y /\ (x <= sn -> y <= sn)) ->
  (forall a b x y, P a b x y -> 1 <= a -> b <= n - 1 -> 0 <= x -> x <= sn -> KLOOP K b y -> KLOOP K a x) ->
  tilesS P it e cnt c c' -> 1 <= it -> e <= n - 1 -> 0 <= c -> c <= sn -> KLOOP K e c' -> KLOOP K it c.
Proof.
  intros P K it e cnt c c' Plt Pcur STEP TI. induction TI as [it c|it j0 e0 cnt0 c c1 c' Pij Tt IHt]; intros LO HI C0 CS KE; [exact KE|].
  pose proof (Plt _ _ _ _ Pij). pose proof (Pcur _ _ _ _ Pij) as [M1 M2]. pose proof (tilesS_le _ Plt _ _ _ _ _ Tt) as [JE _].
  eapply STEP; [exact Pij| lia| lia| lia| lia| apply IHt; [lia| lia| lia| lia| exact KE]].
Qed.

Lemma dump_elemA : forall (d : nat) (i j c c' : Z) (K : config -> Prop),
  elemS T S sn ck_any d i j c c' -> 1 <= i -> j <= n - 1 -> 0 <= c -> c <= sn -> KLOOP K j c' -> KLOOP K i c.
Proof using AF RC RC2 FDO MST DOK PUT IUL IU IL INSD ESC CRB WFS NR HSN.
  induction d as [|d IH]; intros i j c c' K EL I1 JN C0 CS HK.
  { cbn [elemS] in EL. destruct EL as [SC|[]]. eapply dump_scalarA; eassumption. }
  cbn [elemS] in EL. destruct EL as [SC|CO]; [eapply dump_scalarA; eassumption|].
  destruct CO as (e & cnt & cv & -> & CK & CO). unfold ck_any in CK.
  assert (OPEN : forall t tend (P : Z -> Z -> Z -> Z -> Prop), T i = cword t (e + 1) cv -> T e = tword tend i -> tilesS P (i + 1) e cnt c c' ->
            (t = t_arr /\ tend = t_arr_end \/ t = t_obj /\ tend = t_obj_end) -> (forall a b x y, P a b x y -> a < b) ->
            (forall a b x y, P a b x y -> x <= y /\ (x <= sn -> y <= sn)) ->
            (KLOOP K e c' -> KLOOP K (i + 1) c) -> KLOOP K i c).
  { intros t tend P Ti Te TI Ht Plt Pcur ITEMS.
    pose proof (tilesS_le _ Plt _ _ _ _ _ TI) as [IE _]. pose proof (tilesS_cur _ sn Pcur _ _ _ _ _ TI) as [CC1 CC2].
    assert (TR : 0 <= T i < 2^64) by (rewrite Ti; apply cword_range; [destruct Ht as [[-> _]|[-> _]]; unfold t_arr, t_obj; lia| lia| lia]).
    assert (TRE : 0 <= T e < 2^64) by (rewrite Te; apply tword_range; [destruct Ht as [[_ ->]|[_ ->]]; unfold t_arr_end, t_obj_end; lia| lia]).

    assert (CLOSE : KLOOP K e c').
    { unfold KLOOPA. intros Σ m k sv1 sv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc GI0 FRM K0 KB.
      eapply (dump_headA RT AF PMc FDO MST D DOK PUT IUL CRB K e); [exact GI0| exact FRM| lia| exact TRE| exact K0| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - KB I1 IE JN CS CC2 C0; lia|].
      intros. eapply (dump_closeA RT AF PMc FDO MST D DOK PUT IU CRB K e c'); [eassumption| eassumption| lia| lia| | exact HK| clear - K0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB I1 IE; lia| clear - C0 CS CC1 CC2; lia].
      rewrite Te, ttype_tword by lia. destruct Ht as [[_ ->]|[_ ->]]; [right| left]; reflexivity. }
    unfold KLOOPA. intros Σ m k sv1 sv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc GI0 FRM K0 KB.
    eapply (dump_headA RT AF PMc FDO MST D DOK PUT IUL CRB K i); [exact GI0| exact FRM| lia| exact TR| exact K0| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - KB I1 IE JN CS C0; lia|].
    intros. eapply (dump_openA RT AF PMc FDO MST D DOK PUT IUL IU CRB K i c); [eassumption| eassumption| lia| lia| exact TR| | apply ITEMS; exact CLOSE| clear - K0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB I1; lia| clear - C0 CS; lia].
    rewrite Ti, ttype_cword by lia. destruct Ht as [[-> _]|[-> _]]; [right| left]; reflexivity. }
  destruct CO as [(Ti & Te & TI)|(Ti & Te & TI)].
  -
    eapply (OPEN t_arr t_arr_end); [exact Ti| exact Te| exact TI| left; split; reflexivity| apply elemS_lt| apply elemS_cur|].
    intros KE. eapply (tilesS_kloopA (elemS T S sn ck_any d)); [apply elemS_lt| apply elemS_cur| | exact TI| lia| lia| lia| lia| exact KE].
    intros a b x y Pab A1 Bn X0 XS Kb. eapply IH; [exact Pab| exact A1| exact Bn| exact X0| exact XS| exact Kb].
  -
    assert (FCUR : forall a b x y, fieldS T S sn (elemS T S sn ck_any d) a b x y -> x <= y /\ (x <= sn -> y <= sn)).
    { intros a b x y (c1 & Hs & Hp). pose proof (str_rec_cur _ _ _ _ _ _ Hs). pose proof (elemS_cur _ _ _ _ _ _ _ _ _ Hp). lia. }
    eapply (OPEN t_obj t_obj_end); [exact Ti| exact Te| exact TI| right; split; reflexivity| apply fieldS_lt| exact FCUR|].
    intros KE. eapply (tilesS_kloopA (fieldS T S sn (elemS T S sn ck_any d))); [apply fieldS_lt| exact FCUR| | exact TI| lia| lia| lia| lia| exact KE].
    intros a b x y (c1 & STR & Pab) A1 Bn X0 XS Kb. pose proof (elemS_lt _ _ _ _ _ _ _ _ _ Pab). pose proof (str_rec_cur _ _ _ _ _ _ STR) as (S0 & S1 & S2).
    pose proof (elemS_cur _ _ _ _ _ _ _ _ _ Pab) as [PC1 PC2].

    eapply dump_scalarA; [right; right; split; [reflexivity| exact STR]| lia| lia| lia| lia|].
    eapply IH; [exact Pab| lia| exact Bn| lia| lia| exact Kb].
Qed.

Lemma dump_rootA : forall (K : config -> Prop), KLOOP K (n - 1) sn -> KLOOP K 1 0.
Proof using AF RC RC2 FDO MST DOK PUT IUL IU IL INSD ESC CRB WFS NR HSN.
  intros K HK. destruct WFS as (_ & _ & _ & _ & EL).
  eapply (dump_elemA TAPE_MAX_DEPTH); [exact EL| lia| lia| lia| lia| exact HK].
Qed.
End Loop.

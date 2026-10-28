(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Export Malloc_fp.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import MI_Inv MI_WGroup MI_Reframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocReframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RF_enframe RMallocKit_A RMalloc_fp RF_realloc_frame RF_aligned_head RF_aligned_arms.
Import ListNotations.
Open Scope Z_scope.

Notation RMFACTS := (@MFACTS_g ref_reserved).

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section SLOTW.
Variables (st : mstate) (m : mem) (g b : aptr) (r : region) (k : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Hypothesis HMR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Let c : aptr := (fst b, snd b + 16 + stride * k).
Let cz := snd b + 16 + stride * k.
Let eo := snd b + 16 + stride * k + stride - 4.
Let st1 := rf_tick st.

Lemma rsw_prep : rmrep st1 m /\ ticks_ok st1 /\ sstart mr k = cz.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  split; [apply rmrep_set_tick; exact HMR|]. split; [apply ticks_ok_set_tick; [lia| exact TK]|].
  unfold sstart, gbase. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, cz. fold stride. lia.
Qed.

(* [comment removed for export] *)
Lemma rsw8 : forall stx mx (o v : Z), rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st1 -> s_groups stx = s_groups st1 ->
  cz - 4 <= o < cz + stride - 4 -> 0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros stx mx o v MRx TKx ER EG Ho Hv. exact (rwr8_rep st1 g b r k 0 Hr Hk B0 K0 SPAN S16 NOGRP stx mx o v MRx TKx ER EG Ho Hv).
Qed.
Lemma rsw16 : forall stx mx (o v : Z), rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st1 -> s_groups stx = s_groups st1 ->
  cz - 4 <= o -> o + 2 <= cz + stride - 4 -> 0 <= v < 65536 ->
  rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. exact (rwr16_rep st1 g b r k 0 Hr Hk B0 K0 SPAN S16 NOGRP stx mx o v MRx TKx ER EG Ho Ho2 Hv).
Qed.
Lemma rsw32 : forall stx mx (o v : Z), rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st1 -> s_groups stx = s_groups st1 ->
  cz - 4 <= o -> o + 4 <= cz + stride - 4 -> 0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. exact (rwr32_rep st1 g b r k 0 Hr Hk B0 K0 SPAN S16 NOGRP stx mx o v MRx TKx ER EG Ho Ho4 Hv).
Qed.

(* [comment removed for export] *)
Lemma rss_stores : forall stx mx (po n : Z), rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st1 -> s_groups stx = s_groups st1 ->
  cz <= po -> 0 <= n -> po + n <= eo -> eo - po - n < 2^32 ->
  rmrep (wrs (ss_list (fst b) po eo n k) stx) (rr_setsize_mem mx (r_base r + po) (r_base r + eo) n k)
  /\ ticks_ok (wrs (ss_list (fst b) po eo n k) stx)
  /\ s_regions (wrs (ss_list (fst b) po eo n k) stx) = s_regions st1 /\ s_groups (wrs (ss_list (fst b) po eo n k) stx) = s_groups st1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros stx mx po n MRx TKx ERx EGx PO N0 PE R32.
  assert (SK : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
  set (rsv := eo - po - n). assert (RSV : 0 <= rsv < 2^32) by (unfold rsv; lia).
  unfold rr_setsize_mem. cbv zeta. replace (r_base r + eo - (r_base r + po) - n) with rsv by (unfold rsv; lia).
  unfold ss_list. cbv zeta. fold rsv.
  (* [comment removed for export] *)
  set (stA := if negb (rsv =? 0) then wr8 (fst b, eo - rsv) 0 stx else stx).
  set (mA := if rsv =? 0 then mx else write_to_mem mx (wa (r_base r + eo - rsv)) [b8 0]).
  assert (PA : rmrep stA mA /\ ticks_ok stA /\ s_regions stA = s_regions st1 /\ s_groups stA = s_groups st1).
  { subst stA mA. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact MRx|]. split; [exact TKx|]. split; assumption.
    - destruct (rsw8 stx mx (eo - rsv) 0 MRx TKx ERx EGx) as [M1 T1]; [unfold rsv, eo, cz in *; lia| lia|].
      replace (r_base r + eo - rsv) with (r_base r + (eo - rsv)) by lia.
      split; [exact M1|]. split; [exact T1|]. split; assumption. }
  destruct PA as (MA & TA & ERA & EGA).
  (* [comment removed for export] *)
  set (stB := if 5 <=? rsv then wr32 (fst b, eo - 4) rsv (wr8 (fst b, eo - 5) 0 stA) else stA).
  set (mB := if 5 <=? rsv then write_to_mem (write_to_mem mA (wa (r_base r + eo - 5)) [b8 0]) (wa (r_base r + eo - 4)) (le4 (wz rsv)) else mA).
  assert (PB : rmrep stB mB /\ ticks_ok stB /\ s_regions stB = s_regions st1 /\ s_groups stB = s_groups st1).
  { subst stB mB. destruct (Z.leb_spec 5 rsv) as [LE|GT].
    - destruct (rsw8 stA mA (eo - 5) 0 MA TA ERA EGA) as [M1 T1]; [unfold rsv, eo, cz in *; lia| lia|].
      destruct (rsw32 _ _ (eo - 4) rsv M1 T1 ERA EGA) as [M2 T2]; [unfold rsv, eo, cz in *; lia| unfold rsv, eo, cz in *; lia| lia|].
      replace (r_base r + eo - 5) with (r_base r + (eo - 5)) by lia. replace (r_base r + eo - 4) with (r_base r + (eo - 4)) by lia.
      split; [exact M2|]. split; [exact T2|]. split; assumption.
    - split; [exact MA|]. split; [exact TA|]. split; assumption. }
  destruct PB as (MB & TB & ERB & EGB).
  (* [comment removed for export] *)
  assert (KV : 0 <= k + 32 * Z.min rsv 5 < 256) by lia.
  destruct (rsw8 stB mB (po - 3) (k + 32 * Z.min rsv 5) MB TB ERB EGB) as [MC TC]; [unfold eo, cz in *; lia| exact KV|].
  assert (EW : wrs ((if negb (rsv =? 0) then [((fst b, eo - rsv), 0)] else []) ++
                    (if 5 <=? rsv then [((fst b, eo - 5), 0); ((fst b, eo - 4), rsv); ((fst b, eo - 4 + 1), Z.shiftr rsv 8);
                                        ((fst b, eo - 4 + 2), Z.shiftr rsv 16); ((fst b, eo - 4 + 3), Z.shiftr rsv 24)] else []) ++
                    [((fst b, po - 3), k + 32 * Z.min rsv 5)]) stx
               = wr8 (fst b, po - 3) (k + 32 * Z.min rsv 5) stB).
  { rewrite !wrs_app. subst stB stA. destruct (Z.eqb_spec rsv 0); destruct (Z.leb_spec 5 rsv); cbn [negb wrs]; reflexivity. }
  rewrite EW. replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. fold mA. fold mB.
  split; [exact MC|]. split; [exact TC|]. split; [exact ERB| exact EGB].
Qed.

(* [comment removed for export] *)
Lemma rsetsize_mrep : forall off n, 0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> stride - 4 - n < 2^32 ->
  rmrep (rf_setsize_st st c g b k off n) (rr_setsize_mem m (r_base r + (cz + 16 * off)) (r_base r + eo) n k)
  /\ ticks_ok (rf_setsize_st st c g b k off n).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros off n OFF0 N0 FIT S32. destruct rsw_prep as (MR1 & TK1 & ESS).
  assert (SK : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
  unfold rf_setsize_st, rf_full_st. change (MI_Inv.MR st g) with mr. fold stride. rewrite ESS. unfold UNIT, IB.
  replace (cz + stride - 4) with eo by (unfold eo, cz; lia).
  destruct (rss_stores st1 m (cz + 16 * off) n MR1 TK1 eq_refl eq_refl ltac:(lia) N0 ltac:(unfold eo, cz; lia) ltac:(unfold eo, cz; lia)) as (MC & TC & _ & _).
  exact (rmrep_havoc _ _ (aadd c (16 * off)) n MC TC).
Qed.

(* [comment removed for export] *)
Lemma rmove_mrep : forall off n, 1 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> stride - 4 - n < 2^32 ->
  0 <= (cz + 16 * off - snd b - 16) / 16 < 65536 -> off < 65536 ->
  rmrep (rf_move_st st c g b k off n)
        (ra_move_mem m (r_base r + cz) (r_base r + (cz + 16 * off)) (r_base r + eo) n k ((cz + 16 * off - snd b - 16) / 16) off)
  /\ ticks_ok (rf_move_st st c g b k off n).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros off n OFF1 N0 FIT S32 Q16 O16. destruct rsw_prep as (MR1 & TK1 & ESS).
  assert (SK : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
  unfold rf_move_st, rf_full_st. change (MI_Inv.MR st g) with mr. fold stride. rewrite ESS.
  assert (EGB : snd (MI_Inv.gbase mr) = snd b) by (unfold MI_Inv.gbase; rewrite Hmem; reflexivity).
  rewrite EGB. unfold UNIT, IB.
  replace (cz + stride - 4) with eo by (unfold eo, cz; lia).
  set (po := cz + 16 * off). set (q := (po - snd b - 16) / 16).
  unfold mv_list, ra_move_mem. cbv zeta. fold po. fold q. set (SSL := ss_list (fst b) po eo n k). rewrite (wrs_app _ (SSL ++ _)), (wrs_app SSL).
  (* [comment removed for export] *)
  destruct (rsw8 st1 m (po - 4) 0 MR1 TK1 eq_refl eq_refl) as [M1 T1]; [unfold po, eo, cz in *; lia| lia|].
  destruct (rsw8 _ _ (po - 3) k M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold po, eo, cz in *; lia| lia|].
  destruct (rsw16 _ _ (po - 2) q M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold po, eo, cz in *; lia| unfold po, eo, cz in *; lia| exact Q16|].
  set (stH := wr16 (fst b, po - 2) q (wr8 (fst b, po - 3) k (wr8 (fst b, po - 4) 0 st1))) in *.
  assert (EH : wrs [((fst b, po - 4), 0); ((fst b, po - 3), k); ((fst b, po - 2), q); ((fst b, po - 2 + 1), Z.shiftr q 8)] st1 = stH) by reflexivity.
  rewrite EH.
  (* [comment removed for export] *)
  destruct (rss_stores stH _ po n M3 T3 eq_refl eq_refl ltac:(unfold po; lia) N0 ltac:(unfold po, eo, cz; lia) ltac:(unfold po, eo, cz; lia)) as (M4 & T4 & ER4 & EG4).
  fold SSL in M4, T4, ER4, EG4.
  (* [comment removed for export] *)
  destruct (rsw8 _ _ (cz - 3) 224 M4 T4 ER4 EG4) as [M5 T5]; [unfold eo, cz in *; lia| lia|].
  assert (ER5 : s_regions (wr8 (fst b, cz - 3) 224 (wrs SSL stH)) = s_regions st1) by exact ER4.
  assert (EG5 : s_groups (wr8 (fst b, cz - 3) 224 (wrs SSL stH)) = s_groups st1) by exact EG4.
  destruct (rsw16 _ _ (cz - 2) off M5 T5 ER5 EG5) as [M6 T6]; [lia| unfold eo, cz in *; lia| lia|].
  replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia.
  replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia.
  replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia.
  replace (r_base r + cz - 3) with (r_base r + (cz - 3)) by lia. replace (r_base r + cz - 2) with (r_base r + (cz - 2)) by lia.
  exact (rmrep_havoc _ _ (aadd c (16 * off)) n M6 T6).
Qed.
End SLOTW.
End WithCeiling0.

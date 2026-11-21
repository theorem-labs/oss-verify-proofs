(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRelG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBitsG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintLzG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintTallyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition CFGG (s : deflate_state) : Prop := ds_w_bits s = 15 /\ ds_hash_bits s = 15 /\ (ds_strategy s <> 2 /\ ds_strategy s <> 3).

Lemma INVG_of_DC c0 s : DC c0 s -> CFGG s -> INVG s.
Proof.
  intros [[D X] V] (C1 & C2 & C3).
  pose proof (df_wsize _ D) as E1. pose proof (df_hsize _ D) as E2. pose proof (df_lbs _ D) as E3.
  rewrite C1 in E1. rewrite C2 in E2, E3. change (2 ^ 15) with 32768 in E1, E2. change (2 ^ (15 - 1)) with 16384 in E3.
  pose proof (df_wmask _ D) as E4. pose proof (df_hmask _ D) as E5. pose proof (df_hshift _ D) as E6. rewrite C2 in E6. change ((15 + MIN_MATCH - 1) / MIN_MATCH) with 5 in E6.
  pose proof (df_wsz _ D). pose proof (df_pbs _ D). pose proof (df_symend _ D). pose proof (df_wl _ D). pose proof (df_pl _ D). pose proof (df_hl _ D). pose proof (df_bl _ D).
  pose proof (df_strstart _ D). pose proof (df_ins _ D). pose proof (df_look _ D). pose proof (df_sl _ D). pose proof (df_hw _ D). pose proof (dx_hw _ X).
  pose proof (sv_ain _ _ V). pose proof (sv_aout _ _ V). pose proof (dx_opt _ X). pose proof (dx_stat _ X). pose proof (dx_ml _ X). pose proof (dx_pl _ X).
  pose proof (df_pend _ D). pose proof (dx_pout0 _ X).
  constructor; try (exact (df_tl _ D)); unfold MAX_MATCH in *; try lia.
Qed.


Definition PBC (B : Z -> Prop) (s : deflate_state) : Prop :=
  (ds_pending_out s = 0 /\ forall i, 0 <= i < ds_pending s -> B i)
  \/ (cs_avail_out (ds_strm s) = 0 /\ forall i, ds_pending_out s <= i < ds_pending_out s + ds_pending s -> B i).
Definition SYMB (B : Z -> Prop) (s : deflate_state) : Prop :=
  forall i, ds_lit_bufsize s <= i < ds_lit_bufsize s + ds_sym_next s -> B i.

Definition FREL (s1 s2 : deflate_state) : Prop :=
  exists W C B bnd ms pm,
    REL W C B bnd ms pm s1 s2
    /\ (forall i, i < WHI s1 -> W i)
    /\ bnd <= ds_strstart s1
    /\ PBC B s1 /\ SYMB B s1
    /\ HWI s1.

Definition FREL0 (s1 s2 : deflate_state) : Prop :=
  exists W C B bnd ms pm,
    REL W C B bnd ms pm s1 s2
    /\ (forall i, i < WHI s1 -> W i)
    /\ PBC B s1 /\ SYMB B s1
    /\ ds_level s1 = 0.

Definition DREL (s1 s2 : deflate_state) : Prop :=
  exists W C B bnd ms pm,
    REL W C B bnd ms pm s1 s2
    /\ (forall i, i < WHI s1 -> W i)
    /\ (ds_level s1 <> 0 -> bnd <= ds_strstart s1)
    /\ PBC B s1 /\ SYMB B s1
    /\ HWI s1.

Lemma DREL_FREL s1 s2 : DREL s1 s2 -> ds_level s1 <> 0 -> FREL s1 s2.
Proof. intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) L. exists W, C, B, bnd, ms, pm. repeat (split; [auto|]). exact HH. Qed.
Lemma FREL_DREL s1 s2 : FREL s1 s2 -> DREL s1 s2.
Proof. intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm. repeat (split; [auto|]). exact HH. Qed.
Lemma DREL_FREL0 s1 s2 : DREL s1 s2 -> ds_level s1 = 0 -> FREL0 s1 s2.
Proof. intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) L. exists W, C, B, bnd, ms, pm. repeat (split; [auto|]). exact L. Qed.
Lemma FREL0_DREL s1 s2 : FREL0 s1 s2 -> DREL s1 s2.
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & HP & HS & L). exists W, C, B, bnd, ms, pm. split; [exact R|]. split; [exact HW|].
  split; [intros X; exfalso; exact (X L)|]. split; [exact HP|]. split; [exact HS|]. unfold HWI. rewrite L. apply HWI4_lvl0.
Qed.

Lemma FREL_clean s1 s2 : FREL s1 s2 -> clean s1 = clean s2.
Proof. intros (W & C & B & bnd & ms & pm & R & _). exact (r_clean _ _ _ _ _ _ _ _ R). Qed.


Definition FLUSH_BLOCK_REL : Prop :=
  forall W C B bnd ms pm s1 s2 last,
    REL W C B bnd ms pm s1 s2 -> fb_entry s1 last -> fb_entry s2 last ->
    SYMB B s1 -> (forall i, i < WHI s1 -> W i) -> ds_block_start s1 <= ds_strstart s1 ->
    let s1' := tr_flush_block s1 (fb_buf s1) (fb_len s1) last in
    let s2' := tr_flush_block s2 (fb_buf s2) (fb_len s2) last in
    REL W C (Bx B 0 (ds_pending s1')) bnd ms pm s1' s2'.


Definition fwk (s : deflate_state) :=
  (ds_pending s, ds_pending_out s, ds_sym_next s, ds_lit_bufsize s, cs_avail_out (ds_strm s), ds_level s).

Lemma fwk_fws s : fwk (fst (fws s 32768)) = fwk s.
Proof. unfold fws. destruct (Z.leb _ _); [|reflexivity]. cbn [fst]. unfold slide_hash. dsr. destruct (_ <? _); reflexivity. Qed.
Lemma fwk_read_buf s off n : fwk (fst (read_buf s (RB_window off) n)) = fwk s.
Proof. unfold read_buf. destruct (_ =? 0); [reflexivity|]. unfold fwk. dsr. destruct (ds_wrap s =? 1); [|destruct (ds_wrap s =? 2)]; dsr; reflexivity. Qed.
Lemma fwk_fill_window_insert f : forall s str, fwk (fill_window_insert f s str) = fwk s.
Proof.
  induction f as [|f IH]; intros s str; [reflexivity|]. rewrite fill_window_insert_step.
  destruct (negb _); [|reflexivity]. cbv zeta. destruct (_ <? _); [|rewrite IH]; unfold insert_string; reflexivity.
Qed.
Lemma fwk_fwr s more : fwk (fst (fwr s more)) = fwk s.
Proof.
  unfold fwr. destruct (_ =? 0); [reflexivity|].
  pose proof (fwk_read_buf s (ds_strstart s + ds_lookahead s) more) as E. destruct (read_buf s _ more) as [s' n]. cbn [fst] in *.
  destruct (Z.leb _ _); [rewrite fwk_fill_window_insert|]; unfold fwk in *; dsr; exact E.
Qed.
Lemma fwk_fill_window_loop f : forall s, fwk (fill_window_loop f s 32768) = fwk s.
Proof.
  induction f as [|f IH]; intros s; cbn [fill_window_loop]; [reflexivity|].
  rewrite fill_window_body_eq. pose proof (fwk_fws s) as E1. destruct (fws s 32768) as [s1 more]. cbn [fst] in E1.
  pose proof (fwk_fwr s1 more) as E2. destruct (fwr s1 more) as [s2 brk]. cbn [fst] in E2.
  destruct brk; [congruence|]. destruct (_ && _); [rewrite IH|]; congruence.
Qed.
Lemma fwk_fill_window s : ds_w_size s = 32768 -> fwk (fill_window s) = fwk s.
Proof.
  intros Hw. unfold fill_window. rewrite Hw. rewrite <- (fwk_fill_window_loop 263 s).
  unfold fill_window_high. destruct (Z.ltb _ _); [|reflexivity]. destruct (Z.ltb _ _); [reflexivity|]. destruct (Z.ltb _ _); reflexivity.
Qed.
Lemma fwk_fields s s' : fwk s' = fwk s ->
  ds_pending s' = ds_pending s /\ ds_pending_out s' = ds_pending_out s /\ ds_sym_next s' = ds_sym_next s
  /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ cs_avail_out (ds_strm s') = cs_avail_out (ds_strm s) /\ ds_level s' = ds_level s.
Proof.
  intros E. unfold fwk in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat split; assumption.
Qed.

Lemma PBC_SYMB_transfer B s s' : fwk s' = fwk s -> PBC B s -> SYMB B s -> PBC B s' /\ SYMB B s'.
Proof.
  intros E P Q. pose proof (fwk_fields _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6).
  unfold PBC, SYMB in *. rewrite E1, E2, E3, E4, E5. exact (conj P Q).
Qed.

Lemma st_fill_rel s1 s2 flush :
  FREL s1 s2 -> INVG s1 -> INVG s2 -> ds_level s1 <> 0 ->
  snd (st_fill s1 flush) = snd (st_fill s2 flush)
  /\ FREL (fst (st_fill s1 flush)) (fst (st_fill s2 flush))
  /\ INVG (fst (st_fill s1 flush)) /\ INVG (fst (st_fill s2 flush))
  /\ (ds_lookahead s1 < MIN_LOOKAHEAD -> Z.min (ds_strstart (fst (st_fill s1 flush)) + ds_lookahead (fst (st_fill s1 flush)) + 258) 65536 <= ds_high_water (fst (st_fill s1 flush)))
  /\ (MIN_LOOKAHEAD <= ds_lookahead s1 -> fst (st_fill s1 flush) = s1).
Proof.
  intros FR I1 I2 Hlv. pose proof FR as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
  unfold st_fill. rel_fields R.
  destruct (Z.ltb_spec (ds_lookahead s1) MIN_LOOKAHEAD) as [L|L].
  2:{ cbn [fst snd]. split; [reflexivity|]. split; [exact FR|]. split; [exact I1|]. split; [exact I2|]. split; [intros; lia|reflexivity]. }
  pose proof (fill_window_rel _ _ _ _ _ _ _ _ R I1 I2 HW Hb) as (W' & C' & bnd' & HC' & HW' & Hb' & R').
  pose proof (fill_window_facts s1 I1) as (I1' & Elv & Ebs & Hhw & Hmin).
  pose proof (fill_window_facts s2 I2) as (I2' & _).
  pose proof (fwk_fill_window s1 (ig_wsize s1 I1)) as EK.
  pose proof (PBC_SYMB_transfer B _ _ EK HP HS) as [HP' HS'].
  set (t1 := fill_window s1) in *. clearbody t1. set (t2 := fill_window s2) in *. clearbody t2.
  assert (FR' : FREL t1 t2).
  { exists W', C', B, bnd', ms, pm. split; [exact R'|]. split; [exact HW'|]. split; [exact Hb'|]. split; [exact HP'|]. split; [exact HS'|].
    unfold HWI. apply HWI4_hw. exact Hmin. }
  rel_fields R'.
  destruct (_ && _); [|destruct (_ =? 0)]; cbn [fst snd];
    (split; [reflexivity|]); (split; [exact FR'|]); (split; [exact I1'|]); (split; [exact I2'|]); split; intros; try lia; exact Hmin.
Qed.


Definition HFREL (s1 s2 : deflate_state) (hh : Z) : Prop :=
  exists W C B bnd ms pm,
    REL W C B bnd ms pm s1 s2
    /\ (forall i, i < WHI s1 -> W i)
    /\ bnd <= ds_strstart s1
    /\ PBC B s1 /\ SYMB B s1
    /\ HWI s1
    /\ (hh <> 0 -> cv C bnd hh).

Lemma st_hash_rel s1 s2 :
  FREL s1 s2 -> INVG s1 -> INVG s2 ->
  snd (st_hash s1) = snd (st_hash s2)
  /\ HFREL (fst (st_hash s1)) (fst (st_hash s2)) (snd (st_hash s1))
  /\ INVG (fst (st_hash s1)) /\ INVG (fst (st_hash s2))
  /\ lz5 (fst (st_hash s1)) = lz5 s1 /\ fwk (fst (st_hash s1)) = fwk s1 /\ clean (fst (st_hash s1)) = set_ins_h (clean s1) (ds_ins_h (fst (st_hash s1))).
Proof.
  intros FR I1 I2. pose proof FR as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
  pose proof (ig_ss s1 I1). pose proof (ig_sl s1 I1).
  unfold st_hash. rel_fields R.
  destruct (Z.leb_spec MIN_MATCH (ds_lookahead s1)) as [L|L].
  2:{ cbn [fst snd]. split; [reflexivity|]. split; [|split; [exact I1|]; split; [exact I2|]; split; [reflexivity|]; split; [reflexivity|destruct s1; reflexivity]].
      exists W, C, B, bnd, ms, pm. repeat (split; [assumption|]). intros X. exfalso. exact (X eq_refl). }
  unfold MIN_MATCH in L.
  pose proof (rel_bnd_up _ _ _ bnd (ds_strstart s1) _ _ _ _ R Hb) as R0.
  pose proof (insert_string_rel _ _ _ _ _ _ _ _ (ds_strstart s1) R0 I1 I2 ltac:(lia) ltac:(lia) ltac:(apply HW; unfold WHI; lia) ltac:(lia)) as (Eh & R1 & CV).
  pose proof (INVG_insert_string s1 (ds_strstart s1) I1) as I1'. pose proof (INVG_insert_string s2 (ds_strstart s1) I2) as I2'.
  split; [exact Eh|]. split.
  - exists W, (fun p => C p \/ p = Z.land (ds_strstart s1) 32767), B, (ds_strstart s1), ms, pm.
    split; [exact R1|]. unfold insert_string. dsr. split; [exact HW|]. split; [lia|]. split; [exact HP|]. split; [exact HS|]. split; [exact HH|].
    intros _. eapply cv_mono; [exact CV|intros p Cp; left; exact Cp|lia].
  - split; [exact I1'|]. split; [exact I2'|]. unfold insert_string; dsr. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
Qed.


Lemma fwk_clean s : fwk (clean s) = fwk s. Proof. reflexivity. Qed.

Lemma fwk_of_clean s t : clean t = clean s -> fwk t = fwk s.
Proof. intros E. rewrite <- (fwk_clean t), <- (fwk_clean s), E. reflexivity. Qed.


Lemma st_match_rel s1 s2 hh :
  HFREL s1 s2 hh -> INVG s1 -> INVG s2 -> ds_level s1 <> 0 -> 1 <= ds_lookahead s1 ->
  ds_strstart s1 + MIN_LOOKAHEAD <= 65536 -> 1 <= ds_prev_length s1 ->
  FREL (st_match s1 hh) (st_match s2 hh)
  /\ INVG (st_match s1 hh) /\ INVG (st_match s2 hh)
  /\ lz5 (st_match s1 hh) = lz5 s1 /\ fwk (st_match s1 hh) = fwk s1
  /\ (lm_cond s1 hh = true -> ds_match_length (st_match s1 hh) <= ds_lookahead s1)
  /\ (lm_cond s1 hh = false -> st_match s1 hh = s1).
Proof.
  intros HF I1 I2 Hlv Hlk Hss Hpl. pose proof HF as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH & Hcv).
  pose proof (ig_ss s1 I1). pose proof (ig_sl s1 I1).
  unfold st_match, lm_cond. rel_fields R. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss |- *.
  destruct (Z.eqb_spec hh NIL) as [Hh0|Hh0]; cbn [negb andb].
  { split; [exists W, C, B, bnd, ms, pm; repeat (split; [assumption|]); exact HH|].
    split; [exact I1|]. split; [exact I2|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros X; discriminate X|reflexivity]. }
  destruct (Z.leb_spec (wrap32 (ds_strstart s1 - hh)) (ds_w_size s1 - (258 + 3 + 1))) as [Hd|Hd].
  2:{ split; [exists W, C, B, bnd, ms, pm; repeat (split; [assumption|]); exact HH|].
      split; [exact I1|]. split; [exact I2|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros X; discriminate X|reflexivity]. }
  unfold NIL in Hh0.
  assert (HW2 : forall i, 0 <= i <= ds_strstart s1 + 258 -> W i).
  { intros i Hi. apply HW. unfold WHI. eapply HWI4_use; [exact HH|exact Hlv|lia|lia|lia]. }
  pose proof (longest_match_rel _ _ _ _ _ _ _ _ hh R I1 I2 HW2 ltac:(lia) Hb (Hcv Hh0) Hh0 Hpl) as LM.
  cbv zeta in LM. destruct LM as (Er & ms' & Hms & R' & J1 & J2 & L5 & CL & Hrng & Hg & Hle).
  destruct (longest_match s1 hh) as [t1 ml]. destruct (longest_match s2 hh) as [t2 ml2]. cbn [fst snd] in *. subst ml2.
  pose proof (lz5_eq _ _ L5) as (Ess & Elk & Ehw & Elv & Ebs). pose proof (fwk_of_clean _ _ CL) as FK.
  split.
  - exists W, C, B, bnd, ms', pm. split; [apply rel_set_match_length; [exact R'|exact Hg]|].
    unfold WHI in *. dsr. rewrite Ess, Elk, Ehw. split; [exact HW|]. split; [exact Hb|].
    pose proof (PBC_SYMB_transfer B s1 (set_match_length t1 ml) ltac:(exact FK) HP HS) as [HP' HS'].
    split; [exact HP'|]. split; [exact HS'|]. unfold HWI in *. dsr. rewrite Elv, Elk, Ess, Ehw. exact HH.
  - split; [apply INVG_set_match_length; [lia|exact J1]|]. split; [apply INVG_set_match_length; [lia|exact J2]|].
    split; [exact L5|]. split; [exact FK|]. split; [intros _; dsr; exact Hle|intros X; discriminate X].
Qed.

Section Tally.

  Lemma deflate_fast_insert_rel f : forall W C B bnd ms pm s1 s2,
    REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
    bnd <= ds_strstart s1 ->
    (forall i, 0 <= i <= ds_strstart s1 + ds_match_length s1 + 2 -> W i) ->
    ds_strstart s1 + ds_match_length s1 + ds_lookahead s1 <= 65536 - 1 -> 3 <= ds_lookahead s1 ->
    1 <= ds_match_length s1 <= Z.of_nat f ->
    let t1 := deflate_fast_insert f s1 in let t2 := deflate_fast_insert f s2 in
    exists C', (forall p, C p -> C' p)
      /\ REL W C' B (ds_strstart t1) ms pm t1 t2
      /\ INVG t1 /\ INVG t2
      /\ ds_strstart t1 = ds_strstart s1 + ds_match_length s1 /\ ds_match_length t1 = 0
      /\ fwk t1 = fwk s1 /\ ds_lookahead t1 = ds_lookahead s1 /\ ds_high_water t1 = ds_high_water s1 /\ ds_block_start t1 = ds_block_start s1
      /\ ds_prev_length t1 = ds_prev_length s1.
  Proof.
    induction f as [|f IH]; intros W C B bnd ms pm s1 s2 R I1 I2 Hb HW Hsl Hlk3 Hml; [cbn in Hml; lia|].
    cbn [deflate_fast_insert]. rel_fields R.
    pose proof (ig_ss s1 I1). pose proof (ig_ins s1 I1). pose proof (ig_look s1 I1). pose proof (ig_ml s1 I1).
    pose proof (rel_set_strstart _ _ _ _ _ _ _ _ (ds_strstart s1 + 1) R) as R1.
    pose proof (INVG_set_strstart s1 (ds_strstart s1 + 1) ltac:(lia) ltac:(lia) ltac:(lia) I1) as I11.
    pose proof (INVG_set_strstart s2 (ds_strstart s1 + 1) ltac:(lia) ltac:(rel_fields R; lia) ltac:(rel_fields R; lia) I2) as I21.
    pose proof (rel_bnd_up _ _ _ bnd (ds_strstart s1 + 1) _ _ _ _ R1 ltac:(lia)) as R1'.
    dsr.
    pose proof (insert_string_rel _ _ _ _ _ _ _ _ (ds_strstart s1 + 1) R1' I11 I21 ltac:(lia) ltac:(lia) ltac:(apply HW; lia) ltac:(lia)) as (Eh & R2 & _).
    pose proof (INVG_insert_string _ (ds_strstart s1 + 1) I11) as I12. pose proof (INVG_insert_string _ (ds_strstart s1 + 1) I21) as I22.
    destruct (insert_string (set_strstart s1 _) _) as [u1 h1] eqn:Eu1. destruct (insert_string (set_strstart s2 _) _) as [u2 h2] eqn:Eu2. cbn [fst snd] in *.
    assert (Fu : ds_strstart u1 = ds_strstart s1 + 1 /\ ds_match_length u1 = ds_match_length s1 /\ ds_lookahead u1 = ds_lookahead s1
                 /\ fwk u1 = fwk s1 /\ ds_high_water u1 = ds_high_water s1 /\ ds_block_start u1 = ds_block_start s1 /\ ds_prev_length u1 = ds_prev_length s1).
    { apply (f_equal fst) in Eu1. cbn [fst] in Eu1. subst u1. unfold insert_string. dsr. repeat split; reflexivity. }
    destruct Fu as (Ess & Eml & Elk & Efw & Ehw & Ebs & Epl).
    pose proof (rel_set_match_length _ _ _ _ _ _ _ _ (ds_match_length u1 - 1) R2 ltac:(intros Hm; apply (r_g1 _ _ _ _ _ _ _ _ R2); lia)) as R3.
    pose proof (INVG_set_match_length u1 (ds_match_length u1 - 1) ltac:(lia) I12) as I13.
    pose proof (INVG_set_match_length u2 (ds_match_length u1 - 1) ltac:(lia) I22) as I23.
    rel_fields R2. dsr. rewrite Eml.
    destruct (Z.eqb_spec (ds_match_length s1 - 1) 0) as [Z0|Z0]; cbn [negb].
    - exists (fun p => C p \/ p = Z.land (ds_strstart s1 + 1) 32767). split; [auto|]. dsr. rewrite Ess.
      split; [rewrite <- Eml; exact R3|]. split; [rewrite <- Eml; exact I13|]. split; [rewrite <- Eml; exact I23|].
      rewrite Elk, Ehw, Ebs, Epl. repeat split; try lia. unfold fwk in *. dsr. exact Efw.
    - destruct (IH _ _ _ _ _ _ _ _ R3 I13 I23 ltac:(dsr; lia) ltac:(dsr; rewrite Ess; intros i Hi; apply HW; lia) ltac:(dsr; lia) ltac:(dsr; lia) ltac:(dsr; lia))
        as (C' & HC' & R4 & J1 & J2 & Ess' & Eml' & Efw' & Elk' & Ehw' & Ebs' & Epl').
      cbv zeta. rewrite <- Eml. exists C'. split; [intros p Cp; apply HC'; left; exact Cp|].
      split; [exact R4|]. split; [exact J1|]. split; [exact J2|].
      revert Ess' Eml' Efw' Elk' Ehw' Ebs' Epl'. dsr. rewrite Ess, Eml, Elk, Ehw, Ebs, Epl. unfold fwk in *. dsr. rewrite Efw. intros. repeat split; try assumption; lia.
  Qed.

  Lemma st_lit_rel W C B bnd ms pm s1 s2 :
    REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
    (forall i, i < WHI s1 -> W i) -> bnd <= ds_strstart s1 -> PBC B s1 -> SYMB B s1 -> HWI s1 ->
    1 <= ds_lookahead s1 -> 0 <= ds_sym_next s1 ->
    snd (st_lit s1) = snd (st_lit s2)
    /\ FREL (fst (st_lit s1)) (fst (st_lit s2)) /\ INVG (fst (st_lit s1)) /\ INVG (fst (st_lit s2))
    /\ fst (st_lit s1) = set_strstart (set_lookahead (set_dyn_ltree_fc (set_sym_next (set_pending_buf s1 (tl_pb s1 (arr_get (ds_window s1) (ds_strstart s1)))) (ds_sym_next s1 + 1 + 1 + 1)) (tl_fc s1 (arr_get (ds_window s1) (ds_strstart s1)))) (ds_lookahead s1 - 1)) (ds_strstart s1 + 1).
  Proof.
    intros R I1 I2 HW Hb HP HS HH Hlk Hsn.
    pose proof (ig_ss s1 I1). pose proof (ig_sl s1 I1). pose proof (ig_wl s1 I1). pose proof (ig_ins s1 I1).
    unfold st_lit.
    assert (EW : arr_get (ds_window s2) (ds_strstart s1) = arr_get (ds_window s1) (ds_strstart s1)).
    { symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [lia|apply HW; unfold WHI; lia]. }
    rel_fields R. rewrite EW. set (c := arr_get (ds_window s1) (ds_strstart s1)) in *.
    pose proof (tr_tally_lit_rel _ _ _ _ _ _ _ _ c R I1 I2) as [Eb R1].
    pose proof (INVG_tr_tally_lit s1 c I1) as J1. pose proof (INVG_tr_tally_lit s2 c I2) as J2.
    pose proof (tr_tally_lit_shape s1 c) as [Sh1 Sb1]. pose proof (tr_tally_lit_shape s2 c) as [Sh2 Sb2].
    destruct (tr_tally_lit s1 c) as [t1 b1]. destruct (tr_tally_lit s2 c) as [t2 b2]. cbn [fst snd] in *. subst t1 t2 b1 b2.
    rel_fields R. split; [reflexivity|]. dsr. rel_fields R.
    pose proof (tl_pb_len s1 c) as L1.
    split; [|split; [|split; [|reflexivity]]].
    - exists W, C, (Bx B (ds_lit_bufsize s1 + ds_sym_next s1) (ds_lit_bufsize s1 + ds_sym_next s1 + 3)), bnd, ms, pm.
      split; [apply rel_set_strstart, rel_set_lookahead; exact R1|].
      unfold WHI, PBC, SYMB, HWI, Bx in *. dsr. split; [intros i Hi; apply HW; lia|]. split; [lia|].
      split; [destruct HP as [[P1 P2]|[P1 P2]]; [left|right]; split; auto|].
      split; [intros i Hi; destruct (Z_lt_le_dec i (ds_lit_bufsize s1 + ds_sym_next s1)); [left; apply HS; lia|right; lia]|].
      eapply HWI4_shift; [exact HH|lia|lia|lia].
    - apply INVG_set_strstart; dsr; try lia. apply INVG_set_lookahead; dsr; try lia. exact J1.
    - pose proof (ig_ins s2 I2). pose proof (ig_sl s2 I2). pose proof (ig_look s2 I2). pose proof (ig_ss s2 I2).
      pose proof (rel_strstart _ _ _ _ _ _ _ _ R). pose proof (rel_lookahead _ _ _ _ _ _ _ _ R). pose proof (rel_insert _ _ _ _ _ _ _ _ R).
      apply INVG_set_strstart; dsr; try lia. apply INVG_set_lookahead; dsr; try lia. exact J2.
  Qed.

  Lemma st_dist_rel W C B bnd ms pm s1 s2 :
    REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
    (forall i, i < WHI s1 -> W i) -> bnd <= ds_strstart s1 -> PBC B s1 -> SYMB B s1 -> HWI s1 ->
    ds_level s1 <> 0 -> 0 <= ds_sym_next s1 ->
    MIN_MATCH <= ds_match_length s1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 65536 ->
    snd (st_dist s1) = snd (st_dist s2)
    /\ FREL (fst (st_dist s1)) (fst (st_dist s2)) /\ INVG (fst (st_dist s1)) /\ INVG (fst (st_dist s2))
    /\ ds_strstart (fst (st_dist s1)) = ds_strstart s1 + ds_match_length s1
    /\ ds_lookahead (fst (st_dist s1)) = ds_lookahead s1 - ds_match_length s1
    /\ ds_match_length (fst (st_dist s1)) = 0
    /\ fwk (fst (st_dist s1)) = fwk (set_sym_next s1 (ds_sym_next s1 + 1 + 1 + 1))
    /\ ds_high_water (fst (st_dist s1)) = ds_high_water s1 /\ ds_block_start (fst (st_dist s1)) = ds_block_start s1
    /\ ds_prev_length (fst (st_dist s1)) = ds_prev_length s1.
  Proof.
    intros R I1 I2 HW Hb HP HS HH Hlv Hsn Hml Hss.
    pose proof (ig_ss s1 I1). pose proof (ig_sl s1 I1). pose proof (ig_wl s1 I1). pose proof (ig_ins s1 I1). pose proof (ig_look s1 I1). pose proof (ig_ml s1 I1).
    unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hml, Hss.
    unfold st_dist. rel_fields R.
    rewrite <- (r_ms _ _ _ _ _ _ _ _ R ltac:(apply (r_g1 _ _ _ _ _ _ _ _ R); unfold MIN_MATCH; lia)).
    set (d := wrap32 (ds_strstart s1 - ds_match_start s1)). set (l := ds_match_length s1 - MIN_MATCH).
    pose proof (tr_tally_dist_rel _ _ _ _ _ _ _ _ d l R I1 I2) as [Eb R1].
    pose proof (INVG_tr_tally_dist s1 d l I1) as J1. pose proof (INVG_tr_tally_dist s2 d l I2) as J2.
    pose proof (tr_tally_dist_shape s1 d l) as [Sh1 Sb1]. pose proof (tr_tally_dist_shape s2 d l) as [Sh2 Sb2].
    destruct (tr_tally_dist s1 d l) as [t1 b1]. destruct (tr_tally_dist s2 d l) as [t2 b2]. cbn [fst snd] in *. subst t1 t2 b1 b2.
    split; [rel_fields R; reflexivity|].
    set (B' := Bx B _ _) in R1.
    match goal with |- context [set_lookahead ?x (ds_lookahead ?x - ds_match_length ?x)] =>
      pose proof (rel_set_lookahead _ _ _ _ _ _ _ _ (ds_lookahead x - ds_match_length x) R1) as R2;
      pose proof (INVG_set_lookahead x (ds_lookahead x - ds_match_length x)) as J1' end.
    dsr. specialize (J1' ltac:(lia) ltac:(lia) J1).
    match type of R2 with REL _ _ _ _ _ _ ?u1 ?u2 => set (v1 := u1) in *; set (v2 := u2) in *;
      assert (J2' : INVG v2) by (subst v2; rel_fields R; apply INVG_set_lookahead; dsr; rel_fields R; try lia; exact J2) end.
    assert (HSl : PBC B' v1 /\ SYMB B' v1).
    { subst v1 B'. unfold PBC, SYMB, Bx in *. dsr. split.
      - destruct HP as [[P1 P2]|[P1 P2]]; [left|right]; split; auto.
      - intros i Hi. destruct (Z_lt_le_dec i (ds_lit_bufsize s1 + ds_sym_next s1)); [left; apply HS; lia|right; lia]. }
    destruct HSl as [HP' HS'].
    rel_fields R2. unfold ins_cond. subst v1 v2. dsr. rel_fields R.
    match goal with |- context [if ?c then st_ins _ else _] => destruct c eqn:Ec end.
    -
      apply andb_prop in Ec. destruct Ec as [_ Ec]. apply Z.leb_le in Ec. revert Ec. dsr. unfold MIN_MATCH. intros Ec.
      unfold st_ins. dsr.
      match goal with |- context [deflate_fast_insert _ (set_match_length ?x ?m)] =>
        pose proof (rel_set_match_length _ _ _ _ _ _ _ _ m R2 ltac:(intros _; apply (r_g1 _ _ _ _ _ _ _ _ R); unfold MIN_MATCH; lia)) as R3;
        pose proof (INVG_set_match_length _ m ltac:(dsr; lia) J1') as K1;
        pose proof (INVG_set_match_length _ m ltac:(dsr; lia) J2') as K2 end.
      dsr. rel_fields R.
      match goal with |- context [deflate_fast_insert ?f ?x] =>
        destruct (deflate_fast_insert_rel f _ _ _ _ _ _ _ _ R3 K1 K2) as (C' & HC' & R4 & K1' & K2' & Ess & Eml & Efw & Elk & Ehw & Ebs & Epl);
        [dsr; lia | dsr; intros i Hi; apply HW | dsr; lia | dsr; lia | dsr; rewrite Z2Nat.id; lia |] end.
      { unfold WHI. dsr. lia. }
      revert Ess Eml Efw Elk Ehw Ebs Epl R4 K1' K2'. dsr.
      set (u1 := deflate_fast_insert _ _). set (u2 := deflate_fast_insert _ _). clearbody u1 u2.
      intros Ess Eml Efw Elk Ehw Ebs Epl R4 K1' K2'.
      pose proof (fwk_fields _ _ Efw) as (Fp & Fpo & Fsn & Flb & Fao & Flv). dsr.
      split; [|split; [|split; [|rewrite Ess, Elk, Eml, Ehw, Ebs, Epl; unfold fwk; dsr; rewrite Fp, Fpo, Fsn, Flb, Fao, Flv; repeat split; first [reflexivity | lia]]]].
      + exists W, C', B', (ds_strstart u1), ms, pm. split; [rewrite (rel_strstart _ _ _ _ _ _ _ _ R4); apply rel_set_strstart; exact R4|].
        unfold WHI, PBC, SYMB, HWI in *. dsr. rewrite Ess, Elk, Ehw, Fp, Fpo, Fsn, Flb, Fao, Flv.
        split; [intros i Hi; apply HW; lia|]. split; [lia|]. split; [exact HP'|]. split; [exact HS'|].
        eapply HWI4_shift; [exact HH|lia|lia|lia].
      + apply INVG_set_strstart; dsr; rewrite ?Ess, ?Elk; try lia; [|exact K1']. pose proof (ig_ins u1 K1'). lia.
      + pose proof (ig_ins u2 K2'). pose proof (rel_strstart _ _ _ _ _ _ _ _ R4). pose proof (rel_lookahead _ _ _ _ _ _ _ _ R4). pose proof (rel_insert _ _ _ _ _ _ _ _ R4).
        apply INVG_set_strstart; dsr; try lia. exact K2'.
    -
      unfold st_noins. dsr. rel_fields R.
      set (ss' := ds_strstart s1 + ds_match_length s1).
      assert (Hr : ss' + 1 < Z.max (ds_high_water s1) (ds_strstart s1 + ds_lookahead s1) /\ ss' + 1 < 65536).
      { subst ss'. unfold HWI, HWI4 in HH. destruct HH as [X|[X|X]]; [exfalso; exact (Hlv X)|lia|lia]. }
      assert (EW0 : arr_get (ds_window s2) ss' = arr_get (ds_window s1) ss').
      { symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [lia|apply HW; unfold WHI; lia]. }
      assert (EW1 : arr_get (ds_window s2) (ss' + 1) = arr_get (ds_window s1) (ss' + 1)).
      { symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [lia|apply HW; unfold WHI; lia]. }
      rewrite EW0.
      match goal with |- context [update_hash (set_ins_h (set_match_length (set_strstart ?x _) _) ?h0) _ _] =>
        pose proof (rel_set_ins_h _ _ _ _ _ _ _ _ h0 (rel_set_match_length _ _ _ _ _ _ _ _ 0 (rel_set_strstart _ _ _ _ _ _ _ _ ss' R2) ltac:(unfold MIN_MATCH; lia))) as R3 end.
      rewrite (update_hash_rel _ _ _ _ _ _ _ _ _ _ R3). dsr. rewrite EW1.
      match goal with |- _ /\ INVG ?x1 /\ INVG ?x2 /\ _ => set (u1 := x1); set (u2 := x2) end.
      assert (R4 : REL W C B' bnd ms pm u1 u2) by (subst u1 u2; apply rel_set_ins_h; exact R3).
      assert (K1 : INVG u1).
      { subst u1. apply INVG_set_ins_h, INVG_set_ins_h. apply INVG_set_match_length; [lia|]. apply INVG_set_strstart; dsr; try lia. exact J1'. }
      assert (K2 : INVG u2).
      { subst u2. pose proof (ig_ins s2 I2). pose proof (rel_strstart _ _ _ _ _ _ _ _ R). pose proof (rel_insert _ _ _ _ _ _ _ _ R). pose proof (rel_lookahead _ _ _ _ _ _ _ _ R). pose proof (rel_match_length _ _ _ _ _ _ _ _ R).
        apply INVG_set_ins_h, INVG_set_ins_h. apply INVG_set_match_length; [lia|]. apply INVG_set_strstart; dsr; try lia. exact J2'. }
      split; [|split; [exact K1|split; [exact K2|subst u1 ss'; dsr; repeat split; reflexivity]]].
      exists W, C, B', bnd, ms, pm. split; [exact R4|]. subst u1 u2 ss'.
      unfold WHI, PBC, SYMB, HWI in *. dsr.
      split; [intros i Hi; apply HW; lia|]. split; [lia|]. split; [exact HP'|]. split; [exact HS'|].
      eapply HWI4_shift; [exact HH|lia|lia|lia].
  Qed.
End Tally.


Lemma lzv_tfb s buf len last : lzv (tr_flush_block s buf len last) = lzv s.
Proof. rewrite (k_tr_flush_block lzv keeps_lzv). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.

Lemma INVG_transfer s t :
  INVG s -> lzv t = lzv s ->
  arr_len (ds_pending_buf t) = arr_len (ds_pending_buf s) -> tree_lens t ->
  0 <= ds_pending t -> (ds_pending t = 0 -> ds_pending_out t = 0) ->
  0 <= cs_avail_in (ds_strm t) -> 0 <= cs_avail_out (ds_strm t) ->
  0 <= ds_opt_len t < 2 ^ 64 -> 0 <= ds_static_len t < 2 ^ 64 ->
  INVG t.
Proof.
  intros I E L TL P PO AI AO OL SL. pose proof (lzv_fields _ _ E) as F. repeat match type of F with _ /\ _ => destruct F as [? F] end.
  destruct I; constructor; try assumption;
  repeat match goal with H : ?f t = ?f s |- context [?f t] => rewrite H end; try assumption.
  rewrite L; assumption.
Qed.

Definition lzm (s : deflate_state) :=
  (ds_strstart s, ds_lookahead s, ds_high_water s, ds_level s, ds_block_start s,
   (ds_match_length s, ds_prev_length s, ds_insert s, ds_match_available s, ds_lit_bufsize s)).
Lemma lzm_fields a b : lzm b = lzm a ->
  ds_strstart b = ds_strstart a /\ ds_lookahead b = ds_lookahead a /\ ds_high_water b = ds_high_water a /\ ds_level b = ds_level a
  /\ ds_block_start b = ds_block_start a /\ ds_match_length b = ds_match_length a /\ ds_prev_length b = ds_prev_length a
  /\ ds_insert b = ds_insert a /\ ds_match_available b = ds_match_available a /\ ds_lit_bufsize b = ds_lit_bufsize a.
Proof.
  intros E. unfold lzm in E.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.
Lemma lzm_of_lzv a b : lzv b = lzv a -> lzm b = lzm a.
Proof.
  intros E. pose proof (lzv_fields _ _ E) as F. repeat match type of F with _ /\ _ => destruct F as [? F] end.
  unfold lzm. repeat match goal with H : ?f b = ?f a |- context [?f b] => rewrite H end. reflexivity.
Qed.
Ltac lzm_rw E :=
  let F := fresh "LZM" in pose proof (lzm_fields _ _ E) as F; unfold lzm in *; dsr;
  repeat match type of F with _ /\ _ => let F1 := fresh "LZM" in destruct F as [F1 F]; rewrite ?F1 in * end;
  rewrite ?F in *.

Section Flush.
  Hypothesis HFB : FB_CALL.
  Hypothesis HFBR : FLUSH_BLOCK_REL.

  Lemma flush_block_only_rel s1 s2 last :
    FREL s1 s2 -> INVG s1 -> INVG s2 -> fb_entry s1 last -> fb_entry s2 last -> ds_block_start s1 <= ds_strstart s1 ->
    let t1 := flush_block_only s1 last in let t2 := flush_block_only s2 last in
    FREL t1 t2 /\ INVG t1 /\ INVG t2
    /\ lzm t1 = lzm (set_block_start s1 (ds_strstart s1))
    /\ ds_sym_next t1 = 0
    /\ (ds_pending t1 = 0 \/ cs_avail_out (ds_strm t1) = 0)
    /\ cs_avail_in (ds_strm t1) = cs_avail_in (ds_strm s1).
  Proof.
    intros FR I1 I2 FE1 FE2 Hbs. pose proof FR as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
    rewrite !flush_block_only_eq'.
    pose proof (HFBR _ _ _ _ _ _ _ _ last R FE1 FE2 HS HW Hbs) as R8. cbv zeta in R8.
    pose proof (proj2 (HFB s1 last FE1)) as P1. pose proof (proj2 (HFB s2 last FE2)) as P2.
    pose proof (lzv_tfb s1 (fb_buf s1) (fb_len s1) last) as L1. pose proof (lzv_tfb s2 (fb_buf s2) (fb_len s2) last) as L2.
    set (s8 := tr_flush_block s1 _ _ _) in *. clearbody s8. set (s8' := tr_flush_block s2 _ _ _) in *. clearbody s8'.
    pose proof (fp_pending _ _ _ P1) as Hp8. pose proof (fp_pout _ _ _ P1) as Hpo8. pose proof (fp_sn _ _ _ P1) as Hsn8.
    destruct (fp_strm _ _ _ P1) as (dt1 & Est1 & _). destruct (fp_strm _ _ _ P2) as (dt2 & Est2 & _).
    pose proof (ig_lbs s1 I1) as LBS. pose proof (ig_bl s1 I1) as BL1.
    assert (J1 : INVG s8).
    { eapply INVG_transfer; [exact I1|exact L1|rewrite (fp_pbl _ _ _ P1); lia|exact (fp_tl _ _ _ P1)|lia|intros; exact Hpo8
        |rewrite Est1; dsr; exact (ig_ain s1 I1)|rewrite Est1; dsr; exact (ig_aout s1 I1)|rewrite (fp_optlen _ _ _ P1); lia|rewrite (fp_statlen _ _ _ P1); lia]. }
    assert (J2 : INVG s8').
    { pose proof (fp_pending _ _ _ P2). pose proof (ig_lbs s2 I2).
      eapply INVG_transfer; [exact I2|exact L2|rewrite (fp_pbl _ _ _ P2); pose proof (ig_bl s2 I2); lia|exact (fp_tl _ _ _ P2)|lia|intros; exact (fp_pout _ _ _ P2)
        |rewrite Est2; dsr; exact (ig_ain s2 I2)|rewrite Est2; dsr; exact (ig_aout s2 I2)|rewrite (fp_optlen _ _ _ P2); lia|rewrite (fp_statlen _ _ _ P2); lia]. }
    pose proof (rel_set_block_start _ _ _ _ _ _ _ _ (ds_strstart s8) R8) as R9. rel_fields R8.
    pose proof (INVG_set_block_start s8 (ds_strstart s8) J1) as J1'. pose proof (INVG_set_block_start s8' (ds_strstart s8) J2) as J2'.
    set (u1 := set_block_start s8 (ds_strstart s8)) in *. set (u2 := set_block_start s8' (ds_strstart s8)) in *.
    pose proof (bi_flush_pending_le u1) as BFL0.
    pose proof (flush_pending_rel _ _ _ _ _ _ _ _ R9 J1' J2' ltac:(subst u1; dsr; lia) ltac:(revert BFL0; subst u1; dsr; rewrite (fp_pbl _ _ _ P1); intros; lia)
                  ltac:(subst u1; dsr; rewrite Hpo8; intros i Hi; unfold Bx; right; lia) ltac:(left; subst u1; dsr; exact Hpo8)) as (R10 & K1 & K2).
    clear BFL0.
    pose proof (flush_pending_shape u1 ltac:(subst u1; dsr; exact (ig_aout _ J1)) ltac:(subst u1; dsr; lia) ltac:(subst u1; dsr; lia)) as SH.
    cbv zeta in SH. destruct SH as (po & st & E & Ei & En & Ea & Eo & El & Hlen & Hpo & _).
    rewrite E in *.
    pose proof (bi_flush_pending_le u1) as BFL.
    pose proof (k_bi_flush lzv true true keeps_lzv eq_refl u1) as L3.
    pose proof (k_bi_flush ds_sym_next true false keeps_sym_next eq_refl u1) as SN3.
    set (s9 := bi_flush u1) in *. clearbody s9.
    set (t2 := flush_pending u2) in *. clearbody t2.
    assert (Eu : lzv u1 = lzv (set_block_start s1 (ds_strstart s1)) /\ ds_pending u1 = ds_pending s8 /\ ds_pending_out u1 = 0 /\ ds_sym_next u1 = 0 /\ cs_avail_out (ds_strm u1) = cs_avail_out (ds_strm s1) /\ cs_avail_in (ds_strm u1) = cs_avail_in (ds_strm s1)).
    { subst u1. dsr. rewrite Est1. dsr. split; [|repeat split; try assumption; reflexivity].
      pose proof (lzv_fields _ _ L1) as F. repeat match type of F with _ /\ _ => destruct F as [? F] end.
      unfold lzv. dsr. repeat match goal with H : ?f s8 = ?f s1 |- context [?f s8] => rewrite H end. reflexivity. }
    clearbody u1 u2. destruct Eu as (Lu & Epu & Epou & Esnu & Eaou & Eaiu).
    rewrite Epou in *. rewrite Esnu in SN3.
    assert (LL : lzm s9 = lzm (set_block_start s1 (ds_strstart s1))) by (apply lzm_of_lzv; rewrite L3; exact Lu).
    split; [|split; [exact K1|]; split; [exact K2|]].
    2:{ lzm_rw LL. split; [reflexivity|]. split; [exact SN3|]. split; [|rewrite Ea; exact Eaiu].
        rewrite Eo. destruct Hpo as [[A1 A2]|[[A1 [A2 A3]]|[A1 A2]]]; [left; exact A1|right; lia|].
        destruct (Z.eq_dec (ds_pending s9) 0); [left; lia|right; lia]. }
    exists W, C, (Bx (Bx B 0 (ds_pending s8)) (ds_pending u1) (ds_pending s9)), bnd, ms, pm. split; [exact R10|].
    unfold WHI, PBC, SYMB, HWI, Bx in *. lzm_rw LL.
    split; [exact HW|]. split; [exact Hb|]. split.
    { rewrite Eo. destruct Hpo as [[A1 A2]|[[A1 [A2 A3]]|[A1 A2]]].
      - left. split; [exact A2|intros; lia].
      - right. split; [lia|]. intros i Hi. rewrite Epu in *. destruct (Z_lt_le_dec i (ds_pending s8)); [left; right; lia|right; lia].
      - left. split; [exact A2|]. intros i Hi. rewrite Epu in *. destruct (Z_lt_le_dec i (ds_pending s8)); [left; right; lia|right; lia]. }
    split; [rewrite SN3; intros; lia|]. exact HH.
  Qed.

  Lemma flush_block_rel s1 s2 last :
    FREL s1 s2 -> INVG s1 -> INVG s2 -> fb_entry s1 last -> fb_entry s2 last -> ds_block_start s1 <= ds_strstart s1 ->
    snd (flush_block s1 last) = snd (flush_block s2 last)
    /\ fst (flush_block s1 last) = flush_block_only s1 last /\ fst (flush_block s2 last) = flush_block_only s2 last
    /\ (snd (flush_block s1 last) = None -> ds_pending (flush_block_only s1 last) = 0 /\ cs_avail_out (ds_strm (flush_block_only s1 last)) <> 0).
  Proof.
    intros FR I1 I2 FE1 FE2 Hbs.
    pose proof (flush_block_only_rel s1 s2 last FR I1 I2 FE1 FE2 Hbs) as (FR' & _ & _ & _ & _ & Hpo & _).
    rewrite !flush_block_eq'. cbn [fst snd]. rewrite <- (clean_eq_fieldT ds_strm _ _ (FREL_clean _ _ FR') ltac:(reflexivity)).
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_block_only s1 last))) 0); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]).
    - intros X; discriminate X.
    - intros _. split; [|assumption]. destruct Hpo; [assumption|contradiction].
  Qed.
End Flush.


Lemma st_tally_rel s1 s2 :
  FREL s1 s2 -> INVG s1 -> INVG s2 ->
  ds_level s1 <> 0 -> 1 <= ds_lookahead s1 -> 0 <= ds_sym_next s1 ->
  (MIN_MATCH <= ds_match_length s1 -> ds_match_length s1 <= ds_lookahead s1) -> ds_strstart s1 + MIN_LOOKAHEAD <= 65536 ->
  snd (st_tally s1) = snd (st_tally s2)
  /\ FREL (fst (st_tally s1)) (fst (st_tally s2)) /\ INVG (fst (st_tally s1)) /\ INVG (fst (st_tally s2)).
Proof.
  intros FR I1 I2 Hlv Hlk Hsn Hml Hss. pose proof FR as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
  unfold st_tally. rel_fields R.
  destruct (Z.leb_spec MIN_MATCH (ds_match_length s1)) as [M|M].
  - pose proof (st_dist_rel _ _ _ _ _ _ _ _ R I1 I2 HW Hb HP HS HH Hlv Hsn ltac:(split; [exact M|apply Hml; exact M]) Hss) as (E & FR' & J1 & J2 & _).
    split; [exact E|]. split; [exact FR'|]. split; assumption.
  - pose proof (st_lit_rel _ _ _ _ _ _ _ _ R I1 I2 HW Hb HP HS HH Hlk Hsn) as (E & FR' & J1 & J2 & _).
    split; [exact E|]. split; [exact FR'|]. split; assumption.
Qed.

Section FastRel.
  Variable c0 : cstrm.
Variable s01 : deflate_state.
Variable s02 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Hypothesis HFBR : FLUSH_BLOCK_REL.

  Lemma dmode3_level s : dmode s = 3 -> ds_level s <> 0.
  Proof. unfold dmode. destruct (Z.eqb_spec (ds_level s) 0); [intros X; discriminate X|intros _; assumption]. Qed.

  Lemma fast_step_rel s1 s2 :
    FTI c0 s01 s1 -> FTI c0 s02 s2 -> FREL s1 s2 -> INVG s1 -> INVG s2 ->
    snd (st_body s1 flush) = snd (st_body s2 flush)
    /\ FREL (fst (st_body s1 flush)) (fst (st_body s2 flush))
    /\ INVG (fst (st_body s1 flush)) /\ INVG (fst (st_body s2 flush)).
  Proof.
    intros F1 F2 FR I1 I2.
    pose proof F1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1). pose proof F2 as (HDC2 & HK2 & Hp2 & Hm2 & Hst2 & Ho2).
    pose proof (dmode3_level _ Hm1) as Hlv.
    unfold st_body.
    pose proof (st_fill_rel s1 s2 flush FR I1 I2 Hlv) as (Ee & FRa & Ia1 & Ia2 & _).
    pose proof (fill_stage c0 s01 flush HC0 s1 F1) as FS1. cbv zeta in FS1. destruct FS1 as (Fa1 & _ & _ & _ & _ & Ews1 & Hnone1 & _ & _ & Hss1 & _).
    pose proof (fill_stage c0 s02 flush HC0 s2 F2) as FS2. cbv zeta in FS2. destruct FS2 as (Fa2 & _ & _ & _ & _ & Ews2 & Hnone2 & _).
    rewrite (ig_wsize s1 I1) in Hss1.
    destruct (st_fill s1 flush) as [a1 e1]. destruct (st_fill s2 flush) as [a2 e2]. cbn [fst snd] in *. subst e2.
    destruct e1 as [o|].
    { cbn [fst snd]. split; [reflexivity|]. split; [exact FRa|]. split; assumption. }
    destruct (Hnone1 eq_refl) as [Hlk1 _]. destruct (Hnone2 eq_refl) as [Hlk2 _].
    pose proof (FTI_facts _ _ _ Fa1) as (Da1 & Xa1 & Va1 & _ & _ & _ & Hpl1 & Hml1 & _ & Hn1 & Hsn1 & _).
    assert (Hlva : ds_level a1 <> 0) by (apply dmode3_level; exact (proj1 (proj2 (proj2 (proj2 Fa1))))).
    pose proof (st_hash_rel a1 a2 FRa Ia1 Ia2) as (Eh & HFR & Ib1 & Ib2 & L5b & Kb & CLb).
    pose proof (hash_stage c0 s01 a1 Fa1 Hlk1) as HS1. cbv zeta in HS1. destruct HS1 as [HR1 Hlm1].
    pose proof (hash_stage c0 s02 a2 Fa2 Hlk2) as HS2. cbv zeta in HS2. destruct HS2 as [HR2 Hlm2].
    destruct (st_hash a1) as [b1 hh]. destruct (st_hash a2) as [b2 hh2]. cbn [fst snd] in *. subst hh2.
    pose proof (lz5_eq _ _ L5b) as (Ess_b & Elk_b & Ehw_b & Elv_b & Ebs_b).
    assert (Epl_b : ds_prev_length b1 = ds_prev_length a1) by (apply (f_equal ds_prev_length) in CLb; exact CLb).
    assert (Eml_b : ds_match_length b1 = ds_match_length a1) by (apply (f_equal ds_match_length) in CLb; exact CLb).
    pose proof (st_match_rel b1 b2 hh HFR Ib1 Ib2 ltac:(rewrite Elv_b; exact Hlva) ltac:(rewrite Elk_b; exact Hlk1)
                  ltac:(rewrite Ess_b; exact Hss1) ltac:(rewrite Epl_b, Hpl1; lia)) as (FRc & Ic1 & Ic2 & L5c & Kc & Hle & Hid).
    pose proof (match_stage c0 s01 a1 b1 hh Fa1 Hlk1 HR1 Hlm1) as MR1.
    pose proof (match_stage c0 s02 a2 b2 hh Fa2 Hlk2 HR2 Hlm2) as MR2.
    pose proof (lz5_eq _ _ L5c) as (Ess_c & Elk_c & Ehw_c & Elv_c & Ebs_c).
    assert (Hmlc : MIN_MATCH <= ds_match_length (st_match b1 hh) -> ds_match_length (st_match b1 hh) <= ds_lookahead (st_match b1 hh)).
    { intros M. rewrite Elk_c. destruct (lm_cond b1 hh) eqn:Elm; [exact (Hle eq_refl)|]. rewrite (Hid eq_refl) in M |- *. rewrite Eml_b in M. exfalso. lia. }
    set (d1 := st_match b1 hh) in *. set (d2 := st_match b2 hh) in *.
    pose proof (fwk_fields _ _ Kc) as (_ & _ & Esn_c & _). pose proof (fwk_fields _ _ Kb) as (_ & _ & Esn_b & _).
    pose proof (st_tally_rel d1 d2 FRc Ic1 Ic2 ltac:(rewrite Elv_c, Elv_b; exact Hlva) ltac:(rewrite Elk_c, Elk_b; exact Hlk1)
                  ltac:(rewrite Esn_c, Esn_b; lia) Hmlc ltac:(rewrite Ess_c, Ess_b; exact Hss1)) as (Eb & FRe & Ie1 & Ie2).
    pose proof (tally_stage c0 s01 a1 b1 d1 Fa1 Hlk1 HR1 MR1) as TS1. cbv zeta in TS1. destruct TS1 as [(adv1 & TR1 & Had1 & Had1' & Had1'' & _) _].
    pose proof (tally_stage c0 s02 a2 b2 d2 Fa2 Hlk2 HR2 MR2) as TS2. cbv zeta in TS2. destruct TS2 as [(adv2 & TR2 & Had2 & Had2' & Had2'' & _) _].
    destruct (st_tally d1) as [e1 bf]. destruct (st_tally d2) as [e2 bf2]. cbn [fst snd] in *. subst bf2.
    unfold st_bflush. destruct bf.
    2:{ cbn [fst snd]. split; [reflexivity|]. split; [exact FRe|]. split; assumption. }
    destruct (Hnone1 eq_refl) as [_ Hslack1]. destruct (Hnone2 eq_refl) as [_ Hslack2].
    pose proof (trip_end c0 s01 HC0 a1 b1 d1 e1 adv1 Fa1 Hlk1 ltac:(rewrite Ews1; exact Hslack1) HR1 MR1 TR1 ltac:(lia) Had1'') as TE1.
    pose proof (trip_end c0 s02 HC0 a2 b2 d2 e2 adv2 Fa2 Hlk2 ltac:(rewrite Ews2; exact Hslack2) HR2 MR2 TR2 ltac:(lia) Had2'') as TE2.
    destruct TE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FE1 & _).
    destruct TE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FE2 & _).
    pose proof (fe_diff _ _ FE1) as Hdiff.
    pose proof (flush_block_rel HFB HFBR e1 e2 0 FRe Ie1 Ie2 FE1 FE2 ltac:(lia)) as (Er & Ef1 & Ef2 & _).
    pose proof (flush_block_only_rel HFB HFBR e1 e2 0 FRe Ie1 Ie2 FE1 FE2 ltac:(lia)) as (FRf & If1 & If2 & _).
    destruct (flush_block e1 0) as [f1 r1]. destruct (flush_block e2 0) as [f2 r2]. cbn [fst snd] in *. subst r2 f1 f2.
    destruct r1; cbn [fst snd]; (split; [reflexivity|]); (split; [exact FRf|]); split; assumption.
  Qed.

  Lemma fast_loop_rel fuel : forall s1 s2,
    FTI c0 s01 s1 -> FTI c0 s02 s2 -> FREL s1 s2 -> INVG s1 -> INVG s2 -> lz_meas s1 < Z.of_nat fuel ->
    let r1 := deflate_fast_loop fuel s1 flush in let r2 := deflate_fast_loop fuel s2 flush in
    snd r1 = snd r2 /\ FREL (fst r1) (fst r2) /\ INVG (fst r1) /\ INVG (fst r2)
    /\ (snd r1 = None -> FTI c0 s01 (fst r1) /\ FTI c0 s02 (fst r2) /\ ds_lookahead (fst r1) = 0).
  Proof.
    induction fuel as [|f IH]; intros s1 s2 F1 F2 FR I1 I2 Hmz; cbn [deflate_fast_loop].
    { exfalso. pose proof (FTI_facts _ _ _ F1) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite (deflate_fast_body_eq s1 flush), (deflate_fast_body_eq s2 flush).
    pose proof (fast_step_rel s1 s2 F1 F2 FR I1 I2) as (Eo & FR' & I1' & I2').
    pose proof (fast_step c0 s01 flush HC0 HFB s1 F1) as [_ M1]. pose proof (fast_step c0 s02 flush HC0 HFB s2 F2) as [_ M2].
    destruct (st_body s1 flush) as [t1 o1]. destruct (st_body s2 flush) as [t2 o2]. cbn [fst snd] in *. subst o2.
    destruct o1 as [| |bs].
    - destruct M1 as [F1' Hm']. destruct M2 as [F2' _]. exact (IH t1 t2 F1' F2' FR' I1' I2' ltac:(lia)).
    - cbn [fst snd]. split; [reflexivity|]. split; [exact FR'|]. split; [exact I1'|]. split; [exact I2'|].
      intros _. split; [exact (proj1 M1)|]. split; [exact (proj1 M2)|exact (proj2 M1)].
    - cbn [fst snd]. split; [reflexivity|]. split; [exact FR'|]. split; [exact I1'|]. split; [exact I2'|]. intros X; discriminate X.
  Qed.

  Lemma FREL_set_insert s1 s2 v : FREL s1 s2 -> FREL (set_insert s1 v) (set_insert s2 v).
  Proof.
    intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
    split; [apply rel_set_insert; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
  Qed.

  Lemma deflate_fast_rel :
    let s1 := s01 in let s2 := s02 in
    FTI c0 s1 s1 -> FTI c0 s2 s2 -> FREL s1 s2 -> INVG s1 -> INVG s2 -> 0 <= flush <= 5 ->
    let r1 := deflate_fast s1 flush in let r2 := deflate_fast s2 flush in
    snd r1 = snd r2 /\ FREL (fst r1) (fst r2) /\ INVG (fst r1) /\ INVG (fst r2).
  Proof.
    cbv zeta. set (s1 := s01). set (s2 := s02). intros F1 F2 FR I1 I2 Hfl. unfold deflate_fast.
    pose proof (FREL_clean _ _ FR) as EC.
    assert (Efuel : lz_fuel s2 = lz_fuel s1).
    { unfold lz_fuel. rewrite <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_lookahead _ _ EC ltac:(reflexivity)). reflexivity. }
    rewrite Efuel.
    pose proof (FTI_facts _ _ _ F1) as (D1 & X1 & V1 & _). pose proof (FTI_facts _ _ _ F2) as (D2 & X2 & V2 & _).
    assert (Hmz : lz_meas s1 < Z.of_nat (lz_fuel s1)).
    { apply lz_fuel_meas. unfold lz_meas. pose proof (df_look _ D1). pose proof (sv_ain _ _ V1). lia. }
    pose proof (fast_loop_rel (lz_fuel s1) s1 s2 F1 F2 FR I1 I2 Hmz) as (Er & FRr & J1 & J2 & Hn).
    destruct (deflate_fast_loop _ s1 flush) as [t1 r1]. destruct (deflate_fast_loop _ s2 flush) as [t2 r2]. cbn [fst snd] in *. subst r2.
    destruct r1 as [bs|].
    { cbn [fst snd]. split; [reflexivity|]. split; [exact FRr|]. split; assumption. }
    destruct (Hn eq_refl) as (G1 & G2 & Hl0).
    pose proof (FTI_facts _ _ _ G1) as (Dt1 & Xt1 & Vt1 & Sw1 & _ & _ & _ & _ & _ & _ & _ & _ & Hss1 & _).
    pose proof (FTI_facts _ _ _ G2) as (Dt2 & Xt2 & Vt2 & Sw2 & _ & _ & _ & _ & _ & _ & _ & _ & Hss2 & _).
    pose proof G1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & _). pose proof G2 as (HDC2 & HK2 & Hp2 & Hm2 & Hst2 & _).
    pose proof (FREL_clean _ _ FRr) as ECt. rewrite <- (clean_eq_fieldT ds_strstart _ _ ECt ltac:(reflexivity)).
    set (v := if ds_strstart t1 <? MIN_MATCH - 1 then ds_strstart t1 else MIN_MATCH - 1).
    assert (Hv : 0 <= v <= ds_strstart t1 /\ v <= 2) by (subst v; unfold MIN_MATCH; destruct (Z.ltb_spec (ds_strstart t1) (3 - 1)); lia).
    pose proof (FREL_set_insert t1 t2 v FRr) as FRu.
    pose proof (INVG_set_insert t1 v ltac:(lia) J1) as K1.
    pose proof (INVG_set_insert t2 v ltac:(rewrite <- (clean_eq_fieldT ds_strstart _ _ ECt ltac:(reflexivity)); lia) J2) as K2.
    destruct (DD_set_insert t1 v Dt1 Xt1 ltac:(lia) ltac:(lia)) as [Du1 Xu1].
    destruct (DD_set_insert t2 v Dt2 Xt2 ltac:(rewrite <- (clean_eq_fieldT ds_strstart _ _ ECt ltac:(reflexivity)); lia) ltac:(lia)) as [Du2 Xu2].
    assert (DCu1 : DC c0 (set_insert t1 v)) by (split; [split; assumption|apply (SV_strm c0 t1); [reflexivity|exact Vt1]]).
    assert (DCu2 : DC c0 (set_insert t2 v)) by (split; [split; assumption|apply (SV_strm c0 t2); [reflexivity|exact Vt2]]).
    assert (FE : forall last, 0 <= last <= 1 -> fb_entry (set_insert t1 v) last /\ fb_entry (set_insert t2 v) last).
    { intros last Hl. split; (eapply DC_fb_entry; [exact (c0'_ok _ HC0)|eassumption|dsr; assumption|dsr; unfold dmode in *; dsr; congruence|exact Hl]). }
    set (u1 := set_insert t1 v) in *. set (u2 := set_insert t2 v) in *. clearbody u1 u2.
    unfold deflate_tail. pose proof (FREL_clean _ _ FRu) as ECu.
    destruct (Z.eqb_spec flush Z_FINISH).
    - destruct (FE 1 ltac:(lia)) as [FE1 FE2]. pose proof (fe_diff _ _ FE1).
      pose proof (flush_block_rel HFB HFBR u1 u2 1 FRu K1 K2 FE1 FE2 ltac:(lia)) as (Eb & Ef1 & Ef2 & _).
      pose proof (flush_block_only_rel HFB HFBR u1 u2 1 FRu K1 K2 FE1 FE2 ltac:(lia)) as (FRf & L1 & L2 & _).
      destruct (flush_block u1 1) as [f1 r1]. destruct (flush_block u2 1) as [f2 r2]. cbn [fst snd] in *. subst r2 f1 f2.
      destruct r1; cbn [fst snd]; (split; [reflexivity|]); (split; [exact FRf|]); split; assumption.
    - rewrite <- (clean_eq_fieldT ds_sym_next _ _ ECu ltac:(reflexivity)).
      destruct (Z.eqb_spec (ds_sym_next u1) 0); cbn [negb].
      + cbn [fst snd]. split; [reflexivity|]. split; [exact FRu|]. split; assumption.
      + destruct (FE 0 ltac:(lia)) as [FE1 FE2]. pose proof (fe_diff _ _ FE1).
        pose proof (flush_block_rel HFB HFBR u1 u2 0 FRu K1 K2 FE1 FE2 ltac:(lia)) as (Eb & Ef1 & Ef2 & _).
        pose proof (flush_block_only_rel HFB HFBR u1 u2 0 FRu K1 K2 FE1 FE2 ltac:(lia)) as (FRf & L1 & L2 & _).
        destruct (flush_block u1 0) as [f1 r1]. destruct (flush_block u2 0) as [f2 r2]. cbn [fst snd] in *. subst r2 f1 f2.
        destruct r1; cbn [fst snd]; (split; [reflexivity|]); (split; [exact FRf|]); split; assumption.
  Qed.
End FastRel.

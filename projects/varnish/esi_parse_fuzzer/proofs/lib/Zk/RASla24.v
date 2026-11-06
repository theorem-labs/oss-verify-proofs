(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I Malluin RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MTree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree.PortMisc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RF_muly.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_high_low x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
  intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [LT|GE].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_shl_small x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.
Lemma lor_small_shl x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.
(* [comment removed for export] *)
Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
  intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma hdr_byte_facts x ai : 0 <= x < 256 -> 0 <= ai < 32 ->
  0 <= Z.lor (Z.land x 18446744073709551584) ai < 256 /\ Z.land (Z.lor (Z.land x 18446744073709551584) ai) 31 = ai.
Proof.
  intros Hx Hai.
  assert (E : Z.land x 18446744073709551584 = Z.land x 224).
  { replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    rewrite <- !Z.land_assoc. reflexivity. }
  rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
  split.
  - change 256 with (2^8). apply lor_lt_pow2; lia.
  - rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
    change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
  intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
  replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Lemma cell_read_hdr_havoc_old : forall st b o,
  snd b mod 16 = 0 -> 0 <= o < 12 ->
  (forall v t, (r_cells (get_shadow st (fst b))) !! (snd b + o) = Some (v, t) -> (t < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id].
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  unfold hav_add. unfold stale. cbn [existsb fst snd].
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
  - specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
    cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
  - cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed.
Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof.
  intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
  rewrite (mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal. 
Qed.

(* [comment removed for export] *)
Lemma unsigned_mod32_swrap_add_not a b :
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
  pose proof (sxv_range b) as RB.
  rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
  replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia.
  unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
  assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
  clearbody x y. Z.div_mod_to_equations. nia.
Qed.
Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof.
  intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite <- !Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section TAIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition stA : mstate := hdr_havoc p stT.
Definition stB : mstate := set_usage sc (usage stT sc + cnt) stA.
Definition recA : meta := mkMeta None None (Some p) AV FR 0 0 0 ml.
Definition stC : mstate := put_meta mt recA stB.
Definition stD : mstate := put_group p (Some mt) ai stC.
Definition recF : meta := mkMeta (Some mt) (Some mt) (Some p) (AV - 1) FR (cnt - 1) 1 sc ml.
Definition stE : mstate := put_meta mt recF stD.
Definition stFin : mstate := set_active sc (Some mt) stE.
Definition st_model : mstate :=
  let st := hdr_havoc p stT in
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto ai in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta mt (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some mt) ai st2 in
  let st4 := add_slots mt p (get_stride (get_meta_rec st3 mt)) cnt st3 in
  let st5 := upd_meta mt (fun r => m_set_avail (m_avail r - 1) r) st4 in
  let st6 := upd_meta mt (fun r => m_set_prev (Some mt) (m_set_next (Some mt) r)) st5 in
  set_active sc (Some mt) st6.
#[using="P0 FR AV P G p mt ai cnt stT"] Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.
#[using="P0 AI CNT P G p mt stT"] Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
  pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (mask_upto ai <= mask_upto (cnt - 1)).
  { unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  unfold AV, FR. lia.
Qed.
Lemma rec_set_slots st v q : get_meta_rec (set_slots v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma rec_put_group st b g a q : get_meta_rec (put_group b g a st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma rec_hdr_havoc st b q : get_meta_rec (hdr_havoc b st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="P0 REC CNT SC P G"] Lemma st_model_eq_rec q : get_meta_rec st_model q = get_meta_rec stFin q.
Proof.
  unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
  rewrite !rec_set_active.
  destruct (decide (q = mt)) as [->|NE].
  - rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
    unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
    replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    change (Z.land 1 1) with 1. reflexivity.
  - rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.
(* [comment removed for export] *)
Definition tailW : list (Z * Z) :=
  [(CTX + 464 + 8 * sc, CTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z.

(* [comment removed for export] *)
#[using="TK ACT UR OLD12 NOGRP GNONE PEND P16 P0 Hk Hr REC MST ML AI CNT SC r"] Lemma tail_walk :
  forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
  mrep stT mC -> mem_inv rsegs mC ->
  evt rsegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
                   s2 s3 s4 (Z_to_bv 64 (CTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (MLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24524) fc None m' (seg_rom rsegs)
      /\ munch tailW mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
      /\ mrep stFin m' /\ ticks_ok stFin)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (CTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (MLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x243cc) fc None mC (seg_rom rsegs)).
Proof.
  intros until mC. intros MR MI.
  pose proof (munch_refl tailW mC) as MU. pose proof (wmono_refl rsegs mC) as WM. unfold tailW in MU.
  (first [ pose proof ((meta_slot_bounds stT mC mt MR MST)) as dR_1; dand5 dR_1 as Gpos GC GI G4 _ | pose proof (meta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _) ]). fold G in Gpos, GC, GI, G4.
  (first [ pose proof ((rregion_facts stT mC (fst p) r MR Hr)) as dR_2; dand5 dR_2 as R4 RAL RC RI1 RI2 | pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
  (first [ pose proof (AV_FR_range) as dR_3; dand3 dR_3 as AVR FRR AV1R | pose proof AV_FR_range as (AVR & FRR & AV1R) ]). fold AV in AVR, AV1R. fold AV FR in FRR.
  (* [comment removed for export] *)
  destruct (mrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold stA in MRA, TKA.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK in *.
  (* [comment removed for export] *)
  pose proof (mrep_usage_read stA mC sc (wa (402528 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
  change (usage stA sc) with (usage stT sc) in RDU.
  replace (wa (402528 + 464 + 8 * sc)) with (Z_to_bv 64 (402520 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
  step. clear RDU.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
  (* [comment removed for export] *)
  (first [ pose proof (MRA) as dR_4; dand3 dR_4 as _ (_ & _ & USG & _) _ | pose proof MRA as (_ & (_ & _ & USG & _) & _) ]).
  pose proof (u64arr_store_ok rsegs _ _ (usages stA) sc (wa (402528 + 464 + 8 * sc)) USG
                ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
  replace (wa (402528 + 464 + 8 * sc)) with (Z_to_bv 64 (402520 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_usage stA mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold CTX in MRB; fold stB in MRB end.
  raw_store_finish0 (402528 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
  assert (TKB : ticks_ok stB) by exact TKA.
  assert (MSTB : meta_slot stB mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRA TKA.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia. rewrite sllw2_word by lia.
  step.
  set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
  mchunk MRB MSTB CH. change (conc stB mt) with G in CH. change (get_meta_rec stB mt) with (get_meta_rec stT mt) in CH.
  rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
  replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
  meta_open G MUa WMa.
  (* [comment removed for export] *)
  step. step.
  assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
  { subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
  rewrite (sx32_congr v3 AV V3).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
  step. step.
  set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
  assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
  { subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
  (* [comment removed for export] *)
  step. step.
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRC : mrep stC mX);
    [ eapply mrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
      change (conc stB p) with P; unfold wz at 3 4;
      rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
      rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
      replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
    | clear MUa WMa; rename H into CH1 ] end.
  assert (TKC : ticks_ok stC) by (exact (ticks_ok_upd_meta stB mt (fun _ => recA) TKB)).
  assert (MSTC : meta_slot stC mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRB TKB MSTB.
  (* [comment removed for export] *)
  (first [ pose proof (MRC) as dR_5; dand6 dR_5 as WFC _ _ _ _ SHC | pose proof MRC as (WFC & _ & _ & _ & _ & SHC) ]). (first [ pose proof (WFC) as dR_6; dand5 dR_6 as _ _ DJ _ WG | pose proof WFC as (_ & _ & DJ & _ & WG) ]).
  destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    (first [ pose proof ((wr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as hb; destruct dR_7 as [LHB HB] | pose proof ((wr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia))) as dR_7; dand3 dR_7 as hb LHB HB | destruct (wr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) ]) end.
  destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HDR : rw_cells rsegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
    [ apply rw_cells_of_bytes; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
    | clear HB LHB ] end.
  (first [ pose proof ((meta_chunk_facts stC _ mt MRC MSTC)) as dR_8; dand7 dR_8 as _ _ _ _ _ GRG _ | pose proof (meta_chunk_facts stC _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _) ]).
  pose proof (GRG (fst p) r Hr Hk) as GX. change (conc stC mt) with G in GX. clear GRG.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step.
  pose proof (byte_range y8) as Y8.
  step. unfold zxb.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia.
  replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
  step.
  pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
  rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
  rewrite (land224_m32 (bv_unsigned y8)) by lia.
  pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
  (* [comment removed for export] *)
  set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
  step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    rename H into HDR2;
    assert (MRC2 : mrep stC mX);
    [ eapply (mrep_transport_unowned _ _ _ _ MRC MUb WMb)
    | assert (MRD : mrep stD mX);
      [ eapply (mrep_put_group_new stC mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
        [ change (conc stC p) with P; unfold pw, wz; cbn [oconc]; change (conc stC mt) with G; exact HDR2
        | rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
      | ] ] end.
  { (* [comment removed for export] *)
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
    destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
    - unfold CTX in X1. lia.
    - unfold MLOCK in X2. lia.
    - unfold NEED_LOCKS in X3. lia.
    - unfold PAGE_SIZE_A in X4. lia.
    - change (s_areas stC) with (s_areas stT) in Hak. change (conc stC ak) with (conc stT ak) in Rak.
      (first [ pose proof ((area_conc stT ak ar WFC Hak)) as dR_9; dex1 dR_9 as rga; dand7 dR_9 as Hra Ca Sa0 Sa1 _ NK _ | pose proof ((area_conc stT ak ar WFC Hak)) as dR_9; dand8 dR_9 as rga Hra Ca Sa0 Sa1 _ NK _ | destruct (area_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _) ]).
      assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
      pose proof (area_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
    - change (s_groups stC) with (s_groups stT) in Hb. change (conc stC b) with (conc stT b) in Rb.
      (first [ pose proof ((group_conc stT b gh WFC Hb)) as dR_10; dex1 dR_10 as rb; dand6 dR_10 as Hrb Cb Kb Sb0 Sb1 _ | pose proof ((group_conc stT b gh WFC Hb)) as dR_10; dand7 dR_10 as rb Hrb Cb Kb Sb0 Sb1 _ | destruct (group_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ]).
      destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
      + rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
      + pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
    - change (s_regions stC) with (s_regions stT) in Hq. change (get_shadow stC q) with (get_shadow (hdr_havoc p stT) q) in Cq.
      destruct (N.eq_dec q (fst p)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
                    ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
    - unfold GOT_SSP in X5. lia.
    - unfold SSP_GUARD in X6. lia. }
  clear MRC MRC2 MUb WMb HDR2.
  assert (TKD : ticks_ok stD) by exact TKC.
  assert (MSTD : meta_slot stD mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear TKC MSTC.
  (* [comment removed for export] *)
  (first [ pose proof (MRD) as dR_11; dand3 dR_11 as _ (_ & ACTS & _) _ | pose proof MRD as (_ & (_ & ACTS & _) & _) ]). pose proof (actives_length stD) as LACT. unfold CTX in ACTS.
  mchunk MRD MSTD CH.
  change (get_meta_rec stD mt) with (get_meta_rec (put_meta mt recA stB) mt) in CH. rewrite get_meta_rec_put_same in CH.
  unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
  change (conc stD mt) with G in CH. change (conc stD p) with P in CH. unfold wz in CH.
  set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
  meta_open G MUc WMc.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
  replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit W), EW, land_pg_mask by lia.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
  replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. step. step. step.
  rewrite ?(unsigned_lit (mask_upto ai)) by lia.
  (* [comment removed for export] *)
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  lazymatch goal with H : u64arr rsegs ?mX _ (actives stD) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read rsegs mX (402528 + 80) (actives stD) sc (pw stD (active stD sc)) (wa (402528 + 80 + 8 * sc)) H
                  (actives_nth stD sc SC) ltac:(lia) eq_refl) as RDA end.
  change (active stD sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
  replace (wa (402528 + 80 + 8 * sc)) with (Z_to_bv 64 (402608 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRE : mrep stE mX);
    [ eapply mrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
      eapply rw_cells_congr; [| | | exact H]
    | clear MUc WMc; rename H into CH3 ] end.
  { unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
    change (conc stD mt) with G. change (conc stD p) with P.
    unfold wz. rewrite !app_nil_r.
    rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
    2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
        fold AV. Z.div_mod_to_equations. lia. }
    do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
  { reflexivity. }
  { cbn. tauto. }
  assert (TKE : ticks_ok stE) by (exact (ticks_ok_upd_meta stD mt (fun _ => recF) TKD)).
  clear MRD TKD MSTD.
  (* [comment removed for export] *)
  clear CH3.
  lazymatch goal with H : u64arr rsegs ?mX _ (actives stD) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_store_ok rsegs _ _ (actives stD) sc (wa (402528 + 80 + 8 * sc)) H
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
  replace (wa (402528 + 80 + 8 * sc)) with (Z_to_bv 64 (402608 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
  st1.
  replace (Z_to_bv 64 (402608 + 8 * sc + 0)) with (Z_to_bv 64 (402608 + 8 * sc)) in SOK by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_active stE mX sc (Some mt) MRE SC) as MRF; unfold CTX in MRF; fold stFin in MRF end.
  unfold pw in MRF. cbn [oconc] in MRF. change (conc stE mt) with G in MRF.
  raw_store_finish0 (402528 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MRF| exact TKE].
Qed.
End TAIL.
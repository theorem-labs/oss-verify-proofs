(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma land_high_low x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n k) as [LT|GE].
- Local Ltac2 Set LiaHints.tbl := fun () => "0040>22555333611.1158285538305.1061382040793.116944168077.11 00000700;00?00CS2Hy2NZS2LTS2GES2Hy".
rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lor_shl_small x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.
#[using="Type"] Lemma lor_small_shl x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.
#[using="Type"] Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
intros Hq. Local Ltac2 Set LiaHints.tbl := fun () => "0040=13243987229.317210505389.345081156397.359206986038.3000004005006007S2HqSSS".
replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hdr_byte_facts x ai : 0 <= x < 256 -> 0 <= ai < 32 ->
0 <= Z.lor (Z.land x 18446744073709551584) ai < 256 /\ Z.land (Z.lor (Z.land x 18446744073709551584) ai) 31 = ai.
Proof.
intros Hx Hai.
assert (E : Z.land x 18446744073709551584 = Z.land x 224).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0080=24997267206.725793536646.726800064025.629311285958.744738322902.756087464873.663370424053.567153861609.500000500;00<00=00B00F00G00KS3HaiS2Hx1HSSS3HaiS2HxSS2Hx".
replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- !Z.land_assoc. reflexivity. }
rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
split.
- change 256 with (2^8). apply lor_lt_pow2; lia.
- rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
intros Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0040=10351595562.310709356901.363045839500.36755912037.3 00000400500900:S2HiSS2HiS".
rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cell_read_hdr_havoc_old : forall st b o,
snd b mod 16 = 0 -> 0 <= o < 12 ->
(forall v t, (r_cells (get_shadow st (fst b))) !! (snd b + o) = Some (v, t) -> (t < s_tick st)%N) ->
exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id].
unfold cell_read. cbn [r_cells r_hav r_havp].
Local Ltac2 Set LiaHints.tbl := fun () => "0030>28681479561.2140979608525.7 41128464653.2100000@00D00TS3B162Ho1H2H02H4S2HoS3B162Ho1H2H42H5".
replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
rewrite lookup_insert_eq. cbn [default from_option id].
replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
unfold hav_add. unfold stale. cbn [existsb fst snd].
replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
- specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
- cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section TAIL.
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
#[using="stT cnt ai mt p G P AV FR P0"] Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
intros Hkk. unfold mask_upto. Local Ltac2 Set LiaHints.tbl := fun () => "0060>25671427541.333482648185.34 41418083475.3241422282358.3351792502754.326753815139.32 00000500;00<00=00B00CS3HkkS1H2H0SSS3HkkS".
rewrite Z.pow_add_r by lia. change (2^1) with 2.
assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
change (2^32) with (2 * 2^31). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="stT mt p G P CNT AI P0"] Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>15790603493.3241416074060.3443223934777.3553949108762.3058878855052.3400000500600?00G00KS3CNTSS2A12C11HS3CNT2AIS2AI".
pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
assert (mask_upto ai <= mask_upto (cnt - 1)).
{ unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
unfold AV, FR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rec_set_slots st v q : get_meta_rec (set_slots v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_put_group st b g a q : get_meta_rec (put_group b g a st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_hdr_havoc st b q : get_meta_rec (hdr_havoc b st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="G P SC CNT REC P0"] Lemma st_model_eq_rec q : get_meta_rec st_model q = get_meta_rec stFin q.
Proof.
unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
rewrite !rec_set_active.
destruct (decide (q = mt)) as [->|NE].
- rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
Local Ltac2 Set LiaHints.tbl := fun () => "0040>18042335451.3029317249091.3057862664595.3063966968627.3000000400500:00;S2SCSS3CNTS".
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
change (Z.land 1 1) with 1. reflexivity.
- rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End TAIL.
End CANSEC1.

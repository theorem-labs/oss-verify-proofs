(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2 F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_W14 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "Stdlib.NArith.BinNat.N.lt"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.hdr_havoc"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.Malloc.set_usage"; "OSSVerify.KrLib.Heap.Malloc.usage"; "OSSVerify.KrLib.Heap.Malloc.mask_upto"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.upd_meta"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.m_set_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.m_set_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_set_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_set_mem"; "OSSVerify.KrLib.Heap.Malloc.m_set_freed"; "OSSVerify.KrLib.Heap.Malloc.m_set_avail"; "OSSVerify.KrLib.Heap.Malloc.put_group"; "OSSVerify.KrLib.Heap.Malloc.add_slots"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_set_prev"; "OSSVerify.KrLib.Heap.Malloc.m_set_next"; "OSSVerify.KrLib.Heap.Malloc.set_active"].


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


Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
  intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hdr_byte_facts x ai : ltac2:(CDefT.buildp (gd_tbl_ASlot_W14 ()) "P,(0.(1.=O2.)(2.O2.+100.))P,(0.(1.=O1.)(2.O1.+20.))(0.(0.(1.=(3.(4.O2.+??????????????>0.)O1.))(2.(3.(4.O2.+??????????????>0.)O1.)+100.))(5.$6.(4.(3.(4.O2.+??????????????>0.)O1.)+1?.)O1.))")
(* [comment removed for export] *).
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
Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
  intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
  replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_old : ltac2:(CDefT.buildp (gd_tbl_ASlot_W14 ()) "Pst,$7.Pb,(8.$9.$6.)Po,$6.P,(5.$6.(:.(;.$9.$6.R2.)+10.)=)P,(0.(1.=R2.)(2.R2.+<.))P,Pv,$6.Pt,$9.P,(5.(<.(8.$6.$9.))(=.$6.(8.$6.$9.)(>.$6.$?.$10.(8.$6.$9.))(11.$6.$?.$10.(8.$6.$9.))(12.(;.$9.$6.R6.)R5.)(13.(14.R7.(15.$9.$6.R6.))))(16.(8.$6.$9.)(17.$6.$9.R2.R1.)))(18.R2.(19.R8.))(1:.$6.Lh,$6.(5.$1;.(1<.(14.(1=.R6.R7.)(15.$9.$6.R6.))(12.(;.$9.$6.R6.)R5.))(1>.R1.)))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis NOGRP : ltac2:(CDefT.buildp (gd_tbl_ASlot_W14 ()) "Pb',(8.$9.$6.)Pgh,$1?.P,(5.(<.$1?.)(=.(8.$9.$6.)$1?.(>.$20.(21.$9.$22.$6.$?.)(23.$9.$22.$24.$6.$?.$10.)$1?.)(11.$20.(21.$9.$22.$6.$?.)(23.$9.$22.$24.$6.$?.$10.)$1?.)R2.(25.VstT,))(16.$1?.R1.))P,(5.$9.(15.$9.$6.R3.)(15.$9.$6.Vp,))(26.(1.(12.(;.$9.$6.R4.)+9.)(;.$9.$6.Vp,))(1.(12.(;.$9.$6.Vp,)+9.)(;.$9.$6.R4.)))")
(* [comment removed for export] *).
Hypothesis OLD12 : ltac2:(CDefT.buildp (gd_tbl_ASlot_W14 ()) "Po,$6.Pv,$6.Pt,$9.P,(0.(1.(;.$9.$6.Vp,)R3.)(2.R3.(12.(;.$9.$6.Vp,)+<.)))P,(5.(<.(8.$6.$9.))(=.$6.(8.$6.$9.)(>.$6.$?.$10.(8.$6.$9.))(11.$6.$?.$10.(8.$6.$9.))R4.(13.(14.VstT,(15.$9.$6.Vp,))))(16.(8.$6.$9.)(17.$6.$9.R3.R2.)))(18.R3.(19.VstT,))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
Definition st_model : mstate := ltac2:(CDefT.buildp (gd_tbl_ASlot_W14 ()) "Zst,$7.(1=.Vp,VstT,)Zst1,$7.(27.Vsc,(12.(28.R1.Vsc,)Vcnt,)R1.)Zavail,$6.(29.Vai,)Zfreed,$6.(2:.(29.(2:.Vcnt,+1.))R1.)Zst2,$7.(2;.Vmt,Lr,$2<.(2=.Vsc,(2>.+1.(2?.(2:.Vcnt,+1.)(30.(16.$20.Vp,)(31.R2.(32.R3.R1.))))))R3.)Zst3,$7.(33.Vp,(16.$20.Vmt,)Vai,R1.)Zst4,$7.(34.Vmt,Vp,(35.(36.R1.Vmt,))Vcnt,R1.)Zst5,$7.(2;.Vmt,Lr,$2<.(32.(2:.(37.R1.)+1.)R1.)R1.)Zst6,$7.(2;.Vmt,Lr,$2<.(38.(16.$20.Vmt,)(39.(16.$20.Vmt,)R1.))R1.)(3:.Vsc,(16.$20.Vmt,)R1.)")
(* [comment removed for export] *).

#[using="stT cnt ai mt p G P AV FR P0"] Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

#[using="stT mt p G P CNT AI P0"] Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
  pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (mask_upto ai <= mask_upto (cnt - 1)).
  { unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  unfold AV, FR. lia.
Qed.

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
    replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    change (Z.land 1 1) with 1. reflexivity.
  - rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.


End TAIL.

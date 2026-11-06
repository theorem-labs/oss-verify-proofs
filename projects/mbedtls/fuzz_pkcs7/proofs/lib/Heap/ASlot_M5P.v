(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A3 ASlot_W9 ASlot_W13 ASlot_W14 ASlot_M4P.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_M5P () : Init.string Init.list := ["Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.snd"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc.wr8"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.r_hav"; "OSSVerify.KrLib.Heap.Malloc.r_havp"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.zero_hdrs"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.countable.prod_countable"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.area"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.s_ctx"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc.Known"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Stdlib.Lists.List.existsb"; "stdpp.base.filter"; "stdpp.list_basics.list.list_filter"; "Stdlib.Bool.Bool.Is_true"; "Stdlib.ZArith.BinInt.Z.ltb"; "stdpp.decidable.Is_true_dec"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Heap.Malloc.hdr_havoc"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.Heap.Malloc.put_meta"; "OSSVerify.KrLib.Heap.Malloc.m_set_maplen"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.ASlot_W13.enf0_st"; "Corelib.Init.Datatypes.Some"; "Stdlib.NArith.BinNat.N.lt"; "NEST.nt_stW"; "NEST.nt_stT"; "NEST.nt_written"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "OSSVerify.KrLib.Heap.Malloc.mkMeta"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.F_malloc_enframe.rdv"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.MallocTree.pans_mem"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "OSSVerify.KrLib.Heap.Malloc_fp.grp_hdr_cov"; "Corelib.Init.Logic.ex"].



Lemma cells_wr8_other st q v o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(1.$2.O1.(3.$4.$2.O3.)))(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.(>.O3.O2.O4.)(?.$4.$2.O3.))))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.O4.(?.$4.$2.O3.)))))")
(* [comment removed for export] *).
Proof. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.


Lemma hav_wr8 st q v : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.(8.$2.$9.$:.(11.(6.$2.$4.)))(12.(=.(>.O2.O1.O3.)(?.$4.$2.O2.)))(12.(=.O3.(?.$4.$2.O2.))))(1.(8.$2.$9.$:.$4.)(13.(=.(>.O2.O1.O3.)(?.$4.$2.O2.)))(13.(=.O3.(?.$4.$2.O2.)))))")
(* [comment removed for export] *).
Proof. rewrite get_shadow_wr8_same. split; reflexivity. Qed.

Lemma cells_wr8_other' st rid off v o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(1.$2.O1.O3.))(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.(>.(14.$4.$2.O4.O3.)O2.O5.)O4.)))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.O5.O4.))))")
(* [comment removed for export] *).
Proof. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.

Lemma hav_wr8_any st q v rid : r_hav (get_shadow (wr8 q v st) rid) = r_hav (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma havp_wr8_any st q v rid : r_havp (get_shadow (wr8 q v st) rid) = r_havp (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma shadow_put_meta st m r rid : get_shadow (put_meta m r st) rid = get_shadow st rid.
Proof. reflexivity. Qed.

Lemma cell_read_wr8_other' st rid off v o : o <> off ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.

Lemma cell_read_wr8_same' st rid off v : ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known v.
Proof. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.

Lemma cell_read_wr8_same_land st rid off v : ticks_ok st ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known (Z.land v 255).
Proof.
  intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
  - apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.

Lemma ticks_ok_same2 st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.

Section ZH.
Variables (p : aptr) (s : Z).

#[using="Type"] Lemma zh_proj : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "Pk,$15.Pi,$2.Pst,$16.Zst',$16.(17.Vp,Vs,R2.R3.R1.)(10.(1.(8.$4.$18.$19.$1:.)(1;.R1.)(1;.R2.))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)(20.R1.)(20.R2.))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$21.)(22.R1.)(22.R2.))(10.(1.$4.(23.R1.)(23.R2.))(10.(1.$4.(24.R1.)(24.R2.))(10.(1.(11.(6.$2.$2.))(25.R1.)(25.R2.))(10.(1.$26.(27.R1.)(27.R2.))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)(6.$1<.$2.))(28.R1.)(28.R2.))(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$29.)(2:.R1.)(2:.R2.))))))))))")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [repeat split; reflexivity|].
  ddestruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma zh_shadow_other q : q <> fst p -> forall k i st, get_shadow (zero_hdrs p s i k st) q = get_shadow st q.
Proof.
  intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.

#[using="Type"] Lemma zh_hav : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "Pk,$15.Pi,$2.Pst,$16.(10.(1.(8.$2.$9.$:.(11.(6.$2.$4.)))(12.(=.(17.Vp,Vs,R2.R3.R1.)(?.$4.$2.Vp,)))(12.(=.R1.(?.$4.$2.Vp,))))(1.(8.$2.$9.$:.$4.)(13.(=.(17.Vp,Vs,R2.R3.R1.)(?.$4.$2.Vp,)))(13.(=.R1.(?.$4.$2.Vp,)))))")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
  pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.

#[using="Type"] Lemma zh_cells_other o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "Pk,$15.Pi,$2.Pst,$16.P,Pj,$2.P,(10.(2;.R3.R1.)(2<.R1.(2=.R3.(2>.R4.))))(0.(1.$2.O1.(2?.(2=.(2=.(3.$4.$2.Vp,)$30.)(31.R2.Vs,))+4.)))(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.(17.Vp,Vs,R3.R4.R2.)(?.$4.$2.Vp,))))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.R2.(?.$4.$2.Vp,)))))")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH by (intros j Hj; apply Ho; lia).
  pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.


#[using="Type"] Lemma zh_cell_read_other o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "Pk,$15.Pi,$2.Pst,$16.P,Pj,$2.P,(10.(2;.R3.R1.)(2<.R1.(2=.R3.(2>.R4.))))(0.(1.$2.O1.(2?.(2=.(2=.(3.$4.$2.Vp,)$30.)(31.R2.Vs,))+4.)))(1.$32.(33.(=.(17.Vp,Vs,R3.R4.R2.)(?.$4.$2.Vp,))O1.)(33.(=.R2.(?.$4.$2.Vp,))O1.))")
(* [comment removed for export] *).
Proof.
  intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
  destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.


#[using="Type"] Lemma zh_cell_read_at : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(2<.=Vs,)Pk,$15.Pi,$2.Pst,$16.Pj,$2.P,(34.R2.)P,(10.(2;.R4.R2.)(2<.R2.(2=.R4.(2>.R5.))))(1.$32.(33.(=.(17.Vp,Vs,R5.R6.R4.)(?.$4.$2.Vp,))(2?.(2=.(2=.(3.$4.$2.Vp,)$30.)(31.R3.Vs,))+4.))(35.=))")
(* [comment removed for export] *).
Proof.
  intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cell_read_other by (intros j' Hj'; nia).
    pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
  - apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.

(* [comment removed for export] *)
Lemma existsb_filter_gt12 (l : list (Z * N)) (f : Z * N -> bool) : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,Pch,(6.$2.$4.)P,(1.$36.A1.O1.R1.$37.)(2<.+<.(?.$2.$4.R2.))(1.$36.(38.(6.$2.$4.)O1.(39.(6.$2.$4.)(11.(6.$2.$4.))(3:.(6.$2.$4.))Lch,(6.$2.$4.)(3;.(3<.+<.(?.$2.$4.R1.)))Lx,(6.$2.$4.)(3=.(3<.+<.(?.$2.$4.R1.)))O2.))(38.(6.$2.$4.)O1.O2.))")
(* [comment removed for export] *).
Proof.
  intros Hf. induction l as [|ch l IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
  destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.

Lemma stale_hav_add_ge hl bb T t : 12 <= bb -> stale (hav_add 12 T hl) bb t = stale hl bb t.
Proof.
  intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
  replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
  apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.

Lemma cell_read_hdr_havoc_other st b o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(1.$2.(3>.(3.$4.$2.O2.)+10.)=)P,(0.(10.(2;.(3.$4.$2.O2.)O1.)(2<.O1.(2=.(3.$4.$2.O2.)+<.))))(1.$32.(33.(=.(3?.O2.O3.)(?.$4.$2.O2.))O1.)(33.(=.O3.(?.$4.$2.O2.))O1.))")
(* [comment removed for export] *).
Proof.
  intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id].
    assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
    fold (get_shadow st (fst b)).
    destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma hav_hdr_havoc_other st b u : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(1.$2.O1.(40.(3.$4.$2.O2.)+10.)))(1.(5.(11.(6.$2.$4.)))(7.$2.(11.(6.$2.$4.))(8.$2.$9.$:.(11.(6.$2.$4.)))(;.$2.$9.$:.(11.(6.$2.$4.)))O1.(12.(=.(3?.O2.O3.)(?.$4.$2.O2.))))(7.$2.(11.(6.$2.$4.))(8.$2.$9.$:.(11.(6.$2.$4.)))(;.$2.$9.$:.(11.(6.$2.$4.)))O1.(12.(=.O3.(?.$4.$2.O2.)))))")
(* [comment removed for export] *).
Proof.
  intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cells_hdr_havoc st b : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.(8.$2.$9.$:.(6.$2.$4.))(<.(=.(3?.O1.O2.)(?.$4.$2.O1.)))(<.(=.O2.(?.$4.$2.O1.))))(1.(8.$2.$9.$:.$4.)(13.(=.(3?.O1.O2.)(?.$4.$2.O1.)))(13.(=.O2.(?.$4.$2.O1.)))))")
(* [comment removed for export] *).
Proof.
  unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section NEST.
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.

Definition nt_stW : mstate := ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(>.(14.$4.$2.(?.$4.$2.Vb,)(2=.(2=.(3.$4.$2.Vb,)(2=.+10.(31.Vstrideg,Vidx,)))-3.))(41.(42.Vidx,+1?.)+<0.)(43.Vmm,(44.=(45.Vst3,Vmm,))(46.Vst3,Vg,Vb,Vidx,)))")
(* [comment removed for export] *).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.

Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "Po,$2.Pv,$2.Pt,$4.P,(10.(2;.VX,R3.)(2<.R3.(2?.(2=.VX,Vstrideg,)+4.)))P,(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))R4.(<.(=.Vst3,(?.$4.$2.Vb,))))(47.(6.$2.$4.)(14.$2.$4.R3.R2.)))(48.R3.(23.Vst3,))")
(* [comment removed for export] *).


#[using="SC"] Lemma szc_range : 1 <= szc <= 8191.
Proof. unfold szc. apply size_class_range. exact SC. Qed.

#[using="r N SO STR"] Lemma nest_model_eq :
  upd_meta mm (m_set_maplen 0) (nest_layout st3 g idx jn (UNIT * size_class sc) cnt) = nt_stT.
Proof.
  unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
  rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
  unfold upd_meta. rewrite rec_zero_hdrs.
  change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
  rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
  unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ntW_proj : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.(8.$4.$18.$19.$1:.)(1;.$49.)(1;.Vst3,))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)(20.$49.)(20.Vst3,))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$21.)(22.$49.)(22.Vst3,))(10.(1.$4.(23.$49.)(23.Vst3,))(10.(1.$4.(24.$49.)(24.Vst3,))(10.(1.(11.(6.$2.$2.))(25.$49.)(25.Vst3,))(10.(1.$26.(27.$49.)(27.Vst3,))(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)(6.$1<.$2.))(28.$49.)(28.Vst3,)))))))))")
(* [comment removed for export] *).
Proof. repeat split; reflexivity. Qed.

#[using="Type"] Lemma ntT_proj : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.(8.$4.$18.$19.$1:.)(1;.$4:.)(1;.Vst3,))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)(20.$4:.)(20.Vst3,))(10.(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$21.)(22.$4:.)(22.Vst3,))(10.(1.$4.(23.$4:.)(23.Vst3,))(10.(1.$4.(24.$4:.)(24.Vst3,))(10.(1.(11.(6.$2.$2.))(25.$4:.)(25.Vst3,))(10.(1.$26.(27.$4:.)(27.Vst3,))(1.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)(6.$1<.$2.))(28.$4:.)(28.Vst3,)))))))))")
(* [comment removed for export] *).
Proof.
  unfold nt_stT. ddestruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.

#[using="G0"] Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
  unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
  change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
    with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
  destruct (decide (q = mm)) as [->|NE].
  - rewrite get_meta_rec_put_same, G0. reflexivity.
  - rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma ntT_active c : active nt_stT c = active st3 c.
Proof. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

#[using="Type"] Lemma ntT_usage i : usage nt_stT i = usage st3 i.
Proof. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

#[using="Type"] Lemma ntT_ctx : ctx nt_stT = ctx st3.
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.

#[using="Type"] Lemma ntT_conc q : conc nt_stT q = conc st3 q.
Proof. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.

#[using="Type"] Lemma ntT_shadow_other q : q <> fst b -> get_shadow nt_stT q = get_shadow st3 q.
Proof.
  intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
  rewrite get_shadow_wr8_other by exact NE.
  change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
  unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma ntW_hav : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.(8.$2.$9.$:.(11.(6.$2.$4.)))(12.(=.$49.(?.$4.$2.Vb,)))(12.(=.Vst3,(?.$4.$2.Vb,))))(1.(8.$2.$9.$:.$4.)(13.(=.$49.(?.$4.$2.Vb,)))(13.(=.Vst3,(?.$4.$2.Vb,)))))")
(* [comment removed for export] *).
Proof.
  unfold nt_stW, enf0_st, wr16.
  split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.

#[using="Type"] Lemma ntT_hav : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.(8.$2.$9.$:.(11.(6.$2.$4.)))(12.(=.$4:.(?.$4.$2.Vb,)))(12.(=.Vst3,(?.$4.$2.Vb,))))(1.(8.$2.$9.$:.$4.)(13.(=.$4:.(?.$4.$2.Vb,)))(13.(=.Vst3,(?.$4.$2.Vb,)))))")
(* [comment removed for export] *).
Proof.
  unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
  rewrite A, B. exact ntW_hav.
Qed.

(* [comment removed for export] *)
Definition nt_written (o : Z) : Prop :=
  o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).

#[using="jn sc szc N SC J"] Lemma ntW_cells_other o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(1.$2.O1.(2?.VX,+3.)))P,(0.(1.$2.O1.(2?.VX,+2.)))P,(0.(1.$2.O1.(2?.VX,+1.)))(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.$49.(?.$4.$2.Vb,))))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.Vst3,(?.$4.$2.Vb,)))))")
(* [comment removed for export] *).
Proof.
  intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite !cells_wr8_other' by lia. reflexivity.
Qed.

#[using="jn sc szc N SC J"] Lemma ntW_cell_read_other o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(1.$2.O1.(2?.VX,+3.)))P,(0.(1.$2.O1.(2?.VX,+2.)))P,(0.(1.$2.O1.(2?.VX,+1.)))(1.$32.(33.(=.$49.(?.$4.$2.Vb,))O1.)(33.(=.Vst3,(?.$4.$2.Vb,))O1.))")
(* [comment removed for export] *).
Proof.
  intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="jn N SC J CNT"] Lemma ntT_cells_other o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(4;.O1.))(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.$4:.(?.$4.$2.Vb,))))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.Vst3,(?.$4.$2.Vb,)))))")
(* [comment removed for export] *).
Proof.
  intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
  rewrite zh_cells_other.
  2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
  unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.

#[using="jn N SC J CNT"] Lemma ntT_cell_read_other o : ~ nt_written o ->
  cell_read (get_shadow nt_stT (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="TK3"] Lemma ntW_ticks_ok : ticks_ok nt_stW.
Proof.
  unfold nt_stW. apply ticks_ok_wr8.
  assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
  eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.

#[using="jn N SC J CNT TK3"] Lemma ntT_cell_read_zero j : 0 <= j <= cnt ->
  cell_read (get_shadow nt_stT (fst b)) (X + 12 + j * (16 * szc)) = Known 0.
Proof.
  intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
  apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.

#[using="jn N SC J CNT TK3"] Lemma ntT_cell_read_hdr k : 1 <= k <= 3 -> exists v, cell_read (get_shadow nt_stT (fst b)) (X - k) = Known v.
Proof.
  intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
  unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
  assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
                          (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
  assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
  assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
  assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
  destruct (Z.eq_dec k 3) as [->|N3].
  { eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
  rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite 2 cell_read_wr8_other' by lia.
  destruct (Z.eq_dec k 1) as [->|N1].
  { eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
  assert (k = 2) by lia. subst k.
  rewrite cell_read_wr8_other' by lia.
  eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="jn sc szc N SC J SO"] Lemma slot_geom : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(1.$4<.(4=.(45.Vst3,Vg,))(47.$1<.Vb,))(10.(1.(5.$1:.)(7.$4.$1:.(8.$4.$18.$19.$1:.)(;.$4.$18.$19.$1:.)(?.$4.$2.Vb,)(1;.Vst3,))(47.$1:.Vr,))(10.(1.$4>.(4?.Vr,)$50.)(10.(2;.=(3.$4.$2.Vb,))(10.(1.$2.(3>.(3.$4.$2.Vb,)+10.)=)(10.(2;.=Vidx,)(10.(2;.+10.Vstrideg,)(10.(1.$2.(3>.Vstrideg,+10.)=)(10.(2;.(2=.VX,Vstrideg,)(51.(52.Vr,)))(10.(2;.=(31.Vstrideg,Vidx,))Pb',(6.$4.$2.)Pgh,$1?.P,(1.(5.$1?.)(7.(6.$4.$2.)$1?.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)(;.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)R2.(20.Vst3,))(47.$1?.R1.))P,(1.$4.(?.$4.$2.R3.)(?.$4.$2.Vb,))(53.(2;.(2=.(3.$4.$2.R4.)+9.)(2?.VX,+4.))(2;.(2?.(2=.VX,Vstrideg,)+4.)(3.$4.$2.R4.)))))))))))))")
(* [comment removed for export] *).
Proof.
  destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
  fold strideg in Sspan, Ss16, Ssmod, Snogrp.
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  repeat (split; [first [assumption | unfold X; lia] |]).
  intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.

#[using="r jn sc szc N SC J SO"] Lemma X_mod16 : X mod 16 = 0.
Proof.
  ddestruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _).
  unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
  rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.

#[using="jn N SC J CNT SO G0 MSmm FRESH3"] Lemma nt_tail_hyps : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "(10.(54.$4:.Vmm,)(10.(1.$29.(45.$4:.Vmm,)(55.(56.$1<.)(56.$1<.)(56.$1<.)======))(10.(1.(5.$1:.)(7.$4.$1:.(8.$4.$18.$19.$1:.)(;.$4.$18.$19.$1:.)(?.$4.$2.Vp,)(1;.$4:.))(47.$1:.Vr,))(10.(2;.=(3.$4.$2.Vp,))(10.(1.$2.(3>.(3.$4.$2.Vp,)+10.)=)(10.(2;.(2=.(3.$4.$2.Vp,)+10.)(51.(52.Vr,)))(10.(1.(5.$1?.)(7.$1<.$1?.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)(;.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)Vp,(20.$4:.))(56.$1?.))(10.Pb',(6.$4.$2.)Pgh,$1?.P,(1.(5.$1?.)(7.(6.$4.$2.)$1?.(8.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)(;.$1<.(1=.$4.$18.$2.$9.)(1>.$4.$18.$19.$2.$9.$:.)$1?.)R2.(20.$4:.))(47.$1?.R1.))P,(1.$4.(?.$4.$2.R3.)(?.$4.$2.Vp,))(53.(2;.(2=.(3.$4.$2.R4.)+9.)(3.$4.$2.Vp,))(2;.(2=.(3.$4.$2.Vp,)+9.)(3.$4.$2.R4.)))(10.Po,$2.Pv,$2.Pt,$4.P,(10.(2;.(3.$4.$2.Vp,)R3.)(2<.R3.(2=.(3.$4.$2.Vp,)+<.)))P,(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))R4.(<.(=.$4:.(?.$4.$2.Vp,))))(47.(6.$2.$4.)(14.$2.$4.R3.R2.)))(48.R3.(23.$4:.))(1.$4.(23.$4:.)(23.Vst3,)))))))))))")
(* [comment removed for export] *).
Proof.
  ddestruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  ddestruct ntT_proj as (PR & PG & PA & PT & _).
  split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
  split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
  split. { rewrite PR. exact Sreg. }
  split. { unfold p, X. cbn. lia. }
  split. { exact X_mod16. }
  split. { unfold p. cbn [snd]. lia. }
  split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
           destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
  split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
  split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
           rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
           eapply FRESH3; [| exact Hc]. lia. }
  exact PT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.

#[using="r jn N SC J CNT SO G0 MSmm FRESH3"] Lemma ntF_rec_mt : get_meta_rec stF mm = sm_rec sc cnt (cnt - 1) 0 mm p.
Proof.
  apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.

#[using="r jn N SC J CNT SO G0 MSmm FRESH3"] Lemma ntF_stride : get_stride (get_meta_rec stF mm) = 16 * szc.
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.

#[using="Type"] Lemma ntF_shadow_eq : s_shadow stF = s_shadow (hdr_havoc p nt_stT).
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.

#[using="r jn N SC J SO"] Lemma ntF_cell_read_other o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(0.(10.(2;.VX,O1.)(2<.O1.(2=.VX,+<.))))(1.$32.(33.(=.VstF,(?.$4.$2.Vb,))O1.)(33.(=.$4:.(?.$4.$2.Vb,))O1.))")
(* [comment removed for export] *).
Proof.
  intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.

#[using="Type"] Lemma ntF_cells o : (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow nt_stT (fst b))) !! o.
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.

#[using="Type"] Lemma ntF_havp : r_havp (get_shadow stF (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.

#[using="Type"] Lemma ntF_hav u : u <> X / 16 -> (r_hav (get_shadow stF (fst b))) !! u = (r_hav (get_shadow st3 (fst b))) !! u.
Proof.
  intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="jn N SC J CNT SO STR FITN G0 MSmm TK3 FRESH3"] Lemma nt_slot_ok (req : Z) : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
  intros RQ FIT. pose proof szc_range as SZR.
  ddestruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  ddestruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
  pose proof ntF_stride as STF.
  pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  ddestruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _). fold stF in PF1, PF2, PF3, PF4.
  ddestruct ntT_proj as (PR & PG & PA & PT & _).
  constructor; rewrite ?STF.
  - rewrite ntF_rec_mt. reflexivity.
  - rewrite PF1, PR. exact Sreg.
  - exact Skind.
  - exact TP0.
  - exact TP16.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
  - lia.
  - rewrite Z.mul_comm. apply Z_mod_mult.
  - lia.
  - exact RQ.
  - exact FIT.
  - intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
    + left. unfold p. cbn [snd]. lia.
    + rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf); [left; lia| right]. nia.
  - unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
    rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
  - unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
    apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
  - apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
  - rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

(* [comment removed for export] *)
#[using="jn N SC J CNT"] Lemma ntF_span_cells o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(10.(2;.(2=.VX,+10.)O1.)(2<.O1.(2?.(2=.(2=.VX,+10.)(31.+10.Vszc,))+4.)))(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.VstF,(?.$4.$2.Vb,))))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))O1.(<.(=.Vst3,(?.$4.$2.Vb,)))))")
(* [comment removed for export] *).
Proof.
  intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
  intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.

#[using="r jn N SC J SO"] Lemma ntF_span_hav o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(2;.(2=.VX,+10.)O1.)(1.(5.(11.(6.$2.$4.)))(7.$2.(11.(6.$2.$4.))(8.$2.$9.$:.(11.(6.$2.$4.)))(;.$2.$9.$:.(11.(6.$2.$4.)))(40.O1.+10.)(12.(=.VstF,(?.$4.$2.Vb,))))(7.$2.(11.(6.$2.$4.))(8.$2.$9.$:.(11.(6.$2.$4.)))(;.$2.$9.$:.(11.(6.$2.$4.)))(40.O1.+10.)(12.(=.Vst3,(?.$4.$2.Vb,)))))")
(* [comment removed for export] *).
Proof. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="r jn N SC J CNT SO"] Lemma ntF_rdv13 o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(1.(5.(6.$2.$4.))(7.$2.(6.$2.$4.)(8.$2.$9.$:.(6.$2.$4.))(;.$2.$9.$:.(6.$2.$4.))(2=.VX,+=.)(<.(=.Vst3,(?.$4.$2.Vb,))))(56.(6.$2.$4.)))P,(1.(5.(11.(6.$2.$4.)))(7.$2.(11.(6.$2.$4.))(8.$2.$9.$:.(11.(6.$2.$4.)))(;.$2.$9.$:.(11.(6.$2.$4.)))(40.(2=.VX,+=.)+10.)(12.(=.Vst3,(?.$4.$2.Vb,))))(56.(11.(6.$2.$4.))))P,(1.(5.$4.)(7.$2.$4.(8.$2.$9.$:.$4.)(;.$2.$9.$:.$4.)(40.(2=.VX,+=.)+1000.)(13.(=.Vst3,(?.$4.$2.Vb,))))(56.$4.))(1.$2.(57.$58.$59.O1.VstF,(14.$4.$2.(?.$4.$2.Vb,)(2=.VX,+=.)))=)")
(* [comment removed for export] *).
Proof.
  intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
  rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
  unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="r jn N SC J CNT SO TK3"] Lemma ntF_unknown off h : ltac2:(CDefT.buildp (gd_tbl_ASlot_M5P ()) "P,(2;.=O2.)P,(1.$32.(33.(=.VstF,(?.$4.$2.Vb,))O2.)(5:.O1.))(53.(5;.VstF,(?.$4.$2.Vb,)O2.)(10.(1.$32.(33.(=.Vst3,(?.$4.$2.Vb,))O2.)(5:.O1.))(10.(0.(10.(2;.(2?.VX,+3.)O2.)(2<.O2.VX,)))(0.(5<.$2.Lj,$2.(10.(10.(2;.=R1.)(2;.R1.Vcnt,))(1.$2.O2.(2=.(2=.VX,+<.)(31.R1.(31.+10.Vszc,))))))))))")
(* [comment removed for export] *).
Proof.
  intros Ho Hc. pose proof szc_range as SZR.
  destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
  2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
  all: right; rewrite ntF_cell_read_other in Hc by lia.
  - destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
      split; [exact Hc|]. split; [lia|]. (intros dd_H; ddestruct dd_H as (j & Hj & E)). nia.
    + exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
  - destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
      [destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
      split; [exact Hc|]. split; [lia|]. (intros dd_H; ddestruct dd_H as (j & Hj & E)).
      assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
    + exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
      pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
      pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
      replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
      split; [exact Hc|]. split; [lia|]. (intros dd_H; ddestruct dd_H as (j & Hj & E)).
      apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.

#[using="Type"] Lemma ntF_shadow_other q : q <> fst b -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.

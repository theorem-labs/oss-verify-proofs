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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A3 ASlot_W9 ASlot_W14.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_M4P () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Numbers.BinNums.Z"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.aadd"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.add_slots"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.mkMeta"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.mask_upto"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "OSSVerify.KrLib.Heap.Malloc.hdr_havoc"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "stdpp.base.insert"; "stdpp.fin_maps.map_insert"; "stdpp.gmap.gmap_partial_alter"; "OSSVerify.KrLib.Heap.Malloc.mkGhdr"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.Heap.Malloc.area"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.Malloc.mkShadow"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.hav_add"; "stdpp.option.from_option"; "Corelib.Init.Datatypes.id"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.Malloc.r_hav"; "OSSVerify.KrLib.Heap.Malloc.r_havp"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "SMG.sm_rec"].


(* [comment removed for export] *)
Lemma pos_iter_slots' (m p : aptr) (stride : Z) : forall n tb,
  0 < stride ->
  let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
  fst (Pos.iter F (0, tb) n) = Z.pos n
  /\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
    intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
    left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
  - rewrite Pos.iter_succ. ddestruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
    unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
    split; [lia|]. split.
    + rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
    + intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
      * right. exists (Z.pos n). split; [lia| reflexivity].
      * rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first' m p stride c st : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "P,(0.+1.O2.)P,(1.=O3.)(2.(3.(4.(5.$6.$7.))(8.$6.(5.$6.$7.)(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)(5.$6.$7.))(11.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)(5.$6.$7.))(12.O4.$13.)(14.(15.O5.O4.O3.O2.O1.)))(16.(5.$6.$7.)(17.$6.$7.O5.=)))Pq,$6.P,(18.(3.(4.(5.$6.$7.))(8.$6.(5.$6.$7.)(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)(5.$6.$7.))(11.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)(5.$6.$7.))R1.(14.(15.O5.O4.O3.O2.O1.)))(19.(5.$6.$7.))))(1:.(18.(3.(4.(5.$6.$7.))(8.$6.(5.$6.$7.)(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)(5.$6.$7.))(11.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)(5.$6.$7.))R2.(14.O1.))(19.(5.$6.$7.))))(1;.$7.Li,$7.(2.(2.(0.=R1.)(1.R1.O2.))(3.$6.R3.(12.O4.(1<.$13.(1=.O3.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
  destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
  ddestruct (pos_iter_slots' m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

Lemma mask_upto_range' k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

(* [comment removed for export] *)
Lemma put_meta_wr8_comm mt r q v st : put_meta mt r (wr8 q v st) = wr8 q v (put_meta mt r st).
Proof. destruct st; reflexivity. Qed.
Lemma put_meta_zero_hdrs_comm mt r p size : forall k i st,
  put_meta mt r (zero_hdrs p size i k st) = zero_hdrs p size i k (put_meta mt r st).
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH, put_meta_wr8_comm. reflexivity. Qed.
Lemma rec_zero_hdrs p size q : forall k i st, get_meta_rec (zero_hdrs p size i k st) q = get_meta_rec st q.
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. destruct st; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SMG.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis P0 : 0 <= snd p.

Definition sm_rec : meta := ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "(1>.(16.$6.Vmt,)(16.$6.Vmt,)(16.$6.Vp,)(1?.(20.Vai,)+1.)(1?.(20.(1?.Vcnt,+1.))(20.Vai,))(1?.Vcnt,+1.)+1.Vsc,Vml,)")
(* [comment removed for export] *).

#[using="Type"] Lemma smg_proj : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "(2.(3.(9.$;.$<.$?.$21.)(22.VstF,)(22.VstT,))(2.(3.(9.$;.$<.$?.$23.)(24.VstF,)(24.(25.Vp,VstT,)))(2.(3.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(27.VstF,)(28.$6.$26.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(29.$6.$26.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(2:.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.))Vp,(2;.(16.$6.Vmt,)(2<.Vai,+1?.))(27.VstT,)))(2.(3.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$2=.)(2>.VstF,)(2>.VstT,))(2.(3.$;.(2?.VstF,)(2?.VstT,))(2.(3.$;.(30.VstF,)(30.VstT,))(2.(3.(31.(5.$7.$7.))(32.VstF,)(32.VstT,))(2.(3.$33.(34.(35.VstF,))(34.(35.VstT,)))(2.(3.$7.(36.(35.VstF,))(36.(35.VstT,)))(3.$37.(38.(35.VstF,))(38.(35.VstT,))))))))))))")
(* [comment removed for export] *).
Proof. repeat split; reflexivity. Qed.

#[using="SC CNT REC P0"] Lemma smg_rec_mt : get_meta_rec stF mt = sm_rec.
Proof.
  unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
  unfold stFin, stE. rewrite rec_set_active, get_meta_rec_put_same. reflexivity.
Qed.


#[using="Type"] Lemma smg_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof.
  unfold stF, st_model. cbv zeta. rewrite active_set_active. destruct (c =? sc); [reflexivity|].
  rewrite !active_upd_meta. reflexivity.
Qed.


#[using="SC CNT"] Lemma smg_stride : get_stride sm_rec = if (cnt =? 1) && negb (ml =? 0) then ml * 4096 - 16 else 16 * size_class sc.
Proof.
  unfold get_stride, sm_rec. cbn [m_last_idx m_maplen m_sizeclass].
  replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); try reflexivity; lia).
  unfold UNIT. reflexivity.
Qed.

#[using="SC CNT REC"] Lemma smg_slot0 : 0 < get_stride sm_rec -> (s_slots stF) !! (fst p, snd p + 16) = Some (mt, 0).
Proof.
  intros HS. unfold stF, st_model. cbv zeta.
  match goal with |- s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ ?X))) !! _ = _ =>
    change (s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ X)))) with (s_slots X) end.
  match goal with |- s_slots (add_slots mt p ?s cnt ?X) !! _ = _ =>
    replace s with (get_stride sm_rec) end.
  2:{ unfold upd_meta. rewrite rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC. unfold get_stride, sm_rec.
      cbn [m_last_idx m_maplen m_sizeclass m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      reflexivity. }
  change (fst p, snd p + 16) with (aadd p UNIT).
  apply (proj1 (add_slots_first' mt p (get_stride sm_rec) cnt _ ltac:(lia) HS)).
Qed.

#[using="Type"] Lemma smg_shadow_other q : q <> fst p -> get_shadow stF q = get_shadow stT q.
Proof.
  intros NE. unfold get_shadow. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma smg_shadow_p : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "(3.$23.(39.VstF,(3:.$;.$7.Vp,))(3;.(3<.(39.VstT,(3:.$;.$7.Vp,)))(28.$7.(31.(5.$7.$;.))(9.$7.$=.$10.(31.(5.$7.$;.)))(29.$7.(31.(5.$7.$;.))(9.$7.$=.$10.(31.(5.$7.$;.)))(2:.$7.$=.$10.(31.(5.$7.$;.))))(3=.(3>.$;.$7.Vp,)+10.)(3?.+<.(2?.VstT,)(40.(31.(5.$7.$;.))(31.(5.$7.$;.))(41.(31.(5.$7.$;.)))(42.(5.$7.$;.))(8.$7.(31.(5.$7.$;.))(9.$7.$=.$10.(31.(5.$7.$;.)))(11.$7.$=.$10.(31.(5.$7.$;.)))(3=.(3>.$;.$7.Vp,)+10.)(43.(39.VstT,(3:.$;.$7.Vp,))))))(43.(39.VstT,(3:.$;.$7.Vp,))))(44.(39.VstT,(3:.$;.$7.Vp,)))))")
(* [comment removed for export] *).
Proof.
  unfold get_shadow at 1. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. reflexivity.
Qed.

#[using="Type"] Lemma smg_group_p : (s_groups stF) !! p = Some (mkGhdr (Some mt) (Z.land ai 31)).
Proof. rewrite (proj1 (proj2 (proj2 smg_proj))). apply lookup_insert_eq. Qed.

#[using="Type"] Lemma smg_groups_inv b' gh : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "P,(3.(4.$26.)(8.$6.$26.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(11.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)O2.(27.VstF,))(16.$26.O1.))(1:.(2.(3.$6.O2.Vp,)(3.$26.O1.(2;.(16.$6.Vmt,)(2<.Vai,+1?.))))(2.(18.(3.$6.O2.Vp,))(3.(4.$26.)(8.$6.$26.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(11.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)O2.(27.VstT,))(16.$26.O1.))))")
(* [comment removed for export] *).
Proof.
  rewrite (proj1 (proj2 (proj2 smg_proj))). intros H. destruct (decide (b' = p)) as [->|NE].
  - left. rewrite lookup_insert_eq in H. inversion H. auto.
  - right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.

#[using="P0"] Lemma smg_groups_old b' gh : (s_groups stT) !! p = None -> (s_groups stT) !! b' = Some gh -> (s_groups stF) !! b' = Some gh.
Proof.
  intros GN H. rewrite (proj1 (proj2 (proj2 smg_proj))). rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite GN in H. discriminate.
Qed.

#[using="SC"] Lemma smg_grp_hdr_cov off : snd p <= off < snd p + 12 -> grp_hdr_cov stF (fst p) off.
Proof. intros Ho. dexists p, (mkGhdr (Some mt) (Z.land ai 31)). split; [exact smg_group_p|]. split; [reflexivity| lia]. Qed.

#[using="P0"] Lemma smg_grp_hdr_cov_old q off : (s_groups stT) !! p = None -> grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. (intros GN dd_H; ddestruct dd_H as (b' & gh & Hb & Hf & Ho)). dexists b', gh. split; [apply smg_groups_old; assumption| auto]. Qed.

#[using="Type"] Lemma smg_conc q : conc stF q = conc stT q.
Proof. unfold conc, get_region. rewrite (proj1 smg_proj). reflexivity. Qed.

#[using="Type"] Lemma smg_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. split; intros H; (eapply meta_slot_same_areas; [| exact H]); rewrite (proj1 (proj2 (proj2 (proj2 smg_proj)))); reflexivity. Qed.

(* [comment removed for export] *)
#[using="SC CNT REC P0"] Lemma smg_ret_span rid' S len : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "P,(1;.$6.Lg,$6.(1;.$6.Lb,$6.(2.(3.$37.(45.VstF,Vsc,)(16.$6.R2.))(2.(3.$37.(46.(47.VstF,R2.))(16.$6.R1.))(2.(3.$;.O3.(3:.$;.$7.R1.))(2.(3.$7.O2.(1<.(1<.(3>.$;.$7.R1.)+10.)(1=.(48.(47.VstF,R2.))=)))(3.$7.O1.(1?.(48.(47.VstF,R2.))+4.))))))))(2.(3.$;.O3.(3:.$;.$7.Vp,))(2.(3.$7.O2.(1<.(3>.$;.$7.Vp,)+10.))(3.$7.O1.(1?.(48.$49.)+4.))))")
(* [comment removed for export] *).
Proof.
  (intros dd_H; ddestruct dd_H as (g & b & HA & HM & -> & -> & ->)). rewrite smg_active, Z.eqb_refl in HA. inversion HA; subst g.
  rewrite smg_rec_mt in HM |- *. cbn in HM. inversion HM; subst b. split; [reflexivity| split; [lia| reflexivity]].
Qed.
End SMG.

Lemma Zle_1_nonneg' x : 1 <= x < 2^28 -> 0 <= x /\ True.
Proof. intros H. split; [lia| exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SM.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt : aptr) (rid : N) (r0 : region).
Let p : aptr := (rid, 0).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 1 <= ml < 2^28.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis HrT : (s_regions stT) !! rid = Some r0.
Hypothesis Hk0 : r_kind r0 = RKGroup.
Hypothesis SHT : (s_shadow stT) !! rid = None.
Hypothesis GNT : forall off, (s_groups stT) !! (rid, off) = None.

Let P0 : 0 <= snd p := Z.le_refl 0.
Let ML0 : 0 <= ml := proj1 (Zle_1_nonneg' ml ML).


#[using="Type"] Lemma sm_proj : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "(2.(3.(9.$;.$<.$?.$21.)(22.VstF,)(22.VstT,))(2.(3.(9.$;.$<.$?.$23.)(24.VstF,)(24.(25.Vp,VstT,)))(2.(3.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(27.VstF,)(28.$6.$26.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(29.$6.$26.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.)(2:.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$26.))Vp,(2;.(16.$6.Vmt,)(2<.Vai,+1?.))(27.VstT,)))(2.(3.(9.$6.(:.$;.$<.$7.$=.)(>.$;.$<.$?.$7.$=.$10.)$2=.)(2>.VstF,)(2>.VstT,))(2.(3.$;.(2?.VstF,)(2?.VstT,))(2.(3.$;.(30.VstF,)(30.VstT,))(2.(3.(31.(5.$7.$7.))(32.VstF,)(32.VstT,))(2.(3.$33.(34.(35.VstF,))(34.(35.VstT,)))(2.(3.$7.(36.(35.VstF,))(36.(35.VstT,)))(3.$37.(38.(35.VstF,))(38.(35.VstT,))))))))))))")
(* [comment removed for export] *).
Proof. exact (smg_proj stT sc cnt ai mt p). Qed.

#[using="SC CNT REC P0"] Lemma sm_rec_mt : get_meta_rec stF mt = sm_rec sc cnt ai ml mt p.
Proof. apply (smg_rec_mt stT sc cnt ai ml mt p); assumption. Qed.

#[using="Type"] Lemma sm_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof. exact (smg_active stT sc cnt ai mt p c). Qed.

#[using="sc SC ML"] Lemma sm_ml_nz : (ml =? 0) = false.
Proof. apply Z.eqb_neq. lia. Qed.

#[using="SC CNT ML"] Lemma sm_stride : get_stride (sm_rec sc cnt ai ml mt p) = if cnt =? 1 then ml * 4096 - 16 else 16 * size_class sc.
Proof. rewrite (smg_stride sc cnt ai ml mt p) by assumption. rewrite sm_ml_nz, andb_true_r. reflexivity. Qed.

#[using="SC CNT REC"] Lemma sm_slot0 : 0 < get_stride (sm_rec sc cnt ai ml mt p) -> (s_slots stF) !! (rid, 16) = Some (mt, 0).
Proof. intros HS. apply (smg_slot0 stT sc cnt ai ml mt p); assumption. Qed.

(* [comment removed for export] *)
#[using="SHT"] Lemma sm_cell_read off : 0 <= off -> cell_read (get_shadow stF rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  intros Ho. unfold get_shadow. rewrite (proj1 (proj2 sm_proj)). fold (get_shadow (hdr_havoc p stT) rid).
  apply cell_read_hh0; [exact SHT| exact Ho].
Qed.

#[using="SHT"] Lemma sm_cells_none off : (r_cells (get_shadow stF rid)) !! off = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_cells]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

#[using="SHT"] Lemma sm_hav_none off : 16 <= off -> (r_hav (get_shadow stF rid)) !! (off / 16) = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. intros Ho. change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_hav]. unfold p. cbn [fst snd]. change (0 / 16) with 0.
  rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). unfold get_shadow. rewrite SHT. cbn. apply lookup_empty.
Qed.

#[using="SHT"] Lemma sm_havp_none k : (r_havp (get_shadow stF rid)) !! k = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_havp]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

#[using="Type"] Lemma sm_shadow_other q : q <> rid -> get_shadow stF q = get_shadow stT q.
Proof. intros NE. exact (smg_shadow_other stT sc cnt ai mt p q NE). Qed.

#[using="GNT"] Lemma sm_groups_rid off gh : (s_groups stF) !! (rid, off) = Some gh -> off = 0 /\ gh = mkGhdr (Some mt) (Z.land ai 31).
Proof.
  intros H. destruct (smg_groups_inv stT sc cnt ai mt p _ _ H) as [[E ->]|[NE H']].
  - unfold p in E. inversion E. auto.
  - rewrite GNT in H'. discriminate.
Qed.

#[using="SC"] Lemma sm_grp_hdr_cov off : 0 <= off < 12 -> grp_hdr_cov stF rid off.
Proof. clear ML0 P0 CNT AI ML REC HrT Hk0 GNT SHT. intros Ho. apply (smg_grp_hdr_cov stT sc cnt ai mt p SC off). cbn. lia. Qed.

#[using="GNT P0"] Lemma sm_grp_hdr_cov_old q off : grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros H. exact (smg_grp_hdr_cov_old stT sc cnt ai mt p P0 q off (GNT 0) H). Qed.

#[using="Type"] Lemma sm_conc q : conc stF q = conc stT q.
Proof. exact (smg_conc stT sc cnt ai mt p q). Qed.

#[using="Type"] Lemma sm_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. exact (smg_meta_slot stT sc cnt ai mt p q). Qed.

#[using="SHT"] Lemma sm_rdv o : rdv pans_mem o stF (rid, 13) = 0.
Proof. clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. unfold rdv. cbn [fst snd]. rewrite sm_cell_read by lia. reflexivity. Qed.

#[using="ml SC CNT ML REC P0"] Lemma sm_stride_mod16 : get_stride (get_meta_rec stF mt) mod 16 = 0.
Proof.
  rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1).
  - replace (ml * 4096 - 16) with ((256 * ml - 1) * 16) by lia. apply Z_mod_mult.
  - rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
#[using="SC CNT AI ML REC HrT Hk0 SHT GNT P0"] Lemma sm_slot_ok (req nd : Z) :
  0 <= req < 2^32 -> req + 4 <= 16 * size_class sc ->
  r_len r0 = nd -> nd = 4096 * ml -> req + 20 <= nd -> 16 * size_class sc < 2^18 ->
  (cnt = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * cnt + 16 <= nd /\ nd < 16 * size_class sc * cnt + 16 + 4096) ->
  meta_slot stT mt ->
  slot_ok stF mt p r0 0 req
  /\ get_stride (get_meta_rec stF mt) = (if cnt =? 1 then nd - 16 else 16 * size_class sc)
  /\ 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) <= nd.
Proof.
  intros RQ FIT LEN EML NDR SZ NDC MS.
  pose proof (size_class_range sc SC) as SZR.
  assert (RU : round_up_pg nd = nd).
  { rewrite EML. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace (- (4096 * ml)) with ((- ml) * 4096) by lia. rewrite Z_mod_mult. lia. }
  assert (STR : get_stride (get_meta_rec stF mt) = if cnt =? 1 then nd - 16 else 16 * size_class sc).
  { rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1); lia. }
  assert (S20 : 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) * cnt <= nd
               /\ req + 4 <= get_stride (get_meta_rec stF mt) /\ get_stride (get_meta_rec stF mt) - 4 - req < 2^31
               /\ (forall off, 16 * off + req + 4 <= get_stride (get_meta_rec stF mt) -> off < 65536)).
  { rewrite STR. destruct (Z.eqb_spec cnt 1) as [E1|NE1].
    - rewrite E1. destruct NDC as [[_ X]|[X1 X2]]; (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros off Hoff; lia).
    - destruct NDC as [[X _]|[X1 X2]]; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros off Hoff. lia. }
  ddestruct S20 as (G20 & GSP & GFIT & G31 & G18).
  pose proof (mask_upto_range' ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (AM : mask_upto ai <= mask_upto (cnt - 1)) by (unfold mask_upto; apply Z.sub_le_mono_r; apply Z.pow_le_mono_r; lia).
  split; [| split; [exact STR| split; [exact G20| nia]]].
  constructor.
  - rewrite sm_rec_mt. reflexivity.
  - rewrite (proj1 sm_proj). exact HrT.
  - exact Hk0.
  - unfold p. cbn [snd]. lia.
  - reflexivity.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - replace (m_last_idx (get_meta_rec stF mt)) with (cnt - 1) by (rewrite sm_rec_mt; reflexivity).
    rewrite LEN, RU. unfold p. cbn [snd]. replace (cnt - 1 + 1) with cnt by lia. lia.
  - exact G20.
  - apply sm_stride_mod16.
  - exact G31.
  - lia.
  - exact GFIT.
  - intros b' gh Hb' Hf. destruct b' as [b1 b2]. unfold p in Hf. cbn in Hf. subst b1. destruct (sm_groups_rid _ _ Hb') as [-> _]. unfold p. cbn [snd]. left. lia.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0 - 4) with 12 by lia. rewrite sm_cell_read by lia. reflexivity.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. apply G18. exact OF.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0) with 16 by lia. apply sm_slot0. rewrite <- sm_rec_mt. lia.
  - apply (proj1 (sm_meta_slot mt)). exact MS.
  - rewrite sm_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

#[using="ml SC CNT REC P0"] Lemma sm_ret_span rid' S len : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4P ()) "P,(1;.$6.Lg,$6.(1;.$6.Lb,$6.(2.(3.$37.(45.VstF,Vsc,)(16.$6.R2.))(2.(3.$37.(46.(47.VstF,R2.))(16.$6.R1.))(2.(3.$;.O3.(3:.$;.$7.R1.))(2.(3.$7.O2.(1<.(1<.(3>.$;.$7.R1.)+10.)(1=.(48.(47.VstF,R2.))=)))(3.$7.O1.(1?.(48.(47.VstF,R2.))+4.))))))))(2.(3.$;.O3.Vrid,)(3.$7.O2.+10.))")
(* [comment removed for export] *).
Proof.
  intros H. ddestruct (smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H) as (-> & -> & _). unfold p. cbn. split; reflexivity.
Qed.
End SM.

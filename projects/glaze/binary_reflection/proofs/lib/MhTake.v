(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhFrame2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RepGroupTransportJ.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st1 st2 : mst) (M1 M2 : mem) (x : Z).
  (* [comment removed for export] *)
  Hypothesis Emem : g_mem st2 x = g_mem st1 x.
  Hypothesis Ecnt : g_cnt st2 x = g_cnt st1 x.
  Hypothesis Elast : g_lastidx st2 x = g_lastidx st1 x.
  Hypothesis Ess : forall k, g_slot_start st2 x k = g_slot_start st1 x k.
  Hypothesis Ese : forall k, g_slot_end st2 x k = g_slot_end st1 x k.
  Hypothesis Eai : s_ai st2 x = s_ai st1 x.
  Hypothesis Einb : forall q, inband st2 x q = inband st1 x q.
  Hypothesis Eend : endb_own st2 x -> endb_own st1 x.
  Hypothesis Ekind : match s_kind st2 x with GTop => s_kind st1 x = GTop /\ g_maplen st2 x = g_maplen st1 x | GNest _ _ _ => True end.
  (* [comment removed for export] *)
  Hypothesis Eslot : forall k, 0 <= k <= g_lastidx st1 x ->
    s_slot st2 x k = s_slot st1 x k \/ s_slot st2 x k = SAvail \/ s_slot st2 x k = SFreed \/ (exists o, s_slot st2 x k = SJunk o).
  (* [comment removed for export] *)
  Hypothesis Agree : forall a, gcell st2 x a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
  Hypothesis Grow : mem_grows M1 M2.
  (* [comment removed for export] *)
  Hypothesis Rng : 0 <= g_mem st1 x /\ g_mem st1 x + 16 <= g_span_end st1 x /\ g_span_end st1 x < 2 ^ 64.
  Hypothesis Cells1 : forall a, gcell st2 x a -> g_mem st1 x <= a < g_span_end st1 x.

  Lemma CRJ : forall a, gcell st2 x a -> 0 <= a < 2 ^ 64.
  Proof using Cells1 Rng st1. intros a G. pose proof (Cells1 a G). lia. Qed.

  Lemma byte_trJ : forall a b, gcell st2 x a -> byte_at M1 a b -> byte_at M2 a b.
  Proof using Agree. intros a b G B. unfold byte_at in *. rewrite (Agree a G). exact B. Qed.

  Lemma cell_trJ : forall a n v, (forall y, a <= y < a + Z.of_nat n -> gcell st2 x y) -> (0 < Z.of_nat n) ->
    cell M1 a n v -> cell M2 a n v.
  Proof using Cells1 Rng Agree st1.
    intros a n v G Hn C.
    pose proof (CRJ a (G a ltac:(lia))). pose proof (CRJ (a + Z.of_nat n - 1) (G (a + Z.of_nat n - 1) ltac:(lia))).
    eapply cell_agree; [lia | lia | | exact C]. intros y Hy Hr. apply Agree. apply G. exact Hr.
  Qed.

  Lemma rep_hdr_transportJ : forall k q rc,
    0 <= k <= g_lastidx st1 x -> slot_ptr st2 x k = Some q ->
    rep_hdr st1 M1 x k q rc -> rep_hdr st2 M2 x k q rc.
  Proof using Cells1 Rng Agree Einb Elast.
    intros k q rc Hk Hq [A B C].
    assert (G : forall a, q - 4 <= a < q -> gcell st2 x a).
    { intros a Ha. unfold gcell. right. right. left. exists k, q. rewrite Elast. repeat split; try lia. exact Hq. }
    constructor.
    - apply byte_trJ; [apply G; lia | exact A].
    - apply byte_trJ; [apply G; lia | exact B].
    - rewrite Einb. apply cell_trJ; [cbn; intros y Hy; apply G; lia | cbn; lia | exact C].
  Qed.

  Lemma rep_group_transportJ : rep_group st1 M1 x -> rep_group st2 M2 x.
  Proof using Cells1 Rng Grow Agree Eslot Ekind Eend Einb Eai Ese Ess Elast Ecnt Emem.
    intros [Hm Hai Hh Hd Hs].
    assert (Gh : forall a, g_mem st1 x <= a < g_mem st1 x + 12 -> gcell st2 x a) by (intros a Ha; unfold gcell; left; rewrite Emem; exact Ha).
    constructor.
    - rewrite Emem. apply cell_trJ; [cbn; intros y Hy; apply Gh; lia | cbn; lia | exact Hm].
    - rewrite Emem, Eai. destruct Hai as (b & Hb & Hba & Hmod). exists b. split; [exact Hb|]. split; [|exact Hmod].
      apply byte_trJ; [apply Gh; lia | exact Hba].
    - intros k Hk Hend. rewrite Ess. rewrite Ecnt in Hk, Hend.
      assert (G : gcell st2 x (g_slot_start st1 x k - 4)).
      { unfold gcell. right. left. exists k. rewrite Ecnt, Ess. repeat split; try lia.
        destruct Hend as [H|H]; [left; exact H | right; exact H]. }
      apply byte_trJ; [exact G|].
      apply Hh; [exact Hk|]. destruct Hend as [H|H]; [left; exact H | right; apply Eend; exact H].
    - destruct (s_kind st2 x); [|exact I]. destruct Ekind as [K E]. rewrite K in Hd. rewrite Emem, E.
      eapply defined_grows; [exact Grow | exact Hd].
    - intros k Hk. rewrite Elast in Hk.
      destruct (Eslot k Hk) as [E | [E | [E | [o E]]]]; rewrite E; [|exact I|exact I|exact I].
      pose proof (Hs k Hk) as RS. destruct (s_slot st1 x k) as [| |q n o r|c o|o] eqn:Sk; cbn [rep_slot] in *; try exact I.
      + destruct RS as (RH & Rz & R5).
        assert (Hq : slot_ptr st2 x k = Some q) by (unfold slot_ptr; rewrite E; reflexivity).
        assert (Gf : forall a, ((0 < r /\ a = q + n) \/ (5 <= r /\ g_slot_end st1 x k - 5 <= a < g_slot_end st1 x k)) -> gcell st2 x a).
        { intros a Ha. unfold gcell. right. right. right. exists k, q, n, o, r. rewrite Elast, Ese. split; [lia|]. split; [exact E | exact Ha]. }
        split; [exact (rep_hdr_transportJ k q _ Hk Hq RH)|]. split.
        * intros Hr. apply byte_trJ; [apply Gf; left; lia | exact (Rz Hr)].
        * intros Hr. destruct (R5 Hr) as [C B]. rewrite Ese. split.
          -- apply cell_trJ; [cbn; intros y Hy; apply Gf; right; lia | cbn; lia | exact C].
          -- apply byte_trJ; [apply Gf; right; lia | exact B].
      + destruct RS as (rc & Hrc & RH). exists rc. split; [exact Hrc|]. rewrite Ess.
        apply (rep_hdr_transportJ k _ rc Hk); [|exact RH]. unfold slot_ptr. rewrite E, Ess. reflexivity.
  Qed.
End RepGroupTransportJ.
End MhFrame2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhSetBit. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame MhFrame2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhSetBit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma testbit_sub_pow2 : forall av i j, 0 <= av -> 0 <= i -> 0 <= j -> Z.testbit av i = true ->
  Z.testbit (av - 2 ^ i) j = (negb (Z.eqb i j) && Z.testbit av j)%bool.
Proof.
  intros av i j Hav Hi Hj Hb.
  assert (HL : Z.ldiff (2 ^ i) av = 0).
  { apply Z.bits_inj_0. intros k. destruct (Z.lt_ge_cases k 0) as [Hk|Hk]; [apply Z.testbit_neg_r; exact Hk|].
    rewrite Z.ldiff_spec, testbit_pow2 by lia. destruct (Z.eqb_spec i k) as [<-|Hne]; [rewrite Hb; reflexivity | reflexivity]. }
  rewrite (Z.sub_nocarry_ldiff av (2 ^ i) HL). rewrite Z.ldiff_spec, testbit_pow2 by lia.
  destruct (Z.eqb_spec i j) as [<-|Hne]; cbn; [rewrite Bool.andb_false_r; reflexivity | rewrite Bool.andb_true_r; reflexivity].
Qed.

Section Take.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem).
  Variables (m i : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hi : 0 <= i <= g_lastidx st m.
  Hypothesis Hslot : s_slot st m i = SAvail.
  Hypothesis Hhead : m = head_of (s_alist st (g_sc st m)).
  #[local] Notation jq := (g_slot_start st m i).
  (* [comment removed for export] *)
  Let av := mr_avail (s_meta st m).
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition sb_wr (a : Z) : Prop := (sp - MSTK <= a < sp) \/ (m + 24 <= a < m + 28).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sb_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMav : cell M' (m + 24) 4 (av - 2 ^ i).

  (* [comment removed for export] *)
  Definition st1 : mst := set_slot st m i (SJunk 0).
  Definition st' : mst := set_meta st1 m (mr_set_avail (s_meta st m) (av - 2 ^ i)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_ctx : s_ctx st' = s_ctx st. Proof using. reflexivity. Qed.
  Lemma e_areas : s_areas st' = s_areas st. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_alist : s_alist st' = s_alist st. Proof using. reflexivity. Qed.
  Lemma e_groups : s_groups st' = s_groups st. Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = s_regions st. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. reflexivity. Qed.
  Lemma e_meta : forall x, s_meta st' x = if Z.eqb x m then mr_set_avail (s_meta st m) (av - 2 ^ i) else s_meta st x.
  Proof using. intros x. reflexivity. Qed.
  Lemma e_meta_other : forall x, x <> m -> s_meta st' x = s_meta st x.
  Proof using. intros x Hx. rewrite e_meta. destruct (Z.eqb_spec x m); [contradiction|reflexivity]. Qed.
  Lemma e_next : forall x, mr_next (s_meta st' x) = mr_next (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = mr_prev (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_mem : forall x, mr_mem (s_meta st' x) = mr_mem (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_freed : forall x, mr_freed (s_meta st' x) = mr_freed (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_Wr : forall x, mr_W (s_meta st' x) = mr_W (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_avail_m : mr_avail (s_meta st' m) = av - 2 ^ i.
  Proof using. rewrite e_meta, Z.eqb_refl. reflexivity. Qed.
  Lemma e_avail_other : forall x, x <> m -> mr_avail (s_meta st' x) = mr_avail (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_slot : forall x k, s_slot st' x k = if (Z.eqb x m && Z.eqb k i)%bool then SJunk 0 else s_slot st x k.
  Proof using. intros. reflexivity. Qed.
  Lemma e_slot_mi : s_slot st' m i = SJunk 0.
  Proof using. rewrite e_slot, !Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_other : forall x k, (x <> m \/ k <> i) -> s_slot st' x k = s_slot st x k.
  Proof using. intros x k H. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn; try reflexivity. exfalso; lia. Qed.

  (* [comment removed for export] *)
  Lemma e_gW : forall x, g_W st' x = g_W st x. Proof using. intros; unfold g_W; apply e_Wr. Qed.
  Lemma e_gmem : forall x, g_mem st' x = g_mem st x. Proof using. intros; unfold g_mem; apply e_mem. Qed.
  Lemma e_glast : forall x, g_lastidx st' x = g_lastidx st x. Proof using. intros; unfold g_lastidx; rewrite e_gW; reflexivity. Qed.
  Lemma e_gcnt : forall x, g_cnt st' x = g_cnt st x. Proof using. intros; unfold g_cnt; rewrite e_glast; reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof using. intros; unfold g_sc; rewrite e_gW; reflexivity. Qed.
  Lemma e_gml : forall x, g_maplen st' x = g_maplen st x. Proof using. intros; unfold g_maplen; rewrite e_gW; reflexivity. Qed.
  Lemma e_gstride : forall x, g_stride st' x = g_stride st x.
  Proof using. intros; unfold g_stride; rewrite e_gml, e_glast, e_gsc; reflexivity. Qed.
  Lemma e_gss : forall x k, g_slot_start st' x k = g_slot_start st x k.
  Proof using. intros; unfold g_slot_start; rewrite e_gmem, e_gstride; reflexivity. Qed.
  Lemma e_gse : forall x k, g_slot_end st' x k = g_slot_end st x k.
  Proof using. intros; unfold g_slot_end; rewrite e_gss, e_gstride; reflexivity. Qed.
  Lemma e_gspan : forall x, gspan st' x = gspan st x.
  Proof using. intros; unfold gspan, g_span_end; rewrite e_gmem, e_gstride, e_gcnt; reflexivity. Qed.
  Lemma e_inband : forall x q, inband st' x q = inband st x q.
  Proof using. intros; unfold inband; rewrite e_gmem; reflexivity. Qed.
  Lemma e_ptr_ok : forall x k q, ptr_ok st' x k q <-> ptr_ok st x k q.
  Proof using Hi. intros; unfold ptr_ok; rewrite e_gmem, e_inband, e_gsc, e_gml; tauto. Qed.
  Lemma e_endb : forall x, endb_own st' x <-> endb_own st x.
  Proof using Hi. intros; unfold endb_own; rewrite e_kind, e_gspan. destruct (s_kind st x); [tauto|]. rewrite e_gse. tauto. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using Hi. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using Hi. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using Hi. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using Hi. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x. Proof using Hi. intros; unfold listed; rewrite e_in_flist, e_in_alist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using Hi. intros; unfold fresh; rewrite e_ctx, e_areas; tauto. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (U_wfg st L HWF m Hgrp). Qed.
  Lemma t_masks : 0 <= av < 2 ^ 32 /\ 0 <= mr_freed (s_meta st m) < 2 ^ 32 /\
                  Z.testbit av i = true /\ Z.testbit (mr_freed (s_meta st m)) i = false.
  Proof using Hslot Hi Hgrp HWF L RN.
    pose proof t_wfg as WG. split; [exact (wg_avr st L m WG)|]. split; [exact (wg_frr st L m WG)|]. split.
    - apply (proj2 (wg_av st L m WG i ltac:(lia))). split; [lia | exact Hslot].
    - destruct (Z.testbit (mr_freed (s_meta st m)) i) eqn:E; [|reflexivity]. exfalso.
      apply (proj1 (wg_fr st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E.
  Qed.
  Lemma t_last : 0 <= g_lastidx st m < 32. Proof using av. unfold g_lastidx, w_lastidx. apply Z.mod_pos_bound. lia. Qed.
  Lemma t_pow : 0 < 2 ^ i <= 2 ^ 31.
  Proof using av Hi m st. pose proof t_last. split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. Qed.
  Lemma t_av' : 0 <= av - 2 ^ i < 2 ^ 32.
  Proof using HMav Hslot Hi Hgrp HWF M' L RN.
    destruct t_masks as (A1 & _ & A2 & _). pose proof t_pow. split; [|lia].
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases av (2 ^ i)) as [LT|GE]; [|lia]. exfalso.
    assert (Z.testbit av i = false); [|congruence].
    destruct (Z.eq_dec av 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
  Qed.
  Lemma t_bit : forall j, 0 <= j -> Z.testbit (av - 2 ^ i) j = (negb (Z.eqb i j) && Z.testbit av j)%bool.
  Proof using Hslot Hi Hgrp HWF L RN. intros j Hj. destruct t_masks as (A1 & _ & A2 & _). apply testbit_sub_pow2; try lia. exact A2. Qed.
  Lemma t_stride : 16 <= g_stride st m /\ g_stride st m mod 16 = 0. Proof using Hgrp HWF L RN. exact (wg_stride st L m t_wfg). Qed.
  Lemma t_i_ai : i <= s_ai st m. Proof using Hslot Hi Hgrp HWF L RN. exact (wg_avai st L m t_wfg i Hi Hslot). Qed.

  (* [comment removed for export] *)
  Lemma t_ptr_ok0 : ptr_ok st m i jq.
  Proof using HMav av Hslot Hi Hgrp HWF M' L RN.
    pose proof t_wfg as WG. pose proof t_stride as [S16 Smod]. pose proof (wg_mem st L m WG) as (M1 & M2 & M3). pose proof t_last as TL.
    assert (SCR : 0 <= g_sc st m < 64) by (unfold g_sc, w_sizeclass; apply Z.mod_pos_bound; lia).
    assert (SI : 0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia).
    (* [comment removed for export] *)
    assert (Q : g_stride st m * i < 2 ^ 20).
    { destruct (wg_sc st L m WG) as [S48|(S63 & L0 & _)].
      - pose proof (wg_q st L m WG S48) as Q. assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia). lia.
      - assert (i = 0) by lia. subst i. lia. }
    assert (EI : inband st m jq = g_stride st m * i / 16).
    { unfold inband, g_slot_start, UNIT. f_equal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    unfold ptr_ok. rewrite EI. split; [|split; [|split; [|split; [|split]]]].
    - unfold g_slot_start, UNIT. clear - M2 Smod SI. lia.
    - unfold g_slot_start, UNIT. lia.
    - unfold g_slot_start, UNIT. replace (g_mem st m + 16 + g_stride st m * i - g_mem st m - 16) with (g_stride st m * i) by lia. clear - Smod SI. lia.
    - clear - Q SI. lia.
    - intros S48. pose proof (size_class_pos (g_sc st m) ltac:(lia)) as [SC1 SC2].
      assert (ES : (g_maplen st m <> 0 /\ g_lastidx st m = 0 /\ g_stride st m = g_maplen st m * 4096 - UNIT) \/ g_stride st m = UNIT * size_class (g_sc st m)).
      { unfold g_stride, slot_stride. destruct (negb (g_maplen st m =? 0) && (g_lastidx st m =? 0))%bool eqn:B.
        - left. apply Bool.andb_true_iff in B. destruct B as [B1 B2]. apply Bool.negb_true_iff in B1. apply Z.eqb_neq in B1. apply Z.eqb_eq in B2.
          split; [exact B1 | split; [exact B2 | reflexivity]].
        - right. reflexivity. }
      destruct ES as [(ML & L0 & ES)|ES].
      + assert (I0 : i = 0) by lia. rewrite I0, Z.mul_0_r, Z.mul_0_r, Z.add_0_l, Z.mul_1_r. change (0 / 16) with 0. lia.
      + rewrite ES. unfold UNIT. replace (16 * size_class (g_sc st m) * i) with (size_class (g_sc st m) * i * 16) by lia.
        rewrite Z.div_mul by lia. nia.
    - intros Hml. pose proof (wg_kind st L m WG) as KD. destruct (s_kind st m) as [|hm j ho] eqn:K.
      + destruct KD as (K1 & K2 & K3 & K4). unfold UNIT in K4.
        assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
        assert (16 * (g_stride st m * i / 16) <= g_stride st m * i) by (apply Z.mul_div_le; lia).
        clear - H H0 K4 K1 S16. lia.
      + destruct KD as (K1 & _). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_dll : forall l, dll st l -> dll st' l.
  Proof using. intros l D k Hk. destruct (D k Hk) as [A B]. rewrite e_next, e_prev. split; assumption. Qed.

  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L. destruct (WF_ctx st L HWF); constructor; assumption. Qed.

  Lemma t_wf_areas : wf_areas st'.
  Proof using HWF L. destruct (WF_areas st L HWF); constructor; assumption. Qed.

  Lemma t_in_alist_sc : forall sc, In m (s_alist st sc) -> sc = g_sc st m.
  Proof using HWF L RN. intros sc Hin. symmetry. exact (proj2 (proj2 (wl_aU st (WF_lists st L HWF) sc m Hin))). Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hhead Hi Hgrp HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist; try assumption.
    - apply t_dll. exact D1.
    - intros x Hx. destruct (FU x Hx) as (U & NG & NF & Me & Av & Fr & W).
      assert (x <> m) by (intros ->; exact (NG Hgrp)).
      rewrite e_metaU, e_is_group, e_fresh, e_meta_other by assumption. repeat split; assumption.
    - intros sc Hsc. apply t_dll. exact (D2 sc Hsc).
    - intros sc x Hx. rewrite e_is_group, e_gsc. exact (AU sc x Hx).
    - intros x U NL. rewrite e_next, e_prev. apply LK; [apply e_metaU; exact U | intros Hl; apply NL; apply e_listed; exact Hl].
    - intros x Hl. rewrite e_next, e_prev. apply LKD. apply e_listed. exact Hl.
    - intros sc x Hx Hne. rewrite e_freed. destruct (Z.eq_dec x m) as [->|Hxm].
      + exfalso. apply Hne. rewrite (t_in_alist_sc sc Hx). exact Hhead.
      + rewrite e_avail_other by exact Hxm. exact (RS sc x Hx Hne).
  Qed.

  (* [comment removed for export] *)
  Lemma t_slot_wf : forall x k sl, is_group st x -> 0 <= k <= g_lastidx st x -> (x <> m \/ k <> i) ->
    s_slot st x k = sl -> slot_wf st L x k sl -> slot_wf st' L x k sl.
  Proof using Hi.
    intros x k sl Hx Hk Hne Hs SW. destruct sl as [| |q2 n2 o2 r2|c o2|o2]; cbn [slot_wf] in *; try exact I.
    - destruct SW as (A & B & C & D & E & F & G). rewrite e_gss, e_gstride. conjs; try assumption; try lia.
      apply e_ptr_ok. exact F.
    - destruct SW as (A & B & C & D & E). rewrite e_gss. conjs; try assumption.
      all: try (apply e_is_group; exact B). all: try (apply e_ptr_ok; exact E).
    - destruct SW as (A & B & C). rewrite e_gss, e_gstride. conjs; try assumption. apply e_ptr_ok. exact C.
  Qed.

  Lemma t_wf_group_other : forall x, is_group st x -> x <> m -> wf_group st' L x.
  Proof using Hslot Hi HWF RN.
    intros x Hx Hxm. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_alist, ?e_kind;
      rewrite ?(e_meta_other x Hxm); try assumption.
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Av k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Fr k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Avai k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (High k Hk).
    - intros Hall Hne Hl. apply Full; [| exact Hne | exact Hl].
      intros k Hk. rewrite <- (e_slot_other x k) by (left; exact Hxm). exact (Hall k Hk).
    - destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride. conjs; try assumption; try lia.
      rewrite e_slot_other; [exact K6|].
      destruct (Z.eq_dec hm m) as [->|]; [right | left; assumption]. intros ->. rewrite Hslot in K6. discriminate K6.
    - intros Hall. apply FF. intros k Hk. rewrite <- (e_slot_other x k) by (left; exact Hxm). exact (Hall k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm).
      apply t_slot_wf; [exact Hx | exact Hk | left; exact Hxm | reflexivity | exact (Slots k Hk)].
    - intros Hsc Hst k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Fit Hsc Hst k Hk).
  Qed.

  Lemma t_wf_group_m : wf_group st' L m.
  Proof using HMav Hhead Hslot Hi Hgrp HWF M' RN.
    pose proof t_wfg as WG. pose proof t_av' as AR. pose proof t_last as TL. destruct t_masks as (A1 & F1 & A2 & F2). pose proof t_i_ai as IA.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_alist, ?e_kind,
      ?e_freed, ?e_avail_m; try assumption.
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. rewrite t_bit by exact Hk.
      destruct (Z.eqb_spec i k) as [<-|Hik]; cbn [negb andb].
      + rewrite Z.eqb_refl. split; [intros E; discriminate E | intros [_ E]; discriminate E].
      + replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). exact (Av k Hk).
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb].
      destruct (Z.eqb_spec k i) as [->|Hki].
      + rewrite F2. split; [intros E; discriminate E | intros [_ E]; discriminate E].
      + exact (Fr k Hk).
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki]; [intros E; discriminate E|]. exact (Avai k Hk).
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki]; [lia|]. exact (High k Hk).
    - intros Hall Hne. exfalso. exact (Hne Hhead).
    - destruct (s_kind st m) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride. conjs; try assumption; try lia.
      rewrite e_slot_other; [exact K6 | left; congruence].
    - intros Hall. exfalso. destruct (Hall i Hi) as [E|E]; rewrite e_slot_mi in E; discriminate E.
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki].
      + cbn [slot_wf]. rewrite e_gss, e_gstride. split; [lia|]. split; [unfold IB; pose proof t_stride; lia|].
        apply e_ptr_ok. replace (g_slot_start st m i + 16 * 0) with (g_slot_start st m i) by lia. exact t_ptr_ok0.
      + apply t_slot_wf; [exact Hgrp | exact Hk | right; exact Hki | reflexivity | exact (Slots k Hk)].
    - intros Hsc Hst k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki]; [split; intros E; discriminate E|]. exact (Fit Hsc Hst k Hk).
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using HMav Hhead Hslot Hi Hgrp HWF M' RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups.
    - exact ND.
    - intros x Hx. destruct (Z.eq_dec x m) as [->|Hxm]; [apply t_wf_group_m | apply t_wf_group_other; [exact Hx | exact Hxm]].
    - intros m1 m2 H1 H2. rewrite !e_ai, !e_glast, !e_gsc. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. rewrite e_regions in Hin. rewrite e_is_group, e_kind, e_gmem, e_gml. exact (REG b len x Hin).
    - intros x F. rewrite e_meta_other; [apply FR0; apply e_fresh; exact F|].
      intros ->. apply (wg_notfresh st L m t_wfg). apply e_fresh. exact F.
    - intros x U NG NFL NFR. apply (OTH x); [apply e_metaU; exact U | rewrite <- e_is_group; exact NG
        | rewrite <- e_in_flist; exact NFL | rewrite <- e_fresh; exact NFR].
    - intros x Hl. destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_listed, e_fresh. repeat split; assumption.
    - intros m1 m2 H1 H2 G1 G2 E. apply (ONEFF m1 m2 H1 H2); [intros k Hk | intros k Hk | rewrite !e_gsc in E; exact E].
      + rewrite e_glast in G1. specialize (G1 k Hk). rewrite e_slot in G1. destruct (Z.eqb m1 m && Z.eqb k i)%bool; [destruct G1 as [F|F]; discriminate F | exact G1].
      + rewrite e_glast in G2. specialize (G2 k Hk). rewrite e_slot in G2. destruct (Z.eqb m2 m && Z.eqb k i)%bool; [destruct G2 as [F|F]; discriminate F | exact G2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_slot_ptr : forall x k, (x <> m \/ k <> i) -> slot_ptr st' x k = slot_ptr st x k.
  Proof using. intros x k H. unfold slot_ptr. rewrite e_slot_other by exact H. rewrite e_gss. reflexivity. Qed.
  Lemma e_slot_ptr_mi : slot_ptr st' m i = Some jq.
  Proof using. unfold slot_ptr. rewrite e_slot_mi, e_gss. f_equal. lia. Qed.


  Lemma o_garb : forall a, jq - 3 <= a < g_slot_end st m i -> garbage st m i a.
  Proof using Hslot Hi. intros a Ha. unfold garbage. rewrite Hslot. split; [exact Hi | exact Ha]. Qed.
  Lemma o_hdr_cell : gcell st m (jq - 4).
  Proof using av Hi. unfold gcell. right; left. exists i. split; [unfold g_cnt; lia|]. split; [reflexivity|]. left. unfold g_cnt. lia. Qed.

  Lemma t_gcell_back : forall x a, gcell st' x a -> gcell st x a \/ (x = m /\ jq - 3 <= a < jq).
  Proof using Hi.
    intros x a G. unfold gcell in *.
    rewrite ?e_gmem, ?e_gcnt, ?e_glast in G.
    destruct G as [G | [G | [G | G]]].
    - left. left. exact G.
    - left. right. left. destruct G as (k & Hk & Ha & Hend). exists k. rewrite e_gss in Ha.
      split; [exact Hk|]. split; [exact Ha|]. destruct Hend as [Hend|Hend]; [left; exact Hend | right; apply e_endb; exact Hend].
    - destruct G as (k & q & Hk & Hp & Ha).
      destruct (Z.eq_dec x m) as [->|Hxm].
      + destruct (Z.eq_dec k i) as [->|Hki].
        * rewrite e_slot_ptr_mi in Hp. injection Hp. intros <-.
          destruct (Z.eq_dec a (jq - 4)) as [->|NE]; [left; exact o_hdr_cell | right; split; [reflexivity | lia]].
        * left. right. right. left. exists k, q. rewrite <- (e_slot_ptr m k) by (right; exact Hki). tauto.
      + left. right. right. left. exists k, q. rewrite <- (e_slot_ptr x k) by (left; exact Hxm). tauto.
    - left. right. right. right. destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). exists k, q, n2, o2, r2.
      rewrite e_gse in Ha. split; [exact Hk|]. split; [|exact Ha].
      destruct (Z.eq_dec x m) as [->|Hxm].
      + destruct (Z.eq_dec k i) as [->|Hki]; [rewrite e_slot_mi in Hs; discriminate Hs|].
        rewrite e_slot_other in Hs by (right; exact Hki). exact Hs.
      + rewrite e_slot_other in Hs by (left; exact Hxm). exact Hs.
  Qed.


  Lemma t_appb : forall a, appb st' a <-> appb st a.
  Proof using Hslot Hi.
    intros a. split.
    - intros (x & k & q & n2 & o2 & r2 & Hx & Hk & Hs & Ha). rewrite e_glast in Hk. apply e_is_group in Hx.
      assert (Hne : x <> m \/ k <> i).
      { destruct (Z.eq_dec x m) as [->|]; [right | left; assumption]. intros ->. rewrite e_slot_mi in Hs. discriminate Hs. }
      rewrite e_slot_other in Hs by exact Hne. exists x, k, q, n2, o2, r2. repeat split; try assumption; lia.
    - intros (x & k & q & n2 & o2 & r2 & Hx & Hk & Hs & Ha).
      assert (Hne : x <> m \/ k <> i).
      { destruct (Z.eq_dec x m) as [->|]; [right | left; assumption]. intros ->. rewrite Hslot in Hs. discriminate Hs. }
      exists x, k, q, n2, o2, r2. rewrite e_glast, e_slot_other by exact Hne. split; [apply e_is_group; exact Hx|]. repeat split; try assumption; lia.
  Qed.

  Lemma t_areab : forall a, areab st' a <-> areab st a.
  Proof using Hi. intros a. unfold areab. rewrite e_areas. tauto. Qed.

  Lemma t_garbage_back : forall x k a, garbage st' x k a -> garbage st x k a.
  Proof using Hslot.
    intros x k a G. unfold garbage in *. rewrite e_glast, e_gss, e_gse in G. destruct G as [Hk G].
    destruct (Z.eq_dec x m) as [->|Hxm].
    - destruct (Z.eq_dec k i) as [->|Hki].
      + rewrite e_slot_mi in G. rewrite Hslot. split; [exact Hk | lia].
      + rewrite e_slot_other in G by (right; exact Hki). split; [exact Hk|].
        destruct (s_slot st m k); rewrite ?e_gss, ?e_gspan in G; exact G.
    - rewrite e_slot_other in G by (left; exact Hxm). split; [exact Hk|].
      destruct (s_slot st x k); rewrite ?e_gss, ?e_gspan in G; exact G.
  Qed.
  Lemma t_garbage_mi : forall a, garbage st' m i a -> jq <= a.
  Proof using. intros a G. unfold garbage in G. rewrite e_slot_mi, e_gss in G. lia. Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof using Hslot Hi Hgrp HWF L RN.
    pose proof t_stride as [S16 _].
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN].
    constructor; rewrite ?e_regions.
    - intros x Hx. apply e_is_group in Hx. rewrite e_gmem, e_gspan. exact (INR x Hx).
    - intros m1 m2 a H1 H2 Hne G1 G2. apply e_is_group in H1. apply e_is_group in H2.
      destruct (t_gcell_back m1 a G1) as [G1'|(-> & R1)]; destruct (t_gcell_back m2 a G2) as [G2'|(-> & R2)].
      + exact (CELLS m1 m2 a H1 H2 Hne G1' G2').
      + exact (GC m i a m1 Hgrp (o_garb a ltac:(unfold g_slot_end, IB; lia)) H1 G1').
      + exact (GC m i a m2 Hgrp (o_garb a ltac:(unfold g_slot_end, IB; lia)) H2 G2').
      + exact (Hne eq_refl).
    - intros x a Hx Hr Har. apply e_is_group in Hx. rewrite e_gmem, e_gspan in Hr. apply t_areab in Har. exact (AREA x a Hx Hr Har).
    - intros x a Hx G Ap. apply e_is_group in Hx. apply t_appb in Ap.
      destruct (t_gcell_back x a G) as [G'|(-> & R)]; [exact (APC x a Hx G' Ap) | exact (GA m i a Hgrp (o_garb a ltac:(unfold g_slot_end, IB; lia)) Ap)].
    - intros a Ap Ar. apply t_appb in Ap. apply t_areab in Ar. exact (APA a Ap Ar).
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply e_is_group in H1. apply e_is_group in H2. rewrite e_glast in Hk1, Hk2.
      assert (N1 : m1 <> m \/ k1 <> i).
      { destruct (Z.eq_dec m1 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S1. discriminate S1. }
      assert (N2 : m2 <> m \/ k2 <> i).
      { destruct (Z.eq_dec m2 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S2. discriminate S2. }
      rewrite e_slot_other in S1 by exact N1. rewrite e_slot_other in S2 by exact N2.
      exact (APD m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne).
    - intros x k a x2 Hx G H2 C. apply e_is_group in Hx. apply e_is_group in H2.
      pose proof (t_garbage_back x k a G) as G'.
      destruct (t_gcell_back x2 a C) as [C'|(-> & R)].
      + exact (GC x k a x2 Hx G' H2 C').
      + (* [comment removed for export] *)
        assert (NE : x <> m \/ k <> i).
        { destruct (Z.eq_dec x m) as [->|]; [right|left; assumption]. intros ->. pose proof (t_garbage_mi a G). lia. }
        apply (garbage_private st L HWF x k m i a Hx Hgrp G' Hi); [intros c o E; rewrite Hslot in E; discriminate E | exact NE | unfold g_slot_end, IB; lia].
    - intros x k a Hx G Ap. apply e_is_group in Hx. apply t_appb in Ap. exact (GA x k a Hx (t_garbage_back x k a G) Ap).
    - intros x k a Hx G Ar. apply e_is_group in Hx. apply t_areab in Ar. exact (GAR x k a Hx (t_garbage_back x k a G) Ar).
    - intros x Hx. apply e_is_group in Hx. rewrite e_kind, e_gspan, e_gmem, e_gml.
      pose proof (SPAN x Hx) as S. destruct (s_kind st x); [exact S|]. rewrite e_gss, e_gse. exact S.
  Qed.

  Lemma t_wf_live : wf_live st' L.
  Proof using Hslot Hi HWF RN.
    destruct (WF_live st L HWF) as [IN ND FUN LEN].
    constructor.
    - intros q2 n2 Hin. destruct (IN q2 n2 Hin) as (x & k & o2 & r2 & Hx & Hk & Hs).
      exists x, k, o2, r2. rewrite e_glast. split; [apply e_is_group; exact Hx|]. split; [exact Hk|].
      rewrite e_slot_other; [exact Hs|].
      destruct (Z.eq_dec x m) as [->|]; [right|left; assumption]. intros ->. rewrite Hslot in Hs. discriminate Hs.
    - exact ND.
    - intros m1 i1 m2 i2 q2 n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      apply e_is_group in H1. apply e_is_group in H2. rewrite e_glast in Hk1, Hk2.
      assert (N1 : m1 <> m \/ i1 <> i).
      { destruct (Z.eq_dec m1 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S1. discriminate S1. }
      assert (N2 : m2 <> m \/ i2 <> i).
      { destruct (Z.eq_dec m2 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S2. discriminate S2. }
      rewrite e_slot_other in S1 by exact N1. rewrite e_slot_other in S2 by exact N2.
      exact (FUN m1 i1 m2 i2 q2 n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2).
    - exact LEN.
  Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof using HMav Hslot Hi HWF M' L.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; rewrite ?e_regions, ?e_brk; try assumption.
    - intros b len x Hin. rewrite e_gsc. exact (GB b len x Hin).
    - intros b len x Hin Hx63. rewrite e_gsc in Hx63.
      destruct (G63 b len x Hin Hx63) as [(q & n2 & o2 & r2 & Hs & Hlen) | (o2 & Hs)].
      + left. exists q, n2, o2, r2. split; [|exact Hlen]. rewrite e_slot_other; [exact Hs|].
        destruct (Z.eq_dec x m) as [->|]; [right|left; assumption]. intros <-. rewrite Hslot in Hs. discriminate Hs.
      + rewrite e_slot. destruct (Z.eqb x m && Z.eqb 0 i)%bool; [right; exists 0; reflexivity | right; exists o2; exact Hs].
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof using HWF L RN. apply (wf_img_same st L HWF); reflexivity. Qed.

  Lemma t_WF : WF st' L.
  Proof using HMav Hhead Hslot Hi Hgrp HWF M'.
    split; [exact t_wf_ctx|]. split; [exact t_wf_areas|]. split; [exact t_wf_lists|]. split; [exact t_wf_groups|].
    split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rep_meta_set_avail : forall (Ma Mb : mem) a r av',
    0 <= a -> a + 40 < 2 ^ 64 ->
    agree_on (fun x => (a <= x < a + 24) \/ (a + 28 <= x < a + 40)) Ma Mb ->
    cell Mb (a + 24) 4 av' ->
    rep_meta Ma a r -> rep_meta Mb a (mr_set_avail r av').
  Proof using av m st.
    intros Ma Mb a r av' Ha Hnw Hag Hav [P N Me Av Fr W].
    constructor; cbn; try exact Hav; (eapply cell_agree; [ | | | eassumption]); try (cbn; lia);
      (eapply agree_on_mono; [exact Hag|]); cbn; intros; lia.
  Qed.

  Lemma t_m_area : exists ar k, In ar (s_areas st) /\ 0 <= k < NSLOTS /\ m = meta_addr ar k /\
      ar mod 4096 = 0 /\ HEAPLO <= ar /\ ar + 4096 <= CEIL /\ ar + 24 <= m /\ m + 40 <= ar + 4096.
  Proof using av Hgrp HWF L.
    destruct (metaU_area st L HWF m (wg_U st L m t_wfg)) as (ar & k & A & B & C & D & E & F & G & H & _).
    exists ar, k. repeat split; try assumption; lia.
  Qed.

  Lemma t_agree_low : agree_on (fun a => IMG_LO <= a < IMG_HI) M M'.
  Proof using HMwr Hsp av Hgrp HWF sp m L st RN.
    apply (agree_of_writes sb_wr); [exact HMwr|]. intros a Ha W.
    destruct t_m_area as (ar & k & _ & _ & _ & _ & Har & _ & Hm1 & _).
    hsep; ceil; unfold sb_wr, HEAPLO, MSTK in *. lia.
  Qed.

  Lemma t_agree_area : forall ar a, In ar (s_areas st) -> ar <= a < ar + 4096 -> ~ (m + 24 <= a < m + 28) ->
    M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof using HMwr Hsp av Hgrp HWF sp L RN.
    intros ar a Har Ha Hnot. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
    apply (agree_of_writes sb_wr (fun x => x = a)); [exact HMwr| | hsep; ceil; unfold HEAPLO in *; lia |reflexivity].
    intros b -> W. destruct W as [W|W].
    - ceil; unfold MSTK in *. lia.
    - exact (Hnot W).
  Qed.

  Lemma t_agree_cell : forall x a, is_group st x -> gcell st' x a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof using HMwr Hsp Hi Hgrp HWF sp L RN.
    intros x a Hx G.
    assert (SP : g_mem st x <= a < gspan st x).
    { destruct (t_gcell_back x a G) as [G0|(-> & R)]; [exact (gcell_in_span st L HWF x a Hx G0)|].
      pose proof (gcell_in_span st L HWF m _ Hgrp o_hdr_cell). destruct (group_range st L HWF m Hgrp).
      pose proof (wg_mem st L m t_wfg) as (M1 & _). pose proof t_stride as [S16 _]. pose proof t_last.
      assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
      unfold gspan, g_span_end, g_slot_start, UNIT, IB in *. lia. }
    destruct (group_range st L HWF x Hx) as [R1 R2].
    apply (agree_of_writes sb_wr (fun y => y = a)); [exact HMwr| | hsep; ceil; unfold HEAPLO in *; lia |reflexivity].
    intros b -> W. destruct W as [W|W].
    - ceil; unfold MSTK in *. lia.
    - destruct t_m_area as (ar & k & Har & Hk & Hm & Hal & Hlo & Hhi & H1 & H2).
      apply (ge_area st (WF_geom st L HWF) x a Hx); [lia|]. exists ar. split; [exact Har | lia].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMav HMgrow HMwr Hsp Hi Hgrp HREP HWF sp M L RN.
    pose proof HREP as [ST CX AR GR].
    assert (LOW : forall a k v, IMG_LO <= a /\ a + Z.of_nat k <= IMG_HI -> 0 <= a -> cell M a k v -> cell M' a k v).
    { intros a k v Hk Ha C. eapply cell_agree; [exact Ha | hsep; unfold HEAPLO in *; lia | | exact C].
      eapply agree_on_mono; [exact t_agree_low|]. cbn. intros; lia. }
    constructor.
    - destruct ST; constructor; try (eapply LOW; [cbn; hsep; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, HEAPLO; lia | unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia | eassumption]);
        try (eapply defined_grows; [exact HMgrow | eassumption]).
      + eapply img_clear_agree; [unfold A_TAB_CTZ; lia | unfold A_TAB_CTZ; lia | |eassumption]. eapply agree_on_mono; [exact t_agree_low|]. cbn. hsep; unfold A_TAB_CTZ, HEAPLO. intros; lia.
      + eapply img_clear_agree; [unfold A_TAB_SC; lia | unfold A_TAB_MED; lia | |eassumption]. eapply agree_on_mono; [exact t_agree_low|]. cbn. hsep; unfold A_TAB_SC, A_TAB_MED, HEAPLO. intros; lia.
    - destruct CX; constructor; intros;
        try (eapply LOW; [cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX, HEAPLO; lia
             | unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
             | eauto]);
        try (eapply defined_grows; [exact HMgrow | eassumption]).
    - intros ar Har. change (In ar (s_areas st)) in Har. pose proof (AR ar Har) as [CK NS DF MT].
      destruct t_m_area as (ar0 & k0 & Har0 & Hk0 & Hm & Hal0 & Hlo0 & Hhi0 & H01 & H02).
      destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
      assert (SEP : ar = ar0 \/ ar + 4096 <= ar0 \/ ar0 + 4096 <= ar).
      { destruct (Z.eq_dec ar ar0) as [->|Hne]; [left; reflexivity|right].
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (ar <> ar0) by exact Hne. lia. }
      hsep; ceil; unfold HEAPLO in Hlo, Hhi, Hlo0, Hhi0.
      constructor.
      + eapply cell_agree; [lia | cbn; lia | | exact CK]. intros a Hra Ha. apply (t_agree_area ar); [exact Har | cbn in Ha; lia |].
        cbn in Ha. unfold meta_addr, AREA_HDR, META_SZ in Hm. lia.
      + eapply cell_agree; [lia | cbn; lia | | exact NS]. intros a Hra Ha. apply (t_agree_area ar); [exact Har | cbn in Ha; lia |].
        cbn in Ha. unfold meta_addr, AREA_HDR, META_SZ in Hm. lia.
      + eapply defined_grows; [exact HMgrow | exact DF].
      + intros k Hk. rewrite e_meta. destruct (Z.eqb_spec (meta_addr ar k) m) as [E|NE].
        * rewrite E. apply (rep_meta_set_avail M M' m (s_meta st m) (av - 2 ^ i)); [lia | lia | | exact HMav |].
          -- intros a Hra Ha. apply (t_agree_area ar0); [exact Har0 | lia | lia].
          -- rewrite <- E. exact (MT k Hk).
        * apply (rep_meta_agree M M'); [unfold meta_addr, AREA_HDR, META_SZ; lia | unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia | | exact (MT k Hk)].
          intros a Hra Ha. apply (t_agree_area ar); [exact Har | unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia |].
          unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *.
          destruct SEP as [-> | SEP]; [|lia].
          assert (k <> k0) by (intros ->; apply NE; rewrite Hm; reflexivity). nia.
    - intros x Hx. change (is_group st x) in Hx.
      destruct (group_range st L HWF x Hx) as [R1 R2]. pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
      pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (X1 & X2 & X3).
      assert (SPAN' : forall a, gcell st' x a -> g_mem st x <= a < gspan st x).
      { intros a G. destruct (t_gcell_back x a G) as [G0|(-> & R)]; [exact (gcell_in_span st L HWF x a Hx G0)|].
        pose proof (gcell_in_span st L HWF m _ Hgrp o_hdr_cell).
        pose proof (wg_mem st L m t_wfg) as (M1 & _). pose proof t_stride as [T16 _]. pose proof t_last.
        assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
        unfold gspan, g_span_end, g_slot_start, UNIT, IB in *. lia. }
      apply (rep_group_transportJ st st' M M' x); rewrite ?e_gmem, ?e_gcnt, ?e_glast, ?e_ai, ?e_kind, ?e_gml; try reflexivity.
      + exact (e_gss x).
      + exact (e_gse x).
      + exact (e_inband x).
      + intros E. apply (proj1 (e_endb x)). exact E.
      + destruct (s_kind st x); [split; reflexivity | exact I].
      + intros k Hk. rewrite e_slot. destruct (Z.eqb x m && Z.eqb k i)%bool eqn:B; [right; right; right; exists 0; reflexivity | left; reflexivity].
      + intros a G. apply (t_agree_cell x a Hx G).
      + exact HMgrow.
      + assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; assert (0 <= g_lastidx st x) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia); nia).
        hsep; ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia.
      + intros a G. exact (SPAN' a G).
      + exact (GR x Hx).
  Qed.

  Theorem take_close : WF st' L /\ REP st' M'.
  Proof using HMav HMgrow HMwr Hsp Hhead Hslot Hi Hgrp HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.
End Take.

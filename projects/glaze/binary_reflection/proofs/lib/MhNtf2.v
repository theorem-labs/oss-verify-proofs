(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.MhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.MhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.MhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA.MhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.MhBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.MhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.MhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.MhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf.MhNtfA OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf.MhNtfB OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf.MhNtfC OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf.MhNtfD OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf.MhSub.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac lia_pairs ::= fail.
(* [comment removed for export] *)
Ltac keep_only_disj H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H H' then fail else clear H' end.
Ltac with_disj1 tac := match goal with H : _ \/ _ |- _ => solve [ keep_only_disj H; tac ] end.
Ltac lia_fast ::= first [ solve [ clear_disj; rnfix; zlia ] | solve [ with_disj1 ltac:(rnfix; zlia) ] | lia ].
(* [comment removed for export] *)
Tactic Notation "rpeel" "-" ne_hyp_list(Hs) := rewrite rdn_wbytes_out_Z by (zlen; clear - Hs; zlia).

(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; rnfix; zlia ] | solve [ with_disj1 ltac:(rnfix; zlia) ] | lia ] ].
Section MemHelp2.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma wbytes_get_inside : forall bs (Mb : mem) (addr x : word),
    bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64 ->
    bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + Z.of_nat (length bs) ->
    wbytes Mb addr bs x = nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned addr)).
  Proof using.
    induction bs as [|b rest IH]; intros Mb addr x Hnw Hx; cbn [wbytes length] in *; [lia|].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned addr)) as [E|Hne].
    - assert (Ex : x = addr) by (apply bv_eq; exact E). subst x. rewrite Z.sub_diag. cbn.
      destruct rest as [|b' rest'].
      + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
      + assert (Hu1 : bv_unsigned (addr + 1)%bv = bv_unsigned addr + 1) by (apply u_add1; cbn [length] in Hnw; lia).
        rewrite wbytes_below by (cbn [length] in *; lia). cbv beta. rewrite bv_eqb_refl. reflexivity.
    - destruct rest as [|b' rest']; [cbn [length] in Hx; lia|].
      assert (Hu1 : bv_unsigned (addr + 1)%bv = bv_unsigned addr + 1) by (apply u_add1; cbn [length] in Hnw; lia).
      rewrite IH by (cbn [length] in *; lia). rewrite Hu1.
      replace (Z.to_nat (bv_unsigned x - bv_unsigned addr)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned addr + 1)))) by lia.
      reflexivity.
  Qed.

  Lemma rdn1_in_z8 : forall (Mb : mem) a0 j, 0 <= a0 -> a0 + 8 < 2 ^ 64 -> 0 <= j < 8 ->
    rdn RSEGS (wbytes Mb (Z_to_bv 64 a0) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (a0 + j)) 1%nat = Some [Z_to_bv 8 0].
  Proof using.
    intros Mb a0 j H0 H8 Hj. apply rdn1_of_byte.
    rewrite wbytes_get_inside by (wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
    rewrite !u_Z2bv by lia. replace (a0 + j - a0) with j by lia.
    assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
    destruct E as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; reflexivity.
  Qed.

  Lemma group_bytes_defined : forall stX (L : list (Z * Z)) MX fuel x, WF stX L -> REP stX MX ->
    nest_depth_le stX fuel x -> is_group stX x -> defined MX (g_mem stX x) (gspan stX x).
  Proof using.
    intros stX L0 MX fuel. induction fuel as [|f IH]; intros x W R D Hx; cbn in D.
    - destruct (s_kind stX x) as [|hm j o] eqn:K; [|destruct D].
      pose proof (rg_def stX MX x (rp_groups stX MX R x Hx)) as DF. rewrite K in DF.
      pose proof (ge_span stX (WF_geom stX L0 W) x Hx) as SP. rewrite K in SP.
      intros a Ha. apply DF. lia.
    - destruct (s_kind stX x) as [|hm j o] eqn:K.
      + pose proof (rg_def stX MX x (rp_groups stX MX R x Hx)) as DF. rewrite K in DF.
        pose proof (ge_span stX (WF_geom stX L0 W) x Hx) as SP. rewrite K in SP.
        intros a Ha. apply DF. lia.
      + destruct (span_in_host stX L0 W x hm j o Hx K) as (Hh & _ & LO & HI).
        intros a Ha. apply (IH hm W R D Hh). lia.
  Qed.

  Lemma w2le1 : forall v, 0 <= v < 256 -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
  Proof using. intros v Hv. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u_Z2bv by lia. reflexivity. Qed.
End MemHelp2.

Section FreeArm.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (m i off : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hi : 0 <= i <= g_lastidx st m.
  Hypothesis Hslot : s_slot st m i = SJunk off.
  Hypothesis Hsp : CEIL + 96 <= sp /\ sp < 2 ^ 64 /\ sp mod 16 = 0.
  Hypothesis SOK : store_ok RSEGS M (Z_to_bv 64 (sp - 96)) 96%nat = true.
  Variables (regs : bvmap 5 word) (rom : word -> option byte).
  Hypothesis OJ : only_junk st m i.

  #[local] Notation W := (g_W st m).
  #[local] Notation av := (mr_avail (s_meta st m)).
  #[local] Notation fr := (mr_freed (s_meta st m)).
  #[local] Notation nxt := (mr_next (s_meta st m)).
  #[local] Notation prv := (mr_prev (s_meta st m)).
  #[local] Notation sc := (g_sc st m).
  #[local] Notation mask := (Z.lor av fr).
  #[local] Notation self := (2 ^ i).
  #[local] Notation all := (2 * 2 ^ g_lastidx st m - 1).
  #[local] Notation cx := (s_ctx st).
  #[local] Notation MM1 := (M1 st M sp regs).
  Hypothesis Hall : mask + self = all.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma f_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) m Hgrp). Qed.
  Lemma f_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL /\ m mod 8 = 0.
  Proof using Hgrp HWF L st. exact (metaU_rng st L HWF m (group_metaU st L HWF m Hgrp)). Qed.
  Lemma f_last : 0 <= g_lastidx st m < 32. Proof using. exact (glast_rng st m). Qed.
  Lemma f_sc : 0 <= sc < 64. Proof using sp i. unfold g_sc, w_sizeclass. apply Z.mod_pos_bound. lia. Qed.
  Lemma f_REP1 : REP st MM1. Proof using Hsp HREP HWF L RN. exact (M1_REP st L M sp HWF HREP Hsp regs). Qed.

  (* [comment removed for export] *)
  Lemma f_fj : free_or_junk st m.
  Proof using Hall Hslot Hi Hgrp HWF sp off i L RN.
    pose proof f_wfg as WG. destruct (hd_masks st L m i off 0 HWF Hgrp Hi Hslot) as (AV & FRr & Ta & Tf & Tm). pose proof f_last as HL.
    intros k Hk. destruct (s_slot st m k) as [| |q n o r|c o|o] eqn:Sk; [left; reflexivity | right; left; reflexivity | | | right; right; exists o; reflexivity].
    all: exfalso.
    all: assert (Hki : k <> i) by (intros ->; rewrite Hslot in Sk; discriminate Sk).
    all: assert (TA : Z.testbit av k = false) by
           (destruct (Z.testbit av k) eqn:T; [|reflexivity]; apply (proj1 (wg_av st L m WG k ltac:(lia))) in T; destruct T as [_ T]; rewrite Sk in T; discriminate T).
    all: assert (TF : Z.testbit fr k = false) by
           (destruct (Z.testbit fr k) eqn:T; [|reflexivity]; apply (proj1 (wg_fr st L m WG k ltac:(lia))) in T; destruct T as [_ T]; rewrite Sk in T; discriminate T).
    all: assert (TM : Z.testbit (mask + self) k = false) by
           (rewrite (testbit_add_pow2 mask i k) by (try lia; try exact Tm; apply Z.lor_nonneg; lia);
            rewrite Z.lor_spec, TA, TF; replace (i =? k) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    all: rewrite Hall in TM; replace all with (Z.ones (g_lastidx st m + 1)) in TM
           by (unfold Z.ones; rewrite Z.shiftl_1_l, Z.pow_add_r, Z.pow_1_r by lia; lia);
         rewrite Z.ones_spec_low in TM by lia; discriminate TM.
  Qed.

  (* [comment removed for export] *)
  Definition WRC (MA MB : mem) : Prop :=
    forall a, 0 <= a < 2 ^ 64 -> MB (Z_to_bv 64 a) <> MA (Z_to_bv 64 a) ->
      (exists x, metaU st x /\ x <= a < x + 40) \/ (CTX <= a < CTX_END) \/ (CEIL <= a).

  (* [comment removed for export] *)
  Definition HDR (MX : mem) : Prop :=
    forall hm hi o, s_kind st m = GNest hm hi o ->
      exists rc, 0 <= rc < 8 /\ byte_at MX (g_mem st m - 4) 0 /\ byte_at MX (g_mem st m - 3) (hi + 32 * rc) /\
                 cell MX (g_mem st m - 2) 2 (inband st hm (g_mem st m)).

  (* [comment removed for export] *)
  Definition DQ_POST (d : nat) (r1 : bvmap 5 word) (stD : mst) (MD : mem) (r2 : bvmap 5 word) : Prop :=
    WF stD L /\ REP stD MD /\
    s_brk stD = s_brk st /\ s_limbo stD = m :: s_limbo st /\ s_canary stD = s_canary st /\
    mr_W (s_meta stD m) = mr_W (s_meta st m) /\ mr_mem (s_meta stD m) = mr_mem (s_meta st m) /\
    (s_kind st m = GTop -> Permutation (s_regions st) (rg st m :: s_regions stD) /\ nojunk stD) /\
    (forall hm hi o, s_kind st m = GNest hm hi o ->
        s_regions stD = s_regions st /\ is_group stD hm /\ 0 <= hi <= g_lastidx stD hm /\ s_slot stD hm hi = SJunk o /\
        g_mem st m = g_slot_start stD hm hi + 16 * o /\ g_mem st m + 8 <= g_slot_end stD hm hi /\
        only_junk stD hm hi /\ (forall d', d = S d' -> nest_depth_le stD d' hm)) /\
    getr r2 10 = Z_to_bv 64 m /\ getr r2 18 = Z_to_bv 64 CTX /\ getr r2 2 = Z_to_bv 64 (sp - 96) /\ getr r2 9 = Z_to_bv 64 A_CANARY /\
    keeps_but (clobDQ ++ [11; 13; 14]%bv ++ clobACT) r1 r2 /\
    (forall x, g_mem stD x = g_mem st x) /\ WRC MM1 MD /\ fsub st stD /\
    FR L (sp - 96) (sp - 48) MM1 MD.

  (* [comment removed for export] *)
  Lemma f_nums : 4096 + 24 <= m /\ (m + 40 <= CEIL /\ 140735332483072 <= CEIL <= 140737479966720) /\ m mod 8 = 0 /\
                 0 <= sc < 64 /\ 0 <= g_lastidx st m < 32 /\ CEIL + 96 <= sp /\ sp < 2 ^ 64.
  Proof using Hsp Hgrp HWF i L. pose proof f_rng as R. pose proof f_sc. pose proof f_last. destruct Hsp as (S1 & S2 & _). ceil. unfold HEAPLO in *. repeat split; lia. Qed.


  (* [comment removed for export] *)
  Lemma f_nest : forall hm hi o, s_kind st m = GNest hm hi o ->
    is_group st hm /\ hm <> m /\ 0 <= hi <= g_lastidx st hm /\ s_slot st hm hi = SHost m o /\
    g_mem st m = g_slot_start st hm hi + 16 * o /\ g_mem st m + 8 <= g_slot_end st hm hi /\ g_sc st hm < 48.
  Proof using Hi Hgrp HWF sp i L RN.
    intros hm hi o K. pose proof (wg_kind st L m f_wfg) as KD. rewrite K in KD.
    destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    pose proof (wg_stride st L m f_wfg) as [S16 _].
    split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K6|]. split; [exact K9|]. split; [|exact K8].
    assert (32 <= g_cnt st m * g_stride st m) by nia.
    unfold g_slot_end. rewrite K9. unfold UNIT, IB in *. lia.
  Qed.

  Lemma only_junk_dissolved : forall hm hi o, s_kind st m = GNest hm hi o -> only_junk (MhDissolve.st' st m) hm hi.
  Proof using OJ Hgrp HWF i L RN.
    intros hm hi o K x k o' Hx Hk E. apply MhDissolve.e_is_group in Hx. destruct Hx as [Hx Hxm].
    rewrite MhDissolve.e_glast in Hk. rewrite MhDissolve.e_slot in E.
    destruct (MhDissolve.hslot_cases st L m HWF Hgrp x k) as [[_ E2]|(hm' & hi' & o2 & K' & -> & -> & _)].
    - rewrite E2 in E. destruct (OJ x k o' Hx Hk E) as [Ex _]. exfalso. exact (Hxm Ex).
    - rewrite K in K'. injection K'. intros _ <- <-. split; reflexivity.
  Qed.

  Lemma nojunk_dissolved : s_kind st m = GTop -> nojunk (MhDissolve.st' st m).
  Proof using OJ Hgrp HWF i L RN.
    intros K x k o' Hx Hk E. apply MhDissolve.e_is_group in Hx. destruct Hx as [Hx Hxm].
    rewrite MhDissolve.e_glast in Hk. rewrite MhDissolve.e_slot in E.
    destruct (MhDissolve.hslot_cases st L m HWF Hgrp x k) as [[_ E2]|(hm' & hi' & o2 & K' & _)]; [|rewrite K in K'; discriminate K'].
    rewrite E2 in E. destruct (OJ x k o' Hx Hk E) as [Ex _]. exact (Hxm Ex).
  Qed.

  (* [comment removed for export] *)
  Lemma FRmeta : forall x a, metaU st x -> x <= a < x + 40 -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a.
  Proof using Hsp Hi Hgrp HWF sp i m.
    intros x a Ux Ha. destruct (metaU_area st L HWF x Ux) as (ar & kk & Har & _ & _ & _ & Rlo & Rhi & A1 & A2 & _).
    split; [lia|]. split; [pose proof (metaU_img st L HWF x Ux); lia|]. intros (p & n & Hin & Hpn). destruct (wL_in st L (WF_live st L HWF) p n Hin) as (y & k & o & r & Hy & Hk & Sy).
    apply (ge_app_area st (WF_geom st L HWF) a); [exists y, k, p, n, o, r; repeat split; try assumption; lia | exists ar; split; [exact Har | lia]].
  Qed.

  Lemma WRC_refl : forall MA, WRC MA MA.
  Proof using. intros MA a _ NE. exfalso. exact (NE eq_refl). Qed.

  Lemma WRC_trans : forall MA MB MC, WRC MA MB -> WRC MB MC -> WRC MA MC.
  Proof using.
    intros MA MB MC W1 W2 a Hr NE. destruct (decide (MC (Z_to_bv 64 a) = MB (Z_to_bv 64 a))) as [E|NE2].
    - apply W1; [exact Hr | congruence].
    - apply W2; [exact Hr | exact NE2].
  Qed.

  Lemma WRC_M1 : WRC M MM1.
  Proof using Hsp Hi i m. intros a Hr NE. right; right. pose proof (M1_writes st M sp Hsp regs a Hr NE). destruct Hsp as (S1 & _). lia. Qed.

  Lemma HDR_M : HDR M.
  Proof using Hi Hgrp HREP HWF sp i L RN.
    intros hm hi o K. destruct (f_nest hm hi o K) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    pose proof (rg_slots st M hm (rp_groups st M HREP hm N1) hi N3) as RS. rewrite N4 in RS. cbn [rep_slot] in RS.
    destruct RS as (rc & Hrc & RH). rewrite <- N5 in RH. destruct RH as [B4 B3 B2].
    exists rc. split; [exact Hrc|]. split; [exact B4|]. split; [exact B3 | exact B2].
  Qed.

  Lemma hdr_gcell : forall hm hi o a, s_kind st m = GNest hm hi o -> g_mem st m - 4 <= a < g_mem st m -> gcell st hm a.
  Proof using Hi Hgrp HWF sp i L RN.
    intros hm hi o a K Ha. destruct (f_nest hm hi o K) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    unfold gcell. right. right. left. exists hi, (g_mem st m). unfold slot_ptr. rewrite N4, <- N5. repeat split; lia.
  Qed.

  Lemma HDR_keep : forall MA MB, HDR MA -> WRC MA MB -> HDR MB.
  Proof using Hsp Hi Hgrp HWF sp i L.
    intros MA MB H W hm hi o K. destruct (H hm hi o K) as (rc & Hrc & B4 & B3 & B2).
    destruct (f_nest hm hi o K) as (N1 & _).
    pose proof (gcell_in_span st L HWF hm _ N1 (hdr_gcell hm hi o (g_mem st m - 4) K ltac:(lia))) as X4.
    pose proof (gcell_in_span st L HWF hm _ N1 (hdr_gcell hm hi o (g_mem st m - 1) K ltac:(lia))) as X1.
    destruct (group_range st L HWF hm N1) as [GR1 GR2].
    assert (AG : agree_on (fun a => g_mem st m - 4 <= a < g_mem st m) MA MB).
    { intros a Hr Ha. destruct (decide (MB (Z_to_bv 64 a) = MA (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      pose proof (hdr_gcell hm hi o a K Ha) as G. pose proof (gcell_in_span st L HWF hm a N1 G).
      destruct (W a Hr NE) as [(x & Ux & Hx)|[A|A]].
      - exact (gcell_not_meta st L HWF hm x a N1 G Ux Hx).
      - unfold HEAPLO, CTX_END, CTX in *. lia.
      - ceil. lia. }
    ceil; unfold HEAPLO in *.
    exists rc. split; [exact Hrc|]. split; [|split].
    - eapply byte_agree; [| |exact B4]; [lia|]. eapply agree_on_mono; [exact AG|]. intros a Ha; cbv beta in Ha |- *; lia.
    - eapply byte_agree; [| |exact B3]; [lia|]. eapply agree_on_mono; [exact AG|]. intros a Ha; cbv beta in Ha |- *; lia.
    - eapply cell_agree; [| | |exact B2]; [lia|cbn; lia|]. eapply agree_on_mono; [exact AG|]. intros a Ha; cbv beta in Ha |- *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dq_stage : forall (d : nat) r1,
    nest_depth_le st d m ->
    getr r1 10 = Z_to_bv 64 m -> getr r1 12 = Z_to_bv 64 sc -> getr r1 2 = Z_to_bv 64 (sp - 96) ->
    getr r1 9 = Z_to_bv 64 A_CANARY -> getr r1 18 = Z_to_bv 64 CTX ->
    exists stD MD r2,
      msteps RSEGS (mkst r1 (0x62334%bv : word) MM1 rom) (mkst r2 (0x62448%bv : word) MD rom) /\ DQ_POST d r1 stD MD r2.
  Proof using Hall OJ Hsp Hslot Hi Hgrp HREP HWF off i.
    intros d r1 Hdep C10 C12 C2 C9 C18.
    pose proof f_wfg as WG. pose proof f_nums as (R1 & R2 & R8 & HS & HL & S1 & S2).
    pose proof f_REP1 as HREP1. pose proof f_fj as FJ. pose proof (wg_Wr st L m WG) as WR.
    destruct (hd_masks st L m i off 0 HWF Hgrp Hi Hslot) as (AV & FRr & Ta & Tf & Tm).
    destruct (G_meta_cells st L MM1 HWF HREP1 m Hgrp) as (ar1 & k1 & _ & _ & _ & _ & _ & _ & _ & RM1 & _ & _).
    destruct RM1 as [Rp1 Rn1 Rme1 Rav1 Rfr1 RW1].
    pose proof (meta_store_ok st L MM1 HWF HREP1 m (group_metaU st L HWF m Hgrp)) as SOKm.
    assert (SOKm16 : store_ok RSEGS MM1 (Z_to_bv 64 m) 16%nat = true).
    { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKm | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
    destruct (hd_next st L m i sp HWF Hgrp Hi Hsp) as [NX NXf].
    (* [comment removed for export] *)
    assert (POSTdis : forall MD, WF (MhDissolve.st' st m) L -> REP (MhDissolve.st' st m) MD ->
      WF (MhDissolve.st' st m) L /\ REP (MhDissolve.st' st m) MD /\
      s_brk (MhDissolve.st' st m) = s_brk st /\ s_limbo (MhDissolve.st' st m) = m :: s_limbo st /\ s_canary (MhDissolve.st' st m) = s_canary st /\
      mr_W (s_meta (MhDissolve.st' st m) m) = mr_W (s_meta st m) /\ mr_mem (s_meta (MhDissolve.st' st m) m) = mr_mem (s_meta st m) /\
      (s_kind st m = GTop -> Permutation (s_regions st) (rg st m :: s_regions (MhDissolve.st' st m)) /\ nojunk (MhDissolve.st' st m)) /\
      (forall hm hi o, s_kind st m = GNest hm hi o ->
        s_regions (MhDissolve.st' st m) = s_regions st /\ is_group (MhDissolve.st' st m) hm /\ 0 <= hi <= g_lastidx (MhDissolve.st' st m) hm /\
        s_slot (MhDissolve.st' st m) hm hi = SJunk o /\
        g_mem st m = g_slot_start (MhDissolve.st' st m) hm hi + 16 * o /\ g_mem st m + 8 <= g_slot_end (MhDissolve.st' st m) hm hi /\
        only_junk (MhDissolve.st' st m) hm hi /\ (forall d', d = S d' -> nest_depth_le (MhDissolve.st' st m) d' hm))).
    { intros MD W' R'. split; [exact W'|]. split; [exact R'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split.
      - intros K. split; [exact (dissolve_top st L m HWF Hgrp K) | exact (nojunk_dissolved K)].
      - intros hm hi o K. destruct (dissolve_hostslot st L m HWF Hgrp FJ hm hi o K) as (G1 & G2 & G3 & G4).
        destruct (f_nest hm hi o K) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
        split; [exact (dissolve_nest st m hm hi o K)|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
        split; [exact N6|]. split; [exact (only_junk_dissolved hm hi o K)|].
        intros d' ->. apply MhDissolve.e_depth. cbn in Hdep. rewrite K in Hdep. exact Hdep. }
    destruct (Z.eq_dec nxt 0) as [NX0|NX0].
    - (* [comment removed for export] *)
      pose proof Rn1 as Rn0. rewrite NX0 in Rn0.
      destruct (segL0 MM1 m nxt ltac:(ceil; unfold HEAPLO; lia) Rn1 r1 rom C10 NX0) as (r2 & RUN2 & K2).
      assert (NI : MhDissolve.inl st m = false).
      { apply MhDissolve.inl_false. intros I. destruct (alist_member st L HWF sc m I) as (_ & _ & _ & _ & Lm).
        destruct (wl_linked st (WF_lists st L HWF) m Lm) as [N _]. exact (N NX0). }
      assert (NM : MhDissolve.multi st m = false) by (unfold MhDissolve.multi; rewrite NI; reflexivity).
      assert (PV0 : prv = 0).
      { destruct (wl_link st (WF_lists st L HWF) m (group_metaU st L HWF m Hgrp)) as [_ P]; [|exact P].
        intros Lm. destruct (wl_linked st (WF_lists st L HWF) m Lm) as [N _]. exact (N NX0). }
      pose proof Rp1 as Rp0. rewrite PV0 in Rp0.
      destruct (dissolve_close st L MM1 MM1 m (CEIL + MSTK) HWF HREP1 Hgrp FJ ltac:(lia)
                  ltac:(intros a _ NE; exfalso; exact (NE eq_refl)) (mem_grows_refl _) Rp0 Rn0
                  ltac:(intros X; rewrite NM in X; discriminate X) ltac:(intros X; rewrite NM in X; discriminate X)
                  ltac:(intros X; rewrite NI in X; discriminate X)) as [W' R'].
      exists (MhDissolve.st' st m), MM1, r2. split; [exact RUN2|].
      destruct (POSTdis MM1 W' R') as (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8).
      unfold DQ_POST. repeat (split; [assumption|]).
      split; [kept_rw K2; exact C10|]. split; [kept_rw K2; exact C18|]. split; [kept_rw K2; exact C2|]. split; [kept_rw K2; exact C9|].
      split; [eapply keeps_but_mono; [exact K2 | intros r Hr; cbn in Hr |- *; tauto]|].
      split; [intros; reflexivity|]. split; [apply WRC_refl|]. split; [apply fsub_dissolve|].
      apply FR_refl.
    - (* [comment removed for export] *)
      destruct (NXf NX0) as (Im & In_ & S48).
      assert (IL : MhDissolve.inl st m = true) by (apply MhDissolve.inl_true; exact Im).
      set (hd := c_active cx sc).
      assert (Ehd : hd = head_of (s_alist st sc)) by (subst hd; apply (wc_active st (WF_ctx st L HWF)); lia).
      pose proof (rc_active st MM1 (rp_ctx st MM1 HREP1) sc ltac:(lia)) as HDc. fold hd in HDc.
      assert (HDr : 0 <= hd < 2 ^ 64).
      { rewrite Ehd. destruct (s_alist st sc) as [|a l] eqn:El; cbn; [lia|].
        assert (Ia : In a (s_alist st sc)) by (rewrite El; left; reflexivity).
        destruct (alist_member st L HWF sc a Ia) as (_ & _ & _ & Ua & _). destruct (metaU_rng st L HWF a Ua). ceil; unfold HEAPLO in *. lia. }
      destruct (segDQ_pfx MM1 m sc nxt hd ltac:(ceil; unfold HEAPLO; lia) HS NX Rn1 HDc r1 rom C10 C12 C18 NX0 (proj2 S48))
        as (r2 & RUN2 & D10 & D11 & D12 & D13 & D18 & K2).
      pose proof (wl_adll st (WF_lists st L HWF) sc ltac:(lia)) as Dl.
      pose proof (proj1 (NoDup_ListNoDup _) (wl_anodup st (WF_lists st L HWF) sc)) as NDl.
      destruct (Z.eq_dec nxt m) as [NXm|NXm].
      + (* [comment removed for export] *)
        assert (NM : MhDissolve.multi st m = false).
        { destruct (MhDissolve.multi st m) eqn:E; [|reflexivity]. exfalso.
          apply (proj1 (MhDissolve.multi_nxt st L m HWF IL) E). exact NXm. }
        assert (Lm : s_alist st sc = [m]).
        { pose proof (proj1 (dllf_self_iff _ _ _ m (proj1 (dll_dllf st _) Dl) NDl Im) NXm) as Z1.
          destruct (s_alist st sc) as [|a [|b l2]] eqn:El; [destruct Im | | rewrite !zlen_cons in Z1; pose proof (zlen_nonneg l2); lia].
          destruct Im as [<-|[]]. reflexivity. }
        assert (El' : MhDissolve.l' st m = []) by (unfold MhDissolve.l'; rewrite Lm; cbn; rewrite Z.eqb_refl; reflexivity).
        assert (SOKa : store_ok RSEGS MM1 (Z_to_bv 64 (ctx_active sc)) 8%nat = true).
        { eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact (ctx_store_ok st MM1 HREP1) | | ]; unfold ctx_active, CTX; rewrite ?u_Z2bv by lia; cbn; lia. }
        destruct (segDQs MM1 m sc nxt hd ltac:(ceil; unfold HEAPLO; lia) HS HDr SOKm16 SOKa ltac:(rewrite NXm; ceil; unfold HEAPLO; lia) r2 rom D10 D11 D12 D13 NXm) as (r3 & RUN3 & K3).
        destruct (dissolve_close st L MM1 (m_dqs MM1 m sc) m (CEIL + MSTK) HWF HREP1 Hgrp FJ ltac:(lia)) as [W' R'].
        { intros a Hr NE. unfold MhDissolve.d_wr. rewrite IL.
          unfold m_dqs, ctx_active, CTX in NE.
          assert (W3 : (m <= a < m + 16) \/ (682024 + 80 + 8 * sc <= a < 682024 + 80 + 8 * sc + 8)).
          { revert NE. generalize MM1. intros Mb NE. wdiff NE Mb a. }
          destruct W3 as [A|A]; [right; left; split; [reflexivity | exact A] | right; right; right; split; [reflexivity|]].
          unfold ctx_active, CTX. exact A. }
        { unfold m_dqs. do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
        { unfold cell, m_dqs, ctx_active, CTX. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
        { unfold cell, m_dqs, ctx_active, CTX. apply rdn_wbytes_hit8. zsimp; lia. }
        { intros X. rewrite NM in X. discriminate X. }
        { intros X. rewrite NM in X. discriminate X. }
        { intros _. rewrite El'. cbn [head_of]. unfold cell, m_dqs, ctx_active, CTX. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
        exists (MhDissolve.st' st m), (m_dqs MM1 m sc), r3.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3]|].
        destruct (POSTdis _ W' R') as (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8).
        unfold DQ_POST. repeat (split; [assumption|]).
        split; [kept_rw K3; exact D10|]. split; [kept_rw K3; exact D18|]. split; [kept_rw K3; kept_rw K2; exact C2|]. split; [kept_rw K3; kept_rw K2; exact C9|].
        split; [eapply keeps_but_mono; [eapply keeps_but_trans; [exact K2 | eapply keeps_but_mono; [exact K3|]; intros r Hr; cbn in Hr |- *; clear - Hr; tauto] | intros r Hr; cbn in Hr |- *; clear - Hr; tauto]|].
        split; [intros; reflexivity|]. split.
        { intros a Hr NE. unfold m_dqs, ctx_active, CTX in NE.
          assert (W3 : (m <= a < m + 16) \/ (682024 + 80 + 8 * sc <= a < 682024 + 80 + 8 * sc + 8)).
          { revert NE. generalize MM1. intros Mb NE. wdiff NE Mb a. }
          destruct W3 as [A|A]; [left; exists m; split; [exact (group_metaU st L HWF m Hgrp) | lia] | right; left; unfold CTX_END, CTX; lia]. }
        split; [apply fsub_dissolve|].
        split; [unfold m_dqs; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
        intros a Hr NE. unfold m_dqs, ctx_active, CTX in NE.
        assert (W3 : (m <= a < m + 16) \/ (682024 + 80 + 8 * sc <= a < 682024 + 80 + 8 * sc + 8)).
        { revert NE. generalize MM1. intros Mb NE. wdiff NE Mb a. }
        destruct W3 as [A|A].
        * right; left. apply (FRmeta m); [exact (group_metaU st L HWF m Hgrp) | lia].
        * right; right. unfold CTX_END, CTX. lia.
      + (* [comment removed for export] *)
        assert (MU : MhDissolve.multi st m = true) by (apply (MhDissolve.multi_nxt st L m HWF IL); exact NXm).
        destruct (dllf_links_In _ _ _ m (proj1 (dll_dllf st _) Dl) Im) as [_ Ip].
        destruct (alist_member st L HWF sc nxt In_) as (_ & Gn & SCn & Un & Ln).
        destruct (alist_member st L HWF sc prv Ip) as (_ & Gp & _ & Up & Lp).
        assert (NPm : prv <> m) by (apply (MhDissolve.multi_prv st L m HWF IL); exact MU).
        destruct (metaU_rng st L HWF nxt Un) as (Hn1 & Hn2 & Hn8). destruct (metaU_rng st L HWF prv Up) as (Hp1 & Hp2 & _).
        pose proof (metaU_sep st L HWF m nxt (group_metaU st L HWF m Hgrp) Un (fun E => NXm (eq_sym E))) as SEPn.
        pose proof (metaU_sep st L HWF m prv (group_metaU st L HWF m Hgrp) Up (fun E => NPm (eq_sym E))) as SEPp.
        assert (NP : nxt = prv \/ nxt + 40 <= prv \/ prv + 40 <= nxt).
        { destruct (Z.eq_dec nxt prv) as [E|NE]; [left; exact E | right; exact (metaU_sep st L HWF nxt prv Un Up NE)]. }
        ceil; unfold HEAPLO in Hn1, Hn2, Hp1, Hp2.
        assert (PRr : 0 <= prv < 2 ^ 64) by lia.
        pose proof (meta_store_ok st L MM1 HWF HREP1 nxt Un) as SOKn40. pose proof (meta_store_ok st L MM1 HWF HREP1 prv Up) as SOKp40.
        assert (SOKn : store_ok RSEGS MM1 (Z_to_bv 64 nxt) 8%nat = true).
        { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKn40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
        assert (SOKp : store_ok RSEGS MM1 (Z_to_bv 64 (prv + 8)) 8%nat = true).
        { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKp40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
        destruct (MhDissolve.l_split st L m HWF IL) as (l1 & l2 & El & El' & N1 & N2).
        (* [comment removed for export] *)
        assert (DQwr : forall MD, (forall a, 0 <= a < 2 ^ 64 -> MD (Z_to_bv 64 a) <> MM1 (Z_to_bv 64 a) ->
                   (m <= a < m + 16) \/ (prv + 8 <= a < prv + 16) \/ (nxt <= a < nxt + 8) \/ (ctx_active sc <= a < ctx_active sc + 8)) ->
                   (forall a, 0 <= a < 2 ^ 64 -> MD (Z_to_bv 64 a) <> MM1 (Z_to_bv 64 a) -> MhDissolve.d_wr st m (CEIL + MSTK) a) /\
                   ((mem_grows MM1 MD -> FR L (sp - 96) (sp - 48) MM1 MD) /\ WRC MM1 MD)).
        { intros MD W. split; [|split].
          - intros a Hr NE. unfold MhDissolve.d_wr. rewrite IL, MU. destruct (W a Hr NE) as [A|[A|[A|A]]].
            + right; left. split; [reflexivity | exact A].
            + right; right; left. split; [reflexivity | left; exact A].
            + right; right; left. split; [reflexivity | right; exact A].
            + right; right; right. split; [reflexivity | exact A].
          - intros G. split; [exact G|]. intros a Hr NE. destruct (W a Hr NE) as [A|[A|[A|A]]].
            + right; left. apply (FRmeta m); [exact (group_metaU st L HWF m Hgrp) | lia].
            + right; left. apply (FRmeta prv); [exact Up | lia].
            + right; left. apply (FRmeta nxt); [exact Un | lia].
            + right; right. unfold ctx_active, CTX_END, CTX in *. lia.
          - intros a Hr NE. destruct (W a Hr NE) as [A|[A|[A|A]]].
            + left. exists m. split; [exact (group_metaU st L HWF m Hgrp) | lia].
            + left. exists prv. split; [exact Up | lia].
            + left. exists nxt. split; [exact Un | lia].
            + right; left. unfold ctx_active, CTX_END, CTX in *. lia. }
        destruct (Z.eq_dec hd m) as [Hhm|Hhm].
        * (* [comment removed for export] *)
          assert (Ehd' : head_of (MhDissolve.l' st m) = nxt).
          { destruct (MhDissolve.head_l' st L m HWF IL l1 l2 El El') as [(A & B & C)|(A & B & C)]; [|exfalso; apply C; rewrite <- Ehd; exact Hhm].
            rewrite C. subst l1. cbn [app] in El. pose proof Dl as D2. rewrite El in D2. apply (proj1 (dll_dllf st _)) in D2.
            assert (Hl2 : l2 <> []).
            { intros E2. apply (proj1 (MhDissolve.multi_iff st m) MU). fold (g_sc st m). rewrite El, E2. reflexivity. }
            rewrite (head_of_znth l2 Hl2). symmetry. apply (dllf_remove_head _ _ l2 m D2). apply zlen_pos. exact Hl2. }
          assert (SOKa : store_ok RSEGS MM1 (Z_to_bv 64 (ctx_active sc)) 8%nat = true).
          { eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact (ctx_store_ok st MM1 HREP1) | | ]; unfold ctx_active, CTX; rewrite ?u_Z2bv by lia; cbn; lia. }
          destruct (segDQh MM1 m sc nxt prv hd ltac:(ceil; unfold HEAPLO; lia) HS NX PRr Rn1 Rp1 HDc SOKm16 SOKa
                      ltac:(ceil; unfold HEAPLO; lia) ltac:(ceil; unfold HEAPLO; lia) SEPn SEPp SOKn SOKp r2 rom D10 D11 D12 D13 NXm Hhm)
            as (r3 & RUN3 & E11 & K3).
          set (M2 := m_dqh MM1 m sc nxt prv) in RUN3.
          assert (W5 : forall a, 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) <> MM1 (Z_to_bv 64 a) ->
                      (m <= a < m + 16) \/ (prv + 8 <= a < prv + 16) \/ (nxt <= a < nxt + 8) \/ (ctx_active sc <= a < ctx_active sc + 8)).
          { intros a Hr NE. unfold M2, m_dqh, ctx_active, CTX in NE. unfold ctx_active, CTX. revert NE. generalize MM1. intros Mb NE. wdiff NE Mb a. }
          destruct (DQwr _ W5) as (DW & DF & DC).
          assert (G2 : mem_grows MM1 M2) by (unfold M2, m_dqh; do 5 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
          destruct (dissolve_close st L MM1 M2 m (CEIL + MSTK) HWF HREP1 Hgrp FJ ltac:(lia) DW G2) as [W' R'].
          { unfold cell, M2, m_dqh. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          { unfold cell, M2, m_dqh. apply rdn_wbytes_hit8. zsimp; lia. }
          { intros _. unfold cell, M2, m_dqh, ctx_active, CTX. do 4 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          { intros _. unfold cell, M2, m_dqh, ctx_active, CTX. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          { intros _. rewrite Ehd'. unfold cell, M2, m_dqh, ctx_active, CTX. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          set (stD0 := MhDissolve.st' st m) in W', R'.
          (* [comment removed for export] *)
          destruct (meta_cells st L MM1 HWF HREP1 nxt Un) as (arn & kn & _ & _ & _ & _ & _ & _ & RMn & _).
          destruct RMn as [Qp Qn Qme Qav Qfr QW].
          destruct (wl_rest st (WF_lists st L HWF) sc nxt In_ ltac:(rewrite <- Ehd, Hhm; exact NXm)) as [AVn FRn].
          rewrite AVn in Qav.
          pose proof (wG_each st L (WF_groups st L HWF) nxt Gn) as WGn.
          destruct (rg_aidx st MM1 nxt (rp_groups st MM1 HREP1 nxt Gn)) as (b & Hb & Bat & Bmod).
          pose proof (wg_ai st L nxt WGn) as AIr. pose proof (glast_rng st nxt) as GLn. pose proof (wg_frr st L nxt WGn) as FRr_n.
          destruct (group_range st L HWF nxt Gn) as [GR1 GR2]. pose proof (MhDissolve.span_nonempty st L HWF nxt Gn) as SPn.
          assert (GC8 : gcell st nxt (g_mem st nxt + 8)) by (unfold gcell; left; lia).
          pose proof (gcell_not_meta st L HWF nxt m _ Gn GC8 (group_metaU st L HWF m Hgrp)) as NG1.
          pose proof (gcell_not_meta st L HWF nxt nxt _ Gn GC8 Un) as NG2.
          pose proof (gcell_not_meta st L HWF nxt prv _ Gn GC8 Up) as NG3.
          ceil; unfold HEAPLO in GR1, GR2.
          assert (SOKh : store_ok RSEGS M2 (Z_to_bv 64 (nxt + 24)) 8%nat = true).
          { eapply store_ok_mono; [exact G2|]. eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKn40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
          destruct (segACT M2 nxt (g_mem st nxt) b (mr_freed (s_meta st nxt)) ltac:(ceil; unfold HEAPLO; lia) ltac:(ceil; unfold HEAPLO; lia) Hb FRr_n)
            with (regs := r3) (rom := rom) as (r4 & RUN4 & K4).
          { unfold M2, m_dqh, ctx_active, CTX. pose proof (metaU_img st L HWF nxt Un) as IMn.
            do 5 (rpeel - NP SEPn SEPp Hn1 Hn2 Hp1 Hp2 R1 R2 S48 IMn). exact Qav. }
          { unfold M2, m_dqh, ctx_active, CTX. pose proof (metaU_img st L HWF nxt Un) as IMn.
            do 5 (rpeel - NP SEPn SEPp Hn1 Hn2 Hp1 Hp2 R1 R2 S48 IMn). exact Qme. }
          { unfold M2, m_dqh, ctx_active, CTX. pose proof (group_img st L HWF nxt Gn) as [IGn _].
            do 5 (rpeel - NG1 NG2 NG3 GR1 GR2 SPn IGn Hn1 Hn2 Hp1 Hp2 R1 R2 S48). apply byte_at_rdn1. exact Bat. }
          { unfold M2, m_dqh, ctx_active, CTX. pose proof (metaU_img st L HWF nxt Un) as IMn.
            do 5 (rpeel - NP SEPn SEPp Hn1 Hn2 Hp1 Hp2 R1 R2 S48 IMn). exact Qfr. }
          { exact SOKh. }
          { exact E11. }
          set (M3 := m_act M2 nxt b (mr_freed (s_meta st nxt))) in RUN4.
          assert (W6 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) <> M2 (Z_to_bv 64 a) -> nxt + 24 <= a < nxt + 32).
          { intros a Hr NE. unfold M3, m_act in NE. revert NE. generalize M2. intros Mb NE. wdiff NE Mb a. }
          assert (G3 : mem_grows M2 M3) by (unfold M3, m_act; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
          destruct (activate_close stD0 L M2 M3 nxt (CEIL + MSTK) W' R') as [W'' R''].
          { subst stD0. apply MhDissolve.e_is_group. split; [exact Gn | exact NXm]. }
          { subst stD0. rewrite MhDissolve.e_gsc, SCn, MhDissolve.e_alist_sc, Ehd'. reflexivity. }
          { subst stD0. rewrite MhDissolve.e_avail. exact AVn. }
          { lia. }
          { intros a Hr NE. unfold MhActivate.a_wr. right. exact (W6 a Hr NE). }
          { exact G3. }
          { unfold cell, M3, m_act, MhActivate.av'. subst stD0. rewrite MhDissolve.e_freed, MhDissolve.e_ai, <- Bmod.
            pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 (lo_bits (mr_freed (s_meta st nxt)) (b mod 32 + 1))))) as RH.
            rewrite length_N_to_le_bytes in RH. apply RH. rewrite u_Z2bv by lia. lia. }
          { unfold cell, M3, m_act, MhActivate.fr'. subst stD0. rewrite MhDissolve.e_freed, MhDissolve.e_ai, <- Bmod.
            rdn_peel1.
            pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 (hi_bits (mr_freed (s_meta st nxt)) (b mod 32 + 1))))) as RH.
            rewrite length_N_to_le_bytes in RH. apply RH. rewrite u_Z2bv by lia. lia. }
          exists (MhActivate.st' stD0 nxt), M3, r4.
          split; [eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]|].
          destruct (POSTdis _ W' R') as (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8). fold stD0 in P3, P4, P5, P6, P7, P8.
          unfold DQ_POST. split; [exact W''|]. split; [exact R''|].
          split; [exact P3|]. split; [rewrite MhActivate.e_limbo; exact P4|]. split; [exact P4c|].
          split; [rewrite (MhActivate.e_meta_other stD0 nxt m (fun E => NXm (eq_sym E))); exact P5|].
          split; [rewrite (MhActivate.e_meta_other stD0 nxt m (fun E => NXm (eq_sym E))); exact P6|].
          split.
          { intros K. destruct (P7 K) as [PR NJ]. split; [rewrite MhActivate.e_regions; exact PR|].
            intros x k o' Hx Hk E. apply MhActivate.e_is_group in Hx. rewrite MhActivate.e_glast in Hk. rewrite MhActivate.e_slot in E.
            destruct (MhActivate.a_slot_cases stD0 nxt x k) as [[E2 _]|(_ & _ & _ & E2)]; rewrite E2 in E; [exact (NJ x k o' Hx Hk E) | discriminate E]. }
          split.
          { intros hm hi o' K. destruct (P8 hm hi o' K) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
            rewrite MhActivate.e_regions, MhActivate.e_glast, MhActivate.e_slot, MhActivate.e_gss, MhActivate.e_gse.
            split; [exact Q1|]. split; [apply MhActivate.e_is_group; exact Q2|]. split; [exact Q3|]. split.
            { destruct (MhActivate.a_slot_cases stD0 nxt hm hi) as [[E2 _]|(_ & _ & SF2 & E2)]; rewrite E2; [exact Q4|]. rewrite Q4 in SF2. discriminate SF2. }
            split; [exact Q5|]. split; [exact Q6|]. split.
            - intros x k o2 Hx Hk E. apply MhActivate.e_is_group in Hx. rewrite MhActivate.e_glast in Hk. rewrite MhActivate.e_slot in E.
              destruct (MhActivate.a_slot_cases stD0 nxt x k) as [[E2 _]|(_ & _ & _ & E2)]; rewrite E2 in E; [exact (Q7 x k o2 Hx Hk E) | discriminate E].
            - intros d' Ed. apply (x_depth stD0 (MhActivate.st' stD0 nxt) (MhActivate.SLa stD0 nxt)). exact (Q8 d' Ed). }
          split; [kept_rw K4; kept_rw K3; exact D10|]. split; [kept_rw K4; kept_rw K3; exact D18|].
          split; [kept_rw K4; kept_rw K3; kept_rw K2; exact C2|]. split; [kept_rw K4; kept_rw K3; kept_rw K2; exact C9|].
          split.
          { exact (keeps_join _ _ r1 r2 r4 K2 (keeps_join _ _ r2 r3 r4 K3 K4)). }
          split; [intros; rewrite MhActivate.e_gmem; reflexivity|].
          split.
          { eapply WRC_trans; [exact DC|]. intros a Hr NE. left. exists nxt. split; [exact Un | pose proof (W6 a Hr NE); lia]. }
          split; [eapply fsub_trans; [apply fsub_dissolve | apply fsub_activate]|].
          eapply FR_trans; [apply DF; exact G2|].
          split; [exact G3|]. intros a Hr NE. right; left. apply (FRmeta nxt); [exact Un | pose proof (W6 a Hr NE); lia].
        * (* [comment removed for export] *)
          assert (Ehd' : head_of (MhDissolve.l' st m) = hd).
          { destruct (MhDissolve.head_l' st L m HWF IL l1 l2 El El') as [(A & B & C)|(A & B & C)]; [|rewrite B; symmetry; exact Ehd].
            exfalso. apply Hhm. rewrite Ehd. exact B. }
          destruct (segDQn MM1 m sc nxt prv hd ltac:(ceil; unfold HEAPLO; lia) HS NX PRr HDr Rn1 Rp1 HDc SOKm16
                      ltac:(ceil; unfold HEAPLO; lia) ltac:(ceil; unfold HEAPLO; lia) SEPn SEPp SOKn SOKp r2 rom D10 D11 D12 D13 NXm Hhm)
            as (r3 & RUN3 & K3).
          assert (W4 : forall a, 0 <= a < 2 ^ 64 -> m_dqn MM1 m nxt prv (Z_to_bv 64 a) <> MM1 (Z_to_bv 64 a) ->
                      (m <= a < m + 16) \/ (prv + 8 <= a < prv + 16) \/ (nxt <= a < nxt + 8) \/ (ctx_active sc <= a < ctx_active sc + 8)).
          { intros a Hr NE. unfold m_dqn in NE. revert NE. generalize MM1. intros Mb NE. wdiff NE Mb a. }
          destruct (DQwr _ W4) as (DW & DF & DC).
          destruct (dissolve_close st L MM1 (m_dqn MM1 m nxt prv) m (CEIL + MSTK) HWF HREP1 Hgrp FJ ltac:(lia) DW) as [W' R'].
          { unfold m_dqn. do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
          { unfold cell, m_dqn. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          { unfold cell, m_dqn. apply rdn_wbytes_hit8. zsimp; lia. }
          { intros _. unfold cell, m_dqn. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          { intros _. unfold cell, m_dqn. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
          { intros _. rewrite Ehd'. unfold cell, m_dqn, ctx_active, CTX in *. do 4 rdn_peel1. exact HDc. }
          exists (MhDissolve.st' st m), (m_dqn MM1 m nxt prv), r3.
          split; [eapply msteps_trans; [exact RUN2 | exact RUN3]|].
          destruct (POSTdis _ W' R') as (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8).
          unfold DQ_POST. repeat (split; [assumption|]).
          split; [kept_rw K3; exact D10|]. split; [kept_rw K3; exact D18|]. split; [kept_rw K3; kept_rw K2; exact C2|]. split; [kept_rw K3; kept_rw K2; exact C9|].
          split; [eapply keeps_but_mono; [eapply keeps_but_trans; [exact K2 | eapply keeps_but_mono; [exact K3|]; intros r Hr; cbn in Hr |- *; clear - Hr; tauto] | intros r Hr; cbn in Hr |- *; clear - Hr; tauto]|].
          split; [intros; reflexivity|]. split; [exact DC|]. split; [apply fsub_dissolve|].
          apply DF. unfold m_dqn. do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition spF : Z := Z.max (sp - 48) (CEIL + MSTK).
  Lemma spF_ok : CEIL + MSTK <= spF /\ sp - 48 <= spF /\ spF - MSTK <= sp - 96.
  Proof using Hsp Hi i m st. ceil; unfold spF, MSTK in *. destruct Hsp as (S1 & _). lia. Qed.

  Lemma fm_stage : forall lo stP MP rP (base len : word),
    lo <= sp - 96 ->
    WF stP L -> REP stP MP -> In m (s_limbo stP) -> s_canary stP = s_canary st ->
    getr rP 10 = Z_to_bv 64 m -> getr rP 2 = Z_to_bv 64 (sp - 96) -> getr rP 18 = Z_to_bv 64 CTX -> getr rP 9 = Z_to_bv 64 A_CANARY ->
    getr rP 12 = base -> getr rP 11 = len -> ret_ok (getr regs 1) ->
    FR L lo (sp - 48) MM1 MP -> mem_grows M MP ->
    exists st' M' r',
      msteps RSEGS (mkst rP (0x62504%bv : word) MP rom) (mkst r' (getr regs 1) M' rom) /\
      WF st' L /\ REP st' M' /\ s_brk st' = s_brk stP /\ s_limbo st' = zremove m (s_limbo stP) /\ s_regions st' = s_regions stP /\
      s_canary st' = s_canary stP /\
      (forall x k o, is_group st' x -> 0 <= k <= g_lastidx st' x -> s_slot st' x k = SJunk o ->
                     is_group stP x /\ 0 <= k <= g_lastidx stP x /\ s_slot stP x k = SJunk o) /\
      getr r' 10 = base /\ getr r' 11 = len /\
      getr r' 1 = getr regs 1 /\ getr r' 2 = Z_to_bv 64 sp /\ getr r' 8 = getr regs 8 /\ getr r' 9 = getr regs 9 /\
      getr r' 18 = getr regs 18 /\ getr r' 19 = getr regs 19 /\
      keeps_but ([13; 18]%bv ++ clobE) rP r' /\ fsub stP st' /\ FR L lo (sp - 48) MM1 M'.
  Proof using SOK Hsp Hi Hgrp HWF i.
    intros lo stP MP rP base len Hlo WFP REPP Lim Ecan P10 P2 P18 P9 P12 P11 RET FRP GP.
    pose proof f_nums as (R1 & R2 & R8 & HS & HL & S1 & S2). pose proof spF_ok as (F1 & F2 & F3).
    destruct (wG_limbo stP L (WF_groups stP L WFP) m Lim) as (Um & NGm & NLm & NFm).
    destruct (M1_saved st M sp Hsp regs) as (SV1 & SV8 & SV9 & SV18 & SV19 & SVc).
    pose proof (meta_store_ok stP L MP WFP REPP m Um) as SOKm.
    assert (SOKsp : store_ok RSEGS MP (Z_to_bv 64 (sp - 96)) 48%nat = true).
    { eapply store_ok_mono; [exact GP|]. eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
    set (l := s_flist stP). set (fh := c_free_head (s_ctx stP)).
    assert (Efh : fh = head_of l) by (subst fh l; exact (wc_fhead stP (WF_ctx stP L WFP))).
    pose proof (rc_fmh stP MP (rp_ctx stP MP REPP)) as Cfh. fold fh in Cfh.
    assert (FHr : 0 <= fh < 2 ^ 64 /\ (fh <> 0 -> l <> [] /\ In fh l)).
    { rewrite Efh. destruct l as [|a l2] eqn:El; cbn; [lia|].
      assert (Ia : In a (s_flist stP)) by (fold l; rewrite El; left; reflexivity).
      destruct (wl_fU stP (WF_lists stP L WFP) a Ia) as (Ua & _). destruct (metaU_rng stP L WFP a Ua). ceil; unfold HEAPLO in *.
      split; [lia|]. intros _. split; [congruence | left; reflexivity]. }
    destruct FHr as [FHr FHin].
    (* [comment removed for export] *)
    assert (FIN : forall (r5 : bvmap 5 word) (M5 : mem),
      msteps RSEGS (mkst rP (0x62504%bv : word) MP rom) (mkst r5 (0x625c8%bv : word) M5 rom) ->
      keeps_but [13; 18]%bv rP r5 ->
      WF (MhFreeMeta.st' stP m) L -> REP (MhFreeMeta.st' stP m) M5 ->
      FR L lo (sp - 48) MM1 M5 ->
      exists st' M' r',
        msteps RSEGS (mkst rP (0x62504%bv : word) MP rom) (mkst r' (getr regs 1) M' rom) /\
        WF st' L /\ REP st' M' /\ s_brk st' = s_brk stP /\ s_limbo st' = zremove m (s_limbo stP) /\ s_regions st' = s_regions stP /\
        s_canary st' = s_canary stP /\
        (forall x k o, is_group st' x -> 0 <= k <= g_lastidx st' x -> s_slot st' x k = SJunk o ->
                       is_group stP x /\ 0 <= k <= g_lastidx stP x /\ s_slot stP x k = SJunk o) /\
        getr r' 10 = base /\ getr r' 11 = len /\
        getr r' 1 = getr regs 1 /\ getr r' 2 = Z_to_bv 64 sp /\ getr r' 8 = getr regs 8 /\ getr r' 9 = getr regs 9 /\
        getr r' 18 = getr regs 18 /\ getr r' 19 = getr regs 19 /\
        keeps_but ([13; 18]%bv ++ clobE) rP r' /\ fsub stP st' /\ FR L lo (sp - 48) MM1 M').
    { intros r5 M5 RUN5 K5 W5 R5 FR5.
      pose proof (rc_canary _ M5 (rp_statics _ M5 R5)) as CAN5. cbn [s_canary MhFreeMeta.st'] in CAN5.
      change (s_canary (MhFreeMeta.st' stP m)) with (s_canary stP) in CAN5. rewrite Ecan in CAN5.
      destruct (segE M5 sp (s_canary st) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) base len
                 ltac:(lia) RET CAN5) with (regs := r5) (rom := rom)
        as (re & RUNe & E2 & E1 & E8 & E9 & E18 & E19 & E10 & E11 & Ke).
      1-6: eapply (FR_rdn_keep L lo (sp - 48) MM1); [exact FR5 | ceil; lia | cbn; lia | cbn; lia | assumption].
      1: kept_rw K5; exact P2. 1: kept_rw K5; exact P9. 1: kept_rw K5; exact P12. 1: kept_rw K5; exact P11.
      exists (MhFreeMeta.st' stP m), M5, re.
      split; [eapply msteps_trans; [exact RUN5 | exact RUNe]|].
      split; [exact W5|]. split; [exact R5|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { intros x k o Hx Hk E. apply MhFreeMeta.e_is_group in Hx. rewrite (MhFreeMeta.e_glast stP m NGm x Hx) in Hk.
        rewrite MhFreeMeta.e_slot in E. repeat split; try assumption; lia. }
      repeat (split; [assumption|]). split; [eapply keeps_join; [exact K5 | exact Ke] | split; [apply fsub_freemeta; exact NGm | exact FR5]]. }
    (* [comment removed for export] *)
    assert (FZwr : forall a, 0 <= a < 2 ^ 64 -> m_fz MP (sp - 96) m (Z_to_bv 64 a) <> MP (Z_to_bv 64 a) ->
                   (sp - 88 <= a < sp - 48) \/ (m <= a < m + 40)).
    { intros a Hr NE. unfold m_fz, z8' in NE. revert NE. generalize MP. intros Mb NE. wdiff NE Mb a. }
    assert (FZg : mem_grows MP (m_fz MP (sp - 96) m)) by (unfold m_fz; do 10 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    assert (Z8split' : word_to_le_bytes 8 (Z_to_bv 64 0) = (word_to_le_bytes 4 (Z_to_bv 64 0) ++ word_to_le_bytes 4 (Z_to_bv 64 0))%list) by reflexivity.
    destruct (Z.eq_dec fh 0) as [Fh0|Fh0].
    - (* [comment removed for export] *)
      assert (Lnil : l = []).
      { destruct l as [|a l2] eqn:El; [reflexivity|]. exfalso.
        assert (Ia : In a (s_flist stP)) by (fold l; rewrite El; left; reflexivity).
        destruct (wl_fU stP (WF_lists stP L WFP) a Ia) as (Ua & _). destruct (metaU_rng stP L WFP a Ua).
        rewrite Efh in Fh0. cbn in Fh0. unfold HEAPLO in *. lia. }
      assert (Qnil : MhFreeMeta.q_nil stP = true) by (unfold MhFreeMeta.q_nil; fold l; rewrite Lnil; reflexivity).
      assert (SOKc : store_ok RSEGS MP (Z_to_bv 64 ctx_free_meta_head) 8%nat = true).
      { eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact (ctx_store_ok stP MP REPP) | | ]; unfold ctx_free_meta_head, CTX; rewrite ?u_Z2bv by lia; cbn; lia. }
      destruct (segFMe MP (sp - 96) m fh ltac:(ceil; lia) ltac:(ceil; unfold HEAPLO; lia) SOKsp SOKm Cfh SOKc rP rom P10 P2 P18 Fh0) as (r5 & RUN5 & K5).
      set (M5 := m_fe MP (sp - 96) m) in RUN5.
      assert (W5 : forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) <> MP (Z_to_bv 64 a) ->
                  (sp - 88 <= a < sp - 48) \/ (m <= a < m + 40) \/ (ctx_free_meta_head <= a < ctx_free_meta_head + 8)).
      { intros a Hr NE. unfold M5, m_fe, ctx_free_meta_head, CTX in NE. unfold ctx_free_meta_head, CTX.
        destruct (decide (m_fz MP (sp - 96) m (Z_to_bv 64 a) = MP (Z_to_bv 64 a))) as [E0|NE0].
        - rewrite <- E0 in NE. revert NE. generalize (m_fz MP (sp - 96) m). intros Mb NE. wdiff NE Mb a.
        - destruct (FZwr a Hr NE0); lia. }
      assert (G5 : mem_grows MP M5) by (unfold M5, m_fe; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); exact FZg).
      destruct (freemeta_close stP L MP M5 m spF WFP REPP Um NGm NLm NFm F1) as [WF5 REP5].
      { intros a Hr NE. unfold MhFreeMeta.q_wr. rewrite Qnil. destruct (W5 a Hr NE) as [A|[A|A]]; [left; lia | right; left; exact A | right; right; right; split; [reflexivity | exact A]]. }
      { exact G5. }
      { unfold cell, M5, m_fe, ctx_free_meta_head, CTX, MhFreeMeta.q_prev. rewrite Z.eqb_refl, Qnil. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fe, ctx_free_meta_head, CTX, MhFreeMeta.q_next. rewrite Z.eqb_refl, Qnil. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 5 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 4 rdn_peel1. rewrite Z8split' , wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia). rdn_peel1.
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 4 rdn_peel1. rewrite Z8split', wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia).
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros X. rewrite Qnil in X. discriminate X. }
      { intros X. rewrite Qnil in X. discriminate X. }
      { intros _. unfold cell, M5, m_fe, ctx_free_meta_head, CTX. apply rdn_wbytes_hit8. zsimp; lia. }
      apply (FIN r5 M5 RUN5 K5 WF5 REP5).
      eapply FR_trans; [exact FRP|]. split; [exact G5|]. intros a Hr NE. destruct (W5 a Hr NE) as [A|[A|A]].
      + left. lia.
      + right; left. destruct (metaU_area stP L WFP m Um) as (ar & kk & Har & _ & _ & _ & Rlo & Rhi & A1 & A2 & _).
        split; [lia|]. split; [pose proof (metaU_img stP L WFP m Um); lia|]. intros (p & n & Hin & Hpn). destruct (wL_in stP L (WF_live stP L WFP) p n Hin) as (y & k & o & r & Hy & Hk & Sy).
        apply (ge_app_area stP (WF_geom stP L WFP) a); [exists y, k, p, n, o, r; repeat split; try assumption; lia | exists ar; split; [exact Har | lia]].
      + right; right. unfold ctx_free_meta_head, CTX_END, CTX in *. lia.
    - (* [comment removed for export] *)
      destruct (FHin Fh0) as [Lnn Ifh].
      assert (Qnil : MhFreeMeta.q_nil stP = false) by (unfold MhFreeMeta.q_nil; fold l; apply is_nilb_false; exact Lnn).
      set (ft := znth l (zlen l - 1)).
      pose proof (wl_fdll stP (WF_lists stP L WFP)) as Dl. fold l in Dl.
      destruct (dllf_ends _ _ _ (proj1 (dll_dllf stP _) Dl) (zlen_pos _ Lnn)) as [Nft Pfh].
      rewrite <- (head_of_znth _ Lnn), <- Efh in Nft, Pfh. fold ft in Nft, Pfh.
      assert (Ift : In ft l) by (subst ft; apply last_In; exact Lnn).
      destruct (wl_fU stP (WF_lists stP L WFP) fh Ifh) as (Ufh & NGfh & _). destruct (wl_fU stP (WF_lists stP L WFP) ft Ift) as (Uft & NGft & _).
      assert (Nhm : fh <> m) by (intros E; apply NLm; left; fold l; rewrite <- E; exact Ifh).
      assert (Ntm : ft <> m) by (intros E; apply NLm; left; fold l; rewrite <- E; exact Ift).
      destruct (metaU_rng stP L WFP fh Ufh) as (Hh1 & Hh2 & _). destruct (metaU_rng stP L WFP ft Uft) as (Ht1 & Ht2 & _).
      pose proof (metaU_sep stP L WFP m fh Um Ufh (fun E => Nhm (eq_sym E))) as SEPh.
      pose proof (metaU_sep stP L WFP m ft Um Uft (fun E => Ntm (eq_sym E))) as SEPt.
      assert (HT : fh = ft \/ fh + 40 <= ft \/ ft + 40 <= fh).
      { destruct (Z.eq_dec fh ft) as [E|NE]; [left; exact E | right; exact (metaU_sep stP L WFP fh ft Ufh Uft NE)]. }
      ceil; unfold HEAPLO in Hh1, Hh2, Ht1, Ht2.
      destruct (meta_cells stP L MP WFP REPP fh Ufh) as (arh & kh & _ & _ & _ & _ & _ & _ & RMh & _).
      pose proof (rm_prev _ _ _ RMh) as Chd0. rewrite Pfh in Chd0. unfold cell in Chd0.
      pose proof (meta_store_ok stP L MP WFP REPP fh Ufh) as SOKh40. pose proof (meta_store_ok stP L MP WFP REPP ft Uft) as SOKt40.
      assert (SOKh : store_ok RSEGS MP (Z_to_bv 64 fh) 8%nat = true).
      { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKh40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
      assert (SOKt : store_ok RSEGS MP (Z_to_bv 64 (ft + 8)) 8%nat = true).
      { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKt40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
      destruct (segFMq MP (sp - 96) m fh ft ltac:(ceil; lia) ltac:(ceil; unfold HEAPLO; lia) FHr ltac:(lia) SOKsp SOKm Cfh rP rom
                  ltac:(unfold HEAPLO; lia) ltac:(ceil; lia) ltac:(unfold HEAPLO; lia) ltac:(ceil; lia) SEPh SEPt Chd0 SOKh SOKt P10 P2 P18 Fh0)
        as (r5 & RUN5 & K5).
      set (M5 := m_fq MP (sp - 96) m fh ft) in RUN5.
      assert (W5 : forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) <> MP (Z_to_bv 64 a) ->
                  (sp - 88 <= a < sp - 48) \/ (m <= a < m + 40) \/ (ft + 8 <= a < ft + 16) \/ (fh <= a < fh + 8)).
      { intros a Hr NE. unfold M5, m_fq in NE.
        destruct (decide (m_fz MP (sp - 96) m (Z_to_bv 64 a) = MP (Z_to_bv 64 a))) as [E0|NE0].
        - rewrite <- E0 in NE. revert NE. generalize (m_fz MP (sp - 96) m). intros Mb NE. wdiff NE Mb a.
        - destruct (FZwr a Hr NE0); lia. }
      assert (G5 : mem_grows MP M5) by (unfold M5, m_fq; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact FZg).
      assert (Etl : znth (s_flist stP) (zlen (s_flist stP) - 1) = ft) by reflexivity.
      assert (Efh2 : head_of (s_flist stP) = fh) by (symmetry; exact Efh).
      destruct (freemeta_close stP L MP M5 m spF WFP REPP Um NGm NLm NFm F1) as [WF5 REP5].
      { intros a Hr NE. unfold MhFreeMeta.q_wr. rewrite Qnil, Etl, Efh2.
        destruct (W5 a Hr NE) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; split; [reflexivity | left; exact A] | right; right; left; split; [reflexivity | right; exact A]]. }
      { exact G5. }
      { unfold cell, M5, m_fq, MhFreeMeta.q_prev. rewrite Z.eqb_refl, Qnil, Etl. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fq, MhFreeMeta.q_next. rewrite Z.eqb_refl, Qnil, Efh2. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 6 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 5 rdn_peel1. rewrite Z8split' , wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia). rdn_peel1.
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 5 rdn_peel1. rewrite Z8split', wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia).
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 4 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros _. rewrite Etl. unfold cell, M5, m_fq. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros _. rewrite Efh2. unfold cell, M5, m_fq. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros X. rewrite Qnil in X. discriminate X. }
      apply (FIN r5 M5 RUN5 K5 WF5 REP5).
      eapply FR_trans; [exact FRP|]. split; [exact G5|]. intros a Hr NE.
      assert (FRm : forall x, metaU stP x -> x <= a < x + 40 -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a).
      { intros x Ux Ha. destruct (metaU_area stP L WFP x Ux) as (ar & kk & Har & _ & _ & _ & Rlo & Rhi & A1 & A2 & _).
        split; [lia|]. split; [pose proof (metaU_img stP L WFP x Ux); lia|]. intros (p & n & Hin & Hpn). destruct (wL_in stP L (WF_live stP L WFP) p n Hin) as (y & k & o & r & Hy & Hk & Sy).
        apply (ge_app_area stP (WF_geom stP L WFP) a); [exists y, k, p, n, o, r; repeat split; try assumption; lia | exists ar; split; [exact Har | lia]]. }
      destruct (W5 a Hr NE) as [A|[A|[A|A]]].
      + left. lia.
      + right; left. apply (FRm m Um). lia.
      + right; left. apply (FRm ft Uft). lia.
      + right; left. apply (FRm fh Ufh). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition MID (d : nat) (stX : mst) (MX : mem) : Prop :=
    WF stX L /\ REP stX MX /\
    s_brk stX = s_brk st /\ s_limbo stX = m :: s_limbo st /\ s_canary stX = s_canary st /\
    mr_W (s_meta stX m) = mr_W (s_meta st m) /\ mr_mem (s_meta stX m) = mr_mem (s_meta st m) /\
    (s_kind st m = GTop -> Permutation (s_regions st) (rg st m :: s_regions stX) /\ nojunk stX) /\
    (forall hm hi o, s_kind st m = GNest hm hi o ->
        s_regions stX = s_regions st /\ is_group stX hm /\ 0 <= hi <= g_lastidx stX hm /\ s_slot stX hm hi = SJunk o /\
        g_mem st m = g_slot_start stX hm hi + 16 * o /\ g_mem st m + 8 <= g_slot_end stX hm hi /\
        only_junk stX hm hi /\ (forall d', d = S d' -> nest_depth_le stX d' hm)) /\
    (forall x, g_mem stX x = g_mem st x) /\ HDR MX /\ fsub st stX /\
    FR L (sp - 96) (sp - 48) MM1 MX.

  Lemma DQ_MID : forall d r1 stD MD r2, DQ_POST d r1 stD MD r2 -> MID d stD MD.
  Proof using Hsp Hi Hgrp HREP HWF i.
    intros d r1 stD MD r2 (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8 & _ & _ & _ & _ & _ & PG & PW & PS & P9).
    unfold MID. repeat (split; [assumption|]). split; [|split; [exact PS | exact P9]].
    apply (HDR_keep MM1 MD); [|exact PW]. apply (HDR_keep M MM1); [exact HDR_M | exact WRC_M1].
  Qed.

  Lemma nest_depth_kind : forall (st1 st2 : mst) f x, (forall y, s_kind st2 y = s_kind st1 y) ->
    nest_depth_le st1 f x -> nest_depth_le st2 f x.
  Proof using.
    intros st1 st2 f. induction f as [|f IH]; intros x EK D; cbn in *; rewrite EK; destruct (s_kind st1 x); try exact D.
    apply IH; [exact EK | exact D].
  Qed.

  (* [comment removed for export] *)
  Lemma MID_policy : forall d stX MX MX' u q b sq,
    MID d stX MX -> WF (MhPolicy.st' stX u q b sq) L -> REP (MhPolicy.st' stX u q b sq) MX' ->
    FR L (sp - 96) (sp - 48) MM1 MX' -> WRC MX MX' -> MID d (MhPolicy.st' stX u q b sq) MX'.
  Proof using Hsp Hi Hgrp HWF i.
    intros d stX MX MX' u q b sq (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8 & PG & PH & PS & P9) W' R' F' WR'.
    unfold MID. split; [exact W'|]. split; [exact R'|].
    split; [exact P3|]. split; [exact P4|]. split; [exact P4c|]. split; [exact P5|]. split; [exact P6|].
    split; [exact P7|]. split; [|split; [exact PG | split; [exact (HDR_keep MX MX' PH WR') | split; [eapply fsub_trans; [exact PS | apply fsub_policy] | exact F']]]].
    intros hm hi o K. destruct (P8 hm hi o K) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    repeat (split; [assumption|]). intros d' Ed. apply (nest_depth_kind stX); [intros; reflexivity | exact (Q8 d' Ed)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fgu_stage : forall d stD MD r2,
    MID d stD MD ->
    getr r2 10 = Z_to_bv 64 m -> getr r2 18 = Z_to_bv 64 CTX ->
    exists stU MU r3,
      msteps RSEGS (mkst r2 (0x62448%bv : word) MD rom) (mkst r3 (0x6247c%bv : word) MU rom) /\
      MID d stU MU /\ mem_grows MD MU /\
      getr r3 11 = Z_to_bv 64 sc /\ getr r3 12 = Z_to_bv 64 W /\ keeps_but [11; 12; 13; 14]%bv r2 r3.
  Proof using Hsp Hi Hgrp HWF i.
    intros d stD MD r2 MD0 C10 C18. pose proof MD0 as (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8 & PG & PH & PS & P9).
    pose proof f_nums as (R1 & R2 & R8 & HS & HL & S1 & S2). pose proof spF_ok as (F1 & F2 & F3).
    pose proof (wg_Wr st L m f_wfg) as WR.
    assert (Lim : In m (s_limbo stD)) by (rewrite P4; left; reflexivity).
    destruct (wG_limbo stD L (WF_groups stD L P1) m Lim) as (Um & _).
    destruct (meta_cells stD L MD P1 P2 m Um) as (ar & k & _ & _ & _ & _ & _ & _ & RM & _). destruct RM as [_ _ Rme _ _ RW]. rewrite P5 in RW.
    pose proof (wc_usage stD (WF_ctx stD L P1) sc) as US.
    assert (MU : sc < 48 -> rdn RSEGS MD (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (c_usage (s_ctx stD) sc)))).
    { intros H48. apply (rc_usage stD MD (rp_ctx stD MD P2)). lia. }
    destruct (segFGu MD m W (c_usage (s_ctx stD) sc) ltac:(ceil; unfold HEAPLO; lia) WR RW MU (ctx_store_ok stD MD P2) r2 rom C10 C18)
      as (r3 & RUN3 & D11 & D12 & K3).
    set (MU2 := m_u MD W (c_usage (s_ctx stD) sc)) in RUN3.
    set (u' := fun s => if ((s =? sc) && (sc <? 48))%bool then bv_unsigned (usage_word W (c_usage (s_ctx stD) sc)) else c_usage (s_ctx stD) s).
    assert (WU : forall a, 0 <= a < 2 ^ 64 -> MU2 (Z_to_bv 64 a) <> MD (Z_to_bv 64 a) -> sc < 48 /\ ctx_usage sc <= a < ctx_usage sc + 8).
    { intros a Hr NE. unfold MU2, m_u in NE. change (w_sizeclass W) with sc in NE. destruct (Z.ltb_spec sc 48) as [H48|H48]; [|exfalso; exact (NE eq_refl)].
      split; [exact H48|]. unfold ctx_usage, CTX in *. revert NE. generalize MD. intros Mb NE. wdiff NE Mb a. }
    assert (GU : mem_grows MD MU2).
    { unfold MU2, m_u. destruct (w_sizeclass W <? 48); [apply wbytes_grows | apply mem_grows_refl]. }
    destruct (policy_close stD L MD MU2 spF u' (c_unmap_seq (s_ctx stD)) (c_bounces (s_ctx stD)) (c_seq (s_ctx stD))
                (fun a => sc < 48 /\ ctx_usage sc <= a < ctx_usage sc + 8) P1 P2) as [W' R'].
    { intros s0. unfold u'. destruct ((s0 =? sc) && (sc <? 48))%bool; [apply u64_range | apply (wc_usage stD (WF_ctx stD L P1))]. }
    { exact (wc_useq stD (WF_ctx stD L P1)). }
    { exact (wc_bnc stD (WF_ctx stD L P1)). }
    { exact (wc_seq stD (WF_ctx stD L P1)). }
    { exact F1. }
    { intros a Hr NE. right. destruct (WU a Hr NE) as [H48 A]. unfold ctx_usage, CTX in *. split; [lia|]. split; [exact H48 | exact A]. }
    { exact GU. }
    { intros s0 Hs0. unfold u'. destruct (Z.eqb_spec s0 sc) as [->|Hne]; cbn [andb].
      - destruct (Z.ltb_spec sc 48) as [H48|H48].
        + left. unfold cell, MU2, m_u. change (w_sizeclass W) with sc. rewrite (proj2 (Z.ltb_lt sc 48) H48).
          rewrite Z_to_bv_bv_unsigned. apply rdn_wbytes_hit8. unfold ctx_usage, CTX. zsimp; lia.
        + right. split; [reflexivity|]. intros a Ha [H48' _]. lia.
      - right. split; [reflexivity|]. intros a Ha [_ A]. unfold ctx_usage, CTX in Ha, A. lia. }
    { intros j Hj. right. split; [reflexivity|]. intros [H48 A]. unfold ctx_usage, ctx_unmap_seq, CTX in A. lia. }
    { intros j Hj. right. split; [reflexivity|]. intros [H48 A]. unfold ctx_usage, ctx_bounces, CTX in A. lia. }
    { right. split; [reflexivity|]. intros [H48 A]. unfold ctx_usage, ctx_seq, CTX in A. lia. }
    exists (MhPolicy.st' stD u' (c_unmap_seq (s_ctx stD)) (c_bounces (s_ctx stD)) (c_seq (s_ctx stD))), MU2, r3.
    split; [exact RUN3|]. split.
    - apply (MID_policy d stD MD MU2); try assumption.
      + eapply FR_trans; [exact P9|]. split; [exact GU|]. intros a Hr NE. right; right. destruct (WU a Hr NE) as [H48 A]. unfold ctx_usage, CTX_END, CTX in A |- *. lia.
      + intros a Hr NE. right; left. destruct (WU a Hr NE) as [H48 A]. unfold ctx_usage, CTX_END, CTX in A |- *. lia.
    - split; [exact GU|]. split; [exact D11|]. split; [exact D12 | exact K3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fgtop_stage : forall d stU MU r3,
    MID d stU MU -> g_maplen st m <> 0 ->
    getr r3 10 = Z_to_bv 64 m -> getr r3 11 = Z_to_bv 64 sc -> getr r3 12 = Z_to_bv 64 W -> getr r3 18 = Z_to_bv 64 CTX ->
    exists stP MP r4,
      msteps RSEGS (mkst r3 (0x6247c%bv : word) MU rom) (mkst r4 (0x62504%bv : word) MP rom) /\
      MID d stP MP /\ mem_grows MU MP /\
      getr r4 10 = Z_to_bv 64 m /\ getr r4 11 = Z_to_bv 64 (g_maplen st m * 4096) /\ getr r4 12 = Z_to_bv 64 (g_mem st m) /\
      getr r4 18 = Z_to_bv 64 CTX /\ keeps_but [11; 12; 13]%bv r3 r4.
  Proof using Hsp Hi Hgrp HWF i.
    intros d stU MU r3 MD0 Hml C10 C11 C12 C18. pose proof MD0 as (P1 & P2 & P3 & P4 & P4c & P5 & P6 & P7 & P8 & PG & PH & PS & P9).
    pose proof f_nums as (R1 & R2 & R8 & HS & HL & S1 & S2). pose proof spF_ok as (F1 & F2 & F3).
    pose proof (wg_Wr st L m f_wfg) as WR. pose proof (wg_mem st L m f_wfg) as (G1 & G2 & G3).
    assert (Lim : In m (s_limbo stU)) by (rewrite P4; left; reflexivity).
    destruct (wG_limbo stU L (WF_groups stU L P1) m Lim) as (Um & _).
    destruct (meta_cells stU L MU P1 P2 m Um) as (ar & k & _ & _ & _ & _ & _ & _ & RM & _). destruct RM as [_ _ Rme _ _ RW]. rewrite P5 in RW. rewrite P6 in Rme.
    set (seq := c_seq (s_ctx stU)). pose proof (wc_seq stU (WF_ctx stU L P1)) as SQ. fold seq in SQ.
    pose proof (cell1_rdn MU ctx_seq seq SQ (rc_seq stU MU (rp_ctx stU MU P2))) as Cseq.
    assert (MGr : 0 <= g_mem st m < 2 ^ 64).
    { destruct (group_range st L HWF m Hgrp) as [X1 X2]. pose proof (MhDissolve.span_nonempty st L HWF m Hgrp). ceil; unfold HEAPLO in *. lia. }
    destruct (segFGtop m W (g_mem st m) seq ltac:(ceil; unfold HEAPLO; lia) WR SQ MU RW Rme Cseq (ctx_store_ok stU MU P2) r3 rom C10 C11 C12 C18)
      as (r4 & RUN4 & D10 & D11 & D12 & D18 & K4).
    { unfold g_maplen in Hml. exact Hml. }
    set (MP := m_top W seq MU) in RUN4.
    set (bnc := ((7 <=? sc) && (sc <=? 38))%bool).
    set (q' := fun j => if (bnc && (j =? sc - 7))%bool then MhNtf.MhNtfD.seq' seq else if (seq =? 255) then 0 else c_unmap_seq (s_ctx stU) j).
    set (WS := fun a => (seq = 255 /\ CTX + 848 <= a < CTX + 880) \/ a = ctx_seq \/ (7 <= sc <= 38 /\ a = ctx_unmap_seq (sc - 7))).
    pose proof (seq'_rng seq SQ) as [SQ' [SQ'' |[]]].
    assert (Hb7 : bnc = true -> 7 <= sc <= 38).
    { unfold bnc. intros X. apply Bool.andb_true_iff in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia. }
    assert (WT : forall a, 0 <= a < 2 ^ 64 -> MP (Z_to_bv 64 a) <> MU (Z_to_bv 64 a) -> WS a).
    { intros a Hr NE. unfold MP, m_top, m_s, m_z in NE. change (w_sizeclass W) with sc in NE. fold bnc in NE.
      unfold WS, ctx_seq, ctx_unmap_seq, CTX in *.
      assert (STEP1 : forall Mb, wbytes Mb (Z_to_bv 64 (682024 + 912)) [Z_to_bv 8 (MhNtf.MhNtfD.seq' seq)] (Z_to_bv 64 a) <> Mb (Z_to_bv 64 a) -> a = 682024 + 912).
      { intros Mb X. apply wbytes_diff_g in X; [cbn in X; lia | lia | cbn; lia | exact Hr]. }
      assert (STEPz : forall Mb, MhNtf.MhNtfD.m_z seq Mb (Z_to_bv 64 a) <> Mb (Z_to_bv 64 a) -> seq = 255 /\ 682024 + 848 <= a < 682024 + 880).
      { intros Mb X. unfold MhNtf.MhNtfD.m_z, CTX in X. destruct (Z.eqb_spec seq 255) as [E|NE2]; [|exfalso; exact (X eq_refl)].
        split; [exact E|]. revert X. generalize Mb. intros Mc X. unfold MhNtf.MhNtfD.z8 in X. wdiff X Mc a. }
      destruct bnc.
      - destruct (decide (wbytes (MhNtf.MhNtfD.m_z seq MU) (Z_to_bv 64 (682024 + 912)) [Z_to_bv 8 (MhNtf.MhNtfD.seq' seq)] (Z_to_bv 64 a) =
                          MU (Z_to_bv 64 a))) as [E1|NE1].
        + rewrite <- E1 in NE. apply wbytes_diff_g in NE; [cbn in NE; right; right; split; [exact (Hb7 eq_refl) | lia] | lia | cbn; lia | exact Hr].
        + destruct (decide (MhNtf.MhNtfD.m_z seq MU (Z_to_bv 64 a) = MU (Z_to_bv 64 a))) as [E2|NE2].
          * rewrite <- E2 in NE1. right; left. exact (STEP1 _ NE1).
          * left. exact (STEPz _ NE2).
      - destruct (decide (MhNtf.MhNtfD.m_z seq MU (Z_to_bv 64 a) = MU (Z_to_bv 64 a))) as [E2|NE2].
        + rewrite <- E2 in NE. right; left. exact (STEP1 _ NE).
        + left. exact (STEPz _ NE2). }
    assert (GP : mem_grows MU MP).
    { unfold MP, m_top, m_s, m_z. destruct ((7 <=? w_sizeclass W) && (w_sizeclass W <=? 38))%bool; destruct (seq =? 255);
        repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. }
    destruct (policy_close stU L MU MP spF (c_usage (s_ctx stU)) q' (c_bounces (s_ctx stU)) (MhNtf.MhNtfD.seq' seq) WS P1 P2) as [W' R'].
    { exact (wc_usage stU (WF_ctx stU L P1)). }
    { intros j. unfold q'. destruct (bnc && (j =? sc - 7))%bool; [lia|]. destruct (seq =? 255); [lia | exact (wc_useq stU (WF_ctx stU L P1) j)]. }
    { exact (wc_bnc stU (WF_ctx stU L P1)). }
    { lia. }
    { exact F1. }
    { intros a Hr NE. right. pose proof (WT a Hr NE) as X. split; [|exact X]. unfold WS, ctx_seq, ctx_unmap_seq, CTX in X |- *. lia. }
    { exact GP. }
    { intros s0 Hs0. right. split; [reflexivity|]. intros a Ha X. unfold WS, ctx_usage, ctx_seq, ctx_unmap_seq, CTX in Ha, X. lia. }
    { intros j Hj. unfold q'. destruct (Z.eqb_spec j (sc - 7)) as [Ej|Nj].
      - destruct bnc eqn:Eb; cbn [andb].
        + left. unfold cell, MP, m_top. change (w_sizeclass W) with sc. fold bnc. rewrite Eb, Ej. rewrite (w2le1 (MhNtf.MhNtfD.seq' seq)) by lia.
          pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 (MhNtf.MhNtfD.seq' seq)] (m_s seq MU) (Z_to_bv 64 (ctx_unmap_seq (sc - 7)))) as RH.
          cbn [length] in RH. apply RH. unfold ctx_unmap_seq, CTX. rewrite u_Z2bv by lia. lia.
        + destruct (Z.eqb_spec seq 255) as [Es|Ns].
          * left. unfold cell, MP, m_top, m_s. change (w_sizeclass W) with sc. fold bnc. rewrite Eb.
            unfold MhNtf.MhNtfD.m_z. rewrite (proj2 (Z.eqb_eq seq 255) Es). unfold ctx_seq, ctx_unmap_seq, CTX, MhNtf.MhNtfD.z8.
            rdn_peel1. unfold word_to_le_bytes at 5. cbn [Z_to_le_bytes]. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))) with (Z_to_bv 8 0).
            assert (C4 : forall b0, 0 <= j - b0 < 8 -> forall Mb, rdn RSEGS (wbytes Mb (Z_to_bv 64 (682024 + 848 + b0)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (682024 + 848 + j)) 1 = Some [Z_to_bv 8 0]).
            { intros b0 Hb0 Mb. replace (682024 + 848 + j) with (682024 + 848 + b0 + (j - b0)) by lia. apply rdn1_in_z8; lia. }
            destruct (Z.lt_ge_cases j 24); [|replace (682024 + 872) with (682024 + 848 + 24) by lia; apply C4; lia].
            rdn_peel1. destruct (Z.lt_ge_cases j 16); [|replace (682024 + 864) with (682024 + 848 + 16) by lia; apply C4; lia].
            rdn_peel1. destruct (Z.lt_ge_cases j 8); [|replace (682024 + 856) with (682024 + 848 + 8) by lia; apply C4; lia].
            rdn_peel1. replace (682024 + 848) with (682024 + 848 + 0) by lia. apply C4; lia.
          * right. split; [reflexivity|]. unfold WS. intros [[Es _]|[X|[Eb' X]]]; [exact (Ns Es) | unfold ctx_unmap_seq, ctx_seq in X; lia |].
            unfold bnc in Eb. apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; apply Z.leb_gt in Eb; lia.
      - destruct (Z.eqb_spec seq 255) as [Es|Ns].
        + left. rewrite Bool.andb_false_r. unfold cell, MP, m_top, m_s. change (w_sizeclass W) with sc. fold bnc.
          unfold MhNtf.MhNtfD.m_z. rewrite (proj2 (Z.eqb_eq seq 255) Es). unfold ctx_seq, ctx_unmap_seq, CTX, MhNtf.MhNtfD.z8.
          assert (C4 : forall b0, 0 <= j - b0 < 8 -> forall Mb, rdn RSEGS (wbytes Mb (Z_to_bv 64 (682024 + 848 + b0)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (682024 + 848 + j)) 1 = Some [Z_to_bv 8 0]).
          { intros b0 Hb0 Mb. replace (682024 + 848 + j) with (682024 + 848 + b0 + (j - b0)) by lia. apply rdn1_in_z8; lia. }
          unfold word_to_le_bytes at 1. cbn [Z_to_le_bytes]. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))) with (Z_to_bv 8 0).
          destruct bnc; [rdn_peel1|]; rdn_peel1;
          (destruct (Z.lt_ge_cases j 24); [|replace (682024 + 872) with (682024 + 848 + 24) by lia; apply C4; lia]);
          rdn_peel1; (destruct (Z.lt_ge_cases j 16); [|replace (682024 + 864) with (682024 + 848 + 16) by lia; apply C4; lia]);
          rdn_peel1; (destruct (Z.lt_ge_cases j 8); [|replace (682024 + 856) with (682024 + 848 + 8) by lia; apply C4; lia]);
          rdn_peel1; replace (682024 + 848) with (682024 + 848 + 0) by lia; apply C4; lia.
        + right. rewrite Bool.andb_false_r. split; [reflexivity|]. unfold WS. intros [[Es _]|[X|[Eb' X]]]; [exact (Ns Es) | unfold ctx_unmap_seq, ctx_seq in X; lia | unfold ctx_unmap_seq in X; lia]. }
    { intros j Hj. right. split; [reflexivity|]. unfold WS, ctx_bounces, ctx_seq, ctx_unmap_seq, CTX. intros [[_ X]|[X|[B X]]]; lia. }
    { left. unfold cell, MP, m_top, m_s. change (w_sizeclass W) with sc. fold bnc. rewrite (w2le1 (MhNtf.MhNtfD.seq' seq)) by lia.
      pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 (MhNtf.MhNtfD.seq' seq)]) as RH. cbn [length] in RH.
      destruct bnc; [unfold ctx_unmap_seq, ctx_seq, CTX; rdn_peel1; apply RH; zsimp; lia | unfold ctx_seq, CTX; apply RH; zsimp; lia]. }
    exists (MhPolicy.st' stU (c_usage (s_ctx stU)) q' (c_bounces (s_ctx stU)) (MhNtf.MhNtfD.seq' seq)), MP, r4.
    split; [exact RUN4|]. split.
    - apply (MID_policy d stU MU MP); try assumption.
      + eapply FR_trans; [exact P9|]. split; [exact GP|]. intros a Hr NE. right; right. pose proof (WT a Hr NE) as X.
        unfold WS, ctx_seq, ctx_unmap_seq, CTX_END, CTX in X |- *. lia.
      + intros a Hr NE. right; left. pose proof (WT a Hr NE) as X. unfold WS, ctx_seq, ctx_unmap_seq, CTX_END, CTX in X |- *. lia.
    - split; [exact GP|]. split; [exact D10|]. split; [rewrite D11; f_equal; unfold g_maplen; lia|]. split; [exact D12|]. split; [exact D18 | exact K4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma COV2 : forall big : list reg,
    forallb (fun r => existsb (fun x => bv_eqb x r) NTF_CLOB || existsb (fun x => bv_eqb x r) [1; 2; 8; 9; 18; 19]%bv)%bool big = true ->
    forall r, In r big -> In r NTF_CLOB \/ In r [1; 2; 8; 9; 18; 19]%bv.
  Proof using.
    intros big Hb r Hr. pose proof (proj1 (forallb_forall _ _) Hb r Hr) as X. cbn beta in X. apply Bool.orb_true_iff in X.
    destruct X as [X|X]; [left | right]; apply in_regs_dec; exact X.
  Qed.

  Lemma m_not_limbo : ~ In m (s_limbo st).
  Proof using Hgrp HWF L RN. intros Hl. destruct (wG_limbo st L (WF_groups st L HWF) m Hl) as (_ & NG & _). exact (NG Hgrp). Qed.

  Lemma ntf_freearm : forall (d : nat) r1,
    match d with O => True | S d' => NTF_SPEC d' end ->
    nest_depth_le st d m ->
    getr r1 10 = Z_to_bv 64 m -> getr r1 12 = Z_to_bv 64 sc -> getr r1 2 = Z_to_bv 64 (sp - 96) ->
    getr r1 9 = Z_to_bv 64 A_CANARY -> getr r1 18 = Z_to_bv 64 CTX ->
    keeps_but (clobN0 ++ clobD) regs r1 -> ret_ok (getr regs 1) -> getr regs 2 = Z_to_bv 64 sp ->
    CEIL + 96 * (Z.of_nat d + 1) <= sp -> defined M (sp - 96 * (Z.of_nat d + 1)) sp ->
    exists st' M' r',
      msteps RSEGS (mkst r1 (0x62334%bv : word) MM1 rom) (mkst r' (getr regs 1) M' rom) /\
      WF st' L /\ REP st' M' /\ s_brk st' = s_brk st /\ s_limbo st' = s_limbo st /\ s_canary st' = s_canary st /\ nojunk st' /\
      ntf_ret st st' r' /\ keeps_but NTF_CLOB regs r' /\ fsub st st' /\ FR L (sp - 96 * (Z.of_nat d + 1)) (sp - 48) MM1 M'.
  Proof using Hall OJ SOK Hsp Hslot Hi Hgrp HREP HWF off i.
    intros d r1 IH Hdep C10 C12 C2 C9 C18 K1 RET H2 Hspd DEFd.
    pose proof f_nums as (R1 & R2 & R8 & HS & HL & S1 & S2). pose proof f_wfg as WG.
    assert (Hd0 : 0 <= Z.of_nat d) by lia.
    assert (GM1 : mem_grows M MM1) by exact (proj1 (M1_FR st L M sp Hsp regs)).
    destruct (dq_stage d r1 Hdep C10 C12 C2 C9 C18) as (stD & MD & r2 & RUN2 & DQ).
    pose proof DQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & D18 & D2 & D9 & K2 & _ & _ & _ & FRD).
    pose proof (DQ_MID d r1 stD MD r2 DQ) as MIDD.
    destruct (fgu_stage d stD MD r2 MIDD D10 D18) as (stU & MU & r3 & RUN3 & MIDU & GU & E11 & E12 & K3).
    pose proof MIDU as (U1 & U2 & U3 & U4 & U4c & U5 & U6 & U7 & U8 & UG & UH & US & U9). unfold HDR in UH.
    assert (GD : mem_grows MM1 MD) by exact (proj1 FRD).
    destruct (s_kind st m) as [|hm hi ho] eqn:K.
    - (* [comment removed for export] *)
      pose proof (wg_kind st L m WG) as KD. rewrite K in KD. destruct KD as (Kml & Kreg & _).
      destruct (fgtop_stage d stU MU r3 MIDU ltac:(lia) ltac:(kept_rw K3; exact D10) E11 E12 ltac:(kept_rw K3; exact D18))
        as (stP & MP & r4 & RUN4 & MIDP & GP & F10 & F11 & F12 & F18 & K4).
      pose proof MIDP as (Q1 & Q2 & Q3 & Q4 & Q4c & Q5 & Q6 & Q7 & Q8 & QG & QH & QS & Q9).
      destruct (fm_stage (sp - 96) stP MP r4 (Z_to_bv 64 (g_mem st m)) (Z_to_bv 64 (g_maplen st m * 4096)) ltac:(lia) Q1 Q2
                  ltac:(rewrite Q4; left; reflexivity) Q4c F10 ltac:(kept_rw K4; kept_rw K3; exact D2) F18 ltac:(kept_rw K4; kept_rw K3; exact D9)
                  F12 F11 RET Q9 ltac:(eapply mem_grows_trans; [exact GM1 | eapply mem_grows_trans; [exact GD | eapply mem_grows_trans; [exact GU | exact GP]]]))
        as (st' & M' & r' & RUN5 & W' & R' & B' & L' & RG' & C' & SL' & E10 & E11' & E1 & E2 & E8 & E9 & E18 & E19 & K5 & FS5 & FR5).
      exists st', M', r'. split.
      { eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4 | exact RUN5]. }
      split; [exact W'|]. split; [exact R'|]. split; [rewrite B'; exact Q3|]. split; [rewrite L', Q4; cbn; rewrite Z.eqb_refl; apply zremove_notin; exact m_not_limbo|].
      split; [rewrite C'; exact Q4c|].
      split; [intros x kk o Hx Hk E; destruct (SL' x kk o Hx Hk E) as (Hx0 & Hk0 & E0); exact (proj2 (Q7 K) x kk o Hx0 Hk0 E0)|].
      split.
      { right. exists (g_mem st m), (4096 * g_maplen st m), m. rewrite RG'. split; [exact (proj1 (Q7 K))|].
        split; [exact E10|]. split; [rewrite E11'; f_equal; lia | lia]. }
      split.
      { apply (keeps_final regs r' ((clobN0 ++ clobD) ++ ((clobDQ ++ [11; 13; 14]%bv ++ clobACT) ++ ([11; 12; 13; 14]%bv ++ ([11; 12; 13]%bv ++ ([13; 18]%bv ++ clobE)))))).
        - eapply keeps_join; [exact K1|]. eapply keeps_join; [exact K2|]. eapply keeps_join; [exact K3|]. eapply keeps_join; [exact K4 | exact K5].
        - apply COV2. reflexivity.
        - exact E1. - rewrite E2, H2; reflexivity. - exact E8. - exact E9. - exact E18. - exact E19. }
      split; [eapply fsub_trans; [exact QS | exact FS5]|].
      eapply FR_widen; [| |exact FR5]; lia.
    - (* [comment removed for export] *)
      destruct d as [|d']; [cbn in Hdep; rewrite K in Hdep; destruct Hdep|].
      destruct (U8 hm hi ho eq_refl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
      pose proof (Q8 d' eq_refl) as DEPh.
      destruct (f_nest hm hi ho K) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
      pose proof (wg_kind st L m WG) as KD. rewrite K in KD. destruct KD as (Kml & _).
      (* [comment removed for export] *)
      assert (Lim : In m (s_limbo stU)) by (rewrite U4; left; reflexivity).
      destruct (wG_limbo stU L (WF_groups stU L U1) m Lim) as (Um & _).
      destruct (meta_cells stU L MU U1 U2 m Um) as (ar & k & _ & _ & _ & _ & _ & _ & RM & _). destruct RM as [_ _ Rme _ _ RW]. rewrite U6 in Rme.
      pose proof (wg_Wr st L m WG) as WR.
      destruct (segFGn1 m W (g_mem st m) ltac:(ceil; unfold HEAPLO; lia) WR MU Rme r3 rom ltac:(kept_rw K3; exact D10) E12 ltac:(unfold g_maplen in Kml; exact Kml))
        as (r4 & RUN4 & F10 & F8 & F19 & F1 & K4).
      (* [comment removed for export] *)
      destruct (UH hm hi ho eq_refl) as (rc & Hrc & HB4 & HB3 & HB2).
      assert (Einb : inband stU hm (g_mem st m) = inband st hm (g_mem st m)) by (unfold inband; rewrite (UG hm); reflexivity).
      rewrite <- Einb in HB2. rewrite Q5 in HB4, HB3, HB2.
      destruct (J_gm_pre stU L MU U1 U2 hm hi ho rc Q2 Q3 Q4 Hrc HB4 HB3 HB2) as [GMR GMP].
      rewrite <- Q5 in GMR, GMP.
      destruct (get_meta_run r4 MU rom (Z_to_bv 64 0x62494) _ _ _ _ _ _ _ _ _ _ GMR GMP F10 F1 ltac:(reflexivity)) as (r5 & RUN5 & G10 & G11 & K5).
      change (keeps_but gm_clob r4 r5) in K5.
      replace (Z_to_bv 64 0x62494) with (0x62494%bv : word) in RUN5 by (apply bv_eq; reflexivity).
      (* [comment removed for export] *)
      pose proof (gp_pe _ _ _ _ _ _ _ _ _ GMP) as Ppe. pose proof (gp_idx _ _ _ _ _ _ _ _ _ GMP) as Pidx.
      assert (GAp : forall a, g_mem st m <= a < g_mem st m + 8 -> garbage stU hm hi a).
      { intros a Ha. unfold garbage. rewrite Q4. split; [exact Q3 | right; lia]. }
      assert (PR : HEAPLO + 16 <= g_mem st m /\ g_mem st m + 8 <= CEIL).
      { pose proof (garbage_in_span stU L U1 hm hi (g_mem st m) Q2 (GAp (g_mem st m) ltac:(lia))) as X0.
        pose proof (garbage_in_span stU L U1 hm hi (g_mem st m + 7) Q2 (GAp (g_mem st m + 7) ltac:(lia))) as X7.
        destruct (group_range stU L U1 hm Q2) as [X1 X2].
        pose proof (wg_stride stU L hm (wG_each stU L (WF_groups stU L U1) hm Q2)) as [S16 _].
        assert (0 <= g_stride stU hm * hi) by (apply Z.mul_nonneg_nonneg; lia).
        pose proof (wg_slots stU L hm (wG_each stU L (WF_groups stU L U1) hm Q2) hi Q3) as SWj. rewrite Q4 in SWj. destruct SWj as (Ho0 & _).
        pose proof Q5 as Q5'. unfold g_slot_start, UNIT in Q5'. lia. }
      destruct PR as [PR1 PR2].
      assert (SOKg : store_ok RSEGS MU (Z_to_bv 64 (g_mem st m)) 8%nat = true).
      { pose proof (group_bytes_defined stU L MU 8 hm U1 U2 (wg_depth stU L hm (wG_each stU L (WF_groups stU L U1) hm Q2)) Q2) as DF.
        pose proof (garbage_in_span stU L U1 hm hi (g_mem st m) Q2 (GAp (g_mem st m) ltac:(lia))) as X0.
        pose proof (garbage_in_span stU L U1 hm hi (g_mem st m + 7) Q2 (GAp (g_mem st m + 7) ltac:(lia))) as X7.
        destruct (group_range stU L U1 hm Q2) as [X1 X2].
        eapply store_ok_defined; [exact DF | lia | cbn; lia | unfold HEAPLO in *; lia | ceil; lia]. }
      pose proof (gm_b3 _ _ _ _ _ _ _ _ _ _ _ GMR) as B3.
      destruct (segFGn2 MU m (g_mem st m) (hi + 32 * rc) ltac:(ceil; unfold HEAPLO; lia) ltac:(lia) ltac:(pose proof (glast_rng stU hm); unfold g_lastidx in *; lia)
                  Rme (rdn1_of_byte MU _ _ B3) SOKg r5 rom ltac:(kept_rw K5; exact F19) ltac:(kept_rw K5; exact F8)) as (r6 & RUN6 & H11 & H1 & K6).
      set (MZ := m_n2 MU (g_mem st m)) in RUN6.
      assert (GZ : mem_grows MU MZ) by (unfold MZ, m_n2; apply wbytes_grows).
      assert (WZ : forall a, 0 <= a < 2 ^ 64 -> MZ (Z_to_bv 64 a) <> MU (Z_to_bv 64 a) -> g_mem st m <= a < g_mem st m + 8).
      { intros a Hr NE. unfold MZ, m_n2 in NE. apply wbytes_diff_g in NE; [rewrite length_N_to_le_bytes in NE; cbn in NE; lia | unfold HEAPLO in *; lia | rewrite length_N_to_le_bytes; ceil; cbn; lia | exact Hr]. }
      assert (REPZ : REP stU MZ).
      { apply (REP_frame stU L MU U1 U2 MZ GZ). intros a Hr NE. right. exists hm, hi. split; [exact Q2|].
        unfold garbage. rewrite Q4. split; [exact Q3|]. right. pose proof (WZ a Hr NE). lia. }
      assert (FRZ : FR L (sp - 96) (sp - 48) MM1 MZ).
      { eapply FR_trans; [exact U9|]. split; [exact GZ|]. intros a Hr NE. right; left. pose proof (WZ a Hr NE) as A.
        assert (GA : garbage stU hm hi a) by (unfold garbage; rewrite Q4; split; [exact Q3 | right; lia]).
        pose proof (garbage_in_span stU L U1 hm hi a Q2 GA). destruct (group_range stU L U1 hm Q2). split; [lia|].
        split; [pose proof (group_img stU L U1 hm Q2); lia|].
        intros (p & n & Hin & Hpn). destruct (wL_in stU L (WF_live stU L U1) p n Hin) as (y & kk & o2 & r & Hy & Hk & Sy).
        apply (ge_garb_app stU (WF_geom stU L U1) hm hi a Q2 GA). exists y, kk, p, n, o2, r. repeat split; try assumption; lia. }
      (* [comment removed for export] *)
      assert (Ei : (hi + 32 * rc) mod 32 = hi).
      { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        pose proof (glast_rng stU hm). unfold g_lastidx in *. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      rewrite Ei in H11.
      assert (SPm : (sp - 96) mod 16 = 0) by (destruct Hsp as (_ & _ & X); rewrite Zminus_mod, X; reflexivity).
      destruct (IH stU L MZ r6 rom hm hi ho (sp - 96) U1 REPZ Q2 Q3 Q4 DEPh Q7 ltac:(kept_rw K6; exact G10) H11
                  ltac:(kept_rw K6; kept_rw K5; kept_rw K4; kept_rw K3; exact D2) ltac:(rewrite H1; reflexivity)
                  ltac:(lia) ltac:(lia) SPm)
        as (st7 & M7 & r7 & RUN7 & W7 & R7 & B7 & L7 & C7 & NJ7 & RET7 & K7 & FS7 & FR7).
      { eapply defined_grows; [eapply mem_grows_trans; [exact GM1 | eapply mem_grows_trans; [exact GD | eapply mem_grows_trans; [exact GU | exact GZ]]]|].
        intros a Ha. apply DEFd. lia. }
      rewrite H1 in RUN7. replace (Z_to_bv 64 0x624a8) with (0x624a8%bv : word) in RUN7 by (apply bv_eq; reflexivity).
      destruct (segFGn3 m r7 rom M7 (getr r7 10) ltac:(kept_rw K7; kept_rw K6; kept_rw K5; exact F19) eq_refl) as (r8 & RUN8 & I12 & I10 & K8).
      assert (FR78 : FR L (sp - 96 * (Z.of_nat (S d') + 1)) (sp - 48) MM1 M7).
      { eapply FR_trans; [eapply FR_widen; [| |exact FRZ]; lia|]. eapply FR_widen; [| |exact FR7]; lia. }
      destruct (fm_stage (sp - 96 * (Z.of_nat (S d') + 1)) st7 M7 r8 (getr r7 10) (getr r7 11) ltac:(lia) W7 R7
                  ltac:(rewrite L7, U4; left; reflexivity) ltac:(rewrite C7; exact U4c) I10
                  ltac:(kept_rw K8; kept_rw K7; kept_rw K6; kept_rw K5; kept_rw K4; kept_rw K3; exact D2)
                  ltac:(kept_rw K8; kept_rw K7; kept_rw K6; kept_rw K5; kept_rw K4; kept_rw K3; exact D18)
                  ltac:(kept_rw K8; kept_rw K7; kept_rw K6; kept_rw K5; kept_rw K4; kept_rw K3; exact D9)
                  I12 ltac:(kept_rw K8; reflexivity) RET FR78
                  ltac:(eapply mem_grows_trans; [exact GM1 | eapply mem_grows_trans; [exact GD | eapply mem_grows_trans; [exact GU | eapply mem_grows_trans; [exact GZ | exact (proj1 FR7)]]]]))
        as (st' & M' & r' & RUN9 & W' & R' & B' & L' & RG' & C' & SL' & E10 & E11' & E1 & E2 & E8 & E9 & E18 & E19 & K9 & FS9 & FR9).
      exists st', M', r'. split.
      { eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
        eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|].
        eapply msteps_trans; [exact RUN8 | exact RUN9]. }
      split; [exact W'|]. split; [exact R'|]. split; [rewrite B', B7; exact U3|].
      split; [rewrite L', L7, U4; cbn; rewrite Z.eqb_refl; apply zremove_notin; exact m_not_limbo|].
      split; [rewrite C', C7; exact U4c|].
      split; [intros x kk o Hx Hk E; destruct (SL' x kk o Hx Hk E) as (Hx0 & Hk0 & E0); exact (NJ7 x kk o Hx0 Hk0 E0)|].
      split.
      { destruct RET7 as [[Z11 RG7]|(b & len & x & PERM & B10 & B11 & LEN)].
        - left. split; [rewrite E11'; exact Z11 | rewrite RG', RG7; exact Q1].
        - right. exists b, len, x. rewrite RG', <- Q1. split; [exact PERM|]. split; [rewrite E10; exact B10|]. split; [rewrite E11'; exact B11 | exact LEN]. }
      split.
      { apply (keeps_final regs r' ((clobN0 ++ clobD) ++ ((clobDQ ++ [11; 13; 14]%bv ++ clobACT) ++ ([11; 12; 13; 14]%bv ++ ([1; 8; 10; 12; 19]%bv ++ (gm_clob ++ ([1; 11; 12]%bv ++ (NTF_CLOB ++ ([10; 12]%bv ++ ([13; 18]%bv ++ clobE)))))))))).
        - eapply keeps_join; [exact K1|]. eapply keeps_join; [exact K2|]. eapply keeps_join; [exact K3|]. eapply keeps_join; [exact K4|].
          eapply keeps_join; [exact K5|]. eapply keeps_join; [exact K6|]. eapply keeps_join; [exact K7|]. eapply keeps_join; [exact K8 | exact K9].
        - apply COV2. reflexivity.
        - exact E1. - rewrite E2, H2; reflexivity. - exact E8. - exact E9. - exact E18. - exact E19. }
      split; [eapply fsub_trans; [exact US | eapply fsub_trans; [exact FS7 | exact FS9]]|].
      exact FR9.
  Qed.
End FreeArm.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Run.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Theorem ntf_run : forall d, NTF_SPEC d.
  Proof using.
    induction d as [|d IHd].
    all: unfold NTF_SPEC; intros st L M regs rom m i off sp HWF HREP Hgrp Hi Hslot Hdep OJ H10 H11 H2 RET Hspd Hsp64 Hsp16 DEF.
    all: assert (Hsp : CEIL + 96 <= sp /\ sp < 2 ^ 64 /\ sp mod 16 = 0) by (split; [lia | split; [exact Hsp64 | exact Hsp16]]).
    all: assert (SOK : store_ok RSEGS M (Z_to_bv 64 (sp - 96)) 96%nat = true)
           by (eapply store_ok_defined; [exact DEF | lia | cbn; lia | ceil; lia | exact Hsp64]).
    all: destruct (ntf_head st L M m i off sp HWF HREP Hgrp Hi Hslot Hsp SOK regs rom H10 H11 H2) as (r1 & pc1 & RUN1 & C10 & C11 & C12 & C13 & C2 & C9 & K1 & HP).
    all: pose proof (M1_FR st L M sp Hsp regs) as FR01.
    all: destruct HP as [[-> PATH]|(-> & Hall & C18)].
    1,3: destruct (ntf_nofree st L M m i off sp HWF HREP Hgrp Hi Hslot Hsp regs rom r1 RET H2 C10 C11 C12 C13 C2 C9 K1 PATH OJ)
          as (st' & M' & r' & RUN2 & W' & R' & B' & L' & RG' & C' & NJ' & E11 & K' & FS' & FR');
         exists st', M', r'; split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|];
         split; [exact W'|]; split; [exact R'|]; split; [exact B'|]; split; [exact L'|]; split; [exact C'|]; split; [exact NJ'|];
         split; [left; split; [exact E11 | exact RG']|]; split; [exact K'|]; split; [exact FS'|];
         (eapply FR_trans; [eapply FR_widen; [| |exact FR01] | eapply FR_widen; [| |exact FR']]; lia).
    - destruct (ntf_freearm st L M m i off sp HWF HREP Hgrp Hi Hslot Hsp SOK regs rom OJ Hall 0%nat r1 I Hdep C10 C12 C2 C9 C18 K1 RET H2 Hspd DEF)
        as (st' & M' & r' & RUN2 & W' & R' & B' & L' & C' & NJ' & RT & K' & FS' & FR').
      exists st', M', r'; split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
      repeat (split; [assumption|]). eapply FR_trans; [eapply FR_widen; [| |exact FR01] | eapply FR_widen; [| |exact FR']]; lia.
    - destruct (ntf_freearm st L M m i off sp HWF HREP Hgrp Hi Hslot Hsp SOK regs rom OJ Hall (S d) r1 IHd Hdep C10 C12 C2 C9 C18 K1 RET H2 Hspd DEF)
        as (st' & M' & r' & RUN2 & W' & R' & B' & L' & C' & NJ' & RT & K' & FS' & FR').
      exists st', M', r'; split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
      repeat (split; [assumption|]). eapply FR_trans; [eapply FR_widen; [| |exact FR01] | eapply FR_widen; [| |exact FR']]; lia.
  Qed.
End Run.

Ltac lia_pairs ::= idtac.

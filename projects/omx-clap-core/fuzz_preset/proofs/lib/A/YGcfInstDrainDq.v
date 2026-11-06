(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstDrainDq.v (commit 67deba317dfb, blob bbdd9a7432ec) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfBatch ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG04 YGcfRoom YG06bcf.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Section D.
Variable B : asyms.

Lemma atok_cd_returns_cf : forall ns c z S S' (P : bool -> unit * astate -> Prop),
atok ns (cache_dealloc c z S) P -> DMwalkIFA.cd_returns c z S S' -> exists ns', P ns' (tt, S').
Proof.
intros ns c z S S' P HA [HR|(c0 & old & dl & snap & k & g & HE & HG & HK)].
- rewrite HR in HA. exists ns. exact HA.
- rewrite HE in HA. cbn in HA. destruct HA as [_ HK']. unfold aGranted in HG. apply Z.eqb_eq in HG. subst g.
  specialize (HK' 1 ltac:(cbn; right; reflexivity)). rewrite HK in HK'. cbn in HK'.
  exists (progz (KMapFreeArray c0 old dl) 1). exact HK'.
Qed.

Lemma fa_len_room_cf : forall NMAXD S its zs,
DRq_cf B NMAXD S its zs -> fa_len (rg_free (reg S kBatchClass)) + max_cached kBatchClass / 2 <= 2 ^ 27.
Proof.
intros NMAXD S its zs (RX & _).
pose proof (proj1 RX) as W.
pose proof (wfr_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
unfold wf_class_cf in CL.

pose proof (YG06bcf.fa_len_bound_cf _ _ _ _ _ _ CL ltac:(reflexivity)) as FB.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S kBatchClass W ltac:(unfold kBatchClass; lia)) as MB.
change (class_size kBatchClass) with 8192 in FB. change (max_cached kBatchClass / 2) with 1.
unfold kFreeArrayOffset in MB. lia.
Qed.

Lemma drq_cd_cf : DMwalkIFA.drq_cd (DRq_cf B kQuarantineMax) RMAXD_cf.
Proof.
intros S its z zs HD. pose proof HD as (RX & CD & UQ & Q1 & Q2 & SZ & PB & CI & HHO).
pose proof (proj1 RX) as W.
pose proof (wfr_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
unfold wf_class_cf in CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F0 FM]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
pose proof (YG04.fa_len_nonneg (rg_free (reg S kBatchClass)) (wrc_runs _ _ _ _ _ _ CL)) as FN.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S kBatchClass W ltac:(unfold kBatchClass; lia)) as MB.
pose proof (fa_len_room_cf _ S its (z :: zs) HD) as FA27.

assert (HCI : st_cache_inited S = true) by (apply CI; right; intros E; discriminate E).

pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 (proj2 RX))))) as SLOTS.
destruct RX as (_ & _ & _ & _ & SF & _).
pose proof (proj1 (Forall_forall _ _) SF z ltac:(apply in_app_iff; left; left; reflexivity)) as (Z1 & Z2 & Z3).
pose proof (wrc_cache _ _ _ _ _ _ CL) as PC. rewrite HCI in PC. destruct PC as [PM PL].
split.
-
  unfold DMwalkIFA.cd_model. unfold RMAXD_cf, kFreeArrayOffset in *.
  split; [unfold kBatchClass; lia|]. split; [exact HCI|]. split; [exact PL|]. split; [exact PM|].
  split; [lia|]. split; [lia|]. split; [exact Z2|]. split; [exact Z3|].
  split; [lia|]. split; [exact A2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FM|].
  split; [exact FA27|].

  intros HG. pose proof (YG06bcf.fa_len_bound_cf _ _ _ _ _ _ CL ltac:(reflexivity)) as FBB.
  change (class_size kBatchClass) with 8192 in FBB. change (max_cached kBatchClass / 2) with 1 in HG.
  unfold kFreeArrayMapSize, kFreeArrayMax in *. lia.
-
  intros S' HRet.
  assert (OK : atok true (cache_dealloc kBatchClass z S)
    (cache_dealloc_post_cf (as_universe B) 0 0 0 S kBatchClass (z - region_off kBatchClass)))
    by (apply (cache_dealloc_ok_cf (as_universe B) 0 0 0 S kBatchClass z true W ltac:(unfold kBatchClass; lia));
        [lia | exact Z2 | exact Z3]).
  destruct (atok_cd_returns_cf _ _ _ _ _ _ OK HRet) as (ns' & POST).
  unfold cache_dealloc_post_cf in POST. cbv zeta in POST. cbn [snd] in POST.
  destruct POST as (W' & RO & CI' & AU & CE & MF & LEN).
  pose proof RO as (EC & ES & ESA & ESR & EQT & EQG & EFS & EDP & EII & ENV).

  assert (EQI : q_items S' = q_items S)
    by (unfold q_items, all_batches; rewrite EQT, EQG; reflexivity).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  +
    destruct HD as ((_ & IT & ND & BL & SF' & NDS) & _).
    split; [exact W'|]. split.
    * rewrite EC. exact IT.
    * split; [rewrite EQI; exact ND|]. split; [exact BL|].
      rewrite app_nil_r in SF', NDS. cbn [map] in *. rewrite app_nil_r. apply NoDup_cons_iff in NDS as [HZ NDS'].
      split; [|exact NDS'].
      apply Forall_forall. intros y Hy.
      pose proof (proj1 (Forall_forall _ _) SF' y ltac:(right; exact Hy)) as (Y1 & Y2 & Y3).
      rewrite (AU kBatchClass ltac:(unfold kBatchClass; lia)). split; [exact Y1|]. split; [exact Y2|].
      intros Hin. destruct (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[EY _]|Hold]; [|exact (Y3 Hold)].

      apply HZ. replace z with y by lia. exact Hy.
  +
    intros c' Hc'. pose proof (CD c' Hc') as CD'. unfold cdef in *.
    rewrite (AU c' ltac:(lia)), (LEN c' ltac:(lia)), Nat2Z.inj_add.
    destruct (Z.eqb_spec c' kBatchClass) as [->|NE].
    * replace (kBatchClass =? kBatchClass) with true in * by (symmetry; apply Z.eqb_refl).
      cbn [length] in CD'. rewrite Nat2Z.inj_succ in CD'. cbn [Z.of_nat]. lia.
    * replace (c' =? kBatchClass) with false in * by (symmetry; apply Z.eqb_neq; exact NE). cbn [Z.of_nat]. lia.
  +
    unfold unq_cf, quar_n, queued_n in *. rewrite EC, EQI. exact UQ.
  + rewrite EQT. exact Q1.
  + rewrite EQG. exact Q2.
  + exact SZ.
  + exact PB.
  + intros _. exact CI'.
  +
    apply (cf_hull_counts _ S); [unfold nsec_cf; rewrite ES; reflexivity | unfold sec_T_cf; rewrite ES; reflexivity | exact HHO].
Qed.

End D.
End U.

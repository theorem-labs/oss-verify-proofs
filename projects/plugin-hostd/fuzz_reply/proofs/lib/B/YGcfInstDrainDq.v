(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b (a working branch): the bookkeeping field of
   H3's CacheDealloc contract, [DMwalkIF.drq_cd] at DRq := YGcfInstDrainR.DRq_cf B kQuarantineMax and RMAXD :=
   RMAXD_cf.  It says that a pending BATCH OBJECT meets CacheDealloc's model premises, and that the invariant
   moves to the rest of the list at whichever state the model returns (DMwalkIF.cd_returns, b1-drain
   215f6356933: the immediate IRet, or the granted answer of the free-array growth's KMapFreeArray).
   Both results come from ONE model lemma: YG03cf.cache_dealloc_ok_cf's [atok] post holds along every path the
   machine can follow, the granted arm included (YG01.atok's IAsk case takes every [aok] answer, and the only
   granted one is 1, YG00.v:604).
   This file is instance glue, not layer: it imports the walk's interface (DMwalkIF), which carries cgif's image,
   so the image-free files (YGcfInstDrainR / X / Q / Cm / Cn / Cg / Cl / RL) do not import it.
   rule 24: no function proved (kind: interface-instance discharge of one invariant field). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfBatch ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DMspec DMiface DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstDrainR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG04 YGcfRoom YG06bcf.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Section D.
Variable B : asyms.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The two results of the model's CacheDealloc, from one [atok] post.                                            *)
(* [cd_returns] names the immediate return and the granted continuation of the free-array growth; [atok] covers
   both, so one application of the model's lemma serves them.  (The refusal arm spins, which [atok] excludes.) *)
Lemma atok_cd_returns_cf : forall ns c z S S' (P : bool -> unit * astate -> Prop),
atok ns (cache_dealloc c z S) P -> DMwalkIF.cd_returns c z S S' -> exists ns', P ns' (tt, S').
Proof.
intros ns c z S S' P HA [HR|(c0 & old & dl & snap & k & g & HE & HG & HK)].
- rewrite HR in HA. exists ns. exact HA.
- rewrite HE in HA. cbn in HA. destruct HA as [_ HK']. unfold aGranted in HG. apply Z.eqb_eq in HG. subst g.
  specialize (HK' 1 ltac:(cbn; right; reflexivity)). rewrite HK in HK'. cbn in HK'.
  exists (progz (KMapFreeArray c0 old dl) 1). exact HK'.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The field.                                                                                                    *)
(* The free array's own numbers come from the invariant, not from a new premise: the class's elements are distinct
   multiples of its size below the allocated part (YG01cf.wrc_elems / wrc_nodup), so their count - and with it the
   free array's length - is at most rg_alloc_user / class_size, far below the 2 ^ 27 the walk asks; the deficit
   clause of DRq_cf states that count exactly. *)
Lemma fa_len_room_cf : forall NMAXD S its zs,
DRq_cf B NMAXD S its zs -> fa_len (rg_free (reg S kBatchClass)) + max_cached kBatchClass / 2 <= 2 ^ 27.
Proof.
intros NMAXD S its zs (RX & _).
pose proof (proj1 RX) as W.
pose proof (wfr_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
unfold wf_class_cf in CL.
(* the free array's elements are distinct multiples of class_size below the allocated part (YG06bcf.v:406) *)
pose proof (YG06bcf.fa_len_bound_cf _ _ _ _ _ _ CL ltac:(reflexivity)) as FB.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 S kBatchClass W ltac:(unfold kBatchClass; lia)) as MB.
change (class_size kBatchClass) with 8192 in FB. change (max_cached kBatchClass / 2) with 1.
unfold kFreeArrayOffset in MB. lia.
Qed.

Lemma drq_cd_cf : DMwalkIF.drq_cd (DRq_cf B kQuarantineMax) RMAXD_cf.
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
(* the flag: the list of batch objects is not empty, so DRq_cf's guarded conjunct fires *)
assert (HCI : st_cache_inited S = true) by (apply CI; right; intros E; discriminate E).
(* the batch object's slot, from the recycle invariant *)
pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 (proj2 RX))))) as SLOTS.
destruct RX as (_ & _ & _ & _ & SF & _).
pose proof (proj1 (Forall_forall _ _) SF z ltac:(apply in_app_iff; left; left; reflexivity)) as (Z1 & Z2 & Z3).
pose proof (wrc_cache _ _ _ _ _ _ CL) as PC. rewrite HCI in PC. destruct PC as [PM PL].
split.
- (* cd_model at the batch class *)
  unfold DMwalkIF.cd_model. unfold RMAXD_cf, kFreeArrayOffset in *.
  split; [unfold kBatchClass; lia|]. split; [exact HCI|]. split; [exact PL|]. split; [exact PM|].
  split; [lia|]. split; [lia|]. split; [exact Z2|]. split; [exact Z3|].
  split; [lia|]. split; [exact A2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FM|].
  split; [exact FA27|].
  (* the growth clause: the free array's length is tiny next to its cap, so a growth still fits *)
  intros HG. pose proof (YG06bcf.fa_len_bound_cf _ _ _ _ _ _ CL ltac:(reflexivity)) as FBB.
  change (class_size kBatchClass) with 8192 in FBB. change (max_cached kBatchClass / 2) with 1 in HG.
  unfold kFreeArrayMapSize, kFreeArrayMax in *. lia.
- (* the invariant at either result *)
  intros S' HRet.
  assert (OK : atok true (cache_dealloc kBatchClass z S)
    (cache_dealloc_post_cf (as_universe B) 0 0 0 S kBatchClass (z - region_off kBatchClass)))
    by (apply (cache_dealloc_ok_cf (as_universe B) 0 0 0 S kBatchClass z true W ltac:(unfold kBatchClass; lia));
        [lia | exact Z2 | exact Z3]).
  destruct (atok_cd_returns_cf _ _ _ _ _ _ OK HRet) as (ns' & POST).
  unfold cache_dealloc_post_cf in POST. cbv zeta in POST. cbn [snd] in POST.
  destruct POST as (W' & RO & CI' & AU & CE & MF & LEN).
  pose proof RO as (EC & ES & ESA & ESR & EQT & EQG & EFS & EDP & EII & ENV).
  (* the chunk list and the queues are the entry's, so every clause over them carries over *)
  assert (EQI : q_items S' = q_items S)
    by (unfold q_items, all_batches; rewrite EQT, EQG; reflexivity).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  + (* the recycle invariant: WfR_cf is the post's, and the lists are the entry's *)
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
      (* the pushed object is z itself, which NoDup keeps apart from the rest *)
      apply HZ. replace z with y by lia. exact Hy.
  + (* the class deficit: the dealloc adds exactly one element of the batch class *)
    intros c' Hc'. pose proof (CD c' Hc') as CD'. unfold cdef in *.
    rewrite (AU c' ltac:(lia)), (LEN c' ltac:(lia)), Nat2Z.inj_add.
    destruct (Z.eqb_spec c' kBatchClass) as [->|NE].
    * replace (kBatchClass =? kBatchClass) with true in * by (symmetry; apply Z.eqb_refl).
      cbn [length] in CD'. rewrite Nat2Z.inj_succ in CD'. cbn [Z.of_nat]. lia.
    * replace (c' =? kBatchClass) with false in * by (symmetry; apply Z.eqb_neq; exact NE). cbn [Z.of_nat]. lia.
  + (* the deficit and the byte bounds read the chunks and the queues only *)
    unfold unq_cf, quar_n, queued_n in *. rewrite EC, EQI. exact UQ.
  + rewrite EQT. exact Q1.
  + rewrite EQG. exact Q2.
  + exact SZ.
  + exact PB.
  + intros _. exact CI'.
  + (* the admission: CacheDealloc keeps st_secs (regs_only), so both meters are the entry's *)
    apply (cf_hull_counts _ S); [unfold nsec_cf; rewrite ES; reflexivity | unfold sec_T_cf; rewrite ES; reflexivity | exact HHO].
Qed.

End D.
End U.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanCtrlProps SizeHist Gap AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Context {SBc PAc : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation apost := (AsanNodeSem.apost ATOP).
Local Notation atot := (atotal (aok34 (ATOP:=ATOP) (SBc:=SBc) (PAc:=PAc)) apost).
Local Notation SBP st := (a_space_beg st = SBc /\ a_ptr_array st = PAc) (only parsing).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).
#[using="Type"] Lemma drain_norec_ok : forall R (P : R -> Model -> Prop) st (k : astate -> AM R) mo,
INV [] [] st mo -> a_qglob_bytes st + a_qloc_bytes st <= Q_MAX ->
(forall st' mo', INV [] [] st' mo' -> a_live st' = a_live st -> a_next st' = a_next st -> a_qloc_bytes st' = 0 ->
a_qglob_bytes st' = a_qglob_bytes st + a_qloc_bytes st -> VC st' = VC st -> (forall c, get_cls st' c = get_cls st c) -> atot (k st') mo' P) ->
atot (drain st k) mo P.
Proof.
intros R P st k mo HI HQ Hk. pose proof HI as [HA HM]. pose proof HA as (_ & _ & HBW & Hb1 & Hb2 & _).
unfold drain. cbv zeta. cbn [a_qglob a_qglob_bytes a_qloc a_qloc_bytes set_qloc].
set (st1 := set_qglob (a_qglob st ++ a_qloc st) (a_qglob_bytes st + a_qloc_bytes st) (set_qloc [] 0 st)).
assert (HI1 : INV [] [] st1 mo).
{ unfold st1. apply (INV_requeue [] [] [] st [] 0 _ _ mo HI).
- unfold qbatches. cbn [app]. rewrite !qchunks_app. apply Permutation_app_comm.
- unfold qbatches. cbn [app]. rewrite !zlen_app. Local Ltac2 Set LiaHints.tbl := fun () => "0030>14801083991.2026751509411.1831114173809.1800000900B00CS2HQ4HbigS3Hb13Hb2S".
lia.
- unfold qbatches in HBW. cbn [app] in *. apply Forall_app in HBW as [X Y]. apply Forall_app; split; assumption.
- reflexivity.
- rewrite bsum_app. lia. }
change (a_qglob_bytes st1) with (a_qglob_bytes st + a_qloc_bytes st).
destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st + a_qloc_bytes st)) as [Hbig|Hsmall]; [lia|].
apply Hk; auto; unfold st1; cbn; try reflexivity. all: (intros; reflexivity).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma INV_qbytes_nonneg : forall st mo, INV [] [] st mo -> 0 <= a_qloc_bytes st /\ 0 <= a_qglob_bytes st.
Proof.
intros st mo HI. pose proof HI as [HA HM]. pose proof HA as (_ & _ & HBW & Hb1 & Hb2 & _).
unfold qbatches in HBW. cbn [app] in HBW. apply Forall_app in HBW as [X Y].
pose proof (bsum_nonneg _ X). pose proof (bsum_nonneg _ Y). Local Ltac2 Set LiaHints.tbl := fun () => "0010>47663917259.1500000>S3Hb13Hb21H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition free_post_g (st : astate) (id : AsanCtrl.aptr) (ch : achunk) (st' : astate) (mo' : Model) : Prop :=
free_post (RESV:=RESV) (ATOP:=ATOP) st id st' mo'
/\ a_qloc_bytes st' + a_qglob_bytes st' <= a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES.
#[using="Type"] Theorem afree_core_g : forall st mo id ch,
INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> (a_live st) !! id = Some ch ->
a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES <= Q_MAX ->
FAINV st -> VC st + 2^19 <= VCMAX -> SBP st ->
atot (afree st (Some id)) mo (free_post_g st id ch).
Proof.
intros st mo id ch HI Hql Hqg Hl HG HFA HVC HSBP.
assert (HFA1 : FAINV (set_live (delete id (a_live st)) st)) by (eapply FAINV_frame; [| exact HFA]; intros; reflexivity).
assert (HVC1 : VC (set_live (delete id (a_live st)) st) = VC st) by reflexivity.
pose proof (INV_qbytes_nonneg st mo HI) as [Hl0 Hg0].
pose proof (INV_live_to_hand st id ch mo HI Hl) as HI1.
set (st1 := set_live (delete id (a_live st)) st) in *.
assert (Hwf : chunk_wf ch).
{ destruct HI1 as [HA1 _]. destruct HA1 as (_ & HW1 & _). rewrite all_chunks_cons in HW1. apply Forall_cons_iff in HW1 as [X _]. exact X. }
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10789184491.4515728214422.3615732446970.4518928695579.4523650754571.3638053082122.3646150050660.2446150050660.2561549098435.2565846976092.2500000=00J00Z00a01001:01?01D01Q01bS2E22E32E42F2S2HG2E22E32E4S2HG2E22E32E42F2S2E22F2S2E23Hsm3Hqg2E3S2E22E32E4S3HwfS3HwfS4Hszb6HsmallS2HG3Hl03Hg04Hbig".
assert (Hszb : 0 <= chunk_size ch <= 2^30) by (destruct ch; cbn in Hwf |- *; lia).
unfold afree. rewrite Hl. fold st1. cbv zeta.
destruct (Z.leb_spec (chunk_size ch) Q_MAX) as [Hsmall|Hbig]; [| unfold Q_BATCH_BYTES in HG; lia].
apply (enqueue_ok _ _ st1 ch (chunk_size ch) _ mo HI1 eq_refl ltac:(lia)); try (unfold st1; cbn; assumption).
all: try exact HFA1. all: try (fold st1 in HVC1; rewrite HVC1; exact HVC).
intros st2 mo2 HI2 E1 E2 E3 E4 HFA2 HVC2 HSBP2. unfold st1 in E1, E2, E3, E4. cbn [a_live a_next a_qglob_bytes a_qloc_bytes set_live] in E1, E2, E3, E4.
fold st1 in HVC1. rewrite HVC1 in HVC2.
destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [Hbig|Hsm].
- apply (drain_norec_ok _ _ st2 _ mo2 HI2); [lia|]. intros st3 mo3 HI3 F1 F2 F3 F4 FV FC. apply atotal_ret. unfold free_post_g, free_post.
rewrite F1, F2, E1, E2, F3, F4. unfold st1. cbn. unfold Q_CACHE.
split; [| lia]. split; [exact HI3|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [eapply FAINV_frame; [exact FC| exact HFA2]| rewrite FV; exact HVC2].
- apply atotal_ret. unfold free_post_g, free_post. rewrite E1, E2. unfold st1. cbn.
split; [| lia]. split; [exact HI2|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HFA2| exact HVC2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithResv.

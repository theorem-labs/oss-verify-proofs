(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "modulo"; "div"; "of_nat"; "leb"; "mul"; "shiftr"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "False"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "pair"; "option"; "prod"; "list"; "bool"; "cons"; "fst"; "nat"; "true"; "Some"; "snd"; "None"; "app"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_live"; "sec_chunk"; "AA"; "aa_frames"; "aa_geom"; "ag_fsb"; "ag_spacebeg"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_sec"; "ageom"; "sc_map_beg"; "sc_map_size"; "topG"; "frames_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_mut_addrA"; "client_owned_shadowA"; "frame_flag"; "alloc_lawsA"; "client_addrA"; "pairwise_disjoint"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "FS_total"; "rz"; "FS_frames_off"; "Size"; "fs_frame"; "fs_num_iter"; "kUserSpaceSize"; "region_beg"; "fs_frame_size"; "kCompactPtrScale"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "maskv"; "acell"; "cells_footb"; "RTC_A"; "c_addr"; "c_w"; "rtc_cells_img"; "G0"; "bview"; "cst_ok"; "restrictv"; "rtc_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "IA_BEG"; "QG"; "SEC_INST"; "IA_END"; "rtc_extra"; "AInvA"; "busyb"; "depot_wf"; "fs_inv"; "ia_inv"; "live_block_repr"; "live_ids"; "misc_inv"; "primary_repr"; "q_foot"; "quarantine_repr"; "secondary_repr"; "thread_inv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.AllocLaws"; "inv_img"; "cst_inv_okb"; "inv_img_ranges"; "ranges_apartb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.AllocLaws.L"; "fr_apart"; "pw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "DEPOT"; "MAP1"; "MAP1N"; "NFBLK"; "STORE"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition inv_img (z : Z) : Prop := ltac2:(tb__ "0|0|
SfSdS19S52S61Vz;A2S1dA3SfScS1S5fVz;A2S3Vz;Zee070A2A2SfScS1S2S5eZ40A2Vz;A2S3Vz;S2S5eZc0A2A2A2SfScS1S5dVz;A2S3Vz;S60A2A2SfScS1Z180e88Vz;A2S3Vz;Z180e8cA2A2S7eVz;A1A2A2A2A2A2").
Lemma inv_img_lt : ltac2:(tb__ "0|0|
S0S70R1A1S3R2S42A2F_;Fz;").
Proof.
  intros z H. unfold inv_img, SEC_INST, QG, IA_BEG, IA_END, IMG_HI in *.
  destruct H as [H|[H|[H|[H|[H|H]]]]]; try lia.
  - unfold cells_footb, rtc_extra in H. cbn [existsb] in H. unfold in_cellb in H. cbn [c_addr c_w Z.of_nat] in H.
    repeat (apply orb_prop in H as [H|H]; [apply andb_prop in H as [_ H]; apply Z.ltb_lt in H; cbn in H; lia|]). discriminate.
  - pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.dstat_img z H) as X. unfold IMG_HI in X. lia.
Qed.

Definition inv_img_ranges : list (Z * Z) := ltac2:(tb__ "0|2|
S21S17S0S0A2M0S74S51G0S51S15S0S0S54R1A1S8S55R1A1A1A4Lc;S61A4S1aG0S15S0S0S5fS4Zee070S5fA2A4S1aG0S15S0S0S2S5eZ40A2Z80A4S1aG0S15S0S0S5dS4S60S5dA2A4S1aG0S15S0S0Z180e88Z4A4S1aG0S15S0S0S79S4S2S7aSaZ8S7bA2A2S79A2A4S1aG0S15S0S0S7dS2Z10M1SaG1S7cA2A2A4S23G0A1A3A3A3A3A3A3A3").
Lemma inv_img_ranges_ok : ltac2:(tb__ "0|0|
S0S70R1A1S4fS72R2A2F_;Fz;").
Proof.
  intros z H. unfold inv_img_ranges, in_rangesZ. destruct H as [H|[H|[H|[H|[H|H]]]]].
  - unfold cells_footb in H. apply existsb_exists in H as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    exists (c_addr c), (Z.of_nat (c_w c)). split; [|lia]. apply in_or_app. left. apply in_map_iff. exists c. split; [reflexivity | exact Hc].
  - exists SEC_INST, (0xee070 - SEC_INST). split; [apply in_or_app; right; cbn; tauto | lia].
  - exists (QG + 64), 128. split; [apply in_or_app; right; cbn; tauto | lia].
  - exists IA_BEG, (IA_END - IA_BEG). split; [apply in_or_app; right; cbn; tauto | lia].
  - exists 0x180e88, 4. split; [apply in_or_app; right; cbn; tauto | lia].
  - destruct H as [H|H].
    + exists DEPOT, (MAP1 + 8 * MAP1N - DEPOT). split; [apply in_or_app; right; cbn; tauto | lia].
    + exists STORE, (16 + 16 * NFBLK). split; [apply in_or_app; right; cbn; tauto | lia].
Qed.
Definition ranges_apartb (l1 l2 : list (Z * Z)) : bool := ltac2:(tb__ "0|3|
S3fS17S0S0A2M0G0S3fG0G0S24S9S2S1bS0S0R2A3M1S1fS0S0R2A3A2S1bS0S0R1A3M2A2S9S2G2S1fS0S0R1A3A2G1A2A2Lr2;Vl2;A3Lr1;Vl1;A3").
Lemma ranges_apartb_sound : ltac2:(tb__ "0|1|
S18S17S0S0A2A1M0G0SdS19S73R2R1A2S1dA3S0S4fR4R1A2S4fR4R2A2S11F_;F_;Fa;F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H a (b1 & n1 & I1 & R1) (b2 & n2 & I2 & R2). unfold ranges_apartb in H.
  pose proof (proj1 (forallb_forall _ _) H (b1, n1) I1) as H1. cbn beta in H1. pose proof (proj1 (forallb_forall _ _) H1 (b2, n2) I2) as H2. cbn [fst snd] in H2.
  apply orb_prop in H2 as [X|X]; apply Z.leb_le in X; lia.
Qed.
Definition cst_inv_okb (CST : list (Z * Z)) : bool := ranges_apartb CST inv_img_ranges.
Lemma cst_inv_ok : ltac2:(tb__ "0|0|
S18S17S0S0A2A1SdS19S71R1A1S1dA3S0S4fR3R1A2SeS70R2A1A1F_;Fa;F_;FCST;").
Proof. intros CST H a Ha Hi. exact (ranges_apartb_sound _ _ H a Ha (inv_img_ranges_ok a Hi)). Qed.

Section L.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.

Hypothesis HCSTI : ltac2:(tb__ "0|0|
S0S4fVCST;R1A2SeS70R2A1A1F_;Fa;").
Let AInv := AInvA segsA.
Let view := view segsA.

Lemma law_client_app_A : ltac2:(tb__ "0|1|
S27S36S18S12Q40A1A1S6fS0VAInv;R5R4R3R2A4S3bVCST;R6R2A3SfScS1S33S29R7A1A1M0R3A2S3R3S5Z2Z2fA2A2A2SfScScS1S42R3A2S3R3G0A2A2SfS3R3S44A2S1S43R3A2A2A2ScS1Z0R3A2S3R3S42A2A2A2A2F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a (HG & HR & HF & HRest & HM & HI3 & HB) Hcl.
  destruct HRest as (Hsep & _).
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). rewrite FS_total_val in F2.
  pose proof (proj1 (geom_bands _ HG)) as WB. rewrite FS_total_val in WB.
  destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
  - left. exact S.
  - right; left. destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & _ & _ & _ & _ & S8).
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - right; left. destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - right; right. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
  - right; left. destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Definition pw {T} (R : T -> T -> Prop) (l : list T) : Prop :=
  forall i j x y, (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Lemma pw_app : forall T (R : T -> T -> Prop) l1 l2,
  pw R l1 -> pw R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> pw R (l1 ++ l2).
Proof.
  intros T R l1 l2 H1 H2 H12 i j x y Hij Hi Hj.
  destruct (Nat.lt_ge_cases i (length l1)) as [Li|Li]; destruct (Nat.lt_ge_cases j (length l1)) as [Lj|Lj].
  - rewrite nth_error_app1 in Hi, Hj by assumption. exact (H1 i j x y Hij Hi Hj).
  - rewrite nth_error_app1 in Hi by assumption. rewrite nth_error_app2 in Hj by assumption.
    exact (H12 x y (nth_error_In _ _ Hi) (nth_error_In _ _ Hj)).
  - lia.
  - rewrite nth_error_app2 in Hi, Hj by assumption. apply (H2 (i - length l1)%nat (j - length l1)%nat x y); [lia | exact Hi | exact Hj].
Qed.
Lemma lnodup_pos : forall (T U : Type) (f : T -> U) (l : list T) i j x y,
  List.NoDup (map f l) -> (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> f x <> f y.
Proof.
  intros T U f. induction l as [|h l IH]; intros i j x y ND Hij Hi Hj; [destruct i; discriminate|].
  destruct j as [|j]; [lia|]. cbn [nth_error] in Hj. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. intros E. apply NI. rewrite E. apply in_map. exact (nth_error_In _ _ Hj).
  - cbn [nth_error] in Hi. apply (IH i j x y ND); [lia | exact Hi | exact Hj].
Qed.
Definition fr_apart (x y : Z * Z) : Prop := ltac2:(tb__ "0|2|
SfS1S2S1bS0S0Vx;A3M0S1fS0S0Vx;A3A2S1bS0S0Vy;A3M1A2S1S2G1S1fS0S0Vy;A3A2G0A2A2").

Lemma frames_of_pw : ltac2:(tb__ "0|5|
S0S18S18S17S0S0A2M0A1M1A1S0S1Z0M2R1A2S1S2R2S8S22G1R3A2A1A2ZbA2S1cG1SdS16G1A1S3eG1R6R2A3S1eG1R1A2A3ScS40S0S74G0S0S1bS0S0A2R2A4A2G0S3dG0R1R3A3ScScS1G2S1bS0S0R2A3M3A2S3G3S4aS2R8S8R5A1A2M4A1A2A2SdS0S1fS0S0R2A3S49RaG4G3A3A3A2F_;Fpf;A2F_;Fb;Fk;S78G0S77S34R4R5A2A3F_;F_;F_;Fc0;FB;FF;").
Proof.
  intros F. induction B as [|b B IH]; intros c0 Hc0 Hlen HB; [intros i j x y _ Hi; destruct i; discriminate|].
  cbn [frames_of]. cbn [length] in Hlen.
  destruct (HB 0%nat b eq_refl) as [NDb Hb]. rewrite Z.add_0_r in Hb.
  apply pw_app.
  - intros i j x y Hij Hi Hj. rewrite nth_error_map in Hi, Hj.
    destruct (nth_error b i) as [pi|] eqn:Ei; [|discriminate]. destruct (nth_error b j) as [pj|] eqn:Ej; [|discriminate].
    cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
    pose proof (lnodup_pos _ _ fst b i j pi pj NDb Hij Ei Ej) as NE.
    destruct (Hb pi (nth_error_In _ _ Ei)) as [R1 E1]. destruct (Hb pj (nth_error_In _ _ Ej)) as [R2 E2].
    unfold fr_apart. cbn [fst snd]. rewrite E1, E2. apply fs_frames_disjoint; lia.
  - apply (IH (c0 + 1)); [lia | lia |]. intros k b' Hk. specialize (HB (S k) b' Hk).
    replace (c0 + 1 + Z.of_nat k) with (c0 + Z.of_nat (S k)) by lia. exact HB.
  - intros x y Hx Hy. apply in_map_iff in Hx as (pi & <- & Hpi). destruct y as [f' s'].
    apply frames_of_in in Hy as (k & pos & Hk & Hin & ->).
    destruct (Hb pi Hpi) as [R1 E1].
    assert (Hnk : nth_error (b :: B) (S k) = Some (nth k B [])) by (cbn [nth_error]; apply nth_error_nth'; exact Hk).
    destruct (HB (S k) _ Hnk) as [_ Hb']. destruct (Hb' (pos, f') Hin) as [R2 E2]. cbn [fst snd] in R2, E2.
    unfold fr_apart. cbn [fst snd]. rewrite E1, E2. replace (c0 + 1 + Z.of_nat k) with (c0 + Z.of_nat (S k)) by lia.
    apply fs_frames_disjoint; lia.
Qed.

Lemma frames_pw : ltac2:(tb__ "0|0|
S27S36S18S12Q40A1A1S6fVAInv;R4R3R2R1A4S78S17S0S0A2S77S28R5A1A3F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & _). destruct HF as (Flen & Fcls & _). unfold aa_frames.
  apply (frames_of_pw (ag_fsb (aa_geom A))); [lia | rewrite Flen; lia|].
  intros k b Hk. assert (Lk : (k < length (aa_fs_busy A))%nat) by (apply nth_error_Some; rewrite Hk; discriminate). rewrite Flen in Lk.
  assert (Eb : fs_busy A (0 + Z.of_nat k) = b).
  { unfold fs_busy, nthZ. rewrite Z.add_0_l, Nat2Z.id. apply nth_error_nth. exact Hk. }
  destruct (Fcls (0 + Z.of_nat k) ltac:(unfold FS_NCLASSES; lia)) as [ND Hpf]. rewrite Eb in ND, Hpf. split; [exact ND | exact Hpf].
Qed.

Theorem law_blocks_A : ltac2:(tb__ "0|e|
S27S36S18S12Q40A1A1S6fVAInv;R4R3R2R1A4ScS3cS21S17S0S0A2M0S25R5A1S28R5A1A3A1ScS0S0S3dG0S15S0S0R2R1A4M1S25R7A1A3ScS1Z1M2R2A2ScSdS0S6R3Z10M3A2Z0M4A3ScS1Z1000M5R3A2ScS1S2S2R3R2A2M6Z800A2S33S29R8A1M7A1M8A2S1S42S4R3G5A2A2A2A2A2A2F_;Fn;Fb;S0S0S3dG0G1S28R7A1A3ScSdS0S6R3Z40M9A2G4A3ScSdS0S6R2G9A2G4A3ScS1G9R2A2ScS1S42R3A2ScS1G6G8A2ScS1S42S39G7S15S0S0R3R2A4A2MaA2ScS1S2GaG2A2G8A2ScS0S0S3dG0G1S25RaA1A3SfS1G6S39S29RbA1S15S0S0R6R5A4A2MbA2McS1S2GbG2A2MdS4R3G3A2A2A2F_;Fn;Fb;S0S0S3dG0G1S28RaA1A3SfGcS1GdR3A2A2F_;Fs';Ff';A2A2A2A2A2A2A2A2F_;Fs;Ff;A2A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & _).
  pose proof (geom_nums _ HG) as (F1 & F2 & F0 & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite FS_total_val in F2. rewrite kSpaceSize_val in SP2.
  assert (FRM : forall f s, In (f, s) (aa_frames A) -> exists c pos, 0 <= c < 11 /\ 0 <= pos < fs_num_iter c /\ s = fs_frame_size c /\ f = fs_frame (ag_fsb (aa_geom A)) c pos
                  /\ frame_flag (aa_geom A) (f, s) = fs_flags (ag_fsb (aa_geom A)) c + pos).
  { intros f s Hin. destruct (aa_frames_fact _ A _ _ HF Hin) as (c & pos & u & v & Hc & Hs & Eb & _ & Hpos & Hf & _).
    exists c, pos. split; [exact Hc|]. split; [exact Hpos|]. split; [exact Hs|]. split; [exact Hf|].
    unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite Hs, fs_class_of_size_ok by lia. rewrite Hf, fs_pos_frame by lia. reflexivity. }
  split; [|split].
  -
    intros i j b n b' n' Hij Hi Hj.
    destruct (Nat.lt_ge_cases i (length (aa_live A))) as [Li|Li]; destruct (Nat.lt_ge_cases j (length (aa_live A))) as [Lj|Lj].
    + rewrite nth_error_app1 in Hi, Hj by assumption. pose proof (rz_bound n); pose proof (rz_bound n'); destruct (live_pair_apart segsA A rho tp md i j b n b' n' HA Hij Hi Hj); lia.
    + rewrite nth_error_app1 in Hi by assumption. rewrite nth_error_app2 in Hj by assumption.
      pose proof (nth_error_In _ _ Hi) as Hin. pose proof (nth_error_In _ _ Hj) as Hin'.
      destruct (Hsep b n Hin) as (_ & _ & _ & S4 & _). rewrite FS_total_val in S4.
      destruct (FRM b' n' Hin') as (c & pos & Hc & Hpos & -> & -> & _).
      pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. lia.
    + lia.
    + rewrite nth_error_app2 in Hi, Hj by assumption.
      pose proof (frames_pw A rho tp md HA (i - length (aa_live A))%nat (j - length (aa_live A))%nat (b, n) (b', n') ltac:(lia) Hi Hj) as D.
      unfold fr_apart in D. cbn [fst snd] in D. exact D.
  -
    intros b n Hin. destruct (Hsep b n Hin) as (S1 & S2 & S3 & _).
    destruct (is_primary n) eqn:EP.
    + pose proof (live_prim_facts segsA A rho tp md b n HA Hin EP) as F. cbn zeta in F. set (c := ClassID (needed n)) in *.
      destruct F as (Hn & Hc & X0 & XM & XU & XS & S16 & RZ & RZ16).
      unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. pose proof (Size_pos c Hc) as SPc.

      split; [clear - Hn; lia|]. split; [|split; [clear - S2; unfold IMG_HI in S2; lia|split; [first [clear - Hn Hc X0 XU XS SP2; lia | nia] | clear - S2; lia]]].

      apply Z.mod_divide in XM; [|lia]. apply Z.mod_divide in S16; [|lia]. apply Z.mod_divide in RZ16; [|lia]. apply Z.mod_divide in SP0; [|lia].
      apply Z.mod_divide; [lia|].
      replace b with ((b - rz n - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) + rz n + ag_spacebeg (aa_geom A) + c * 2 ^ 32) by lia.
      apply Z.divide_add_r; [apply Z.divide_add_r; [apply Z.divide_add_r; [exact (Z.divide_trans _ _ _ S16 XM) | exact RZ16] |
        apply (Z.divide_trans _ (2 ^ 16)); [exists 4096; reflexivity | exact SP0]] | exists (c * 2 ^ 28); lia].
    + destruct (live_sec_facts segsA A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & MP & DI).
      destruct DI as (D1 & D2 & D3 & _). unfold PG in *.
      split; [lia|]. split; [|split; [unfold IMG_HI in S2; lia | split; [lia | lia]]].
      apply Z.mod_divide in MP; [|lia]. apply Z.mod_divide; [lia|]. rewrite Eb.
      apply Z.divide_add_r; [apply Z.divide_add_r; [apply (Z.divide_trans _ 4096); [exists 256; reflexivity | exact MP] | exists 256; reflexivity] | exists 128; reflexivity].
  -
    intros f s Hin. destruct (FRM f s Hin) as (c & pos & Hc & Hpos & -> & -> & ->).
    pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    + intros b n Hbn. destruct (Hsep b n Hbn) as (_ & _ & _ & S4 & _). rewrite FS_total_val in S4. lia.
    + intros f' s' Hin'. destruct (FRM f' s' Hin') as (c' & pos' & Hc' & Hpos' & -> & -> & _).
      pose proof (fs_geom_nums (aa_geom A) c' pos' HG Hc' Hpos') as M'. cbn zeta in M'. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M'. lia.
Qed.

Section Frame.
Variables (A : AA) (rho rho' : valuation) (tp : list word) (md : Model).
Hypothesis HA : ltac2:(tb__ "0|0|
VAInv;VA;Vrho;Vtp;Vmd;A4").
Hypothesis H1 : ltac2:(tb__ "0|1|
S12Q40M0A1SeS37VCST;VA;S13G0R1A2A3A1SeS38VA;S13G0R2A2A2A1SdS16S12Q8A1A1S35Vrho';R3A2S35Vrho;R3A2A3F_;F_;Fa;").
Hypothesis H2 : ltac2:(tb__ "0|4|
S12Q40M0A1S38VA;S13G0R1A2A2SeSdS16S12Q8A1M1A1M2S35Vrho;R2A2S20G1A1M3A3A1SeSdG2S35Vrho';R3A2G3A3A1F_;F_;Fa;").
Let m := view (rm rho).
Let m' := view (rm rho').
Let G := aa_geom A.

Lemma V1 : ltac2:(tb__ "0|0|
S0SeS37VCST;VA;R1A3A1SeS38VA;R2A2A1SdS16S12Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof.
  intros z N1 N2. unfold m, m', view. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
  2,3: rewrite !view_out by lia; reflexivity.
  rewrite !view_in by lia. unfold rd_of. rewrite H1; [reflexivity | rewrite u64_lit by lia; exact N1 | rewrite u64_lit by lia; exact N2].
Qed.

Let HG : geom_ok G. Proof. exact (proj1 HA). Qed.
Let HF : fs_inv (restrictv (fs_footb G) m) A. Proof. destruct HA as (_ & _ & H & _). exact H. Qed.
Let Hsep : live_sep A. Proof. destruct HA as (_ & _ & _ & (H & _) & _). exact H. Qed.

Lemma owned_range : ltac2:(tb__ "0|1|
S0S38VA;R1A2ScS1S41S2S2aVG;A1M0S47A2A1R2A2S3R2S41S2G0S45A2A1A2A2F_;Fz;").
Proof.
  intros z (f & s & Hin & Hz).
  destruct (aa_frames_fact _ A _ _ HF Hin) as (c & pos & u & v & Hc & Hs & Eb & _ & Hpos & Hf & _).
  pose proof (fs_geom_nums G c pos HG Hc Hpos) as M. cbn zeta in M. fold G in Hf. rewrite <- Hf, <- Hs in M. destruct M as (M1 & M2 & M3 & M4 & M5 & _).
  fold G. split.
  - apply Z.le_trans with (Sh f); [apply Sh_mono; exact M1 | lia].
  - apply Z.le_lt_trans with (Sh (f + s - 1)); [lia|]. unfold Sh.
    assert ((f + s - 1) / 8 < (ag_fsb G + FS_total) / 8); [|lia].
    rewrite FS_total_val in *. apply Z.div_lt_upper_bound; [lia|].
    pose proof (Z.div_mod (ag_fsb G + 11571200) 8 ltac:(lia)) as DM.
    assert (E0 : (ag_fsb G + 11571200) mod 8 = 0).
    { pose proof (geom_nums G HG) as (_ & _ & F0 & _). unfold PG in F0. apply Z.mod_divide in F0; [|lia]. destruct F0 as [q Eq]. rewrite Eq.
      replace (q * 4096 + 11571200) with ((q * 512 + 1446400) * 8) by lia. apply Z_mod_mult. }
    lia.
Qed.
Lemma owned_in_band : ltac2:(tb__ "0|0|
S0S38VA;R1A2ScS1S44R2A2S3R2S43A2A2F_;Fz;").
Proof.
  intros z Hz. pose proof (owned_range z Hz) as R.
  pose proof (geom_nums G HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). rewrite FS_total_val in *. rewrite FS_frames_off_val in R. unfold IMG_HI in F1.
  pose proof (Sh_in_band (ag_fsb G + 36864) ltac:(lia)) as S1.
  assert (SU : Sh (ag_fsb G + 11571200) <= SHADOW_BAND_HI).
  { unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END. pose proof (Z.div_le_upper_bound (ag_fsb G + 11571200) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.
Lemma mut_client : ltac2:(tb__ "0|0|
S0S37VCST;VA;R1A3S3bVCST;VA;R2A3F_;Fz;").
Proof. intros z H. left. exact H. Qed.
Lemma band_not_mut : ltac2:(tb__ "0|0|
S0ScS1S44R1A2S3R1S43A2A2SeS37VCST;VA;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hm. destruct (client_addr_bounds CST HCST A z _ HG HF Hsep (mut_client z Hm)) as [_ B].
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hz. lia.
Qed.
Lemma rt_not_mut : ltac2:(tb__ "0|0|
S0S75VG;R1A2SeS37VCST;VA;R2A3A1F_;Fz;").
Proof. intros z Hz Hm. exact (client_not_rt CST HCST A z _ HG HF Hsep (mut_client z Hm) Hz). Qed.

Lemma AGnb : ltac2:(tb__ "0|0|
S0SeS37VCST;VA;R1A3A1SeScS1S44R2A2S3R2S43A2A2A1SdS16S12Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof. intros z N1 N2. apply V1; [exact N1|]. intros Ho. apply N2. exact (owned_in_band z Ho). Qed.

Lemma AGband_def : ltac2:(tb__ "0|3|
S0ScS1S44R1A2S3R1S43A2A2SeSdS16S12Q8A1M0A1M1Vm;R2A1S20G0A1M2A3A1SeSdG1Vm';R3A1G2A3A1F_;F_;Fz;").
Proof.
  intros z Hz Hd. destruct (Z_le_dec 0 z) as [Z0|Z0]; [|unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in Hz; lia].
  assert (Z1 : z < 2 ^ 64) by (unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz; lia).
  assert (OFF : 0x646000 <= z < 2 ^ 64) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in Hz; lia).
  destruct (rm rho (Z_to_bv 64 z)) as [b|] eqn:E.
  -
    assert (D' : rm rho' (Z_to_bv 64 z) <> None).
    { destruct (rm rho' (Z_to_bv 64 z)) as [b'|] eqn:E'; [discriminate|]. exfalso.

      assert (NN : ~ ~ (client_owned_shadowA A z \/ ~ client_owned_shadowA A z)) by tauto.
      apply NN. intros [Ho|Hn].
      - apply (H2 (Z_to_bv 64 z)); [rewrite u64_lit by lia; exact Ho | rewrite E; discriminate | exact E'].
      - rewrite (H1 (Z_to_bv 64 z)) in E'; [rewrite E in E'; discriminate | rewrite u64_lit by lia; exact (band_not_mut z Hz) | rewrite u64_lit by lia; exact Hn]. }
    unfold m', view. rewrite view_in by lia. unfold rd_of. destruct (rm rho' (Z_to_bv 64 z)); [discriminate | exfalso; apply D'; reflexivity].
  - exfalso. apply Hd. unfold m, view. rewrite view_in by lia. unfold rd_of. rewrite E. apply image_byte_A_off. exact OFF.
Qed.

Lemma cells_footb_shape : ltac2:(tb__ "0|3|
S18S51A1M0G0S0SdS18S17S0S1cA2M1A1S74S51G1S51S15S0S1cS54R1A1S55R1A1A4Lc;M2R3A4S74S51G1G2R2A4A3SdS19S52R4R2A2S52R3R2A2A3F_;Fz;Fl2;Fl1;").
Proof.
  induction l1 as [|c1 l1 IH]; intros [|c2 l2] z E; try discriminate; [reflexivity|].
  cbn [map] in E. injection E as Ea Ew El. unfold cells_footb. cbn [existsb]. fold (cells_footb l1 z). fold (cells_footb l2 z).
  rewrite (IH l2 z El). unfold in_cellb. rewrite Ea, Ew. reflexivity.
Qed.
Lemma footb_img_G0 : ltac2:(tb__ "0|0|
S30S0SdS19S52S56S53R2A2R1A2S52S56S53S57A2R1A2A3Fz;FG1;").
Proof. intros G1 z. apply cells_footb_shape. reflexivity. Qed.
Lemma rtc_foot_rt : ltac2:(tb__ "0|0|
S0SdS19S52S5bS53VG;A2R1A2S1dA3S75VG;R2A2F_;Fz;").
Proof.
  intros z Hz. unfold rtc_cells in Hz. unfold cells_footb in Hz. rewrite existsb_app in Hz. apply orb_prop in Hz as [Hz|Hz].
  - left. split; [|rewrite <- (footb_img_G0 G); exact Hz].
    apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells_img in Hc. unfold IMG_HI. repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc.
  - right. apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells_geom, fs_log_cell, fs_needs_gc_cell in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc.
Qed.
Lemma rt_not_band : ltac2:(tb__ "0|0|
S0S75VG;R1A2SeScS1S44R2A2S3R2S43A2A2A1F_;Fz;").
Proof.
  intros z Hz Hb. pose proof (geom_nums G HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & _).
  pose proof (geom_bands G HG) as (FB & TB & CB & DB & _). rewrite FS_total_val in *.
  unfold rt_zone, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct Hz as [[Hz _]|[Hz|[Hz|[Hz|Hz]]]]; [lia | clear -Hz Hb TB; lia | clear -Hz Hb CB; lia | clear -Hz Hb DB; lia | clear -Hz Hb FB; lia].
Qed.
Lemma AGrt : ltac2:(tb__ "0|0|
S0S75VG;R1A2SdS16S12Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. apply AGnb; [exact (rt_not_mut z Hz) | exact (rt_not_band z Hz)]. Qed.
Lemma frame_rtc : rtc_inv m' G.
Proof.
  destruct HA as (_ & HR & _). fold G in HR. unfold rtc_inv in *. eapply cells_ok_frame; [|exact HR].
  intros z Hz. apply AGrt. exact (rtc_foot_rt z Hz).
Qed.

Lemma fsb_not_band : ltac2:(tb__ "0|1|
S0ScS1S2aVG;A1M0R1A2S3R1S2G0S45A2A2A2SeScS1S44R2A2S3R2S43A2A2A1F_;Fz;").
Proof.
  intros z Hz Hb. pose proof (proj1 (geom_bands G HG)) as FB. rewrite FS_total_val in *.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.
Lemma fsb_mut_cases : ltac2:(tb__ "0|3|
S0ScS1S2aVG;A1M0R1A2S3R1S2G0S45A2A2A2S37VCST;VA;R2A3S10S0S0S10S0S0ScScS1Z0M1R2A2S3R2ZbA2A2ScScS1G1R1A2S3R1S4aR2A1A2A2ScSdS19S63VA;R2R1A3S1dA3ScS1S49G0R2R1A3M2R5A2S3R5S2G2S4dR2A1A2A2A2A2A2A2Lp;A2Lc;A2F_;F_;Fz;").
Proof.
  intros z Hz Hm. pose proof (geom_nums G HG) as (F1 & F2 & _). rewrite FS_total_val in *.
  destruct Hm as [S|[L|[FR|C]]].
  - fold G in S. lia.
  - destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (_ & _ & _ & S4 & _). fold G in S4. rewrite FS_total_val in S4. lia.
  - destruct FR as (f & s & Hin & Hx). destruct (aa_frames_fact _ A _ _ HF Hin) as (c & p & u & v & Hc & -> & Eb & _ & Hp & -> & _).
    exists c, p. split; [exact Hc|]. split; [exact Hp|]. split; [eapply busyb_of_split; exact Eb | exact Hx].
  - destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
Qed.
Lemma frame_fs : ltac2:(tb__ "0|0|
S65S5aS5cVG;A1Vm';A2VA;A2").
Proof.
  pose proof HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh). fold G in Fhint, Fflags, Ffree, Fsh.
  pose proof (geom_nums G HG) as (F1 & F2 & F0 & _).
  split; [exact Flen|]. split; [exact Fcls|]. fold G. split; [|split; [|split]].
  - destruct Fhint as [Hhl Fhint]. split; [exact Hhl|]. intros c Hc. destruct (Fhint c Hc) as [Hr Hcell]. split; [exact Hr|].
    intros k Hk. specialize (Hcell k Hk). cbn [c_addr c_w c_val] in Hcell, Hk |- *. unfold fs_hint_cell in *. unfold FS_NCLASSES in Hc.
    unfold restrictv in Hcell |- *. rewrite fs_footb_true1 in Hcell |- * by lia.
    rewrite AGrt; [exact Hcell|]. unfold rt_zone. do 4 right. lia.
  - intros c pos Hc Hpos. specialize (Fflags c pos Hc Hpos).
    pose proof (fs_geom_nums G c pos HG Hc Hpos) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
    unfold restrictv in Fflags |- *. rewrite fs_footb_true2 in Fflags |- * by (rewrite FS_kFlagsOffset_val, FS_total_val; lia).
    rewrite AGnb; [exact Fflags | | apply fsb_not_band; rewrite FS_total_val; lia].
    intros Hm. destruct (fsb_mut_cases (fs_flags (ag_fsb G) c + pos) ltac:(rewrite FS_total_val; lia) Hm) as (c' & p' & Hc' & Hp' & _ & Hx).
    pose proof (fs_geom_nums G c' p' HG Hc' Hp') as M'. cbn zeta in M'. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M'. lia.
  - intros c pos Hc Hpos Hfree z Hz. specialize (Ffree c pos Hc Hpos Hfree z Hz).
    pose proof (fs_geom_nums G c pos HG Hc Hpos) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    destruct M as (M1 & M2 & _).
    unfold restrictv in Ffree |- *. rewrite fs_footb_true2 in Ffree |- * by (rewrite FS_kFlagsOffset_val, FS_total_val; lia).
    rewrite AGnb; [exact Ffree | | apply fsb_not_band; rewrite FS_total_val; lia].
    intros Hm. destruct (fsb_mut_cases z ltac:(rewrite FS_total_val; lia) Hm) as (c' & p' & Hc' & Hp' & Hb' & Hx).
    destruct (Z.eq_dec c c') as [Ec|Nc]; [destruct (Z.eq_dec pos p') as [Ep|Np]|].
    + subst c' p'. rewrite Hfree in Hb'. discriminate.
    + subst c'. destruct (fs_frames_disjoint (ag_fsb G) c pos c p' Hc Hpos Hc' Hp' ltac:(right; exact Np)); lia.
    + destruct (fs_frames_disjoint (ag_fsb G) c pos c' p' Hc Hpos Hc' Hp' ltac:(left; exact Nc)); lia.
  - intros z Hz. specialize (Fsh z Hz). unfold restrictv in Fsh |- *. rewrite fs_footb_true3 in Fsh |- * by exact Hz.
    destruct Fsh as [b Hb].
    assert (BD : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
    { rewrite FS_total_val, FS_frames_off_val in *. unfold IMG_HI in F1. pose proof (topG_range G) as TG.
      pose proof (Sh_in_band (ag_fsb G + 36864) ltac:(lia)) as S1.
      assert (SU : Sh (ag_fsb G + 11571200) <= SHADOW_BAND_HI).
      { unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END. pose proof (Z.div_le_upper_bound (ag_fsb G + 11571200) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
      lia. }
    pose proof (AGband_def z BD ltac:(rewrite Hb; discriminate)) as D. destruct (m' z) as [b'|]; [exists b'; reflexivity | exfalso; apply D; reflexivity].
Qed.

Let MK : forall z, m' z = m z -> maskv (fs_footb G) m' z = maskv (fs_footb G) m z.
Proof. intros z E. unfold maskv. rewrite E. reflexivity. Qed.

Lemma live_same_or_apart : ltac2:(tb__ "0|3|
S0S0S0S0S3dS17S0S0A2M0S15S0S0R4R3A4M1S25VA;A1M2A3S3dG0S15S0S0R3R2A4G2A3SfSdG0S15S0S0R6R5A4G1A3SfS1S2R6R5A2S4R4S46R3A1A2A2S1S2R4R3A2S4R6S46R5A1A2A2A2A2F_;F_;Fn';Fb';Fn;Fb;").
Proof.
  intros b n b' n' Hin Hin'. destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (In_nth_error _ _ Hin') as [j Hj].
  destruct (Nat.lt_trichotomy i j) as [L|[E|L]].
  - right. exact (live_pair_apart segsA A rho tp md i j b n b' n' HA L Hi Hj).
  - left. subst j. rewrite Hi in Hj. injection Hj as <- <-. reflexivity.
  - right. destruct (live_pair_apart segsA A rho tp md j i b' n' b n HA L Hj Hi); [right | left]; assumption.
Qed.

Lemma live_below : ltac2:(tb__ "0|0|
S0S0S0S3dS17S0S0A2S15S0S0R3R2A4S25VA;A1A3ScS1S4R4S46R3A1A2R2A2S3R2R4A2A2ScSeS37VCST;VA;R3A3A1SeScS1S44R3A2S3R3S43A2A2A1A2F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz. pose proof (rz_bound n) as RZ.
  destruct (Hsep b n Hin) as (S1 & S2 & S3 & S4 & _). fold G in S3, S4.
  pose proof (geom_nums G HG) as (F1 & F2 & F0 & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite FS_total_val, kSpaceSize_val in *.

  assert (BOX : (ag_spacebeg G <= z < ag_spacebeg G + 2 ^ 37)
                \/ (exists k ch, nth_error (aa_sec A) k = Some ch /\ sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch)).
  { destruct (is_primary n) eqn:EP.
    - left. pose proof (live_prim_facts segsA A rho tp md b n HA Hin EP) as F. cbn zeta in F. fold G in F. set (c := ClassID (needed n)) in *.
      destruct F as (Hn & Hc & X0 & XM & XU & XS & _). unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. pose proof (Size_pos c Hc) as SPc.
      first [clear - Hz Hn Hc X0 XU XS SPc; lia | nia].
    - right. destruct (live_sec_facts segsA A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _). pose proof (rz_sec n Hn1 EP) as R.
      exists k, ch. split; [exact Hk|]. unfold PG in *. lia. }
  split.
  - intros [S|[L|[FR|C]]].
    + fold G in S. lia.
    + destruct L as (b' & n' & Hin' & Hx). destruct (live_same_or_apart b n b' n' Hin Hin') as [E|[D|D]]; [injection E as <- <-; lia | | ]; pose proof (rz_bound n'); lia.
    + destruct FR as (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
      pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hx.
      destruct BOX as [B|(k & ch & Hk & B)].
      * pose proof (geom_seps G HG) as (_ & _ & _ & Q4 & _). rewrite FS_total_val, kSpaceSize_val in Q4. lia.
      * destruct HA as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (_ & _ & _ & DF & _). fold G in DF. rewrite FS_total_val in DF. lia.
    + destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
  - intros Hb. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hb. destruct BOX as [B|(k & ch & Hk & B)].
    + unfold HIGH_SHADOW_END in SP1. lia.
    + destruct HA as (_ & _ & _ & (_ & _ & _ & HS & _) & _). destruct HS as (HS1 & _). destruct (HS1 k ch Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
      destruct D10 as (_ & _ & _ & _ & DB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DB. lia.
Qed.

Lemma live_shadow_eq : ltac2:(tb__ "0|1|
S0S0S0S3dS17S0S0A2S15S0S0R3R2A4S25VA;A1A3ScS1Z0R2A2S1R2S7R3Z8A2A2A2SdS16S12Q8A1A1Vm';S2S41R5A1R3A2M0A1Vm;G0A1A3F_;F_;Fg;Fn;Fb;").
Proof.
  intros b n g Hin Hg.
  destruct (Hsep b n Hin) as (S1 & S2 & S3 & S4 & _). fold G in S3, S4. rewrite FS_total_val in S4.
  pose proof (geom_nums G HG) as (F1 & F2 & F0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). rewrite FS_total_val in *. unfold IMG_HI in *.
  assert (B16 : b mod 8 = 0).
  { destruct (law_blocks_A A rho tp md HA) as (_ & LB & _). destruct (LB b n Hin) as (_ & B16 & _).
    apply Z.mod_divide in B16; [|lia]. destruct B16 as [q Eq]. rewrite Eq. replace (q * 16) with (q * 2 * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod b 8 ltac:(lia)) as DMb. pose proof (Z.div_mod n 8 ltac:(lia)) as DMn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MBn.
  assert (BD : SHADOW_BAND_LO <= Sh b + g < SHADOW_BAND_HI).
  { pose proof (Sh_in_band b ltac:(lia)) as SB1. pose proof (Sh_in_band (b + n) ltac:(lia)) as SB2.
    assert (Sh b + g <= Sh (b + n)); [|lia]. unfold Sh.
    assert ((b + 8 * g) / 8 <= (b + n) / 8) by (apply Z.div_le_mono; lia).
    replace (b + 8 * g) with (g * 8 + b) in H by lia. rewrite Z.div_add_l in H by lia. lia. }
  apply V1; [exact (band_not_mut _ BD)|].
  intros (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
  pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hx.
  destruct M as (M1 & M2 & M3 & M4 & M5 & _).
  set (f := fs_frame (ag_fsb G) c p) in *. set (s := fs_frame_size c) in *.
  assert (F8 : f mod 8 = 0 /\ (f + s) mod 8 = 0).
  { apply Z.mod_divide in M3; [|lia]. apply Z.mod_divide in M4; [|lia]. destruct M3 as [q1 E1]. destruct M4 as [q2 E2]. rewrite E1, E2.
    split; [replace (q1 * 64) with (q1 * 8 * 8) by lia | replace (q1 * 64 + q2 * 64) with ((q1 + q2) * 8 * 8) by lia]; apply Z_mod_mult. }
  destruct F8 as [F8 FS8].
  pose proof (Z.div_mod f 8 ltac:(lia)) as DMf. pose proof (Z.div_mod (f + s) 8 ltac:(lia)) as DMfs.
  unfold Sh in Hx.
  assert (E1 : (f + s - 1) / 8 = (f + s) / 8 - 1).
  { replace (f + s - 1) with ((f + s) / 8 * 8 - 1) by lia. replace ((f + s) / 8 * 8 - 1) with (((f + s) / 8 - 1) * 8 + 7) by lia.
    rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }

  assert (X1 : f <= b + 8 * g) by lia. assert (X2 : b + 8 * g < f + s) by lia. lia.
Qed.

Lemma frame_live_blocks : ltac2:(tb__ "0|0|
S67S50S5cVG;A1Vm';A2VA;A2").
Proof.
  destruct HA as (_ & _ & _ & (_ & HLB & _) & _). fold G m in HLB. intros b n Hin. destruct (HLB b n Hin) as (L1 & L2 & L3 & L4 & L5 & L6).
  pose proof (rz_bound n) as RZ.
  assert (BEL : forall z, b - rz n <= z < b -> maskv (fs_footb G) m' z = maskv (fs_footb G) m z).
  { intros z Hz. apply MK. destruct (live_below b n z Hin Hz) as [N1 N2]. exact (AGnb z N1 N2). }
  split; [rewrite BEL by lia; exact L1|].
  split; [eapply cell_ok_agree; [|exact L2]; cbn [c_addr c_w]; intros k Hk; apply BEL; lia|].
  split; [eapply cell_ok_agree; [|exact L3]; cbn [c_addr c_w]; intros k Hk; apply BEL; lia|].
  split.
  { destruct L4 as [L4a L4b]. split.
    - intros g Hg. rewrite MK by (apply (live_shadow_eq b n g Hin); lia). exact (L4a g Hg).
    - intros Hn. rewrite MK by (apply (live_shadow_eq b n (n / 8) Hin); destruct (Hsep b n Hin) as (S1 & _); pose proof (Z.div_pos n 8); lia). exact (L4b Hn). }
  split.
  { destruct L5 as [E|[M1 M2]]; [left; exact E | right].
    split; (eapply cell_ok_agree; [|eassumption]; cbn [c_addr c_w]; intros k Hk; apply BEL; lia). }
  destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite BEL by lia; exact Ht | exact Hm4].
Qed.

Lemma img_not_mut : ltac2:(tb__ "0|0|
S0S3R1S42A2SeS4fVCST;R2A2A1SeS37VCST;VA;R3A3A1F_;F_;Fz;").
Proof.
  intros z Hz HC [S|[L|[FR|C]]]; [| | | exact (HC C)].
  - pose proof (topG_range G). fold G in S. unfold IMG_HI in Hz. lia.
  - destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (_ & S2 & _). lia.
  - destruct FR as (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
    pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val in M. fold G in Hx. lia.
Qed.
Lemma AGimg : ltac2:(tb__ "0|0|
S0S3R1S42A2SeS4fVCST;R2A2A1SdS16S12Q8A1A1Vm';R3A1Vm;R3A1A3F_;F_;Fz;").
Proof.
  intros z Hz HC. apply AGnb; [exact (img_not_mut z Hz HC)|]. unfold IMG_HI, SHADOW_BAND_LO, LOW_SHADOW_BEG in *. lia.
Qed.
Lemma AGinv_img : ltac2:(tb__ "0|0|
S0S70R1A1SdS16S12Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. apply AGimg; [exact (inv_img_lt z Hz) | intros C; exact (HCSTI z C Hz)]. Qed.
Lemma img_present' : ltac2:(tb__ "0|1|
S0ScS1Ze4000R1A2S3R1S42A2A2S10S12Q8A1M0G0SdS16G0A1Vm';R3A1S1eG0R1A2A3Lb;A2F_;Fz;").
Proof. intros z Hz. unfold m', view. unfold IMG_HI in Hz. rewrite view_in by lia. apply rd_of_imageA. lia. Qed.
Lemma mask_img : ltac2:(tb__ "0|0|
S58S0S3R1S42A2SdS16S12Q8A1A1S50S5cVG;A1R3R2A3R3R2A1A3F_;Fz;Fmm;").
Proof.
  intros mm z Hz. apply maskv_out. pose proof (geom_old _ HG) as (G1 & G2 & G3 & _). unfold IMG_HI in *. rewrite FS_total_val in G3.
  apply fs_footb_false_intro; rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val; unfold Sh, SHADOW_OFF; lia.
Qed.

Lemma live_box : ltac2:(tb__ "0|2|
S0S0S0S3dS17S0S0A2S15S0S0R3R2A4S25VA;A1A3ScS1S4R4S46R3A1A2R2A2S3R2S2R4R3A2A2A2SfScS1S2bVG;A1M0R3A2S3R3S2G0S5Z2Z25A2A2A2A2S10S1cS1cS10S26S26ScSdS16S26A1S3eS26S2fVA;A1R2A3S1eS26R1A2A3ScS1S31R1A1M1R5A2S3R5S2G1S32R1A1A2A2A2A2Lch;A2Lk;A2A2F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz. pose proof (rz_bound n) as RZ.
  pose proof (geom_nums G HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite kSpaceSize_val in *.
  destruct (is_primary n) eqn:EP.
  - left. pose proof (live_prim_facts segsA A rho tp md b n HA Hin EP) as F. cbn zeta in F. fold G in F. set (c := ClassID (needed n)) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & _). unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. pose proof (Size_pos c Hc). nia.
  - right. destruct (live_sec_facts segsA A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _). pose proof (rz_sec n Hn1 EP) as R.
    exists k, ch. split; [exact Hk|]. unfold PG in *. lia.
Qed.

Lemma frame_depot : ltac2:(tb__ "0|0|
S64S50S5cVG;A1Vm';A2VA;A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & _ & HD & _) & _ & HI3 & _). fold G m in HD. unfold depot_wf in *.
  eapply depot_mem_frame; [|exact HD]. intros a Ha.
  pose proof (fs_footb_DFP A a HG HI3 Ha) as FF. fold G in FF. unfold maskv. rewrite FF.
  destruct Ha as [Hs|Hblk].
  - apply AGinv_img. unfold inv_img. do 5 right. exact Hs.
  - assert (Hbn : exists bn, In bn (dblocks (aa_depot A)) /\ fst bn <= a < fst bn + snd bn).
    { destruct Hblk as [(b & Hb & Hab)|(b & Hb & Hab)]; [exists (b, NBSZ) | exists (b, FBSZ)]; (split; [|exact Hab]); unfold dblocks; apply in_or_app;
        [left | right]; apply in_map_iff; exists b; split; [reflexivity | exact Hb | reflexivity | exact Hb]. }
    destruct Hbn as ([bb L] & Hbn & Hab). cbn [fst snd] in Hab.
    destruct HI3 as (_ & _ & _ & _ & X5 & _). destruct (X5 (bb, L) Hbn) as (DI & _ & _ & _ & SF & SSP & _ & SSEC). cbn [fst snd] in DI. fold G in DI, SF, SSP.
    unfold sepZ in SF, SSP. cbn [fst snd] in SF, SSP. rewrite FS_total_val in SF. rewrite kSpaceSize_val in SSP.
    assert (LBIG : 0xf000 < L).
    { unfold dblocks in Hbn. apply in_app_or in Hbn as [H|H]; apply in_map_iff in H as (x & E & _); injection E as _ <-; unfold NBSZ, FBSZ; lia. }
    pose proof (dyn_in_big _ _ _ DI LBIG) as BH. destruct DI as (D1 & D2 & D3 & D4 & D5).
    apply AGnb.
    + intros [S|[Lv|[FR|C]]].
      * fold G in S. lia.
      * destruct Lv as (b & n & Hin & Hx). destruct (live_box b n a Hin ltac:(pose proof (rz_bound n); lia)) as [B|(k & ch & Hk & B)]; [lia|].
        specialize (SSEC ch (nth_error_In _ _ Hk)). unfold sepZ in SSEC. cbn [fst snd] in SSEC. lia.
      * destruct FR as (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
        pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val in M. fold G in Hx. lia.
      * destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
    + unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma frame_thread : ltac2:(tb__ "0|0|
S6eS50S5cVG;A1Vm';A2VG;A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & HT & _) & _). fold G m in HT. destruct HT as [T1 T2].
  assert (AT : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> maskv (fs_footb G) m' z = maskv (fs_footb G) m z).
  { intros z Hz. apply MK. apply AGrt. unfold rt_zone. right; left. exact Hz. }
  split; [rewrite AT by lia; exact T1|]. eapply present_agree; [|exact T2]. intros z Hz. apply AT. lia.
Qed.
Lemma frame_misc : ltac2:(tb__ "0|0|
S69S50S5cVG;A1Vm';A2A1").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & HMi) & _). fold G m in HMi. destruct HMi as (M1 & M2 & M3).
  split; [|split].
  - eapply cells_ok_frame; [|exact M1]. intros z Hz. apply MK. apply AGinv_img. left. exact Hz.
  - intros z Hz. rewrite mask_img by (unfold IMG_HI; lia). apply img_present'. unfold IMG_HI. lia.
  - intros z Hz. unfold ERRNO_A in Hz. rewrite mask_img by (unfold IMG_HI; lia). apply img_present'. unfold IMG_HI. lia.
Qed.
Lemma frame_ia : ltac2:(tb__ "0|0|
S66S50S5cVG;A1Vm';A2VA;A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & HI & _) & _). fold G m in HI.
  assert (AI : forall z, (IA_BEG <= z < IA_END) \/ (0x180e88 <= z < 0x180e8c) -> maskv (fs_footb G) m' z = maskv (fs_footb G) m z).
  { intros z Hz. apply MK. apply AGinv_img. unfold inv_img. do 3 right. destruct Hz as [Hz|Hz]; [left | right; left]; exact Hz. }
  unfold ia_inv in *. destruct HI as (I1 & I2 & I3 & I4).
  split; [rewrite AI by (right; lia); exact I1|]. split; [rewrite AI by (right; lia); exact I2|]. split; [rewrite AI by (right; lia); exact I3|].
  destruct (aa_internal_inited A).
  - destruct I4 as [I4 I5]. split; [rewrite AI by (right; lia); exact I4|]. eapply filled_agree; [|exact I5]. intros z Hz. apply AI. left. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END in *. lia.
  - destruct I4 as [I4 I5]. split; [rewrite AI by (right; lia); exact I4|]. eapply filled_agree; [|exact I5]. intros z Hz. apply AI. left. exact Hz.
Qed.

Lemma frame_bandtp : bandtp_inv m' tp.
Proof.
  pose proof HA as (_ & _ & _ & _ & _ & _ & HB). fold m in HB. eapply bandtp_mono; [|exact HB]. intros z Hz. apply AGband_def. exact Hz.
Qed.

Lemma owned_preimage : ltac2:(tb__ "0|1|
S0S38VA;R1A2S10S0S0ScSdS0S41R1A1R3A3ScS1S2S2aVG;A1M0S47A2R1A2S3R1S2G0S45A2A2A2A2Lx;A2F_;Fz;").
Proof.
  intros z (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
  pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. fold G in Hx. destruct M as (M1 & M2 & M3 & M4 & M5 & _).
  set (f := fs_frame (ag_fsb G) c p) in *. set (s := fs_frame_size c) in *.
  pose proof (geom_nums G HG) as (F1 & _). unfold IMG_HI in F1. rewrite FS_frames_off_val in *.
  assert (F8 : f mod 8 = 0 /\ (f + s) mod 8 = 0).
  { apply Z.mod_divide in M3; [|lia]. apply Z.mod_divide in M4; [|lia]. destruct M3 as [q1 E1]. destruct M4 as [q2 E2]. rewrite E1, E2.
    split; [replace (q1 * 64) with (q1 * 8 * 8) by lia | replace (q1 * 64 + q2 * 64) with ((q1 + q2) * 8 * 8) by lia]; apply Z_mod_mult. }
  destruct F8 as [F8 FS8]. pose proof (Z.div_mod f 8 ltac:(lia)) as DMf. pose proof (Z.div_mod (f + s) 8 ltac:(lia)) as DMfs.
  assert (E1 : (f + s - 1) / 8 = (f + s) / 8 - 1).
  { replace (f + s - 1) with (((f + s) / 8 - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  unfold Sh in Hx. exists (8 * (z - SHADOW_OFF)). split.
  - unfold Sh. replace (8 * (z - SHADOW_OFF)) with ((z - SHADOW_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia.
  - lia.
Qed.

Lemma not_owned_by_preimage : ltac2:(tb__ "0|2|
S0S0SdS0S41R2A1R1A3SfS1S2R3Z8M0A2S2aVG;A1M1A2S1S2S2G1S45A2G0A2R3A2A2SeS38VA;R3A2A1F_;F_;Fz;Fx;").
Proof.
  intros x z Ex Hx Ho. destruct (owned_preimage z Ho) as (y & Ey & Hy). rewrite <- Ey in Ex. unfold Sh in Ex.
  assert (E : x / 8 = y / 8) by lia. rewrite FS_frames_off_val in Hy.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.

Lemma AGshadow : ltac2:(tb__ "0|3|
S0S0S0S1Z0M0R3A2S1R3S5Z2Z2fA2A2SdS0S6R5Z8M1A2G0A3SfS1S2R5G1A2S2aVG;A1M2A2S1S2S2G2S45A2G1A2R6A2A2ScS1S41R7A1R5A2S3R5S41R6A1A2A2SdS16S12Q8A1A1Vm';R6A1Vm;R6A1A3F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z L0 H47 L8 Hap Hz.
  assert (PRE : exists x, Sh x = z /\ lo <= x < hi).
  { exists (8 * (z - SHADOW_OFF)). unfold Sh in *. split.
    - replace (8 * (z - SHADOW_OFF)) with ((z - SHADOW_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia.
    - pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)). pose proof (Z.mod_pos_bound hi 8 ltac:(lia)). lia. }
  destruct PRE as (x & Ex & Hx).
  assert (BD : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
  { pose proof (Sh_in_band x ltac:(lia)) as SB. rewrite Ex in SB. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in *. lia. }
  apply V1; [exact (band_not_mut z BD)|]. apply (not_owned_by_preimage x z Ex). lia.
Qed.

Lemma AGshadow8 : ltac2:(tb__ "0|3|
S0S0S0S1Z0M0R3A2S1R3S5Z2Z2fA2A2SdS0S6R5Z8A2G0A3M1G1SfS1R6S2S2aVG;A1M2S47A2A2S1S2G2S45A2R7A2A2ScS1S41R8A1R6A2S3R6S41R7A1A2A2SdS16S12Q8A1A1Vm';R7A1Vm;R7A1A3F_;F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z L0 H47 L8 H8 Hap Hz.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as DL. pose proof (Z.div_mod hi 8 ltac:(lia)) as DH.
  assert (PRE : exists x, Sh x = z /\ lo <= x /\ x + 8 <= hi /\ x mod 8 = 0).
  { exists (8 * (z - SHADOW_OFF)). unfold Sh in *. split; [|split; [|split]].
    - replace (8 * (z - SHADOW_OFF)) with ((z - SHADOW_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia.
    - lia.
    - lia.
    - replace (8 * (z - SHADOW_OFF)) with ((z - SHADOW_OFF) * 8) by lia. apply Z_mod_mult. }
  destruct PRE as (x & Ex & Hx1 & Hx2 & Hx8).
  assert (BD : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
  { pose proof (Sh_in_band x ltac:(lia)) as SB. rewrite Ex in SB. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in *. lia. }
  apply V1; [exact (band_not_mut z BD)|]. intros Ho. destruct (owned_preimage z Ho) as (y & Ey & Hy). rewrite <- Ey in Ex. unfold Sh in Ex.
  assert (E : x / 8 = y / 8) by lia.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.

Lemma slot_id_not_live : ltac2:(tb__ "0|2|
S0S0S0ScS1Z1R3A2S1R3Z1eA2A2S1Z0M0R3A2SdS0S6R4S48R5A1A2G0A3S1S2R5S48R6A1A2S4bA2SeS3dS0S7R6Z10A2S68VG;VA;R7A3A3A1ScS1S2S4cS2bVG;A1R8A2R7A2M1R6A2S3R6S2G1S48R8A1A2A2A2SeS4fS25VA;A1R7A2A1F_;F_;F_;F_;F_;F_;Fz;Fo;Fc;").
Proof.
  intros c o z Hc Ho HoM HoU Hnid Hz (b & n & Hin & Hzb).
  pose proof (geom_nums G HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite kSpaceSize_val in SP2.
  pose proof (Size_pos c Hc) as SPc.
  destruct (is_primary n) eqn:EP.
  - pose proof (live_prim_facts segsA A rho tp md b n HA Hin EP) as F. cbn zeta in F. fold G in F. set (c' := ClassID (needed n)) in *.
    destruct F as (Hn & Hc' & X0 & XM & XU & XS & S16 & RZ & RZ16).
    destruct (Z.eq_dec c' c) as [Ec|Nc].
    + pose proof (live_id_in G A b n c Hin EP Ec) as Hid. rewrite Ec in *.
      set (o' := b - rz n - region_beg (ag_spacebeg G) c) in *.
      assert (NX : o <> o') by (intros E; apply Hnid; rewrite E; exact Hid).
      destruct (aligned_apart (Size c) o o' SPc HoM XM NX) as [D|D]; unfold o' in *; lia.
    + unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. pose proof (Size_pos c' Hc').
      assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; nia.
  - destruct (live_sec_facts segsA A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _).
    destruct HA as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). fold G in DS. rewrite kSpaceSize_val in DS.
    unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, PG in *. destruct DS as [DS|DS]; nia.
Qed.

Lemma space_not_mut : ltac2:(tb__ "0|1|
S0ScS1S2bVG;A1M0R1A2S3R1S2S2G0S5Z2Z25A2A2Z1000A2A2A2SeS4fS25VA;A1R2A2A1ScSeS37VCST;VA;R3A3A1SeScS1S44R3A2S3R3S43A2A2A1A2F_;F_;Fz;").
Proof.
  intros z Hz NL. pose proof (geom_nums G HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite FS_total_val, kSpaceSize_val in *.
  split.
  - intros [S|[L|[FR|C]]]; [fold G in S; lia | exact (NL L) | |].
    + destruct FR as (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
      pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val in M. fold G in Hx.
      pose proof (geom_seps G HG) as (_ & _ & _ & Q4 & _). rewrite FS_total_val, kSpaceSize_val in Q4. lia.
    + destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI, HIGH_SHADOW_END in *. lia.
  - unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.
Lemma sec_not_mut : ltac2:(tb__ "0|1|
S1cS26S0SdS16S26A1S3eS26S2fVA;A1R3A3S1eS26R2A2A3ScS1S31R3A1M0R2A2S3R2S2G0S32R3A1A2A2A2SeS4fS25VA;A1R3A2A1ScSeS37VCST;VA;R4A3A1SeScS1S44R4A2S3R4S43A2A2A1A2F_;F_;F_;Fz;Fch;Fk;").
Proof.
  intros k ch z Hk Hz NL.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & HS & _) & _ & HI3 & _). destruct HS as (HS1 & _). destruct (HS1 k ch Hk) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _ & D12 & _).
  fold G in D10, D12. pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as BH. destruct D10 as (_ & _ & _ & _ & DB).
  destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (_ & _ & _ & DF & _). fold G in DF. rewrite FS_total_val in DF.
  split.
  - intros [S|[L|[FR|C]]]; [fold G in S; lia | exact (NL L) | |].
    + destruct FR as (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
      pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val in M. fold G in Hx. lia.
    + destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
  - unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma shiftr4 : ltac2:(tb__ "0|0|
S0SdS0SbR1S4eA2S7R1Z10A2A3Fo;").
Proof. intros o. unfold kCompactPtrScale. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma q_foot_eq : ltac2:(tb__ "0|0|
S0S6bVA;R1A2SdS16S12Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Proof.
  intros z Hq.
  pose proof HA as (_ & _ & _ & (_ & _ & HPR & HS & HQ & _) & _ & HI3 & _). fold G m in HPR, HS, HQ.
  destruct HQ as (QF & _). destruct HPR as (_ & _ & _ & P4).
  pose proof (geom_nums G HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite FS_total_val, kSpaceSize_val in *.
  pose proof (geom_seps G HG) as (_ & _ & _ & Q4 & _). rewrite FS_total_val, kSpaceSize_val in Q4.
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) QF qb Hqb) as (B0 & _ & _ & _ & _ & _ & BI & (x & Ex & X0 & XM & XU)). fold G in Ex.
  destruct Hz as [Hz|Hz].
  -
    destruct (P4 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). fold G in ND.
    unfold kQuarantineBatchSize in *. change (Size 24) with 8192 in *.
    assert (NL : ~ in_rangesZ (aa_live A) z).
    { apply (slot_id_not_live 24 (16 * x) z ltac:(lia) ltac:(lia)).
      - change (Size 24) with 8192. apply Z.mod_divide in XM; [|lia]. destruct XM as [q Eq]. rewrite Eq. replace (16 * (q * 512)) with (q * 8192) by lia. apply Z_mod_mult.
      - change (Size 24) with 8192. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. lia.
      - replace (16 * x / 16) with x by (rewrite Z.mul_comm, Z.div_mul; lia).
        intros Hid. apply list_relations.list.NoDup_app in ND as (_ & _ & ND). apply list_relations.list.NoDup_app in ND as (_ & _ & ND).
        apply list_relations.list.NoDup_app in ND as (_ & ND & _). apply (ND x (proj2 (list_elem_of_In _ _) Hid)). apply list_elem_of_In.
        unfold q_ids. apply in_or_app. right. change (24 =? 24) with true. cbv iota. apply in_map_iff. exists qb. split; [|exact Hqb].
        unfold qb_id, ptr_to_compact. fold G. rewrite shiftr4, Ex. match goal with |- ?t / 16 = x => replace t with (x * 16) by lia end. apply Z.div_mul. lia.
      - change (Size 24) with 8192. lia. }
    destruct (space_not_mut z ltac:(unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *; lia) NL) as [N1 N2']. exact (AGnb z N1 N2').
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [j Hj]. destruct (BI j it Hj) as [_ QI].
    destruct it as [u n]. cbn [fst snd] in *. unfold q_item_ok in QI. cbn [fst snd] in QI. cbn zeta in QI. fold G in QI.
    destruct QI as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & Q9 & Q10 & _). pose proof (rz_bound n) as RZ.
    assert (Hitq : In (u, n) (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists qb; split; [exact Hqb | exact Hit]).
    destruct (is_primary n) eqn:EP.
    +
      destruct (Q9 eq_refl) as (R1 & R2 & R3). set (c := ClassID (needed n)) in *.
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.primary_cls n Q2 EP) as Hc. fold c in Hc.
      destruct (P4 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). fold G in ND.
      pose proof (Size_pos c Hc) as SPc.
      assert (NS : n <= 64512) by (destruct (Z_le_dec 64513 n) as [L|L]; [rewrite (not_primary_large n L) in EP; discriminate | lia]).
      pose proof (slot_ok_all n ltac:(lia)) as SO. unfold slot_ok in SO.
      apply andb_prop in SO as [SO _]. apply andb_prop in SO as [SO _]. apply andb_prop in SO as [SO S3]. apply andb_prop in SO as [_ S2].
      apply Z.leb_le in S2. apply Z.eqb_eq in S3. unfold slot in S2, S3. fold c in S2, S3.
      assert (NDn : rz n + n <= needed n).
      { unfold needed, kChunkHeader2Size. pose proof (Z.div_mod (Z.max n 16 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 16 + 8 - 1) 8 ltac:(lia)). unfold round_up. lia. }
      unfold region_beg, kRegionSize in R1, R2, R3. set (rb := ag_spacebeg G + c * 2 ^ 32) in *. set (o := u - rz n - rb) in *.
      unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in N3.
      assert (OU : 0 <= o /\ o + Size c <= 2 ^ 32 - 2 ^ 29) by (unfold o; lia).
      assert (SLOT : forall y, rb + o <= y < rb + o + Size c -> ~ in_rangesZ (aa_live A) y).
      { intros y Hy. apply (slot_id_not_live c o y Hc (proj1 OU) R2); [unfold kUserSpaceSize, kRegionSize, kFreeArraySize; lia | | unfold region_beg, kRegionSize; fold rb; exact Hy].
        intros Hid. apply list_relations.list.NoDup_app in ND as (_ & _ & ND). apply list_relations.list.NoDup_app in ND as (_ & _ & ND).
        apply list_relations.list.NoDup_app in ND as (_ & ND & _). apply (ND (o / 16) (proj2 (list_elem_of_In _ _) Hid)). apply list_elem_of_In.
        unfold q_ids. apply in_or_app. left. apply in_map_iff. exists (u, n). split.
        - unfold it_id, it_ab, it_cls, ptr_to_compact. cbn [fst snd]. fold G. fold c. rewrite shiftr4. unfold region_beg, kRegionSize. fold rb. reflexivity.
        - apply filter_In. split; [exact Hitq|]. cbn [snd]. unfold it_cls. cbn [snd]. fold c. rewrite EP, Z.eqb_refl. reflexivity. }
      assert (UE : u = rb + o + rz n) by (unfold o; lia).
      assert (RBR : ag_spacebeg G + 2 ^ 32 <= rb /\ rb + 2 ^ 32 <= ag_spacebeg G + 2 ^ 37) by (unfold rb; lia).
      destruct Hz as [Hz|Hz].
      * destruct (space_not_mut z ltac:(lia) (SLOT z ltac:(lia))) as [N1 N2']. exact (AGnb z N1 N2').
      * unfold IMG_HI in Q1. apply (AGshadow u (u + n + 8) z); [clear -Q1; lia | clear -UE OU S2 NDn RBR SP2 TG; lia | | rewrite FS_total_val; clear -Q4 UE OU S2 NDn RBR RZ; lia |].
        --
           apply Z.mod_divide; [lia|]. rewrite UE. unfold rb.
           assert (D1 : (8 | o)) by (apply (Z.divide_trans _ 16); [exists 2; reflexivity | apply (Z.divide_trans _ (Size c)); apply Z.mod_divide; lia]).
           assert (D2 : (8 | rz n)) by (unfold rz; rewrite Z.shiftl_mul_pow2 by (unfold rz_log; repeat destruct (_ <=? _); lia); apply Z.divide_mul_l; exists 2; reflexivity).
           assert (D3 : (8 | ag_spacebeg G)) by (apply (Z.divide_trans _ (2 ^ 16)); [exists 8192; reflexivity | apply Z.mod_divide; lia]).
           apply Z.divide_add_r; [apply Z.divide_add_r; [apply Z.divide_add_r; [exact D3 | exists (c * 2 ^ 29); lia] | exact D1] | exact D2].
        -- unfold Sh in *. pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
           assert (u / 8 + (n + 7) / 8 <= (u + n + 8) / 8); [|lia]. apply Z.div_le_lower_bound; lia.
    +
      destruct (Q10 eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [k Hk].
      destruct HS as (HS1 & _). destruct (HS1 k ch Hk) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12.
      pose proof (rz_sec n Q2 EP) as RZs. pose proof (round_up_ge8 n) as R8. unfold PG in *.
      pose proof (dyn_in_big _ _ _ D10 ltac:(clear -D8 D9; lia)) as BH. unfold IMG_HI in BH.
      pose proof HI3 as (_ & _ & SEC3 & _ & _ & ND6 & _). destruct (SEC3 k ch Hk) as (DS & _ & _ & DF & DJ & _). fold G in DS, DF. rewrite FS_total_val in DF. rewrite kSpaceSize_val in DS.
      assert (NLV : forall y, sc_map_beg ch <= y < sc_map_beg ch + sc_map_size ch -> ~ in_rangesZ (aa_live A) y).
      { intros y Hy (b' & n' & Hin' & Hyb).
        destruct (live_box b' n' y Hin' ltac:(pose proof (rz_bound n'); clear -Hyb H; lia)) as [B|(k' & ch' & Hk' & B)]; [clear -B Hy DS; lia|].
        destruct (Nat.eq_dec k k') as [Ek|Nk]; [|destruct (DJ k' ch' Hk' Nk) as [D|D]; clear -D B Hy; lia].
        subst k'. rewrite Hk in Hk'. injection Hk' as <-.

        destruct (is_primary n') eqn:EP'.
        - pose proof (live_prim_facts segsA A rho tp md b' n' HA Hin' EP') as F. cbn zeta in F. fold G in F. set (c' := ClassID (needed n')) in *.
          destruct F as (Hn' & Hc' & X0' & XM' & XU' & XS' & _). pose proof (Size_pos c' Hc') as SPc'.
          unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in X0', XU'.
          pose proof (rz_bound n') as RZ'. clear -Hyb Hy DS X0' XU' XS' Hc' SPc' SP1 RZ'. lia.
        - destruct (live_sec_facts segsA A rho tp md b' n' HA Hin' EP') as (k2 & ch2 & Hk2 & Eb2 & Hn2 & Hend2 & _ & _).
          assert (k2 = k).
          { destruct (Nat.eq_dec k2 k) as [E|N]; [exact E|]. exfalso. destruct (SEC3 k2 ch2 Hk2) as (_ & _ & _ & _ & DJ2 & _). destruct (DJ2 k ch Hk N) as [D|D]; unfold PG in *; clear -D Hyb Hy Eb2 Hend2 Hn2; lia. }
          subst k2. rewrite Hk in Hk2. injection Hk2 as <-.
          apply list_relations.list.NoDup_app in ND6 as (_ & ND6 & _). apply (ND6 u).
          + apply list_elem_of_In. apply in_map_iff. exists (b', n'). split; [cbn [fst]; unfold PG in *; clear -Eb2 Eu; lia|]. apply filter_In. split; [exact Hin' | cbn [snd]; rewrite EP'; reflexivity].
          + apply list_elem_of_In. apply in_map_iff. exists (u, n). split; [reflexivity|]. apply filter_In. split; [exact Hitq | cbn [snd]; rewrite EP; reflexivity]. }
      destruct Hz as [Hz|Hz].
      * destruct (sec_not_mut k ch z Hk ltac:(clear -Hz Eu RZs D8 D9; lia) (NLV z ltac:(clear -Hz Eu RZs D8 D9; lia))) as [N1 N2']. exact (AGnb z N1 N2').
      * apply (AGshadow u (u + n + 8) z); [clear -Eu BH; lia | clear -Eu D8 D12 Esz R8 TG; lia | | rewrite FS_total_val; clear -DF Eu D8 Esz R8; lia |].
        -- apply Z.mod_divide; [lia|]. rewrite Eu. apply Z.mod_divide in D6; [|lia]. destruct D6 as [q Eq]. rewrite Eq. exists (q * 512 + 768). lia.
        -- unfold Sh in *. pose proof (Z.div_mod u 8 ltac:(lia)) as DM1. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DM2. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MB.
           assert (LE : u / 8 + (n + 7) / 8 <= (u + n + 8) / 8) by (apply Z.div_le_lower_bound; clear -DM1 DM2 MB; lia). clear -Hz LE. lia.
Qed.

Lemma live_in_user : ltac2:(tb__ "0|2|
S0S4fS25VA;A1R1A2ScS1S2bVG;A1M0R2A2S3R2S2S2G0S5Z2Z25A2A2Z1000A2A2A2S10S0S0ScScS1Z1R1A2S1R1Z1eA2A2ScS1S4cG0R1A2M1R4A2S3R4S2G1S4bA2A2A2A2Lc';A2F_;F_;Fz;").
Proof.
  intros z (b & n & Hin & Hzb) Hz.
  destruct (is_primary n) eqn:EP.
  - pose proof (live_prim_facts segsA A rho tp md b n HA Hin EP) as F. cbn zeta in F. fold G in F. set (c := ClassID (needed n)) in *.
    destruct F as (Hn & Hc & X0 & XM & XU & XS & _ & RZ & _). exists c. split; [exact Hc|]. lia.
  - exfalso. destruct (live_sec_facts segsA A rho tp md b n HA Hin EP) as (k & ch & Hk & Eb & Hn1 & Hend & _ & _).
    destruct HA as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 k ch Hk) as (DS & _). fold G in DS. rewrite kSpaceSize_val in DS.
    unfold PG in *. lia.
Qed.

Lemma frame_primary : ltac2:(tb__ "0|0|
S6aS50S5cVG;A1Vm';A2VA;A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & HPR & _) & _ & HI3 & _). fold G m in HPR. destruct HPR as (P1 & P2 & P3 & P4).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. intros c Hc. specialize (P4 c Hc). fold G in P4 |- *.
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  pose proof (geom_nums G HG) as (F1 & F2 & _ & T1 & T2 & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite FS_total_val, kSpaceSize_val in *.
  pose proof (geom_seps G HG) as (_ & _ & _ & Q4 & _). rewrite FS_total_val, kSpaceSize_val in Q4.
  pose proof P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & N6 & _ & _ & _ & PU & _).
  unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in N3, N6.
  apply (class_repr_agree_gen (maskv (fs_footb G) m) (maskv (fs_footb G) m') G A A c cs Hc eq_refl eq_refl eq_refl (fun b n H _ _ => H)); [| | exact P4].
  - intros z Hz. apply MK. unfold cls_meta in Hz. cbn zeta in Hz. unfold region_info, free_array, region_beg, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. rewrite kSpaceSize_val in Hz.
    destruct Hz as [Hz|[Hz|[Hz|Hz]]].
    +
      assert (NL : ~ in_rangesZ (aa_live A) z).
      { intros L. destruct (live_in_user z L ltac:(lia)) as (c' & Hc' & Hx). unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hx. lia. }
      destruct (space_not_mut z ltac:(lia) NL) as [X1 X2]. exact (AGnb z X1 X2).
    +
      assert (NL : ~ in_rangesZ (aa_live A) z).
      { intros L. destruct (live_in_user z L ltac:(lia)) as (c' & Hc' & Hx). unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hx.
        assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E|[E|E]] by lia; [subst c'; lia | nia | nia]. }
      destruct (space_not_mut z ltac:(lia) NL) as [X1 X2]. exact (AGnb z X1 X2).
    +
      apply (AGshadow (ag_spacebeg G + c * 2 ^ 32) (ag_spacebeg G + c * 2 ^ 32 + cs_mapped_user cs) z);
        [unfold HIGH_SHADOW_END in SP1; clear -SP1 Hc; lia | clear -N2 N3 Hc SP2 TG; lia | | rewrite FS_total_val; unfold HIGH_SHADOW_END in SP1; clear -Q4 N2 N3 Hc SP1; lia | exact Hz].
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in SP0; [|lia]. destruct SP0 as [q Eq]. rewrite Eq. exists (q * 8192 + c * 2 ^ 29). lia.
    + apply AGrt. unfold rt_zone. right; left. lia.
  -
    intros z Hz NL. destruct (PU z Hz NL) as [bb Hb]. exists bb. rewrite <- Hb. apply MK.
    unfold region_beg, kRegionSize in Hz.
    destruct (space_not_mut z ltac:(lia) NL) as [X1 X2]. exact (AGnb z X1 X2).
Qed.

Lemma frame_secondary : ltac2:(tb__ "0|0|
S6dS50S5cVG;A1Vm';A2VA;A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & HS & _) & _ & HI3 & _). fold G m in HS.
  pose proof (geom_nums G HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & SP1 & SP2 & SP0 & TG). rewrite FS_total_val, kSpaceSize_val in *. unfold HIGH_SHADOW_END in SP1.
  pose proof HS as (HS1 & _ & HS3 & _ & HS5 & _). fold G in HS5.
  pose proof HI3 as (SG3 & _ & SEC3 & _). fold G in SG3.
  apply (secondary_repr_agree_gen (maskv (fs_footb G) m) (maskv (fs_footb G) m') A A eq_refl eq_refl eq_refl); [| | | | exact HS].
  - intros i ch z Hi Hz. apply MK. destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12. unfold PG in D6, D7, D8.
    pose proof (dyn_in_big _ _ _ D10 ltac:(clear -D8 D9; lia)) as BH. unfold IMG_HI in BH.
    destruct (SEC3 i ch Hi) as (DS & _ & _ & DF & DJ & _). fold G in DS, DF. rewrite FS_total_val in DF. rewrite kSpaceSize_val in DS.
    destruct Hz as [Hz|Hz].
    +
      assert (NL : ~ in_rangesZ (aa_live A) z).
      { intros (b' & n' & Hin' & Hzb). destruct (live_box b' n' z Hin' ltac:(pose proof (rz_bound n'); clear -Hzb H; lia)) as [B|(k' & ch' & Hk' & B)]; [clear -B Hz DS D8 D9; lia|].
        destruct (Nat.eq_dec i k') as [Ek|Nk]; [|destruct (DJ k' ch' Hk' Nk) as [D|D]; clear -D B Hz D8 D9; lia].
        subst k'. rewrite Hi in Hk'. injection Hk' as <-.
        destruct (is_primary n') eqn:EP'.
        - pose proof (live_prim_facts segsA A rho tp md b' n' HA Hin' EP') as F. cbn zeta in F. fold G in F. set (c' := ClassID (needed n')) in *.
          destruct F as (Hn' & Hc' & X0' & XM' & XU' & XS' & _). pose proof (Size_pos c' Hc') as SPc'. pose proof (rz_bound n') as RZ'.
          unfold region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in X0', XU'. clear -Hzb Hz DS X0' XU' XS' Hc' SPc' SP1 RZ' D8 D9. lia.
        - destruct (live_sec_facts segsA A rho tp md b' n' HA Hin' EP') as (k2 & ch2 & Hk2 & Eb2 & Hn2 & Hend2 & _ & _). unfold PG in Eb2.
          assert (k2 = i).
          { destruct (Nat.eq_dec k2 i) as [E|N]; [exact E|]. exfalso. destruct (SEC3 k2 ch2 Hk2) as (_ & _ & _ & _ & DJ2 & _). destruct (DJ2 i ch Hi N) as [D|D]; clear -D Hzb Hz Eb2 Hend2 Hn2 D8 D9; lia. }
          subst k2. rewrite Hi in Hk2. injection Hk2 as <-. clear -Hzb Hz Eb2. lia. }
      destruct (sec_not_mut i ch z Hi ltac:(clear -Hz D8 D9; lia) NL) as [X1 X2]. exact (AGnb z X1 X2).
    + assert (A8 : sc_map_beg ch mod 8 = 0 /\ (sc_map_beg ch + sc_map_size ch) mod 8 = 0).
      { apply Z.mod_divide in D6; [|lia]. apply Z.mod_divide in D7; [|lia]. destruct D6 as [q1 E1]. destruct D7 as [q2 E2]. rewrite E1, E2.
        split; [replace (q1 * 4096) with (q1 * 512 * 8) by lia | replace (q1 * 4096 + q2 * 4096) with ((q1 * 512 + q2 * 512) * 8) by lia]; apply Z_mod_mult. }
      apply (AGshadow8 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -BH; lia | clear -D12 TG; lia | exact (proj1 A8) | exact (proj2 A8) | rewrite FS_total_val, FS_frames_off_val; clear -DF; lia | exact Hz].
  -
    intros z Hz. apply MK. destruct HS3 as [C0 C1]. unfold kPtrArrayReserve in C1.
    destruct SG3 as (_ & _ & _ & PS & PT & PF & PC & PD). rewrite kSpaceSize_val in PS. rewrite FS_total_val in PF. unfold kPtrArrayReserve in PS, PF.
    destruct HS5 as (_ & D1 & D2 & D3 & D4 & D5). unfold kPtrArrayReserve in D2, D3, D4, D5.
    fold G in Hz.
    apply AGnb.
    + intros [S|[L|[FR|C]]].
      * fold G in S. clear -S Hz C1 D3. lia.
      * destruct L as (b' & n' & Hin' & Hzb). destruct (live_box b' n' z Hin' ltac:(pose proof (rz_bound n'); clear -Hzb H; lia)) as [B|(k' & ch' & Hk' & B)]; [clear -B Hz C1 PS; lia|].
        destruct (SEC3 k' ch' Hk') as (_ & _ & DP & _). fold G in DP. unfold kPtrArrayReserve in DP. clear -DP B Hz C1. lia.
      * destruct FR as (f & s & Hinf & Hx). destruct (aa_frames_fact _ A _ _ HF Hinf) as (c & p & u & v & Hc & -> & _ & _ & Hp & -> & _).
        pose proof (fs_geom_nums G c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val in M. fold G in Hx. destruct M as (M1 & M2 & _). clear -M1 M2 Hx Hz C1 PF. lia.
      * destruct (HCST _ C) as [X _]. pose proof (dyn_in_big _ _ _ (conj D1 (conj D2 (conj D3 (conj D4 D5)))) ltac:(clear; lia)) as PBH. unfold IMG_LO, IMG_HI in *. clear -X PBH Hz. lia.
    + unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -D5 Hz C1. lia.
  - intros z Hz. apply MK. apply AGinv_img. unfold inv_img. right; left. exact Hz.
  - intros i ch Hi z Hz NL. destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D13 & _).
    destruct (D13 z Hz NL) as [bb Hb]. exists bb. rewrite <- Hb. apply MK. destruct (sec_not_mut i ch z Hi Hz NL) as [X1 X2]. exact (AGnb z X1 X2).
Qed.

Lemma frame_quarantine : ltac2:(tb__ "0|0|
S6cS50S5cVG;A1Vm';A2VA;A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & HQ & _) & _). fold G m in HQ.
  apply (quarantine_repr_agree_gen (maskv (fs_footb G) m) (maskv (fs_footb G) m') A A eq_refl eq_refl eq_refl eq_refl (fun c => eq_refl) (fun c => eq_refl) (fun c x H => H) Hsep); [| | | | exact HQ].
  - apply Forall_forall. intros qb Hqb. apply Forall_forall. intros it Hit. exact (proj1 (rz_bound (snd it))).
  - intros z Hz. apply MK. exact (q_foot_eq z Hz).
  - intros z Hz. apply MK. apply AGrt. unfold rt_zone. right; left. fold G in Hz. lia.
  - intros z Hz. apply MK. apply AGinv_img. unfold inv_img. right; right; left. exact Hz.
Qed.

Lemma frame_all : ltac2:(tb__ "0|0|
VAInv;VA;Vrho';Vtp;Vmd;A4").
Proof.
  pose proof HA as (_ & _ & _ & _ & HM & HI3 & _).
  split; [exact HG|]. split; [exact frame_rtc|]. split; [exact frame_fs|].
  split.
  { split; [exact Hsep|]. split; [exact frame_live_blocks|]. split; [exact frame_primary|]. split; [exact frame_secondary|].
    split; [exact frame_quarantine|]. split; [exact frame_depot|]. split; [exact frame_ia|]. split; [exact frame_thread | exact frame_misc]. }
  split; [exact HM|]. split; [exact HI3 | exact frame_bandtp].
Qed.

End Frame.

Theorem law_fake_frame_release_A : ltac2:(tb__ "0|c|
S27S36S36S18S12Q40M0A1A1S6fS0S0VAInv;R7R6R4R3A4S3dS17S0S0A2M1S15S0S0R3R2A4S28R8A1A3S0ScS1Z0M2R1A2S3R1S5Z2Z40A2A2A2SeScS1R6R2A2S3R2S2R6R5A2A2A2A1SeSdS0R3S39S29RcA1S15S0S0R7R6A4A2A3A1SeScS1S41R8A1M3R4A2S3R4S41S2R8R7A2A1M4A2A2A1SdS16S12Q8M5A1M6A1M7S35RcS14G0R5A2M8A2S35RdG8A2A3F_;F_;F_;F_;Fz;SdG7S35R8S14G0S39S29RaA1S15S0S0R5R4A4A2A2A2S1eG6S14G5G2A2A2A3S0ScS1R7R1A2S3R1S2R7R6A2A2A2SeSdG7S35RbS14G0R2A2M9A2S20G6A1MaA3A1F_;Fz;S0ScS1G3R1A2S3R1G4A2A2SeSdG7S35RcG9A2GaA3A1F_;Fz;S10S27S27S10S18G1A1MbGbS10GbGbScVAInv;R3ReRdRcA4ScSdGbS28R10A1S21G1R2S1aG1S15S0S0RbRaA4R1A3A3A3ScSdGbS28R3A1S21G1R2R1A3A3ScSdGbS25R3A1S25R10A1A3ScSdS0S2eR3A1S2eR10A1A3ScSdS0S2dR3A1S2dR10A1A3ScSdS0S2cR3A1S2cR10A1A3SdS30S29R3A1S29R10A1A3A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2F_;F_;F_;F_;F_;F_;Fs;Ff;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rhoE rho3 tp md f s HA Hin HOUT HFL HFR HSH.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct (aa_frames_fact _ A _ _ HF Hin) as (c & pos & u & v & Hc & Hsz & Ebusy & Hnotin & Hpos & Hf & Hnth). subst s.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as NUM. cbn zeta in NUM.
  rewrite <- Hf in NUM. destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  set (F := ag_fsb (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG. pose proof (proj1 (geom_bands _ HG)) as WB. fold F in WB.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in *. unfold IMG_HI in N8. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB.
  set (fl := fs_flags F c + pos).
  assert (Efl : frame_flag (aa_geom A) (f, fs_frame_size c) = fl).
  { unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite fs_class_of_size_ok by lia. fold F. rewrite Hf, fs_pos_frame by lia. reflexivity. }
  rewrite Efl in HOUT, HFL.
  assert (ESH : Sh (f + fs_frame_size c) = Sh f + fs_frame_size c / 8).
  { unfold Sh. apply Z.mod_divide in N3; [|lia]. apply Z.mod_divide in N4; [|lia]. destruct N3 as [q1 E1]. destruct N4 as [q2 E2]. rewrite E1, E2.
    replace (q1 * 64 + q2 * 64) with ((q1 * 8 + q2 * 8) * 8) by lia. replace (q1 * 64) with (q1 * 8 * 8) by lia. replace (q2 * 64) with (q2 * 8 * 8) by lia.
    rewrite !Z.div_mul by lia. lia. }
  rewrite ESH in HOUT, HSH.
  assert (ShF : Sh (F + 36864) <= Sh f) by (apply Sh_mono; lia).
  assert (ShE : Sh f + fs_frame_size c / 8 <= Sh (F + 11571200)) by (rewrite <- ESH; apply Sh_mono; lia).
  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).
  pose proof (fs_frame_size_pos c ltac:(lia)) as SZP.
  assert (SZ8 : 0 <= fs_frame_size c / 8) by (apply Z.div_pos; lia).

  set (A' := fs_release A c pos).
  assert (HB : nth_error (aa_fs_busy A) (Z.to_nat c) = Some (u ++ (pos, f) :: v)) by (rewrite Hnth, Ebusy; reflexivity).
  destruct (frames_of_release (aa_fs_busy A) 0 (Z.to_nat c) u pos f v HB) as (l1 & l2 & E1 & E2).
  rewrite Z.add_0_l, Z2Nat.id in E1 by lia.
  assert (EB' : aa_fs_busy A' = list_upd (aa_fs_busy A) (Z.to_nat c) (u ++ v)).
  { unfold A', fs_release. cbn [aa_fs_busy]. f_equal. change (nth (Z.to_nat c) (aa_fs_busy A) []) with (fs_busy A c).
    rewrite Ebusy. apply remove_pos_split. exact Hnotin. }

  set (v3 := view (rm rho3)). set (vE := view (rm rhoE)).
  assert (DEFV : forall z, 0 <= z < 2 ^ 64 -> rm rho3 (Z_to_bv 64 z) <> None -> exists x, v3 z = Some x).
  { intros z Hz Hd. unfold v3, view. rewrite view_in by lia. unfold rd_of. destruct (rm rho3 (Z_to_bv 64 z)) as [x|]; [exists x; reflexivity | exfalso; apply Hd; reflexivity]. }
  assert (V1 : forall z, f <= z < f + fs_frame_size c -> exists x, v3 z = Some x) by (intros z Hz; apply DEFV; [lia | exact (HFR z Hz)]).
  assert (V2 : v3 fl = Some (Z_to_bv 8 0)).
  { unfold v3, view. unfold fl, fs_flags in *. rewrite view_in by lia. unfold rd_of. rewrite HFL. reflexivity. }
  assert (V4 : forall z, Sh f <= z < Sh f + fs_frame_size c / 8 -> exists x, v3 z = Some x) by (intros z Hz; apply DEFV; [unfold Sh, SHADOW_OFF in *; lia | exact (HSH z Hz)]).
  assert (V5 : forall z, ~ (f <= z < f + fs_frame_size c \/ z = fl \/ Sh f <= z < Sh f + fs_frame_size c / 8) -> v3 z = vE z).
  { intros z Hz. unfold v3, vE, view. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. unfold rd_of. rewrite HOUT; [reflexivity | lia | tauto | tauto | tauto]. }
  destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  fold F vE in Fhint, Fflags, Ffree, Fsh. rewrite FS_frames_off_val, FS_total_val in Fsh.
  assert (Hlenc : (Z.to_nat c < length (aa_fs_busy A))%nat) by (rewrite Flen; lia).
  assert (EBc : forall c0, 0 <= c0 -> fs_busy A' c0 = if c0 =? c then u ++ v else fs_busy A c0).
  { intros c0 Hc0. apply (fs_busy_release A c pos c0 u v); auto; try lia. fold F. rewrite <- Hf. exact Ebusy. }
  assert (EBB : forall c0 p0, 0 <= c0 -> busyb A' c0 p0 = busyb A c0 p0 && negb ((c0 =? c) && (p0 =? pos))).
  { intros c0 p0 Hc0. unfold busyb. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
    - subst c0. rewrite Ebusy, !existsb_app. cbn [existsb fst andb].
      destruct (Z.eqb_spec p0 pos).
      + subst p0. rewrite Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
        rewrite (existsb_pos_false u pos Hnotin). cbn.
        apply existsb_pos_false. destruct (Fcls c Hc) as [Hnd _]. rewrite Ebusy, map_app in Hnd. cbn in Hnd.
        intros Hv. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. right. exact Hv.
      + replace (pos =? p0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb]. rewrite andb_true_r. reflexivity.
    - cbn [andb negb]. rewrite andb_true_r. reflexivity. }

  assert (HF' : fs_inv (restrictv (fs_footb (aa_geom A)) v3) A').
  { split; [|split; [|split; [|split; [|split]]]].
    - unfold A', fs_release. cbn [aa_fs_busy]. rewrite length_list_upd. exact Flen.
    - intros c0 Hc0. change (aa_geom A') with (aa_geom A). fold F. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
      + subst c0. destruct (Fcls c Hc) as [Hnd Hpf]. rewrite Ebusy in Hnd, Hpf. split.
        * rewrite map_app in *. cbn in Hnd. eapply NoDup_remove_1. exact Hnd.
        * intros pf Hpf'. apply Hpf. apply in_app_or in Hpf' as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
      + exact (Fcls c0 Hc0).
    - change (aa_geom A') with (aa_geom A). fold F. change (aa_fs_hint A') with (aa_fs_hint A).
      destruct Fhint as [Hhl Fhint]. split; [exact Hhl|]. intros c0 Hc0. destruct (Fhint c0 Hc0) as [Hhr Hhc]. split; [exact Hhr|].
      intros k Hk. cbn [c_addr c_w c_val]. specialize (Hhc k Hk). cbn [c_addr c_w c_val] in Hhc. unfold fs_hint_cell in *.
      unfold FS_NCLASSES in Hc0.
      cbn [c_addr c_w c_val] in Hk.
      unfold restrictv in Hhc |- *. rewrite fs_footb_true1 in Hhc by (fold F; lia). rewrite fs_footb_true1 by (fold F; lia).
      rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia). exact Hhc.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0. rewrite EBB by lia.
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      destruct (Z.eqb_spec c0 c); [destruct (Z.eqb_spec p0 pos)|].
      + subst c0 p0. cbn [andb negb]. rewrite andb_false_r. fold fl. exact V2.
      + cbn [andb negb]. rewrite andb_true_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
      + cbn [andb negb]. rewrite andb_true_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0 Hfree z Hz. rewrite EBB in Hfree by lia.
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      destruct (Z.eq_dec c0 c) as [Ec|Nc]; [destruct (Z.eq_dec p0 pos) as [Ep|Np]|].
      + subst c0 p0. rewrite <- Hf in Hz. apply V1. lia.
      + destruct (fs_frames_disjoint F c0 p0 c pos Hc0 Hp0 Hc Hpos ltac:(lia)) as [D|D]; rewrite <- Hf in D;
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia);
        (subst c0; replace (p0 =? pos) with false in Hfree by (symmetry; apply Z.eqb_neq; lia); rewrite Z.eqb_refl in Hfree; cbn in Hfree; rewrite andb_true_r in Hfree;
         specialize (Ffree c p0 Hc Hp0 Hfree z Hz); unfold restrictv in Ffree;
         rewrite fs_footb_true2 in Ffree by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia); exact Ffree).
      + destruct (fs_frames_disjoint F c0 p0 c pos Hc0 Hp0 Hc Hpos ltac:(lia)) as [D|D]; rewrite <- Hf in D;
        rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia);
        (replace (c0 =? c) with false in Hfree by (symmetry; apply Z.eqb_neq; lia); cbn in Hfree; rewrite andb_true_r in Hfree;
         specialize (Ffree c0 p0 Hc0 Hp0 Hfree z Hz); unfold restrictv in Ffree;
         rewrite fs_footb_true2 in Ffree by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia); exact Ffree).
    - change (aa_geom A') with (aa_geom A). fold F. rewrite FS_frames_off_val, FS_total_val. intros z Hz.
      unfold restrictv. rewrite fs_footb_true3 by (fold F; rewrite FS_frames_off_val, FS_total_val; lia).
      destruct (Z_le_dec (Sh f) z); [destruct (Z_lt_dec z (Sh f + fs_frame_size c / 8))|].
      1: apply V4; lia.
      all: rewrite V5 by (unfold Sh, SHADOW_OFF in *; lia); specialize (Fsh z Hz); unfold restrictv in Fsh;
           rewrite fs_footb_true3 in Fsh by (fold F; rewrite FS_frames_off_val, FS_total_val; lia); exact Fsh. }
  exists A', l1, l2.
  split.
  { apply (AInvA_fs_update segsA A A' rhoE rho3 tp md HA).
    - unfold A', fs_release, same_but_fs. cbn. repeat split; reflexivity.
    - intros z Hz. fold view. fold v3 vE. apply V5. intros [X|[X|X]].
      + rewrite fs_footb_true2 in Hz by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). discriminate.
      + subst z. rewrite fs_footb_true2 in Hz by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; clear -N6 N7; lia). discriminate.
      + rewrite fs_footb_true3 in Hz by (fold F; rewrite FS_frames_off_val, FS_total_val; lia). discriminate.
    - exact HF'. }
  split; [exact E1|]. split; [unfold aa_frames; rewrite EB'; exact E2|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Theorem law_frame_A : ltac2:(tb__ "0|7|
S27S36S36S18S12Q40M0A1M1A1S6fVAInv;R5R4R2R1A4G1SeS37VCST;R7S13G0R1A2M2A3A1SeS38R8S13G0R2A2A2A1SdS16S12Q8A1M3A1M4S35R7R3A2S35R8R3A2M5A3F_;F_;Fa;G1S38R8G2A2SeSdG4S35R8R2A2S20G3A1M6A3A1SeSdG4G5G6A3A1F_;F_;Fa;VAInv;R8R6R5R4A4F_;F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof. intros A rho rho' tp md HA H1 H2. exact (frame_all A rho rho' tp md HA H1 H2). Qed.

Theorem alloc_laws_A : ltac2:(tb__ "0|0|
S3aS76VAInv;VCST;A3").
Proof.
  constructor.
  - exact law_frame_A.
  - intros A rho rho' tp md HA E. unfold AInv, AInvA in *. rewrite E. exact HA.
  - exact (AInvA_mat segsA).
  - exact law_blocks_A.
  - exact law_client_app_A.
  - intros A rho tp md (_ & HR & _). unfold rtc_inv, rtc_cells in HR. apply Forall_app in HR. exact (proj1 HR).
  - exact AInvA_budget.
  - exact law_fake_frame_release_A.
Qed.

End L.

Corollary alloc_laws_A_b : ltac2:(tb__ "0|0|
S18S17S0S0A2A1S59R1A1SdS19S71R2A1S1dA3S3aS76S62S76A1R3A3F_;F_;FCST;").
Proof. intros CST H1 H2. exact (alloc_laws_A CST H1 (cst_inv_ok CST H2)). Qed.


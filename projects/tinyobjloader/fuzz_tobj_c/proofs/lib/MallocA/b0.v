(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SegQ_wf2.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.

(* [comment removed for export] *)
Module InvQ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "option"; "prod"; "app"; "bool"; "nat"; "true"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_geom"; "ageom"; "aa_cache_inited"; "aa_live"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "AInvQ"; "rest_invQ"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "maskv"; "mkACell"; "present"; "view"; "acell"; "c_addr"; "c_w"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "Sh"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "model_inv"; "QG"; "fs_footb"; "present_but"; "AInvA"; "bandtp_inv"; "batch_repr"; "class_repr"; "depot_wf"; "fs_inv"; "ia_inv"; "inv3"; "live_block_repr"; "live_sep"; "misc_inv"; "primary_repr"; "q_item_ok"; "quarantine_repr"; "secondary_repr"; "thread_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "q_ids"; "qall"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "q_pure"; "set_q"; "KQ_facts"; "QNPRE"; "batch_pure"; "cls_view"; "item_pure"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws ContractFreeNull RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition rest_invQ (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S0S44VA;A1S0S43Vm;VA;A2S0S46Vm;VA;A2S0S49Vm;VA;A2S0S0S4fVA;A1S25Vm;S27S15S38Z48A2U8S31A3A2A2S0S3fVm;VA;A2S0S41Vm;VA;A2S0S4aVm;SeVA;A1A2S45Vm;A1A2A2A2A2A2A2A2A2").

Definition AInvQ (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
S29S19S1fVrho;A1A2S24SeVA;A1SfS0S36R1A1S0S2eR2R1A2S0S40S2dS39R1A1M0R2A2VA;A2S0S22S26G0R2A2VA;A2S0S37S19VA;Vtp;Vmd;A4S0S42VA;A1S3cR2Vtp;A2A2A2A2A2A2A2TG;Tm;").

Lemma q_item_pure : ltac2:(tb__ "0|0|
S24SdS5S2S2A2S47R3R2R1A3S55R3R2A2F_;Fit;FA;Fm;").
Proof.
  intros m A it (I1 & I2 & _ & _ & _ & _ & _ & _ & I9 & I10 & _). unfold item_pure, cls_of. cbn zeta in *.
  split; [exact I1|]. split; [exact I2|]. split; [exact I9 | exact I10].
Qed.
Lemma batch_repr_pure : ltac2:(tb__ "0|0|
S24SdScS36SeR2A1A1S3dR4R3R2A3S53R4R3A2F_;F_;Fb;FA;Fm;").
Proof.
  intros m A b HG (B1 & _ & _ & B4 & _ & _ & B7 & (x & Ex & X0 & Xal & X1)).
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S2 & _).
  unfold batch_pure, cls_of. split; [rewrite Ex; unfold region_beg, kRegionSize; lia|]. split; [exact B4|].
  split; [exists x; split; [exact Ex | split; [exact X0 | split; [exact Xal | exact X1]]]|].
  apply Forall_forall. intros it Hit. destruct (In_nth_error _ _ Hit) as [i Hi]. exact (q_item_pure m A it (proj2 (B7 i it Hi))).
Qed.
Lemma quarantine_repr_pure : ltac2:(tb__ "0|0|
S24SdS36SeR1A1A1S48R3R2A2S0S4fR3A1S25R4S27S15S38Z48A2U8S31A3A2A2F_;F_;FA;Fm;").
Proof.
  intros m A HG (HB & _ & _ & _ & _ & _ & HMIN & _ & _ & HND). split; [|exact HMIN]. unfold q_pure, qall. split; [|exact HND].
  eapply Forall_impl; [|exact HB]. intros b Hb. exact (batch_repr_pure m A b HG Hb).
Qed.

Theorem AInvA_Q : ltac2:(tb__ "0|0|
SdS1eS3SaQ40A1A1S1aS3bS19R4R3R2R1A5S21R5R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  destruct HRest as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact (quarantine_repr_pure _ A HG R5)|].
  split; [exact R6|]. split; [exact R7|]. split; [exact R8 | exact R9].
Qed.

Definition rigidQ (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|4|
S0S1SaQ40M0A1M1S1dVrho;P97A2SbG0S14SeVA;A1M2A1A2A3S0S1G1S1dVrho;P98A2SbG0S12G2A1A2A3S0S1G1S1dVrho;P9bA2SbG0S13G2A1M3A2A3S1G1S1dVrho;P9cA2SbG0S15G3S2fA2A2A3A2A2A2").
Definition K0 (Kc : KcA) (A : AA) : jpredA := ltac2:(tb__ "0|0|
S1eS3SaQ40A1A1S3S1bA1S1aS0S21VA;R4R3R1A4S0VKc;R2R1A2S0S35VA;R4A2S0S34VA;R4A2S23VA;R4A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").

Lemma model_inv_mat : ltac2:(tb__ "0|0|
SdS3SaQ40A1A1S1aS1aS37S19R4R3R2A4S58S19R4R3R2A4S37S19R6R5R3A4F_;F_;Fmd';Fmd;Ftp;FA;").
Proof.
  intros A tp md md' HM (Hex & Hpaid & _). destruct Hex as (mat' & ->).
  assert (EV : m_vmmaps (with_vm_backing (m_vm_lazy md) mat' md) = m_vmmaps md) by apply m_vmmaps_with_vm_backing.
  assert (EL : m_vm_lazy (with_vm_backing (m_vm_lazy md) mat' md) = m_vm_lazy md) by apply m_vm_lazy_with_vm_backing.
  unfold model_inv, vm_geom, ledger_inv in HM |- *. rewrite EV, EL, Hpaid.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  refine (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj _ (conj L6 (conj L7 (conj L8 L9))))))))))))))).
  eapply depot_vm_mat; [exact EV | exact EL | exact L5].
Qed.

Theorem K0_stable : ltac2:(tb__ "0|0|
S32SdS33R2A1S57S19S52S20R3R2A2A3F_;FA;FKc;").
Proof.
  intros Kc A HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Htop & HRG). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [|split; [|split; [|split]]].
  - destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta. rewrite Erm.
    split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [exact (model_inv_mat A tp md md' HM Hme) | exact (conj HI3 HB)].
  - destruct Hme as ((mat' & ->) & _). rewrite <- (with_vm_backing_id md) in HK. exact (Kc_ok_mat Kc tr md _ _ _ _ HKc HK).
  - unfold tp_ok in *. rewrite <- (Hw 24%positive) by (unfold QNPRE; lia). exact Htp.
  - unfold top_high in *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (unfold QNPRE, V_DEPTH; lia). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite <- (Hw 151%positive), <- (Hw 152%positive), <- (Hw 155%positive), <- (Hw 156%positive) by (unfold QNPRE; lia).
    exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

Lemma Permutation_lfilter : forall {X} (f : X -> bool) (l l' : list X), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros X f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - apply Permutation_refl.
  - cbn [List.filter]. destruct (f x); [apply perm_skip; exact IH | exact IH].
  - cbn [List.filter]. destruct (f x), (f y); try apply Permutation_refl. apply perm_swap.
  - exact (Permutation_trans IH1 IH2).
Qed.
Lemma qitems_perm : ltac2:(tb__ "0|1|
S3ScA1M0G0S1cScR2R1A3S1cS5S2S2A2S4dR3A1S4dR2A1A3F_;Fl';Fl;").
Proof. intros l l' P. unfold qitems. apply Permutation_flat_map. exact P. Qed.
Lemma q_ids_perm : ltac2:(tb__ "0|1|
SfS3ScA1M0G0S2S1cScR3R2A3S1cS2S4bR5R4R2A3S4bR5R3R2A3A3F_;Fc;Fl';Fl;FG;").
Proof.
  intros G l l' c P. unfold q_ids. apply Permutation_app.
  - apply Permutation_map. apply Permutation_lfilter. exact (qitems_perm l l' P).
  - destruct (c =? 24); [apply Permutation_map; exact P | apply Permutation_refl].
Qed.

Lemma ND_permQ : forall {X} (l k : list X), Permutation l k -> NoDup k -> NoDup l.
Proof.
  intros X l k HP ND. apply (proj2 (NoDup_ListNoDup _)). apply (Permutation_NoDup (Permutation_sym HP)). apply (proj1 (NoDup_ListNoDup _)). exact ND.
Qed.

Lemma set_q_qall : ltac2:(tb__ "0|1|
SdS3ScA1M0G0S1G0S4cS50R3R2R1A3A1S6ScR2R1A3A3Fg;Ft;FA;").
Proof. intros. reflexivity. Qed.

Theorem K0_perm : ltac2:(tb__ "0|1|
S32SdS3ScA1M0G0S1eS3SaQ40A1A1S3S1bA1S1aS1cScS4cR7A1S6ScR6R5A3A3S20R9R8R5R4R3R2A6S20RaS50R9R8R7A3R6R5R4R3A6F_;F_;Fmd;Ftr;Ftp;Frho;Fg;Ft;FA;FKc;").
Proof.
  intros Kc A t g rho tp tr md P (HA & HK & Htp & Htop & HRG).
  split; [|exact (conj HK (conj Htp (conj Htop HRG)))].
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  change (aa_geom (set_q A t g)) with (aa_geom A).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|split; [exact HM|split; [|exact HB]]].
  - destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
    split; [exact R1|]. split; [exact R2|]. split.
    { destruct R3 as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
      intros c Hc. specialize (P4 c Hc). change (aa_cls (set_q A t g)) with (aa_cls A).
      unfold class_repr in P4 |- *. change (aa_live (set_q A t g)) with (aa_live A). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      rewrite set_q_qall.
      destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & ND & CL & CI1 & CI2 & CT & CC & CMU & CFA).
      repeat (split; [assumption|]). change (aa_geom (set_q A t g)) with (aa_geom A). change (live_ids (aa_geom A) (set_q A t g) c) with (live_ids (aa_geom A) A c).
      split; [|split; [exact CL | split; [exact CI1 | split; [exact CI2 | split; [exact CT | split; [|exact (conj CMU CFA)]]]]]].
      + eapply ND_permQ; [|exact ND]. rewrite !app_assoc. apply Permutation_app_head. apply q_ids_perm. apply Permutation_sym. exact P.
      + rewrite <- (Permutation_length (q_ids_perm (aa_geom A) _ _ c P)). exact CC. }
    split; [exact R4|]. split; [|exact (conj R6 (conj R7 (conj R8 R9)))].
    split; [|exact R5m]. destruct R5 as [QF QN]. unfold q_pure. rewrite set_q_qall. split.
    + apply Forall_forall. intros b Hb. apply (Permutation_in _ (Permutation_sym P)) in Hb.
      pose proof (proj1 (Forall_forall _ _) QF b Hb) as X. exact X.
    + eapply ND_permQ; [apply Permutation_map; apply Permutation_sym; exact P | exact QN].
  - destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbn zeta.
    change (aa_geom (set_q A t g)) with (aa_geom A). change (aa_live (set_q A t g)) with (aa_live A). change (aa_sec (set_q A t g)) with (aa_sec A).
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    split.
    { intros z Hz. apply I4. unfold q_foot in *. change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g) in Hz.
      apply Exists_exists in Hz as (b & Hb & Hz). apply Exists_exists. exists b. split; [exact (Permutation_in _ (Permutation_sym P) Hb) | exact Hz]. }
    split; [exact I5|]. split.
    { rewrite set_q_qall. eapply ND_permQ; [|exact I6]. apply Permutation_app_head. apply Permutation_map. apply Permutation_lfilter. exact (qitems_perm _ _ (Permutation_sym P)). }
    split; [|split].
    { unfold qlarge, large_live in *. rewrite set_q_qall. change (aa_live (set_q A t g)) with (aa_live A).
      rewrite <- (Permutation_length (Permutation_lfilter is_large _ _ (qitems_perm _ _ P))). exact I7. }
    { exact I8. }
    { change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      intros NE. apply I9. intros E. apply NE. unfold qall in P. rewrite E in P. exact (Permutation_nil P). }
Qed.

Section Facts.
Variables (A : AA) (m : bview).
Hypothesis HG : geom_ok (aa_geom A).
Let G := aa_geom A. Let SB := ag_spacebeg G. Let T := ag_thread G.
Let mm : bview := ltac2:(tb__ "0|0|
S26S39VG;A1Vm;A2").
Lemma MS : ltac2:(tb__ "0|0|
S2S0S16VSB;R1A2S17R1S15S15VSB;S2fA2Z1000A2A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. Qed.
Lemma MSH : ltac2:(tb__ "0|0|
S2S0S16S30VSB;A1R1A2S17R1S30S15S15VSB;S2fA2Z1000A2A1A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_space_sh; [exact HG | exact Hz]. Qed.
Lemma MT : ltac2:(tb__ "0|0|
S2S0S16VT;R1A2S17R1S15VT;Z1000A2A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_T; [exact HG | exact Hz]. Qed.
Lemma MI : ltac2:(tb__ "0|0|
S2S17R1Z646000A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold mm. apply maskv_out. apply fs_footb_img; [exact HG | exact Hz]. Qed.
Lemma cell_tr : ltac2:(tb__ "0|1|
S2aS8S56R1S2cR2A1A2S1S4SaQ8A1A1Vmm;S15S2bR3A1S18R2A1A2M0A1Vm;G0A1A3F_;Fk;S25Vmm;R2A2S25Vm;R3A2F_;F_;Fc;").
Proof. intros c H Hc. eapply cell_ok_agree; [|exact Hc]. intros k Hk. symmetry. exact (H k Hk). Qed.
Lemma pres_tr : ltac2:(tb__ "0|0|
S2S2S2S0S16R3R1A2S17R1R2A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;S28Vmm;R3R2A3S28Vm;R4R3A3F_;F_;Fhi;Flo;").
Proof. intros lo hi H Hp z Hz. rewrite <- (H z Hz). exact (Hp z Hz). Qed.
Lemma presb_tr : ltac2:(tb__ "0|0|
S2S2S3S5S2S2A2A1S2S0S16R4R1A2S17R1R3A2A2S1S4SaQ8A1A1Vmm;R2A1Vm;R2A1A3F_;Fz;S3aVmm;R4R3R2A4S3aVm;R5R4R3A4F_;F_;FL;Fhi;Flo;").
Proof. intros lo hi L H Hp z Hz Hn. rewrite <- (H z Hz). exact (Hp z Hz Hn). Qed.

Lemma class_repr_view : ltac2:(tb__ "0|0|
S2S0S16Z1R1A2S16R1Z1eA2A2S1S7S10VA;A1S9A3S3eVmm;VG;VA;R3S4eVA;R3A2A5S54Vm;VG;S11VA;A1R4S4eVA;R4A2A5F_;F_;F_;Fc;").
Proof.
  intros c Hc HCI HC. unfold class_repr in HC. cbn zeta in HC. fold SB T in HC.
  destruct HC as (C1 & C2 & C3 & C4 & _ & C6 & _ & _ & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & _ & C19 & C20 & C21 & _ & _ & CI & _).
  destruct (CI HCI) as (K1 & K2 & K3 & K4 & K5).
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). fold G SB in S1, S2. unfold HIGH_SHADOW_END in S1.
  pose proof kSpaceSize_val as KSV.
  assert (ZRI : forall z, region_info SB c <= z < region_info SB c + kRegionInfoStride -> mm z = m z).
  { intros z Hz. apply MS. unfold region_info, kRegionInfoStride in Hz. rewrite KSV in *. lia. }
  assert (ZFA : forall z, free_array SB c <= z < free_array SB c + kFreeArraySize -> mm z = m z).
  { intros z Hz. apply MS. unfold free_array, region_beg, kUserSpaceSize, kFreeArraySize in Hz. unfold kRegionSize in Hz. rewrite KSV. change (2 ^ 32) with 4294967296 in Hz. change (2 ^ 29) with 536870912 in Hz. lia. }
  assert (ZRG : forall z, region_beg SB c <= z < region_beg SB c + cs_mapped_user (cls_of A c) -> mm z = m z).
  { intros z Hz. apply MS. unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold kRegionSize in *. rewrite KSV. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. lia. }
  assert (ZSH : forall z, Sh (region_beg SB c) <= z < Sh (region_beg SB c + cs_mapped_user (cls_of A c)) -> mm z = m z).
  { intros z Hz. apply MSH. unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize in *. unfold kRegionSize in *. rewrite KSV. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *.
    unfold Sh in *. pose proof (Z.div_le_mono SB (SB + c * 4294967296) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (SB + c * 4294967296 + cs_mapped_user (cls_of A c)) (SB + 2 ^ 37 + 4096) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (ZPC : forall z, pc_entry G c <= z < pc_entry G c + 80 -> mm z = m z).
  { intros z Hz. apply MT. unfold pc_entry in Hz. fold T in Hz. lia. }
  constructor; fold SB.
  - apply cell_tr; [|exact C1]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_mutex, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C2]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_num_freed, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C3]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_mapped_free_array, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C4]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_allocated_user, kRegionInfoStride. lia.
  - apply cell_tr; [|exact C6]. cbn [c_addr c_w]. intros k Hk. apply ZRI. unfold RI_mapped_user, kRegionInfoStride. lia.
  - apply pres_tr; [exact ZRI | exact C9].
  - exact (conj C10 (conj C11 (conj C12 C13))).
  - exact (conj C14 C15).
  - intros i x Hi. apply cell_tr; [|exact (C16 i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply ZFA. pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold kFreeArraySize in *. lia.
  - apply pres_tr; [|exact C17]. intros z Hz. apply ZFA. unfold kFreeArraySize in *. lia.
  - apply presb_tr; [exact ZRG | exact C19].
  - apply pres_tr; [exact ZSH | exact C20].
  - apply cell_tr; [|exact K1]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. lia.
  - apply cell_tr; [|exact K2]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. lia.
  - apply cell_tr; [|exact K3]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. lia.
  - intros i x Hi. apply cell_tr; [|exact (K4 i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply ZPC. unfold pc_entry. fold T. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
    assert (max_count c <= 16) by (apply (max_count_le16 c); lia). lia.
  - apply pres_tr; [|exact C21]. intros z Hz. apply ZPC. exact Hz.
  - exact K5.
Qed.
End Facts.

Theorem K0_facts : ltac2:(tb__ "0|0|
S32SdS1eS3SaQ40A1A1S3S1bA1S1aS20R6R5R4R3R2R1A6S51R6R5S29S19S1fR5A1A2A3F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof.
  intros Kc A rho tp tr md (HA & HK & Htp & Htop & HRG).
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  destruct R3 as (P1 & P2 & P3 & P4). destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  set (m := view segsA (rm rho)) in *.
  constructor.
  - exact HG.
  - exact HRG.
  - exact HR.
  - apply (cell_tr A m); [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply (MI A m HG). unfold QG. lia.
  - destruct R8 as [_ R8]. apply (pres_tr A m); [|intros z Hz; apply R8; lia]. intros z Hz. apply (MT A m HG). lia.
  - exact P1.
  - intros HCI c Hc. exact (class_repr_view A m HG c Hc HCI (P4 c Hc)).
  - exact R5.
  - intros c Hc. pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). exact ND.
  - intros z Hz. exact (proj1 (I4 z Hz)).
  - exact I1.
  - exact Htop.
  - intros it Hit EP. destruct R5 as [QF _].
    unfold qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
    pose proof (proj1 (Forall_forall _ _) QF b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
    destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct R4 as [S1 _]. destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct (I3 i ch Hi) as (X1 & _). pose proof (topG_range (aa_geom A)) as TG. pose proof (rz_sec (snd it) IP2 EP) as RZ.
    assert (RU : snd it <= round_up (snd it) 8) by (unfold round_up; pose proof (Z.div_mod (snd it + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (snd it + 8 - 1) 8 ltac:(lia)); lia).
    unfold PG in *. rewrite RZ. split; [destruct X1; [left | right]; lia | lia].
Qed.
End InvQ.

(* [comment removed for export] *)
Module RebuildN.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "AA"; "aa_sec"; "qbatch"; "aa_q_global"; "aa_q_thread"; "sec_chunk"; "aa_live"; "aa_ptr_committed"; "aa_cls"; "aa_internal_inited"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "ag_thread"; "ageom"; "aa_frames"; "class_state"; "qb_items"; "aa_Kf"; "aa_Km"; "aa_V"; "ag_pab"; "depot_state"; "mkAA"; "sc_map_beg"; "sc_map_size"; "@Corelib.Init.Datatypes"; "list"; "option"; "prod"; "bool"; "Some"; "app"; "snd"; "nat"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "ERRNO_A"; "present"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "AInvA"; "QG"; "q_foot"; "quarantine_repr"; "secondary_repr"; "IA_BEG"; "IA_END"; "geom_ok"; "ia_inv"; "inv3"; "live_sep"; "misc_inv"; "primary_repr"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "rz"; "Sh"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN"; "bumpVK"; "znull"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@Stdlib.Lists.List"; "In"; "nth_error"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition znull (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
S2S0S6S8S34Z40A2Vz;A2S7Vz;Zee040A2A2S2S0S6Zee048Vz;A2S7Vz;Zee070A2A2S2S1S5Vz;Z173660A3S2S0S6S31Vz;A2S7Vz;S8S31Z4A2A2A2S2S0S6S8S1aVG;A1M0Zad0A2Vz;A2S7Vz;S8G0Zc60A2A2A2S0S6S8S34Z20A2Vz;A2S7Vz;S8S34Z30A2A2A2A2A2A2A2A2").

Definition bumpVK (A : AA) (n : Z) : AA := ltac2:(tb__ "0|0|
S24SbVA;A1S14VA;A1S16VA;A1SdVA;A1S13VA;A1S12VA;A1S10VA;A1SfVA;A1S17VA;A1S19VA;A1S18VA;A1S15VA;A1S8S21VA;A1Vn;A2S8S20VA;A1Z1A2S1fVA;A1Af").

Lemma bumpVK_same_but_budget : ltac2:(tb__ "0|3|
ScS5S0S1S1bSbS4aR2R1A2M0A1SbR2A1A3S0S1S27S1dA1S14G0A1S14R2A1A3S0S1S2aS16G0A1S16R2A1A3S0S1S27S11A1SdG0A1SdR2A1A3S0S1S5S13G0A1S13R2A1A3S0S1S27S29S5S5A2A1M1S12G0A1S12R2A1A3S0S1S27SeA1M2S10G0A1S10R2A1A3S0S1G2SfG0A1SfR2A1A3S0S1S23S17G0A1S17R2A1A3S0S1S27S5A1S19G0A1S19R2A1A3S0S1S27G1A1S18G0A1S18R2A1A3S0S1S2aS15G0A1S15R2A1A3S1G1S1cG0A1S1cR2A1A3A2A2A2A2A2A2A2A2A2A2A2A2Fn;FA;").
Proof. intros A n. repeat split; reflexivity. Qed.

Lemma secondary_repr_agreeN : ltac2:(tb__ "0|8|
S30S30ScScS1S1bSbR1A1SbR2A1A3S1S27S11A1SdR2A1SdR3A1A3S1S5S13R3A1S13R4A1A3S1S27S29S5S5A2A1S12R4A1S12R5A1A3S2eS11S5S1S28S11A1S4eS11SdR9A1R3A3S2bS11R2A2A3S2S0S6S25R3A1M0R2A2S7R2S8G0S26R3A1A2M1A2A2S0S6S46G0A1R2A2S7R2S46G1A1A2A2A2S1S28S42Q8A1A1M2RcR3A1RdR3A1A3F_;F_;Fz;Fch;Fi;S5S0S6S22SbR8A1A1M3R1A2S7R1S8G3S13R8A1A2A2A2S1G2RaR2A1RbR2A1M4A3F_;Fz;S5S2S0S6S34R1A2S7R1S8S34Z20A2A2A2S2S0S6S8S34Z30A2R1A2S7R1S8S34Z40A2M5A2A2S0S6Zee040M6R1A2S7R1Zee044A2A2A2A2S1G2G4RcR2A1A3F_;Fz;S32RaG5G6A3S32RbZee048Zee070A3S39RdRbA2M7G7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES EP EL AG1 AG2 AGI P7 P9 (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite EG, ES, EP, EL.
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply (AG1 i ch); [exact Hi | left; unfold PG in D8; lia]. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AG2; lia|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply (AG1 i ch); [exact Hi | left; exact Hz]|].
    eapply present_agree; [|exact D14]; intros z Hz; apply (AG1 i ch); [exact Hi | right; exact Hz]. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AG2; pose proof (Zle_0_nat (length (aa_sec A))); lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  assert (CI : forall cc, (SEC_INST <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 32) \/ (SEC_INST + 48 <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 64) ->
               cell_ok m cc -> cell_ok m' cc).
  { intros cc H1. apply cell_ok_agree. intros k Hk. apply AGI. lia. }
  unfold SEC_INST in *.
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I5]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [exact P7|].
  split; [eapply cell_ok_agree; [|exact I8]; cbn [c_addr c_w]; intros k Hk; apply AGI; right; right; lia|].
  exact P9.
Qed.

Lemma quarantine_repr_agreeQ : ltac2:(tb__ "0|7|
S30S30ScScS1S1bSbR1A1SbR2A1A3S1S27S11A1SdR2A1SdR3A1A3S1S27SeA1M0S10R3A1S10R4A1A3S1G0SfR4A1SfR5A1A3S1S27S1dA1S14R5A1S14R6A1A3S44SeSeS44S29S5S5A2M1G1S6Z10S45S2dS5S5R1A3A1A2Lit;S1eR1A1A3Lqb;S2cSeS10R7A1SfR7A1A3A3S5S37R9R1A2S1S28S42Q8A1A1M2RbR2A1RcR2A1M3A3F_;Fz;S5S0S6S8S1aSbRaA1A1M4Z50A2R1A2S7R1S8G4Z70A2A2A2S1G2G3RdR2A1M5A3F_;Fz;S5S0S6S36R1A2S7R1S8S36Zc0A2A2A2S1G2G5ReR2A1A3F_;Fz;S38RdRbA2M6G6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES ET EGq EC HRZ AG AGT AGI (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  assert (FQ : forall qb z, In qb (aa_q_thread A ++ aa_q_global A) ->
            (qb_addr qb <= z < qb_addr qb + kQuarantineBatchSize)
            \/ Exists (fun it : Z * Z => (fst it - rz (snd it) <= z < fst it) \/ (Sh (fst it) <= z < Sh (fst it) + (snd it + 7) / 8)) (qb_items qb) -> m' z = m z).
  { intros qb z Hqb Hz. apply AG. unfold q_foot. apply Exists_exists. exists qb. split; [exact Hqb | exact Hz]. }
  split.
  { apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (proj1 (Forall_forall _ _) HRZ qb Hqb) as RZb.
    unfold batch_repr. rewrite EG, EC. unfold kQuarantineBatchSize in *.
    split; [exact B0|]. split; [eapply cell_ok_agree; [|exact B1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [exact B3|]. split; [exact B4|].
    split; [eapply present_agree; [|exact B5]; intros z Hz; apply (FQ qb); [exact Hqb | left; lia]|].
    split.
    - intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (nth_error_In _ _ Hi) as Hin.
      unfold kQuarantineBatchCount in B3.
      split; [eapply cell_ok_agree; [|exact I1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
      pose proof (proj1 (Forall_forall _ _) RZb it Hin) as RZi. cbn in RZi.
      unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, ES, EC.
      destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
      assert (AGi : forall z, fst it - rz (snd it) <= z < fst it -> m' z = m z).
      { intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | left; exact Hz]. }
      split; [exact J1|]. split; [exact J2|].
      split; [rewrite AGi by lia; exact J3|].
      split; [eapply present_agree; [|exact J4]; intros z Hz; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J5]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J6]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply present_agree; [|exact J7]; intros z Hz; apply AGi; lia|].
      split; [apply (alloc_magic_ok_agree m m'); [exact AGi | exact RZi | exact J8]|].
      split; [exact J9|]. split; [exact J10|].
      assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
      eapply present_agree; [|exact J11]. intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | right; lia].
    - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4]. }
  assert (HB : forall b z, In b (aa_q_thread A ++ aa_q_global A) -> qb_addr b <= z < qb_addr b + 8 -> m' z = m z).
  { intros b z Hb Hz. apply (FQ b); [exact Hb | left; unfold kQuarantineBatchSize; lia]. }
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; left; exact Hb | exact Hz] | exact Q2]|].
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; right; exact Hb | exact Hz] | exact Q3]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGT; lia | exact Q4]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGI; unfold QG in *; lia | exact Q5]|].
  split; [eapply cell_ok_agree; [|exact Q6]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [eapply cell_ok_agree; [|exact Q7]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [exact Q8 | exact Q9].
Qed.

Lemma ia_inv_agreeN : ltac2:(tb__ "0|1|
S30S30ScScS1S2aS15R1A1S15R2A1A3S5S2S0S6S3aR1A2S7R1S3bA2A2S0S6Z180e88R1A2S7R1Z180e8cA2A2A2S1S28S42Q8A1A1R6R2A1R7R2A1A3F_;Fz;S3dR6R4A2M0G0F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EI AG H. unfold ia_inv in *. rewrite EI. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END in *.
  destruct H as (H1 & H2 & H3 & H4).
  split; [rewrite AG by (right; lia); exact H1|]. split; [rewrite AG by (right; lia); exact H2|]. split; [rewrite AG by (right; lia); exact H3|].
  destruct (aa_internal_inited A); destruct H4 as [H5 H6]; (split; [rewrite AG by (right; lia); exact H5|]); intros z Hz; rewrite AG by (left; lia); exact (H6 z Hz).
Qed.

Lemma misc_inv_N : ltac2:(tb__ "0|2|
S30S30S5S2S0S6Z173661M0R1A2S7R1Z173662A2A2S2S0S6Zeec4dR1A2S7R1Zeec4eA2A2S2S0S6Z183018R1A2S7R1Z18301cA2A2S2S0S6Z182f1cR1A2S7R1Z182f20A2A2S0S6Ze9b28R1A2S7R1Ze9b30A2A2A2A2A2A2S1S28S42Q8A1A1R3R2A1R4R2A1A3F_;Fz;S32R2Z173660G0A3S32R3S31S8S31Z4A2A3S40R5A1M1G1F_;F_;F_;F_;Fm';Fm;").
Proof.
  intros m m' AG P1 P2 (H1 & _ & _). split; [|split; [exact P1 | exact P2]].
  eapply cells_ok_frame; [|exact H1]. intros z Hz. apply AG. unfold cells_footb in Hz.
  apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y].
  apply Z.leb_le in X. apply Z.ltb_lt in Y. unfold rtc_extra in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in X, Y; lia.
Qed.

Lemma live_foot : ltac2:(tb__ "0|3|
S30ScS3cSbR1A1A1S3fR2A1S3eR3A1S41R5R4A2S39R6R5A2S5S5S5S4dS29S5S5A2S2fS5S5R3R2A4S12R9A1A3S2S0S6SaR4S45R3A1A2R2A2S7R2S8R4R3A2A2A2S0S6S46R4A1M0R2A2S7R2S8G0S9S8R3Z7A2Z8A2A2A2A2A2S0S6S47R3A2S0S3S0S6S1aSbRbA1A1M1R3A2S7R3S8G1Z1000A2A2A2A1S0S6Z10S45R4A1M2A2S6G2Z800A2A2A2A2F_;F_;Fz;Fn;Fb;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG Hsep HI3 HPR HSR b n z Hin Hz.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (topG_range (aa_geom A)) as ACV.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & L4 & L5 & _ & _ & L8). fold G T in L5. unfold IMG_HI in L2. fold G in L3.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in L8.
  pose proof (rz_bound n) as RZB.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (T3 & _). fold T SB in T3. rewrite kSpaceSize_val in T3.
  assert (GS : SB mod 2 ^ 16 = 0 /\ 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  destruct GS as (GS0 & GS1 & GS2).

  assert (SHB : forall y, Sh b <= y < Sh b + (n + 7) / 8 -> IMG_HI <= y /\ ~ (T <= y < T + 0x1000)).
  { intros y Hy. unfold Sh, SHADOW_OFF in Hy.
    pose proof (Z.div_le_mono (b + n + 7) (140737479966720 + 7) 8 ltac:(clear; lia) ltac:(clear -L1 L3 ACV; lia)) as D1. cbn in D1.
    pose proof (Z.div_mod b 8 ltac:(clear; lia)) as E1. pose proof (Z.mod_pos_bound b 8 ltac:(clear; lia)) as M1.
    pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)) as E2. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)) as M2.
    pose proof (Z.div_mod (b + n + 7) 8 ltac:(clear; lia)) as E3. pose proof (Z.mod_pos_bound (b + n + 7) 8 ltac:(clear; lia)) as M3.
    pose proof (Z.div_pos b 8 ltac:(clear -L2; lia) ltac:(clear; lia)) as D3.
    unfold IMG_HI. fold T in TB. clear -Hy D1 E1 M1 E2 M2 E3 M3 D3 TB L2. lia. }
  destruct Hz as [Hz|Hz]; [|destruct (SHB z Hz) as [X Y]; split; [exact X | split; [exact Y | exact RZB]]].
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  -
    assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    unfold IMG_HI. clear -Hz BLO T3 GS1 RZB. split; [lia|]. split; [lia | exact RZB].
  -
    destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (dyn_in_big _ _ _ D10 ltac:(clear -D8 D9; lia)) as D10'. unfold IMG_HI in D10'. clear D10. rename D10' into D10.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    destruct (SEC3 i ch Hi) as (_ & ST & _). fold T in ST.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    unfold IMG_HI. clear -INM ST D10 RZB. split; [lia|]. split; [lia | exact RZB].
Qed.

Lemma q_items_rz : ltac2:(tb__ "0|1|
ScS44SeSeS44S29S5S5A2M0G0S6Z10S45S2dS5S5R1A3A1A2Lit;S1eR1A1A3Lqb;S2cSeS10R1A1SfR1A1A3A3FA;").
Proof. intros A. apply Forall_forall. intros qb _. apply Forall_forall. intros it _. pose proof (rz_bound (snd it)). lia. Qed.

Lemma q_foot_high : ltac2:(tb__ "0|0|
S30ScS5S38R3R2A2S37R3R2A2S6S47R3A2F_;F_;Fz;FA;Fm;").
Proof.
  intros m A z (Q1 & _) Hq. unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold IMG_HI in B0.
  destruct Hz as [Hz|Hz]; [unfold IMG_HI; lia|].
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ I2].
  destruct I2 as (J1 & J2 & _). unfold IMG_HI in J1. pose proof (rz_bound (snd it)) as RZ.
  assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
  unfold IMG_HI, Sh, SHADOW_OFF in *. destruct Hz as [Hz|Hz]; [lia|].
  pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem null_rebuild : ltac2:(tb__ "0|2|
ScS49S49S27S42Q40A1A1S4cS5S35S43R6R5R3R2A5S6Z0R2A2S5S3S4bSbR9A1R1A2A1S1S28S42Q8A1M0A1M1S33S43S48R8A1R2A3S33S43S48R9A1R2A3A3F_;Fz;S5S4bSbRaA1R1A2S4G0G0S1G1S33S43S48RaA1R3A3S2bG0R1A2A3Lb;A2F_;Fz;S35S43S4aRaR5A2R8R7R6A5F_;F_;F_;F_;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv HA Hnv VO PRES.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.

  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & CI & DI). fold G T in TB, TI. fold G in CI, DI. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI, CI, DI.
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  assert (A' := bumpVK A nv).
  assert (ZD : forall z, znull G z \/ ~ znull G z) by (intros z; unfold znull; clear; lia).
  assert (AGZ : forall z, (z < IMG_HI -> ~ ((SEC_INST + 64 <= z < 0xee040) \/ (0xee048 <= z < 0xee070) \/ z = 0x173660 \/ (ERRNO_A <= z < ERRNO_A + 4) \/ (SEC_INST + 32 <= z < SEC_INST + 48))) ->
                          ~ (T + 2768 <= z < T + 3168) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros Hz. unfold znull in Hz. fold G T in Hz. unfold SEC_INST, ERRNO_A, IMG_HI in *. clear -H1 H2 Hz G4. lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    apply VO. intros Zz. unfold znull in Zz. fold G T in Zz. unfold SEC_INST, ERRNO_A in Zz.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc.
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y Zz TI; lia|]). destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y;
        first [ clear -X Y Zz G4 TI; lia | clear -X Y Zz G6 G13 CI; lia | clear -X Y Zz G8 G14 DI; lia | clear -X Y Zz G2 G10; lia ] |]). destruct Hc. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (bumpVK A nv)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. unfold znull in Zz. fold G T in Zz.
         assert (CS : z < 0x646000 \/ (T + 2768 <= z < T + 3168)) by (unfold SEC_INST, ERRNO_A in Zz; clear -Zz; lia).
         destruct CS as [CS|CS]; [rewrite (fs_footb_img G z HG CS) in Hz; discriminate | rewrite (fs_footb_T G z HG) in Hz; [discriminate | fold T; clear -CS; lia]]. }
    exact HF. }

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ znull G z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, (z < IMG_HI -> ~ ((SEC_INST + 64 <= z < 0xee040) \/ (0xee048 <= z < 0xee070) \/ z = 0x173660 \/ (ERRNO_A <= z < ERRNO_A + 4) \/ (SEC_INST + 32 <= z < SEC_INST + 48))) ->
                           ~ (T + 2768 <= z < T + 3168) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros Hz. unfold znull in Hz. fold G T in Hz. unfold SEC_INST, ERRNO_A, IMG_HI in *. clear -H1 H2 Hz G4. lia. }
  assert (PRm : forall z, znull G z -> exists b, m3 z = Some b).
  { intros z Hz. unfold m3. rewrite maskv_out; [exact (PRES z Hz)|].
    unfold znull in Hz. fold G T in Hz.
    assert (CS : z < 0x646000 \/ (T + 2768 <= z < T + 3168)) by (unfold SEC_INST, ERRNO_A in Hz; clear -Hz; lia).
    destruct CS as [CS|CS]; [exact (fs_footb_img G z HG CS) | apply (fs_footb_T G z HG); fold T; clear -CS; lia]. }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (HLB : live_block_repr m3 (bumpVK A nv)).
  { intros b n Hin. change (aa_live (bumpVK A nv)) with (aa_live A) in Hin.
    destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
    { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & Y & _). fold G T in Y. apply AGmI; [intros L; exfalso; clear -X L; unfold IMG_HI in *; lia | clear -Y; lia]. }
    pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
    pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
    split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [split|split].
    + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
    + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
      replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
      clear -DP. lia.
    + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
    + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  assert (HPR' : primary_repr m3 (bumpVK A nv)).
  { destruct HPR as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    intros c Hc. change (aa_geom (bumpVK A nv)) with G. change (aa_cls (bumpVK A nv)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (bumpVK A nv) c); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (P4 c Hc)].
    intros z Hz. pose proof (P4 c Hc) as PC. unfold class_repr in PC.
    destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in *.
    pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
    destruct HI3 as ((T3 & _) & _). fold G T in T3. rewrite kSpaceSize_val in T3.
    unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz. unfold region_info, free_array, region_beg, kUserSpaceSize in Hz. unfold kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize, Sh, SHADOW_OFF in Hz.
    set (SB := ag_spacebeg G) in *.
    pose proof (Z.div_le_mono (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) 140737479966720 8 ltac:(clear; lia) ltac:(clear -Hc M1 M2 M3 GS2 ACV; lia)) as D1.
    change (140737479966720 / 8) with 17592184995840 in D1.
    pose proof (Z.div_pos (SB + c * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2.
    apply AGmI; unfold IMG_HI, SEC_INST, ERRNO_A; clear -Hz Hc M1 M2 M3 M5 M6 GS1 GS2 T3 TB TI D1 D2; [intros L|]; lia. }
  assert (HSR' : secondary_repr m3 (bumpVK A nv)).
  { apply (secondary_repr_agreeN mE m3 A (bumpVK A nv)); try reflexivity.
    - intros i ch z Hi Hz. destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      unfold PG in D8. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (_ & ST & _). fold G T in ST. fold G in D12.
      pose proof (dyn_in_big _ _ _ D10 ltac:(clear -D8 D9; lia)) as D10'. unfold IMG_HI in D10'.
      destruct D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
      apply AGmI; unfold IMG_HI; [intros L; exfalso|].
      + destruct Hz as [Hz|Hz]; [clear -Hz L D10'; lia|]. unfold Sh, SHADOW_OFF in Hz. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)). clear -Hz L H. lia.
      + destruct Hz as [Hz|Hz]; [clear -Hz ST; lia|]. unfold Sh, SHADOW_OFF in Hz.
        pose proof (Z.div_le_mono (sc_map_beg ch + sc_map_size ch) 140737479966720 8 ltac:(clear; lia) ltac:(clear -D12 ACV; lia)) as D1. cbn in D1.
        pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)) as D0. clear -Hz D0 D1 TB. lia.
    - intros z Hz. destruct HSR as (_ & _ & S2 & S3 & S45 & _). unfold kPtrArrayReserve in *.
      pose proof (dyn_ok_big _ _ _ S45 ltac:(clear; lia)) as S4. unfold IMG_HI in S4. fold G in S4.
      destruct HI3 as ((_ & _ & _ & _ & PT) & _). fold G T in PT. unfold kPtrArrayReserve in PT.
      fold G in Hz. apply AGmI; unfold IMG_HI; [intros L; exfalso; clear -Hz L S4; lia | clear -Hz S2 PT; lia].
    - intros z Hz. apply AGmI; unfold SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia].
    - apply PRESX. destruct HSR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I7 & _). exact I7.
    - apply PRESX. destruct HSR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I9). exact I9.
    - exact HSR. }
  assert (HQR' : quarantine_repr m3 (bumpVK A nv)).
  { apply (quarantine_repr_agreeQ mE m3 A (bumpVK A nv)); try reflexivity.
    - exact (q_items_rz A).
    - intros z Hz. destruct HI3 as (_ & _ & _ & Q3 & _). destruct (Q3 z Hz) as [QT _]. fold G T in QT.
      pose proof (q_foot_high mE A z HQR Hz) as QH. apply AGmI; [intros L; exfalso; clear -QH L; lia | clear -QT; lia].
    - intros z Hz. fold G T in Hz. apply AGmI; unfold IMG_HI, SEC_INST, ERRNO_A; [intros L; clear -Hz L TI; lia | clear -Hz; lia].
    - intros z Hz. apply AGmI; unfold QG, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia].
    - exact HQR. }
  assert (HIA' : ia_inv m3 (bumpVK A nv)).
  { apply (ia_inv_agreeN mE m3 A (bumpVK A nv)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia]. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. rewrite AGmI; [exact X | unfold IMG_HI, SEC_INST, ERRNO_A; clear -TI; lia | clear; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz TI; lia].
    - intros z Hz. apply PRm. unfold znull. clear -Hz. lia.
    - intros z Hz. apply PRm. unfold znull. clear -Hz. lia. }

  unfold AInvA. change (aa_geom (bumpVK A nv)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. split; [exact Hsep|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split.
    {
      unfold depot_wf in HDW |- *. change (aa_depot (bumpVK A nv)) with (aa_depot A).
      eapply depot_mem_frame; [|exact HDW]. intros a Ha.
      destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold SEC_INST, ERRNO_A, IMG_HI; [clear -Hs; lia | clear -Hs TI; lia].
      - destruct (dm_nb _ _ HDW bb Hbb) as (_ & Hb1 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
        destruct (X5 (bb, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & ST & _).
        unfold sepZ in ST. cbn [fst snd] in ST. fold G T in ST. unfold NBSZ in *. unfold IMG_HI in Hb1; apply AGmI; unfold IMG_HI; [intros L; exfalso; clear -L Hb1 Hab; lia | clear -ST Hab; lia].
      - destruct (dm_fbases _ _ HDW bb Hbb) as (_ & Hb1 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
        destruct (X5 (bb, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & ST & _).
        unfold sepZ in ST. cbn [fst snd] in ST. fold G T in ST. unfold FBSZ in *. unfold IMG_HI in Hb1; apply AGmI; unfold IMG_HI; [intros L; exfalso; clear -L Hb1 Hab; lia | clear -ST Hab; lia]. }
    split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split.
  { unfold model_inv in HM |- *. change (aa_geom (bumpVK A nv)) with G in *. cbn [aa_V aa_Km aa_Kf bumpVK].
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8). unfold vm_geom in V1 |- *. cbn [aa_sec aa_geom bumpVK]. fold G.
    split; [exact V1|]. split; [|split; [exact V3 | split; [clear -V4 Hnv; lia | split; [clear -V5; lia | split; [exact V6 | split; [exact V7|]]]]]].
    2: {
         unfold ledger_inv, gap_ok, gapN_ok, gapS_ok, blocks_left in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls bumpVK] in V8 |- *.
         destruct V8 as (L1 & L2 & L3 & [L4a L4b] & L5 & L6 & L7 & L8 & L9 & L10).
         split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [split; [clear -L4a Hnv; lia | clear -L4b Hnv; lia]|].
         split; [exact L5|]. split; [clear -L6; lia|]. split; [clear -L7; unfold kPtrArrayCommit in *; lia|].
         split; [exact L8|split; [cbn [aa_sec bumpVK]; clear -L9; lia | exact L10]]. }
    rewrite (PrimCredit.prim_credit_same A (bumpVK A nv) eq_refl).
    unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpVK].
    pose proof (acost_mono (aa_V A) (aa_V A + nv) ltac:(clear -Hnv; lia)). unfold BETA1 in *. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 H V5. lia. }
  split; [exact HI3|].

  pose proof (geom_bands _ HG) as (_ & TB7 & _). fold G T in TB7.
  eapply bandtp_agree; [|exact HB]. intros z Hz. apply VO. unfold znull, SEC_INST, ERRNO_A. fold T.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -Hz TB7. lia.
Qed.
End RebuildN.


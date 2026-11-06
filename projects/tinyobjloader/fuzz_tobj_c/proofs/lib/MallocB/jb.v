(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.

(* [comment removed for export] *)
Module InvQ9.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "qb_addr"; "ageom"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qitems"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3"; "KQ_regroup"; "KQ_secband"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws ContractFreeNull RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem K0_secband : ltac2:(tb__ "0|0|
S6SdS7R1A1A1FKc;").
Proof.
  intros Kc A rho tp tr md (HA & HK & Htp & Htop & HRG) it Hit EP.
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  destruct R5 as [QF _].
  unfold qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
  pose proof (proj1 (Forall_forall _ _) QF b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
  destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
  destruct R4 as [S1 _]. destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (rz_sec (snd it) IP2 EP) as RZ.
  assert (RU : snd it <= round_up (snd it) 8) by (unfold round_up; pose proof (Z.div_mod (snd it + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (snd it + 8 - 1) 8 ltac:(lia)); lia).
  destruct D10 as (_ & _ & _ & _ & DB). unfold PG in *. rewrite RZ. clear - DB Eu Esz D8 RU IP2. destruct DB as [DB|DB]; [left | right]; lia.
Qed.

Lemma q_ids_regroup : ltac2:(tb__ "0|1|
S3SaS1A1M0G0S0S4S0S5S1S0S2R3A4S5S1S0S2R2A4A3S4SbS0S0A2S9R4A1S9R3A1A3S4S0S8R6R5R3A3S8R6R4R3A3A3F_;F_;Fc;Fl';Fl;FG;").
Proof.
  intros G l l' c P1 P2. unfold q_ids. apply Permutation_app.
  - apply Permutation_map. apply Permutation_lfilter. exact P2.
  - destruct (c =? 24); [|apply Permutation_refl].
    assert (E : forall k, map (qb_id G) k = map (fun a => ptr_to_compact (ag_spacebeg G) 24 a) (map qb_addr k)) by (intros k; rewrite map_map; reflexivity).
    rewrite !E. apply Permutation_map. exact P1.
Qed.

Theorem K0_regroup : ltac2:(tb__ "0|0|
S6ScS7R1A1A1FKc;").
Proof.
  intros Kc A t g rho tp tr md P1 P2 P3 (HA & HK & Htp & Htop & HRG).
  split; [|exact (conj HK (conj Htp (conj Htop HRG)))].
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  change (aa_geom (set_q A t g)) with (aa_geom A).
  assert (OLDB : forall b, In b (t ++ g) -> exists b0, In b0 (qall A) /\ qb_addr b0 = qb_addr b).
  { intros b Hb. assert (HA0 : In (qb_addr b) (map qb_addr (qall A))) by (apply (Permutation_in _ (Permutation_sym P1)); apply in_map; exact Hb).
    apply in_map_iff in HA0 as (b0 & EA & Hb0). exists b0. split; assumption. }
  assert (OLDI : forall b it, In b (t ++ g) -> In it (qb_items b) -> exists b1, In b1 (qall A) /\ In it (qb_items b1)).
  { intros b it Hb Hit. assert (Hit0 : In it (qitems (qall A))) by (apply (Permutation_in _ (Permutation_sym P2)); unfold qitems; apply in_flat_map; exists b; split; assumption).
    unfold qitems in Hit0. apply in_flat_map in Hit0. exact Hit0. }
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|split; [exact HM|split; [|exact HB]]].
  - destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
    split; [exact R1|]. split; [exact R2|]. split.
    { destruct R3 as (Q1 & Q2 & Q3 & Q4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
      intros c Hc. specialize (Q4 c Hc). change (aa_cls (set_q A t g)) with (aa_cls A).
      unfold class_repr in Q4 |- *. change (aa_live (set_q A t g)) with (aa_live A). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      rewrite set_q_qall.
      destruct Q4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & ND & CL & CI1 & CI2 & CT & CC & CMU & CFA).
      repeat (split; [assumption|]). change (aa_geom (set_q A t g)) with (aa_geom A). change (live_ids (aa_geom A) (set_q A t g) c) with (live_ids (aa_geom A) A c).
      split; [|split; [exact CL | split; [exact CI1 | split; [exact CI2 | split; [exact CT | split; [|exact (conj CMU CFA)]]]]]].
      + eapply ND_permQ; [|exact ND]. rewrite !app_assoc. apply Permutation_app_head. apply q_ids_regroup; apply Permutation_sym; assumption.
      + rewrite <- (Permutation_length (q_ids_regroup (aa_geom A) _ _ c P1 P2)). exact CC. }
    split; [exact R4|]. split; [|exact (conj R6 (conj R7 (conj R8 R9)))].
    split; [|exact R5m]. destruct R5 as [QF QN]. unfold q_pure. rewrite set_q_qall. split.
    + apply Forall_forall. intros b Hb. destruct (OLDB b Hb) as (b0 & Hb0 & EA).
      pose proof (proj1 (Forall_forall _ _) QF b0 Hb0) as (B1 & B2 & B3 & B4).
      unfold batch_pure. rewrite <- EA. split; [exact B1|]. split; [exact (proj1 (Forall_forall _ _) P3 b Hb)|]. split; [exact B3|].
      apply Forall_forall. intros it Hit. destruct (OLDI b it Hb Hit) as (b1 & Hb1 & Hit1).
      pose proof (proj1 (Forall_forall _ _) QF b1 Hb1) as (_ & _ & _ & HIP). exact (proj1 (Forall_forall _ _) HIP it Hit1).
    + eapply ND_permQ; [exact (Permutation_sym P1) | exact QN].
  - destruct HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbn zeta.
    change (aa_geom (set_q A t g)) with (aa_geom A). change (aa_live (set_q A t g)) with (aa_live A). change (aa_sec (set_q A t g)) with (aa_sec A).
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    split.
    { intros z Hz. apply I4. unfold q_foot in *. change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g) in Hz.
      apply Exists_exists in Hz as (b & Hb & Hz). destruct Hz as [Hz|Hz].
      - destruct (OLDB b Hb) as (b0 & Hb0 & EA). apply Exists_exists. exists b0. split; [exact Hb0|]. left. rewrite EA. exact Hz.
      - apply Exists_exists in Hz as (it & Hit & Hz). destruct (OLDI b it Hb Hit) as (b1 & Hb1 & Hit1).
        apply Exists_exists. exists b1. split; [exact Hb1|]. right. apply Exists_exists. exists it. split; [exact Hit1 | exact Hz]. }
    split; [exact I5|]. split.
    { rewrite set_q_qall. eapply ND_permQ; [|exact I6]. apply Permutation_app_head. apply Permutation_map. apply Permutation_lfilter. exact (Permutation_sym P2). }
    split; [|split].
    { unfold qlarge, large_live in *. rewrite set_q_qall. change (aa_live (set_q A t g)) with (aa_live A).
      rewrite <- (Permutation_length (Permutation_lfilter is_large _ _ P2)). exact I7. }
    { exact I8. }
    { change (aa_q_thread (set_q A t g) ++ aa_q_global (set_q A t g)) with (t ++ g). change (aa_cache_inited (set_q A t g)) with (aa_cache_inited A).
      intros NE. apply I9. intros E. apply NE. unfold qall in P1. rewrite E in P1. cbn [map] in P1. apply Permutation_nil in P1. exact (map_eq_nil _ _ P1). }
Qed.
End InvQ9.

(* [comment removed for export] *)
Module InvQ2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kUserSpaceSize"; "region_beg"; "free_array"; "kFreeArraySize"; "kSpaceSize"; "region_info"; "@Corelib.Init.Datatypes"; "option"; "None"; "Some"; "list"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "aa_live"; "ag_thread"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "cls_of"; "q_pure"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "present_but"; "QG"; "class_repr"; "geom_ok"; "primary_repr"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "present"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2"; "cls_metaV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2.QWhere"; "qw_where"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws RebuildM SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cls_metaV (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|3|
S11S18VG;A1M0Vc;A2S5SeG0Vc;A2S5S8S6S0R2Vz;A2S2Vz;S1R2Z80A2A2A2S8S6S0R1Vz;A2S2Vz;S1R1S1cVcs;A1A2A2A2S6S0S1S1S1fVG;A1Zd0A2S3Z50M1Vc;A2A2M2Vz;A2S2Vz;S1G2G1A2A2A2A2A2Tfa;Tri;").

Lemma class_repr_view_gen : ltac2:(tb__ "0|2|
S2cS2cS20S19S5S1aS6S0Z1R2A2S0R2Z1eA2A2S5S2dR6R4R3R1A4S7S12S24Q8A1A1R8R2A1R9R2A1A3F_;Fz;S25R7SdS18R6A1R4A2M0S1G0S1dR3A1A2S1eR5A1A4S2bR8SbSdS18R7A1R5A2M1A1SbS1G1S1dR4A1A2A1A3S27RaR8R7R6R5A5S27RaR9R8R7R6A5F_;F_;F_;F_;F_;Fcs;Fc;FA;FG;Fm';Fm;").
Proof.
  intros m m' G A c cs Hc AG PU' PS' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_metaV G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & CT & CC & CMU & CFA).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_metaV G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold ri in *; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; unfold fa in *; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [exact PS'|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AG; right; right; lia|].
  split; [exact ND|].
  split; [exact LV|].
  split.
  - intros Hi. destruct (CI Hi) as (K1 & K2 & K3 & K4 & K5). split; [|split; [|split; [|split; [|exact K5]]]].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K1].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K2].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K3].
    + intros i x Hi'. apply CA; [|exact (K4 i x Hi')]. cbn [c_addr c_w]. intros k Hk. right; right.
      pose proof (nth_error_Some_lt _ _ _ Hi') as L. pose proof (max_count_le16 c Hc). lia.
  - split; [|exact (conj CT (conj CC (conj CMU CFA)))].
    intros Hn. destruct (CN Hn) as [K1 K2]. split; [exact K1|]. eapply filled_agree; [|exact K2]. intros z Hz. apply AG. right; right. lia.
Qed.

Section QWhere.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S5S6S0Z1R1A2S0R1Z1eA2A2S6S0Z0S1bS22VA;R2A2A1M0A2S0G0ScA2A2F_;Fc;").
Let G := aa_geom A. Let SB := ag_spacebeg G. Let T := ag_thread G.

Definition qw_where (z : Z) : Prop := ltac2:(tb__ "0|1|
S8SaS5S5S6S6S0Z1R1A2S0R1Z1eA2A2S6S0S1VSB;S3R1S4Z2Z20A2A2A2M0Vz;A2S2Vz;S1G0ScA2A2A2A2Lc;A2S8S6S0SbVSB;A1Vz;A2S2Vz;SbS1VSB;S10A2A1A2A2S8S6S0S1VT;Z50A2Vz;A2S2Vz;S1VT;Z70A2A2A2S8S6S0S1S26Z98A2Vz;A2S2Vz;S1S26Zc0A2A2A2S6S0S1VT;Zad0A2Vz;A2S2Vz;S1VT;Zc60A2A2A2A2A2A2A2").

Lemma Sh_mono : ltac2:(tb__ "0|0|
S5S5S0R2R1A2S0SbR3A1SbR2A1A2F_;Fb;Fa;").
Proof. intros a b H. unfold Sh. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma QW_where : ltac2:(tb__ "0|0|
S5S21VA;R1A2S2eR2A1F_;Fz;").
Proof.
  intros z [HZ|[HZ|HZ]].
  - unfold qzone in HZ. apply Exists_exists in HZ as (b & Hb & HZ). destruct HZ as [HZ|HZ].
    + destruct (batch_slot A HQP HAU HG b Hb) as (y & E & Y0 & _ & Y1 & _). left. exists 24. split; [lia|]. fold G SB in E. unfold kQuarantineBatchSize in HZ. lia.
    + apply Exists_exists in HZ as (it & Hit & EP & HZ).
      assert (Hit' : In it (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; exact (conj Hb Hit)).
      pose proof (item_slot A HQP HAU HG it Hit' EP) as IS. cbv zeta in IS. fold G SB in IS.
      destruct IS as (C1 & R1 & _ & U1 & _ & _ & _ & RZ & _ & EU & UN & N1 & HS & TOP).
      destruct HZ as [HZ|HZ].
      * left. exists (it_cls it). split; [exact C1|]. lia.
      * right. left. pose proof (item_zones A HQP HAU HG it Hit' EP) as IZ. cbv zeta in IZ. destruct IZ as (_ & _ & _ & Z4 & Z5 & _).
        pose proof (Sh_mono SB (it_ab it) ltac:(lia)). pose proof (Sh_mono (it_ab it + Size (it_cls it)) (SB + kSpaceSize) ltac:(lia)). lia.
  - unfold qhdr_zone in HZ. fold G T in HZ. right. right. destruct HZ as [HZ|[HZ|HZ]]; [left; exact HZ | right; left; lia | right; left; lia].
  - unfold qstat_zone in HZ. fold G T in HZ. do 4 right. exact HZ.
Qed.
End QWhere.

Lemma QW_not_metaV : ltac2:(tb__ "0|5|
S19S28S17R1A1A1S2aS17R2A1A1S23R3A1S5S6S0Z1M0R1A2S0R1Z1eM1A2A2S6S0Z0M2S1bS22R6R2A2A1M3A2S0G3ScA2A2F_;Fc;S5S1aS6S0G0R2A2S0R2G1A2A2S6S0G2S1cR2A1M4A2S0G4SfA2A2S5S21RaR1A2S9S2dS17RbA1R6R5R2A4A1F_;Fz;F_;F_;Fcs;Fc;F_;F_;F_;F_;FA;").
Proof.
  intros A HG H3 HQP HAU c cs Hc Hfa z HQ HM.
  pose proof (QW_where A HG HQP HAU z HQ) as W. unfold qw_where in W.
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & T0 & T1 & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _). destruct H3 as (TS & _). rewrite kSpaceSize_val in TS.
  pose proof (topG_range (aa_geom A)) as TG.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (SH1 : SHADOW_BAND_LO <= Sh SB) by (pose proof (Sh_in_band SB ltac:(unfold HIGH_SHADOW_END in S1; lia)); lia).
  assert (SH2 : Sh (SB + kSpaceSize) < HIGH_SHADOW_END) by (apply Sh_lt_HSE; rewrite kSpaceSize_val; unfold HIGH_SHADOW_END in S1; lia).
  unfold cls_metaV in HM. cbn zeta in HM. fold SB T in HM.
  unfold region_info, free_array, region_beg, kUserSpaceSize, kFreeArraySize in *. unfold kRegionSize, kRegionInfoStride in *. rewrite kSpaceSize_val in *.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, IMG_LO, IMG_HI, QG in *. unfold HIGH_SHADOW_END in *.
  change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. change (2 ^ 37) with 137438953472 in *.
  destruct W as [(c' & Hc' & W)|[W|[W|[W|W]]]]; destruct HM as [HM|[HM|HM]]; try lia.
  all: destruct TS as [TS|TS]; try lia.
  all: destruct TB as [TB|TB]; try lia.
Qed.

Section ViewQ.
Variables (A : AA) (m m' : bview).
Hypothesis HOUT : ltac2:(tb__ "0|0|
S5S9S21VA;R1A2A1S7S12S24Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S5S21VA;R1A2S9S7S12S24Q8A1M0A1M1Vm;R2A1S13G0A1M2A3A1S9S7G1Vm';R3A1G2A3A1F_;F_;Fz;").
Lemma vq_some : ltac2:(tb__ "0|3|
S5SaS24Q8A1M0G0S7S12G0A1M1Vm;R2A1S14G0R1A2M2A3Lb;A2SaG0G0S7G1Vm';R3A1G2A3Lb;A2F_;Fz;").
Proof.
  intros z [b Hb]. destruct (m' z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  assert (NQ : ~ ~ QW A z) by (intros NQ; rewrite (HOUT z NQ), Hb in E; discriminate).
  apply NQ. intros HQ. apply (HIN z HQ); [rewrite Hb; discriminate | exact E].
Qed.
Lemma vq_present : ltac2:(tb__ "0|0|
S5S5S2bVm;R2R1A3S2bVm';R3R2A3F_;Fhi;Flo;").
Proof. intros lo hi H z Hz. exact (vq_some z (H z Hz)). Qed.
Lemma vq_present_but : ltac2:(tb__ "0|0|
S5S5S15S16S5S5A2A1S25Vm;R3R2R1A4S25Vm';R4R3R2A4F_;FL;Fhi;Flo;").
Proof. intros lo hi L H z Hz Hn. exact (vq_some z (H z Hz Hn)). Qed.

Lemma primary_repr_view : ltac2:(tb__ "0|1|
S28S17VA;A1M0A1S2aG0A1S23VA;A1S29Vm;VA;A2S29Vm';VA;A2F_;F_;F_;F_;").
Proof.
  intros HG H3 HQP (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  intros c Hc. pose proof (P4 c Hc) as HC.
  assert (HFA : 0 <= cs_mapped_free_array (nthZ (aa_cls A) c cs_empty) <= kFreeArraySize).
  { unfold class_repr in HC. cbn zeta in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N6 & _). lia. }
  apply (class_repr_view_gen m m' (aa_geom A) A c _ Hc); [| | | exact HC].
  - intros z Hz. apply HOUT. intros HQ. exact (QW_not_metaV A HG H3 HQP HAU c _ Hc HFA z HQ Hz).
  - unfold class_repr in HC. cbn zeta in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _). exact (vq_present_but _ _ _ PU).
  - unfold class_repr in HC. cbn zeta in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PS & _). exact (vq_present _ _ PS).
Qed.
End ViewQ.
End InvQ2.

(* [comment removed for export] *)
Module CInvEnsure.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "div"; "modulo"; "ge"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayCommit"; "kPtrArrayReserve"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "FS_total"; "IMG_LO"; "PG"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "AA"; "ag_pab"; "aa_ptr_committed"; "aa_sec"; "ageom"; "sec_chunk"; "topG"; "aa_cls"; "aa_live"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_spacebeg"; "ag_thread"; "ag_top"; "budget_bound"; "class_state"; "cs_empty"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "bool"; "option"; "false"; "true"; "Some"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "maps_subtract"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_noaccess"; "vm_limit"; "vm_maps"; "vm_reserved"; "iv_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "secondary_repr"; "AInvA"; "SEC_INST"; "inv3"; "geom_ok"; "primary_repr"; "live_sep"; "nthZ"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure"; "zens"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "cls_foot"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zens (G : ageom) (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|1|
ScSaS0S1S47Z30A2Vz;A2S2Vz;S1S47Z38A2A2A2SaS0S1S1cVG;A1S1dVA;A1A2M0Vz;A2S2Vz;S1G0SfA2A2A2A2").

Section Foot.
Let pabZ (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
SaS0S1cVG;A1M0Vz;A2S2Vz;S1G0S10A2A2A2").

Lemma pab_facts : ltac2:(tb__ "0|3|
S4fS1bS45R2R1A2S1aR2A1S1fSaS0S11S1cR1A1M0A2SaS0S1G0S10A2M1S21R1A1A2SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8S4S31S20S1eR3A1A2A1A2S1dR3A1M2A2S0G2S10A2A2SbS9S6G2SfA2Z0A3A2A2A2A2TG;F_;FA;Fm;").
Proof.
  intros m A HSR G. destruct HSR as (_ & _ & S2 & S3 & S45 & _). fold G in S45.
  pose proof (dyn_ok_big _ _ _ S45 ltac:(unfold kPtrArrayReserve; lia)) as B. destruct S45 as [_ (D1 & D2 & D3 & D4 & D5)].
  repeat split; try assumption; lia.
Qed.

Lemma sh_run_band : ltac2:(tb__ "0|2|
S9S9S9S0Z0R3A2M0G0S0S1R5R4A2Z7fffff800000A2SaS0S14R6A1M1R4A2S2R4S1G1S5S1R5Z7A2Z8A2A2A2A2SaS0S13R5A2S2R5S12A2A2F_;F_;F_;F_;Fy;Flen;Fb;").
Proof.
  intros b len y Hb Hl Htop Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono (b + len + 7) (140737479966720 + 7) 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (b + len + 7) 8 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (b + len + 7) 8 ltac:(lia)) as M3.
  lia.
Qed.
Lemma sh_run_band2 : ltac2:(tb__ "0|0|
S9S9S9S0Z0R3A2SaS0R4R3A2S0R3Z7fffff800000A2A2SaS0S14R5A1R3A2S2R3S14R4A1A2A2SaS0S13R4A2S2R4S12A2A2F_;F_;F_;Fy;Fe;Fb;").
Proof.
  intros b e y Hb He Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono e 140737479966720 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3. lia.
Qed.

Lemma live_foot_pab : ltac2:(tb__ "0|1|
S4fS1bS49S1aR1A1A1S4bR2A1S48R3A1S4aR5R4A2S45R6R5A2S9S9S9S56S30S9S9A2S32S9S9R3R2A4S23R9A1A3ScSaS0S8R4S19R3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S14R4A1M0R2A2S2R2S1G0S5S1R3Z7A2Z8A2A2A2A2A2SdVpabZ;S1aRbA1R3A2A1F_;F_;Fz;Fn;Fb;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG Hsep HI3 HPR HSR b n z Hin Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct Hz as [Hz|Hz].
  2: { pose proof (sh_run_band b n z ltac:(clear -L2; lia) ltac:(clear -L1; lia) ltac:(clear -L3 ACV; lia) Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    clear -Hz BLO PS RZB. intros X. lia.
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    destruct (SEC3 i ch Hi) as (_ & _ & SP & _). fold G in SP.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma q_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS49S1aR1A1A1S48R2A1S4aR4R3A2S45R5R4A2S4eR6R5A2S9S4dR7R1A2SdVpabZ;S1aR8A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG HI3 HPR HSR (Q1 & _) z Hq. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *. clear -Hz Ex X0 XA R1 R2 PS. intros X. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct Hz as [Hz|Hz].
  2: {
       assert (UT : u + n <= 140737479966720).
       { destruct (is_primary n) eqn:PRM.
         - assert (Hn : 1 <= n <= 64512).
           { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
           pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
           rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
           set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -V1 V3 R1 R2 GSB ACV Y1 Y3 Hn. nia.
         - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
           destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
           pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
           clear -Eu Esz D8 D11 D12 RU1 RU2 ACV J2. lia. }
       pose proof (sh_run_band u n z ltac:(clear -J1; lia) ltac:(clear -J2; lia) UT Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -Hz V1 V3 R1 R2 PS Y1 Y3 Hn RZ. intros X. nia.
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in *.
    destruct (SEC3 j ch Hj) as (_ & _ & SP & _). fold G in SP.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma cls_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS9S49S1aR2A1A1S48R3A1S4aR5R4A2S45R6R5A2SaS0Z1R5A2S0R5Z1eA2A2S9S5eS1aR8A1R7S4cS2bS22R8A1R7S2cA4R1A4SdVpabZ;S1aR9A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c HG HI3 HPR HSR Hc z Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  destruct HI3 as (SG3 & _). fold G in SG3. destruct SG3 as (_ & _ & _ & PS & PT & _). fold SB in PS. fold T in PT. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G T SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - clear -Hz Hc PS. intros X. lia.
  - clear -Hz Hc PS M5 M6. intros X. nia.
  - clear -Hz Hc PS M1 M2 M3. intros X. nia.
  - assert (BY : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
    { apply (sh_run_band2 (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); [clear -Hc GS1; nia | clear -Hc M1 M2 M3 GS2 ACV; nia | exact Hz]. }
    clear -BY P3. intros X. lia.
  - clear -Hz Hc PT. intros X. lia.
Qed.
End Foot.

Lemma iv_subtract_apartE : ltac2:(tb__ "0|4|
S2dQ40M0A1M1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M2S2eG0R5A2A2R4A2S0R3G2A2A2SbS2fS30G1G1A2M3A1S44R7R6R5R4A4S38G3S32G1G1R7R6A4S39G3A1A3A3F_;F_;F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hlh Hs Hd. unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma in_maps_subtract_apart : ltac2:(tb__ "0|4|
S2fS30S2dQ40M0A1M1G1A2M2A1G1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M3S2eG0R5A2A2R4A2S0R3G3A2A2S56G2S32G1G1R7R6A4R8A3S56G2S32G1G1R8R7A4S3cR9R6R5A3A3F_;F_;F_;F_;Fhi;Flo;Fsz;Fa;Fl;").
Proof.
  induction l as [|[a' s'] l IH]; intros a sz lo hi Hlh Hs Hd Hin; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [E|Hin].
  - left. injection E as -> ->. rewrite (iv_subtract_apartE a sz lo hi Hlh Hs Hd). left. reflexivity.
  - right. exact (IH _ _ _ _ Hlh Hs Hd Hin).
Qed.

Lemma maps_subtract_pos : ltac2:(tb__ "0|5|
S2fS30S2dQ40M0A1M1G1A2M2A1S9S9G1G1S56G2S32G1G1R2R1A4M3R5A3S2Z0S2eG0R2A2A2M4F_;Fs;Fb;G1G1S56G2G3S3cR6R5R4A3A3G4F_;Fs;Fb;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi H. induction l as [|[a sz] l IH]; [intros b s []|]. cbn [maps_subtract]. intros b s Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|exact (IH (fun b' s' Hi => H b' s' (or_intror Hi)) b s Hin)].
  pose proof (H a sz (or_introl eq_refl)) as Hsz. pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma covered_subtract_false : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57R6R3A2S35A3SbS33S57S3cR7R6R5A3R4A2S35A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C, H. reflexivity.
Qed.
Lemma covered_subtract_true : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57S3cR6R5R4A3R3A2S36A3SbS33S57R7R4A2S36A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C in H.
  destruct (covered l x); [reflexivity | discriminate H].
Qed.

Lemma secondary_repr_ensure : ltac2:(tb__ "0|1|
S4fS4fS1bS1aR1A1S1fS1dR2A1S9S9SdS5bR3R4R1A3A1ScS0S11R2A2SaS0S16R2A2S2R2S11A2A2A2SbS34S2dQ8A1A1R7R3A1R8R3A1A3F_;F_;Fz;S0S1R2SfA2S10A2S51R6S52S1S47Z30A2U8S5S1R3SfA2Z8A2A3A2S53R7S1S1cR5A1R4A2M0S1G0SfA2A3S48R7A1S45RaR8A2S45RaS5cR9A1A2F_;F_;F_;F_;F_;F_;Tc;TG;FA;Fm';Fm;").
Proof.
  intros m m' A. cbn zeta. intros AG HcR HC48 HPB HI3 HSR.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  destruct HI3 as (_ & _ & SEC3 & _).
  unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed bumpP].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as ACV.
  assert (AGI : forall z, IMG_LO <= z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m' z = m z).
  { intros z H1 H2. apply AG; [|right; exact H1]. intros [X|X]; [exact (H2 X)|]. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (ag_pab G + c <= z < ag_pab G + c + kPtrArrayCommit) -> m' z = m z).
  { intros z H1 H2. apply AG; [|left; exact H1]. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. fold G in D10, D12.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB.
    destruct (SEC3 i ch Hi) as (_ & _ & SPB & _).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGH; [clear -MB Ho; lia|]. unfold PG in D8. clear -SPB D8 D9 Ho Hw Hk P4 HcR. intros X. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGH; [clear -P1 Hk; lia | clear -L P4 Hk; intros X; lia]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply AGH; [clear -MB Hz; lia | clear -SPB Hz P4 HcR MS; intros X; lia]|].
    eapply present_agree; [|exact D14]. intros z Hz.
    pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -MB; unfold IMG_HI in MB; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
    apply AGH; [clear -BY; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; lia | clear -BY P3 P4 HcR; intros X; lia]. }
  split.
  {
    intros z Hz. destruct (Z_lt_dec z (ag_pab G + c)) as [Hlt|Hge].
    - rewrite AGH; [apply SP; lia | pose proof (Zle_0_nat (length (aa_sec A))); clear -Hz Hlt P1 H; lia | clear -Hlt; intros X; lia].
    - apply HPB. lia. }
  split; [clear -S2 HcR; unfold kPtrArrayCommit in *; lia|].
  split. { rewrite <- Z.add_mod_idemp_l by (unfold kPtrArrayCommit; lia). rewrite S3, Z.add_0_l. apply Z_mod_same_full. }
  split; [exact S45|].
  assert (CI : forall cc, (SEC_INST <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 48) \/ (SEC_INST + 56 <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= 0xead08) ->
               cell_ok m cc -> cell_ok m' cc).
  { intros cc H1. apply cell_ok_agree. intros k Hk. apply AGI; unfold SEC_INST, IMG_LO, IMG_HI in *; clear -H1 Hk; lia. }
  unfold SEC_INST in *.
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [exact HC48|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia|].
  split; [eapply cell_ok_agree; [|exact I8]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold IMG_LO, IMG_HI; clear -Hk; lia|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia.
Qed.

Theorem AInvA_ensure : ltac2:(tb__ "0|8|
S1bS54S54S2fS2dQ40A1M0A1S3dS3dS1aR6A1S1fS1dR7A1S9S1S1cR2A1R1A2S9S46S3aR9R8R6R5A5SbS9S3Z8M1S4S31S20S1eRaA1A2A1A2R3A3S0S1R4SfA2S10A2SbS2fS30G0G0A2A1M2S42S3bR7A1A1S42S3bR8A1M3A1A3SbG2S43G3A1S43S3bR9A1M4A1A3SbG2S40G4A1S3cS40S3bRaA1A1R6S1R6SfA2A3A3SbG2S3fRaA1S3cS3fRbA1R7S1R7SfA2A3A3SbS9S41S3bRbA1A1S41S3bRcA1M5A1A3SbS9S3eG5A1S3eS3bRdA1A1A3S58S40S3bReA1A1A1S58S3fRfA1A1S0S59RfR11A2S1S59R10R11A2SfA2A2S9SdS5bR10R16R1A3A1SbS34S2dQ8A1A1S50S3aS55R15A1M6R2A3S50S3aS55R16A1R2A3A3F_;Fz;S51S50S3aS55R14A1A2S52S1S47Z30A2U8S5S1RfSfA2M7G1A2A3A2S53S50S3aG6A2RfG7A3S46S3aS5cR18A1R16R15R13A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TPB;Tc;TG;Fmd';Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md md'. cbn zeta. intros HA HcN HcR EM ER EN EL ELIM ETOP WN WL HPAID VO HC48 HPB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5).
  pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3).
  pose proof SG3 as (_ & _ & _ & PS & PT & PF & PC & PD).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *. set (PB := ag_pab G + c) in *. set (T := ag_thread G) in *.
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & CI & DI). fold T in TB, TI. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI, CI, DI.
  assert (ZD : forall z, zens G A z \/ ~ zens G A z) by (intros z; unfold zens; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply AGH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGZ : forall z, ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H1 X)|]. apply H2. unfold PB in X. clear -X P4 HcR. lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (cc & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply AGZ; unfold SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y;
        first [ clear -X Y TI PT; lia | clear -X Y CI PC; lia | clear -X Y DI PD; lia | clear -X Y G2 PF; lia ] |]); destruct Hc. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (bumpP A)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. unfold zens in Zz. fold G c in Zz.
         destruct Zz as [Zz|Zz].
         - rewrite (fs_footb_img G z HG) in Hz; [discriminate|]. unfold SEC_INST in Zz. clear -Zz. lia.
         - rewrite (fs_footb_false_intro G z) in Hz; [discriminate| | |].
           + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
             rewrite FS_frames_off_val, FS_total_val in *.
             destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
             destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
             specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
             clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    exact HF. }

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ zens G A z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGmP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> m3 z = mE z).
  { intros z H1 H2. apply AGmH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGmT : forall z, T <= z < T + 0x1000 -> m3 z = mE z).
  { intros z Hz. destruct (Z_lt_dec z IMG_HI) as [L|L].
    - apply AGmI; [exact L|]. unfold IMG_HI, SEC_INST in *. clear -Hz L TI. lia.
    - apply AGmP; [clear -L; lia|]. clear -Hz PT. intros X. lia. }
  assert (PRm : forall z, zens G A z -> exists b, m3 z = Some b).
  { intros z Hz. unfold m3.
    assert (FZ : fs_footb G z = false).
    { unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
      - apply (fs_footb_img G z HG). unfold SEC_INST in Zz. clear -Zz. lia.
      - apply (fs_footb_false_intro G z).
        + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
          rewrite FS_frames_off_val, FS_total_val in *.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
          clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    rewrite maskv_out by exact FZ.
    unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
    - pose proof (HC48 (Z.to_nat (z - (SEC_INST + 48))) ltac:(cbn [c_w]; clear -Zz; lia)) as X. cbn [c_addr] in X.
      rewrite Z2Nat.id in X by (clear -Zz; lia). replace (SEC_INST + 48 + (z - (SEC_INST + 48))) with z in X by lia.
      eexists. exact X.
    - exact (HPB z Zz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (HLB : live_block_repr m3 (bumpP A)).
  { intros b n Hin. change (aa_live (bumpP A)) with (aa_live A) in Hin.
    destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
    { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & _ & _).
      pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Y. fold G in Y. apply AGmP; [exact X | exact Y]. }
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
  assert (HPR' : primary_repr m3 (bumpP A)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (bumpP A)) with G. change (aa_cls (bumpP A)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (bumpP A) cl); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (P4' cl Hc)].
    intros z Hz.
    pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.

    unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
    5: { apply AGmT. clear -Hz Hc. lia. }
    all: apply AGmP; [|exact Y].
    all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
         destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
    all: unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
    - clear -Hz Hc GS1. lia.
    - clear -Hz Hc GS1. nia.
    - clear -Hz Hc GS1. nia.
    - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2. clear -Hz D2. lia. }
  assert (HSR' : secondary_repr m3 (bumpP A)).
  { apply (secondary_repr_ensure mE m3 A); [| exact HcR | | | exact HI3 | exact HSR].
    - intros z Hz [H|H]; [|apply AGmI; [clear -H; unfold IMG_LO, IMG_HI in *; lia | intros X; apply Hz; left; exact X]].
      apply AGmH; [exact H | intros X; apply Hz; right; exact X].
    - intros k Hk. unfold m3. rewrite maskv_out; [exact (HC48 k Hk)|]. apply (fs_footb_img G _ HG). cbn [c_addr c_w] in *. unfold SEC_INST. clear -Hk. lia.
    - intros z Hz. apply PRm. right. exact Hz. }
  assert (HQR' : quarantine_repr m3 (bumpP A)).
  { apply (quarantine_repr_agreeQ mE m3 A (bumpP A)); try reflexivity.
    - exact (q_items_rz A).
    - intros z Hz. pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
      apply AGmP; [exact QH | exact Y].
    - intros z Hz. fold G T in Hz. apply AGmT. clear -Hz. lia.
    - intros z Hz. apply AGmI; unfold QG, SEC_INST, IMG_HI in *; clear -Hz; lia.
    - exact HQR. }
  assert (HIA' : ia_inv m3 (bumpP A)).
  { apply (ia_inv_agreeN mE m3 A (bumpP A)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, SEC_INST, IMG_HI in *; clear -Hz; lia. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. rewrite AGmT; [exact X | clear; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold SEC_INST, IMG_HI in *; clear -Hz; lia.
    - apply PRESX. destruct HMI as (_ & X & _). exact X.
    - apply PRESX. destruct HMI as (_ & _ & X). exact X. }

  unfold AInvA. change (aa_geom (bumpP A)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. split; [exact Hsep|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split.
    { unfold depot_wf in HDW |- *. change (aa_depot (bumpP A)) with (aa_depot A).
      eapply depot_mem_frame; [|exact HDW]. intros a Ha.
      destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold SEC_INST, IMG_HI; clear -Hs; lia.
      - destruct (dm_nb _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold NBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia].
      - destruct (dm_fbases _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold FBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia]. }
    split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split.
  {
    unfold model_inv in HM |- *. change (aa_geom (bumpP A)) with G in *. cbn [aa_V aa_Km aa_Kf bumpP].
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    assert (KLH : PB < PB + kPtrArrayCommit) by (unfold kPtrArrayCommit; clear; lia).
    split.
    { unfold vm_geom, in_maps in V1 |- *. cbn [aa_sec aa_geom bumpP]. fold G. fold G in V1. rewrite EM, EN, EL.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split.
      { intros e x He Hx.
        assert (CV : covered (vm_noaccess (m_vmmaps md)) x = true).
        { apply (covered_subtract_true _ PB (PB + kPtrArrayCommit) x WN ltac:(clear -KLH; lia)).
          unfold covered. apply existsb_exists. exists e. split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        unfold covered in CV. apply existsb_exists in CV as (e0 & He0 & Hx0). unfold in_iv, in_rng, ivB, ivS in Hx0. apply andb_prop in Hx0 as [X1 X2].
        apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (N1 e0 x He0 (conj X1 X2)). }
      split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|].
      intros p Hal Hband. destruct (N9 p Hal Hband) as [L1 L2]. split.
      - apply page_in_ranges_spec in L1 as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [Q1 Q2]. change page_size with 4096 in Q2.
        assert (OUT : bv_unsigned p + 4096 <= PB \/ PB + kPtrArrayCommit <= bv_unsigned p).
        { unfold PB. clear -Hband P3 P4 HcR. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG, kPtrArrayReserve, kPtrArrayCommit in *. lia. }
        destruct (maps_subtract_keeps (m_vm_lazy md) PB (PB + kPtrArrayCommit) r (bv_unsigned p) (bv_unsigned p + 4096) WL ltac:(clear -KLH; lia) Hr Q1 Q2 ltac:(clear; lia) OUT)
          as (r' & Hr' & X1 & X2).
        apply page_in_ranges_spec. exists r'. split; [exact Hr'|]. apply page_in_range_spec. change page_size with 4096. clear -X1 X2. lia.
      - intros j Hj. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (L2 j Hj)]. }
    split; [rewrite (PrimCredit.prim_credit_same A (bumpP A) eq_refl); rewrite budget_boundD_bumpP; fold c;
            set (pcr := PrimCredit.prim_credit A) in *; clearbody pcr; clear -V2 HPAID; lia|].
    split; [rewrite ELIM; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite ETOP; exact V7|].

    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec bumpP] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    rewrite ER, EM.
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, ledger in L4 |- *. cbn [aa_V aa_depot bumpP]. rewrite ER, EM. exact L4. }
    split.
    { destruct L5 as [D1 D2 D3 D4 D5 D6]. constructor.
      - intros bn Hbn. rewrite EM. exact (D1 bn Hbn).
      - intros b Hb. rewrite EL.
        destruct (DEP3 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as (DY & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb, DY. fold G in SPb, DY.
        pose proof (dyn_in_big _ _ _ DY ltac:(unfold FBSZ; clear; lia)) as BB. destruct DY as (_ & _ & DT & _).
        pose proof (topG_range G) as TR.
        apply in_maps_subtract_apart; [exact KLH | rewrite u64_lit; unfold FBSZ; clear; lia | | exact (D2 b Hb)].
        rewrite !u64_lit by (unfold FBSZ, IMG_HI in *; clear -BB DT TR; lia).
        unfold PB. clear -SPb P4 HcR. unfold FBSZ, kPtrArrayReserve, kPtrArrayCommit in *. lia.
      - intros b j Hb Hj. rewrite EN. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (D3 b j Hb Hj)].
      - exact D4.
      - intros bn Hbn. rewrite ETOP. exact (D5 bn Hbn).
      - rewrite ETOP. exact D6. }
    split; [exact L6|]. split; [clear -L7 L9 HcN; fold c in L7 |- *; unfold kPtrArrayCommit in *; lia|].
    split; [unfold in_maps; rewrite ?EM; exact L8|]. split; [exact L9|]. rewrite EN. apply maps_subtract_pos. exact L10. }
  split; [exact HI3|].

  eapply bandtp_agree; [|exact HB]. intros z Hz. apply VO. unfold zens. fold G c.
  unfold SEC_INST, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve, kPtrArrayCommit in *. clear -Hz P3 P4 HcR. intros X. lia.
Qed.

Lemma AInvA_pab : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fS1dR6A1S9SaS0S11S1cR2A1M0A2SaS0S1G0S10A2M1S21R2A1M2A2SaSbS9S6G0S17A2Z0M3A3SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8M4S4S31S20S1eR7A1A2A1A2R1A2S0R1S10A2A2SaSbS9S6R1SfA2G3A3SaSbS9G2S29R2A1M5A3SaSbS9S3eS3bR4A1A1G5A3S9SaS0S1S1cR3A1M6S3G4S4S31S20S1eR8A1A2A1A2A2R1A2S2R1S1G6R2A2A2A2SeS2dQ8A1M7G7SbS34G7A1S50S3aS55R9A1R3A3S37G7R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2A2A2Tc;TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta.
  pose proof HA as (HG & _ & _ & HRest & HM & _). destruct HRest as (_ & _ & _ & HSR & _).
  pose proof (pab_facts _ X HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (_ & SP & _). destruct HM as (_ & _ & _ & _ & _ & _ & TOP & _).
  pose proof (geom_top _ HG) as GT. pose proof (geom_pab _ HG) as GP.
  repeat split; try assumption; try (clear -P4; lia).
  intros z Hz. destruct (SP z Hz) as [b Hb]. exists b. rewrite <- Hb. symmetry. apply maskv_out.
  apply (fs_footb_false_intro X.(aa_geom) z); pose proof HA as (_ & _ & _ & _ & _ & HI3 & _); destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _);
    pose proof (geom_numsS _ HG) as (_ & G2 & G3 & _); pose proof (topG_range (aa_geom X)) as TG.
  - clear -Hz PF P4. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - clear -Hz PF P4. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - rewrite FS_frames_off_val, FS_total_val in *.
    destruct (Z_lt_dec z (Sh (ag_fsb (aa_geom X) + 36864))) as [L|L]; [left; exact L|right].
    destruct (Z_le_dec (Sh (ag_fsb (aa_geom X) + 11571200)) z) as [R|R]; [exact R|exfalso].
    pose proof (sh_run_band2 (ag_fsb (aa_geom X) + 36864) (ag_fsb (aa_geom X) + 11571200) z ltac:(clear -G2; lia) ltac:(clear -G3 TG; lia) ltac:(clear -L R; lia)) as BY.
    clear -BY Hz P3 P4. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
Qed.

Lemma ensure_headroom : ltac2:(tb__ "0|0|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5SbS9S3Z8S4S31S20S1eR5A1A2A1A2S1dR5A1A3S0S2aR6A1S5dA2S7S5aR4R5A2SfA2F_;F_;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA HcN HB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _ & L9 & _).
  pose proof (budgetD_le_budget (bumpP X) (dep_cost_bound_mem _ _ HD) (dm_F_NFBLK _ _ HD) DN) as BD.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpP] in BD.
  rewrite budget_boundD_bumpP, budget_bound_bumpP in BD.
  pose proof (PrimCredit.prim_credit_nonneg X) as PCN.
  unfold headroom. rewrite VL. unfold kPtrArrayCommit in *. set (pcr := PrimCredit.prim_credit X) in *. clearbody pcr. clear -PB BD HB HcN L9 PC K0 F0 PCN. lia.
Qed.

Lemma AInvA_pabsep : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fSaScS0S1S1cR1A1M0S10A2M1S27R1A1M2A2S0S1S1G2S18A2Z1000M3A2G0A2A2SaScS0G1S28R1A1M4A2S0S1G4G3A2G0A2A2SaScS0G1S26R1A1M5A2S0S1G5S15A2G0A2A2SaScS0G1S24R1A1M6A2S0S1G6G3A2G0A2A2ScS0G1S25R1A1M7A2S0S1G7G3A2G0A2A2A2A2A2A2TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta. pose proof HA as (_ & _ & _ & _ & _ & HI3 & _).
  destruct HI3 as ((_ & _ & _ & PS & PT & PF & PC & PD) & _). repeat split; assumption.
Qed.
End CInvEnsure.

(* [comment removed for export] *)
Module InvEnsure.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "div"; "modulo"; "ge"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayCommit"; "kPtrArrayReserve"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "FS_total"; "IMG_LO"; "PG"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "AA"; "ag_pab"; "aa_ptr_committed"; "aa_sec"; "ageom"; "sec_chunk"; "topG"; "aa_cls"; "aa_live"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_spacebeg"; "ag_thread"; "ag_top"; "budget_bound"; "class_state"; "cs_empty"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "bool"; "option"; "false"; "true"; "Some"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "maps_subtract"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_noaccess"; "vm_limit"; "vm_maps"; "vm_reserved"; "iv_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "secondary_repr"; "AInvA"; "SEC_INST"; "inv3"; "geom_ok"; "primary_repr"; "live_sep"; "nthZ"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure"; "zens"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "cls_foot"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zens (G : ageom) (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|1|
ScSaS0S1S47Z30A2Vz;A2S2Vz;S1S47Z38A2A2A2SaS0S1S1cVG;A1S1dVA;A1A2M0Vz;A2S2Vz;S1G0SfA2A2A2A2").

Section Foot.
Let pabZ (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
SaS0S1cVG;A1M0Vz;A2S2Vz;S1G0S10A2A2A2").

Lemma pab_facts : ltac2:(tb__ "0|3|
S4fS1bS45R2R1A2S1aR2A1S1fSaS0S11S1cR1A1M0A2SaS0S1G0S10A2M1S21R1A1A2SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8S4S31S20S1eR3A1A2A1A2S1dR3A1M2A2S0G2S10A2A2SbS9S6G2SfA2Z0A3A2A2A2A2TG;F_;FA;Fm;").
Proof.
  intros m A HSR G. destruct HSR as (_ & _ & S2 & S3 & S45 & _). fold G in S45.
  pose proof (dyn_ok_big _ _ _ S45 ltac:(unfold kPtrArrayReserve; lia)) as B. destruct S45 as [_ (D1 & D2 & D3 & D4 & D5)].
  repeat split; try assumption; lia.
Qed.

Lemma sh_run_band : ltac2:(tb__ "0|2|
S9S9S9S0Z0R3A2M0G0S0S1R5R4A2Z7fffff800000A2SaS0S14R6A1M1R4A2S2R4S1G1S5S1R5Z7A2Z8A2A2A2A2SaS0S13R5A2S2R5S12A2A2F_;F_;F_;F_;Fy;Flen;Fb;").
Proof.
  intros b len y Hb Hl Htop Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono (b + len + 7) (140737479966720 + 7) 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (b + len + 7) 8 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (b + len + 7) 8 ltac:(lia)) as M3.
  lia.
Qed.
Lemma sh_run_band2 : ltac2:(tb__ "0|0|
S9S9S9S0Z0R3A2SaS0R4R3A2S0R3Z7fffff800000A2A2SaS0S14R5A1R3A2S2R3S14R4A1A2A2SaS0S13R4A2S2R4S12A2A2F_;F_;F_;Fy;Fe;Fb;").
Proof.
  intros b e y Hb He Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono e 140737479966720 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3. lia.
Qed.

Lemma live_foot_pab : ltac2:(tb__ "0|1|
S4fS1bS49S1aR1A1A1S4bR2A1S48R3A1S4aR5R4A2S45R6R5A2S9S9S9S56S30S9S9A2S32S9S9R3R2A4S23R9A1A3ScSaS0S8R4S19R3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S14R4A1M0R2A2S2R2S1G0S5S1R3Z7A2Z8A2A2A2A2A2SdVpabZ;S1aRbA1R3A2A1F_;F_;Fz;Fn;Fb;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG Hsep HI3 HPR HSR b n z Hin Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct Hz as [Hz|Hz].
  2: { pose proof (sh_run_band b n z ltac:(clear -L2; lia) ltac:(clear -L1; lia) ltac:(clear -L3 ACV; lia) Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    clear -Hz BLO PS RZB. intros X. lia.
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    destruct (SEC3 i ch Hi) as (_ & _ & SP & _). fold G in SP.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma q_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS49S1aR1A1A1S48R2A1S4aR4R3A2S45R5R4A2S4eR6R5A2S9S4dR7R1A2SdVpabZ;S1aR8A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG HI3 HPR HSR (Q1 & _) z Hq. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *. clear -Hz Ex X0 XA R1 R2 PS. intros X. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct Hz as [Hz|Hz].
  2: {
       assert (UT : u + n <= 140737479966720).
       { destruct (is_primary n) eqn:PRM.
         - assert (Hn : 1 <= n <= 64512).
           { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
           pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
           rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
           set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -V1 V3 R1 R2 GSB ACV Y1 Y3 Hn. nia.
         - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
           destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
           pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
           clear -Eu Esz D8 D11 D12 RU1 RU2 ACV J2. lia. }
       pose proof (sh_run_band u n z ltac:(clear -J1; lia) ltac:(clear -J2; lia) UT Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -Hz V1 V3 R1 R2 PS Y1 Y3 Hn RZ. intros X. nia.
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in *.
    destruct (SEC3 j ch Hj) as (_ & _ & SP & _). fold G in SP.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma cls_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS9S49S1aR2A1A1S48R3A1S4aR5R4A2S45R6R5A2SaS0Z1R5A2S0R5Z1eA2A2S9S5eS1aR8A1R7S4cS2bS22R8A1R7S2cA4R1A4SdVpabZ;S1aR9A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c HG HI3 HPR HSR Hc z Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  destruct HI3 as (SG3 & _). fold G in SG3. destruct SG3 as (_ & _ & _ & PS & PT & _). fold SB in PS. fold T in PT. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G T SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - clear -Hz Hc PS. intros X. lia.
  - clear -Hz Hc PS M5 M6. intros X. nia.
  - clear -Hz Hc PS M1 M2 M3. intros X. nia.
  - assert (BY : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
    { apply (sh_run_band2 (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); [clear -Hc GS1; nia | clear -Hc M1 M2 M3 GS2 ACV; nia | exact Hz]. }
    clear -BY P3. intros X. lia.
  - clear -Hz Hc PT. intros X. lia.
Qed.
End Foot.

Lemma iv_subtract_apartE : ltac2:(tb__ "0|4|
S2dQ40M0A1M1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M2S2eG0R5A2A2R4A2S0R3G2A2A2SbS2fS30G1G1A2M3A1S44R7R6R5R4A4S38G3S32G1G1R7R6A4S39G3A1A3A3F_;F_;F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hlh Hs Hd. unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma in_maps_subtract_apart : ltac2:(tb__ "0|4|
S2fS30S2dQ40M0A1M1G1A2M2A1G1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M3S2eG0R5A2A2R4A2S0R3G3A2A2S56G2S32G1G1R7R6A4R8A3S56G2S32G1G1R8R7A4S3cR9R6R5A3A3F_;F_;F_;F_;Fhi;Flo;Fsz;Fa;Fl;").
Proof.
  induction l as [|[a' s'] l IH]; intros a sz lo hi Hlh Hs Hd Hin; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [E|Hin].
  - left. injection E as -> ->. rewrite (iv_subtract_apartE a sz lo hi Hlh Hs Hd). left. reflexivity.
  - right. exact (IH _ _ _ _ Hlh Hs Hd Hin).
Qed.

Lemma maps_subtract_pos : ltac2:(tb__ "0|5|
S2fS30S2dQ40M0A1M1G1A2M2A1S9S9G1G1S56G2S32G1G1R2R1A4M3R5A3S2Z0S2eG0R2A2A2M4F_;Fs;Fb;G1G1S56G2G3S3cR6R5R4A3A3G4F_;Fs;Fb;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi H. induction l as [|[a sz] l IH]; [intros b s []|]. cbn [maps_subtract]. intros b s Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|exact (IH (fun b' s' Hi => H b' s' (or_intror Hi)) b s Hin)].
  pose proof (H a sz (or_introl eq_refl)) as Hsz. pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma covered_subtract_false : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57R6R3A2S35A3SbS33S57S3cR7R6R5A3R4A2S35A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C, H. reflexivity.
Qed.
Lemma covered_subtract_true : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57S3cR6R5R4A3R3A2S36A3SbS33S57R7R4A2S36A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C in H.
  destruct (covered l x); [reflexivity | discriminate H].
Qed.

Lemma secondary_repr_ensure : ltac2:(tb__ "0|1|
S4fS4fS1bS1aR1A1S1fS1dR2A1S9S9SdS5bR3R4R1A3A1ScS0S11R2A2SaS0S16R2A2S2R2S11A2A2A2SbS34S2dQ8A1A1R7R3A1R8R3A1A3F_;F_;Fz;S0S1R2SfA2S10A2S51R6S52S1S47Z30A2U8S5S1R3SfA2Z8A2A3A2S53R7S1S1cR5A1R4A2M0S1G0SfA2A3S48R7A1S45RaR8A2S45RaS5cR9A1A2F_;F_;F_;F_;F_;F_;Tc;TG;FA;Fm';Fm;").
Proof.
  intros m m' A. cbn zeta. intros AG HcR HC48 HPB HI3 HSR.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  destruct HI3 as (_ & _ & SEC3 & _).
  unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed bumpP].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as ACV.
  assert (AGI : forall z, IMG_LO <= z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m' z = m z).
  { intros z H1 H2. apply AG; [|right; exact H1]. intros [X|X]; [exact (H2 X)|]. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (ag_pab G + c <= z < ag_pab G + c + kPtrArrayCommit) -> m' z = m z).
  { intros z H1 H2. apply AG; [|left; exact H1]. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. fold G in D10, D12.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB.
    destruct (SEC3 i ch Hi) as (_ & _ & SPB & _).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGH; [clear -MB Ho; lia|]. unfold PG in D8. clear -SPB D8 D9 Ho Hw Hk P4 HcR. intros X. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGH; [clear -P1 Hk; lia | clear -L P4 Hk; intros X; lia]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply AGH; [clear -MB Hz; lia | clear -SPB Hz P4 HcR MS; intros X; lia]|].
    eapply present_agree; [|exact D14]. intros z Hz.
    pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -MB; unfold IMG_HI in MB; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
    apply AGH; [clear -BY; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; lia | clear -BY P3 P4 HcR; intros X; lia]. }
  split.
  {
    intros z Hz. destruct (Z_lt_dec z (ag_pab G + c)) as [Hlt|Hge].
    - rewrite AGH; [apply SP; lia | pose proof (Zle_0_nat (length (aa_sec A))); clear -Hz Hlt P1 H; lia | clear -Hlt; intros X; lia].
    - apply HPB. lia. }
  split; [clear -S2 HcR; unfold kPtrArrayCommit in *; lia|].
  split. { rewrite <- Z.add_mod_idemp_l by (unfold kPtrArrayCommit; lia). rewrite S3, Z.add_0_l. apply Z_mod_same_full. }
  split; [exact S45|].
  assert (CI : forall cc, (SEC_INST <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 48) \/ (SEC_INST + 56 <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= 0xead08) ->
               cell_ok m cc -> cell_ok m' cc).
  { intros cc H1. apply cell_ok_agree. intros k Hk. apply AGI; unfold SEC_INST, IMG_LO, IMG_HI in *; clear -H1 Hk; lia. }
  unfold SEC_INST in *.
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [exact HC48|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia|].
  split; [eapply cell_ok_agree; [|exact I8]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold IMG_LO, IMG_HI; clear -Hk; lia|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia.
Qed.

Theorem AInvA_ensure : ltac2:(tb__ "0|8|
S1bS54S54S2fS2dQ40A1M0A1S3dS3dS1aR6A1S1fS1dR7A1S9S1S1cR2A1R1A2S9S46S3aR9R8R6R5A5SbS9S3Z8M1S4S31S20S1eRaA1A2A1A2R3A3S0S1R4SfA2S10A2SbS2fS30G0G0A2A1M2S42S3bR7A1A1S42S3bR8A1M3A1A3SbG2S43G3A1S43S3bR9A1M4A1A3SbG2S40G4A1S3cS40S3bRaA1A1R6S1R6SfA2A3A3SbG2S3fRaA1S3cS3fRbA1R7S1R7SfA2A3A3SbS9S41S3bRbA1A1S41S3bRcA1M5A1A3SbS9S3eG5A1S3eS3bRdA1A1A3S58S40S3bReA1A1A1S58S3fRfA1A1S0S59RfR11A2S1S59R10R11A2SfA2A2S9SdS5bR10R16R1A3A1SbS34S2dQ8A1A1S50S3aS55R15A1M6R2A3S50S3aS55R16A1R2A3A3F_;Fz;S51S50S3aS55R14A1A2S52S1S47Z30A2U8S5S1RfSfA2M7G1A2A3A2S53S50S3aG6A2RfG7A3S46S3aS5cR18A1R16R15R13A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TPB;Tc;TG;Fmd';Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md md'. cbn zeta. intros HA HcN HcR EM ER EN EL ELIM ETOP WN WL HPAID VO HC48 HPB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5).
  pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3).
  pose proof SG3 as (_ & _ & _ & PS & PT & PF & PC & PD).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *. set (PB := ag_pab G + c) in *. set (T := ag_thread G) in *.
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & CI & DI). fold T in TB, TI. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI, CI, DI.
  assert (ZD : forall z, zens G A z \/ ~ zens G A z) by (intros z; unfold zens; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply AGH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGZ : forall z, ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H1 X)|]. apply H2. unfold PB in X. clear -X P4 HcR. lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (cc & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply AGZ; unfold SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y;
        first [ clear -X Y TI PT; lia | clear -X Y CI PC; lia | clear -X Y DI PD; lia | clear -X Y G2 PF; lia ] |]); destruct Hc. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (bumpP A)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. unfold zens in Zz. fold G c in Zz.
         destruct Zz as [Zz|Zz].
         - rewrite (fs_footb_img G z HG) in Hz; [discriminate|]. unfold SEC_INST in Zz. clear -Zz. lia.
         - rewrite (fs_footb_false_intro G z) in Hz; [discriminate| | |].
           + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
             rewrite FS_frames_off_val, FS_total_val in *.
             destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
             destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
             specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
             clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    exact HF. }

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ zens G A z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGmP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> m3 z = mE z).
  { intros z H1 H2. apply AGmH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGmT : forall z, T <= z < T + 0x1000 -> m3 z = mE z).
  { intros z Hz. destruct (Z_lt_dec z IMG_HI) as [L|L].
    - apply AGmI; [exact L|]. unfold IMG_HI, SEC_INST in *. clear -Hz L TI. lia.
    - apply AGmP; [clear -L; lia|]. clear -Hz PT. intros X. lia. }
  assert (PRm : forall z, zens G A z -> exists b, m3 z = Some b).
  { intros z Hz. unfold m3.
    assert (FZ : fs_footb G z = false).
    { unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
      - apply (fs_footb_img G z HG). unfold SEC_INST in Zz. clear -Zz. lia.
      - apply (fs_footb_false_intro G z).
        + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
          rewrite FS_frames_off_val, FS_total_val in *.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
          clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    rewrite maskv_out by exact FZ.
    unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
    - pose proof (HC48 (Z.to_nat (z - (SEC_INST + 48))) ltac:(cbn [c_w]; clear -Zz; lia)) as X. cbn [c_addr] in X.
      rewrite Z2Nat.id in X by (clear -Zz; lia). replace (SEC_INST + 48 + (z - (SEC_INST + 48))) with z in X by lia.
      eexists. exact X.
    - exact (HPB z Zz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (HLB : live_block_repr m3 (bumpP A)).
  { intros b n Hin. change (aa_live (bumpP A)) with (aa_live A) in Hin.
    destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
    { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & _ & _).
      pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Y. fold G in Y. apply AGmP; [exact X | exact Y]. }
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
  assert (HPR' : primary_repr m3 (bumpP A)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (bumpP A)) with G. change (aa_cls (bumpP A)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (bumpP A) cl); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (P4' cl Hc)].
    intros z Hz.
    pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.

    unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
    5: { apply AGmT. clear -Hz Hc. lia. }
    all: apply AGmP; [|exact Y].
    all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
         destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
    all: unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
    - clear -Hz Hc GS1. lia.
    - clear -Hz Hc GS1. nia.
    - clear -Hz Hc GS1. nia.
    - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2. clear -Hz D2. lia. }
  assert (HSR' : secondary_repr m3 (bumpP A)).
  { apply (secondary_repr_ensure mE m3 A); [| exact HcR | | | exact HI3 | exact HSR].
    - intros z Hz [H|H]; [|apply AGmI; [clear -H; unfold IMG_LO, IMG_HI in *; lia | intros X; apply Hz; left; exact X]].
      apply AGmH; [exact H | intros X; apply Hz; right; exact X].
    - intros k Hk. unfold m3. rewrite maskv_out; [exact (HC48 k Hk)|]. apply (fs_footb_img G _ HG). cbn [c_addr c_w] in *. unfold SEC_INST. clear -Hk. lia.
    - intros z Hz. apply PRm. right. exact Hz. }
  assert (HQR' : quarantine_repr m3 (bumpP A)).
  { apply (quarantine_repr_agreeQ mE m3 A (bumpP A)); try reflexivity.
    - exact (q_items_rz A).
    - intros z Hz. pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
      apply AGmP; [exact QH | exact Y].
    - intros z Hz. fold G T in Hz. apply AGmT. clear -Hz. lia.
    - intros z Hz. apply AGmI; unfold QG, SEC_INST, IMG_HI in *; clear -Hz; lia.
    - exact HQR. }
  assert (HIA' : ia_inv m3 (bumpP A)).
  { apply (ia_inv_agreeN mE m3 A (bumpP A)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, SEC_INST, IMG_HI in *; clear -Hz; lia. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. rewrite AGmT; [exact X | clear; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold SEC_INST, IMG_HI in *; clear -Hz; lia.
    - apply PRESX. destruct HMI as (_ & X & _). exact X.
    - apply PRESX. destruct HMI as (_ & _ & X). exact X. }

  unfold AInvA. change (aa_geom (bumpP A)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. split; [exact Hsep|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split.
    { unfold depot_wf in HDW |- *. change (aa_depot (bumpP A)) with (aa_depot A).
      eapply depot_mem_frame; [|exact HDW]. intros a Ha.
      destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold SEC_INST, IMG_HI; clear -Hs; lia.
      - destruct (dm_nb _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold NBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia].
      - destruct (dm_fbases _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold FBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia]. }
    split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split.
  {
    unfold model_inv in HM |- *. change (aa_geom (bumpP A)) with G in *. cbn [aa_V aa_Km aa_Kf bumpP].
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    assert (KLH : PB < PB + kPtrArrayCommit) by (unfold kPtrArrayCommit; clear; lia).
    split.
    { unfold vm_geom, in_maps in V1 |- *. cbn [aa_sec aa_geom bumpP]. fold G. fold G in V1. rewrite EM, EN, EL.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split.
      { intros e x He Hx.
        assert (CV : covered (vm_noaccess (m_vmmaps md)) x = true).
        { apply (covered_subtract_true _ PB (PB + kPtrArrayCommit) x WN ltac:(clear -KLH; lia)).
          unfold covered. apply existsb_exists. exists e. split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        unfold covered in CV. apply existsb_exists in CV as (e0 & He0 & Hx0). unfold in_iv, in_rng, ivB, ivS in Hx0. apply andb_prop in Hx0 as [X1 X2].
        apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (N1 e0 x He0 (conj X1 X2)). }
      split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|].
      intros p Hal Hband. destruct (N9 p Hal Hband) as [L1 L2]. split.
      - apply page_in_ranges_spec in L1 as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [Q1 Q2]. change page_size with 4096 in Q2.
        assert (OUT : bv_unsigned p + 4096 <= PB \/ PB + kPtrArrayCommit <= bv_unsigned p).
        { unfold PB. clear -Hband P3 P4 HcR. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG, kPtrArrayReserve, kPtrArrayCommit in *. lia. }
        destruct (maps_subtract_keeps (m_vm_lazy md) PB (PB + kPtrArrayCommit) r (bv_unsigned p) (bv_unsigned p + 4096) WL ltac:(clear -KLH; lia) Hr Q1 Q2 ltac:(clear; lia) OUT)
          as (r' & Hr' & X1 & X2).
        apply page_in_ranges_spec. exists r'. split; [exact Hr'|]. apply page_in_range_spec. change page_size with 4096. clear -X1 X2. lia.
      - intros j Hj. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (L2 j Hj)]. }
    split; [rewrite (PrimCredit.prim_credit_same A (bumpP A) eq_refl); rewrite budget_boundD_bumpP; fold c;
            set (pcr := PrimCredit.prim_credit A) in *; clearbody pcr; clear -V2 HPAID; lia|].
    split; [rewrite ELIM; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite ETOP; exact V7|].

    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec bumpP] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    rewrite ER, EM.
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, ledger in L4 |- *. cbn [aa_V aa_depot bumpP]. rewrite ER, EM. exact L4. }
    split.
    { destruct L5 as [D1 D2 D3 D4 D5 D6]. constructor.
      - intros bn Hbn. rewrite EM. exact (D1 bn Hbn).
      - intros b Hb. rewrite EL.
        destruct (DEP3 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as (DY & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb, DY. fold G in SPb, DY.
        pose proof (dyn_in_big _ _ _ DY ltac:(unfold FBSZ; clear; lia)) as BB. destruct DY as (_ & _ & DT & _).
        pose proof (topG_range G) as TR.
        apply in_maps_subtract_apart; [exact KLH | rewrite u64_lit; unfold FBSZ; clear; lia | | exact (D2 b Hb)].
        rewrite !u64_lit by (unfold FBSZ, IMG_HI in *; clear -BB DT TR; lia).
        unfold PB. clear -SPb P4 HcR. unfold FBSZ, kPtrArrayReserve, kPtrArrayCommit in *. lia.
      - intros b j Hb Hj. rewrite EN. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (D3 b j Hb Hj)].
      - exact D4.
      - intros bn Hbn. rewrite ETOP. exact (D5 bn Hbn).
      - rewrite ETOP. exact D6. }
    split; [exact L6|]. split; [clear -L7 L9 HcN; fold c in L7 |- *; unfold kPtrArrayCommit in *; lia|].
    split; [unfold in_maps; rewrite ?EM; exact L8|]. split; [exact L9|]. rewrite EN. apply maps_subtract_pos. exact L10. }
  split; [exact HI3|].

  eapply bandtp_agree; [|exact HB]. intros z Hz. apply VO. unfold zens. fold G c.
  unfold SEC_INST, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve, kPtrArrayCommit in *. clear -Hz P3 P4 HcR. intros X. lia.
Qed.

Lemma AInvA_pab : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fS1dR6A1S9SaS0S11S1cR2A1M0A2SaS0S1G0S10A2M1S21R2A1M2A2SaSbS9S6G0S17A2Z0M3A3SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8M4S4S31S20S1eR7A1A2A1A2R1A2S0R1S10A2A2SaSbS9S6R1SfA2G3A3SaSbS9G2S29R2A1M5A3SaSbS9S3eS3bR4A1A1G5A3S9SaS0S1S1cR3A1M6S3G4S4S31S20S1eR8A1A2A1A2A2R1A2S2R1S1G6R2A2A2A2SeS2dQ8A1M7G7SbS34G7A1S50S3aS55R9A1R3A3S37G7R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2A2A2Tc;TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta.
  pose proof HA as (HG & _ & _ & HRest & HM & _). destruct HRest as (_ & _ & _ & HSR & _).
  pose proof (pab_facts _ X HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (_ & SP & _). destruct HM as (_ & _ & _ & _ & _ & _ & TOP & _).
  pose proof (geom_top _ HG) as GT. pose proof (geom_pab _ HG) as GP.
  repeat split; try assumption; try (clear -P4; lia).
  intros z Hz. destruct (SP z Hz) as [b Hb]. exists b. rewrite <- Hb. symmetry. apply maskv_out.
  apply (fs_footb_false_intro X.(aa_geom) z); pose proof HA as (_ & _ & _ & _ & _ & HI3 & _); destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _);
    pose proof (geom_numsS _ HG) as (_ & G2 & G3 & _); pose proof (topG_range (aa_geom X)) as TG.
  - clear -Hz PF P4. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - clear -Hz PF P4. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - rewrite FS_frames_off_val, FS_total_val in *.
    destruct (Z_lt_dec z (Sh (ag_fsb (aa_geom X) + 36864))) as [L|L]; [left; exact L|right].
    destruct (Z_le_dec (Sh (ag_fsb (aa_geom X) + 11571200)) z) as [R|R]; [exact R|exfalso].
    pose proof (sh_run_band2 (ag_fsb (aa_geom X) + 36864) (ag_fsb (aa_geom X) + 11571200) z ltac:(clear -G2; lia) ltac:(clear -G3 TG; lia) ltac:(clear -L R; lia)) as BY.
    clear -BY Hz P3 P4. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
Qed.

Lemma ensure_headroom : ltac2:(tb__ "0|0|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5SbS9S3Z8S4S31S20S1eR5A1A2A1A2S1dR5A1A3S0S2aR6A1S5dA2S7S5aR4R5A2SfA2F_;F_;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA HcN HB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _ & L9 & _).
  pose proof (budgetD_le_budget (bumpP X) (dep_cost_bound_mem _ _ HD) (dm_F_NFBLK _ _ HD) DN) as BD.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpP] in BD.
  rewrite budget_boundD_bumpP, budget_bound_bumpP in BD.
  pose proof (PrimCredit.prim_credit_nonneg X) as PCN.
  unfold headroom. rewrite VL. unfold kPtrArrayCommit in *. set (pcr := PrimCredit.prim_credit X) in *. clearbody pcr. clear -PB BD HB HcN L9 PC K0 F0 PCN. lia.
Qed.

Lemma AInvA_pabsep : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fSaScS0S1S1cR1A1M0S10A2M1S27R1A1M2A2S0S1S1G2S18A2Z1000M3A2G0A2A2SaScS0G1S28R1A1M4A2S0S1G4G3A2G0A2A2SaScS0G1S26R1A1M5A2S0S1G5S15A2G0A2A2SaScS0G1S24R1A1M6A2S0S1G6G3A2G0A2A2ScS0G1S25R1A1M7A2S0S1G7G3A2G0A2A2A2A2A2A2TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta. pose proof HA as (_ & _ & _ & _ & _ & HI3 & _).
  destruct HI3 as ((_ & _ & _ & PS & PT & PF & PC & PD) & _). repeat split; assumption.
Qed.
End InvEnsure.


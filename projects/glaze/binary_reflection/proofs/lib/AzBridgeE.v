(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module BE.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Bridge.
Context {RC : run_ceil}.   (* [comment removed for export] *)
#[local] Notation CEILr := (@GlzConst.RunCeil.CEIL RC).
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable ISP : expr.     (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis IMG_le : img_lo A <= img_hi A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP) <= bv_unsigned a.
(* [comment removed for export] *)
Variable SHC VSH : list (Z * Z).
(* [comment removed for export] *)
Hypothesis SHC_stack : forall z, SB + CEILr / 8 <= z -> z <= SB + (2 ^ 47 - 1) / 8 -> GPS.in_shc SHC z = true.
Hypothesis SHC_img : forall z, SB + img_lo A / 8 <= z -> z <= SB + (img_hi A - 1) / 8 -> GPS.in_shc SHC z = true.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation u := bv_unsigned.

Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH ISP argH_high.
Let hid_hull' := APS.hid_hull A HULL_ok argH ISP argH_high.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_base_le : forall a : word, u (page_base a) <= u a /\ u a < u (page_base a) + 4096 /\ u (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma lz_page : forall model (a : word),
  GPS.lz model a = true ->
  exists iv, In iv (m_vm_lazy model) /\ u (fst iv) <= u (page_base a) /\ u (page_base a) + 4096 <= u (fst iv) + u (snd iv).
Proof.
  intros model a H. unfold GPS.lz, page_in_ranges in H. apply existsb_exists in H as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold page_size in H2.
  exists iv. split; [exact Hin|]. lia.
Qed.

(* [comment removed for export] *)
Lemma lz_false_img : forall E cs R M model (a : word),
  CSOK E cs R M model -> img_lo A <= u a < img_hi A -> GPS.lz model a = false.
Proof.
  intros E cs R M model a HC Ha. destruct (GPS.lz model a) eqn:Hl; [|reflexivity]. exfalso.
  destruct (lz_page model a Hl) as (iv & Hin & H1 & H2).
  pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as [L1 L2].
  pose proof (page_base_le a) as (P1 & P2 & P3). lia.
Qed.

(* [comment removed for export] *)
Definition ceil_top (model : Model) : Prop := page_floor (alloc_top (m_vmmaps model)) <= CEILr.

Lemma lz_false_stack : forall E cs R M model (a : word),
  CSOK E cs R M model -> ceil_top model -> CEILr <= u a -> GPS.lz model a = false.
Proof.
  intros E cs R M model a HC HT Ha. destruct (GPS.lz model a) eqn:Hl; [|reflexivity]. exfalso.
  destruct (lz_page model a Hl) as (iv & Hin & H1 & H2).
  pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as [L1 L2].
  pose proof (page_base_le a) as (P1 & P2 & P3).
  assert (Hpg : (u (page_base a) + 4096) mod 4096 = 0).
  { rewrite Z.add_mod, P3, Z.mod_same by lia. reflexivity. }
  pose proof (page_floor_bound (u (page_base a) + 4096) (alloc_top (m_vmmaps model)) Hpg ltac:(lia)) as HB.
  unfold ceil_top in HT. lia.
Qed.



















Lemma mrestrict_false : forall M, mrestrict (fun _ : word => false) M = M.
Proof. intros M. apply functional_extensionality. intros a. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_full : forall E cs R M model TK,
  CSOK E cs R M model -> know_ok SEGS E (MR E cs model M) TK -> kimg_in_hull A TK -> know_ok SEGS E M TK.
Proof.
  intros E cs R M model TK HC HK Hki.
  rewrite <- (mrestrict_false M). unfold APS.Mr in HK.
  eapply (APS.know_ok_unhide SEGS A E (HID E cs model) (fun _ => false) M TK).
  - apply H_off_segments_cs'.
  - exact Hki.
  - intros a Ha. discriminate Ha.
  - intros a Ha. apply hid_hull'. exact Ha.
  - exact HK.
Qed.




(* [comment removed for export] *)
Theorem transport_regs : forall E cs R M model th tregs,
  CSOK E cs R M model ->
  regs_ent (kn cs) 0 (map (tsubst th) tregs) (s_regs (a_ss cs)) = true ->
  regs_ok (GPS.tenv E th) tregs R.
Proof.
  intros E cs R M model th tregs HC Hregs.
  apply (proj1 (GPS.regs_ok_tsubst E th tregs R)).
  destruct (GPS.regs_ent_sound SEGS E _ (kn cs) _ _ 0%nat (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hregs) as [Hlen Hn].
  intros r. rewrite (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC r). unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|]. symmetry. apply Hn.
  intros Hz. cbn in Hz. unfold ridx in Hz. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0.
  change (bv_unsigned r = 0). pose proof (u5_range r). lia.
Qed.



















End Bridge.
End BE.

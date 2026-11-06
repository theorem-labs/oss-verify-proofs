(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzGPS AzSIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
  length bs = n -> (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros n bs <- Hn. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (bytes_le_to_Z_nonneg bs).
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

(* [comment removed for export] *)
Lemma split_lit_vars : forall n e b k, split_lit e = (b, k) -> expr_vars_lt n e = true -> expr_vars_lt n b = true.
Proof.
  intros n e b k H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ext.
Variable SEGS : list Segment.
Variable RR : shape_rel SEGS.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Variable FXOK : GPS.FX -> Prop.
Variable ISP : expr.
Hypothesis ISP_vars : expr_vars_lt nx0 ISP = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).
#[local] Notation MR := (APS.Mr A argH).

Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0.
Let cs_ok_set_kn' := APS.cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0.

(* [comment removed for export] *)
Lemma node_nameword_ok : forall args cs cs' E R FULL model,
  CSOK E cs R FULL model -> node_nameword nx0 cs args = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ CSOK E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros args cs cs' E R FULL model HC Hn. unfold node_nameword in Hn.
  destruct args as [|base [|e2 rest]]; try discriminate. destruct e2 as [w| | | | | | |]; try discriminate.
  destruct rest; [|discriminate].
  destruct (split_lit base) as [bb bo] eqn:Hsp.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hc Hw].
  apply andb_prop in Hc as [Hfresh Hvb].
  assert (Hw' : 0 < w <= 8).
  { repeat (apply orb_prop in Hw as [Hw|Hw]); apply Z.eqb_eq in Hw; subst w; lia. }
  set (v := nxt cs) in *. set (k := kn cs) in *.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK. fold k in HK.
  set (M := MR E cs model FULL) in HK.
  (* [comment removed for export] *)
  destruct (flat_x_sound SEGS E M k bb bo (ELit w) HK Hflat) as (F1 & F2 & F3).
  cbn [edenot] in F2, F3. rewrite (u64_lit w) in F2, F3 by lia.
  assert (HFL : flat E (SA bb bo) w) by (unfold flat; lia).
  pose proof (flat_u E _ _ HFL) as Hu. unfold estart in F1, F2, Hu; cbn [a_base a_off] in F1, F2, Hu.
  set (a := adenot E (SA bb bo)) in *.
  assert (RD : exists bs, rdn SEGS M a (Z.to_nat w) = Some bs /\ length bs = Z.to_nat w).
  { apply (readable_rdn SEGS M (Z.to_nat w) a); [rewrite Hu, Z2Nat.id by lia; lia|].
    intros x Hx. rewrite Hu, Z2Nat.id in Hx by lia.
    replace x with (Z_to_bv 64 (uE E bb + (bv_unsigned x - uE E bb))) by (unfold uE; rewrite Zplus_minus; apply Z_to_bv_bv_unsigned).
    apply (cover_x_readable SEGS _ E M k bb bo (bo + w) HK Hcov). unfold uE. lia. }
  destruct RD as (bs & Hrd & Hlen).
  set (val := Z_to_bv 64 (bytes_le_to_Z bs)). set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree' E E' cs R FULL model Hag Hfresh HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  (* [comment removed for export] *)
  assert (HM' : MR E' cs model FULL = M).
  { unfold M, Mr. rewrite (hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow). reflexivity. }
  assert (Ha' : adenot E' (SA bb bo) = a).
  { unfold a, adenot. cbn [a_base a_off]. rewrite (edenot_agree' v E E' bb Hag (split_lit_vars (nxt cs) base bb bo Hsp Hvb)). reflexivity. }
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. rewrite HM' in HK'. fold k in HK'.
  assert (HKW : know_ok SEGS E' M (KWord (SA bb bo) (Z.to_nat w) (EVar v) :: kn_cutout k bb bo (ELit w))).
  { constructor.
    - cbn [kentry_ok]. split; [lia|]. split.
      + unfold flat, estart. cbn [a_base a_off].
        replace (edenot E' bb) with (edenot E bb) by (eapply (edenot_agree' v); [exact Hag | exact (split_lit_vars (nxt cs) base bb bo Hsp Hvb)]).
        rewrite Z2Nat.id by lia. lia.
      + rewrite Ha', Hrd. f_equal. cbn [edenot]. unfold E'. rewrite ext1_at. unfold val.
        symmetry. apply word_to_le_bytes_of_bytes_n; [exact Hlen | lia].
    - apply (know_ok_cutout SEGS E' M M k bb bo (ELit w) HK'). intros; reflexivity. }
  assert (HC1 : CSOK E' (set_kn cs (KWord (SA bb bo) (Z.to_nat w) (EVar v) :: kn_cutout k bb bo (ELit w))) R FULL model).
  { apply cs_ok_set_kn'; [exact HC'|]. rewrite HM'. exact HKW. }
  clear - HC1. subst v k.
  destruct HC1; constructor; cbn [bump set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud] in *;
    try assumption; reflexivity.
Qed.

Theorem node_nameword_sound1 : forall args,
  SIF.node1_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK SIF.always (fun cs => node_nameword nx0 cs args).
Proof.
  intros args cs cs' E fx R M model T HC HF _ Hn Hk.
  destruct (node_nameword_ok args cs cs' E R M model HC Hn) as (E' & Hag & HC' & Hpc).
  rewrite <- Hpc. exact (Hk E' fx R M model Hag HC' HF eq_refl).
Qed.

Theorem node_nameword_sound : forall args,
  SIF.node1_stmtN SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK SIF.always (fun cs => node_nameword nx0 cs args).
Proof. intros args. apply SIF.node1_stmt_N. apply node_nameword_sound1. Qed.

End Ext.

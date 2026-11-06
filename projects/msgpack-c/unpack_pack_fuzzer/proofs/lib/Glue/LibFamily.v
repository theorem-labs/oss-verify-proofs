(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module LibFamily.
Section Run.
Variable segs : list Segment.
Variable R : drun.
Let MP := r_MP R.
Let PB := r_PB R.
Variables (N : int) (E0 : env) (K : TSet).
Hypothesis HPB : PB (eb E0).

Let LN := LNODE segs R N E0 K.

Record fmem := FM { fm_id : int; fm_tpl : template; fm_ctx : ctx; fm_plan : plan; fm_obls : list obligation;
                    fm_cutl : list (int * template) }.

Definition heads (FAM : list fmem) : list (int * template) := map (fun M => (fm_id M, fm_tpl M)) FAM.

Definition fmem_ok (HD : list (int * template)) (M : fmem) : Prop :=
  ctx_wfb (fm_ctx M) = true /\ itab_ok segs (c_itab (fm_ctx M)) /\ contracts_ok segs (OPS R) (fm_ctx M) MP PB /\
  c_mroot (fm_ctx M) = t_measure (fm_tpl M) /\
  check segs (fm_ctx M) (fm_plan M) (t_st (fm_tpl M)) = Some (fm_obls M) /\ obls_hold PB (fm_obls M) /\
  vars_below (s_next (t_st (fm_tpl M))) (t_measure (fm_tpl M)) = true /\
  plan_stable N (fm_plan M) = true /\ PrimInt63.leb N (s_next (t_st (fm_tpl M))) = true /\
  c_cuts (fm_ctx M) = imap_of (fm_cutl M) /\ c_ecalls (fm_ctx M) = imap_of [] /\
  Forall (fun kv => (In kv HD /\ uses_plain_cut (fm_plan M) (fst kv) = false) \/ LN (t_st (snd kv))) (fm_cutl M).

Lemma heads_in : forall FAM h T, In (h, T) (heads FAM) -> exists M, In M FAM /\ fm_id M = h /\ fm_tpl M = T.
Proof.
  intros FAM h T H. unfold heads in H. apply in_map_iff in H as (M & E & HM). exists M. injection E as E1 E2. auto.
Qed.

Theorem lnode_family : forall FAM, Forall (fmem_ok (heads FAM)) FAM -> Forall (fun kv => LN (t_st (snd kv))) (heads FAM).
Proof.
  intros FAM HF.
  assert (main : forall (k : nat) M, In M FAM -> forall E ms model,
            bv_unsigned (den E (t_measure (fm_tpl M))) < Z.of_nat k ->
            eb E = eb E0 -> stable N E0 E -> MP model -> st_ok segs (OPS R) E (t_st (fm_tpl M)) ms model ->
            realizes segs (mkCfg ms model) K).
  { induction k as [|k IH]; intros M HM E ms model Hlt Heb HST HMP HS.
    - exfalso. pose proof (bv_unsigned_in_range _ (den E (t_measure (fm_tpl M)))). cbn [Z.of_nat] in Hlt. lia.
    - pose proof (proj1 (Forall_forall _ _) HF M HM) as
        (HWF & HIT & HCO & Hm & HCHK & HOB & HMV & HP & HN & Hc & He & Hcuts).
      apply leb_spec in HN.
      eapply (check_sound_stable segs (OPS R) N (fm_ctx M) MP PB (fm_plan M) (t_st (fm_tpl M)) (fm_obls M)
                HWF HIT HCO (r_MPA R) HCHK HOB ltac:(rewrite Hm; exact HMV) HP HN K E ms model HS);
        [rewrite Heb; exact HPB | exact HMP |].
      split.
      + intros tid T' Hf E' ms' model' Heb' HST' HMP' HS' Hdec. rewrite Hc in Hf.
        destruct (Forall_imap_of _ _ (fm_cutl M) tid T' Hcuts Hf) as [[Hin Hplain] | Hnode].
        * cbn [fst snd] in Hin, Hplain. destruct Hdec as [Hpc | Hlt']; [rewrite Hplain in Hpc; discriminate Hpc|].
          rewrite Hm in Hlt'. destruct (heads_in FAM tid T' Hin) as (M' & HM' & _ & HT').
          apply (IH M' HM' E' ms' model'); [rewrite HT' | congruence | exact (stable_trans N E0 E E' HST HST') | exact HMP' | rewrite HT'; exact HS'].
          rewrite Nat2Z.inj_succ in Hlt. lia.
        * cbn [snd] in Hnode. exact (Hnode E' ms' model' ltac:(congruence) (stable_trans N E0 E E' HST HST') HMP' HS').
      + intros eid T' Hf. exfalso. rewrite He in Hf. apply imap_of_find_in in Hf. exact Hf. }
  apply Forall_forall. intros [h T] Hin. cbn [snd]. destruct (heads_in FAM h T Hin) as (M & HM & _ & HT).
  intros E ms model Heb HST HMP HS. rewrite <- HT in HS.
  apply (main (S (Z.to_nat (bv_unsigned (den E (t_measure (fm_tpl M)))))) M HM E ms model); try assumption.
  pose proof (bv_unsigned_in_range _ (den E (t_measure (fm_tpl M)))). rewrite Nat2Z.inj_succ, Z2Nat.id; lia.
Qed.

Lemma lnode_family_nth : forall FAM i M, Forall (fmem_ok (heads FAM)) FAM -> nth_error FAM i = Some M -> LN (t_st (fm_tpl M)).
Proof.
  intros FAM i M HF Hi. pose proof (lnode_family FAM HF) as L.
  assert (Hin : In (fm_id M, fm_tpl M) (heads FAM)).
  { unfold heads. apply in_map_iff. exists M. split; [reflexivity| exact (nth_error_In _ _ Hi)]. }
  exact (proj1 (Forall_forall _ _) L _ Hin).
Qed.

End Run.
End LibFamily.

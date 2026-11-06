(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive aev : Type :=
| AMmapFixed (addr len : Z)      (* [comment removed for export] *)
| AMmapNull (len r : Z)          (* [comment removed for export] *)
| AMmapFixedNR (addr len : Z)    (* [comment removed for export] *)
| AMunmap (addr len : Z)         (* [comment removed for export] *)
| AMadvise (addr len : Z).       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition art_zfill (M : word -> option byte) (r len : Z) : word -> option byte :=
  fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then Some (Z_to_bv 8 0) else M a.
Definition art_unmap (M : word -> option byte) (r len : Z) : word -> option byte :=
  fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then None else M a.

(* [comment removed for export] *)
Definition art_shlo (r : Z) : Z := (r / 8 + 0x7fff8000) / 4096 * 4096.
Definition art_shhi (r len : Z) : Z := ((r + len) / 8 + 0x7fff8000 + 4095) / 4096 * 4096.
Definition art_reveal (M : word -> option byte) (lo hi : Z) : word -> option byte :=
  fun a => if (lo <=? bv_unsigned a) && (bv_unsigned a <? hi) then (match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end) else M a.

Lemma art_reveal_in : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a = match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end.
Proof. intros M lo hi a H. unfold art_reveal. replace ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_reveal_out : forall M lo hi a, ~ (lo <= bv_unsigned a < hi) -> art_reveal M lo hi a = M a.
Proof.
  intros M lo hi a H. unfold art_reveal. destruct (lo <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? hi) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma art_reveal_some : forall M lo hi a b, M a = Some b -> art_reveal M lo hi a = Some b.
Proof. intros M lo hi a b H. unfold art_reveal. rewrite H. destruct ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)); reflexivity. Qed.
Lemma art_reveal_defined : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a <> None.
Proof. intros M lo hi a H. rewrite art_reveal_in by exact H. destruct (M a); discriminate. Qed.

Lemma art_zfill_in : forall M r len a, r <= bv_unsigned a < r + len -> art_zfill M r len a = Some (Z_to_bv 8 0).
Proof. intros M r len a H. unfold art_zfill. replace ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_zfill_out : forall M r len a, ~ (r <= bv_unsigned a < r + len) -> art_zfill M r len a = M a.
Proof.
  intros M r len a H. unfold art_zfill. destruct (r <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? r + len) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma art_unmap_in : forall M r len a, r <= bv_unsigned a < r + len -> art_unmap M r len a = None.
Proof. intros M r len a H. unfold art_unmap. replace ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_unmap_out : forall M r len a, ~ (r <= bv_unsigned a < r + len) -> art_unmap M r len a = M a.
Proof.
  intros M r len a H. unfold art_unmap. destruct (r <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? r + len) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.

Section Runs.
Variable segs : list Segment.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

Definition art_at_ecall (pc : word) : Prop := exists w, fetch_word segs pc = Some w /\ is_ecall w = true.

(* [comment removed for export] *)
Definition art_mmap_args (regs : bvmap 5 word) (addr len flags : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 222 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 3
  /\ getr regs 13 = Z_to_bv 64 flags /\ getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs 15 = Z_to_bv 64 0.
Definition art_munmap_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 215 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len.
Definition art_madvise_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 233 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 4.

Inductive aruns (Q : list aev -> machine_state -> Prop) : list aev -> machine_state -> Prop :=
| ar_done : forall log s, Q log s -> aruns Q log s
| ar_steps : forall log s s', msteps segs s s' -> aruns Q log s' -> aruns Q log s
| ar_mmap_fixed : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 50 -> EVOK log (AMmapFixed addr len) ->
    aruns Q (log ++ [AMmapFixed addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_mmap_null : forall log regs (pc pc' : word) M rom len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs 0 len 34 -> EVOK log (AMmapNull len 0) ->
    (forall r, GR log M len r ->
       aruns Q (log ++ [AMmapNull len r]) (mkst (regupd regs 10 (Z_to_bv 64 r)) pc' (art_reveal (art_zfill M r len) (art_shlo r) (art_shhi r len)) rom)) ->
    aruns Q log (mkst regs pc M rom)
| ar_mmap_fixed_nr : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 16434 -> EVOK log (AMmapFixedNR addr len) ->
    aruns Q (log ++ [AMmapFixedNR addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_munmap : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_munmap_args regs addr len -> EVOK log (AMunmap addr len) ->
    aruns Q (log ++ [AMunmap addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_unmap M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_madvise : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_madvise_args regs addr len -> EVOK log (AMadvise addr len) ->
    aruns Q (log ++ [AMadvise addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom).

Lemma aruns_mono : forall (Q Q' : list aev -> machine_state -> Prop) log s,
  aruns Q log s -> (forall log' s', Q log' s' -> Q' log' s') -> aruns Q' log s.
Proof.
  intros Q Q' log s H HQ. induction H.
  - apply ar_done. apply HQ. assumption.
  - eapply ar_steps; eassumption.
  - eapply ar_mmap_fixed; eassumption.
  - eapply ar_mmap_null; eassumption.
  - eapply ar_mmap_fixed_nr; eassumption.
  - eapply ar_munmap; eassumption.
  - eapply ar_madvise; eassumption.
Qed.

(* [comment removed for export] *)
Lemma aruns_bind : forall (Q1 Q2 : list aev -> machine_state -> Prop) log s,
  aruns Q1 log s -> (forall log' s', Q1 log' s' -> aruns Q2 log' s') -> aruns Q2 log s.
Proof.
  intros Q1 Q2 log s H HQ. induction H.
  - apply HQ. assumption.
  - eapply ar_steps; eassumption.
  - eapply ar_mmap_fixed; eassumption.
  - eapply ar_mmap_null; eassumption.
  - eapply ar_mmap_fixed_nr; eassumption.
  - eapply ar_munmap; eassumption.
  - eapply ar_madvise; eassumption.
Qed.

Lemma aruns_msteps_done : forall (Q : list aev -> machine_state -> Prop) log s s', msteps segs s s' -> Q log s' -> aruns Q log s.
Proof. intros Q log s s' H HQ. eapply ar_steps; [exact H|]. apply ar_done. exact HQ. Qed.

(* [comment removed for export] *)
Lemma aruns_of_msteps : forall (Q : list aev -> machine_state -> Prop) log s s',
  msteps segs s s' -> aruns Q log s' -> aruns Q log s.
Proof. intros. eapply ar_steps; eassumption. Qed.

End Runs.
Arguments aruns segs EVOK GR {fx} Q log s.

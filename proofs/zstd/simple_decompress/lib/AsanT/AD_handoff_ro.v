(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image Mem Cells Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg FsKit AD_handoff0 AZ_globals.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition mbyte_hit (a : Z) (f : mfact) : bool :=
  match f with
  | MZero (ZLit a0) n => (a0 <=? a) && (a <? a0 + n)
  | MZeroC (ZLit a0) n => (0x625000 <=? a0) && (a0 <=? a) && (a <? a0 + n)
  | MCell (ZLit a0) 1 (ZLit _) => Z.eqb a0 a
  | _ => false
  end.
Definition mbyte_val (f : mfact) : option Z :=
  match f with
  | MZero _ _ | MZeroC _ _ => Some 0
  | MCell _ 1 (ZLit v) => Some v
  | _ => None
  end.
Definition mbyteb (l : list mfact) (a : Z) : option Z :=
  match find (mbyte_hit a) l with Some f => mbyte_val f | None => None end.

Lemma mbyteb_some : forall V m l a v, Forall (mfact_ok bsegs V m) l -> 0x625000 <= a < 2^64 ->
  mbyteb l a = Some v -> m (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros V m l a v HF HA HB. unfold mbyteb in HB.
  destruct (find (mbyte_hit a) l) as [f|] eqn:EF; [|discriminate].
  apply find_some in EF as [Hin Hf]. pose proof (proj1 (Forall_forall _ _) HF f Hin) as OK.
  destruct f as [e w x|e n|e w x|e n|e n c|lo hi|e n|e n|e n]; cbn [mbyte_hit mbyte_val] in Hf, HB; try discriminate;
    destruct e; try discriminate; cbn [mfact_ok zv] in OK.
  - (* [comment removed for export] *)
    destruct w as [|[|w]]; try discriminate. destruct x; try discriminate. injection HB as <-.
    apply Z.eqb_eq in Hf. subst z. cbn [cellw zv] in OK. exact (rw_C1_high m a _ OK ltac:(lia)).
  - (* [comment removed for export] *)
    injection HB as <-. apply andb_prop in Hf as [H0 H2]. apply andb_prop in H0 as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    replace a with (z + (a - z)) by lia. apply (zchunk_pointwise m z n OK); lia.
  - (* [comment removed for export] *)
    injection HB as <-. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    specialize (OK (a - z) ltac:(lia)). replace (z + (a - z)) with a in OK by lia. exact OK.
Qed.

(* [comment removed for export] *)
Definition gran_okb (need v : Z) : bool := (0 <=? v) && (v <=? 7) && ((v =? 0) || (need <=? v)).
Definition unp_checkb (l : list mfact) (A n : Z) : bool :=
  forallb (fun k => let G := A / 8 + Z.of_nat k in
                    match mbyteb l (ASHOFF + G) with
                    | Some v => gran_okb (Z.min (8 * G + 8) (A + n) - 8 * G) v
                    | None => false
                    end)
          (seq 0 (Z.to_nat ((A + n - 1) / 8 - A / 8 + 1))).

Lemma unp_of_checkb : forall V m l A n, Forall (mfact_ok bsegs V m) l -> 0 <= A -> 0 < n -> A + n <= 2^40 ->
  unp_checkb l A n = true -> unpoisoned m A (A + n).
Proof.
  intros V m l A n HF H0 H1 H2 HC. split; [lia|]. split; [lia|].
  intros G _ G1 G2.
  set (k := G - A / 8).
  assert (K : 0 <= k <= (A + n - 1) / 8 - A / 8) by (subst k; clear - H0 H1 G1 G2; Z.div_mod_to_equations; lia).
  unfold unp_checkb in HC. rewrite forallb_forall in HC.
  specialize (HC (Z.to_nat k) ltac:(apply in_seq; lia)). cbv beta zeta in HC.
  rewrite Z2Nat.id in HC by lia. replace (A / 8 + k) with G in HC by (subst k; lia).
  destruct (mbyteb l (ASHOFF + G)) as [v|] eqn:EB; [|discriminate].
  assert (GB : 0 <= G /\ G < 2^40) by (clear - H0 H1 H2 G1 G2; lia).
  exists (Z_to_bv 8 v). split.
  - apply (mbyteb_some V m l _ v HF); [unfold ASHOFF; lia | exact EB].
  - unfold gran_okb in HC. apply andb_prop in HC as [HC HD]. apply andb_prop in HC as [HA HB].
    apply Z.leb_le in HA, HB. unfold gran_ok. rewrite (sval_lit v) by lia.
    apply orb_prop in HD as [HD|HD]; [left; apply Z.eqb_eq in HD; exact HD | right; apply Z.leb_le in HD; lia].
Qed.

(* [comment removed for export] *)
Lemma aro_clientM_init : forall V m, Forall (mfact_ok bsegs V m) both_mem_facts -> aro_clientM m.
Proof.
  intros V m HM. split.
  - assert (C : forallb (fun p => unp_checkb both_mem_facts (fst p) (snd p)) ACLIENT_RO = true) by (vm_compute; reflexivity).
    intros A n HIn. rewrite forallb_forall in C. specialize (C (A, n) HIn). cbn [fst snd] in C.
    destruct (aclient_bounds A n HIn) as (B1 & B2 & B3).
    exact (unp_of_checkb V m both_mem_facts A n HM ltac:(lia) ltac:(lia) ltac:(lia) C).
  - mf V m HM (MWr (ZLit 2147459072) 797184) W.
    replace (shad ACLIENT_HLO) with 2147467808 by reflexivity. replace (shad ACLIENT_HHI) with 2147468600 by reflexivity.
    eapply wr_at_sub'; [exact W | lia | lia | lia].
Qed.
End CANSEC1.

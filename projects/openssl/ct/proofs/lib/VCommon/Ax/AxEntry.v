(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxMem AxState AxSys AxEntryRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition stk_max : Z := 8388608.
Definition eb_size : Z := 2238672.

(* [comment removed for export] *)
Definition entry_store (fl : list (lin * (Z * Z))) : store :=
  fold_left (fun s p => sadd s (fst p) (fst (snd p)) (snd (snd p))) fl st_empty.

Lemma sat_fold (ρ : valuation) (fl : list (lin * (Z * Z))) : forall s,
  sat ρ s -> Forall (fun p => fst (snd p) <= leval ρ (fst p) <= snd (snd p)) fl ->
  sat ρ (fold_left (fun s p => sadd s (fst p) (fst (snd p)) (snd (snd p))) fl s).
Proof.
  induction fl as [|p fl IH]; intros s Hs HF; [exact Hs|]. cbn [fold_left].
  apply Forall_cons_iff in HF as [Hp HF]. apply IH; [apply sat_sadd; [exact Hs | exact Hp] | exact HF].
Qed.

Lemma sat_entry_store (ρ : valuation) (fl : list (lin * (Z * Z))) :
  Forall (fun p => fst (snd p) <= leval ρ (fst p) <= snd (snd p)) fl -> sat ρ (entry_store fl).
Proof. intros H. unfold entry_store. apply sat_fold; [apply sat_empty | exact H]. Qed.

(* [comment removed for export] *)
Definition img_region (i : nat) (sg : Segment) : region :=
  Rg [] (wofZ (Z.of_N (seg_base sg))) (of_Z (Z.of_N (seg_size sg))) (KImg (seg_writable sg) i)
     (depth_for (Z.of_N (seg_size sg))) IEmpty.

Fixpoint img_regions_from (i : nat) (segs : list Segment) : list region :=
  match segs with
  | [] => []
  | sg :: r => img_region i sg :: img_regions_from (S i) r
  end.

Definition img_regions (segs : list Segment) : list region := img_regions_from 0 segs.

Definition stk_region : region := zero_rg sp_terms (wofZ (- stk_max)) stk_max.

Definition eb_region (ph : PhdrInfo) : region :=
  Rg sp_terms w_zero (of_Z eb_size) (KEntry ph) (depth_for eb_size) IEmpty.

Definition entry_mem (segs : list Segment) (ph : PhdrInfo) : list region :=
  img_regions segs ++ [stk_region; eb_region ph].

Definition entry_regs : aregs := aset IEmpty 2%uint63 (XS sp_terms w_zero).

Definition brk_form : lin := (0, [(v_b, 4096)]).

Definition entry_model : amodel :=
  AM [] brk_form brk_form None false 100%uint63 (- stk_max, sp_terms) [] [] FDStd.

Definition entry_state (segs : list Segment) (pc : Z) (ph : PhdrInfo) (s : store) : AST :=
  AS (wofZ pc) entry_regs RNone (entry_mem segs ph) s entry_model 0 0.

Lemma entry_out (ρ : valuation) (segs : list Segment) (pc : Z) (ph : PhdrInfo) (s : store) :
  out_val ρ (entry_state segs pc ph s) [].
Proof. reflexivity. Qed.

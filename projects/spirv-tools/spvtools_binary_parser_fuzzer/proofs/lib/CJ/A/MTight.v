(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog MI_Kit MI_List CtxMono MRefuse.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocRep MallocTree MallocFacts_A MallocFacts_AM.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation MR := get_meta_rec.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition TIGHT (cs : mstate) : Prop :=
  forall g b, m_mem (MR cs g) = Some b ->
    let mr := MR cs g in
    m_last_idx mr = 0 /\ m_avail mr = 0 /\ m_freed mr = 0 /\ m_freeable mr = 1
    /\ ((m_sizeclass mr = 63 /\ m_next mr = None /\ m_prev mr = None /\ 0 < m_maplen mr)
        \/ (m_sizeclass mr = 44 /\ m_maplen mr = 17 /\ active cs 44 = Some g /\ m_next mr = Some g /\ m_prev mr = Some g)).

Definition ACT44 (cs : mstate) : Prop :=
  forall j g, active cs j = Some g -> j = 44 /\ m_avail (MR cs g) = 0 /\ m_freed (MR cs g) = 0 /\ m_next (MR cs g) = Some g.

Section REFUSE.
Variables (pb0 cur : Z).

#[local] Notation RR t pb r := (refrun t pb cur = Some r).

Definition same_active_but (h : lhead) (st st' : mstate) : Prop :=
  forall j, LActive j <> h -> active st' j = active st j.

Definition same_active (st st' : mstate) : Prop := forall j, active st' j = active st j.

Definition N44 (st : mstate) : Prop := forall j g, active st j = Some g -> j = 44.

Definition TAOK (st : mstate) (sc : Z) : Prop :=
  active st sc = None
  \/ exists g, active st sc = Some g /\ m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0 /\ m_next (MR st g) = Some g.

Section AG.
Variables (R : Type) (lay : layout_hook).
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis HREC : forall st j req (k : mstate -> Z -> M R) bail pb r,
  N44 st -> j < 44 -> RR (rec st j req k bail) pb r -> exists st' pb', RR (k st' (-1)) pb' r /\ N44 st'.

End AG.

End REFUSE.

Section NOMUNMAP.
Variable cur : Z.
#[local] Notation NM t pb := (nomunmap t pb cur).

Section AMK.
Context {R : Type} (k : mstate -> optr -> M R) (bail : M R).
Hypothesis HK : forall st' mo pb, NM (k st' mo) pb.

End AMK.

Section AGN.
Variables (R : Type) (lay : layout_hook).
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis HREC : forall st j req (k : mstate -> Z -> M R) bail pb, (forall st' x pb', NM (k st' x) pb') -> NM (rec st j req k bail) pb.

End AGN.

End NOMUNMAP.

End AC_1.

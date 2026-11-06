(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.pupnp.FuzzHttp.images Require Plain.
Import ListNotations.
Open Scope Z_scope.

Definition segsP0 : list Segment := Plain.M.loaded_segments.
Definition imgP0 : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.

Definition moP0 (brk mb sp : word) (inp : ProcInput) : Model :=
  init_model (segments_reserved segsP0) brk mb sp source_alloc_limit inp.

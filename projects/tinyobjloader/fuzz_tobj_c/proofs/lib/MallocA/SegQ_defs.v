(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "app"; "bool"; "snd"; "andb"; "fst"; "list"; "nil"; "prod"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ptr_to_compact"; "is_primary"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ag_spacebeg"; "qbatch"; "aa_q_global"; "aa_q_thread"; "qb_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "it_ab"; "it_id"; "qb_id"; "qitems"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "sub"; "@Stdlib.Lists.List"; "filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Model.
Import ListNotations.
Open Scope Z_scope.

Definition qall (A : AA) : list qbatch := ltac2:(tb__ "0|0|
S1SeS10VA;A1SfVA;A1A3").
Definition qitems (l : list qbatch) : list (Z * Z) := flat_map qb_items l.

Definition it_cls (it : Z * Z) : Z := ClassID (needed (snd it)).
Definition it_ab (it : Z * Z) : Z := ltac2:(tb__ "0|0|
S18S5S0S0Vit;A3ScS3S0S0Vit;A3A1A2").
Definition it_id (G : ageom) (it : Z * Z) : Z := ltac2:(tb__ "0|0|
SaSdVG;A1S12Vit;A1S13Vit;A1A3").

Definition qb_id (G : ageom) (b : qbatch) : Z := ltac2:(tb__ "0|0|
SaSdVG;A1Z18S11Vb;A1A3").

Definition q_ids (G : ageom) (l : list qbatch) (c : Z) : list Z := ltac2:(tb__ "0|1|
S1S0S9S8S0S0A2M0S0S14VG;A1S19G0G0S4SbS3S0S0R1A3A1S17S12R1A1Vc;A2A2Lit;S16Vl;A1A3A4S2S6S0A1L_;S17Vc;Z18A2S9SeS0S15VG;A1Vl;A4S7S0A1X2x2A3").

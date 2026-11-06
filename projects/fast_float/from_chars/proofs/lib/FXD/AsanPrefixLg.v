(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import FxMchr AsanPNodes AsanBNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FL60000 : nat := 60000.
Definition LG_SHLO : Z := 0x7fff7000.
Inductive lshape : Type := LS_00 | LS_0M | LS_1M | LS_1X.
Definition ls_r0 (sh : lshape) : bool := match sh with LS_00 | LS_0M => true | _ => false end.
(* [comment removed for export] *)
Definition ls_pg (sh : lshape) : Z := match sh with LS_00 => 2 | _ => 3 end.
(* [comment removed for export] *)
Definition ls_right (sh : lshape) : bool := match sh with LS_0M | LS_1M => true | _ => false end.

Section Lg.
Context {N : Type}.
Notation MC := (@mchain N).
Variable A1n : anode -> MC -> MC.
Variable A2n : anode2 -> MC -> MC.
Variable PNn : pnode -> MC -> MC.
Variable BNn : bnode -> MC -> MC.
Variable KNPUT : MC -> MC.                (* [comment removed for export] *)
Variable P_ENTRY : plan.                  (* [comment removed for export] *)
Variables VR VP VS : positive.
Variable IPRI : nat.                      (* [comment removed for export] *)

Definition STOPS_LG : list Z := [0x44178; 0x44284; 0x73c44; 0x81f88; 0x82914; 0x3febc; 0x44360; 0xd3088; 0x639e0; 0xd2c84; 0x8fe10; 0x61404; 0x615c8].
Definition SEGLG (pc sys : Z) (node : MC -> MC) (k : MC) : MC := MSegK 20 (PRun FL60000 STOPS_LG []) (KCons pc sys (node k) KNil).
Definition KMSLG (k : MC) : MC := MSplitR 11 0 (A1n NMset k) (A1n NMsetC k).
(* [comment removed for export] *)
Definition FL300 : nat := 300.
(* [comment removed for export] *)
Definition KMS0 (k : MC) : MC := MSegK 20 (PRun FL300 [0xd317c] []) (KCons 0xd317c 0 k KNil).
Definition QF (sh : lshape) : lin := match sh with LS_00 => LIN 0 [(VP, 512)] | LS_1X => LIN 511 [(VP, 512)] | _ => LIN 0 [(VP, 512); (VS, 1)] end.
Definition QF' (sh : lshape) : lin := if ls_r0 sh then QF sh else laddc (QF sh) 1.   (* [comment removed for export] *)
Definition MAPZ (sh : lshape) : lin := LIN (4096 * ls_pg sh) [(VP, 4096)].   (* [comment removed for export] *)
Definition MAPSH (sh : lshape) : lin := LIN (512 * ls_pg sh) [(VP, 512)].    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OSLG (sh : lshape) : list lin :=
  [lconst 0; MAPZ sh; laddc (lscale 8 (QF' sh)) 8192; laddc (MAPZ sh) (-8); laddc (lscale 8 (QF' sh)) 6144; laddc (lscale 8 (QF sh)) 6144].
(* [comment removed for export] *)
Fixpoint pbucket_tree (bk : list Z) (leaf : MC) : MC := match bk with [] => leaf | b :: r => MSplit (lvar VP) b leaf (pbucket_tree r leaf) end.
Definition PBK (sh : lshape) : list Z := List.map (fun k => 2 ^ k - ls_pg sh - 1) [5; 6; 7; 8; 9; 10; 11; 12; 13; 14].
Definition KLSTAT (sh : lshape) (k : MC) : MC := SEGLG 0x44178 0 (fun k => MJoinL (pbucket_tree (PBK sh) (SEGLG 0x44284 0 (fun x => x) MEnd)) 0x44284 k) k.
(* [comment removed for export] *)
Definition KM2 (sh : lshape) (k : MC) : MC :=
  if ls_right sh then SEGLG 0xd3088 0 (fun k => BNn (BEqSize 1 (MAPSH sh) 8) (BNn (BSplitW 1 (laddc (QF' sh) 512)) (KMSLG k))) k
  else SEGLG 0xd3088 0 (fun k => BNn (BEqSize 1 (MAPSH sh) 8) (KMS0 k)) k.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KM4 (sh : lshape) (k : MC) : MC :=
  SEGLG 0xd3088 0 (fun k => (if ls_right sh then BNn (BMergeS 1) else (fun x => x)) (BNn (BSplitW 1 (QF' sh)) (KMSLG k))) k.
(* [comment removed for export] *)
Definition KLARGE (sh : lshape) (k : MC) : MC :=
  MSegK 20 P_ENTRY (KCons 0x82914 0 (A1n NUnw
    (SEGLG 0x73c44 222 (fun k => A1n (NNullS GE true true false) (MSplitG 0 (LG_SHLO - 1) (BNn (BPlaceE 0 (OSLG sh)) k) (BNn (BPlaceE 0 (OSLG sh)) k)))
      (MSep (TSepW 0 IPRI) (MSep (TSepW 0 1) (MSep (TSepR 0 0x10000 0x63a000)
        (SEGLG 0xd3088 0 KMSLG (KM2 sh (KLSTAT sh (SEGLG 0x81f88 0 KNPUT (SEGLG 0xd3088 0 KMSLG (KM4 sh
          (SEGLG 0xd3088 0 KMSLG (SEGLG 0xd3088 0 KMSLG (SEGLG 0x61404 0 (fun x => x) k)))))))))))))) KNil).
End Lg.

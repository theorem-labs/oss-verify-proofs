(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcSteps AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnJoinN HarnDev HarnLong HarnLongL HarnJoinM HarnReent HarnBudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hdr_iso (S : sst) : option (list rstep) := isolate_k (laddc (rgk S 10) (-16)) 16 RZ S.
(* [comment removed for export] *)
Definition hdr_b1 (S : sst) : option (nat * Z) := match find_base (s_rgs S) (laddc (rgk S 10) (-16)) 0 with Some i => Some (i, 1) | None => None end.
(* [comment removed for export] *)
Definition CANON (rz : Z) (k : MCH) : MCH :=
  SURG (SSteps hdr_iso) (A2N (NGiveX (if Z.eqb rz 16 then [2%nat] else [0%nat; 3%nat])) (A2N (NExtHull 0 0 1) (NODE (HRB1 hdr_b1) k))).
(* [comment removed for export] *)
Definition GRP (rpc rz : Z) : MCH := SCALE8 (KMALLOCG rpc (CANON rz MEnd)).
(* [comment removed for export] *)
Definition xf_hdr (P : sst) : list fact :=
  match s_rgs P with
  | H :: _ => match tget (okey 1) (rg_cont H) with Some (BV t 0) => [FBits t 3 2; FRange t 0 255] | _ => [] end
  | [] => []
  end.
(* [comment removed for export] *)
Definition genNB := genMH (fun P als => xf_hdr P) hl_budget.
Definition NEWS (rpc : Z) (k : MCH) : MCH :=
  MJoinG genNB (MSplitR 10 48 (GRP rpc 16) (MSplitR 10 96 (GRP rpc 32) (GRP rpc 64))) rpc k.

(* [comment removed for export] *)
Definition STOPS_M4 : list Z := [0x733e8; 0x608f4; 0x60940; 0x60924; 0x60970; 0xb84f4; 0x90688; 0x90678; 0x681cc; 0x683ac; 0x686cc; 0x684ec; 0xd84a4; 0x639e0; 0xd2c84].
Definition SEG4 (pc : Z) (node : MCH -> MCH) (k : MCH) : MCH := MSegK 20 (PRun F60000 STOPS_M4 []) (KCons pc 0 (node k) KNil).
Definition KM4 (k : MCH) : MCH := SEG4 0x608f4 (PN (PQS 4)) (SEG4 0x60940 (XQS 5) (SEG4 0x733e8 (BN BImm) (SEG4 0x90678 (fun x => x) k))).
Definition VOIDOR (k : MCH) : MCH := MAlt MVoid k.
(* [comment removed for export] *)
Definition capform (S : sst) : option lin := match crls_capsum S with Some (l, _) => Some l | None => None end.
Definition XVOID (k : MCH) : MCH := TRY (HIXF capform) (VOIDOR k).
(* [comment removed for export] *)
Definition LONG1 (kx : MCH) : MCH := NEWS 0x90988 (KM4 (MSegK 20 P_BL (KCons 0x90688 0 (LOOPL (XVOID kx)) KNil))).

(* [comment removed for export] *)
Fixpoint planW (k : nat) (stops : list Z) : plan :=
  match k with
  | O => PRun F60000 stops []
  | Datatypes.S k' => let p := planW k' stops in
      PRun F60000 stops [(0x73458, PLoopW 200 [0x73464] [(0x73464, p)]); (0x7348c, PLoopW 200 [0x7349c] [(0x7349c, p)])]
  end.
Definition STOPS_F (rpc : Z) : list Z := [0x43b04; 0x681cc; 0x683ac; 0x686cc; 0x684ec; 0xd84a4; 0x639e0; 0xd2c84; 0x82914; 0x81f88; 0xd3088; rpc].
Definition SEGF (rpc pc : Z) (node : MCH -> MCH) (k : MCH) : MCH := MSegK 20 (planW 3 (STOPS_F rpc)) (KCons pc 0 (node k) KNil).
Definition FREEX (rpc : Z) (k : MCH) : MCH :=
  SEGF rpc 0x82914 (A1N NUnw) (SEGF rpc 0x81f88 (A1N NPut) (SEGF rpc 0xd3088 (A1N NMsetC) (SEGF rpc 0x43b04 (A2N NEnq) (SEGF rpc rpc (fun x => x) k)))).
(* [comment removed for export] *)
Definition STOPS_5 : list Z := [0x608f4; 0x60940; 0x733e8; 0xb84f4; 0x681cc; 0x683ac; 0x686cc; 0x684ec; 0xd84a4; 0x639e0; 0xd2c84].
Definition SEG5 (pc : Z) (node : MCH -> MCH) (k : MCH) : MCH := MSegK 20 (PRun F60000 STOPS_5 []) (KCons pc 0 (node k) KNil).
Definition MOVE_S (k : MCH) : MCH := SEG5 0x608f4 (XQS 4) (SEG5 0x60940 (PN (PQS 5)) (SEG5 0x733e8 (BN BImm) (SEG5 0xb84f4 (fun x => x) k))).
Definition MOVE_H (k : MCH) : MCH := SEG5 0x608f4 (XQS 4) (SEG5 0x60940 (XQS 5) (SEG5 0x733e8 (BN BImm) (SEG5 0xb84f4 (fun x => x) k))).

(* [comment removed for export] *)
Definition STOPS_X (pcS pcH : Z) : list Z := [0x907a0; 0x908dc; pcS; pcH; 0x681cc; 0x683ac; 0x686cc; 0x684ec; 0xd84a4; 0xb84f4; 0x90ab0].
Definition SEGX (pcS pcH pc : Z) (node : MCH -> MCH) (k : MCH) : MCH := MSegK 20 (PRun F60000 (STOPS_X pcS pcH) []) (KCons pc 0 (node k) KNil).
Definition C1PATH (pcS pcH : Z) (kS : MCH) : MCH :=
  SEGX pcS pcH 0x908dc (fun k => k) (MOVE_S (FREEX 0x90ab0 (A2N (NGiveX [0; 1; 2]%nat) (A2N (NExtDrop 0) (SEGX pcS pcH pcS (fun k => k) kS))))).
(* [comment removed for export] *)
Definition C2PATH (pcS pcH : Z) (kH : MCH) : MCH :=
  NEWS 0x909d4 (MOVE_H (FREEX 0x90ab0 (A2N (NGiveX [0; 4; 5]%nat) (A2N (NExtDrop 1) (SEGX pcS pcH pcH (fun k => k) kH))))).
Definition RESTPATH (pcS pcH : Z) (kH : MCH) : MCH :=
  MSegK 20 (PRun F60000 (STOPS_X pcS pcH) []) (KCons pcH 0 kH (KCons 0x908dc 0 (SEGX pcS pcH 0xd84a4 (fun k => k) (C2PATH pcS pcH kH)) KNil)).
(* [comment removed for export] *)
Definition K23PATH (pcS pcH : Z) (kH : MCH) : MCH := SEGX pcS pcH 0x908dc (fun k => k) MEnd.
Definition K_EXIT (pcS pcH : Z) (kS kH : MCH) : MCH :=
  SIZEDEC (CAPSUM (SEGX pcS pcH 0x907a0 (fun k => k)
    (MSplitR 10 22 (C1PATH pcS pcH kS) (MSplitR 10 23 (K23PATH pcS pcH kH) (RESTPATH pcS pcH kH))))).
(* [comment removed for export] *)
Definition LONGB (pcS pcH : Z) (kS kH : MCH) : MCH :=
  NEWS 0x90988 (KM4 (MSegK 20 P_BL (KCons 0x90688 0 (LOOPL (XVOID (K_EXIT pcS pcH kS kH))) KNil))).

(* [comment removed for export] *)
Definition NAMEDECT (r : Z) (k : MCH) : MCH := TRY (HNAMER (reg_key r)) (TRY (HFSUM (namer_sum r)) (TRY (HDECV (reg_dec r)) k)).
Definition P_LGN : plan := PRun F60000 [0xd84a4; 0x61d38; 0x681cc; 0x683ac; 0x686cc; 0x8fe64] [].
Definition KLONG (pcS pcH : Z) (kS kH : MCH) : MCH := NAMEDECT 11 (MSegK 20 P_LGN (KCons 0xd84a4 0 (LONGB pcS pcH kS kH) KNil)).

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
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnKind HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnJoinN HarnJoinM HarnReent HarnBudget HarnDev HarnLong HarnLongL HarnCR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition INIT_FLAG : Z := 0x174848.   Definition INIT_W0 : Z := 0x126D80.   Definition INIT_W1 : Z := 0x126D88.
Definition INITPREP (k : MCH) : MCH :=
  TRY (HRBK (fun S => at_c S (lconst INIT_FLAG) 4)) (TRY (HRBK (fun S => at_c S (lconst INIT_W0) 8)) (TRY (HRBK (fun S => at_c S (lconst INIT_W1) 8)) k)).
(* [comment removed for export] *)
Definition flag_var (S : sst) : option positive :=
  match at_c S (lconst INIT_FLAG) 4 with
  | Some (i, o, _) => match nth_error (s_rgs S) i with
                      | Some R => match tget (okey o) (rg_cont R) with Some (BV (LIN 0 [(x, 1)]) 0) => Some x | _ => None end
                      | None => None
                      end
  | None => None
  end.
(* [comment removed for export] *)
Definition QC : Z := 1048576.
Fixpoint pri_pos (l : list lin) (i : nat) : option nat :=
  match l with
  | x :: ((y :: _) as t) => match ldivz x 8 with
                            | Some x8 => if lin_eqb y (laddc x8 2147450880) then Some i else pri_pos t (S i)
                            | None => pri_pos t (S i)
                            end
  | _ => None
  end.
(* [comment removed for export] *)
Definition xf_prov (P : sst) : list fact :=
  List.flat_map (fun pv => match find_cell (s_rgs P) pv, find_cell (s_rgs P) (laddc pv 8) with
                           | Some (_, _, dp), Some (_, _, rm) => [FRange (lsub dp (pg_P G1)) 0 PAY_HI; FRange rm 0 (PAY_HI - 1)]
                           | _, _ => []
                           end) [rget (s_regs P) (rk 9); laddc (rget (s_regs P) (rk 9)) 48].
Definition xf_hist (P : sst) (als : list lin) : list fact :=
  xf_prov P ++
  match pri_pos als O with
  | Some p => let QN := nth (p + 66) als (lconst 0) in let QB := nth (p + 67) als (lconst 0) in let J24 := nth (p + 51) als (lconst 0) in
              (* [comment removed for export] *)
              FRange (lsub (lscale QC QN) QB) 0 (QC * 1021) ::
              (* [comment removed for export] *)
              List.flat_map (fun f => match f with
                                      | FRange (LIN 1 [(x, a); (y, b)]) 0 _ =>
                                          if (Z.eqb a 18446744073709551615 && Z.eqb b 1023)%bool then [FRange (laddc (ladd (lscale 18446744073709551615 (lvar x)) (lscale 1023 J24)) 1) 0 1099511627776]
                                          else if (Z.eqb b 18446744073709551615 && Z.eqb a 1023)%bool then [FRange (laddc (ladd (lscale 18446744073709551615 (lvar y)) (lscale 1023 J24)) 1) 0 1099511627776]
                                          else []
                                      | _ => [] end) (List.firstn 1 (List.filter (fun f => match f with FRange (LIN 1 [(_, a); (_, b)]) 0 _ => ((Z.eqb a 18446744073709551615 && Z.eqb b 1023) || (Z.eqb b 18446744073709551615 && Z.eqb a 1023))%bool | _ => false end) (s_facts P))) ++
              (let ks := List.flat_map (fun f => match f with
                                                 | FRange (LIN K [(_, a); (_, b)]) 0 1048576 =>
                                                     if ((Z.eqb a 1 && Z.eqb b 18446744073709551615) || (Z.eqb b 1 && Z.eqb a 18446744073709551615))%bool && Z.leb 1 K && Z.leb K 64 then [K] else []
                                                 | _ => [] end) (s_facts P) in
               List.map (fun K => FRange (laddc (lsub QN J24) K) 0 1048576) (match ks with [] => [1; 2; 4; 8; 16] | _ => ks end))
  | None => []
  end.
(* [comment removed for export] *)
Definition genF0 := genM xf_hist.
Definition genF := genMH xf_hist hl_budget.      (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS_G : list Z := [0x6d990; 0x73440; 0x6da64; 0x681cc; 0x683ac; 0x686cc; 0x684ec; 0xd84a4; 0x639e0; 0xd2c84].
Fixpoint INITSEG (n : nat) : MCH :=
  match n with
  | O => MSegK 20 (PRun F60000 STOPS_G []) (KCons 0x6da64 0 (INITPREP MEnd) KNil)
  | Datatypes.S n' => MSegK 20 (PRun F60000 STOPS_G []) (KCons 0x73440 0 (BN BIms (INITSEG n')) (KCons 0x6da64 0 (INITPREP MEnd) KNil))
  end.
Definition GETTER : MCH :=
  MSegK 20 (PRun F60000 STOPS_G [])
    (KCons 0x6d990 0 (MConcR (INITSEG 4))
    (KCons 0x6da64 0 (INITPREP MEnd) KNil)).
(* [comment removed for export] *)
Definition r42 (S : sst) : lin := rget (s_regs S) 42%positive.
Definition r43 (S : sst) : lin := rget (s_regs S) 43%positive.
Definition ENQ (k : MCH) : MCH :=
  A3N (NPsr 66) (NODE (HPSRK 43 (fun S => Some (r42 S)))
  (MSplitR 41 0
     (A3N (NPsr 67) (MSplitR 41 0
        (A3N (NPsr 51) (MSplitR 41 0 (A2N NEnq k) (A2N NEnq k)))
        (TRY (HIXF (fun S => Some (lsub (lscale QC (r43 S)) (r42 S)))) (MAlt MVoid (A2N NEnq k)))))
     (A2N NEnq k))).
(* [comment removed for export] *)
Definition sh_ab_at (P : lin) (S : sst) : option (nat * nat) :=
  let sh := oshadow P in
  match find_base (s_rgs S) sh 0, find_base (s_rgs S) (laddc sh 3) 0 with
  | Some iA, Some iB =>
      match nth_error (s_rgs S) iA, nth_error (s_rgs S) iB with
      | Some A, Some B => if (lin_eqb (rg_size A) (lconst 3) && lin_eqb (rg_size B) (lconst 1))%bool then Some (iA, iB) else None
      | _, _ => None
      end
  | _, _ => None
  end.
Definition sh_drop_at (P : sst -> lin) (S : sst) : option (list rstep) := match sh_ab_at (P S) S with Some (iA, iB) => Some [RDrop iA; RDrop iB] | None => None end.
Definition sh_mrg_at (P : sst -> lin) (S : sst) : option (nat * nat) :=
  match sh_ab_at (P S) S with Some (iA, iB) => if Nat.eqb iB (Datatypes.S iA) then Some (iA, 2%nat) else None | None => None end.
Definition SHMERGE_AT (P : sst -> lin) (k : MCH) : MCH := TRY (HSURG (SSteps (sh_drop_at P))) (TRY (HSURG (SMerge (sh_mrg_at P))) k).
(* [comment removed for export] *)
Definition genFS := genF.
Definition FREEX2 (rpc : Z) (k : MCH) : MCH :=
  SHMERGE_AT (fun S => rgk S 10)
  (MJoinG genFS
    (MJoinG genF GETTER 0x6da64
       (SEGF rpc 0x82914 (A1N NUnw) (SEGF rpc 0x81f88 (A1N NPut) (SEGF rpc 0xd3088 (A1N NMsetC) (SEGF rpc 0x43b04 ENQ (SEGF rpc rpc (fun x => x) MEnd))))))
    rpc k).

(* [comment removed for export] *)
Definition k23_merge (S : sst) : option (nat * nat) :=
  match find_base (s_rgs S) (rgk S 10) 0, find_base (s_rgs S) (laddc (rgk S 10) 26) 0 with
  | Some i, Some j => if Nat.eqb j (Datatypes.S i) then Some (i, 2%nat) else None
  | _, _ => None
  end.
Definition hdr_n (S : sst) : option (nat * Z * nat) := match find_base (s_rgs S) (laddc (rgk S 10) (-16)) 0 with Some i => Some (i, 4, 4%nat) | None => None end.
Definition CANONK (rz : Z) (k : MCH) : MCH :=
  SURG (SSteps hdr_iso) (TRY (HSURG (SMerge k23_merge))
    (A2N (NGiveX (if Z.eqb rz 16 then [2%nat] else [0%nat; 3%nat])) (A2N (NExtHull 0 0 1) (NODE (HRB1 hdr_b1) (TRY (HRBK hdr_n) k))))).
Definition GRPK (rpc rz : Z) : MCH := SCALE8 (KMALLOCG rpc (CANONK rz MEnd)).
Definition NEWSK (rpc : Z) (k : MCH) : MCH :=
  MJoinG genNB (MSplitR 10 48 (GRPK rpc 16) (MSplitR 10 96 (GRPK rpc 32) (GRPK rpc 64))) rpc k.
(* [comment removed for export] *)
Definition VOIDREQ (k : MCH) : MCH := TRY (HIXF (fun S => Some (rgk S 10))) (MAlt MVoid k).

(* [comment removed for export] *)
Definition C1PATH2 (pcS pcH : Z) (kS : MCH) : MCH :=
  SEGX pcS pcH 0x908dc (fun k => k) (MOVE_S (FREEX2 0x90ab0 (A2N (NGiveX [0; 1; 2]%nat) (A2N (NExtDrop 0) (SEGX pcS pcH pcS (fun k => k) kS))))).
Definition C2PATH2 (pcS pcH : Z) (kH : MCH) : MCH :=
  NEWSK 0x909d4 (MOVE_H (FREEX2 0x90ab0 (A2N (NGiveX [0; 4; 5]%nat) (A2N (NExtDrop 1) (SEGX pcS pcH pcH (fun k => k) kH))))).
Definition RESTPATH2 (pcS pcH : Z) (kH : MCH) : MCH :=
  MSegK 20 (PRun F60000 (STOPS_X pcS pcH) []) (KCons pcH 0 kH (KCons 0x908dc 0 (SEGX pcS pcH 0xd84a4 VOIDREQ (C2PATH2 pcS pcH kH)) KNil)).
Definition C2PATHK (pcS pcH : Z) (kH : MCH) : MCH :=
  NEWSK 0x909d4 (MOVE_H (FREEX2 0x90ab0 (A2N (NGiveX [0; 5; 6]%nat) (A2N (NExtDrop 1) (SEGX pcS pcH pcH (fun k => k) kH))))).
Definition K23PATH2 (pcS pcH : Z) (kH : MCH) : MCH :=
  MSegK 20 (PRun F60000 (STOPS_X pcS pcH) []) (KCons pcH 0 kH (KCons 0x908dc 0 (SEGX pcS pcH 0xd84a4 VOIDREQ (C2PATHK pcS pcH kH)) KNil)).
Definition K_EXIT2 (pcS pcH : Z) (kS kH : MCH) : MCH :=
  SIZEDEC (CAPSUM (SEGX pcS pcH 0x907a0 (fun k => k)
    (MSplitR 10 22 (C1PATH2 pcS pcH kS) (MSplitR 10 23 (K23PATH2 pcS pcH kH) (RESTPATH2 pcS pcH kH))))).
Definition LONGB2 (pcS pcH : Z) (kS kH : MCH) : MCH :=
  NEWSK 0x90988 (KM4 (MSegK 20 P_BL (KCons 0x90688 0 (LOOPL (XVOID (K_EXIT2 pcS pcH kS kH))) KNil))).
Definition KLONG2 (pcS pcH : Z) (kS kH : MCH) : MCH := NAMEDECT 11 (MSegK 20 P_LGN (KCons 0xd84a4 0 (LONGB2 pcS pcH kS kH) KNil)).

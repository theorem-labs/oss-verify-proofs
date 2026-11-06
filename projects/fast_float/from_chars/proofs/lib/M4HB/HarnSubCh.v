(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxMem FxRgs FxFacts FxSubst FxEnt FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcSteps AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HarnKind HxSurg HarnFam HarnLoop HarnSite HarnFk AcFam3 HarnChain HarnJoin HarnJoinN HarnJoinM HarnReent HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23 HarnS HarnSub HarnCls0 HarnBudget HarnPost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition PC0 : Z := 0x90a7c.   Definition PC_S : Z := 0x90ab4.   Definition PC_H : Z := 0x90ab8.
Definition tgt (S : sst) : lin := rgk S 24.
(* [comment removed for export] *)
Definition heap_ptr (S : sst) : option lin :=
  match find_cell (s_rgs S) (laddc (tgt S) 16) with
  | Some (_, _, p) => match find_base (s_rgs S) p 0 with Some _ => Some p | None => None end
  | None => None
  end.
Definition probe_heap (S : sst) : option (list rstep) := match heap_ptr S with Some _ => Some [] | None => None end.
Definition probe_26 (S : sst) : option (list rstep) :=
  match heap_ptr S with Some p => match sh_ab_at p S with Some _ => Some [] | None => None end | None => None end.
Definition SEGE (pc : Z) : MCH := MSegK 20 (PRun F60000 [pc] []) (KCons pc 0 MEnd KNil).
Definition FINK : MCH := MAlt (SURG (SSteps probe_26) MEnd) (MAlt (SURG (SSteps probe_heap) (SEGE PC_H)) (SEGE PC_S)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MSQB (stops : list Z) (k : MCH) : MCH :=
  let P := PRun F60000 (stops ++ [PC_SM0_CALL; PC_SM0_RET; 0x606a4]) [] in
  MSegK 20 P (KCons PC_SM0_CALL 0 (SM0 P (MSQ stops k)) KNil).
(* [comment removed for export] *)
Definition RETH (pc : Z) (k : MCH) : MCH := EXIT0 (MSegK 20 (PRun F60000 [pc] []) (KCons pc 0 k KNil)).
Definition RET0 (k : MCH) : MCH := RETH PC0 k.
Definition MS0 (k : MCH) : MCH := MSQB [] k.    (* [comment removed for export] *)
Definition CRLS_BODY : MCH := MS0 (MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (SSOBR PC0 PC0 FINK) (KLONG2 PC0 PC0 FINK FINK)) KNil)).
Definition CRLS_SUB : MCH := MJoinG genF (MJoinG genF (MJoinG genF CRLS_BODY PC0 MEnd) PC_S MEnd) PC_H MEnd.

(* [comment removed for export] *)
Definition SEG5L (pc : Z) (node : MCH -> MCH) (k : MCH) : MCH := MSegK 20 (PRun F60000 STOPS_5 []) (KCons pc 0 (node k) KNil).
Definition MOVE_H2 (k : MCH) : MCH :=
  MJoinG genF
    (MSegK 20 (PRun F60000 STOPS_5 [])
       (KCons 0x608e8 0 (XQS 4 (SEG5L 0x60934 (XQS 5) (SEG5L 0x733dc (fun x => x) MEnd)))
       (KCons 0x639d4 0 (PN PRP (SEG5L 0x639d4 (PN PRP) (SEG5L 0x733dc (fun x => x) MEnd))) KNil)))
    0x733dc (BN BImm (SEG5L 0xb9d70 (fun x => x) k)).
Definition C2PATH3 (pcS pcH : Z) (kH : MCH) : MCH :=
  NEWSK 0x90d0c (MOVE_H2 (FREEX2 0x90de8 (A2N (NGiveX [0; 4; 5]%nat) (A2N (NExtDrop 1) (SEGX pcS pcH pcH (fun k => k) kH))))).
(* [comment removed for export] *)
Definition var_c (c : Z) (l : lin) : option positive := match List.filter (fun '(_, k) => Z.eqb k c) (l_t l) with [(x, _)] => Some x | _ => None end.
Definition growsum (S : sst) : option (lin * lin) :=
  match cell S (rgk S 24), cell S (laddc (rgk S 24) 8) with
  | Some w0, Some k => match var_c 1 k with Some b => Some (laddc (lsub (laddc w0 (-2)) k) 113, lvar b) | None => None end
  | _, _ => None
  end.
Definition growscl (S : sst) : option (lin * Z) :=
  match cell S (rgk S 24), cell S (laddc (rgk S 24) 8) with
  | Some w0, Some k => match var_c 8 w0, var_c 8 k with Some q, Some a => Some (laddc (lsub (lvar q) (lvar a)) 15, 3) | _, _ => None end
  | _, _ => None
  end.
Definition GROWFIX (k : MCH) : MCH := TRY (HFSUM growsum) (TRY (HSCL growscl) k).
Definition RESTPATH3 (pcS pcH : Z) (kH : MCH) : MCH :=
  MSegK 20 (PRun F60000 (STOPS_X pcS pcH) []) (KCons pcH 0 kH (KCons 0x90c14 0 (SEGX pcS pcH 0xd9d20 VOIDREQ (C2PATH3 pcS pcH kH)) KNil)).
(* [comment removed for export] *)
Definition capword (S : sst) : option lin := cell S (rgk S 24).
(* [comment removed for export] *)
Definition capsum2 (S : sst) : option (lin * lin) :=
  match cell S (rgk S 24), cell S (laddc (rgk S 24) 8), cell S (laddc (rgk S 20) 8) with
  | Some w0, Some k, Some rc => Some (lsub (laddc w0 (-2)) (ladd k rc), rc)
  | _, _, _ => None
  end.
Definition CAPSUM2 (k : MCH) : MCH := TRY (HFSUM capsum2) k.
Definition K_EXIT3 (pcS pcH : Z) (kS kH : MCH) : MCH :=
  TRY (HIXF capword) (SIZEDEC (CAPSUM (CAPSUM2 (GROWFIX (SEGX pcS pcH 0x909cc (fun k => k)
    (MSplitR 10 22 (C1PATH2 pcS pcH kS) (MSplitR 10 23 (K23PATH2 pcS pcH kH) (RESTPATH3 pcS pcH kH)))))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition remform (S : sst) : option lin := cell S (laddc (rgk S 20) 8).
(* [comment removed for export] *)
Definition xf_cap (P : sst) : list fact :=
  match cell P (rgk P 24), cell P (laddc (rgk P 24) 8), cell P (laddc (rgk P 20) 8) with
  | Some w0, Some k, Some rc => [FRange (lsub (laddc w0 (-2)) (ladd k rc)) 0 (PAY_HI + 466)]
  | _, _, _ => []
  end.
Definition genFC := genM (fun P als => xf_hist P als ++ xf_cap P).
Definition LONGB3 (pcS pcH : Z) (kS kH : MCH) : MCH :=
  NEWSK 0x90cc0 (KM4 (MSegK 20 P_BL (KCons 0x90898 0 (TRY (HIXF remform) (MJoinG genFC (LOOPL (XVOID MEnd)) 0x90968 (K_EXIT3 pcS pcH kS kH))) KNil))).
(* [comment removed for export] *)
Definition NAMEDECK (r : Z) (k : MCH) : MCH := NODE (HNAMER (fun _ => Some (rk r))) (TRY (HFSUM (namer_sum r)) (TRY (HDECV (reg_dec r)) k)).
Definition KLONG3 (pcS pcH : Z) (kS kH : MCH) : MCH := NAMEDECK 11 (MSegK 20 P_LGN (KCons 0xd9d20 0 (LONGB3 pcS pcH kS kH) KNil)).
Definition CRLS_BODY3 : MCH := MS0 (MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (SSOBR PC0 PC0 FINK) (KLONG3 PC0 PC0 FINK FINK)) KNil)).
Definition CRLS_SUB3 : MCH := MJoinG genF (MJoinG genF (MJoinG genF CRLS_BODY3 PC0 MEnd) PC_S MEnd) PC_H MEnd.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition obj_ioA (a : sst -> lin) (S : sst) : option (nat * Z) := find_idx (s_rgs S) (a S) 0.
Definition b0_linA (a : sst -> lin) (S : sst) : option lin :=
  match obj_ioA a S with
  | Some (i, o) => match nth_error (s_rgs S) i with
                   | Some R => match Prelude.tget (okey o) (rg_cont R) with Some (BV l 0) => Some l | _ => None end
                   | None => None
                   end
  | None => None
  end.
Definition halfxA (a : sst -> lin) (b : Z) (S : sst) : option lin := match b0_linA a S with Some l => FxEnt.ldivz (laddc l (- b)) 2 | None => None end.
(* [comment removed for export] *)
Definition par_cellA (a : sst -> lin) (b : Z) (S : sst) : option (nat * Z * lin) :=
  match obj_ioA a S with Some (i, o) => Some (i, o, laddc (lscale 2 (lvar (v_last S))) b) | None => None end.
Definition PARREP_SA (a : sst -> lin) (k : MCH) : MCH := NODE (HNAMEL (halfxA a 0)) (NODE (HREPL1 (par_cellA a 0)) k).
Definition PARREP_HA (a : sst -> lin) (k : MCH) : MCH := NODE (HNAMEL (halfxA a 1)) (NODE (HREPL (par_cellA a 1)) k).
Definition cap_wA (a : sst -> lin) (S : sst) : option (nat * Z * nat) := match obj_ioA a S with Some (i, o) => Some (i, o, 8%nat) | None => None end.
(* [comment removed for export] *)
Definition ksum (a : sst -> lin) (S : sst) : option (lin * lin) :=
  match cell S (laddc (a S) 16), cell S (laddc (a S) 8) with
  | Some p, Some k => match find_base (s_rgs S) p 0 with
                      | Some j => match nth_error (s_rgs S) j with Some U => Some (laddc (lsub (rg_size U) k) (-1), lsub k (lvar (v_last S))) | None => None end
                      | None => None end
  | _, _ => None
  end.
Definition kcell (a : sst -> lin) (S : sst) : option (nat * Z * lin) := match obj_ioA a S with Some (i, o) => Some (i, o + 8, lvar (v_last S)) | None => None end.
Definition KNAME (a : sst -> lin) (k : MCH) : MCH := NODE (HNAMEL (fun S => cell S (laddc (a S) 8))) (TRY (HFSUM (ksum a)) (NODE (HREPL (kcell a)) k)).
Definition FINK3A (a : sst -> lin) : MCH :=
  MAlt (SURG (SSteps probe_26) (TRY (HRBK (cap_wA a)) (PARREP_HA a MEnd)))
       (MAlt (SURG (SSteps probe_heap) (TRY (HRBK (cap_wA a)) (KNAME a (PARREP_HA a (SEGE PC_H))))) (PARREP_SA a (SEGE PC_S))).
Definition FINK3 : MCH := FINK3A tgt.
Definition CRLS_BODY4 : MCH := MS0 (MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (SSOBR PC0 PC0 FINK3) (KLONG3 PC0 PC0 FINK3 FINK3)) KNil)).
(* [comment removed for export] *)
Definition xf_fin (P : sst) : list fact :=
  List.flat_map (fun R => match is_const (rg_size R) with
                          | Some 32 => match cell P (laddc (rg_base R) 16), cell P (laddc (rg_base R) 8) with
                                       | Some p, Some k => match find_base (s_rgs P) p 0 with
                                                           | Some j => match nth_error (s_rgs P) j with
                                                                       | Some U => FRange (laddc (lsub (rg_size U) k) (-1)) 0 200 ::
                                                                                   (* [comment removed for export] *)
                                                                                   match find_base (s_rgs P) (oshadow p) 0 with
                                                                                   | Some js => match nth_error (s_rgs P) js with Some A => [FRange (lsub (lscale 8 (rg_size A)) k) 1 256] | None => [] end
                                                                                   | None => [] end
                                                                       | None => [] end
                                                           | None => [] end
                                       | _, _ => [] end
                          | _ => [] end) (s_rgs P).
Definition genFF := genM (fun P als => xf_hist P als ++ xf_fin P).
Definition CRLS_SUB4 : MCH := MJoinG genFF (MJoinG genFF (MJoinG genFF CRLS_BODY4 PC0 MEnd) PC_S MEnd) PC_H MEnd.

(* [comment removed for export] *)
Definition fdp_cur (S : sst) : option lin := cell S (rgk S 20).
Definition fdp_sum (S : sst) : option (lin * lin) :=
  match cell S (rgk S 20), cell S (laddc (rgk S 20) 8) with Some c, Some r => Some (r, lsub c (lvar (v_last S))) | _, _ => None end.
Definition fdp_c1 (S : sst) : option (nat * Z * lin) :=
  match find_idx (s_rgs S) (rgk S 20) 0, cell S (rgk S 20), cell S (laddc (rgk S 20) 8) with
  | Some (i, o), Some c, Some r => Some (i, o + 8, lsub (ladd c r) (lvar (v_last S)))
  | _, _, _ => None
  end.
Definition fdp_c0 (S : sst) : option (nat * Z * lin) := match find_idx (s_rgs S) (rgk S 20) 0 with Some (i, o) => Some (i, o, lvar (v_last S)) | None => None end.
Definition FDPNAME (k : MCH) : MCH := NODE (HNAMEL fdp_cur) (TRY (HFSUM fdp_sum) (NODE (HREPL fdp_c1) (NODE (HREPL fdp_c0) k))).
Definition FINK5 : MCH := FDPNAME (STATNAME FINK3).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition genF2 := genMH xf_hist hl_budget.
Definition genFC2 := genMH (fun P als => xf_hist P als ++ xf_cap P) hl_budget.
Definition SSOBR5 (pcS pcH : Z) (kS : MCH) : MCH :=
  MJoinG genF2 (MSegK 20 P_B (KCons 0x90898 0 (LOOP0V MEnd) KNil)) 0x90968 (SEGX pcS pcH pcS (fun k => k) kS).
Definition LONGB5 (pcS pcH : Z) (kS kH : MCH) : MCH :=
  NEWSK 0x90cc0 (KM4 (MSegK 20 P_BL (KCons 0x90898 0 (TRY (HIXF remform) (MJoinG genFC2 (LOOPL (XVOID MEnd)) 0x90968 (K_EXIT3 pcS pcH kS kH))) KNil))).
Definition KLONG5 (pcS pcH : Z) (kS kH : MCH) : MCH := NAMEDECK 11 (MSegK 20 P_LGN (KCons 0xd9d20 0 (LONGB5 pcS pcH kS kH) KNil)).
Definition CRLS_BODY5 : MCH := MS0 (MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (SSOBR5 PC_RETIRE0 PC_RETIRE0 (RET0 FINK5)) (KLONG5 PC_RETIRE0 PC_RETIRE0 (RET0 FINK5) (RET0 FINK5))) KNil)).
Section RE.
  Variable (nb : positive) (T : sst) (alsT : list lin) (nfix : nat).
  Definition uvar : positive := match l_t (rget (s_regs T) HarnBudget.UKEY) with [(v, _)] => v | _ => 1%positive end.
  Definition genRF := gclean nb (genREU nb T alsT nfix uvar (fun P als => xf_hist P als ++ xf_fin P) HarnBudget.hl_budget).
  Definition CRLS_SUB5 : MCH := MJoinG genRF (MJoinG genRF (MJoinG genRF CRLS_BODY5 PC0 MEnd) PC_S MEnd) PC_H MEnd.
End RE.

(* [comment removed for export] *)
Definition genK (F : sst) (MF : smodel) (als : list lin) : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin) := fun _ _ => Some (F, MF, als).
Definition CRLS_SUB5K (g0 gS gH : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) : MCH :=
  MJoinG gH (MJoinG gS (MJoinG g0 CRLS_BODY5 PC0 MEnd) PC_S MEnd) PC_H MEnd.

(* [comment removed for export] *)
Definition ncache_of (S : sst) (M : smodel) (a : ast) : nat :=
  match AACB.AcCache.apost_cacheadd S M a with
  | Some (_, _, a') => (List.length (a_live a') - List.length (a_live a))%nat
  | None => O
  end.
(* [comment removed for export] *)
Definition FINK6 (n : nat) : MCH := A3N (NCacheDrop n) (NODE (HFSUML sel_all) (NODE (HFSUML sel_all) FINK5)).
Definition CRLS_BODY6 (n : nat) : MCH :=
  A3N NCacheAdd (MS0 (MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (SSOBR5 PC_RETIRE0 PC_RETIRE0 (RET0 (FINK6 n))) (KLONG5 PC_RETIRE0 PC_RETIRE0 (RET0 (FINK6 n)) (RET0 (FINK6 n)))) KNil))).
Section RE6.
  Variable (nb : positive) (T : sst) (alsT : list lin) (nfix : nat) (n : nat).
  Definition CRLS_SUB6 : MCH := MJoinG (genRF nb T alsT nfix) (MJoinG (genRF nb T alsT nfix) (MJoinG (genRF nb T alsT nfix) (CRLS_BODY6 n) PC0 MEnd) PC_S MEnd) PC_H MEnd.
End RE6.
Definition CRLS_SUB6K (n : nat) (g0 gS gH : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) : MCH :=
  MJoinG gH (MJoinG gS (MJoinG g0 (CRLS_BODY6 n) PC0 MEnd) PC_S MEnd) PC_H MEnd.
(* [comment removed for export] *)

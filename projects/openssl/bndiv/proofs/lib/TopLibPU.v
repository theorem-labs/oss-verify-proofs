(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling Image Stage.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Rnd Lib_iface Driver_iface Impl_closed.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Lib_iface Driver_iface Impl_closed.
From OSSVerify.openssl.bndiv.images Require Plain.
From OSSVerify.openssl.bndiv.images Require Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module PL := OSSVerify.Proofs.openssl.bndiv.lib.P.Lib_iface.
Module PD := OSSVerify.Proofs.openssl.bndiv.lib.P.Driver_iface.
Module UL := OSSVerify.Proofs.openssl.bndiv.lib.U.Lib_iface.
Module UD := OSSVerify.Proofs.openssl.bndiv.lib.U.Driver_iface.
Notation RunRnd := OSSVerify.Proofs.openssl.bndiv.lib.P.Rnd.RunRnd.

Section Assembly.
  Context {LM : LibModel}.
  (* [comment removed for export] *)
  Variable Pc : Z -> Z.
  Variable T : list Z.
  Variables NBLK BSZ : Z.
  Variable linv : LS -> list (bptr * Z) -> Prop.
  Hypothesis HP0 : forall c, 0 <= Pc c.
  Hypothesis HC : caps_ok Pc T NBLK BSZ.
  Hypothesis H_init : lwf (okT T) lib_init [] (fun ls Li => linv ls [] /\ subms (map snd Li) T).
  Hypothesis H_one : forall ls d X, linv ls X -> zlength d <= MAX_INPUT ->
                     lwf (okB NBLK BSZ) (lib_one ls d) X (fun r X' => linv (fst r) X').
  Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

  (* [comment removed for export] *)
  Variable LSPp : forall (CE__ : Ceiling) (RN__ : RunRnd), @PL.LibSpec LM.
  Hypothesis LLp : forall (CE__ : Ceiling) (RN__ : RunRnd), @PD.LibLaws LM (LSPp CE__ RN__).
  Hypothesis INITp : forall (CE__ : Ceiling) (RN__ : RunRnd), @PL.rinit_stmt CE__ RN__ LM (LSPp CE__ RN__).
  Hypothesis FUZZp : forall (CE__ : Ceiling) (RN__ : RunRnd), @PL.rfuzz_one_stmt CE__ RN__ LM (LSPp CE__ RN__).

  (* [comment removed for export] *)
  Variable LSPu : forall (CE__ : Ceiling) (RN__ : RunRnd), @UL.LibSpec LM.
  Hypothesis LLu : forall (CE__ : Ceiling) (RN__ : RunRnd), @UD.LibLaws LM (LSPu CE__ RN__).
  Hypothesis INITu : forall (CE__ : Ceiling) (RN__ : RunRnd), @UL.rinit_stmt CE__ RN__ LM (LSPu CE__ RN__).
  Hypothesis FUZZu : forall (CE__ : Ceiling) (RN__ : RunRnd), @UL.rfuzz_one_stmt CE__ RN__ LM (LSPu CE__ RN__).

  Theorem base_bndiv_ubsan_of_lib :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
  Proof.
    exact (baseG_scfg_budgets Pc T NBLK BSZ linv HP0 HC H_init H_one H_rc
             psegs _ _ pstage usegs _ _ ustage image_low_psegs image_low_usegs
             (P.Impl_closed.implG_P_stmt_closed LM LSPp LLp INITp FUZZp)
             (U.Impl_closed.implG_U_stmt_closed LM LSPu LLu INITu FUZZu)).
  Qed.
End Assembly.

(* [comment removed for export] *)

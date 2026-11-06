(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcFam AcSubst AcPri AcConvA AcNPop AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2 AcFam3 AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSubst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam3 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMNode AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBNodes AsanPrefixG AsanPrefixLg AsanPrefixGL AsanBodyFam AsanTailCh AsanBodyCh.

Module AsanBodyChH.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanBodyE AsanTailCh AsanBodyCh.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BodyChH.
Context {N : Type}.
Notation MC := (@mchain N).
Variable HARN : MC -> MC.                  (* [comment removed for export] *)
Variable HARN1 : MC -> MC.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TH_WBL1 : MC := MWritevL 1 T_F0W T_F1W (MSegK 20 PT_RETRY2 (KCons 0xcbc18 0 (MPop MEnd) (KCons 0xcbcd4 0 MVoid KNil))).
Definition TH_KWL (k : MC) : MC :=
  MJoin (MWritevL 1 T_F0W T_F1W (MSegK 20 PT_RETRY2 (KCons 0xcbc94 66 TH_WBL1 (KCons 0xcbc18 0 (MPop MEnd) KNil)))) 0xcbc18 k.
(* [comment removed for export] *)
Definition TH_WBF1 : MC := MWritev2 (lconst 0x639f50) (MSegK 20 PT_RETRY (KCons 0xcbc18 0 (MPop MEnd) KNil)).
Definition TH_KWF (n : nat) (k : MC) : MC :=
  match n with
  | Datatypes.S (Datatypes.S O) => MJoin (MWritev2 (lconst 0x639f50) (MSegK 20 PT_RETRY (KCons 0xcbc94 66 TH_WBF1 (KCons 0xcbc18 0 (MPop MEnd) KNil)))) 0xcbc18 k
  | _ => T_KWF n k
  end.
(* [comment removed for export] *)
Definition NEXTJ (k : MC) : MC := MJoin (MSegK 20 P_CL (KCons 0x8fe54 0 MEnd KNil)) 0x8fe54 k.
(* [comment removed for export] *)
Definition LASTP (kx : MC) : MC := MSegK 20 P_CL (KCons 0x8fe7c 0 kx KNil).
(* [comment removed for export] *)
Fixpoint HRUNH (k : nat) (kx : MC) : MC :=
  match k with
  | O => kx
  | Datatypes.S O => HARN (LASTP kx)
  | Datatypes.S k' => HARN (NEXTJ (HRUNH k' kx))
  end.
(* [comment removed for export] *)
Definition FIRSTH (n : nat) (kx : MC) : MC :=
  MJoin (MSegK 20 P_CL (KCons 0xcc8cc 29 MEnd KNil)) 0xcc8cc
    (MIoctl 1 0x5413 (MSegK 20 PT_RETRY (KCons 0xcbc0c 66 (TH_KWL
       (match n with Datatypes.S O => LASTP kx | _ => NEXTJ (HRUNH (Nat.pred n) kx) end)) KNil))).
(* [comment removed for export] *)
Definition KCALLSH0_1 (n : nat) (kx : MC) : MC := MSplitP 2 (HARN1 (FIRSTH n kx)).
Definition KCALLSH_1 (n : nat) (kx : MC) : MC := MSplitP 2 (MSegK 20 P_CL (KCons 0x8fe54 0 (HARN1 (FIRSTH n kx)) KNil)).
Definition KEXITH (n : nat) : MC :=
  MSegK 40 (jplanF 8) (KCons 0xcbc0c 66 (TH_KWF n (MSegK 40 (jplanF 8) (KCons 0xc6014 94 MExit KNil))) (KCons 0xc6014 94 MExit KNil)).
(* [comment removed for export] *)
Definition HEADH_0 (tail : MC -> MC) (n : nat) : MC := MJoinG genLAR (KCALLSH0_1 n MEnd) 0x8fe7c (tail (KEXITH n)).
Definition HEADH_1 (tail : MC -> MC) (n : nat) : MC := MJoinG genLAR (KCALLSH_1 n MEnd) 0x8fe7c (tail (KEXITH n)).
End BodyChH.
(* [comment removed for export] *)
End AsanBodyChH.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyT AsanBodyIf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT.AsanBodyH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixLg OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixGL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailCh OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCh OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertDefs.AsanBodyChH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyIf.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyCertBase.
Export OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanPrefixGLit OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanPrefixGLLit OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.



Definition CH_E (n : nat) : MCX := BODY_E1 A1X A2X A3X BX HARN_E VIA VCT HARN1_E IB_E n.
Definition CH_P (n : nat) : MCX := BX (BConc VCALLS) (MUse 0 NB_G (BODY_P1 A1X A2X A3X BX HARN_P VIA VCT HARN1_P IB_P n)).
Definition CH_L (n : nat) : MCX := BX (BConc VCALLS) (MUse 1 NB_G (BODY_L1 A1X A2X A3X BX HARN_L VIA VCT HARN1_L QU_I MP_I IB_L n)).
Definition CH_S : MCX := MSplit TG_VN 64512 (MCont 0 NB_G) (MCont 1 NB_G).

(* [comment removed for export] *)
Definition SUBT_E : sub_t := (TTE_S, TTE_M, TTE_A, [(FTE_S, FTE_M, FTE_A)]).
Definition SUBT_P : sub_t := (TTP_S, TTP_M, TTP_A, [(FTP_S, FTP_M, FTP_A)]).
Definition SUBT_L : sub_t := (TTL_S, TTL_M, TTL_A, [(FTL_S, FTL_M, FTL_A)]).
Definition SUBS_X : list sub_t := SUBS_P ++ [SUBT_E; SUBT_P; SUBT_L] ++ SUBS_H.
(* [comment removed for export] *)
Definition SUBP_G : sub_t := (TG_GP, TG0_M, TG0_A, [(PFING_S, PFING_M, PFING_A)]).
Definition SUBP_L : sub_t := (TG_GL, TG0_M, TG0_A, [(PFINL_S, PFINL_M, PFINL_A)]).
Definition SUBS_XE : list sub_t := [SUBT_E; SUBT_E; SUBT_E; SUBT_E; SUBT_E] ++ SUBS_HE.
Definition SUBS_XP : list sub_t := [SUBP_G; SUBP_G; SUBT_P; SUBT_P; SUBT_P] ++ SUBS_HP.
Definition SUBS_XL : list sub_t := [SUBP_L; SUBP_L; SUBT_L; SUBT_L; SUBT_L] ++ SUBS_HL.
(* [comment removed for export] *)
Definition TAIL_E (k : MCX) : MCX := WNORM BX false (MUse 2 NB_G (WNORM BX true k)).
Definition TAIL_P (k : MCX) : MCX := WNORM BX false (MUse 3 NB_G (WNORM BX true k)).
Definition TAIL_L (k : MCX) : MCX := WNORM BX false (MUse 4 NB_G (WNORM BX true k)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CHH_E (n : nat) : MCX := BX (BConc VCALLS_E) (HEADH_0 HARN_E HARN1_E TAIL_E n).
Definition CHH_P (n : nat) : MCX := BX (BConc VCALLS) (MUse 0 NB_G (HEADH_1 HARN_P HARN1_P TAIL_P n)).
Definition CHH_L (n : nat) : MCX := BX (BConc VCALLS) (MUse 1 NB_G (BX (BIrL LNC_L) (LNORM BX (HEADH_1 HARN_L HARN1_L TAIL_L n)))).

Definition body_res_s (subs : list sub_t) (conts : list (sst * smodel * fstate * shp * ast)) (ch : MCX) (c : sst * smodel * fstate * shp * ast)
  : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLH IMGH PV 6 PHI false (Some H0) apostX anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a subs conts ch
    (fst (fst (fst (fst c)))) (snd (fst (fst (fst c)))) (snd (fst (fst c))) (snd (fst c)) (snd c).
Definition body_res := body_res_s SUBS_X.      (* [comment removed for export] *)
Definition ok_nil (r : option (list (sst * smodel * fstate * shp * ast))) : bool := match r with Some [] => true | _ => false end.
Definition certE (n : nat) : bool := ok_nil (body_res [] (CH_E n) (TE_C n)).
Definition certP (n : nat) : bool := ok_nil (body_res [] (CH_P n) (TPP_C n)).
Definition certL (n : nat) : bool := ok_nil (body_res [] (CH_L n) (TPL_C n)).
Definition certHE (n : nat) : bool := ok_nil (body_res_s SUBS_XE [] (CHH_E n) (TE_C n)).
Definition certHP (n : nat) : bool := ok_nil (body_res_s SUBS_XP [] (CHH_P n) (TPP_C n)).
Definition certHL (n : nat) : bool := ok_nil (body_res_s SUBS_XL [] (CHH_L n) (TPL_C n)).
Definition certS (n : nat) : bool := ok_nil (body_res_s [] (CONTS_PL n) CH_S (TP_C n)).
(* [comment removed for export] *)

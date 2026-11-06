(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanLibNode AsanPlan AsanPlanImages BothPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainDefs BothTableL BothLibTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XLm segs (A : atable) (nx0 : nat) : acs -> option acs := ALN.summary_lib segs LIBTAB_BOTH A nx0.

(* [comment removed for export] *)
Section Forms.
  Variable HS_both : nat -> option acs.
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Variable TTm : nat -> option (acs * plan * shape).   (* [comment removed for export] *)

  #[local] Notation CHK C HS HL cs p :=
    (check BSEGS ITm BOTHL NX0 AsanInit.LIMIT (XNm BSEGS BOTHL NX0 RPN.RP_BOTH (iotab_of C)) (XEm BSEGS BOTHL NX0) (XBm BSEGS NX0 (iotab_of C)) (XLm BSEGS BOTHL NX0)
           HS HL TTm KCm BFUELm FUELm None cs p).

  (* [comment removed for export] *)
  Definition main_check (h : nat) (C : class) (p : plan) : cres := CHK C HS_none HL_none (main_start HS_both h C) p.
  Definition pre_check (h : nat) (C : class) (HT : list (nat * (nat * acs))) (p : plan) : cres := CHK C (hs_of HT) (lv_of HT) (main_start HS_both h C) p.
  Definition pay_check (ch : acs) (C : class) (p : plan) : cres := CHK C HS_none HL_none (pay_start ch C) p.
  Definition seg_check (ch : acs) (C : class) (HT : list (nat * (nat * acs))) (p : plan) : cres := CHK C (hs_of HT) (lv_of HT) (pay_start ch C) p.
  (* [comment removed for export] *)
  Definition pre0_check (h : nat) (HT : list (nat * (nat * acs))) (p : plan) : cres := CHK [] (hs_of HT) (lv_of HT) (HSA HS_both h) p.

  (* [comment removed for export] *)
  Definition tailf_check (T : acs) (p : plan) : cres :=
    check BSEGS ITm BOTHL NX0 AsanInit.LIMIT (XNm BSEGS BOTHL NX0 RPN.RP_BOTH (iotab_of [])) (XEm BSEGS BOTHL NX0) (XBm BSEGS NX0 (iotab_of [])) (XLm BSEGS BOTHL NX0)
          HS_none HL_none AP.TT_none KCm BFUELm FUELm None T p.
  Definition tailsF_ok : Prop :=
    forall t T p s, TTm t = Some (T, p, s) -> AP.is_full p = true -> tailf_check T p = COk s /\ shape_closed s = true.
  Definition tailsF_okb (TL : list (acs * plan * shape)) : bool :=
    forallb (fun e : acs * plan * shape => let '(T, p, s) := e in
               if AP.is_full p then match tailf_check T p with COk s' => shape_eqb s s' && shape_closed s | CErr _ _ _ => false end
               else true) TL.
  (* [comment removed for export] *)
  Definition tails_all_ok : Prop := AP.tails_ok BSEGS ITm BOTHL NX0 AsanInit.LIMIT TTm KCm /\ tailsF_ok.
End Forms.


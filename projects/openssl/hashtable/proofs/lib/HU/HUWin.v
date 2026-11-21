(* SPDX-License-Identifier: MIT *)
(* LPS c0dd863a: the UBSan image's stack window under the entry's stack pointer, for the plain family
   start states (VU5, VU6, VU7 *S0.v) and the states their certificates recorded (HUBlob2, HUBlob3);
   H0Win's twin over [HUMainEntryDefs.kn_stack].

   The launch gives [wok_lo sp0, sp0) writable (MemSplit), 6144513 bytes: the KWr fact on the stack
   pointer in [HUMainEntryDefs.kn_stack].  The plain bridge's FX stack region claims whole pages from
   its base [sp0 - 8388608] up (KitCfg/HoDrive.shapes4, HUHandoff.facts_geom), so the families' window
   is that fact cut to whole pages, as the ASan launch's is (AsanInit.stack_window_ok).  The recorded
   runs were made under the old 8 MiB window: [win_cut] moves the lower end of each recorded stack
   fact below [sp0 - STK_W] up to it and keeps its upper end.  Nothing here is trusted: each family
   certificate re-checks its recorded states against the run it computes from the start states. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
From OSSVerify.Proofs.openssl.hashtable.lib Require SymExec2 HUMainEntryDefs.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

(* the window: [kn_stack]'s KWr fact (its only one, on the stack pointer) in whole pages *)
Definition STK_W : Z :=
  match List.find (fun K => match K with SymExec2.SX2.KWr _ _ => true | _ => false end) HUMainEntryDefs.kn_stack with
  | Some (SymExec2.SX2.KWr _ n) => n - n mod 4096
  | _ => 0
  end.

(* a recorded stack fact on [e_sp0] / [e_spw] that reaches below the window, cut at it *)
Definition win_cut (K : kentry) : kentry :=
  let cut (a : saddr) (n : expr) (mk : saddr -> expr -> kentry) :=
    match n with
    | ELit z =>
        if ((expr_eqb (a_base a) e_sp0 || expr_eqb (a_base a) e_spw) && (a_off a <? - STK_W))%bool
        then mk (SA (a_base a) (- STK_W)) (ELit (Z.max 0 (z - (- STK_W - a_off a))))
        else K
    | _ => K
    end in
  match K with
  | KWr a n => cut a n KWr
  | KUnk a n => cut a n KUnk
  | KZero a n => cut a n KZero
  | _ => K
  end.

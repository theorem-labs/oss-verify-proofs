(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack window is the launch's). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.openssl.hashtable.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHoBuild.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan HBPlanImage HBAtable BC6B0Lit.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrClass BrRevS BrDress BrTrans BrGen.
From OSSVerify.Proofs.openssl.hashtable.lib.HBX Require Import BFePcsX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Open Scope Z_scope.
Definition IM : fimage := odflt [] (mk_fimage HASEGS).
Definition code : itrie finstr := odflt iempty (build_code HASEGS fe_pcs).
Definition START : CAP.acs := c6b0_hs24.
(* LPS c0dd863a: the end state is read back from this hole's run [F'] (HB/BFEEndHB0.v); it and its value
   table are defined there and in BFeHoleHB0.v *)
(* [comment removed for export] *)
Definition TT0 : ttab_e := [(2%uint63, CAP.eaddz CAP.e_spw (-8388608)); (4%uint63, AX2.ELit 0)].
(* LPS c0dd863a: the stack region's writable part is the window that START's own KWr fact on the entry's
   stack pointer gives (8 MiB less the launch block's bound, in whole pages: AsanInit.stack_window_ok); its
   offset from the pointer, read here *)
Definition STK_K : Z :=
  match List.find (fun K => match K with AX2.KWr (AX2.SA b _) (AX2.ELit _) => AX2.expr_eqb b CAP.e_spw | _ => false end) (CAP.kn START) with
  | Some (AX2.KWr (AX2.SA _ k) _) => k
  | _ => 0
  end.
Definition shapes : list rshape :=
  [(0%uint63, 0x10000%uint63, 0xbfb000%uint63, 0%uint63, None);
   (2%uint63, of_Z (8388608 + STK_K), 8388608%uint63, 4%uint63, Some PKUnk);
   (4%uint63, 0x7fffa000%uint63, 0x80177600%uint63, 12%uint63, Some PKUnk)].
Definition regtags : ttab_e := gen_tt TT0 100%uint63 (map (fun e => AX2.KWord (AX2.SA (AX2.ELit 0) 0) 8 e) (AX2.s_regs (CAP.a_ss START))).
Definition TT : ttab_e := gen_tt regtags 200%uint63 (CAP.kn START).
Definition d : sdesc := ho_build_fast IM (rb_facts HAT TT shapes [] [] START) (of_Z (AX2.s_pc (CAP.a_ss START))) shapes.   (* [comment removed for export] *)
Definition bs : list ditem := [(4%uint63, 0%uint63, 0%uint63, RK_plain)].
Definition BP : int := 2029648%uint63.        (* [comment removed for export] *)
Definition res := (fx_run IM code BP 20 (dress (state_of d) bs)).
Definition F' : fstate := (fst (fst res)).
Definition RS : stop := (snd (fst res)).
Definition CNT : int := (snd res).
(* [comment removed for export] *)
(* [comment removed for export] *)

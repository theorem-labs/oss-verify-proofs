(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHoBuild.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan HBPlanImage HBAtable BC3A3Lit BFEEndA3.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrClass BrRevS BrDress BrTrans BrGen.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require Import BFePcsX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Open Scope Z_scope.
Definition IM : fimage := odflt [] (mk_fimage HASEGS).
Definition code : itrie finstr := odflt iempty (build_code HASEGS fe_pcs).
Definition START : CAP.acs := c3a3_hs20.
Definition END : CAP.acs := feenda3.
(* [comment removed for export] *)
Definition TT0 : ttab_e := [(2%uint63, CAP.eaddz CAP.e_spw (-8388608)); (4%uint63, AX2.ELit 0)].
Definition shapes : list rshape :=
  [(0%uint63, 0x10000%uint63, 0xbfb000%uint63, 0%uint63, None);
   (2%uint63, 0%uint63, 8388608%uint63, 4%uint63, Some PKUnk);
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
Definition VT : vtab := gen_vt (CAP.nxt START) (AX2.s_regs (CAP.a_ss END)) F'.
(* [comment removed for export] *)
(* [comment removed for export] *)

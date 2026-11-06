(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GcFlush.F72_002.   (* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzRomUbsan.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
#[local] Notation SEGS := Ubsan.M.loaded_segments.
Definition ROMTAB_U : romtab :=
  Eval vm_compute in
    (let t8 := rt_gen (rom_load_g SEGS) SZ8 true 0x13380 8 1926%nat RLeaf in
     [ ((SZ1, false), rt_gen (rom_load_g SEGS) SZ1 false 0x15a40 1 7536%nat RLeaf); ((SZ8, true), t8); ((SZ8, false), t8) ]).
Lemma ROMTAB_U_ok : romtab_check (rom_load_g SEGS) ROMTAB_U = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance rom_cache_U : rom_cache rom_load_g | 0 := {| rc_segs := SEGS; rc_tab := ROMTAB_U; rc_ok := ROMTAB_U_ok |}.
End GlzRomUbsan.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuStrCtor.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition IT : itab := mk_itab_ranges USEGS [(0x2fb54, 51%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 30.
Definition HELLO : Z := 0x128d1.
Definition regs0 : list expr := ELit 0 :: map EVar (seq 0 10) ++ [ELit HELLO] ++ map EVar (seq 10 20).
Definition e_sp : expr := EVar 1.
Definition e_p : expr := EVar 9.
Definition kn0 : list kentry :=
  [KRange e_p CEIL HI47; KWr (SA e_p 0) (ELit 24);     (* [comment removed for export] *)
   KWr (SA e_sp (-64)) (ELit 64); KDisj (SA e_p 0) (ELit 24) (SA e_sp (-64)) (ELit 64); KAlign e_sp 16; KRange e_sp (CEIL + 4096) HI47; KImg 0x10000 0x75000].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 64 0 [] [(e_p, ELit 24)] 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition tin : acs := mkcs 0x2fb54 regs0 kn0 NXF.

Definition LO : nat := 30.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.
Definition x_regs : list expr := sr_havoc regs0 clobbered LO.
Definition x_kn : list kentry := [KWord (SA e_p 0) 1 (ELit 22); KWord (SA e_p 12) 1 (ELit 0)] ++ kn0.
Definition RET : Z := 0x2fc18.
Definition tout : acs := mkcs RET x_regs x_kn (LO + 15)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.

Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN 0 0 CT.

Definition plan_ctor : plan :=
  PVia 0 tout LO (PRun [] (PExt 4 [] (PRun [] (PExt 3 [] (PRun [] (PMerge 0)))))) (PHandoff 0).

Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 200.
Definition BFUEL : nat := 300.

Lemma ctor_cert :
  check USEGS IT AUBSAN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) (B2JCutShare.GlzCallCert.XB0) XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_ctor
  = COk (SHole 0).
Proof. vm_compute. reflexivity. Qed.
Lemma ctor_gplan : gplan_ok plan_ctor = true. Proof. reflexivity. Qed.
Lemma ctor_shape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
End GuStrCtor.
Module GuVecCtor.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module VecCtorU.
Definition ENTRY : Z := 0x2f4f8.
Definition RETPC : Z := 0x2f560.
Definition HEAD : Z := 0x2f77c.        (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges USEGS
  [(0x2f4f8, 27%nat); (0x2f578, 21%nat); (0x2f5d0, 21%nat); (0x2f6f4, 19%nat); (0x2f744, 34%nat); (0x2f7d0, 11%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regs0 : list expr := sr_upd (ELit 0 :: map EVar (seq 0 31)) 4 (ELit (g_tp GUBSAN)).
Definition e_sp : expr := EVar 1.
Definition V : expr := EVar 9.        (* [comment removed for export] *)
Definition FIRST : expr := EVar 10.   (* [comment removed for export] *)
Definition SZ : expr := EVar 12.      (* [comment removed for export] *)
Definition NXF : nat := 31.
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x9c000).
(* [comment removed for export] *)
Definition SZHI : Z := 2 ^ 26 - 1.
             (* [comment removed for export] *)
Definition FRS : Z := 96 + MSTK.      (* [comment removed for export] *)
Definition regs_in : list expr := sr_upd regs0 12 (eadd FIRST SZ).

Definition kn_fixed : list kentry :=
  [ KRange V CEIL HI47; KWr (SA V 0) (ELit 24); KRange (esub V e_sp) 0 (2 ^ 40);
    KRange SZ 1 SZHI; KRange FIRST PTRLO PTRHI; KRange (eadd FIRST SZ) (PTRLO + 1) PTRHI;
    KWr (SA FIRST 0) SZ; KUnk (SA FIRST 0) SZ; img_apart FIRST 0 SZ;
    KDisj (SA FIRST 0) SZ (SA V 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + FRS + 16) HI47; KWr (SA e_sp (- FRS)) (ELit FRS);
    KDisj (SA e_sp (- FRS)) (ELit FRS) (SA V 0) (ELit 24); KDisj (SA FIRST 0) SZ (SA e_sp (- FRS)) (ELit (FRS + WSTK));   (* [comment removed for export] *)
    KImg 0x10000 0x75000 ].
Definition kn_in : list kentry := kn_fixed.
Definition WS : list (expr * expr) := [(V, ELit 24)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition tin : acs := mkcs ENTRY regs_in kn_in NXF [(FIRST, SZ)].

(* [comment removed for export] *)
Definition P : expr := EVar 31.
Definition XLO : nat := 32.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.
Definition regs_out : list expr := sr_havoc regs0 clobbered XLO.
Definition blkP (p n : expr) : list kentry :=
  [ KRange p PTRLO (PTRHI - 1); KRange (eadd n p) (PTRLO + 1) PTRHI; KAlign p 16; KWr (SA p 0) n; KUnk (SA p 0) n;
    KDisj (SA p 0) n (SA FIRST 0) SZ; KDisj (SA p 0) n (SA V 0) (ELit 24); KDisj (SA p 0) n (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 n ].
Definition kn_out : list kentry :=
  [ KWord (SA V 0) 8 P; KWord (SA V 8) 8 (eadd SZ P); KWord (SA V 16) 8 (eadd SZ P) ] ++ blkP P SZ ++ kn_fixed.
Definition tout : acs := mkcs RETPC regs_out kn_out (XLO + 15)%nat [(P, SZ); (FIRST, SZ)].
Definition BCAP : Z := 3 * 2 ^ 26.
Definition CCAP : Z := 2.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN BCAP CCAP CT.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 400.
Definition BFUEL : nat := 300.

(* [comment removed for export] *)
Definition JV : nat := 60.
Definition J : expr := EVar JV.
Definition hv : list nat := [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)
Definition sp4 : expr := eaddz e_sp (-176).                                  (* [comment removed for export] *)
Definition regs_loop : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
     1 (ELit 0x2f708)) 2 sp4) 8 (eadd P J)) 9 P) 10 (ELit (2 ^ 64 - 1))) 11 (eadd FIRST J)) 12 (eadd FIRST SZ)) 13 (ELit 2))
     18 FIRST) 19 V) hv 61.
Definition frame : list kentry :=
  [ (* [comment removed for export] *)
    KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-56)) 8 V; KWord (SA e_sp (-48)) 1 (ELit 0);
    (* [comment removed for export] *)
    KWord (SA e_sp (-72)) 8 (ELit 0x2f548); KWord (SA e_sp (-80)) 8 SZ; KWord (SA e_sp (-88)) 8 (eadd FIRST SZ);
    (* [comment removed for export] *)
    KWord (SA e_sp (-104)) 8 (ELit 0x2f60c); KWord (SA e_sp (-112)) 8 V;
    (* [comment removed for export] *)
    KWord (SA e_sp (-120)) 8 (ELit 0x2f708); KWord (SA e_sp (-128)) 8 P; KWord (SA e_sp (-136)) 8 (eadd P J);
    KWord (SA e_sp (-144)) 8 P; KWord (SA e_sp (-176)) 8 V; KWord (SA e_sp (-168)) 8 (eaddz e_sp (-144));
    KWord (SA e_sp (-160)) 8 (eaddz e_sp (-136)) ].
Definition kn_loop : list kentry :=
  [ KRange J 0 SZHI; KRange (esub SZ J) 1 SZHI;
    KWord (SA V 0) 8 P; KWord (SA V 8) 8 P; KWord (SA V 16) 8 (eadd SZ P) ]
  ++ frame ++ blkP P SZ ++ kn_fixed.
Definition INV : acs := mkcs HEAD regs_loop kn_loop 72 [(P, SZ); (FIRST, SZ)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition body : plan := PCase2 (esub SZ J) 1 (PRun [] (PHandoff 0)) (PRun [HEAD] PNext).
Definition plan : plan := PRun [] (PExt 20 [] (PRun [HEAD] (PLoop JV SZ INV [] body (PContraH 0)))).

Definition SHAPE : shape := SHole 0.
Lemma cert : check USEGS IT AUBSAN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) (B2JCutShare.GlzCallCert.XB0) XC0 (HSce ce) 0%nat BFUEL FUEL None tin plan = COk SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk SHAPE)). Qed.
Lemma gplan : gplan_ok plan = true. Proof. reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.


End VecCtorU.
End GuVecCtor.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GlzConst.
Export GlzRomUbsan.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition regs0 : list expr := ELit 0 :: map EVar (seq 0 31).

Definition e_sp : expr := EVar 1.
Definition e_a0 : expr := EVar 9.   Definition e_a1 : expr := EVar 10.
Definition e_a2 : expr := EVar 11.  Definition e_a3 : expr := EVar 12.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition objhi (n : Z) : Z := HI47 - n.
(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_SZ : Z := 0x9c000.      (* [comment removed for export] *)
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) IMG_LO) (ELit IMG_SZ).



(* [comment removed for export] *)
Definition mkcs (ylo : Z) (ws : list (expr * expr)) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 ylo 0 [] ws 0 e_sp FdStd false.

(* [comment removed for export] *)
Definition caller_saved_but_a01 : list nat := [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.

(* [comment removed for export] *)
Definition str_L (obj a size data : expr) : list kentry :=
  [ KRange obj PTRLO (objhi 24);
    KWord (SA obj 0) 8 (eaddz (escale 8 a) 1); KWord (SA obj 8) 8 size; KWord (SA obj 16) 8 data ].

(* [comment removed for export] *)
Definition sp_facts (ylo : Z) : list kentry := [KAlign e_sp 16; KRange e_sp (CEIL + ylo) HI47].

(* [comment removed for export] *)
Definition CT0 (id : nat) : option gcallee := None.
Definition XN (IT : itab) (NXF : nat) : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN 0 0 CT0.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 2000.
Definition BFUEL : nat := 1000.

(* [comment removed for export] *)
Definition q100w (x : expr) : expr := EAluw ALU_SRL (escale 5243 x) (ELit 19).
Definition q100 (x : expr) : expr := EAlu ALU_SRL (escale 5243 x) (ELit 19).
Definition q1e4a (x : expr) : expr := EAlu ALU_SRL (escale 429497 x) (ELit 32).
Definition q1e4b (x : expr) : expr := EAlu ALU_SRL (escale 109951163 x) (ELit 40).

Definition q1e8h (x : expr) : expr := EAlu ALU_SRL (EMd M_MULHU x (ELit 0xabcc77118461cefd)) (ELit 26).
Definition rem (x q : expr) (d : Z) : expr := rem_expr x q d.
Definition divfact (x q : expr) (d : Z) (k : plan) : plan := PExt 40 [x; q; ELit d] k.
(* [comment removed for export] *)
Definition zfact (x q : expr) (d : Z) (k : plan) : plan :=
  PFact (KRange (escale 4294967296 (rem x q d)) 0 ((d - 1) * 4294967296)) k.

(* [comment removed for export] *)
Lemma ubsan_G_ro_img : g_img_lo GUBSAN <= g_ro_lo GUBSAN /\ g_ro_lo GUBSAN <= g_ro_hi GUBSAN <= g_img_hi GUBSAN. Proof. cbn. lia. Qed.
Lemma ubsan_G_img_ceil {RC : run_ceil} : g_img_hi GUBSAN <= CEIL_run. Proof. pose proof ceil_rng. cbn [g_img_hi GUBSAN]. lia. Qed.
Lemma ubsan_G_img_hull : 0 <= g_img_lo GUBSAN <= g_img_hi GUBSAN /\ g_img_hi GUBSAN < 2 ^ 64. Proof. cbn. lia. Qed.

Lemma ubsan_SEGS_out : forall a : word,
  ~ (g_img_lo GUBSAN <= bv_unsigned a < g_img_hi GUBSAN) -> find_segment USEGS (bv_unsigned a) 1 = None.
Proof.
  intros a Ha. apply ubsan_in_hull. unfold APS.in_hull. cbn [img_lo img_hi AUBSAN g_img_lo g_img_hi GUBSAN] in *.
  destruct (Z_lt_ge_dec (bv_unsigned a) 0x10000) as [H|H].
  - apply Bool.andb_false_iff. left. apply Z.leb_gt. exact H.
  - apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma nil_SWIN_img : forall lo hi, In (lo, hi) (@nil (Z * Z)) ->
  g_ro_hi GUBSAN <= lo /\ hi <= g_img_hi GUBSAN /\ (forall plo phi, In (plo, phi) (g_priv GUBSAN) -> hi <= plo \/ phi <= lo).
Proof. intros lo hi []. Qed.

(* [comment removed for export] *)
Section XNSound.
Context {RC : run_ceil}.
Variable IT : itab.
Hypothesis IT_ok : itab_sound USEGS IT.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable HIDc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Hypothesis bcap_ok : B0c + 0 <= GBUDGET.
Hypothesis ccap_ok : C0c + 0 <= GCOUNT.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXF E E' -> UINV E -> UINV E'.
#[local] Notation AINVc := (AINV_f [] GUBSAN AINVH PERMc SPTOPc HIDc M0c B0c C0c).

Theorem XN_sound :
  gcontracts USEGS IT AUBSAN NXF PERMc SPTOPc FS0 FDS0 AINVc fx_ok UINV RZ GUBSAN 0 0 ->
  GPS.ext_stmt USEGS NXF (XN IT NXF) PERMc SPTOPc FS0 FDS0 AINVc fx_ok UINV RZ.
Proof.
  intros GCs. unfold XN.
  exact (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN 0 0 fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
            ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg
            bcap_ok ccap_ok UINV UINV_agree CT0 ltac:(intros id' ce' H; discriminate H) GCs).
Qed.
End XNSound.

(* [comment removed for export] *)
Definition IXMAX : Z := 32 * 2 ^ 26.
Definition RELHI : Z := 24 * 2 ^ 26 + 256 * IXMAX.
Definition relx (di err ix ix0 : expr) (lo : Z) : kentry :=
  KRange (esub (eadd (escale 24 di) (escale IXMAX err)) (esub ix ix0)) lo RELHI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition divfactU (x q : expr) (d : Z) (k : plan) : plan :=
  divfact x q d (PFact (KRange (escale 2 (rem x q d)) 0 (2 * (d - 1))) (PFact (KRange (escale 4 (rem x q d)) 0 (4 * (d - 1))) k)).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuAAT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition cfg_i8 : acfg :=
  {| c_entry := 0x352c0; c_ninstr := 158; c_fr := 80; c_nsaved := 9; c_K := 1; c_hr := 8; c_wmx := 6;
     c_head := 0x3530c; c_join1 := 0x3537c; c_ret := 0x35530; c_jreg := 19; c_lits := [(20%nat, 45); (21%nat, 1); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuAA.OBJ); (23%nat, eaddz GuAA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x353fc; c_ixreg := 10; c_ix2pc := 0x354b0; c_ix2reg := 10 |}.
Definition cfg_i16 : acfg :=
  {| c_entry := 0x35538; c_ninstr := 166; c_fr := 80; c_nsaved := 10; c_K := 2; c_hr := 8; c_wmx := 6;
     c_head := 0x3558c; c_join1 := 0x3560c; c_ret := 0x357c8; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 45); (22%nat, 2); (23%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuAA.OBJ); (24%nat, eaddz GuAA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x35690; c_ixreg := 10; c_ix2pc := 0x35744; c_ix2reg := 10 |}.
Definition cfg_i32 : acfg :=
  {| c_entry := 0x357d0; c_ninstr := 144; c_fr := 80; c_nsaved := 10; c_K := 4; c_hr := 16; c_wmx := 11;
     c_head := 0x35820; c_join1 := 0x358b8; c_ret := 0x35a08; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 4); (24%nat, 44)];
     c_mregs := [(18%nat, GuAA.G); (19%nat, GuAA.OBJ); (20%nat, eaddz GuAA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x358cc; c_ixreg := 12; c_ix2pc := 0x35988; c_ix2reg := 10 |}.
Definition cfg_i64 : acfg :=
  {| c_entry := 0x35a10; c_ninstr := 156; c_fr := 80; c_nsaved := 10; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x35a60; c_join1 := 0x35b28; c_ret := 0x35c78; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 8); (24%nat, 44)];
     c_mregs := [(18%nat, GuAA.G); (19%nat, GuAA.OBJ); (20%nat, eaddz GuAA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x35b3c; c_ixreg := 10; c_ix2pc := 0x35bf8; c_ix2reg := 10 |}.
Definition cfg_u8 : acfg :=
  {| c_entry := 0x35c80; c_ninstr := 207; c_fr := 112; c_nsaved := 13; c_K := 1; c_hr := 8; c_wmx := 3;
     c_head := 0x35cfc; c_join1 := 0x35d6c; c_ret := 0x35fb4; c_jreg := 19;
     c_lits := [(15%nat, 201); (16%nat, 2 ^ 64 - 3); (17%nat, 44); (20%nat, 99); (21%nat, 2 ^ 64 - 1 - 0x177c0); (22%nat, 2 ^ 64 - 4);
                (23%nat, 1); (25%nat, 2 ^ 64 - 1); (26%nat, 2 ^ 64 - 100); (27%nat, 0x177c0)];
     c_mregs := [(10%nat, IXv); (18%nat, GuAA.OBJ); (24%nat, eaddz GuAA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x35e58; c_ixreg := 10; c_ix2pc := 0x35f0c; c_ix2reg := 10 |}.
Definition cfg_u16 : acfg :=
  {| c_entry := 0x35fbc; c_ninstr := 152; c_fr := 80; c_nsaved := 9; c_K := 2; c_hr := 8; c_wmx := 5;
     c_head := 0x36008; c_join1 := 0x36088; c_ret := 0x36214; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 2); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuAA.OBJ); (23%nat, eaddz GuAA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x360e0; c_ixreg := 10; c_ix2pc := 0x36194; c_ix2reg := 10 |}.
Definition cfg_u32 : acfg :=
  {| c_entry := 0x3621c; c_ninstr := 144; c_fr := 80; c_nsaved := 10; c_K := 4; c_hr := 16; c_wmx := 10;
     c_head := 0x3626c; c_join1 := 0x36304; c_ret := 0x36454; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 4); (24%nat, 44)];
     c_mregs := [(18%nat, GuAA.G); (19%nat, GuAA.OBJ); (20%nat, eaddz GuAA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x36318; c_ixreg := 10; c_ix2pc := 0x363d4; c_ix2reg := 10 |}.
Definition cfg_u64 : acfg :=
  {| c_entry := 0x3645c; c_ninstr := 156; c_fr := 80; c_nsaved := 10; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x364ac; c_join1 := 0x36574; c_ret := 0x366c4; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 8); (24%nat, 44)];
     c_mregs := [(18%nat, GuAA.G); (19%nat, GuAA.OBJ); (20%nat, eaddz GuAA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x36588; c_ixreg := 12; c_ix2pc := 0x36644; c_ix2reg := 10 |}.
Definition cfg_f32 : acfg :=
  {| c_entry := 0x34da0; c_ninstr := 158; c_fr := 80; c_nsaved := 9; c_K := 4; c_hr := 21; c_wmx := 16;
     c_head := 0x34dec; c_join1 := 0x34e84; c_ret := 0x35010; c_jreg := 19; c_lits := [(20%nat, 3); (21%nat, 4); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuAA.OBJ); (23%nat, eaddz GuAA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x34edc; c_ixreg := 10; c_ix2pc := 0x34f90; c_ix2reg := 10 |}.
Definition cfg_f64 : acfg :=
  {| c_entry := 0x35018; c_ninstr := 170; c_fr := 80; c_nsaved := 9; c_K := 8; c_hr := 38; c_wmx := 36;
     c_head := 0x35064; c_join1 := 0x3512c; c_ret := 0x352b8; c_jreg := 19; c_lits := [(20%nat, 7); (21%nat, 8); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuAA.OBJ); (23%nat, eaddz GuAA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x35184; c_ixreg := 10; c_ix2pc := 0x35238; c_ix2reg := 10 |}.
End GuAAT.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuAAX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section X.
  Variable c : acfg.
  Variable elem : smode -> plan -> plan.
Definition XJ0 : expr := EVar 69.
Definition XNX : nat := nxt (INV c ML).
(* [comment removed for export] *)
Definition XTL : acs := add_kn (inst (INV c ML) JV XJ0) [KRange XJ0 0 NVHI].
(* [comment removed for export] *)
Definition XR0 : nat := 42.
Definition XRN : list (nat * nat) := (69%nat, XR0) :: map (fun i => (71 + i, XR0 + 1 + i)%nat) (seq 0 (XNX - 71)).
Definition XLOOPC : plan := PRename XRN (PLoopM JV NV [(INV c ML, body c elem ML, PContraH 1)] [(JV, EVar XR0)]).
Definition XCUTS : list (acs * plan) := [(XTL, XLOOPC)].
Definition xafter_elem (m : smode) (nk : plan) : plan :=
  chainA c m (c_ixreg c)
    (PCase2 (esub NV J) 1
       (PRun [] (PHandoffW (hole m) [(43%nat, escale (c_K c) (eaddz J 1))]))
       (PRun [c_ix2pc c] (chainB c m (c_ix2reg c) (PRun [c_head c] nk)))).
Definition xafter1 (m : smode) (nk : plan) : plan :=
  match m with
  | ML => PFactVia (esub (escale 8 A1) IXv) (esub S1 IXv) (c_hr c + 1) (2 ^ 40) (elem ML (xafter_elem ML nk))
  | MS => elem MS (xafter_elem MS nk)
  end.
Definition XHO : plan := PHandoffW 2 [(69%nat, eaddz J 1)].
Definition xalts1S : list (acs * plan) :=
  if Z.leb 23 (c_hr c) then [(JS1 c ML, xafter1 ML XHO)] else [(JS1 c MS, xafter1 MS PNext); (JS1 c ML, xafter1 ML XHO)].
Definition xbodyS : plan := PCase2 (remK c J) (c_K c - 1) (errJ c MS) (PRun [] (PViaM 1 xalts1S LO1 (diamondS c))).
Definition XPLAN_S : plan := PCase2 NV 0 (EXIT0 MS) (PRun [c_head c] (PLoopM JV NV [(INV c MS, xbodyS, PContraH 0)] [])).
Definition XPLAN_L1 : plan := PCase2 NV 0 (EXIT0 ML) (PRun [c_head c] (PHandoffW 2 [(69%nat, ELit 0)])).
End X.

(* [comment removed for export] *)
Lemma xhs_sub : forall (c : acfg) (CUTS : list (acs * plan)), length CUTS = 1%nat ->
  hs_sub (HScut (GuAA.ceL1 c) CUTS 1) (HScut (GuAA.ce c MS) CUTS 1).
Proof.
  intros c CUTS HL h ch H. left. exists 1%nat.
  assert (E1 : HScut (GuAA.ce c MS) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E1.
  destruct h as [|[|h]].
  - assert (E : HScut (GuAA.ceL1 c) CUTS 1 0 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - assert (E : HScut (GuAA.ceL1 c) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - exfalso. destruct CUTS as [|x [|y r]]; try discriminate HL.
    assert (E : HScut (GuAA.ceL1 c) [x] 1 (Datatypes.S (Datatypes.S h)) = None) by (destruct h as [|[|h]]; reflexivity).
    rewrite E in H. discriminate H.
Qed.
End GuAAX.
Module GuAAu8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GuAAT.cfg_u8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [0x35e58] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q8 : expr := EMd Instr.M_MULHU VAL (ELit 0x28f5c28f5c28f5d).           (* [comment removed for export] *)
Definition armA (k : plan) : plan := xl (xl (fin k)).                                                (* [comment removed for export] *)
Definition armC (k : plan) : plan := divfact VAL q8 100 (zfact VAL q8 100 (xl (fin k))).             (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (armC k)).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u8_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u8_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAu8.
Module GuNumT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BNU : Z := 0x34968.    (* [comment removed for export] *)
Definition BNI : Z := 0x38cc0.    (* [comment removed for export] *)
Definition NINSTR : nat := 270.
Definition IT (B : Z) : itab := mk_itab_ranges USEGS [(B, NINSTR)].
Lemma IT_ok : forall B, itab_sound USEGS (IT B). Proof. intro. apply APS.mk_itab_ranges_sound. Qed.
Definition at_ (B off : Z) : Z := B + off.
Definition RETPC (B : Z) : Z := at_ B 0x3e0.        (* [comment removed for export] *)
Definition is_int (B : Z) : bool := Z.eqb B BNI.

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GUBSAN)).   (* [comment removed for export] *)
Definition TP : expr := EVar 9.    Definition G : expr := EVar 10.    Definition OBJ : expr := EVar 13.
Definition INLO : expr := EVar 38.      (* [comment removed for export] *)
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO. (* [comment removed for export] *)
Definition REM : expr := EVar 32.  Definition IX : expr := EVar 33.
Definition D : expr := EVar 34.    Definition S : expr := EVar 35.    Definition A : expr := EVar 36.   (* [comment removed for export] *)
Definition ERR : expr := EVar 37.  Definition TAGV : expr := EVar 39.
Definition NXF : nat := 40.
Definition BLEN : expr := eadd ITO REM.
(* [comment removed for export] *)
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition CAPHI : Z := 4 * IXHI + 8 * INSZ + CAPK.
Definition AHI : Z := CAPHI / 8.
Definition two62 : Z := 2 ^ 62.
Definition FR : Z := 80.
Definition FRK : Z := FR + 2096.        (* [comment removed for export] *)

Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 112); KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24);
    KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN; KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK)) (ELit (FRK + WSTK)); img_apart d 0 (escale 8 a) ].
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition kn_fixed : list kentry :=
  [ KRange TP CEIL HI47; KRange (esub TP e_sp) 0 (2 ^ 62);
    KRange G CEIL (objhi 112); KWr (SA G 0) (ELit 4); KWr (SA G 96) (ELit 16); KWord (SA G 88) 8 (eadd IT0 REM);
    KRange OBJ CEIL (objhi 24); KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KDisj (SA INLO 0) BLEN (SA e_sp (- FRK)) (ELit (FRK + WSTK)); img_apart INLO 0 BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA G 0) (ELit 112) (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA G 0) (ELit 112); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + 8192) HI47; KWr (SA e_sp (- FRK)) (ELit FRK);
    KRange (esub G e_sp) 0 (2 ^ 62); KRange (esub OBJ e_sp) 0 (2 ^ 62);
    KDisj (SA e_sp (- FRK)) (ELit FRK) (SA G 0) (ELit 112); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA OBJ 0) (ELit 24);
    KDisj (SA e_sp (- FRK)) (ELit FRK) (SA TP 0) (ELit 4);          (* [comment removed for export] *)
    KAlign G 8; KAlign OBJ 8;                                          (* [comment removed for export] *)
    KWr (SA G 0) (ELit 112);    (* [comment removed for export] *)
    KImg 0x10000 0x75000 ].
Definition kn_in (m : smode) (B : Z) : list kentry :=
  [ KWord (SA TP 0) (if is_int B then 4%nat else 1%nat) TAGV; KRange TAGV 0 255;
    KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA G 96) 8 IT0; KWord (SA G 104) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG ]
  ++ str m IX IT0 34 ++ kn_fixed.
Definition WS : list (expr * expr) := [(G, ELit 4); (eaddz G 96, ELit 16); (OBJ, ELit 24); (INLO, BLEN)].
Definition mkcsV (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false.
Definition regs_in : list expr := sr_upd (sr_upd (sr_upd regsW 12 (eaddz G 96)) 13 (eaddz G 88)) 15 (eaddz G 104).
Definition tin (m : smode) (B : Z) : acs := mkcsV B (sr_upd regs_in 14 OBJ) (kn_in m B) NXF (vis m 34).

(* [comment removed for export] *)
Definition xERR := EVar 40. Definition xDI := EVar 41. Definition xIX := EVar 42.



Definition XLO : nat := 46.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition kn_out (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 24; KWord (SA G 96) 8 (eadd IT0 xDI); KRange xDI 0 8; KRange (esub REM xDI) 0 REMHI;
    KWord (SA G 104) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 two62;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ ;
    relx xDI xERR xIX IX 8 ]                                                            (* [comment removed for export] *)
  ++ str m xIX (eadd IT0 xDI) 43 ++ kn_fixed.
(* [comment removed for export] *)
Definition tout (m : smode) (B : Z) : acs := mkcsV (RETPC B) regs_out (kn_out m) (XLO + 15)%nat (vis m 43).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (m : smode) (B : Z) : gcallee2 := GCE2 NXF (tin m B) [tout MS B] [tout ML B] BCAP CCAP.
Definition ce (m : smode) (B : Z) : gcallee := c2_merged (ce2 m B).
(* [comment removed for export] *)
Definition ceL1 (B : Z) : gcallee := GCE NXF (tin ML B) [tout ML B; tout ML B] BCAP CCAP.
End GuNumT.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWAT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition cfg_i8 : acfg :=
  {| c_entry := 0x36e84; c_ninstr := 238; c_fr := 80; c_nsaved := 9; c_K := 1; c_hr := 8; c_wmx := 6;
     c_head := 0x37024; c_join1 := 0x37094; c_ret := 0x37234; c_jreg := 19; c_lits := [(20%nat, 45); (21%nat, 1); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuWA.OBJ); (23%nat, eaddz GuWA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x37114; c_ixreg := 12; c_ix2pc := 0x371b8; c_ix2reg := 10 |}.
Definition cfg_i16 : acfg :=
  {| c_entry := 0x3723c; c_ninstr := 246; c_fr := 80; c_nsaved := 10; c_K := 2; c_hr := 8; c_wmx := 6;
     c_head := 0x373e4; c_join1 := 0x37464; c_ret := 0x3760c; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 45); (22%nat, 2); (23%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuWA.OBJ); (24%nat, eaddz GuWA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x374e8; c_ixreg := 12; c_ix2pc := 0x3758c; c_ix2reg := 10 |}.
Definition cfg_i32 : acfg :=
  {| c_entry := 0x37614; c_ninstr := 227; c_fr := 96; c_nsaved := 11; c_K := 4; c_hr := 16; c_wmx := 11;
     c_head := 0x377c0; c_join1 := 0x37858; c_ret := 0x37998; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 4); (24%nat, 1); (25%nat, 44)];
     c_mregs := [(18%nat, GuWA.G); (19%nat, GuWA.OBJ); (20%nat, eaddz GuWA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x3786c; c_ixreg := 12; c_ix2pc := 0x37918; c_ix2reg := 10 |}.
Definition cfg_i64 : acfg :=
  {| c_entry := 0x379a0; c_ninstr := 239; c_fr := 96; c_nsaved := 11; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x37b4c; c_join1 := 0x37c14; c_ret := 0x37d54; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 8); (24%nat, 1); (25%nat, 44)];
     c_mregs := [(18%nat, GuWA.G); (19%nat, GuWA.OBJ); (20%nat, eaddz GuWA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x37c28; c_ixreg := 10; c_ix2pc := 0x37cd4; c_ix2reg := 10 |}.
Definition cfg_u8 : acfg :=
  {| c_entry := 0x37d5c; c_ninstr := 287; c_fr := 112; c_nsaved := 13; c_K := 1; c_hr := 8; c_wmx := 3;
     c_head := 0x37f2c; c_join1 := 0x37f9c; c_ret := 0x381d0; c_jreg := 19;
     c_lits := [(15%nat, 201); (16%nat, 2 ^ 64 - 3); (17%nat, 44); (20%nat, 99); (21%nat, 2 ^ 64 - 1 - 0x177c0); (22%nat, 2 ^ 64 - 4);
                (23%nat, 1); (25%nat, 2 ^ 64 - 1); (26%nat, 2 ^ 64 - 100); (27%nat, 0x177c0)];
     c_mregs := [(10%nat, IXv); (18%nat, GuWA.OBJ); (24%nat, eaddz GuWA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x38088; c_ixreg := 11; c_ix2pc := 0x3812c; c_ix2reg := 10 |}.
Definition cfg_u16 : acfg :=
  {| c_entry := 0x381d8; c_ninstr := 232; c_fr := 80; c_nsaved := 9; c_K := 2; c_hr := 8; c_wmx := 5;
     c_head := 0x38378; c_join1 := 0x383f8; c_ret := 0x38570; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 2); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuWA.OBJ); (23%nat, eaddz GuWA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x38450; c_ixreg := 12; c_ix2pc := 0x384f4; c_ix2reg := 10 |}.
Definition cfg_u32 : acfg :=
  {| c_entry := 0x38578; c_ninstr := 227; c_fr := 96; c_nsaved := 11; c_K := 4; c_hr := 16; c_wmx := 10;
     c_head := 0x38724; c_join1 := 0x387bc; c_ret := 0x388fc; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 4); (24%nat, 1); (25%nat, 44)];
     c_mregs := [(18%nat, GuWA.G); (19%nat, GuWA.OBJ); (20%nat, eaddz GuWA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x387d0; c_ixreg := 10; c_ix2pc := 0x3887c; c_ix2reg := 10 |}.
Definition cfg_u64 : acfg :=
  {| c_entry := 0x38904; c_ninstr := 239; c_fr := 96; c_nsaved := 11; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x38ab0; c_join1 := 0x38b78; c_ret := 0x38cb8; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 8); (24%nat, 1); (25%nat, 44)];
     c_mregs := [(18%nat, GuWA.G); (19%nat, GuWA.OBJ); (20%nat, eaddz GuWA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x38b8c; c_ixreg := 12; c_ix2pc := 0x38c38; c_ix2reg := 10 |}.
Definition cfg_f32 : acfg :=
  {| c_entry := 0x366cc; c_ninstr := 241; c_fr := 80; c_nsaved := 10; c_K := 4; c_hr := 21; c_wmx := 16;
     c_head := 0x36874; c_join1 := 0x3690c; c_ret := 0x36a88; c_jreg := 19; c_lits := [(20%nat, 3); (21%nat, 4); (22%nat, 1); (23%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuWA.OBJ); (24%nat, eaddz GuWA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x36964; c_ixreg := 12; c_ix2pc := 0x36a08; c_ix2reg := 10 |}.
Definition cfg_f64 : acfg :=
  {| c_entry := 0x36a90; c_ninstr := 253; c_fr := 80; c_nsaved := 10; c_K := 8; c_hr := 38; c_wmx := 36;
     c_head := 0x36c38; c_join1 := 0x36d00; c_ret := 0x36e7c; c_jreg := 19; c_lits := [(20%nat, 7); (21%nat, 8); (22%nat, 1); (23%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GuWA.OBJ); (24%nat, eaddz GuWA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x36d58; c_ixreg := 12; c_ix2pc := 0x36dfc; c_ix2reg := 10 |}.
End GuWAT.
Module GuWAX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section X.
  Variable c : acfg.
  Variable elem : smode -> plan -> plan.
Definition XJ0 : expr := EVar 69.
Definition XNX : nat := nxt (INV c ML).
(* [comment removed for export] *)
Definition XTL : acs := add_kn (inst (INV c ML) JV XJ0) [KRange XJ0 0 NVHI].
(* [comment removed for export] *)
Definition XR0 : nat := 43.
Definition XRN : list (nat * nat) := (69%nat, XR0) :: map (fun i => (71 + i, XR0 + 1 + i)%nat) (seq 0 (XNX - 71)).
Definition XLOOPC : plan := PRename XRN (PLoopM JV NV [(INV c ML, body c elem ML, PContraH 1)] [(JV, EVar XR0)]).
Definition XCUTS : list (acs * plan) := [(XTL, XLOOPC)].
Definition xafter_elem (m : smode) (nk : plan) : plan :=
  chainA c m (c_ixreg c)
    (PCase2 (esub NV J) 1
       (PRun [] (PHandoffW (hole m) [(42%nat, eadd HL (escale (c_K c) (eaddz J 1)))]))
       (PRun [c_ix2pc c] (chainB c m (c_ix2reg c) (PRun [c_head c] nk)))).
Definition xafter1 (m : smode) (nk : plan) : plan :=
  match m with
  | ML => PFactVia (esub (escale 8 A1) IXv) (esub S1 IXv) (c_hr c + 1) (2 ^ 40) (elem ML (xafter_elem ML nk))
  | MS => elem MS (xafter_elem MS nk)
  end.
Definition XHO : plan := PHandoffW 2 [(69%nat, eaddz J 1); (41%nat, HL); (42%nat, NV)].
Definition xalts1S : list (acs * plan) :=
  if Z.leb 23 (c_hr c) then [(JS1 c ML, xafter1 ML XHO)] else [(JS1 c MS, xafter1 MS PNext); (JS1 c ML, xafter1 ML XHO)].
Definition xbodyS : plan := PCase2 (remK c J) (c_K c - 1) (errJ c MS) (PRun [] (PViaM 1 xalts1S LO1 (diamondS c))).
Definition XPLAN_S : plan :=
  PVia 0 (JS0 c MS) 41 (hdr_arms c MS)
    (PFactLe (esub (eadd IT0 HL) INLO) (eadd (esub IT0 INLO) REM) INSZ (PLoopM JV NV [(INV c MS, xbodyS, PContraH 0)] [])).
Definition XPLAN_L1 : plan :=
  PVia 0 (JS0 c ML) 41 (hdr_arms c ML)
    (PFactLe (esub (eadd IT0 HL) INLO) (eadd (esub IT0 INLO) REM) INSZ (PHandoffW 2 [(69%nat, ELit 0); (41%nat, HL); (42%nat, NV)])).
End X.

(* [comment removed for export] *)
Lemma xhs_sub : forall (c : acfg) (CUTS : list (acs * plan)), length CUTS = 1%nat ->
  hs_sub (HScut (GuWA.ceL1 c) CUTS 1) (HScut (GuWA.ce c MS) CUTS 1).
Proof.
  intros c CUTS HL h ch H. left. exists 1%nat.
  assert (E1 : HScut (GuWA.ce c MS) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E1.
  destruct h as [|[|h]].
  - assert (E : HScut (GuWA.ceL1 c) CUTS 1 0 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - assert (E : HScut (GuWA.ceL1 c) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - exfalso. destruct CUTS as [|x [|y r]]; try discriminate HL.
    assert (E : HScut (GuWA.ceL1 c) [x] 1 (Datatypes.S (Datatypes.S h)) = None) by (destruct h as [|[|h]]; reflexivity).
    rewrite E in H. discriminate H.
Qed.
End GuWAX.
Module GuWAu8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GuWAT.cfg_u8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [0x38088] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q8 : expr := EMd Instr.M_MULHU VAL (ELit 0x28f5c28f5c28f5d).
Definition armA (k : plan) : plan := xl (xl (fin k)).
Definition armC (k : plan) : plan := divfact VAL q8 100 (zfact VAL q8 100 (xl (fin k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (armC k)).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u8_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u8_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAu8.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import EscU.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon GuNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA GuAAT OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA GuWAT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation PTRHI := GlzConst.PTRHI.
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x9c000).
Definition ENTRY : Z := 0x322ac.
Definition RETPC : Z := 0x346d8.

Definition DATA_AT : Z := 0x3492c.              (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IT_def : itab := mk_itab_ranges USEGS [(ENTRY, 2464%nat); (DATA_AT, 15%nat)].
Definition IT : itab := Eval vm_compute in IT_def.
Lemma IT_eq : IT = IT_def. Proof. vm_cast_no_check (@eq_refl itab IT_def). Qed.
Lemma IT_ok : itab_sound USEGS IT. Proof. rewrite IT_eq. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regs0 : list expr := sr_upd (ELit 0 :: map EVar (seq 0 31)) 4 (ELit (g_tp GUBSAN)).
Definition e_sp : expr := EVar 1.
Definition G : expr := EVar 9.          (* [comment removed for export] *)
Definition OBJ : expr := EVar 12.       (* [comment removed for export] *)
Definition DEPTH : expr := EVar 14.     (* [comment removed for export] *)
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition BSZ : expr := EVar 33.       (* [comment removed for export] *)
Definition IX : expr := EVar 34.
Definition INLO : expr := EVar 35.

Definition EEND : expr := eadd INLO BSZ.
Definition NXF : nat := 39.
Definition FR : Z := 192.
Definition SK : Z := 8192 + 192.
Definition XD : expr := eaddz (escale (- FR) DEPTH) (SK + FR * 256).
Definition XDMAX : Z := SK + FR * 256.          (* [comment removed for export] *)
Definition SLO : expr := eadd (eaddz e_sp (- XDMAX)) (escale FR DEPTH).   (* [comment removed for export] *)
Definition FLOOR : list amap := [AM SLO (ELit 0) KRW].                    (* [comment removed for export] *)

Definition IXMAX : Z := 32 * INSZ.
Definition CAPMAX : Z := 8 * INSZ.
Definition IXHI2 : Z := BIG + 2 * INSZ + 64.
Definition iixE (ito ix err : expr) : kentry :=
  KRange (esub (eadd (escale 24 ito) (escale IXMAX err)) ix) 0 (24 * INSZ + 256 * IXMAX).
Definition RELHI : Z := 24 * INSZ + 256 * IXMAX.
Definition rel (ito ix : expr) (lo : Z) : kentry := KRange (esub (escale 24 (esub ito ITO)) (esub ix IX)) lo RELHI.
Definition relE (ito ix err : expr) (lo : Z) : kentry :=
  KRange (esub (eadd (escale 24 (esub ito ITO)) (escale IXMAX err)) (esub ix IX)) lo RELHI.
Definition capE (ix ito a err : expr) : kentry :=
  KRange (esub (eaddz (eadd (eadd (escale 4 ix) (escale 8 ito)) (escale CAPMAX err)) CAPK) (escale 8 a)) 0 (4 * IXMAX + 8 * INSZ + CAPK + 256 * CAPMAX).
(* [comment removed for export] *)
Definition placement (d a : expr) : list kentry :=
  [ KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI;
    KDisj (SA d 0) (escale 8 a) (SA SLO 0) (ELit (XDMAX + WSTK)) ].   (* [comment removed for export] *)
Definition strLc (ix ito err d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capE ix ito a err;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (HI47 - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) HI47; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 112); KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24);
    KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ; img_apart d 0 (escale 8 a) ].
Definition strL (ix ito err d s a : expr) : list kentry := placement d a ++ strLc ix ito err d s a.
Definition strS (s : expr) : list kentry := [ KWord (SA OBJ 0) 1 (escale 2 s); KRange s 0 22 ].
Definition str (m : smode) (ix ito err : expr) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strL ix ito err (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition strc (m : smode) (ix ito err : expr) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strLc ix ito err (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
(* [comment removed for export] *)
Definition n13 (t : acs) (k : plan) : plan := match a_vis t with [(b, _)] => PExt 13 [b] k | _ => k end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.

Definition kn_fixed : list kentry :=
  [ KRange G CEIL (HI47 - 112); KAlign G 8; KWr (SA G 0) (ELit 4); KWr (SA G 96) (ELit 16); KWord (SA G 88) 8 EEND;
    KWr (SA G 32) (ELit 4); KUnk (SA G 32) (ELit 4);
    KRange OBJ CEIL (HI47 - 24); KAlign OBJ 8; KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange BSZ 1 INSZ; KRange (eadd INLO BSZ) (PTRLO + 1) PTRHI; KUnk (SA INLO 0) BSZ; img_apart INLO 0 BSZ;
    KDisj (SA G 0) (ELit 112) (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BSZ (SA G 0) (ELit 112); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + SK) HI47; KRange SLO CEIL HI47; KWr (SA SLO 0) XD;
    KRange (esub G e_sp) 0 (2 ^ 62); KRange (esub OBJ e_sp) 0 (2 ^ 62);
    KDisj (SA SLO 0) XD (SA G 0) (ELit 112); KDisj (SA SLO 0) XD (SA OBJ 0) (ELit 24); KDisj (SA INLO 0) BSZ (SA SLO 0) (ELit (XDMAX + WSTK));   (* [comment removed for export] *)
    KRange ITO 0 INSZ; KRange IX 0 BIG;
    KWr (SA G 0) (ELit 112);    (* [comment removed for export] *)
    KImg 0x10000 0x75000 ].
Definition posg (mlo : Z) (ito ix err : expr) (k : Z) (ixhi : Z) : list kentry :=
  [ KWord (SA G 0) 4 err; KWord (SA G 96) 8 (eadd INLO ito); KRange ito 0 (INSZ - k); KRange (esub BSZ ito) k INSZ;
    KWord (SA G 104) 8 ix; KRange ix 0 ixhi; iixE ITO IX (ELit 0); iixE ito ix err;
    KRange (esub ito ITO) mlo INSZ ].
Definition pos0 := posg 0.
Definition pos := posg 1.
Definition kn_in (m : smode) : list kentry :=
  [ KRange DEPTH 0 256 ] ++ pos0 ITO IX (ELit 0) 0 BIG ++ strc m IX ITO (ELit 0) 36 ++ kn_fixed.   (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(G, ELit 4); (eaddz G 32, ELit 4); (eaddz G 96, ELit 16); (OBJ, ELit 24); (INLO, BSZ)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) FLOOR 0 XDMAX 0 vs WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition regs_in : list expr := sr_upd (sr_upd (sr_upd regs0 11 (eaddz G 96)) 12 (eaddz G 88)) 14 (eaddz G 104).
Definition tin (m : smode) : acs := mkcs ENTRY regs_in (kn_in m) NXF (vis m 36).

Definition xERR := EVar 39. Definition xITO := EVar 40. Definition xIX := EVar 41.
Definition XSTR : nat := 42. Definition XLO : nat := 45.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regs0 clobbered XLO.
Definition kn_out (m : smode) : list kentry :=
  [ KRange xERR 0 255; relE xITO xIX xERR 1; KRange (eadd (esub xITO ITO) xERR) 1 (INSZ + 255) ]
  ++ pos0 xITO xIX xERR 0 IXMAX ++ strc m xIX xITO xERR XSTR ++ kn_fixed.      (* [comment removed for export] *)
Definition tout (m : smode) : acs := mkcs RETPC regs_out (kn_out m) (XLO + 15)%nat (vis m XSTR).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 4.
Definition ce2 (m : smode) : gcallee2 := GCE2 NXF (tin m) [tout MS] [tout ML] BCAP CCAP.
Definition ceL1 : gcallee := GCE NXF (tin ML) [tout ML; tout ML] BCAP CCAP.
Definition ce (m : smode) : gcallee := match m with MS => c2_merged (ce2 MS) | ML => ceL1 end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AAcfg (k : nat) : GuAA.acfg :=
  nth k [GuAAT.cfg_i8; GuAAT.cfg_i16; GuAAT.cfg_i32; GuAAT.cfg_i64; GuAAT.cfg_u8; GuAAT.cfg_u16; GuAAT.cfg_u32; GuAAT.cfg_u64; GuAAT.cfg_f32; GuAAT.cfg_f64] GuAAT.cfg_i8.
Definition WAcfg (k : nat) : GuWA.acfg :=
  nth k [GuWAT.cfg_i8; GuWAT.cfg_i16; GuWAT.cfg_i32; GuWAT.cfg_i64; GuWAT.cfg_u8; GuWAT.cfg_u16; GuWAT.cfg_u32; GuWAT.cfg_u64; GuWAT.cfg_f32; GuWAT.cfg_f64] GuWAT.cfg_i8.
Definition AAL1 (c : GuAA.acfg) : gcallee := GCE GuAA.NXF (GuAA.tin c ML) [GuAA.tout c ML; GuAA.tout c ML] GuAA.BCAP GuAA.CCAP.
Definition WAL1 (c : GuWA.acfg) : gcallee := GCE GuWA.NXF (GuWA.tin c ML) [GuWA.tout c ML; GuWA.tout c ML] GuWA.BCAP GuWA.CCAP.
Definition NUML1 (B : Z) : gcallee := GCE GuNumT.NXF (GuNumT.tin ML B) [GuNumT.tout ML B; GuNumT.tout ML B] GuNumT.BCAP GuNumT.CCAP.
Definition CT0 (id : nat) : option gcallee :=
  match id with
  | 203%nat => Some EscU.ceL1 | 223%nat => Some (NUML1 GuNumT.BNU) | 233%nat => Some (NUML1 GuNumT.BNI)
  | _ => if (Nat.leb 310 id && Nat.ltb id 320)%bool then Some (AAL1 (AAcfg (id - 310)))
         else if (Nat.leb 330 id && Nat.ltb id 340)%bool then Some (WAL1 (WAcfg (id - 330))) else None
  end.
Definition CTs (id : nat) : option gcallee := if Nat.eqb id 213 then Some ceL1 else CT0 id.
Definition XN (m : smode) : nat -> list expr -> acs -> option acs :=
  match m with
  | ML => XNr USEGS IT AUBSAN GUBSAN NXF BCAP CCAP 213 14 ceL1 CT0
  | MS => XNc USEGS IT AUBSAN NXF GUBSAN BCAP CCAP CTs
  end.
Definition CT2 (id : nat) : option gcallee2 :=
  match id with
  | 200%nat => Some (EscU.ce2 MS) | 220%nat => Some (GuNumT.ce2 MS GuNumT.BNU) | 230%nat => Some (GuNumT.ce2 MS GuNumT.BNI)
  | _ => if (Nat.leb 300 id && Nat.ltb id 310)%bool then Some (GuAA.ce2 (AAcfg (id - 300)) MS)
         else if (Nat.leb 320 id && Nat.ltb id 330)%bool then Some (GuWA.ce2 (WAcfg (id - 320)) MS) else None
  end.
Definition XB (m : smode) : nat -> list expr -> acs -> option (acs * acs) :=
  match m with
  | MS => XBr USEGS AUBSAN GUBSAN NXF BCAP CCAP 14 210 (ce2 MS) CT2
  | ML => XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP CT2
  end.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 20000.
Definition BFUEL : nat := 1000.
Definition DPATH := dpath USEGS IT AUBSAN (XN ML) (XB ML) BFUEL.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-96)) 8 (EVar 25);
    KWord (SA e_sp (-104)) 8 (EVar 26) ].
Definition TAGv : expr := EExt false 0 1 (EVar 39).          (* [comment removed for export] *)
Definition TAG7 : expr := EAlu Instr.ALU_AND TAGv (ELit 7).
Definition hv_emit : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_emit (a0 : expr) (ss : list expr) (v : nat) : list expr :=
  let r := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
             2 (eaddz e_sp (- FR))) 8 (eaddz G 104)) 9 OBJ) 18 G) 19 (eaddz G 96)) 20 (eaddz G 88)) 10 a0 in
  let r := fold_left (fun r p => sr_upd r (fst p) (snd p)) (combine [21; 22; 23; 24; 25; 26; 27]%nat ss) r in
  sr_havoc r hv_emit v.
Definition regs_free (ss : list expr) (v : nat) : list expr :=
  let r := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
             2 (eaddz e_sp (- FR))) 8 (eaddz G 104)) 9 OBJ) 18 G) 19 (eaddz G 96)) 20 (eaddz G 88) in
  let r := fold_left (fun r p => sr_upd r (fst p) (snd p)) (combine [21; 22; 23; 24; 25; 26; 27]%nat ss) r in
  sr_havoc r (10%nat :: hv_emit) v.
Definition room (m : smode) (req : expr) (v : nat) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) req) 0 22]
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz req 1)) 0 (8 * AHI); KRange (esub (EVar (1 + v)) req) 0 (8 * AHI)]
  end.
Definition JS_geng (psg : expr -> expr -> expr -> Z -> Z -> list kentry) (m : smode) (p : Z) (err ito ix a0 : expr) (k rlo : Z) (ss : list expr) (extra : list kentry) (v : nat) : acs :=
  mkcs p (regs_emit a0 ss (3 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; rel ito ix rlo] ++ extra
        ++ psg ito ix err k BIG ++ str m ix ito err v ++ kn_fixed)
       (18 + v)%nat (vis m v).
Definition JS_gen := JS_geng pos.
Definition JS_emit0 (m : smode) (p : Z) (err ito ix req : expr) (k rlo : Z) (ss : list expr) (extra : list kentry) (v : nat) : acs :=
  JS_geng pos0 m p err ito ix ix k rlo ss (room m req v ++ extra) v.
Definition JS_emit (m : smode) (p : Z) (err ito ix req : expr) (k rlo : Z) (ss : list expr) (extra : list kentry) (v : nat) : acs :=
  JS_gen m p err ito ix ix k rlo ss (room m req v ++ extra) v.
Definition TP : expr := ELit (g_tp GUBSAN).
Definition DUM : expr := ELit 0.
Definition RSZ (m : smode) (v : nat) : list expr :=
  match m with MS => [ELit 0; EVar v] | ML => [ELit 1; EVar v; EVar (2 + v); EVar (1 + v)] end.
(* [comment removed for export] *)
Definition ENSURE (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j (match m with MS => [(JS MS, k MS); (JS ML, k ML)] | ML => [(JS ML, k ML)] end) lo
    (PRun [bpc] (PBranch
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j))))
       (PRun [back] (PMerge j)))).
(* [comment removed for export] *)
Definition ENSURE' (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j (match m with MS => [(JS MS, k MS); (JS ML, k ML)] | ML => [(JS ML, k ML)] end) lo
    (PRun [bpc] (PBranch
       (PRun [back] (PMerge j))
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j)))))).
(* [comment removed for export] *)
Definition ENSUREL (j : nat) (m : smode) (sv : nat) (JS : smode -> acs) (lo : nat) (bpc back : Z) (k : smode -> plan) : plan :=
  PViaM j [(JS ML, k ML)] lo
    (PRun [bpc] (PBranch
       (PRun [] (PExt2 31 (RSZ m sv) (PRun [back] (PMerge j)) (PRun [back] (PMerge j))))
       (PRun [back] (PMerge j)))).

Definition EXIT (m : smode) : plan := PRun [] (PHandoffW (match m with MS => 0 | ML => 1 end) []).
Definition ERR_EXIT (m : smode) : plan := EXIT m.
(* [comment removed for export] *)
Definition CALL (m : smode) (idS idL : nat) (args : list expr) (k : smode -> plan) : plan :=
  match m with MS => PExt2 idS args (k MS) (k ML) | ML => PExt idL args (k ML) end.
Definition ESC_ARGS (ito n ix : expr) (sv : nat) : list expr := [TP; DUM; ito; n; BSZ; ix; INLO; EVar sv; EVar (1 + sv); EVar (2 + sv)].
Definition NUM_ARGS (m : smode) (ito ix : expr) (sv : nat) (tagv : expr) : list expr :=
  [TP; DUM; DUM; DUM; ito; esub BSZ ito; ix] ++
  (match m with MS => [EVar sv; DUM; DUM] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end) ++ [ELit 0; INLO; tagv].
Definition SELF_ARGS (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; DUM; DUM; ito; DUM; BSZ; ix; INLO; EVar sv; EVar (1 + sv); EVar (2 + sv)].
Definition str3 (m : smode) (sv : nat) : list expr :=
  match m with MS => [EVar sv; DUM; DUM] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end.
Definition AA_ARGS (m : smode) (ito ix nv : expr) (sv : nat) : list expr :=
  [TP; DUM; G; OBJ; ito; esub BSZ ito; ix] ++ str3 m sv ++ [ELit 0; INLO; nv].
Definition WA_ARGS (m : smode) (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; G; OBJ; ito; esub BSZ ito; ix] ++ str3 m sv ++ [ELit 0; INLO].
(* [comment removed for export] *)
Definition HOLE (c : nat) (m : smode) : nat := (9 + 2 * c + match m with MS => 0 | ML => 1 end)%nat.
Definition GO (c : nat) (m : smode) : plan := PHandoffW (HOLE c m) [].
(* [comment removed for export] *)
Definition CPV (k : nat) : nat := (7 + k)%nat.   Definition CAB (k : nat) : nat := (10 + k)%nat.
Definition CKEY : nat := 13.  Definition CCOL : nat := 14.  Definition COVAL : nat := 15.  Definition COL : nat := 16.
Definition CQ1 : nat := 17.  Definition CNUM : nat := 18.  Definition CQ2 : nat := 19.  Definition CC2 : nat := 20.  Definition CNVAL : nat := 21.  Definition CNL : nat := 22.
Definition CCB1 : nat := 23.  Definition CCB2 : nat := 24.  Definition CCB3 : nat := 25.  Definition CCB4 : nat := 26.  Definition CCB5 : nat := 27.  Definition CCL : nat := 28.
Definition CPW : nat := 29.  Definition CPWA : nat := 30.
Inductive lmode := LMS | LMT | LML.   (* [comment removed for export] *)
Definition lmo (m : smode) : lmode := match m with MS => LMS | ML => LML end.
(* [comment removed for export] *)
Definition kS (lm : lmode) (c : nat) (k : smode -> plan) (m' : smode) : plan :=
  match lm, m' with LMS, ML | LMT, ML => GO c ML | _, _ => k m' end.
(* [comment removed for export] *)
Fixpoint assocn (l : list (nat * expr)) (i : nat) : option expr :=
  match l with [] => None | (j, x) :: r => if Nat.eqb i j then Some x else assocn r i end.
Fixpoint bregs (fixed : list (nat * expr)) (i n v : nat) : list expr :=
  match n with
  | O => []
  | Datatypes.S n' => match assocn fixed i with
                      | Some e => e :: bregs fixed (Datatypes.S i) n' v
                      | None => EVar v :: bregs fixed (Datatypes.S i) n' (Datatypes.S v)
                      end
  end.
Definition STDREGS : list (nat * expr) :=
  [(0, ELit 0); (2, eaddz e_sp (- FR)); (3, EVar 2); (4, TP); (8, eaddz G 104); (9, OBJ); (18, G); (19, eaddz G 96); (20, eaddz G 88)]%nat.
Definition mkregs (extra : list (nat * expr)) (v : nat) : list expr := bregs (STDREGS ++ extra) 0 32 v.
Definition posK (ito ix err : expr) (k : Z) (ixhi : Z) : list kentry :=
  [ KWord (SA G 0) 4 err; KWord (SA G 96) 8 (eadd INLO ito); KRange ito 0 (INSZ - k); KRange (esub BSZ ito) k INSZ;
    KWord (SA G 104) 8 ix; KRange ix 0 ixhi; iixE ITO IX (ELit 0);
    KRange (esub ito ITO) 1 INSZ ].
(* [comment removed for export] *)
Definition HDR4g (r : nat) (m : smode) (ld chk : Z) (tk_err : bool) (chk8 : Z) (tk8_err : bool) (jn : Z)
           (leaf : Z -> plan) : plan :=
  let fin (hl : Z) := if Z.eqb hl 8
       then PRun [chk8] (if tk8_err then PBranch (PRun [jn] (leaf hl)) (ERR_EXIT m) else PBranch (ERR_EXIT m) (PRun [jn] (leaf hl)))
       else PRun [jn] (leaf hl) in
  let arm (hl : Z) := PExt 42 [] (PRun [chk] (if tk_err then PBranch (fin hl) (ERR_EXIT m) else PBranch (ERR_EXIT m) (fin hl))) in
  PRun [ld] (PCaseReg r 0 (arm 1) (PCaseReg r 1 (arm 2) (PCaseReg r 2 (arm 4) (arm 8)))).
Definition HDR4m (r : nat) (m : smode) (ld chk : Z) (tk_err : bool) (chk8 : Z) (tk8_err : bool) (jn : Z) (j hs : nat) : plan :=
  HDR4g r m ld chk tk_err chk8 tk8_err jn (fun hl => PMergeW j [(hs, ELit hl)]).
Definition HDR4h (r : nat) (m : smode) (ld chk : Z) (tk_err : bool) (chk8 : Z) (tk8_err : bool) (jn : Z) (h hs : nat) : plan :=
  HDR4g r m ld chk tk_err chk8 tk8_err jn (fun hl => PHandoffW h [(hs, ELit hl)]).
(* [comment removed for export] *)
Definition JX (m : smode) (p : Z) (ss : list (nat * expr)) (ito ix : expr) (rlo : Z) (rq : option expr)
              (extra : list kentry) (v : nat) : acs :=
  mkcs p (mkregs ss (3 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; rel ito ix rlo] ++ extra
        ++ match rq with Some r => room m r v | None => [] end
        ++ pos ito ix (ELit 0) 0 BIG ++ str m ix ito (ELit 0) v ++ kn_fixed)
       (3 + v + (32 - length STDREGS - length ss) + 1)%nat (vis m v).
(* [comment removed for export] *)
Definition JXc (m : smode) (p : Z) (ss : list (nat * expr)) (ito ix : expr) (rlo : Z) (rq : option expr)
              (extra : list kentry) (v : nat) : acs :=
  mkcs p (mkregs ss (3 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; rel ito ix rlo] ++ extra
        ++ match rq with Some r => room m r v | None => [] end
        ++ pos ito ix (ELit 0) 0 BIG ++ strc m ix ito (ELit 0) v ++ kn_fixed)
       (3 + v + (32 - length STDREGS - length ss) + 1)%nat (vis m v).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tag7 (m : smode) : plan := EXIT m.     (* [comment removed for export] *)
Definition dispatch (m : smode) : plan :=
  let arm (k : nat) := PExt 42 [] (PHandoffW (2 + k) []) in
  PCase2 TAG7 0 (arm 0%nat) (PCase2 TAG7 1 (arm 1%nat) (PCase2 TAG7 2 (arm 2%nat) (PCase2 TAG7 3 (arm 3%nat)
  (PCase2 TAG7 4 (arm 4%nat) (PCase2 TAG7 5 (arm 5%nat) (PCase2 TAG7 6 (arm 6%nat) (PExt 42 [] (PRun [] (tag7 m))))))))).
(* [comment removed for export] *)
Definition top (m : smode) : plan :=
  n13 (tin m) (                            (* [comment removed for export] *)
  PRun [] (PBranch (EXIT m)
 (PRun [] (PBranch (EXIT m)
 (PRun [] (dispatch m)))))).
(* [comment removed for export] *)
Definition D13 (m : smode) : list dstep := match vis m 36 with [(b, _)] => [DExt 13 [b]] | _ => [] end.   (* [comment removed for export] *)
Definition p0 (m : smode) := DPATH NXF (tin m) (D13 m ++ [DRun []; DBrT; DRun []; DBrT; DRun []]) 0.
Definition ATs (k : Z) (m : smode) : acs :=      (* [comment removed for export] *)
  snd (DPATH NXF (snd (p0 m)) ((DLo TAG7 k :: (if Z.eqb k 0 then [] else [DHi TAG7 (k - 1)])) ++ [DExt 42 []]) 0).
(* [comment removed for export] *)
Definition dead (cs : acs) : acs := set_kn cs (KRange (ELit 1) 0 0 :: kn cs).
(* [comment removed for export] *)
Definition CUT (t : acs) (k : plan) : plan := PViaM 199 [(t, k)] (nxt t) (PMerge 199).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Assembly.
(* [comment removed for export] *)
Variable tagk : nat -> smode -> plan.
Variable cutT : nat -> smode -> acs.
Variable cutK : nat -> smode -> plan.
Variable live : smode -> nat -> smode -> bool.
Variable ncut : nat.
Definition cut_entry (w : smode) (c : nat) (m : smode) : acs * plan :=
  if live w c m then (cutT c m, if Nat.leb 7 c then CUT (cutT c m) (cutK c m) else PRun [] (cutK c m)) else (dead (cutT c m), PContraH 0).
Fixpoint cut_entries (w : smode) (c n : nat) : list (acs * plan) :=
  match n with O => [] | Datatypes.S n' => cut_entry w c MS :: cut_entry w c ML :: cut_entries w (Datatypes.S c) n' end.
Definition CUTS (w : smode) : list (acs * plan) :=
  map (fun k => (ATs (Z.of_nat k) w, PRun [] (tagk k w))) (seq 0 7) ++ cut_entries w 0 ncut.


(* [comment removed for export] *)
Definition cert_stmt (w : smode) (i : nat) : Prop :=
  match nth_error (CUTS w) i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check USEGS IT AUBSAN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (CUTS w) (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh
  | None => True
  end.
Definition top_stmt (w : smode) : Prop :=
  exists sh, gplan_ok (top w) = true /\ holes_only sh = true /\
      check USEGS IT AUBSAN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (CUTS w) 0) 0%nat BFUEL FUEL None (ce_tin (ce w)) (top w) = COk sh.


End Assembly.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JS_rbrv (v : nat) (m : smode) : acs :=
  JS_emit m 0x34658 (ELit 0) (EVar v) (EVar (1 + v)) (eaddz (EVar (1 + v)) 1) 0 2 (map EVar (seq (2 + v) 7))
          [KRange (EVar v) 0 INSZ] (9 + v).
Definition close5v (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rbrv v) v 0x34654 0x34658 EXIT.

Definition close5 (m : smode) (sv : nat) : plan := close5v 8 260 m sv.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition JS_rbre (v : nat) (m : smode) : acs :=
  mkcs 0x34658 (mkregs [(10%nat, EVar (1 + v))] (6 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange (EVar v) 0 INSZ; KRange (EVar (2 + v)) 0 24;
                  relE (EVar v) (EVar (1 + v)) (EVar (2 + v)) 2]
        ++ room m (eaddz (EVar (1 + v)) 1) (3 + v)
        ++ pos (EVar v) (EVar (1 + v)) (EVar (2 + v)) 0 BIG ++ str m (EVar (1 + v)) (EVar v) (EVar (2 + v)) (3 + v) ++ kn_fixed)
       (29 + v)%nat (vis m (3 + v)).
Definition closeE (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rbre v) v 0x34654 0x34658 EXIT.
(* [comment removed for export] *)
Definition ITOW : expr := EVar 260. Definition IXW : expr := EVar 261. Definition ERW : expr := EVar 262.
Definition JS_pw (m : smode) : acs :=
  mkcs 0x34634 (mkregs [] 266)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange ITOW 0 INSZ; KRange ERW 0 24; relE ITOW IXW ERW 22]
        ++ pos ITOW IXW ERW 0 BIG ++ strc m IXW ITOW ERW 263 ++ kn_fixed)
       290%nat (vis m 263).
Definition cont_pw (m : smode) : plan := n13 (JS_pw m) (PRun [0x34654] (closeE 102 290 m 263)).
Definition post_w (m : smode) : plan :=      (* [comment removed for export] *)
  match m with MS => PViaM 101 [(JS_pw MS, cont_pw MS)] 260 (PRun [0x34634] (PMerge 101)) | ML => PRun [0x34634] (GO CPW ML) end.

(* [comment removed for export] *)
Definition JS_rbrAv (v : nat) (m : smode) : acs :=
  JX m 0x34374 [(11%nat, EVar (1 + v))] (EVar v) (EVar (1 + v)) 2 (Some (eaddz (EVar (1 + v)) 1)) [KRange (EVar v) 0 INSZ] (2 + v).
Definition close5Av (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rbrAv v) v 0x34370 0x34374 EXIT.
     (* [comment removed for export] *)
Definition JS_rbrAe (v : nat) (m : smode) : acs :=
  mkcs 0x34374 (mkregs [(11%nat, EVar (1 + v))] (6 + v))
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange (EVar v) 0 INSZ; KRange (EVar (2 + v)) 0 24;
                  relE (EVar v) (EVar (1 + v)) (EVar (2 + v)) 2]
        ++ room m (eaddz (EVar (1 + v)) 1) (3 + v)
        ++ pos (EVar v) (EVar (1 + v)) (EVar (2 + v)) 0 BIG ++ str m (EVar (1 + v)) (EVar v) (EVar (2 + v)) (3 + v) ++ kn_fixed)
       (29 + v)%nat (vis m (3 + v)).
Definition closeEA (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rbrAe v) v 0x34370 0x34374 EXIT.
Definition JS_pwA (m : smode) : acs :=
  mkcs 0x34350 (mkregs [] 266)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange ITOW 0 INSZ; KRange ERW 0 24; relE ITOW IXW ERW 22]
        ++ pos ITOW IXW ERW 0 BIG ++ strc m IXW ITOW ERW 263 ++ kn_fixed)
       290%nat (vis m 263).
Definition cont_pwA (m : smode) : plan := n13 (JS_pwA m) (PRun [0x34370] (closeEA 102 290 m 263)).
Definition post_wA (m : smode) : plan :=     (* [comment removed for export] *)
  match m with MS => PViaM 101 [(JS_pwA MS, cont_pwA MS)] 260 (PRun [0x34350] (PMerge 101)) | ML => PRun [0x34350] (GO CPWA ML) end.

(* [comment removed for export] *)
Definition JS_rcbv (v : nat) (m : smode) : acs :=
  JX m 0x33d58 [(11%nat, EVar (1 + v))] (EVar v) (EVar (1 + v)) 2 (Some (eaddz (EVar (1 + v)) 1)) [KRange (EVar v) 0 INSZ] (2 + v).
Definition closev (j v : nat) (m : smode) (sv : nat) : plan := ENSURE' j m sv (JS_rcbv v) v 0x33d54 0x33d58 EXIT.
Definition closeo (m : smode) (sv : nat) : plan := closev 38 340 m sv.

      (* [comment removed for export] *)

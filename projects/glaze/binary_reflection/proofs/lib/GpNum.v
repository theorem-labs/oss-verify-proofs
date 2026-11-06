(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpAAT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition cfg_i8 : acfg :=
  {| c_entry := 0x33410; c_ninstr := 117; c_fr := 64; c_nsaved := 8; c_K := 1; c_hr := 8; c_wmx := 6;
     c_head := 0x33454; c_join1 := 0x3349c; c_ret := 0x335e0; c_jreg := 19; c_lits := [(20%nat, 45); (21%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpAA.OBJ); (22%nat, eaddz GpAA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x334fc; c_ixreg := 10; c_ix2pc := 0x3356c; c_ix2reg := 10 |}.
Definition cfg_i16 : acfg :=
  {| c_entry := 0x335e4; c_ninstr := 128; c_fr := 80; c_nsaved := 10; c_K := 2; c_hr := 8; c_wmx := 6;
     c_head := 0x3363c; c_join1 := 0x33694; c_ret := 0x337e0; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 45); (22%nat, 65535); (23%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpAA.OBJ); (24%nat, eaddz GpAA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x336f4; c_ixreg := 10; c_ix2pc := 0x33764; c_ix2reg := 10 |}.
Definition cfg_i32 : acfg :=
  {| c_entry := 0x337e4; c_ninstr := 112; c_fr := 80; c_nsaved := 9; c_K := 4; c_hr := 16; c_wmx := 11;
     c_head := 0x3382c; c_join1 := 0x338a0; c_ret := 0x339a0; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 44)];
     c_mregs := [(18%nat, GpAA.OBJ); (19%nat, eaddz GpAA.G 104); (20%nat, GpAA.G)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x338b4; c_ixreg := 11; c_ix2pc := 0x3392c; c_ix2reg := 10 |}.
Definition cfg_i64 : acfg :=
  {| c_entry := 0x339a4; c_ninstr := 124; c_fr := 80; c_nsaved := 9; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x339ec; c_join1 := 0x33a90; c_ret := 0x33b90; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 44)];
     c_mregs := [(18%nat, GpAA.OBJ); (19%nat, eaddz GpAA.G 104); (20%nat, GpAA.G)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x33aa4; c_ixreg := 11; c_ix2pc := 0x33b1c; c_ix2reg := 10 |}.
Definition cfg_u8 : acfg :=
  {| c_entry := 0x33b94; c_ninstr := 143; c_fr := 80; c_nsaved := 10; c_K := 1; c_hr := 8; c_wmx := 3;
     c_head := 0x33bec; c_join1 := 0x33c34; c_ret := 0x33dcc; c_jreg := 19; c_lits := [(20%nat, 99); (21%nat, 44); (22%nat, 0x177c0); (23%nat, 2 ^ 64 - 100)];
     c_mregs := [(10%nat, IXv); (18%nat, GpAA.OBJ); (24%nat, eaddz GpAA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x33ce0; c_ixreg := 11; c_ix2pc := 0x33d50; c_ix2reg := 10 |}.
Definition cfg_u16 : acfg :=
  {| c_entry := 0x33dd0; c_ninstr := 195; c_fr := 112; c_nsaved := 13; c_K := 2; c_hr := 8; c_wmx := 5;
     c_head := 0x33e4c; c_join1 := 0x33ea4; c_ret := 0x340d8; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 99); (23%nat, 624); (24%nat, 2 ^ 64 - 100); (25%nat, 0x147b); (26%nat, 0x177c0); (27%nat, 2 ^ 64 - 10000)];
     c_mregs := [(10%nat, IXv); (18%nat, GpAA.OBJ); (22%nat, eaddz GpAA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x33fd8; c_ixreg := 11; c_ix2pc := 0x34048; c_ix2reg := 10 |}.
Definition cfg_u32 : acfg :=
  {| c_entry := 0x340dc; c_ninstr := 112; c_fr := 80; c_nsaved := 9; c_K := 4; c_hr := 16; c_wmx := 10;
     c_head := 0x34124; c_join1 := 0x34198; c_ret := 0x34298; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 44)];
     c_mregs := [(18%nat, GpAA.OBJ); (19%nat, eaddz GpAA.G 104); (20%nat, GpAA.G)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x341ac; c_ixreg := 10; c_ix2pc := 0x34224; c_ix2reg := 10 |}.
Definition cfg_u64 : acfg :=
  {| c_entry := 0x3429c; c_ninstr := 124; c_fr := 80; c_nsaved := 9; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x342e4; c_join1 := 0x34388; c_ret := 0x34488; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 44)];
     c_mregs := [(18%nat, GpAA.OBJ); (19%nat, eaddz GpAA.G 104); (20%nat, GpAA.G)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x3439c; c_ixreg := 10; c_ix2pc := 0x34414; c_ix2reg := 10 |}.
Definition cfg_f32 : acfg :=
  {| c_entry := 0x33028; c_ninstr := 119; c_fr := 64; c_nsaved := 8; c_K := 4; c_hr := 21; c_wmx := 16;
     c_head := 0x3306c; c_join1 := 0x330dc; c_ret := 0x33200; c_jreg := 19; c_lits := [(20%nat, 3); (21%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpAA.OBJ); (22%nat, eaddz GpAA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x3311c; c_ixreg := 10; c_ix2pc := 0x3318c; c_ix2reg := 10 |}.
Definition cfg_f64 : acfg :=
  {| c_entry := 0x33204; c_ninstr := 131; c_fr := 64; c_nsaved := 8; c_K := 8; c_hr := 38; c_wmx := 36;
     c_head := 0x33248; c_join1 := 0x332e8; c_ret := 0x3340c; c_jreg := 19; c_lits := [(20%nat, 7); (21%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpAA.OBJ); (22%nat, eaddz GpAA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x33328; c_ixreg := 10; c_ix2pc := 0x33398; c_ix2reg := 10 |}.
End GpAAT.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpAAX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
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
  hs_sub (HScut (GpAA.ceL1 c) CUTS 1) (HScut (GpAA.ce c MS) CUTS 1).
Proof.
  intros c CUTS HL h ch H. left. exists 1%nat.
  assert (E1 : HScut (GpAA.ce c MS) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E1.
  destruct h as [|[|h]].
  - assert (E : HScut (GpAA.ceL1 c) CUTS 1 0 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - assert (E : HScut (GpAA.ceL1 c) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - exfalso. destruct CUTS as [|x [|y r]]; try discriminate HL.
    assert (E : HScut (GpAA.ceL1 c) [x] 1 (Datatypes.S (Datatypes.S h)) = None) by (destruct h as [|[|h]]; reflexivity).
    rewrite E in H. discriminate H.
Qed.
End GpAAX.
Module GpAAu16.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpAAT.cfg_u16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [0x33fd8] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q4 : expr := EMd Instr.M_MULHU VAL (ELit 0x68db8bac710cc).              (* [comment removed for export] *)
Definition r4 : expr := rem VAL q4 10000.
Definition armA (k : plan) : plan := xl (xl (fin k)).                                                                  (* [comment removed for export] *)
Definition armB (k : plan) : plan := divfact VAL (q100 VAL) 100 (zfact VAL (q100 VAL) 100 (xl (xl (xl (fin k))))).     (* [comment removed for export] *)
Definition armC (k : plan) : plan := divfact VAL q4 10000 (divfact r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xl (xl (fin k))))).  (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (PCase2 VAL 999 (armB k) (PCase2 VAL 9999 (armB k) (armC k)))).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u16_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u16_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAu16.
Module GpAAu8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpAA GpAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import GpAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpAAT.cfg_u8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF GPLAIN BCAP CCAP CT.
   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [0x33ce0] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q8 : expr := EMd Instr.M_MULHU VAL (ELit 0x28f5c28f5c28f5d).           (* [comment removed for export] *)
Definition armA (k : plan) : plan := xl (xl (fin k)).                                                (* [comment removed for export] *)
Definition armC (k : plan) : plan := divfact VAL q8 100 (zfact VAL q8 100 (xl (fin k))).             (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (armC k)).

#[local] Notation CHK m := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpAA.IT cfg) APLAIN GpAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpAA.ce cfg MS) 0 (GpAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpAA.ceL1 cfg) 0 (GpAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ceL1 cfg) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpAA.ce cfg MS) (GpAA.IT cfg) (GpAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpAA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpAA.IT_ok cfg) GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpAA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u8_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u8_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpAAu8.
Module GpNumT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition BNU : Z := 0x32810.    (* [comment removed for export] *)
Definition BNI : Z := 0x36330.    (* [comment removed for export] *)
Definition NINSTR : nat := 518.
Definition IT (B : Z) : itab := mk_itab_ranges PSEGS [(B, NINSTR)].
Lemma IT_ok : forall B, itab_sound PSEGS (IT B). Proof. intro. apply APS.mk_itab_ranges_sound. Qed.
Definition at_ (B off : Z) : Z := B + off.
Definition RETPC (B : Z) : Z := at_ B 0x748.        (* [comment removed for export] *)
Definition is_int (B : Z) : bool := Z.eqb B BNI.

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GPLAIN)).   (* [comment removed for export] *)
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
Definition FR : Z := 160.
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
    KWr (SA G 0) (ELit 112);    (* [comment removed for export] *)
    KImg 0x10000 0x71000 ].
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
End GpNumT.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpWAT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition cfg_i8 : acfg :=
  {| c_entry := 0x34a84; c_ninstr := 183; c_fr := 80; c_nsaved := 9; c_K := 1; c_hr := 8; c_wmx := 6;
     c_head := 0x34be0; c_join1 := 0x34c28; c_ret := 0x34d5c; c_jreg := 19; c_lits := [(20%nat, 45); (21%nat, 1); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpWA.OBJ); (23%nat, eaddz GpWA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x34c84; c_ixreg := 10; c_ix2pc := 0x34ce8; c_ix2reg := 10 |}.
Definition cfg_i16 : acfg :=
  {| c_entry := 0x34d60; c_ninstr := 191; c_fr := 80; c_nsaved := 10; c_K := 2; c_hr := 8; c_wmx := 6;
     c_head := 0x34ec8; c_join1 := 0x34f20; c_ret := 0x35058; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 45); (22%nat, 65535); (23%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpWA.OBJ); (24%nat, eaddz GpWA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x34f80; c_ixreg := 10; c_ix2pc := 0x34fe0; c_ix2reg := 10 |}.
Definition cfg_i32 : acfg :=
  {| c_entry := 0x3505c; c_ninstr := 178; c_fr := 80; c_nsaved := 10; c_K := 4; c_hr := 16; c_wmx := 11;
     c_head := 0x351bc; c_join1 := 0x35230; c_ret := 0x35320; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 1); (24%nat, 44)];
     c_mregs := [(18%nat, GpWA.OBJ); (19%nat, eaddz GpWA.G 104); (20%nat, GpWA.G)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x35244; c_ixreg := 11; c_ix2pc := 0x352ac; c_ix2reg := 10 |}.
Definition cfg_i64 : acfg :=
  {| c_entry := 0x35324; c_ninstr := 190; c_fr := 80; c_nsaved := 10; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x35484; c_join1 := 0x35528; c_ret := 0x35618; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 1); (24%nat, 44)];
     c_mregs := [(18%nat, GpWA.OBJ); (19%nat, eaddz GpWA.G 104); (20%nat, GpWA.G)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x3553c; c_ixreg := 11; c_ix2pc := 0x355a4; c_ix2reg := 10 |}.
Definition cfg_u8 : acfg :=
  {| c_entry := 0x3561c; c_ninstr := 211; c_fr := 96; c_nsaved := 12; c_K := 1; c_hr := 8; c_wmx := 3;
     c_head := 0x35798; c_join1 := 0x357e0; c_ret := 0x35964; c_jreg := 19; c_lits := [(20%nat, 99); (21%nat, 0x177c0); (22%nat, 0x28f5c28f5c28f5d); (23%nat, 1); (24%nat, 44); (25%nat, 2 ^ 64 - 100)];
     c_mregs := [(10%nat, IXv); (18%nat, GpWA.OBJ); (26%nat, eaddz GpWA.G 104)]; c_vw := 1; c_vhi := 255;
     c_ixpc := 0x35884; c_ixreg := 11; c_ix2pc := 0x358e4; c_ix2reg := 10 |}.
Definition cfg_u16 : acfg :=
  {| c_entry := 0x35968; c_ninstr := 258; c_fr := 112; c_nsaved := 13; c_K := 2; c_hr := 8; c_wmx := 5;
     c_head := 0x35af4; c_join1 := 0x35b4c; c_ret := 0x35d6c; c_jreg := 19; c_lits := [(20%nat, 1); (21%nat, 99); (23%nat, 624); (24%nat, 2 ^ 64 - 100); (25%nat, 0x147b); (26%nat, 0x177c0); (27%nat, 2 ^ 64 - 10000)];
     c_mregs := [(10%nat, IXv); (18%nat, GpWA.OBJ); (22%nat, eaddz GpWA.G 104)]; c_vw := 2; c_vhi := 65535;
     c_ixpc := 0x35c80; c_ixreg := 11; c_ix2pc := 0x35ce0; c_ix2reg := 10 |}.
Definition cfg_u32 : acfg :=
  {| c_entry := 0x35d70; c_ninstr := 178; c_fr := 80; c_nsaved := 10; c_K := 4; c_hr := 16; c_wmx := 10;
     c_head := 0x35ed0; c_join1 := 0x35f44; c_ret := 0x36034; c_jreg := 21; c_lits := [(22%nat, 3); (23%nat, 1); (24%nat, 44)];
     c_mregs := [(18%nat, GpWA.OBJ); (19%nat, eaddz GpWA.G 104); (20%nat, GpWA.G)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x35f58; c_ixreg := 10; c_ix2pc := 0x35fc0; c_ix2reg := 10 |}.
Definition cfg_u64 : acfg :=
  {| c_entry := 0x36038; c_ninstr := 190; c_fr := 80; c_nsaved := 10; c_K := 8; c_hr := 24; c_wmx := 20;
     c_head := 0x36198; c_join1 := 0x3623c; c_ret := 0x3632c; c_jreg := 21; c_lits := [(22%nat, 7); (23%nat, 1); (24%nat, 44)];
     c_mregs := [(18%nat, GpWA.OBJ); (19%nat, eaddz GpWA.G 104); (20%nat, GpWA.G)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x36250; c_ixreg := 10; c_ix2pc := 0x362b8; c_ix2reg := 10 |}.
Definition cfg_f32 : acfg :=
  {| c_entry := 0x3448c; c_ninstr := 185; c_fr := 80; c_nsaved := 9; c_K := 4; c_hr := 21; c_wmx := 16;
     c_head := 0x345e8; c_join1 := 0x34658; c_ret := 0x3476c; c_jreg := 19; c_lits := [(20%nat, 3); (21%nat, 1); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpWA.OBJ); (23%nat, eaddz GpWA.G 104)]; c_vw := 4; c_vhi := 0;
     c_ixpc := 0x34698; c_ixreg := 10; c_ix2pc := 0x346f8; c_ix2reg := 10 |}.
Definition cfg_f64 : acfg :=
  {| c_entry := 0x34770; c_ninstr := 197; c_fr := 80; c_nsaved := 9; c_K := 8; c_hr := 38; c_wmx := 36;
     c_head := 0x348cc; c_join1 := 0x3496c; c_ret := 0x34a80; c_jreg := 19; c_lits := [(20%nat, 7); (21%nat, 1); (22%nat, 44)];
     c_mregs := [(10%nat, IXv); (18%nat, GpWA.OBJ); (23%nat, eaddz GpWA.G 104)]; c_vw := 8; c_vhi := 2 ^ 64 - 1;
     c_ixpc := 0x349ac; c_ixreg := 10; c_ix2pc := 0x34a0c; c_ix2reg := 10 |}.
End GpWAT.
Module GpWAX.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
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
  hs_sub (HScut (GpWA.ceL1 c) CUTS 1) (HScut (GpWA.ce c MS) CUTS 1).
Proof.
  intros c CUTS HL h ch H. left. exists 1%nat.
  assert (E1 : HScut (GpWA.ce c MS) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E1.
  destruct h as [|[|h]].
  - assert (E : HScut (GpWA.ceL1 c) CUTS 1 0 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - assert (E : HScut (GpWA.ceL1 c) CUTS 1 1 = Some (tout c ML)) by reflexivity. rewrite E in H. exact H.
  - exfalso. destruct CUTS as [|x [|y r]]; try discriminate HL.
    assert (E : HScut (GpWA.ceL1 c) [x] 1 (Datatypes.S (Datatypes.S h)) = None) by (destruct h as [|[|h]]; reflexivity).
    rewrite E in H. discriminate H.
Qed.
End GpWAX.
Module GpWAu16.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpWAT.cfg_u16.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [0x35c80] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q4 : expr := EMd Instr.M_MULHU VAL (ELit 0x68db8bac710cc).
Definition r4 : expr := rem VAL q4 10000.
Definition armA (k : plan) : plan := xl (xl (fin k)).
Definition armB (k : plan) : plan := divfact VAL (q100 VAL) 100 (zfact VAL (q100 VAL) 100 (xl (xl (xl (fin k))))).
Definition armC (k : plan) : plan := divfact VAL q4 10000 (divfact r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xl (xl (fin k))))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (PCase2 VAL 999 (armB k) (PCase2 VAL 9999 (armB k) (armC k)))).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u16_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u16_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAu16.
Module GpWAu8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GpWA GpWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import GpWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := GpWAT.cfg_u8.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF GPLAIN BCAP CCAP CT.
   (* [comment removed for export] *)
Definition fin (k : plan) : plan := PRun [0x35884] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q8 : expr := EMd Instr.M_MULHU VAL (ELit 0x28f5c28f5c28f5d).
Definition armA (k : plan) : plan := xl (xl (fin k)).
Definition armC (k : plan) : plan := divfact VAL q8 100 (zfact VAL q8 100 (xl (fin k))).
Definition elem (m : smode) (k : plan) : plan := PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (armC k)).

#[local] Notation CHK m := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GpWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check PSEGS (GpWA.IT cfg) APLAIN GpWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GpWA.ce cfg MS) 0 (GpWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GpWA.ceL1 cfg) 0 (GpWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GpWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS PSEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT PSEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound PSEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts PSEGS IT APLAIN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 PSEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GPLAIN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GPLAIN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ceL1 cfg) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX PSEGS APLAIN plain_in_hull plain_hull_ok [] GPLAIN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx PSEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj plain_G_ro_img plain_G_img_ceil
            (GpWA.ce cfg MS) (GpWA.IT cfg) (GpWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound PSEGS (GpWA.IT cfg) APLAIN plain_in_hull plain_hull_ok (GpWA.IT_ok cfg) GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact (GpWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound PSEGS APLAIN plain_in_hull plain_hull_ok GpWA.NXF [] GPLAIN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GpWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u8_callee_S : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u8_callee_L1 : callee_contract PSEGS [] GPLAIN fx_ok RZ AINVH (GpWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GpWAu8.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GpCommon GpTc32 GpU32 GpI32 GpU64 GpI64 GpWFT GpWDT GpW16.
Export GpNumT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 130 then Some GpTc32.ce else if Nat.eqb id 132 then Some GpI32.ce else if Nat.eqb id 133 then Some GpU32.ce
  else if Nat.eqb id 134 then Some GpI64.ce else if Nat.eqb id 135 then Some GpU64.ce
  else if Nat.eqb id 136 then Some GpWFT.ce else if Nat.eqb id 137 then Some GpWDT.ce
  else if Nat.eqb id 142 then Some GpI32.ceS else if Nat.eqb id 143 then Some GpU32.ceS else None.
Definition B16 (B : Z) : Z := if is_int B then B16I else B16U.
Definition CT2 (B : Z) (id : nat) : option gcallee2 :=
  if Nat.eqb id 138 then Some (GpW16.ce2 ML (B16 B)) else if Nat.eqb id 139 then Some (GpW16.ce2 MS (B16 B)) else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNc PSEGS (IT B) APLAIN NXF GPLAIN BCAP CCAP CT.
(* [comment removed for export] *)
Definition CT1 (B : Z) (id : nat) : option gcallee := if Nat.eqb id 148 then Some (GpW16.ceL1 (B16 B)) else CT id.
Definition XN1 (B : Z) : nat -> list expr -> acs -> option acs := XNc PSEGS (IT B) APLAIN NXF GPLAIN BCAP CCAP (CT1 B).
Definition XB (B : Z) : nat -> list expr -> acs -> option (acs * acs) := XBc PSEGS APLAIN NXF GPLAIN BCAP CCAP (CT2 B).
Definition FUELN : nat := 4000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CAPB : expr := eaddz (eadd (escale 4 IX) (escale 8 (esub IT0 INLO))) CAPK.
Definition RSZ (m : smode) : list expr := match m with MS => [ELit 0; D; CAPB] | ML => [ELit 1; D; A; S; CAPB] end.
Definition B2 : nat := 130.           (* [comment removed for export] *)
Definition BMP : nat := 170.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exitD (m : smode) (K : Z) (XI a : expr) : plan :=
  let it' := eaddz IT0 K in let cons' := esub it' INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - K))                   (* [comment removed for export] *)
  (PFactLe XI (escale 24 cons') IXHI
  (PFactLe (esub (escale 24 cons') XI) (escale 24 cons') BIG
  (match m with                  (* [comment removed for export] *)
   | ML => PFactLe (capexpr XI it' INLO a) (eaddz (escale 104 cons') CAPK) CAPHI (PHandoffW 1 [(41%nat, ELit K)])
   | MS => PHandoffW 0 [(41%nat, ELit K)]
   end)))).
(* [comment removed for export] *)
Definition pre (k : plan) : plan := PRun [] (PExt 42 [] (PRun [] k)).
Definition ERRX (m : smode) : plan := PRun [] (PHandoffW (hole m) [(41%nat, ELit 0)]).      (* [comment removed for export] *)
Definition EXITERR (m : smode) : plan := pre (ERRX m).                                        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grown (k : plan) : plan :=
  PFact (KDisj (SA (EVar 130) 0) (escale 8 (EVar 131)) (SA e_sp (- FRK)) (ELit (FRK + WSTK)))
  (PFact (KDisj (SA (EVar 130) 0) (escale 8 (EVar 131)) (SA G 0) (ELit 112)) k).
(* [comment removed for export] *)
Definition NSZ (hr : Z) : expr := eaddz (escale 2 IX) (2 * hr).
Definition diamond (m : smode) (hr : Z) (cont : smode -> expr -> expr -> expr -> plan) : plan :=
  match m with
  | ML => PBranch (cont ML D S A)
                  (PRun [] (PBump B2 (PExt2 31 (RSZ ML) (cont ML D (NSZ hr) A) (grown (cont ML (EVar 130) (NSZ hr) (EVar 131))))))
  | MS => if Z.leb 23 hr then PBump B2 (PExt2 31 (RSZ MS) (PContraH 0) (grown (cont ML (EVar 130) (NSZ hr) (EVar 131))))
          else PBranch (cont MS D D A)
                       (PRun [] (PBump B2 (PExt2 31 (RSZ MS)
                                   (if Z.leb 12 hr then PContraH 0
                                    else PCase2 IX (11 - hr) (cont MS D (NSZ hr) A) PContra)   (* [comment removed for export] *)
                                   (grown (cont ML (EVar 130) (NSZ hr) (EVar 131))))))
  end.
(* [comment removed for export] *)
Definition room (m : smode) (hr : Z) (s a : expr) (k : plan) : plan :=
  match m with ML => PFactVia (esub (escale 8 a) IX) (esub s IX) (hr + 1) (2 ^ 40) k | MS => k end.
(* [comment removed for export] *)
Definition bufimg (m : smode) (d : expr) (w : Z) (k : plan) : plan :=
  PFact (img_apart (match m with ML => eadd d IX | MS => eadd (eaddz OBJ 1) IX end) 0 (ELit w)) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JLO : nat := 121.
Definition D1 : expr := EVar 121.  Definition S1 : expr := EVar 122.  Definition A1 : expr := EVar 123.
Definition JRS : nat := 125.        (* [comment removed for export] *)
Definition JNX : nat := 150.
Definition roomJ (m : smode) (hr : Z) : list kentry :=
  match m with MS => [KRange (esub D1 IX) hr (2 ^ 40)] | ML => [KRange (esub S1 IX) hr (2 ^ 37)] end.
Definition csregsJ : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition jhavoc (k : Z) : list nat := if (Z.eqb k 9 || Z.eqb k 10 || Z.eqb k 13 || Z.eqb k 14)%bool then 10%nat :: csregsJ else csregsJ.
(* [comment removed for export] *)
Fixpoint ehas (lo hi : nat) (e : expr) : bool :=
  match e with
  | EVar n => (Nat.leb lo n && Nat.ltb n hi)%bool
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ehas lo hi a || ehas lo hi b)%bool
  | EExt _ _ _ a => ehas lo hi a
  | _ => false
  end.
Definition ahas (lo hi : nat) (a : saddr) : bool := ehas lo hi (a_base a).
Definition khas (lo hi : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => ahas lo hi a || ehas lo hi v
  | KZero a n | KWr a n | KUnk a n | KBlob a n _ | KFill a n _ => ahas lo hi a || ehas lo hi n
  | KImg _ _ => false
  | KAlign x _ | KRange x _ _ => ehas lo hi x
  | KDisj a1 n1 a2 n2 => ahas lo hi a1 || ehas lo hi n1 || ahas lo hi a2 || ehas lo hi n2
  end%bool.
(* [comment removed for export] *)
Definition ktp (K : kentry) : bool := match K with KWord a _ _ => expr_eqb (a_base a) TP | _ => false end.
(* [comment removed for export] *)
Inductive jstep : Type := JD (d : dstep) | JB (n : nat).
Definition ITU : itab := IT BNU.  Definition ITI : itab := IT BNI.
Definition XNU := XN BNU.  Definition XNI := XN BNI.  Definition XBU := XB BNU.  Definition XBI := XB BNI.
Fixpoint jpath0 (it : itab) (xn : nat -> list expr -> acs -> option acs) (xb : nat -> list expr -> acs -> option (acs * acs))
         (cs : acs) (l : list jstep) : acs :=
  match l with
  | [] => cs
  | JD d :: r => match dgo PSEGS it APLAIN xn xb BFUEL NXF cs d with Some c => jpath0 it xn xb c r | None => cs end
  | JB n :: r => match APC.node_bump cs n with Some c => jpath0 it xn xb c r | None => cs end
  end.
Definition jpath (B : Z) (cs : acs) (l : list jstep) : acs :=
  if Z.eqb B BNU then jpath0 ITU XNU XBU cs l else jpath0 ITI XNI XBI cs l.
(* [comment removed for export] *)
Definition JSJ (r0 : acs) (k J hr : Z) (m : smode) : acs :=
  mkcsV J (sr_havoc (s_regs (a_ss r0)) (jhavoc k) JRS)
        (roomJ m hr ++ str m IX IT0 121 ++ filter (fun K => negb (khas 34 37 K || ktp K)) (kn r0)) JNX (vis m 121).
(* [comment removed for export] *)
Definition mrgJ (J : Z) : plan := PRun [J] (PMerge 1).
Definition diamondJ (m : smode) (hr J : Z) : plan :=
  match m with
  | ML => PBranch (mrgJ J) (PRun [] (PBump B2 (PExt2 31 (RSZ ML) (mrgJ J) (grown (mrgJ J)))))
  | MS => PBranch (mrgJ J)
                  (PRun [] (PBump B2 (PExt2 31 (RSZ MS)
                              (if Z.leb 12 hr then PContraH 0 else PCase2 IX (11 - hr) (mrgJ J) PContra)
                              (grown (mrgJ J)))))
  end.
(* [comment removed for export] *)
Definition tagsteps (k : Z) : list jstep := (if Z.eqb k 0 then [] else [JD (DHi TAGV (8 * k - 1))]) ++ [JD (DLo TAGV (8 * k + 7))].
Definition pre3 : list jstep := [JD (DRun []); JD (DExt 42 []); JD (DRun [])].
Definition intpre (B stpc K : Z) : list jstep := [JD (DHi REM (K - 1)); JD (DRun [at_ B stpc]); JB 120; JD (DExt 44 [ELit 11]); JD (DRun [])].
Definition armpre (B k : Z) : list jstep :=
  tagsteps k ++ pre3 ++
  match k with
  | 1 | 2 => [JD (DHi REM 0); JB 110; JD (DRun [])]
  | 5 => [JD (DHi REM 1); JB 110; JD (DRun [])]
  | 8 => [JD (DHi REM 3); JD (DRun [])]
  | 12 => [JD (DHi REM 7); JD (DRun [])]
  | 9 => intpre B 0x3c8 4
  | 10 => intpre B 0x36c 4
  | 13 => intpre B 0x294 8
  | 14 => intpre B 0x1f8 8
  | _ => []
  end.
(* [comment removed for export] *)
Definition JR0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  let s := jpath B (tin m B) (armpre B k) in let J := pc s + 4 in (J, set_kn (jpath B s [JD DBrF; JD (DRun [J])]) (kn s)).
  (* [comment removed for export] *)
Definition DARMS : list Z := [1; 2; 5; 8; 9; 10; 12; 13; 14].
Definition JR0_UL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU ML k)) DARMS.
Definition JR0_US : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU MS k)) DARMS.
Definition JR0_IL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI ML k)) DARMS.
Definition JR0_IS : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI MS k)) DARMS.
Definition JR0L (B : Z) (m : smode) : list (Z * (Z * acs)) :=
  if Z.eqb B BNU then match m with ML => JR0_UL | MS => JR0_US end else match m with ML => JR0_IL | MS => JR0_IS end.
Definition jr0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  match find (fun p => Z.eqb (fst p) k) (JR0L B m) with Some (_, x) => x | None => (0, tin m B) end.
(* [comment removed for export] *)
Definition joinJ (B : Z) (m : smode) (k : Z) (hr : Z) (cont : smode -> expr -> expr -> expr -> plan) : plan :=
  (* [comment removed for export] *)
  match m with
  | MS => if Z.leb 23 hr then diamond m hr cont else
      PViaM 1 [(JSJ (snd (jr0 B MS k)) k (fst (jr0 B MS k)) hr MS, cont MS D1 D1 A1); (JSJ (snd (jr0 B MS k)) k (fst (jr0 B MS k)) hr ML, cont ML D1 S1 A1)]
              JLO (diamondJ MS hr (fst (jr0 B MS k)))
  | ML => PViaM 1 [(JSJ (snd (jr0 B ML k)) k (fst (jr0 B ML k)) hr ML, cont ML D1 S1 A1)] JLO (diamondJ ML hr (fst (jr0 B ML k)))
  end.

Section Arms.
Variable B : Z.
Definition o (x : Z) : Z := at_ B x.

(* [comment removed for export] *)
Definition VB0 : expr := EExt false 0 1 (EVar 110).
Definition VB1 : expr := EExt false 0 1 (EVar 111).
Definition HV : expr := EVar 120.
Definition X44 (r : Z) (k : plan) : plan := PExt 44 [ELit r] k.

(* [comment removed for export] *)
Definition i8_cont (m : smode) (d s a : expr) : plan :=
  room m 8 s a (PCase2 VB0 127
    (PRun [] (PBump BMP (PExt 130 [] (PRun [] (exitD m 1 (eadd IX (EVar 199)) a)))))
    (PRun [] (PBump BMP (PExt 130 [] (PRun [] (exitD m 1 (eaddz (eadd IX (EVar 199)) 1) a)))))).
Definition arm_i8 (m : smode) : plan := pre (PCase2 REM 0 (ERRX m) (PBump 110 (PRun [] (joinJ B m 1 8 i8_cont)))).
(* [comment removed for export] *)
Definition q8 : expr := EMd Instr.M_MULHU VB0 (ELit 0x28f5c28f5c28f5d).
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition u8_cont (m : smode) (d s a : expr) : plan :=
  room m 8 s a (PCase2 VB0 9 (xl (xl (PRun [] (exitD m 1 (eaddz IX 1) a))))
               (PCase2 VB0 99 (xl (xl (PRun [] (exitD m 1 (eaddz IX 2) a))))
               (divfact VB0 q8 100 (zfact VB0 q8 100 (xl (PRun [] (exitD m 1 (eaddz IX 3) a))))))).
Definition arm_u8 (m : smode) : plan := pre (PCase2 REM 0 (ERRX m) (PBump 110 (PRun [] (joinJ B m 2 8 u8_cont)))).
(* [comment removed for export] *)
Definition i16_cont (m : smode) (d s a : expr) : plan :=
  room m 8 s a (PCase2 VB1 127
    (PRun [] (PBump BMP (PExt 130 [] (PRun [] (exitD m 2 (eadd IX (EVar 199)) a)))))
    (PRun [] (PBump BMP (PExt 130 [] (PRun [] (exitD m 2 (eaddz (eadd IX (EVar 199)) 1) a)))))).
Definition arm_i16 (m : smode) : plan := pre (PCase2 REM 1 (ERRX m) (PBump 110 (PRun [] (joinJ B m 5 8 i16_cont)))).
(* [comment removed for export] *)
Definition arm_u16 (m : smode) : plan :=
  pre (PBump BMP (PExt2 (match m with ML => 138 | MS => 139 end) [ELit (g_tp GPLAIN); ELit 0; G; OBJ; ITO; REM; IX; D; S; A; ERR; INLO]
         (PRun [] (PHandoff 0)) (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition int_cont (cid cidS : nat) (K hr : Z) (m : smode) (d s a : expr) : plan :=
  room m hr s a (PRun [] (bufimg m d hr (PBump BMP (PExt (match m with ML => cid | MS => cidS end)
                                         (match m with ML => [HV; a; s; d; IX] | MS => [HV; ELit 0; s; ELit 0; IX] end)
                                         (PRun [] (exitD m K (eadd IX (EVar 194)) a)))))).
Definition arm_int (k : Z) (stpc : Z) (cid cidS : nat) (K hr : Z) (m : smode) : plan :=
  pre (PCase2 REM (K - 1) (ERRX m) (PRun [o stpc] (PBump 120 (X44 11 (PRun [] (joinJ B m k hr (int_cont cid cidS K hr))))))).
(* [comment removed for export] *)
Definition fp_cont (cid : nat) (K hr W ylo : Z) (mj : nat) (m : smode) (d s a : expr) : plan :=
  let frw := SA e_sp (- FR - ylo) in
  let buf := match m with ML => eadd d IX | MS => eadd (eaddz OBJ 1) IX end in
  room m hr s a
   (PFact (img_apart buf 0 (ELit W))
    (PFact (KDisj (SA buf 0) (ELit W) frw (ELit ylo))
    ((match m with ML => PFact (KRange buf PTRLO (objhi W)) | MS => fun k => k end)   (* [comment removed for export] *)
    (PRun [] (PBump BMP (PExt cid [] (PRun [] (exitD m K (eadd IX (EVar mj)) a)))))))).
Definition arm_fp (k : Z) (cid : nat) (K hr W ylo : Z) (mj : nat) (m : smode) : plan :=
  pre (PCase2 REM (K - 1) (ERRX m) (PRun [] (joinJ B m k hr (fp_cont cid K hr W ylo mj)))).

(* [comment removed for export] *)
Definition arm_of (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_i8 m | 2 => arm_u8 m | 5 => arm_i16 m | 6 => arm_u16 m
  | 8 => arm_fp 8 136 4 21 17 80 219 m | 9 => arm_int 9 0x3c8 132 142 4 16 m | 10 => arm_int 10 0x36c 133 143 4 16 m
  | 12 => arm_fp 12 137 8 38 38 128 259 m | 13 => arm_int 13 0x294 134 134 8 24 m | 14 => arm_int 14 0x1f8 135 135 8 24 m
  | _ => EXITERR m
  end.
Fixpoint classes (m : smode) (k : Z) (n : nat) : plan :=
  match n with
  | O => arm_of m k
  | Datatypes.S n' => PCase2 TAGV (8 * k + 7) (arm_of m k) (classes m (k + 1) n')
  end.
Definition PLAN (m : smode) : plan := classes m 0 31.
(* [comment removed for export] *)
Definition arm_u16L1 (m : smode) : plan :=
  pre (PBump BMP (PExt 148 [ELit (g_tp GPLAIN); ELit 0; G; OBJ; ITO; REM; IX; D; S; A; ERR; INLO] (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).
Definition arm_ofL1 (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_i8 m | 2 => arm_u8 m | 5 => arm_i16 m | 6 => arm_u16L1 m
  | 8 => arm_fp 8 136 4 21 17 80 219 m | 9 => arm_int 9 0x3c8 132 142 4 16 m | 10 => arm_int 10 0x36c 133 143 4 16 m
  | 12 => arm_fp 12 137 8 38 38 128 259 m | 13 => arm_int 13 0x294 134 134 8 24 m | 14 => arm_int 14 0x1f8 135 135 8 24 m
  | _ => EXITERR m
  end.
Fixpoint classesL1 (m : smode) (k : Z) (n : nat) : plan :=
  match n with
  | O => arm_ofL1 m k
  | Datatypes.S n' => PCase2 TAGV (8 * k + 7) (arm_ofL1 m k) (classesL1 m (k + 1) n')
  end.
Definition PLANL1 (m : smode) : plan := classesL1 m 0 31.   (* [comment removed for export] *)
End Arms.


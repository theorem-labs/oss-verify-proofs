(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition ENTRY : Z := 0x39180.
Definition RETPC : Z := 0x39a24.
Definition STPC : Z := 0x39a20.      (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges PSEGS [(ENTRY, 554%nat)].
Lemma IT_ok : itab_sound PSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 36.
Definition e_pv := e_a0.  Definition e_str := e_a2.  Definition e_pix := e_a3.
Definition e_v : expr := EVar 31.  Definition e_a : expr := EVar 32.  Definition e_size : expr := EVar 33.
Definition e_data : expr := EVar 34.  Definition e_ix : expr := EVar 35.
Definition e_dix : expr := eadd e_data e_ix.
Definition VBYTES : nat := 8.
Definition VMAX : Z := 2 ^ 64 - 1.
Definition WMAX : Z := 20.           (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(e_dix, ELit WMAX); (e_pix, ELit 8)].

(* [comment removed for export] *)
Definition YLO : Z := 0.
Definition kn_in : list kentry :=
  [ KRange e_v 0 VMAX; KRange e_pv PTRLO (objhi (Z.of_nat VBYTES)); KWord (SA e_pv 0) VBYTES e_v ]
  ++ sp_facts YLO ++ str_L e_str e_a e_size e_data ++
  [ KRange e_pix PTRLO (objhi 8); KWord (SA e_pix 0) 8 e_ix; KWr (SA e_pix 0) (ELit 8);
    KRange e_data PTRLO PTRHI; KRange e_ix 0 (2 ^ 40); KWr (SA e_dix 0) (ELit WMAX);
    KDisj (SA e_dix 0) (ELit WMAX) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA e_dix 0) (ELit WMAX) (SA e_str 0) (ELit 24);
    KDisj (SA e_dix 0) (ELit WMAX) (SA e_pix 0) (ELit 8);
    KDisj (SA e_pix 0) (ELit 8) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA e_pix 0) (ELit 8) (SA e_str 0) (ELit 24);
    img_apart (e_dix) 0 (ELit WMAX); KImg 0x10000 0x71000 ].
Definition tin : acs := mkcs YLO WS ENTRY regs0 kn_in NXF.

(* [comment removed for export] *)
Definition M : nat := 60.
Definition LO : nat := 61.
Definition js_regs : list expr :=
  sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_ix (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out : list kentry :=
  [ KRange (EVar M) 1 WMAX; KWord (SA e_pix 0) 8 (eadd e_ix (EVar M)); KWr (SA e_pix 0) (ELit 8);
    KWr (SA e_dix 0) (ELit WMAX) ] ++ sp_facts YLO.
Definition tout : acs := mkcs YLO WS RETPC js_regs kn_out (LO + 14)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.

(* [comment removed for export] *)
Fixpoint xloads (n : nat) (k : plan) : plan :=
  match n with O => k | S n' => PRun [STPC; RETPC] (PExt 0 [] (xloads n' k)) end.
Definition arm_tail : plan :=
  PRun [STPC; RETPC] (PBump M (PFresh 10 0 (Some e_ix) (PFact (KRange (EVar M) 1 WMAX) (PRun [RETPC] (PMerge 0))))).
Definition q8 : expr := q1e8h e_v.              Definition r8 : expr := rem e_v q8 100000000.
Definition q16 : expr := q1e8h q8.              Definition rm : expr := rem q8 q16 100000000.
Definition armA2 : plan := xloads 2 arm_tail.
Definition armA4 : plan := divfact e_v (q100 e_v) 100 (xloads 3 arm_tail).
Definition armB6 : plan := divfact e_v (q1e4a e_v) 10000 (xloads 3 arm_tail).
Definition armB8 : plan :=
  divfact e_v (q1e4b e_v) 10000 (divfact (q1e4b e_v) (q100 (q1e4b e_v)) 100 (xloads 4 arm_tail)).
Definition armC10 : plan := divfact e_v q8 100000000 (divfact r8 (q1e4b r8) 10000 (xloads 4 arm_tail)).
Definition armC12 : plan :=
  divfact e_v q8 100000000 (divfact q8 (q100 q8) 100 (divfact r8 (q1e4b r8) 10000 (xloads 5 arm_tail))).
Definition armD14 : plan :=
  divfact e_v q8 100000000 (divfact r8 (q1e4b r8) 10000 (divfact q8 (q1e4a q8) 10000 (xloads 5 arm_tail))).
Definition armD16 : plan :=
  divfact e_v q8 100000000 (divfact q8 (q1e4b q8) 10000 (divfact (q1e4b q8) (q100 (q1e4b q8)) 100
    (divfact r8 (q1e4b r8) 10000 (xloads 6 arm_tail)))).
Definition armE18 : plan :=
  divfact e_v q8 100000000 (divfact q8 q16 100000000 (divfact rm (q1e4b rm) 10000
    (divfact r8 (q1e4b r8) 10000 (xloads 6 arm_tail)))).
Definition armE20 : plan :=
  divfact e_v q8 100000000 (divfact q8 q16 100000000 (divfact q16 (q100 q16) 100 (divfact rm (q1e4b rm) 10000
    (divfact r8 (q1e4b r8) 10000 (xloads 7 arm_tail))))).
Fixpoint cases (ts : list (Z * plan)) (last : plan) : plan :=
  match ts with [] => last | (t, a) :: ts' => PCase2 e_v t a (cases ts' last) end.
Definition karms : plan :=
  cases [(9, armA2); (99, armA2); (999, armA4); (9999, armA4); (99999, armB6); (999999, armB6);
         (10^7 - 1, armB8); (10^8 - 1, armB8); (10^9 - 1, armC10); (10^10 - 1, armC10);
         (10^11 - 1, armC12); (10^12 - 1, armC12); (10^13 - 1, armD14); (10^14 - 1, armD14);
         (10^15 - 1, armD16); (10^16 - 1, armD16); (10^17 - 1, armE18); (10^18 - 1, armE18);
         (10^19 - 1, armE20)] armE20.
Definition plan_u64 : AP.plan := PVia 0 tout LO karms (PHandoff 0).

Lemma cert : check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_u64 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.   (* [comment removed for export] *)
Lemma gplan : gplan_ok plan_u64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

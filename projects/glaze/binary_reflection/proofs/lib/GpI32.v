(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition ENTRY : Z := 0x38248.
Definition RETPC : Z := 0x385ac.
Definition STPC : Z := 0x385a8.      (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges PSEGS [(ENTRY, 218%nat)].
Lemma IT_ok : itab_sound PSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 36.
Definition e_pv := e_a0.  Definition e_str := e_a2.  Definition e_pix := e_a3.
Definition e_vraw : expr := EVar 31.          (* [comment removed for export] *)
Definition e_v : expr := EExt false 0 4 e_vraw.  (* [comment removed for export] *)  Definition e_a : expr := EVar 32.  Definition e_size : expr := EVar 33.
Definition e_data : expr := EVar 34.  Definition e_ix : expr := EVar 35.
(* [comment removed for export] *)
Definition e_dix (m : smode) : expr := match m with ML => eadd e_data e_ix | MS => eadd (eaddz e_str 1) e_ix end.
Definition VBYTES : nat := 4.

Definition WMAX : Z := 11.           (* [comment removed for export] *)
Definition WS (m : smode) : list (expr * expr) := [(e_dix m, ELit WMAX); (e_pix, ELit 8)].

Definition str_m (m : smode) : list kentry :=
  match m with ML => str_L e_str e_a e_size e_data ++ [KRange e_data PTRLO PTRHI; KDisj (SA (e_dix ML) 0) (ELit WMAX) (SA e_str 0) (ELit 24)]
             | MS => KRange e_str PTRLO (objhi 24) :: strS e_str e_size end.
(* [comment removed for export] *)
Definition YLO : Z := 0.
Definition kn_in (m : smode) : list kentry :=
  [ KRange e_pv PTRLO (objhi (Z.of_nat VBYTES)); KWord (SA e_pv 0) VBYTES e_vraw ]
  ++ sp_facts YLO ++ str_m m ++
  [ KRange e_pix PTRLO (objhi 8); KWord (SA e_pix 0) 8 e_ix; KWr (SA e_pix 0) (ELit 8);
    KRange e_ix 0 (2 ^ 40); KWr (SA (e_dix m) 0) (ELit WMAX);
    KDisj (SA (e_dix m) 0) (ELit WMAX) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA (e_dix m) 0) (ELit WMAX) (SA e_pix 0) (ELit 8);
    KDisj (SA e_pix 0) (ELit 8) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA e_pix 0) (ELit 8) (SA e_str 0) (ELit 24);
    img_apart (e_dix m) 0 (ELit WMAX); KImg 0x10000 0x71000 ].
Definition tin (m : smode) : acs := mkcs YLO (WS m) ENTRY regs0 (kn_in m) NXF.

(* [comment removed for export] *)
Definition M : nat := 60.
Definition LO : nat := 61.
Definition js_regs : list expr :=
  sr_havoc (sr_upd (sr_upd regs0 10 (EVar LO)) 11 (eadd e_ix (EVar M))) caller_saved_but_a01 (S LO).   (* [comment removed for export] *)
Definition kn_out (m : smode) : list kentry :=
  [ KRange (EVar M) 1 WMAX; KWord (SA e_pix 0) 8 (eadd e_ix (EVar M)); KWr (SA e_pix 0) (ELit 8);
    KWr (SA (e_dix m) 0) (ELit WMAX) ] ++ sp_facts YLO.
Definition tout (m : smode) : acs := mkcs YLO (WS m) RETPC js_regs (kn_out m) (LO + 14)%nat.
(* [comment removed for export] *)
Definition cem (m : smode) : gcallee := GCE NXF (tin m) [tout m] 0 0.
Definition ce : gcallee := cem ML.
Definition ceS : gcallee := cem MS.

(* [comment removed for export] *)
Fixpoint xloads (n : nat) (k : plan) : plan :=
  match n with O => k | S n' => PRun [STPC; RETPC] (PExt 0 [] (xloads n' k)) end.
Definition arm_tail : plan :=
  PRun [STPC; RETPC] (PBump M (PFresh 11 0 (Some e_ix) (PFact (KRange (EVar M) 1 WMAX) (PRun [RETPC] (PHandoff 0))))).
Section Arms.
Variable x : expr.   (* [comment removed for export] *)
Definition armA : plan := xloads 2 arm_tail.
Definition armB : plan := divfact x (q100w x) 100 (zfact x (q100w x) 100 (xloads 3 arm_tail)).
Definition armC : plan := divfact x (q1e4a x) 10000 (zfact x (q1e4a x) 10000 (xloads 3 arm_tail)).
Definition armD : plan := divfact x (q1e4b x) 10000 (divfact (q1e4b x) (q100 (q1e4b x)) 100 (xloads 4 arm_tail)).
Definition rE1 := rem x (q1e8h x) 100000000.
Definition armE : plan := divfact x (q1e8h x) 100000000 (divfact rE1 (q1e4b rE1) 10000 (xloads 4 arm_tail)).

End Arms.
Definition two32 : Z := 4294967296.
(* [comment removed for export] *)
Definition xneg : expr := esub (ELit two32) e_v.


(* [comment removed for export] *)
Definition PJ : Z := 0x38284.
Definition XS : nat := 36.  Definition SS : nat := 37.  Definition XD0 : nat := 38.  Definition LOS : nat := 36.  Definition NXS : nat := 39.
Definition ST0_L : acs := Eval vm_compute in snd (dpath PSEGS IT APLAIN (XN IT NXF) XB0 BFUEL NXF (tin ML) [DLo e_v 2147483647; DRun [PJ]] 0).
Definition ST0_S : acs := Eval vm_compute in snd (dpath PSEGS IT APLAIN (XN IT NXF) XB0 BFUEL NXF (tin MS) [DLo e_v 2147483647; DRun [PJ]] 0).
Definition ST0 (m : smode) : acs := match m with ML => ST0_L | MS => ST0_S end.
Definition is_split (K : kentry) : bool :=
  match K with KRange (EExt false 0 4 (EVar 31)) 0 2147483647 => true | _ => false end.
Definition jsS (m : smode) : acs :=
  mkcs YLO (WS m) PJ (sr_upd (sr_upd (sr_upd (s_regs (a_ss (ST0 m))) 12 (EVar XS)) 11 (EVar SS)) 14 (EVar XD0)) ([KRange (EVar XS) 0 2147483647; KRange (EVar SS) 0 1] ++ filter (fun K => negb (is_split K)) (kn (ST0 m))) NXS.
Definition XJ : expr := EVar XS.
Definition pos_armsX (x : expr) : plan :=
  PCase2 x 9 (armA) (PCase2 x 99 (armA) (PCase2 x 999 (armB x) (PCase2 x 9999 (armB x)
    (PCase2 x 99999 (armC x) (PCase2 x 999999 (armC x) (PCase2 x 9999999 (armD x) (PCase2 x 99999999 (armD x)
      (PCase2 x 999999999 (armE x) (armE x))))))))).
Definition plan_i32m (m : smode) : AP.plan :=
  PVia 1 (jsS m) LOS (PCase2 e_v 2147483647 (PRun [PJ] (PMergeW 1 [(XS, e_v); (SS, ELit 0)]))
                     (PCase2 e_v 2147483648 arm_tail                  (* [comment removed for export] *)
                        (PRun [PJ] (PMergeW 1 [(XS, xneg); (SS, ELit 1)]))))
    (pos_armsX XJ).
Definition plan_i32 : AP.plan := plan_i32m ML.
Definition plan_i32S : AP.plan := plan_i32m MS.

Lemma cert : check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_i32 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.   (* [comment removed for export] *)
Lemma certS : check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ceS) 0%nat BFUEL FUEL None (ce_tin ceS) plan_i32S = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan : gplan_ok plan_i32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplanS : gplan_ok plan_i32S = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

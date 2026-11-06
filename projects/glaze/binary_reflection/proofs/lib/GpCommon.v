(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzRomPlain.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GlzRom OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
#[local] Notation SEGS := Plain.M.loaded_segments.
Definition ROMTAB_P : romtab :=
  Eval vm_compute in
    (let t8 := rt_gen (rom_load_g SEGS) SZ8 true 0x13380 8 1926%nat RLeaf in
     [ ((SZ1, false), rt_gen (rom_load_g SEGS) SZ1 false 0x15a40 1 7536%nat RLeaf); ((SZ8, true), t8); ((SZ8, false), t8) ]).
Lemma ROMTAB_P_ok : romtab_check (rom_load_g SEGS) ROMTAB_P = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance rom_cache_P : rom_cache rom_load_g | 0 := {| rc_segs := SEGS; rc_tab := ROMTAB_P; rc_ok := ROMTAB_P_ok |}.
End GlzRomPlain.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GlzConst.
Export GlzRomPlain.   (* [comment removed for export] *)
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
Definition IMG_SZ : Z := 0x97000.      (* [comment removed for export] *)
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
Definition XN (IT : itab) (NXF : nat) : nat -> list expr -> acs -> option acs := XNc PSEGS IT APLAIN NXF GPLAIN 0 0 CT0.
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
Lemma plain_G_ro_img : g_img_lo GPLAIN <= g_ro_lo GPLAIN /\ g_ro_lo GPLAIN <= g_ro_hi GPLAIN <= g_img_hi GPLAIN. Proof. cbn. lia. Qed.
Lemma plain_G_img_ceil {RC : run_ceil} : g_img_hi GPLAIN <= CEIL_run. Proof. pose proof ceil_rng. cbn [g_img_hi GPLAIN]. lia. Qed.
Lemma plain_G_img_hull : 0 <= g_img_lo GPLAIN <= g_img_hi GPLAIN /\ g_img_hi GPLAIN < 2 ^ 64. Proof. cbn. lia. Qed.

Lemma plain_SEGS_out : forall a : word,
  ~ (g_img_lo GPLAIN <= bv_unsigned a < g_img_hi GPLAIN) -> find_segment PSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a Ha. apply plain_in_hull. unfold APS.in_hull. cbn [img_lo img_hi APLAIN g_img_lo g_img_hi GPLAIN] in *.
  destruct (Z_lt_ge_dec (bv_unsigned a) 0x10000) as [H|H].
  - apply Bool.andb_false_iff. left. apply Z.leb_gt. exact H.
  - apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma nil_SWIN_img : forall lo hi, In (lo, hi) (@nil (Z * Z)) ->
  g_ro_hi GPLAIN <= lo /\ hi <= g_img_hi GPLAIN /\ (forall plo phi, In (plo, phi) (g_priv GPLAIN) -> hi <= plo \/ phi <= lo).
Proof. intros lo hi []. Qed.

(* [comment removed for export] *)
Section XNSound.
Context {RC : run_ceil}.
Variable IT : itab.
Hypothesis IT_ok : itab_sound PSEGS IT.
Variable NXF : nat.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP PSEGS RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GPLAIN b m.
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
#[local] Notation AINVc := (AINV_f [] GPLAIN AINVH PERMc SPTOPc HIDc M0c B0c C0c).

Theorem XN_sound :
  gcontracts PSEGS IT APLAIN NXF PERMc SPTOPc FS0 FDS0 AINVc fx_ok UINV RZ GPLAIN 0 0 ->
  GPS.ext_stmt PSEGS NXF (XN IT NXF) PERMc SPTOPc FS0 FDS0 AINVc fx_ok UINV RZ.
Proof.
  intros GCs. unfold XN.
  exact (XNc_sound PSEGS IT APLAIN plain_in_hull plain_hull_ok IT_ok NXF [] GPLAIN 0 0 fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
            plain_G_ro_img plain_G_img_ceil plain_G_img_hull nil_SWIN_img plain_SEGS_out PERMc SPTOPc FS0 FDS0 HIDc M0c B0c C0c B0c_nonneg C0c_nonneg
            bcap_ok ccap_ok UINV UINV_agree CT0 ltac:(intros id' ce' H; discriminate H) GCs).
Qed.
End XNSound.

(* [comment removed for export] *)
Definition IXMAX : Z := 32 * 2 ^ 26.
Definition RELHI : Z := 24 * 2 ^ 26 + 256 * IXMAX.
Definition relx (di err ix ix0 : expr) (lo : Z) : kentry :=
  KRange (esub (eadd (escale 24 di) (escale IXMAX err)) (esub ix ix0)) lo RELHI.

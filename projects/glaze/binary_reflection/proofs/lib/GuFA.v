(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition IT : itab := mk_itab_ranges USEGS [(0x3140c, 556%nat); (0x31cc0, 120%nat); (0x31eac, 22%nat); (0x31f08, 26%nat); (0x31f74, 32%nat); (0x31ff8, 44%nat); (0x320ac, 22%nat); (0x32108, 26%nat); (0x32174, 32%nat); (0x321f8, 44%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition NXF : nat := 34.
Definition regs0 : list expr := ELit 0 :: map EVar (seq 0 31).
Definition e_sp : expr := EVar 1.
Definition AV : expr := EVar 9. Definition C : expr := EVar 10. Definition Q : expr := EVar 11. Definition EE : expr := EVar 12.
Definition B : expr := EVar 31. Definition O : expr := EVar 32. Definition ERP : expr := EVar 33.
Definition FR : Z := 2256.          (* [comment removed for export] *)
Definition BUFMAX : Z := 2 ^ 26.         (* [comment removed for export] *)
Definition kn_common : list kentry :=
  [KWr (SA Q 0) (ELit 8);
   KUnk (SA B 0) (esub EE B); KWr (SA B 0) (esub EE B); KRange (esub EE B) 0 BUFMAX; KRange B PTRLO PTRHI; KRange EE PTRLO PTRHI;
   KWr (SA AV 0) (ELit 24); KWr (SA C 0) (ELit 4);
   KRange AV CEIL HI47; KRange C CEIL HI47; KRange Q CEIL HI47;            KAlign AV 8; KAlign C 8; KAlign Q 8;   (* [comment removed for export] *)
   KDisj (SA AV 0) (ELit 24) (SA C 0) (ELit 40); KDisj (SA AV 0) (ELit 24) (SA Q 0) (ELit 8); KDisj (SA C 0) (ELit 40) (SA Q 0) (ELit 8);
   KDisj (SA AV 0) (ELit 24) (SA B 0) (esub EE B); KDisj (SA C 0) (ELit 40) (SA B 0) (esub EE B); KDisj (SA Q 0) (ELit 8) (SA B 0) (esub EE B);
   KWr (SA e_sp (- FR)) (ELit FR);
   KDisj (SA e_sp (- FR)) (ELit FR) (SA AV 0) (ELit 24); KDisj (SA e_sp (- FR)) (ELit FR) (SA C 0) (ELit 40);
   KDisj (SA e_sp (- FR)) (ELit FR) (SA Q 0) (ELit 8); KDisj (SA e_sp (- FR)) (ELit FR) (SA B 0) (esub EE B);
   KAlign e_sp 16; KRange e_sp (CEIL + 4096) HI47; KImg (g_ro_lo GUBSAN) (g_ro_hi GUBSAN)].
Definition kn0 : list kentry :=
  [KWord (SA Q 0) 8 (eadd B O); KRange O 0 BUFMAX; KRange (esub (esub EE B) O) 0 BUFMAX; KWord (SA C 0) 4 ERP; KRange ERP 0 0] ++ kn_common.
Definition WS : list (expr * expr) := [(AV, ELit 24); (C, ELit 4); (Q, ELit 8)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FR 0 [] WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition tin : acs := mkcs 0x3140c regs0 kn0 NXF.

Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN 0 0 CT.
Definition LIMIT : Z := 2 ^ 34.

(* [comment removed for export] *)
Definition RET : Z := 0x31ca8.
Definition O' : expr := EVar 40. Definition ER' : expr := EVar 41.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.
Definition x_regs : list expr := sr_havoc regs0 clobbered 42.
Definition x_kn : list kentry :=
  [KWord (SA Q 0) 8 (eadd B O'); KRange O' 0 BUFMAX; KRange (esub (esub EE B) O') 0 BUFMAX; KWord (SA C 0) 4 ER'; KRange ER' 0 24] ++ kn_common.
Definition tout : acs := mkcs RET x_regs x_kn 57.

Definition ce : gcallee := GCE NXF tin [tout] 0 0.

(* [comment removed for export] *)
Definition CNT : expr := EVar 150. Definition PAD : expr := EVar 260.

Definition JO : expr := EVar 200. Definition JCNT : expr := EVar 201.
Definition fa_frame : list kentry :=
  [KWord (SA e_sp (-208)) 8 Q; KWord (SA e_sp (-200)) 8 C; KWord (SA e_sp (-192)) 8 (eaddz e_sp (-160));
   KWord (SA e_sp (-184)) 8 (eaddz e_sp (-176)); KWord (SA e_sp (-176)) 8 AV; KWord (SA e_sp (-168)) 8 C; KWord (SA e_sp (-160)) 8 EE;
   KWord (SA e_sp (-104)) 8 (EVar 26); KWord (SA e_sp (-96)) 8 (EVar 25); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-80)) 8 (EVar 23);
   KWord (SA e_sp (-72)) 8 (EVar 22); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-48)) 8 (EVar 19);
   KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-24)) 8 (EVar 8); KWord (SA e_sp (-16)) 8 (EVar 7);
   KWord (SA e_sp (-8)) 8 (EVar 0)].
Definition jkn (cnthi : Z) : list kentry :=
  [KWord (SA Q 0) 8 (eadd B JO); KRange JO 0 BUFMAX; KRange (esub (esub EE B) JO) 0 BUFMAX; KRange JCNT 0 cnthi;
   KWord (SA C 0) 4 ERP; KRange ERP 0 0] ++ fa_frame ++ kn_common.
(* [comment removed for export] *)
Definition jregs (ra a0 a1 a2 a3 a4 a5 s3 : expr) : list expr :=
  [ELit 0; ra; eaddz e_sp (-208); EVar 2; EVar 3; EVar 202; EVar 203; EVar 204; C; Q; a0; a1; a2; a3; a4; a5; EVar 205; EVar 206;
   AV; s3; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 207; EVar 208; EVar 29; EVar 30].
(* [comment removed for export] *)
Definition JCT (t : Z) : acs := mkcs 0x315c0 (jregs (ELit 0x315bc) (ELit 0) (EVar 209) JCNT C (EVar 210) (eadd B JO) (ELit t)) (jkn 3) 211.
(* [comment removed for export] *)
Definition JBOT (t2 w : Z) : acs := mkcs 0x31a74 (jregs (EVar 0) (eadd B JO) (ELit t2) (ELit w) EE JCNT (EVar 209) (ELit 92)) (jkn (2^48)) 211.
(* [comment removed for export] *)
Definition JBUT : acs := mkcs 0x31980 (jregs (EVar 0) JCNT (eadd B JO) (EVar 209) EE (EVar 210) (EVar 211) (ELit 92)) (jkn (2^48)) 212.

Definition FUEL : nat := 3000. Definition BFUEL : nat := 600.







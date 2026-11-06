(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require GpFA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition IT : itab := mk_itab_ranges PSEGS [(0x2f1b8, 263%nat); (0x2f5d4, 110%nat); (0x2f78c, 239%nat); (0x2fb48, 144%nat)].
Lemma IT_ok : itab_sound PSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 36.
Definition regs0 : list expr := ELit 0 :: map EVar (seq 0 3) ++ [ELit 0x86520] ++ map EVar (seq 4 27).
Definition e_sp : expr := EVar 1.
Definition v : expr := EVar 9.      (* [comment removed for export] *)
Definition c : expr := EVar 10.     (* [comment removed for export] *)
Definition q : expr := EVar 11.     (* [comment removed for export] *)
Definition E : expr := EVar 12.     (* [comment removed for export] *)
Definition I : expr := EVar 31.     (* [comment removed for export] *)
Definition dep : expr := EVar 32.   (* [comment removed for export] *)
Definition sv : expr := EVar 33.    (* [comment removed for export] *)
Definition FRX : Z := 4096.         (* [comment removed for export] *)
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x97000).
Definition BUFMAX : Z := 2 ^ 26.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_common : list kentry :=
  [KWr (SA q 0) (ELit 8);
   KUnk (SA I 0) (esub E I); KWr (SA I 0) (esub E I); KRange (esub E I) 0 BUFMAX; KRange I PTRLO PTRHI; KRange E PTRLO PTRHI;
   img_apart I 0 (esub E I); KDisj (SA I 0) (esub E I) (SA e_sp (- FRX)) (ELit (FRX + WSTK));      (* [comment removed for export] *)
   KWr (SA v 0) (ELit 16); KWr (SA v 16) (ELit 24); KWr (SA v 40) (ELit 24); KWr (SA c 0) (ELit 4); KWr (SA c 32) (ELit 4); KRange dep 0 254;
   KRange v CEIL HI47; KRange (eaddz v 64) (CEIL + 64) HI47; KRange c CEIL HI47; KRange q CEIL HI47;   (* [comment removed for export] *)
   KRange (esub v e_sp) 0 (2^46); KRange (esub c e_sp) 0 (2^46); KRange (esub q e_sp) 0 (2^46);   (* [comment removed for export] *)
   KDisj (SA v 0) (ELit 64) (SA c 0) (ELit 40); KDisj (SA v 0) (ELit 64) (SA q 0) (ELit 8); KDisj (SA c 0) (ELit 40) (SA q 0) (ELit 8);
   KDisj (SA v 0) (ELit 64) (SA I 0) (esub E I); KDisj (SA c 0) (ELit 40) (SA I 0) (esub E I); KDisj (SA q 0) (ELit 8) (SA I 0) (esub E I);
   KWr (SA e_sp (- FRX)) (ELit FRX);
   KDisj (SA e_sp (- FRX)) (ELit FRX) (SA v 0) (ELit 64); KDisj (SA e_sp (- FRX)) (ELit FRX) (SA c 0) (ELit 40);
   KDisj (SA e_sp (- FRX)) (ELit FRX) (SA q 0) (ELit 8); KDisj (SA e_sp (- FRX)) (ELit FRX) (SA I 0) (esub E I);
   KAlign e_sp 16; KRange e_sp (CEIL + 8192) HI47; 
    KImg 0x10000 0x71000].
Definition kn0 : list kentry :=
  [KWord (SA q 0) 8 I; KWord (SA v 16) 1 (escale 2 sv); KRange sv 0 22; KWord (SA c 0) 4 (ELit 0); KWord (SA c 32) 4 dep] ++ kn_common.
Definition WS : list (expr * expr) := [(v, ELit 64); (c, ELit 4); (eaddz c 32, ELit 4); (q, ELit 8); (I, esub E I); (eaddz e_sp (- FRX), ELit FRX)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition tin : acs := mkcs 0x2f1b8 regs0 kn0 NXF [].

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 100 then Some GpFA.ce else None.
Definition BCAP : Z := 2 ^ 28.  Definition CCAP : Z := 8.   (* [comment removed for export] *)
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS IT APLAIN NXF GPLAIN BCAP CCAP CT.
Definition CT2 (id : nat) : option gcallee2 := None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc PSEGS APLAIN NXF GPLAIN BCAP CCAP CT2.
Definition LIMIT : Z := 2 ^ 34.

(* [comment removed for export] *)
Definition RET : Z := 0x2f590.

Definition P : expr := EVar 36.        (* [comment removed for export] *)
Definition SV2 : expr := EVar 37.      (* [comment removed for export] *)
Definition ER : expr := EVar 38.       (* [comment removed for export] *)
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.
Definition x_regs : list expr := sr_havoc regs0 clobbered 39.
(* [comment removed for export] *)
Definition x_kn_S : list kentry :=
  [KWord (SA q 0) 8 P; KWord (SA v 16) 1 (escale 2 SV2); KRange SV2 0 22; KWord (SA c 0) 4 ER; KWord (SA c 32) 4 dep] ++ kn_common.
Definition toutS : acs := mkcs RET x_regs x_kn_S 54 [].
(* [comment removed for export] *)
Definition DL : expr := EVar 54. Definition SL : expr := EVar 55. Definition AL : expr := EVar 56.
Definition strL (d s a : expr) : list kentry :=
  [KWord (SA v 16) 8 (eaddz (escale 8 a) 1); KWord (SA v 24) 8 s; KWord (SA v 32) 8 d;
   KRange a 3 (2^24 + 1); KRange s 0 (2^27 + 8); KRange (esub (escale 8 a) s) 1 (2^27 + 8);
   KRange d PTRLO PTRHI; KRange (eadd d (escale 8 a)) PTRLO PTRHI; KAlign d 16; KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA v 0) (ELit 64); KDisj (SA d 0) (escale 8 a) (SA c 0) (ELit 4);
   KDisj (SA d 0) (escale 8 a) (SA c 32) (ELit 4); KDisj (SA d 0) (escale 8 a) (SA q 0) (ELit 8);
   KDisj (SA d 0) (escale 8 a) (SA I 0) (esub E I); KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart d 0 (escale 8 a)].
Definition x_kn_L : list kentry :=
  [KWord (SA q 0) 8 P; KWord (SA c 0) 4 ER; KWord (SA c 32) 4 dep] ++ strL DL SL AL ++ kn_common.
Definition toutL : acs := mkcs RET x_regs x_kn_L 57 [(DL, escale 8 AL)].


(* [comment removed for export] *)
Definition ce2 : gcallee2 := GCE2 NXF tin [toutS] [toutL] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

(* [comment removed for export] *)
Definition HEAD : Z := 0x2f384.
(* [comment removed for export] *)
Definition loop_slots : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 22; 28; 29; 30; 31]%nat.
Definition loop_regs (a0 : expr) (slot0 : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
    2 (eaddz e_sp (-208))) 8 c) 9 q) 10 a0) 18 v) 19 (ELit 0x13220)) 20 (ELit 0x13210)) 21 (ELit 1)) 23 (ELit 3))
    24 (eaddz e_sp (-120))) 25 (eaddz e_sp (-136))) 26 (eaddz e_sp (-112))) 27 (ELit 2)) loop_slots slot0.
Definition frame_kn : list kentry :=
  [KWord (SA e_sp (-208)) 8 (eaddz v 40); KWord (SA e_sp (-200)) 8 (ELit 29281); KWord (SA e_sp (-192)) 8 (ELit 1125899906842627);
   KWord (SA e_sp (-112)) 8 E;
   KWord (SA e_sp (-104)) 8 (EVar 26); KWord (SA e_sp (-96)) 8 (EVar 25); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-80)) 8 (EVar 23);
   KWord (SA e_sp (-72)) 8 (EVar 22); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-48)) 8 (EVar 19);
   KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-24)) 8 (EVar 8); KWord (SA e_sp (-16)) 8 (EVar 7);
   KWord (SA e_sp (-8)) 8 (EVar 0)].
(* [comment removed for export] *)
Definition itk (o : expr) : list kentry :=
  [KWord (SA q 0) 8 (eadd I o); KRange o 0 BUFMAX; KRange (esub (esub E I) o) 0 BUFMAX].

Definition NV : expr := EVar 64. Definition O1 : expr := EVar 65.
Definition j1_kn : list kentry :=
  itk O1 ++ [KRange (esub E I) 1 BUFMAX; KRange NV 1 (2^62); KWord (SA v 16) 1 (escale 2 sv); KRange sv 0 22; KWord (SA c 0) 4 (ELit 0); KWord (SA c 32) 4 (eaddz dep 1)]
  ++ frame_kn ++ kn_common.
Definition J1 : acs := mkcs HEAD (sr_upd (loop_regs (eaddz NV (-1)) 66) 22 (EVar 21)) j1_kn 82 [].
(* [comment removed for export] *)
Definition JJ : nat := 82.
Definition OJ : expr := EVar 83. Definition SVJ : expr := EVar 84. Definition ERJ : expr := EVar 85.
Definition cnt (n : expr) (j : nat) : expr := esub (eaddz n (-1)) (EVar j).     (* [comment removed for export] *)
Definition inv_kn_S : list kentry :=
  itk OJ ++ [KRange (esub E I) 1 BUFMAX; KRange NV 1 (2^62); KWord (SA v 16) 1 (escale 2 SVJ); KRange SVJ 0 22;
             KWord (SA c 0) 4 ERJ; KRange ERJ 0 0; KWord (SA c 32) 4 (eaddz dep 1)] ++ frame_kn ++ kn_common.
Definition INV_S : acs := mkcs HEAD (loop_regs (cnt NV JJ) 86) inv_kn_S 104 [].
Definition OK : expr := EVar 83. Definition DK : expr := EVar 84. Definition SK : expr := EVar 85. Definition AK : expr := EVar 86.
Definition ERK : expr := EVar 87.
Definition inv_kn_L : list kentry :=
  itk OK ++ [KRange (esub E I) 1 BUFMAX; KRange NV 1 (2^62); KWord (SA c 0) 4 ERK; KRange ERK 0 0; KWord (SA c 32) 4 (eaddz dep 1)]
  ++ strL DK SK AK ++ frame_kn ++ kn_common.
Definition INV_L : acs := mkcs HEAD (loop_regs (cnt NV JJ) 88) inv_kn_L 104 [(DK, escale 8 AK)].
(* [comment removed for export] *)
Definition NB : expr := eaddz NV (-1).

Definition O2 : expr := EVar 130. Definition KL : expr := EVar 131.
Definition j2_regs (base : list expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd base
    5 (EVar 132)) 10 (ELit 22)) 11 (eadd I O2)) 12 KL) 13 E) 14 (EVar 133)) 15 (EVar 134)) 16 (EVar 135)) 17 (EVar 136)) 22 (cnt NV JJ).
Definition j2_facts : list kentry :=
  [KWord (SA q 0) 8 (eadd I O2); KRange O2 0 BUFMAX; KRange (esub (esub E I) O2) 0 BUFMAX; KRange KL 0 (2^62 - 1)].
Definition jfacts : list kentry := [KRange (EVar JJ) 0 (2^62 - 2); KRange (esub NB (EVar JJ)) 1 (2^62 - 1)].
Definition J2S (last : bool) : acs :=
  let T := mkcs 0x2f47c (j2_regs (loop_regs (cnt NV JJ) 86)) (j2_facts ++ (if last then [] else jfacts) ++ skipn 3 inv_kn_S) 137 [] in
  if last then inst T JJ NB else T.
Definition J2L (last : bool) : acs :=
  let T := mkcs 0x2f47c (j2_regs (loop_regs (cnt NV JJ) 88)) (j2_facts ++ (if last then [] else jfacts) ++ skipn 3 inv_kn_L) 137 [(DK, escale 8 AK)] in
  if last then inst T JJ NB else T.
(* [comment removed for export] *)
Definition NNS : expr := EVar 200. Definition NNL : expr := EVar 400.










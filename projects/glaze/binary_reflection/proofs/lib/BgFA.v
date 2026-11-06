(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0xa4d58.
Definition RET : Z := 0xa60a0.
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 1699%nat); (0xa67e4, 323%nat); (0xa6cf0, 109%nat); (0xa6ea4, 127%nat); (0xa70a0, 131%nat); (0xa72ac, 140%nat); (0xa74dc, 108%nat); (0xa768c, 125%nat); (0xa7880, 131%nat); (0xa7a8c, 140%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition NXF : nat := 36.
Definition AV : expr := EVar 9. Definition C : expr := EVar 10. Definition Q : expr := EVar 11. Definition EE : expr := EVar 12.
Definition B : expr := EVar 31. Definition O : expr := EVar 32. Definition ERP : expr := EVar 33.
Definition e_mtr : expr := EVar 34.  Definition e_fb : expr := EVar 35.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).   (* [comment removed for export] *)
Definition FR : Z := 2560.          (* [comment removed for export] *)
Definition YLO : Z := FR.         (* [comment removed for export] *)
Definition BUFMAX : Z := 2 ^ 26.

Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition kn_common : list kentry :=
  [KWr (SA Q 0) (ELit 8);
   KUnk (SA B 0) (esub EE B); KWr (SA B 0) (esub EE B); KRange (esub EE B) 0 BUFMAX; KRange B PTRLO PTRHI; KRange EE PTRLO PTRHI;
   KWr (SA AV 0) (ELit 24); KWr (SA C 0) (ELit 4);
   KRange AV PTRLO (objhi 32); KRange C PTRLO (objhi 40); KRange Q PTRLO (objhi 8);   (* [comment removed for export] *)
   KAlign AV 8; KAlign C 8; KAlign Q 8;
   KShOk (SA AV 0) (ELit 24); KShOk (SA C 0) (ELit 8); KShOk (SA Q 0) (ELit 8); KShOk (SA B 0) (esub EE B);
   KDisj (SA AV 0) (ELit 24) (SA C 0) (ELit 40); KDisj (SA AV 0) (ELit 24) (SA Q 0) (ELit 8); KDisj (SA C 0) (ELit 40) (SA Q 0) (ELit 8);
   KDisj (SA AV 0) (ELit 24) (SA B 0) (esub EE B); KDisj (SA C 0) (ELit 40) (SA B 0) (esub EE B); KDisj (SA Q 0) (ELit 8) (SA B 0) (esub EE B);
   KWr (SA e_sp (- FR)) (ELit FR); fb_fact e_fb;   (* [comment removed for export] *)
   KDisj (SA e_sp (- FR)) (ELit FR) (SA AV 0) (ELit 24); KDisj (SA e_sp (- FR)) (ELit FR) (SA C 0) (ELit 40);
   KDisj (SA e_sp (- FR)) (ELit FR) (SA Q 0) (ELit 8); KDisj (SA e_sp (- FR)) (ELit FR) (SA B 0) (esub EE B)]
  ++ [KAlign e_sp 32; KRange e_sp (CEIL + YLO) HI47] ++ [KIMGA] ++ RTC ++ tbl_shadow
  ++ [img_apart AV 0 (ELit 24); shmap_apart AV 0 (ELit 24); img_apart C 0 (ELit 40); shmap_apart C 0 (ELit 40); img_apart Q 0 (ELit 8); shmap_apart Q 0 (ELit 8); shmap_apart B 0 (esub EE B)].   (* [comment removed for export] *)
Definition stk_shok : kentry := KShOk (SA e_sp (- FR)) (ELit FR).   (* [comment removed for export] *)
Definition kn0 : list kentry :=
  [stk_shok; KWord (SA Q 0) 8 (eadd B O); KRange O 0 BUFMAX; KRange (esub (esub EE B) O) 0 BUFMAX; KWord (SA C 0) 4 ERP; KRange ERP 0 0] ++ kn_common.
(* [comment removed for export] *)
Definition WS : list (expr * expr) := [(AV, ELit 24); (C, ELit 8); (Q, ELit 8); (B, esub EE B)].
Definition tin : acs := mkcs YLO WS e_mtr e_fb ENTRY regsT kn0 NXF.

(* [comment removed for export] *)
Definition O' : expr := EVar 40. Definition ER' : expr := EVar 41.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs : list expr := sr_havoc regsT clobbered 42.
Definition x_kn : list kentry :=
  [KWord (SA Q 0) 8 (eadd B O'); KRange O' 0 BUFMAX; KRange (esub (esub EE B) O') 0 BUFMAX; KWord (SA C 0) 4 ER'; KRange ER' 0 24; KRange (esub O' O) 0 BUFMAX] ++ kn_common.   (* [comment removed for export] *)
Definition tout : acs := mkcs YLO WS e_mtr e_fb RET x_regs x_kn 57.

Definition ce : gcallee := GCE NXF tin [tout] 0 0.

(* [comment removed for export] *)
Definition CNT : expr := EVar 150.









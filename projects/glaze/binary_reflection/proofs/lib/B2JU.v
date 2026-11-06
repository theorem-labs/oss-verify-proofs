(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GcFlush.F72_003.   (* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.EscU OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JU_A0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA0.
Definition MEMCPY : Z := 0x732b0.
Definition SS0 : list expr := [DEPTH; TAGv].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition JS_null (m : smode) := JS_emit0 m 0x326e0 (ELit 0) ITO IX (eaddz IX 4) 1 0 SS0 [] 60.
Definition JS_true (m : smode) := JS_emit0 m 0x328dc (ELit 0) ITO IX (eaddz IX 4) 1 0 SS0 [] 60.
Definition JS_false (m : smode) := JS_emit0 m 0x32378 (ELit 0) ITO IX (eaddz IX 5) 1 0 SS0 [] 60.
Definition tag (m : smode) : plan :=
  PRun [] (PBranchP
    (* [comment removed for export] *) (PRun [0x32368] (PBranch
        (ENSURE 0 m 36 JS_false 60 0x32370 0x32378 (fun mm => PRun [MEMCPY] (PExt 1 [] (EXIT mm))))
        (ENSURE 0 m 36 JS_true 60 0x328d4 0x328dc EXIT)))
    (* [comment removed for export] *) (ENSURE 0 m 36 JS_null 60 0x326d8 0x326e0 EXIT)).
Definition cutT (c : nat) (m : smode) : acs := tin m.
Definition cutK (c : nat) (m : smode) : plan := PContraH 0.
Definition live (w : smode) (c : nat) (m : smode) : bool := false.
End B2JUA0.
End B2JU_A0.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JU_A1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuNumT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA1.
Definition tag (m : smode) : plan := PRun [B2JUT.GuNumT.BNU] (CALL m 220 223 (NUM_ARGS m (eaddz ITO 1) IX 36 TAGv) EXIT).
(* [comment removed for export] *)
Definition cutT (c : nat) (m : smode) : acs := tin m.
Definition cutK (c : nat) (m : smode) : plan := PContraH 0.
Definition live (w : smode) (c : nat) (m : smode) : bool := false.
End B2JUA1.
End B2JU_A1.
Module B2JU_A2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA2.
Definition HL : expr := EVar 80.
Definition Nv : expr := EVar 81.                 (* [comment removed for export] *)
Definition ITO1 : expr := eadd (eaddz ITO 1) HL.
Definition JS_hdr (m : smode) : acs :=
  mkcs 0x32b24 (regs_emit (eadd INLO ITO1) [Nv; TAGv] 63)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange Nv 0 (2 ^ 48);
                  rel ITO1 IX 48]
        ++ pos ITO1 IX (ELit 0) 0 BIG ++ str m IX ITO1 (ELit 0) 60 ++ kn_fixed)
       82%nat (vis m 60).
Definition after_esc (m : smode) : plan := PRun [] (PBranchP (EXIT m) (EXIT m)).
Definition esc_call (m : smode) : plan :=
  PRun [0x32b38] (PBranch (ERR_EXIT m) (PRun [EscU.ENTRY] (CALL m 200 203 (ESC_ARGS ITO1 Nv IX 60) after_esc))).
Definition tag (m : smode) : plan :=
  PRun [0x323a4] (PBranch (ERR_EXIT m)
  (PViaM 2 (match m with MS => [(JS_hdr MS, esc_call MS); (JS_hdr ML, esc_call ML)] | ML => [(JS_hdr ML, esc_call ML)] end) 60
     (HDR4m 13 m 0x323cc 0x323d4 false 0x32b18 false 0x32b24 2 80))).
Definition cutT (c : nat) (m : smode) : acs := tin m.
Definition cutK (c : nat) (m : smode) : plan := PContraH 0.
Definition live (w : smode) (c : nat) (m : smode) : bool := false.
End B2JUA2.
End B2JU_A2.
Module B2JU_A3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuNumT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA3.
Definition HL : expr := EVar 80.
Definition J5 : expr := EVar 130.
Definition ITOJ : expr := EVar 131. Definition IXJ : expr := EVar 132.
Definition SS0 : list expr := [DEPTH; TAGv].                  (* [comment removed for export] *)
Definition JS_lcb (m : smode) := JS_emit m 0x32764 (ELit 0) (eaddz ITO 1) IX (eaddz IX 1) 0 24 SS0 [] 60.
Definition TBL : expr := ELit 0x13208.
(* [comment removed for export] *)
Definition NFv : expr := EVar 81.
Definition SSo0 (nf : expr) : list (nat * expr) := [(21, DEPTH); (22, TAGv); (23, TBL); (24, nf)]%nat.   (* [comment removed for export] *)
Definition ITO1 : expr := eadd (eaddz ITO 1) HL.
Definition JS_ohdr (m : smode) : acs :=
  mkcs 0x33a60 (mkregs (SSo0 NFv) 85)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 0 (2 ^ 48);
                  rel ITO1 (eaddz IX 1) 47]
        ++ pos ITO1 (eaddz IX 1) (ELit 0) 0 BIG ++ str m (eaddz IX 1) ITO1 (ELit 0) 82 ++ kn_fixed)
       110%nat (vis m 82).
Definition HEADo : Z := 0x33a8c.
Definition SSo (j : expr) : list (nat * expr) :=
  [(21, eaddz DEPTH 1); (23, TBL); (24, esub NFv j); (25, eaddz OBJ 1); (26, ELit 1); (27, ELit 58)]%nat.
Definition kn_o : list kentry :=
  frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 1 (2 ^ 48);
            KRange J5 0 (2 ^ 48)].
Definition INVo (m : smode) : acs :=
  mkcs HEADo (mkregs (SSo J5) 136)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
Definition HLK : expr := EVar 160. Definition KVv : expr := EVar 161.
Definition NK : expr := EAlu Instr.ALU_SRL KVv (ELit 2).
Definition ITOK : expr := eadd ITOJ HLK.
Definition JS_khdr (m : smode) : acs :=
  mkcs 0x33b9c (mkregs (SSo J5 ++ [(10, eadd INLO ITOK); (11, KVv)])%nat 165)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 (INSZ - 1); KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3);
                 KRange ITOK 0 INSZ; rel ITOK IXJ 71]
        ++ pos ITOK IXJ (ELit 0) 0 BIG ++ str m IXJ ITOK (ELit 0) 162 ++ kn_fixed)
       190%nat (vis m 162).
Definition IXC : expr := EVar 221.
Definition relK (ix : expr) (lo : Z) : kentry :=
  KRange (eadd (esub (escale 24 (esub ITOK ITO)) (esub ix IX)) (escale 2 NK)) lo RELHI.
Definition kn_k : list kentry :=
  kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 (INSZ - 1); KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3);
           KRange ITOK 0 INSZ; KRange (esub BSZ (eadd ITOK NK)) 0 INSZ].
Definition JS_key (m : smode) : acs :=
  mkcs 0x33bd8 (mkregs (SSo J5 ++ [(22, NK)])%nat 225)
       (kn_k ++ [KRange IXC 0 IXHI2; relK IXC 69] ++ posK ITOK IXC (ELit 0) 0 IXHI2 ++ strc m IXC (eadd ITOK NK) (ELit 0) 222 ++ kn_fixed)
       242%nat (vis m 222).
Definition JS_colon (m : smode) : acs :=
  mkcs 0x33bfc (mkregs (SSo J5 ++ [(10, IXC); (22, NK)])%nat 246)
       (kn_k ++ [KRange IXC 0 IXHI2; relK IXC 69] ++ room m (eaddz IXC 1) 243
        ++ posK ITOK IXC (ELit 0) 0 IXHI2 ++ str m IXC (eadd ITOK NK) (ELit 0) 243 ++ kn_fixed)
       262%nat (vis m 243).
Definition ITOV : expr := EVar 285. Definition IXV : expr := EVar 286.
Definition JS_oval (m : smode) : acs :=
  mkcs 0x33c80 (mkregs (SSo J5) 290)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOV 0 INSZ; rel ITOV IXV 48]
        ++ pos ITOV IXV (ELit 0) 0 BIG ++ strc m IXV ITOV (ELit 0) 287 ++ kn_fixed)
       308%nat (vis m 287).
Definition JS_ocomma (m : smode) : acs :=
  mkcs 0x33ca8 (mkregs (SSo J5 ++ [(10, IXV)])%nat 313)
       (kn_o ++ [KRange (esub NFv J5) 2 (2 ^ 48); KRange ITOV 0 INSZ; rel ITOV IXV 48] ++ room m (eaddz IXV 1) 310
        ++ pos ITOV IXV (ELit 0) 0 BIG ++ str m IXV ITOV (ELit 0) 310 ++ kn_fixed)
       330%nat (vis m 310).
Definition loop_end_o (lm : lmode) (m' : smode) : plan :=       (* [comment removed for export] *)
  match lm, m' with LML, _ => PRun [HEADo] PNext | LMS, MS => PRun [HEADo] PNext | _, _ => PRun [HEADo] (GO COL ML) end.
Definition after_oval (lm : lmode) (m : smode) : plan :=                  (* [comment removed for export] *)
  PCase2 (esub NFv J5) 1
     (PRun [0x33d54] (closeo m 287))                                                     (* [comment removed for export] *)
     (ENSURE' 37 m 287 JS_ocomma 310 0x33ca4 0x33ca8 (loop_end_o lm)).  (* [comment removed for export] *)
Definition post_oval (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x33c80] (GO COVAL ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 36 [(JS_oval m, n13 (JS_oval m) (after_oval lm m))] 285 (PRun [0x33c80] (PMerge 36))))
  end.
Definition after_colon (lm : lmode) (m : smode) : plan :=
  PRun [ENTRY] (PFact (iixE (eadd ITOK NK) (eaddz IXC 1) (ELit 0))
               (PFact (KRange (eaddz IXC 1) 0 BIG)
               (CALL m 210 213 (SELF_ARGS (eadd ITOK NK) (eaddz IXC 1) 243) (post_oval lm)))).
Definition after_keyj (lm : lmode) (m : smode) : plan :=                  (* [comment removed for export] *)
  ENSURE' 35 m 222 JS_colon 243 0x33bf8 0x33bfc (kS lm CCOL (after_colon lm)).
Definition after_key (lm : lmode) (m : smode) : plan :=                   (* [comment removed for export] *)
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x33bd8] (GO CKEY ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 39 [(JS_key m, n13 (JS_key m) (after_keyj lm m))] 221 (PRun [0x33bd8] (PMerge 39))))
  end.
Definition after_khdr (lm : lmode) (m : smode) : plan :=
  PRun [0x33bb0] (PBranch
     (PRun [EscU.ENTRY] (CALL m 200 203 (ESC_ARGS ITOK NK IXJ 162) (after_key lm)))
     (ERR_EXIT m)).
Definition bodyo (lm : lmode) (m : smode) : plan :=
  PRun [0x33a94] (PBranch
    (PViaM 34 [(JS_khdr m, after_khdr lm m)] 160 (HDR4m 12 m 0x33aa4 0x33aac true 0x33b98 true 0x33b9c 34 160))
    (ERR_EXIT m)).
Definition loopo (m : smode) : plan :=      (* [comment removed for export] *)
  PLoopM 130 NFv [(INVo m, bodyo (lmo m) m, PContraH 0)] [].
Definition after_ohdr (m : smode) : plan :=
  PRun [0x33a78] (PBranch (PRun [HEADo] (match m with MS => loopo MS | ML => GO COL ML end)) (PRun [0x33d54] (closeo m 82))).
Definition okeys_str (m : smode) : plan :=
  PRun [0x329e4] (PBranch (HDR4h 12 m 0x32a08 0x32a10 true 0x33a54 false 0x33a60 (HOLE 0 m) 80) (ERR_EXIT m)).
(* [comment removed for export] *)
Definition SSn0 (nf : expr) : list (nat * expr) := [(21, DEPTH); (22, nf)]%nat.
Definition JS_nhdr (m : smode) : acs :=
  mkcs 0x330ac (mkregs (SSn0 NFv) 85)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 0 (2 ^ 48);
                  rel ITO1 (eaddz IX 1) 47]
        ++ pos ITO1 (eaddz IX 1) (ELit 0) 0 BIG ++ str m (eaddz IX 1) ITO1 (ELit 0) 82 ++ kn_fixed)
       110%nat (vis m 82).
Definition HEADn : Z := 0x330d0.
Definition SSn (j : expr) : list (nat * expr) :=
  [(21, eaddz DEPTH 1); (22, esub NFv j); (23, eaddz OBJ 1); (24, ELit 34); (25, ELit 58); (26, ELit 1); (27, ELit 44)]%nat.
Definition INVn (m : smode) : acs :=
  mkcs HEADn (mkregs (SSn J5) 136)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 1 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
Definition JS_q1 (m : smode) : acs :=
  mkcs 0x330f4 (mkregs (SSn J5 ++ [(10, IXJ)])%nat 163)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 1 INSZ; rel ITOJ IXJ 47] ++ room m (eaddz IXJ 1) 160
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 160 ++ kn_fixed)
       180%nat (vis m 160).
Definition DIn : expr := EVar 205. Definition IXN : expr := EVar 206.
Definition ITON : expr := eadd ITOJ DIn.
Definition JS_num (m : smode) : acs :=
  mkcs 0x33164 (mkregs (SSn J5) 210)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange DIn 0 8; KRange ITON 0 INSZ; KRange (esub ITON ITO) 1 INSZ; KRange IXN 0 BIG; rel ITON IXN 54]
        ++ pos ITON IXN (ELit 0) 0 BIG ++ strc m IXN ITON (ELit 0) 207 ++ kn_fixed)
       228%nat (vis m 207).
Definition JS_q2 (m : smode) : acs :=
  mkcs 0x33188 (mkregs (SSn J5 ++ [(10, IXN)])%nat 231)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange DIn 0 8; KRange ITON 0 INSZ; KRange (esub ITON ITO) 1 INSZ; KRange IXN 0 BIG; rel ITON IXN 54]
        ++ room m (eaddz IXN 1) 228
        ++ pos ITON IXN (ELit 0) 0 BIG ++ str m IXN ITON (ELit 0) 228 ++ kn_fixed)
       248%nat (vis m 228).
Definition JS_c2 (m : smode) : acs :=
  mkcs 0x331f4 (mkregs (SSn J5 ++ [(10, eaddz IXN 1)])%nat 251)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; KRange DIn 0 8; KRange ITON 0 INSZ; KRange (esub ITON ITO) 1 INSZ; KRange IXN 0 BIG; rel ITON IXN 54]
        ++ room m (eaddz IXN 2) 248
        ++ pos ITON (eaddz IXN 1) (ELit 0) 0 BIG ++ str m (eaddz IXN 1) ITON (ELit 0) 248 ++ kn_fixed)
       268%nat (vis m 248).
Definition ITOV2 : expr := EVar 290. Definition IXV2 : expr := EVar 291.
Definition JS_nval (m : smode) : acs :=
  mkcs 0x33264 (mkregs (SSn J5) 295)
       (kn_o ++ [KRange (esub NFv J5) 1 (2 ^ 48); KRange ITOV2 0 INSZ; KRange (esub ITOV2 ITO) 1 INSZ; rel ITOV2 IXV2 48]
        ++ pos ITOV2 IXV2 (ELit 0) 0 BIG ++ strc m IXV2 ITOV2 (ELit 0) 292 ++ kn_fixed)
       313%nat (vis m 292).
Definition JS_ncomma (m : smode) : acs :=
  mkcs 0x3328c (mkregs (SSn J5 ++ [(10, IXV2)])%nat 318)
       (kn_o ++ [KRange (esub NFv J5) 2 (2 ^ 48); KRange ITOV2 0 INSZ; KRange (esub ITOV2 ITO) 1 INSZ; rel ITOV2 IXV2 48] ++ room m (eaddz IXV2 1) 315
        ++ pos ITOV2 IXV2 (ELit 0) 0 BIG ++ str m IXV2 ITOV2 (ELit 0) 315 ++ kn_fixed)
       335%nat (vis m 315).
Definition loop_end_n (lm : lmode) (m' : smode) : plan :=
  match lm, m' with LML, _ => PRun [HEADn] PNext | LMS, MS => PRun [HEADn] PNext | _, _ => PRun [HEADn] (GO CNL ML) end.
Definition after_nval (lm : lmode) (m : smode) : plan :=
  PCase2 (esub NFv J5) 1
     (PRun [0x33d54] (closeo m 292))
     (ENSURE' 47 m 292 JS_ncomma 315 0x33288 0x3328c (loop_end_n lm)).
Definition post_nval (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x33264] (GO CNVAL ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 46 [(JS_nval m, n13 (JS_nval m) (after_nval lm m))] 290 (PRun [0x33264] (PMerge 46))))
  end.
Definition after_c2 (lm : lmode) (m : smode) : plan :=
  PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITON (eaddz IXN 2) 248) (post_nval lm)).
Definition after_q2 (lm : lmode) (m : smode) : plan := ENSURE' 45 m 228 JS_c2 248 0x331f0 0x331f4 (kS lm CC2 (after_c2 lm)).
Definition after_num (lm : lmode) (m : smode) : plan := ENSURE' 44 m 207 JS_q2 228 0x33184 0x33188 (kS lm CQ2 (after_q2 lm)).
Definition post_num (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x33164] (GO CNUM ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 43 [(JS_num m, n13 (JS_num m) (after_num lm m))] 205 (PRun [0x33164] (PMerge 43))))
  end.
Definition after_q1 (lm : lmode) (m : smode) : plan :=
  PRun [B2JUT.GuNumT.BNU] (CALL m 220 223 (NUM_ARGS m ITOJ (eaddz IXJ 1) 160 TAGv) (post_num lm)).
Definition bodyn (lm : lmode) (m : smode) : plan := ENSURE' 42 m 133 JS_q1 160 0x330f0 0x330f4 (kS lm CQ1 (after_q1 lm)).
Definition loopn (m : smode) : plan := PLoopM 130 NFv [(INVn m, bodyn (lmo m) m, PContraH 0)] [].
Definition after_nhdr (m : smode) : plan :=
  PRun [0x330b4] (PBranch (PRun [HEADn] (match m with MS => loopn MS | ML => GO CNL ML end)) (PRun [0x33d54] (closeo m 82))).
Definition okeys_num (m : smode) : plan :=
  PRun [0x327e8] (PBranch (HDR4h 12 m 0x3280c 0x32814 true 0x330a4 true 0x330ac (HOLE 1 m) 80) (ERR_EXIT m)).
Definition after_lcb (m : smode) : plan :=
  PRun [0x327c8] (PCaseReg 10 0 (PRun [0x329e4] (okeys_str m))
                 (PCaseReg 10 2 (PRun [0x327e8] (okeys_num m))
                                 (ERR_EXIT m))).
Definition tag (m : smode) : plan := ENSURE 30 m 36 JS_lcb 60 0x3275c 0x32764 after_lcb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITOh : expr := EVar 82. Definition IXh : expr := EVar 83.
Definition SSoR : list (nat * expr) := [(21, eaddz DEPTH 1); (23, TBL); (24, NFv); (25, eaddz OBJ 1); (26, ELit 1); (27, ELit 58)]%nat.
Definition T_oL : acs := JX ML HEADo SSoR ITOh IXh 47 None [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 1 (2 ^ 48); KRange ITOh 0 INSZ] 84.
Definition SSnR : list (nat * expr) := [(21, eaddz DEPTH 1); (22, NFv); (23, eaddz OBJ 1); (24, ELit 34); (25, ELit 58); (26, ELit 1); (27, ELit 44)]%nat.
Definition T_nL : acs := JX ML HEADn SSnR ITOh IXh 47 None [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NFv 1 (2 ^ 48); KRange ITOh 0 INSZ; KRange (esub ITOh ITO) 1 INSZ] 84.
Definition cutT (c : nat) (m : smode) : acs :=
  match c with
  | 0 => JS_ohdr m | 1 => JS_nhdr m
  | 13 => JS_key m | 14 => JS_colon m | 15 => JS_oval m | 16 => T_oL
  | 17 => JS_q1 m | 18 => JS_num m | 19 => JS_q2 m | 20 => JS_c2 m | 21 => JS_nval m | 22 => T_nL
  | _ => tin m end%nat.
Definition cutK (c : nat) (m : smode) : plan :=
  match c with
  | 0 => after_ohdr m | 1 => after_nhdr m
  | 13 => n13 (JS_key m) (after_keyj LMT m) | 14 => after_colon LMT m | 15 => n13 (JS_oval m) (after_oval LMT m) | 16 => loopo ML
  | 17 => after_q1 LMT m | 18 => n13 (JS_num m) (after_num LMT m) | 19 => after_q2 LMT m | 20 => after_c2 LMT m
  | 21 => n13 (JS_nval m) (after_nval LMT m) | 22 => loopn ML
  | _ => PContraH 0 end%nat.
(* [comment removed for export] *)
Definition live (w : smode) (c : nat) (m : smode) : bool :=
  match c with
  | 0 | 1 => match w, m with ML, MS => false | _, _ => true end
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => match m with ML => true | MS => false end
  | _ => false end%nat.
End B2JUA3.
End B2JU_A3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JU_A4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA4.
Definition HL : expr := EVar 80.
Definition J5 : expr := EVar 130.
Definition ITOJ : expr := EVar 131. Definition IXJ : expr := EVar 132.
Definition TBLe : expr := ELit 0x13208.
(* [comment removed for export] *)
Definition CLOp : list kentry :=
  [KWord (SA e_sp (-176)) 8 G; KWord (SA e_sp (-168)) 8 (eaddz G 96); KWord (SA e_sp (-160)) 8 (eaddz G 88);
   KWord (SA e_sp (-152)) 8 OBJ; KWord (SA e_sp (-144)) 8 (eaddz G 104)].
(* [comment removed for export] *)
Definition BCv : expr := EVar 59.
Definition NTBL : Z := 2 ^ 64 - 1 - 0x13208.      (* [comment removed for export] *)
Definition SSp (bc : expr) : list (nat * expr) := [(21, TBLe); (22, TAGv); (23, bc); (24, ELit NTBL)]%nat.    (* [comment removed for export] *)
Definition JS_p1 (m : smode) := JX m 0x32944 ((10%nat, IX) :: SSp BCv) (eaddz ITO 1) IX 24 (Some (eaddz IX 1)) (CLOp ++ [KRange BCv 1 128]) 60.
Definition callW (m : smode) (k : nat) : plan :=
  PRun [GuWA.c_entry (WAcfg k)] (CALL m (320 + k) (330 + k) (WA_ARGS m (eaddz ITO 1) (eaddz IX 1) 60) post_w).
Definition pvt0 (m : smode) : plan :=      (* [comment removed for export] *)
  PCaseReg 23 3 (ERR_EXIT m) (PCaseReg 23 4 (callW m 8) (PCaseReg 23 7 (ERR_EXIT m) (PCaseReg 23 8 (callW m 9) (ERR_EXIT m)))).
Definition pvt1 (m : smode) : plan :=      (* [comment removed for export] *)
  PCaseReg 23 1 (callW m 0) (PCaseReg 23 2 (callW m 1) (PCaseReg 23 3 (ERR_EXIT m) (PCaseReg 23 4 (callW m 2)
    (PCaseReg 23 7 (ERR_EXIT m) (PCaseReg 23 8 (callW m 3) (ERR_EXIT m)))))).
Definition pvt2 (m : smode) : plan :=      (* [comment removed for export] *)
  PCaseReg 23 1 (callW m 4) (PCaseReg 23 2 (callW m 5) (PCaseReg 23 3 (ERR_EXIT m) (PCaseReg 23 4 (callW m 6)
    (PCaseReg 23 7 (ERR_EXIT m) (PCaseReg 23 8 (callW m 7) (ERR_EXIT m)))))).
(* [comment removed for export] *)
Definition NSv : expr := EVar 81.
Definition ITO1 : expr := eadd (eaddz ITO 1) HL.
(* [comment removed for export] *)
Definition JS_sa0 (m : smode) := JX m 0x34424 [(21%nat, TBLe); (22%nat, TAGv); (23%nat, NSv)]
                                    ITO1 (eaddz IX 1) 47 None (CLOp ++ [KRange HL 1 8; KRange NSv 0 (2 ^ 48)]) 82.
Definition SSs (j : expr) : list (nat * expr) := [(21, TBLe); (23, esub NSv j); (24, eaddz OBJ 1); (25, ELit 1); (26, ELit 2); (27, ELit 44)]%nat.
Definition kn_s : list kentry := [KRange HL 1 8; KRange NSv 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange (esub NSv J5) 1 (2 ^ 48)].
Definition HEADs : Z := 0x34440.
Definition INVs (m : smode) : acs :=
  mkcs HEADs (mkregs (SSs J5) 136)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255] ++ kn_s ++ [KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 2 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       160%nat (vis m 133).
Definition HLK : expr := EVar 160. Definition KVv : expr := EVar 161.
Definition NK : expr := EAlu Instr.ALU_SRL KVv (ELit 2).
Definition ITOK : expr := eadd ITOJ HLK.
Definition JS_sk (m : smode) := JX m 0x3454c ((10%nat, eadd INLO ITOK) :: (11%nat, KVv) :: SSs J5) ITOK IXJ 71 None
                                   (kn_s ++ [KRange ITOJ 0 (INSZ - 1); KRange (esub ITOJ ITO) 2 INSZ; KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3); KRange ITOK 0 INSZ]) 162.
Definition kn_sk : list kentry := kn_s ++ [KRange ITOJ 0 (INSZ - 1); KRange (esub ITOJ ITO) 2 INSZ; KRange HLK 1 8; KRange KVv 0 (2 ^ 50 + 3);
                                           KRange ITOK 0 INSZ; KRange (esub BSZ (eadd ITOK NK)) 0 INSZ].
Definition IXC : expr := EVar 221.
Definition relK (ix : expr) (lo : Z) : kentry :=
  KRange (eadd (esub (escale 24 (esub ITOK ITO)) (esub ix IX)) (escale 2 NK)) lo RELHI.
Definition JS_se (m : smode) : acs :=
  mkcs 0x34588 (mkregs ((22%nat, NK) :: SSs J5) 225)      (* [comment removed for export] *)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255] ++ kn_sk ++ [KRange IXC 0 IXHI2; relK IXC 69]
        ++ posK ITOK IXC (ELit 0) 0 IXHI2 ++ strc m IXC (eadd ITOK NK) (ELit 0) 222 ++ kn_fixed)
       242%nat (vis m 222).
Definition JS_sc (m : smode) := JX m 0x345d0 ((10%nat, IXC) :: SSs J5) (eadd ITOK NK) IXC 68 (Some (eaddz IXC 1))
                                   (kn_sk ++ [KRange IXC 0 BIG; KRange (esub NSv J5) 2 (2 ^ 48)]) 243.
Definition after_se2 (m : smode) : plan :=                   (* [comment removed for export] *)
  PCase2 (esub NSv J5) 1
     (PRun [0x34654] (closeE 111 250 m 222))
     (ENSURE' 108 m 222 JS_sc 243 0x345cc 0x345d0 (fun m' => PRun [HEADs] PNext)).
Definition after_se (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 107 [(JS_se m, n13 (JS_se m) (after_se2 m))] 220 (PRun [0x34588] (PMerge 107)))).
Definition after_sk (m : smode) : plan :=
  PRun [0x34560] (PBranch (PRun [EscU.ENTRY] (CALL m 200 203 (ESC_ARGS ITOK NK IXJ 162) after_se)) (ERR_EXIT m)).
Definition bodys (m : smode) : plan :=
  PRun [0x34448] (PBranch (PViaM 106 [(JS_sk m, after_sk m)] 160 (HDR4m 12 m 0x34458 0x34460 true 0x34548 true 0x3454c 106 160)) (ERR_EXIT m)).
Definition loops (m : smode) : plan :=
  PLoopM 130 NSv (match m with MS => [(INVs MS, bodys MS, PContraH 0); (INVs ML, bodys ML, PContraH 0)]
                              | ML => [(INVs ML, bodys ML, PContraH 0)] end) [].
Definition after_sa0 (m : smode) : plan :=
  PRun [0x3442c] (PBranch (PRun [HEADs] (loops m)) (PRun [0x34654] (closeE 110 120 m 82))).
Definition strarr (m : smode) : plan :=                      (* [comment removed for export] *)
  PRun [0x3397c] (PBranch (HDR4h 12 m 0x33990 0x33998 true 0x3441c true 0x34424 (HOLE 4 m) 80) (ERR_EXIT m)).
Definition pvt3 (m : smode) : plan :=      (* [comment removed for export] *)
  PRun [0x32fac] (PBranch (PRun [0x34654] (closeE 109 120 m 60)) (PRun [0x3397c] (strarr m))).
(* [comment removed for export] *)
Definition P_PVT : Z := 0x32998.
Definition after_p1 (m : smode) : plan :=
  PRun [0x32998] (PCaseReg 10 0 (GO (CPV 0) m) (PCaseReg 10 1 (GO (CPV 1) m) (PCaseReg 10 2 (GO (CPV 2) m) (pvt3 m)))).
Definition plain4 (m : smode) : plan := PRun [0x3272c] (PExt 42 [] (ENSURE 100 m 36 JS_p1 59 0x3293c 0x32944 (GO 2))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NTv : expr := EVar 81. Definition NVv : expr := EVar 82. Definition BCa : expr := EVar 83.
Definition kn_a : list kentry := [KRange HL 1 8; KRange NTv 0 255; KRange NVv 0 (2 ^ 48); KRange BCa 1 128].
Definition ITO2h : expr := eadd (eaddz ITO 2) HL.
Definition JS_ag (m : smode) := JX m 0x333f0 [(10%nat, eadd INLO ITO2h); (11%nat, NVv); (21%nat, BCa); (22%nat, NTv)]
                                   ITO2h IX 72 None (kn_a ++ [KRange (esub BSZ ITO) 3 INSZ]) 84.
Definition ITOA : expr := EVar 110.
Definition kn_ab : list kentry := kn_a ++ [KRange ITOA 0 INSZ; KRange (esub ITOA ITO) 3 INSZ; KRange (esub BSZ ITOA) 0 INSZ; KWord (SA e_sp (-120)) 8 NVv].
Definition JS_ab (m : smode) := JX m 0x3347c [(10%nat, IX); (21%nat, BCa); (22%nat, NTv)] ITOA IX 72 (Some (eaddz IX 1)) kn_ab 111.
(* [comment removed for export] *)
Definition post_wA0 (m : smode) : plan :=    (* [comment removed for export] *)
  match m with MS => PViaM 101 [(JS_pwA MS, cont_pwA MS)] 260 (PMerge 101) | ML => GO CPWA ML end.
Definition callA (m : smode) (k : nat) : plan :=
  PRun [GuAA.c_entry (AAcfg k)] (CALL m (300 + k) (310 + k) (AA_ARGS m ITOA (eaddz IX 1) NVv 111) (if Nat.eqb k 2 then post_wA0 else post_wA)).
Definition avt0 (m : smode) : plan :=
  PCaseReg 21 3 (ERR_EXIT m) (PCaseReg 21 4 (callA m 8) (PCaseReg 21 7 (ERR_EXIT m) (PCaseReg 21 8 (callA m 9) (ERR_EXIT m)))).
Definition avt1 (m : smode) : plan :=
  PCaseReg 21 1 (callA m 0) (PCaseReg 21 2 (callA m 1) (PCaseReg 21 3 (ERR_EXIT m) (PCaseReg 21 4 (callA m 2)
    (PCaseReg 21 7 (ERR_EXIT m) (PCaseReg 21 8 (callA m 3) (ERR_EXIT m)))))).
Definition avt2 (m : smode) : plan :=
  PCaseReg 21 1 (callA m 4) (PCaseReg 21 2 (callA m 5) (PCaseReg 21 3 (ERR_EXIT m) (PCaseReg 21 4 (callA m 6)
    (PCaseReg 21 7 (ERR_EXIT m) (PCaseReg 21 8 (callA m 7) (ERR_EXIT m)))))).
(* [comment removed for export] *)
Definition P_AVT : Z := 0x334d4.
Definition after_ab (m : smode) : plan :=
  PRun [0x334d4] (PCaseReg 10 0 (GO (CAB 0) m) (PCaseReg 10 1 (GO (CAB 1) m) (PCaseReg 10 2 (GO (CAB 2) m) (ERR_EXIT m)))).
Definition after_ag (m : smode) : plan :=
  PRun [0x33404] (PBranch (ERR_EXIT m)
    (PRun [0x33424] (PBranch
       (PRun [0x33438] (PBranch (ERR_EXIT m) (ENSURE 104 m 84 JS_ab 110 0x33474 0x3347c after_ab)))
       (ERR_EXIT m)))).
Definition HDRa (m : smode) : plan :=
  let aarm (hl : Z) := PExt 42 [] (PRun [0x32594] (PBranch (ERR_EXIT m) (PRun [0x325a0] (PExt 42 []
       (if Z.eqb hl 8 then PRun [0x333e4] (PBranch (ERR_EXIT m) (PRun [0x333f0] (PHandoffW (HOLE 3 m) [(80%nat, ELit hl)])))
        else PRun [0x333f0] (PHandoffW (HOLE 3 m) [(80%nat, ELit hl)])))))) in
  PRun [0x3258c] (PCaseReg 15 0 (aarm 1) (PCaseReg 15 1 (aarm 2) (PCaseReg 15 2 (aarm 4) (aarm 8)))).
Definition aligned4 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x32524] (PBranch (ERR_EXIT m) (PRun [0x32538] (PBranch (ERR_EXIT m) (PRun [0x32570] (PBranch (ERR_EXIT m) (HDRa m)))))).
Definition tag (m : smode) : plan := PRun [0x32508] (PBranch (aligned4 m) (plain4 m)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsteps (k : Z) : list dstep := (if Z.eqb k 0 then [] else [DRHi 10 0]) ++ (if Z.leb k 1 then [] else [DRHi 10 1]) ++ [DRLo 10 k].
(* [comment removed for export] *)
Definition PVs (k : Z) (m : smode) : acs := snd (DPATH NXF (JS_p1 m) (DRun [] :: DRun [P_PVT] :: rsteps k) 0).
Definition ABs (k : Z) (m : smode) : acs := snd (DPATH NXF (JS_ab m) (DRun [P_AVT] :: rsteps k) 0).
Definition cutT (c : nat) (m : smode) : acs :=
  match c with
  | 2 => JS_p1 m | 3 => JS_ag m | 4 => JS_sa0 m
  | 7 => PVs 0 m | 8 => PVs 1 m | 9 => PVs 2 m | 10 => ABs 0 m | 11 => ABs 1 m | 12 => ABs 2 m
  | _ => tin m end%nat.
Definition cutK (c : nat) (m : smode) : plan :=
  match c with
  | 2 => after_p1 m | 3 => after_ag m | 4 => after_sa0 m
  | 7 => pvt0 m | 8 => pvt1 m | 9 => pvt2 m | 10 => avt0 m | 11 => avt1 m | 12 => avt2 m
  | _ => PContraH 0 end%nat.
Definition live (w : smode) (c : nat) (m : smode) : bool :=
  match c with 2 | 3 | 4 | 7 | 8 | 9 | 10 | 11 | 12 => match w, m with ML, MS => false | _, _ => true end | _ => false end%nat.
End B2JUA4.
End B2JU_A4.
Module B2JU_A5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA5.
Definition HL : expr := EVar 80.
Definition NVv : expr := EVar 81.
Definition SS5 (n : expr) : list expr := [DEPTH; n].                           (* [comment removed for export] *)
Definition ITO1 : expr := eadd (eaddz ITO 1) HL.
Definition JS_ahdr (m : smode) : acs :=
  mkcs 0x32c44 (regs_free (SS5 NVv) 63)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 0 (2 ^ 48);
                  rel ITO1 IX 48]
        ++ pos ITO1 IX (ELit 0) 0 BIG ++ str m IX ITO1 (ELit 0) 60 ++ kn_fixed)
       82%nat (vis m 60).
Definition JS_lbr (m : smode) : acs :=
  JS_emit m 0x32c78 (ELit 0) ITO1 IX (eaddz IX 1) 0 48 (SS5 NVv) [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 0 (2 ^ 48)] 100.
Definition J5 : expr := EVar 130.
Definition ITOJ : expr := EVar 131. Definition IXJ : expr := EVar 132.
Definition SSL (j : expr) : list expr := [eaddz DEPTH 1; esub NVv j; eaddz OBJ 1; ELit 1; ELit 44].
Definition HEAD : Z := 0x32ce0.
Definition INV5 (m : smode) : acs :=
  mkcs HEAD (regs_free (SSL J5) 136)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 1 (2 ^ 48);
                  KRange (esub NVv J5) 1 (2 ^ 48); KRange ITOJ 0 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 133 ++ kn_fixed)
       152%nat (vis m 133).
Definition ITO2 : expr := EVar 200. Definition IX2 : expr := EVar 201.
Definition JS_elem (m : smode) : acs :=
  mkcs 0x32d08 (regs_free (SSL J5) 205)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255; KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 1 (2 ^ 48);
                  KRange (esub NVv J5) 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO2 0 INSZ; rel ITO2 IX2 48]
        ++ pos ITO2 IX2 (ELit 0) 0 BIG ++ strc m IX2 ITO2 (ELit 0) 202 ++ kn_fixed)
       221%nat (vis m 202).
Definition JS_comma (m : smode) : acs :=
  JS_emit m 0x32d30 (ELit 0) ITO2 IX2 (eaddz IX2 1) 0 48 (SSL J5)
          [KRange HL 1 8; KRange ITO 0 (INSZ - 2); KRange NVv 1 (2 ^ 48); KRange (esub NVv J5) 2 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange ITO2 0 INSZ] 230.
Definition after_elem (m : smode) : plan :=
  PCase2 (esub NVv J5) 1
     (PRun [0x34654] (close5 m 202))
     (ENSURE' 7 m 202 JS_comma 230 0x32d2c 0x32d30 (fun m' => PRun [HEAD] PNext)).
Definition post_call (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 6 [(JS_elem m, n13 (JS_elem m) (after_elem m))] 200 (PRun [0x32d08] (PMerge 6)))).
Definition body5 (m : smode) : plan := PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITOJ IXJ 133) post_call).
Definition loop5 (m : smode) : plan :=
  PLoopM 130 NVv (match m with MS => [(INV5 MS, body5 MS, PContraH 0); (INV5 ML, body5 ML, PContraH 0)]
                              | ML => [(INV5 ML, body5 ML, PContraH 0)] end) [].
Definition after_lbr (m : smode) : plan :=
  PRun [0x32ccc] (PBranch (PRun [HEAD] (loop5 m)) (PRun [0x34654] (close5 m 100))).
Definition tag (m : smode) : plan :=
  PRun [0x325e8] (PBranch (ERR_EXIT m)
  (PViaM 5 (match m with MS => [(JS_ahdr MS, ENSURE 4 MS 60 JS_lbr 100 0x32c70 0x32c78 after_lbr);
                                (JS_ahdr ML, ENSURE 4 ML 60 JS_lbr 100 0x32c70 0x32c78 after_lbr)]
                       | ML => [(JS_ahdr ML, ENSURE 4 ML 60 JS_lbr 100 0x32c70 0x32c78 after_lbr)] end) 60
     (HDR4m 13 m 0x32610 0x32618 false 0x32c38 false 0x32c44 5 80))).
(* [comment removed for export] *)
Definition cutT (c : nat) (m : smode) : acs := tin m.
Definition cutK (c : nat) (m : smode) : plan := PContraH 0.
Definition live (w : smode) (c : nat) (m : smode) : bool := false.
End B2JUA5.
End B2JU_A5.
Module B2JU_A6.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuNumT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module B2JUA6.
Definition HL : expr := EVar 80.
Definition J5 : expr := EVar 140.
Definition ITOJ : expr := EVar 141. Definition IXJ : expr := EVar 142.
Definition MEMCPY : Z := 0x732b0.
Definition ITO2e : expr := eaddz ITO 2.
(* [comment removed for export] *)
Definition JS_nl (m : smode) := JX m 0x33590 [(10%nat, IX); (21%nat, DEPTH); (22%nat, TAGv)] (eaddz ITO 1) IX 24 (Some (eaddz IX 1)) [] 60.
Definition ext0 (m : smode) : plan := ENSURE 60 m 36 JS_nl 60 0x33588 0x33590 EXIT.
(* [comment removed for export] *)
Definition ext1 (m : smode) : plan :=
  let tarm (hl : Z) := PExt 42 [] (PRun [0x3249c] (PBranch (ERR_EXIT m)
                         (PRun [ENTRY] (CALL m 210 213 (SELF_ARGS (eaddz ITO (1 + hl)) IX 36) EXIT)))) in
  PRun [0x3246c] (PBranch (ERR_EXIT m)
    (PRun [0x32494] (PCaseReg 12 0 (tarm 1) (PCaseReg 12 1 (tarm 2) (PCaseReg 12 2 (tarm 4) (tarm 8)))))).
(* [comment removed for export] *)
Definition HB : expr := EVar 59.
Definition S56 (s5 s6 : expr) : list (nat * expr) := [(21%nat, s5); (22%nat, s6)].
Definition JS_m0 (m : smode) := JX m 0x32e8c ((10%nat, eadd INLO ITO) :: S56 DEPTH HB) (eaddz ITO 1) IX 24 None [KRange HB 0 255; KRange (esub BSZ ITO) 2 INSZ] 61.
Definition JS_m1 (m : smode) := JX m 0x33650 ((10%nat, IX) :: S56 DEPTH HB) ITO2e IX 48 (Some (eaddz IX 1)) [KRange HB 0 255] 90.
Definition JS_m2 (m : smode) := JX m 0x336d4 ((11%nat, eaddz IX 1) :: S56 DEPTH HB) ITO2e (eaddz IX 1) 47 (Some (eaddz IX 10)) [KRange HB 0 255] 120.
Definition JS_m3l (m : smode) := JX m 0x33724 ((11%nat, eaddz IX 10) :: S56 DEPTH HB) ITO2e (eaddz IX 10) 38 (Some (eaddz IX 23)) [KRange HB 0 255] 170.
Definition JS_m3r (m : smode) := JX m 0x3374c ((11%nat, eaddz IX 10) :: S56 DEPTH HB) ITO2e (eaddz IX 10) 38 (Some (eaddz IX 24)) [KRange HB 0 255] 170.
Definition LEN : expr := EVar 210.
(* [comment removed for export] *)
Definition JS_m4 (m : smode) := JX m 0x33768 (S56 DEPTH LEN) ITO2e (eaddz IX 10) 38 None [KRange LEN 13 14] 211.
Definition IXL : expr := eadd (eaddz IX 10) LEN.
Definition JS_m5 (m : smode) := JX m 0x33798 ((11%nat, IXL) :: S56 DEPTH LEN) ITO2e IXL 24 (Some (eaddz IXL 1)) [KRange LEN 13 14] 240.
Definition JS_m6 (m : smode) := JX m 0x337d8 ((11%nat, eaddz IXL 1) :: S56 DEPTH LEN) ITO2e (eaddz IXL 1) 23 (Some (eaddz IXL 11)) [KRange LEN 13 14] 270.
Definition ITOS1 : expr := EVar 350. Definition IXS1 : expr := EVar 351.
Definition JS_m7 (m : smode) := JXc m 0x33824 (S56 (eaddz DEPTH 1) LEN) ITOS1 IXS1 14 None [KRange LEN 13 14; KRange ITOS1 0 INSZ] 352.
Definition JS_m8 (m : smode) := JX m 0x33864 ((11%nat, IXS1) :: S56 (eaddz DEPTH 1) LEN) ITOS1 IXS1 14 (Some (eaddz IXS1 1)) [KRange LEN 13 14; KRange ITOS1 0 INSZ] 380.
Definition JS_m9 (m : smode) := JX m 0x338a4 ((11%nat, eaddz IXS1 1) :: S56 (eaddz DEPTH 1) LEN) ITOS1 (eaddz IXS1 1) 13 (Some (eaddz IXS1 9)) [KRange LEN 13 14; KRange ITOS1 0 INSZ; KRange IXS1 0 BIG] 410.
Definition ITOS2 : expr := EVar 470. Definition IXS2 : expr := EVar 471.
(* [comment removed for export] *)
Definition JS_m10 (m : smode) := JXc m 0x33d34 (S56 (eaddz DEPTH 1) LEN) ITOS2 IXS2 5 None [KRange LEN 13 14; KRange ITOS2 0 INSZ] 472.
Definition after_m10 (m : smode) : plan := PRun [0x33d54] (closev 71 500 m 472).
Definition post_m2 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 70 [(JS_m10 m, n13 (JS_m10 m) (after_m10 m))] 470 (PRun [0x33d34] (PMerge 70)))).
Definition after_m9 (m : smode) : plan :=
  PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITOS1 (eaddz IXS1 9) 410) post_m2).
Definition after_m8 (m : smode) : plan := ENSUREL 69 m 380 JS_m9 410 0x3389c 0x338a4 after_m9.
Definition after_m7 (m : smode) : plan := ENSUREL 68 m 352 JS_m8 380 0x3385c 0x33864 after_m8.
Definition post_m1 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 67 [(JS_m7 m, n13 (JS_m7 m) (after_m7 m))] 350 (PRun [0x33824] (PMerge 67)))).
Definition after_m6 (m : smode) : plan :=
  PRun [MEMCPY] (PExt 1 [] (PRun [ENTRY] (CALL m 210 213 (SELF_ARGS ITO2e (eaddz IXL 11) 270) post_m1))).
Definition after_m5 (m : smode) : plan := ENSUREL 66 m 240 JS_m6 270 0x337d0 0x337d8 after_m6.
Definition after_m4 (m : smode) : plan := ENSUREL 65 m 211 JS_m5 240 0x33790 0x33798 after_m5.
Definition after_m3 (len : Z) (m : smode) : plan :=
  PRun [MEMCPY] (PExt 1 [] (PMergeW 64 [(210%nat, ELit len)])).      (* [comment removed for export] *)
Definition after_m2 (m : smode) : plan :=
  PRun [MEMCPY] (PExt 1 [] (PViaM 64 [(JS_m4 ML, GO 6 ML)] 210
    (PRun [0x33714] (PBranch (ENSUREL 63 m 120 JS_m3l 170 0x3371c 0x33724 (after_m3 13))
                             (ENSUREL 63 m 120 JS_m3r 170 0x33744 0x3374c (after_m3 14)))))).
Definition after_m1 (m : smode) : plan := ENSURE 62 m 90 JS_m2 120 0x336cc 0x336d4 after_m2.
Definition after_m0 (m : smode) : plan := ENSURE 61 m 61 JS_m1 90 0x33648 0x33650 after_m1.
Definition ext2 (m : smode) : plan :=
  PRun [0x32e78] (PBranch (PViaM 60 [(JS_m0 m, after_m0 m)] 59 (PRun [0x32e8c] (PMerge 60))) (ERR_EXIT m)).
(* [comment removed for export] *)
Definition CB : expr := EVar 59.
Definition NTAG : expr := escale 32 (EAlu Instr.ALU_SRL CB (ELit 5)).   (* [comment removed for export] *)
Definition kn_x : list kentry := [KRange CB 0 255; KWord (SA e_sp (-176)) 4 NTAG].
Definition JS_x0 (m : smode) := JX m 0x32690 ((10%nat, eadd INLO ITO) :: (12%nat, CB) :: S56 DEPTH TAGv) (eaddz ITO 1) IX 24 None [KRange CB 0 255; KRange (esub BSZ ITO) 2 INSZ] 61.
Definition JS_x1 (m : smode) := JX m 0x33dc4 ((11%nat, IX) :: S56 DEPTH TAGv) ITO2e IX 48 (Some (eaddz IX 1)) kn_x 90.
Definition ITOC1 : expr := EVar 150. Definition IXC1 : expr := EVar 151.
Definition JS_x2 (m : smode) := JXc m 0x33e04 (S56 DEPTH TAGv) ITOC1 IXC1 55 None (kn_x ++ [KRange ITOC1 0 INSZ; KRange (esub ITOC1 ITO) 2 INSZ]) 152.
Definition JS_x3 (m : smode) := JX m 0x33e74 ((11%nat, IXC1) :: S56 DEPTH TAGv) ITOC1 IXC1 55 (Some (eaddz IXC1 1)) (kn_x ++ [KRange ITOC1 0 INSZ; KRange (esub ITOC1 ITO) 2 INSZ]) 180.
Definition ITOC2 : expr := EVar 240. Definition IXC2 : expr := EVar 241.
Definition JS_x4 (m : smode) := JXc m 0x34350 (S56 DEPTH TAGv) ITOC2 IXC2 61 None [KRange ITOC2 0 INSZ; KRange (esub ITOC2 ITO) 2 INSZ] 242.
Definition post_x2 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 83 [(JS_x4 m, n13 (JS_x4 m) (PRun [0x34370] (close5Av 84 270 m 242)))] 240 (PRun [0x34350] (PMerge 83)))).
Definition after_x3 (m : smode) : plan :=
  PRun [B2JUT.GuNumT.BNI] (CALL m 230 233 (NUM_ARGS m ITOC1 (eaddz IXC1 1) 180 NTAG) post_x2).
Definition after_x2 (m : smode) : plan := ENSURE' 82 m 152 JS_x3 180 0x33e70 0x33e74 after_x3.
Definition post_x1 (m : smode) : plan :=
  PRun [] (PBranchP (EXIT m) (PViaM 81 [(JS_x2 m, n13 (JS_x2 m) (after_x2 m))] 150 (PRun [0x33e04] (PMerge 81)))).
Definition after_x1 (m : smode) : plan :=
  PRun [B2JUT.GuNumT.BNI] (CALL m 230 233 (NUM_ARGS m ITO2e (eaddz IX 1) 90 NTAG) post_x1).
Definition cplx_single (m : smode) : plan := ENSURE' 80 m 61 JS_x1 90 0x33dc0 0x33dc4 after_x1.
(* [comment removed for export] *)
Definition NCv : expr := EVar 81.
Definition ITO2c : expr := eadd (eaddz ITO 2) HL.
Definition JS_ca0 (m : smode) := JX m 0x34060 (S56 NCv TAGv) ITO2c IX 72 None (kn_x ++ [KRange HL 1 8; KRange NCv 0 (2 ^ 48)]) 82.
Definition JS_ca1 (m : smode) := JX m 0x3408c ((11%nat, IX) :: S56 NCv TAGv) ITO2c IX 72 (Some (eaddz IX 1)) (kn_x ++ [KRange HL 1 8; KRange NCv 0 (2 ^ 48)]) 110.
Definition SSc (j : expr) : list (nat * expr) :=
  [(21, esub NCv j); (22, ELit 91); (23, eaddz OBJ 1); (24, ELit 44); (25, ELit 93); (26, ELit 1)]%nat.
Definition kn_ca : list kentry := kn_x ++ [KRange HL 1 8; KRange NCv 1 (2 ^ 48); KRange J5 0 (2 ^ 48); KRange (esub NCv J5) 1 (2 ^ 48)].
Definition HEADc : Z := 0x340bc.
Definition INVc (m : smode) : acs :=
  mkcs HEADc (mkregs ((11%nat, IXJ) :: SSc J5) 146)       (* [comment removed for export] *)
       (frame ++ [KWord (SA e_sp (-121)) 1 TAGv; KRange DEPTH 0 255] ++ kn_ca ++ [KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 3 INSZ; rel ITOJ IXJ 47]
        ++ pos ITOJ IXJ (ELit 0) 0 BIG ++ str m IXJ ITOJ (ELit 0) 143 ++ kn_fixed)
       165%nat (vis m 143).
Definition JS_cb1 (m : smode) := JX m 0x340dc ((11%nat, IXJ) :: SSc J5) ITOJ IXJ 47 (Some (eaddz IXJ 1)) (kn_ca ++ [KRange ITOJ 0 INSZ; KRange (esub ITOJ ITO) 3 INSZ]) 165.
Definition DI1 : expr := EVar 215. Definition IXN1 : expr := EVar 216. Definition ITON1 : expr := eadd ITOJ DI1.
Definition kn_cb2 : list kentry := kn_ca ++ [KRange ITOJ 0 INSZ; KRange DI1 0 8; KRange ITON1 0 INSZ; KRange (esub ITON1 ITO) 3 INSZ; KRange IXN1 0 BIG].
Definition JS_cb2 (m : smode) := JXc m 0x34140 (SSc J5) ITON1 IXN1 54 None kn_cb2 217.
Definition JS_cb3 (m : smode) := JX m 0x34164 ((10%nat, IXN1) :: SSc J5) ITON1 IXN1 54 (Some (eaddz IXN1 1)) kn_cb2 240.
Definition DI2 : expr := EVar 290. Definition IXN2 : expr := EVar 291. Definition ITON2 : expr := eadd ITOJ DI2.
Definition kn_cb4 : list kentry := kn_ca ++ [KRange ITOJ 0 INSZ; KRange DI2 0 16; KRange ITON2 0 INSZ; KRange (esub ITON2 ITO) 3 INSZ; KRange IXN2 0 BIG].
Definition JS_cb4 (m : smode) := JXc m 0x341c8 (SSc J5) ITON2 IXN2 61 None kn_cb4 292.
Definition JS_cb5 (m : smode) := JX m 0x341ec ((10%nat, IXN2) :: SSc J5) ITON2 IXN2 61 (Some (eaddz IXN2 1)) kn_cb4 315.
Definition JS_cb6 (m : smode) := JX m 0x34250 ((11%nat, eaddz IXN2 1) :: SSc J5) ITON2 (eaddz IXN2 1) 60 (Some (eaddz IXN2 2))
                                    (kn_cb4 ++ [KRange (esub NCv J5) 2 (2 ^ 48)]) 340.
Definition loop_end_c (lm : lmode) (m' : smode) : plan :=
  match lm, m' with LML, _ => PRun [HEADc] PNext | LMS, MS => PRun [HEADc] PNext | _, _ => PRun [HEADc] (GO CCL ML) end.
Definition after_cb5 (lm : lmode) (m : smode) : plan :=                   (* [comment removed for export] *)
  PCase2 (esub NCv J5) 1
     (PRun [0x34370] (close5Av 98 340 m 315))
     (ENSURE' 97 m 315 JS_cb6 340 0x3424c 0x34250 (loop_end_c lm)).
Definition after_cb4 (lm : lmode) (m : smode) : plan := ENSURE' 96 m 292 JS_cb5 315 0x341e8 0x341ec (kS lm CCB5 (after_cb5 lm)).
Definition post_cb2 (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x341c8] (GO CCB4 ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 95 [(JS_cb4 m, n13 (JS_cb4 m) (after_cb4 lm m))] 290 (PRun [0x341c8] (PMerge 95))))
  end.
Definition after_cb3 (lm : lmode) (m : smode) : plan :=
  PRun [B2JUT.GuNumT.BNI] (CALL m 230 233 (NUM_ARGS m ITON1 (eaddz IXN1 1) 240 NTAG) (post_cb2 lm)).
Definition after_cb2 (lm : lmode) (m : smode) : plan := ENSURE' 94 m 217 JS_cb3 240 0x34160 0x34164 (kS lm CCB3 (after_cb3 lm)).
Definition post_cb1 (lm : lmode) (m : smode) : plan :=
  match lm, m with
  | LMS, ML | LMT, ML => PRun [] (PBranchP (EXIT ML) (PRun [0x34140] (GO CCB2 ML)))
  | _, _ => PRun [] (PBranchP (EXIT m) (PViaM 93 [(JS_cb2 m, n13 (JS_cb2 m) (after_cb2 lm m))] 215 (PRun [0x34140] (PMerge 93))))
  end.
Definition after_cb1 (lm : lmode) (m : smode) : plan :=
  PRun [B2JUT.GuNumT.BNI] (CALL m 230 233 (NUM_ARGS m ITOJ (eaddz IXJ 1) 165 NTAG) (post_cb1 lm)).
Definition bodyc (lm : lmode) (m : smode) : plan := ENSURE' 92 m 143 JS_cb1 165 0x340d8 0x340dc (kS lm CCB1 (after_cb1 lm)).
Definition loopc (m : smode) : plan := PLoopM 140 NCv [(INVc m, bodyc (lmo m) m, PContraH 0)] [].
Definition after_ca1 (m : smode) : plan :=                   (* [comment removed for export] *)
  PRun [0x340a8] (PBranch (PRun [HEADc] (match m with MS => loopc MS | ML => GO CCL ML end)) (PRun [0x34370] (close5Av 91 140 m 110))).
Definition after_ca0 (m : smode) : plan := ENSURE' 90 m 82 JS_ca1 110 0x34088 0x3408c after_ca1.
Definition cplx_array (m : smode) : plan :=                  (* [comment removed for export] *)
  PRun [0x335e0] (PBranch (ERR_EXIT m) (HDR4h 13 m 0x33608 0x33610 false 0x34058 true 0x34060 (HOLE 5 m) 80)).
Definition after_x0 (m : smode) : plan :=                    (* [comment removed for export] *)
  PRun [0x326a0] (PBranch (PRun [0x33dc0] (cplx_single m)) (PRun [0x335e0] (cplx_array m))).
Definition ext3 (m : smode) : plan :=
  PRun [0x32678] (PBranch (ERR_EXIT m) (PViaM 79 [(JS_x0 m, after_x0 m)] 59 (PRun [0x32690] (PMerge 79)))).
Definition tag (m : smode) : plan :=
  PRun [0x3243c] (PCaseReg 11 0 (PRun [0x32e34] (ext0 m)) (PCaseReg 11 1 (PRun [0x32454] (ext1 m))
                 (PCaseReg 11 2 (PRun [0x32e64] (ext2 m)) (PCaseReg 11 3 (PRun [0x32660] (ext3 m)) (ERR_EXIT m))))).
(* [comment removed for export] *)
Definition ITOh : expr := EVar 82. Definition IXh : expr := EVar 83.
Definition SScR : list (nat * expr) := [(21, NCv); (22, ELit 91); (23, eaddz OBJ 1); (24, ELit 44); (25, ELit 93); (26, ELit 1)]%nat.
Definition T_cL : acs := JX ML HEADc ((11%nat, IXh) :: SScR) ITOh IXh 47 None (kn_x ++ [KRange HL 1 8; KRange NCv 1 (2 ^ 48); KRange ITOh 0 INSZ; KRange (esub ITOh ITO) 3 INSZ]) 84.
Definition cutT (c : nat) (m : smode) : acs :=
  match c with
  | 5 => JS_ca0 m | 6 => JS_m4 m
  | 23 => JS_cb1 m | 24 => JS_cb2 m | 25 => JS_cb3 m | 26 => JS_cb4 m | 27 => JS_cb5 m | 28 => T_cL
  | _ => tin m end%nat.
Definition cutK (c : nat) (m : smode) : plan :=
  match c with
  | 5 => after_ca0 m | 6 => after_m4 m
  | 23 => after_cb1 LMT m | 24 => n13 (JS_cb2 m) (after_cb2 LMT m) | 25 => after_cb3 LMT m | 26 => n13 (JS_cb4 m) (after_cb4 LMT m)
  | 27 => after_cb5 LMT m | 28 => loopc ML
  | _ => PContraH 0 end%nat.
Definition live (w : smode) (c : nat) (m : smode) : bool :=
  match c, w, m with
  | 5, ML, MS => false | 5, _, _ => true | 6, _, ML => true
  | (23 | 24 | 25 | 26 | 27 | 28), _, ML => true
  | _, _, _ => false end%nat.
End B2JUA6.
End B2JU_A6.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallRec OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import EscU.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export B2JUT.
Import B2JU_A0 B2JU_A1 B2JU_A2 B2JU_A3 B2JU_A4 B2JU_A5 B2JU_A6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
Module B2JU.
Definition tagk (k : nat) (m : smode) : plan :=
  match k with
  | 0 => B2JUA0.tag m | 1 => B2JUA1.tag m | 2 => B2JUA2.tag m | 3 => B2JUA3.tag m
  | 4 => B2JUA4.tag m | 5 => B2JUA5.tag m | _ => B2JUA6.tag m
  end%nat.
(* [comment removed for export] *)
Definition cutT (c : nat) (m : smode) : acs :=
  match c with
  | 0 | 1 => B2JUA3.cutT c m | 2 | 3 | 4 => B2JUA4.cutT c m | 5 | 6 => B2JUA6.cutT c m
  | 7 | 8 | 9 | 10 | 11 | 12 => B2JUA4.cutT c m
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => B2JUA3.cutT c m
  | 23 | 24 | 25 | 26 | 27 | 28 => B2JUA6.cutT c m
  | 29 => JS_pw m | 30 => JS_pwA m | _ => tin m
  end%nat.
Definition cutK (c : nat) (m : smode) : plan :=
  match c with
  | 0 | 1 => B2JUA3.cutK c m | 2 | 3 | 4 => B2JUA4.cutK c m | 5 | 6 => B2JUA6.cutK c m
  | 7 | 8 | 9 | 10 | 11 | 12 => B2JUA4.cutK c m
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => B2JUA3.cutK c m
  | 23 | 24 | 25 | 26 | 27 | 28 => B2JUA6.cutK c m
  | 29 => cont_pw m | 30 => cont_pwA m | _ => PContraH 0
  end%nat.
Definition live (w : smode) (c : nat) (m : smode) : bool :=
  match c with
  | 0 | 1 => B2JUA3.live w c m | 2 | 3 | 4 => B2JUA4.live w c m | 5 | 6 => B2JUA6.live w c m
  | 7 | 8 | 9 | 10 | 11 | 12 => B2JUA4.live w c m
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => B2JUA3.live w c m
  | 23 | 24 | 25 | 26 | 27 | 28 => B2JUA6.live w c m
  | 29 | 30 => match m with ML => true | MS => false end
  | _ => false
  end%nat.
Definition NC : nat := 31.

(* [comment removed for export] *)
Definition CL_0 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 0 ML.
Definition CL_1 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 1 ML.
Definition CL_2 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 2 ML.
Definition CL_3 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 3 ML.
Definition CL_4 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 4 ML.
Definition CL_5 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 5 ML.
Definition CL_6 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 6 ML.
Definition CL_7 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 7 ML.
Definition CL_8 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 8 ML.
Definition CL_9 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 9 ML.
Definition CL_10 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 10 ML.
Definition CL_11 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 11 ML.
Definition CL_12 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 12 ML.
Definition CL_13 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 13 ML.
Definition CL_14 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 14 ML.
Definition CL_15 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 15 ML.
Definition CL_16 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 16 ML.
Definition CL_17 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 17 ML.
Definition CL_18 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 18 ML.
Definition CL_19 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 19 ML.
Definition CL_20 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 20 ML.
Definition CL_21 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 21 ML.
Definition CL_22 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 22 ML.
Definition CL_23 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 23 ML.
Definition CL_24 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 24 ML.
Definition CL_25 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 25 ML.
Definition CL_26 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 26 ML.
Definition CL_27 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 27 ML.
Definition CL_28 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 28 ML.
Definition CL_29 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 29 ML.
Definition CL_30 : acs * plan := Eval vm_compute in B2JUT.cut_entry cutT cutK live ML 30 ML.
Definition CL (c : nat) : acs * plan := match c with 0 => CL_0 | 1 => CL_1 | 2 => CL_2 | 3 => CL_3 | 4 => CL_4 | 5 => CL_5 | 6 => CL_6 | 7 => CL_7 | 8 => CL_8 | 9 => CL_9 | 10 => CL_10 | 11 => CL_11 | 12 => CL_12 | 13 => CL_13 | 14 => CL_14 | 15 => CL_15 | 16 => CL_16 | 17 => CL_17 | 18 => CL_18 | 19 => CL_19 | 20 => CL_20 | 21 => CL_21 | 22 => CL_22 | 23 => CL_23 | 24 => CL_24 | 25 => CL_25 | 26 => CL_26 | 27 => CL_27 | 28 => CL_28 | 29 => CL_29 | _ => CL_30 end%nat.
Fixpoint weave (ms : list (acs * plan)) (c : nat) : list (acs * plan) :=
  match ms with [] => [] | e :: r => e :: CL c :: weave r (Datatypes.S c) end.
Definition TAGS_ML : list (acs * plan) := Eval vm_compute in map (fun k => (ATs (Z.of_nat k) ML, PRun [] (tagk k ML))) (seq 0 7).
Definition TAGS_MS : list (acs * plan) := Eval vm_compute in map (fun k => (ATs (Z.of_nat k) MS, PRun [] (tagk k MS))) (seq 0 7).
Definition MSE_ML : list (acs * plan) := Eval vm_compute in map (fun c => B2JUT.cut_entry cutT cutK live ML c MS) (seq 0 NC).
Definition MSE_MS : list (acs * plan) := Eval vm_compute in map (fun c => B2JUT.cut_entry cutT cutK live MS c MS) (seq 0 NC).
Definition CUTSL_ML : list (acs * plan) := TAGS_ML ++ weave MSE_ML 0.
Definition CUTSL_MS : list (acs * plan) := TAGS_MS ++ weave MSE_MS 0.
Definition CUTS (w : smode) : list (acs * plan) := match w with ML => CUTSL_ML | MS => CUTSL_MS end.


Definition cert_stmt (w : smode) (i : nat) : Prop :=
  match nth_error (CUTS w) i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check USEGS IT AUBSAN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (CUTS w) (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh
  | None => True
  end.
Definition top_stmt (w : smode) : Prop :=
  exists sh, gplan_ok (top w) = true /\ holes_only sh = true /\
      check USEGS IT AUBSAN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (CUTS w) 0) 0%nat BFUEL FUEL None (ce_tin (ce w)) (top w) = COk sh.
Lemma CUTS_len : forall w, length (CUTS w) = 69%nat. Proof. destruct w; reflexivity. Qed.
End B2JU.

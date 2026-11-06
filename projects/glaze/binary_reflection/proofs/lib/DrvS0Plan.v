(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ERRNO : Z := 0x8647c.
Definition PERM_E : list (expr * expr) := PERM_T ++ [(ELit ERRNO, ELit 4)].
Definition P_STRNLEN : Z := DN2.P_STRNLEN.
Definition NZB : list nat := [1%nat; 2%nat].     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition XNE (nzb : list nat) (dird : bool) := DN2.XNe PSEGS ADRV NXD GDRV nzb dird.
Definition XEE := DN2.XEe PSEGS NXD.
(* [comment removed for export] *)
Definition ITE : itab := mk_itab_ranges PSEGS ((0x614a8, 3%nat) :: DRANGES).
Lemma ITE_ok : itab_sound PSEGS ITE.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition CHKe (nzb : list nat) (dird : bool) (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  check PSEGS ITE ADRV NXD LIMIT (XNE nzb dird) XEE XB0 XC0 hs 0%nat bf fuel None cs p.

(* [comment removed for export] *)
Definition END0' : expr := EAlu Instr.ALU_ADD STR0 L0.
(* [comment removed for export] *)
Definition knXu : list kentry :=
  [KRange END0' 0 (HI47 - 9); KUnk (SA STR0 0) (EAlu Instr.ALU_ADD L0 (ELit 8)); KWr (SA (ELit 0) ERRNO) (ELit 4)].
Definition mkE (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs := ACS (mk_ss p regs k nx) [] 0 YLO 0 [] PERM_E 0 (eaddz SP0 0) FdStd false.

(* [comment removed for export] *)
Definition tMu (argc : kentry) : acs := mkE P_MAIN regsM (argc :: knXu ++ knM) 29%nat.
Definition tMu1 : acs := tMu (KRange ARGC 1 1).
Definition tMu3 : acs := tMu (KRange ARGC 3 1024).

Definition SE : list Z := [P_STDIO_WRITE; P_EXIT; P_MEMCPY; P_STRNLEN].
Definition pEX : plan := PRun SE (PEmit 65 [] PExit).
Definition pW (k : plan) : plan := PRun SE (PEmit 66 [] k).
(* [comment removed for export] *)
Definition pS_A : plan := PRun SE (PExt 5 [] (PRun SE (PExt 1 [] (pW pEX)))).
Definition pS_B : plan := PRun SE (PExt 5 [] (pW (pW pEX))).
Definition pS_C : plan := pW (PRun SE (PExt 1 [] (pW pEX))).
Definition pS3 (L : expr) (a b : Z) : plan := PSplit L a pS_A (PSplit L b pS_B pS_C).
(* [comment removed for export] *)
Definition planU : plan := PRun SE (PExt 1 [] (PRun SE (PExt 1 [] (PRun SE (PExt 67 [] (PRun SE (PExt 1 [] (PRun SE (pS3 L0 66 73))))))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AERR : expr := EVar (nxt hOPEN).
Definition knXo : list kentry := [KRange AERR (two64 - 4095) (two64 - 1); KWr (SA (ELit 0) ERRNO) (ELit 4)].
Definition tCO : acs :=
  ACS (mk_ss P_AFTER_ECALL (sr_upd (s_regs (a_ss hOPEN)) 10 AERR) (knXo ++ kn hOPEN) (Datatypes.S (nxt hOPEN)))
      [] 0 YLO 0 [] PERM_E 0 (eaddz SP0 0) FdStd false.
Definition planCO : plan := PRun SE (PExt 1 [] (PRun SE (PExt 1 [] (PRun SE (PExt 67 [] (PRun SE (PExt 1 [] (PRun SE (pS3 L1 62 63))))))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tRF : acs :=
  ACS (mk_ss DrvS2Plan.P_AFTER_ECALL (s_regs (a_ss tVRb)) (KWr (SA (ELit 0) ERRNO) (ELit 4) :: kn tVRb) NXR)
      [] 0 YLO 0 (a_vis tVRb) PERM_E 0 (eaddz SP0 0) FdStd false.
Definition pX1 (k : plan) : plan := PRun SE (PExt 1 [] k).
(* [comment removed for export] *)
Definition planRF : plan := pX1 (pX1 (pX1 (pX1 (pX1 (pX1 (pW pEX)))))).

(* [comment removed for export] *)
Definition knP : list kentry :=
  [KRange D1 64 4194304; KRange L1 0 131071; KWord (SA END1 0) 1 (ELit 0);
   KRange END1' 0 (HI47 - 9); KUnk (SA STR1 0) (EAlu Instr.ALU_ADD L1 (ELit 8))].
Definition tR0d' : acs := ACS (mk_ss P_AFTER_MALLOC1 (sr_upd regsR0 18 STR1) (knP ++ kn1) 29%nat) [] 0 YLO 0 [(BUF, ELit 65536)] PERM_T 0 (eaddz SP0 0) FdStd false.
Definition tR0e : acs := ACS (mk_ss P_AFTER_MALLOC1 (sr_upd regsR0 18 STR1) (KWr (SA (ELit 0) ERRNO) (ELit 4) :: KBlob (SA STR1 0) L1 2 :: knP ++ kn1) 29%nat)
                            [] 0 YLO 0 [(BUF, ELit 65536)] PERM_E 0 (eaddz SP0 0) FdStd false.
Lemma entN1d : ENT29 hN1 tR0d' [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma thN1d : nth_error (TH29 hN1 tR0d' []) 4 = Some FLEN /\ nth_error (TH29 hN1 tR0d' []) 0 = Some SP0
              /\ nth_error (TH29 hN1 tR0d' []) 5 = Some D1 /\ nth_error (TH29 hN1 tR0d' []) 6 = Some L1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition SEd : list Z := DrvS2Plan.P_ECALL :: SE.
(* [comment removed for export] *)
Definition planD : plan := PRun SEd (PExt 68 [] (PRun SE (PExt 1 [] (PRun SE (PExt 1 [] (PRun SE (PExt 67 [] (PRun SE (PExt 1 [] (PRun SE (pS3 L1 60 61))))))))))).

(* [comment removed for export] *)
Definition zUSAGE1 : list Z := [117; 115; 97; 103; 101; 58; 32].                  (* [comment removed for export] *)
Definition zUSAGE2 : list Z := [32; 73; 78; 80; 85; 84; 10].                     (* [comment removed for export] *)
Definition zCO : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32].   (* [comment removed for export] *)
Definition zNL : list Z := [10].
Definition zRE : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32].   (* [comment removed for export] *)
Definition zRF : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32;
                           98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition shS3 (L : expr) (a b : Z) (pre : list Z) (j : nat) (suf : list Z) : shape :=
  SCase L a (SEmitP 2 [SPLit pre; SPBlob j; SPLit suf] (SEmitP 1 [] (SExit 2)))
    (SCase L b (SEmitP 2 [SPLit pre; SPBlob j; SPLit suf] (SEmitP 2 [] (SEmitP 1 [] (SExit 2))))
               (SEmitP 2 [SPLit pre; SPBlob j] (SEmitP 2 [SPLit suf] (SEmitP 1 [] (SExit 2))))).
Lemma certU1 : CHKe NZB false HS0 BF FUEL tMu1 planU = COk (shS3 L0 66 73 zUSAGE1 1 zUSAGE2). Proof. vm_compute. reflexivity. Qed.
Lemma certU3 : CHKe NZB false HS0 BF FUEL tMu3 planU = COk (shS3 L0 66 73 zUSAGE1 1 zUSAGE2). Proof. vm_compute. reflexivity. Qed.
Lemma certCO : CHKe NZB false HS0 BF FUEL tCO planCO = COk (shS3 L1 62 63 zCO 2 zNL). Proof. vm_compute. reflexivity. Qed.
Lemma certRF : CHKe [] false HS0 BF FUEL tRF planRF = COk (SEmitP 2 [SPLit zRF] (SEmitP 1 [] (SExit 2))). Proof. vm_compute. reflexivity. Qed.
Lemma certD : CHKe NZB true HS0 BF FUEL tR0e planD = COk (shS3 L1 60 61 zRE 2 zNL). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma tR0e_parts : kn tR0e = KWr (SA (ELit 0) ERRNO) (ELit 4) :: KBlob (SA STR1 0) L1 2 :: kn tR0d' /\ a_vis tR0e = a_vis tR0d' /\ a_brk tR0e = a_brk tR0d'
                   /\ a_ylo tR0e = a_ylo tR0d' /\ a_maps tR0e = a_maps tR0d' /\ s_log (a_ss tR0e) = [] /\ pc tR0e = pc tR0d'
                   /\ s_regs (a_ss tR0e) = s_regs (a_ss tR0d') /\ nxt tR0e = nxt tR0d'.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma tRF_parts : kn tRF = KWr (SA (ELit 0) ERRNO) (ELit 4) :: kn tVRb /\ a_vis tRF = a_vis tVRb /\ a_brk tRF = a_brk tVRb /\ a_ylo tRF = a_ylo tVRb
                  /\ a_maps tRF = a_maps tVRb /\ s_log (a_ss tRF) = [] /\ pc tRF = pc tVRb /\ s_regs (a_ss tRF) = s_regs (a_ss tVRb)
                  /\ nxt tRF = nxt tVRb.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma tCO_parts : kn tCO = knXo ++ kn hOPEN /\ a_vis tCO = [] /\ a_brk tCO = a_brk hOPEN /\ a_ylo tCO = a_ylo hOPEN /\ a_maps tCO = a_maps hOPEN
                  /\ s_log (a_ss tCO) = [] /\ pc tCO = P_AFTER_ECALL /\ s_regs (a_ss tCO) = sr_upd (s_regs (a_ss hOPEN)) 10 AERR
                  /\ fresh_ok NXD hOPEN = true /\ a_vis hOPEN = [] /\ Nat.leb NXD (nxt hOPEN) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

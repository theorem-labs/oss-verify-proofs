(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic HUExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev HUStdioDefs HUStdioWrite.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec HU_code_26b000_26c000 HU_code_26f000_270000 HU_code_270000_271000 HU_code_277000_278000 HU_code_dc000_dd000 HU_code_dd000_de000   .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

(* [comment removed for export] *)
Module H0Exit_run1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StepTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.WalkTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibAtomic HUExitBase.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 s1 s2 s3 code : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x351d58) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b1850)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x351b38) [Z_to_bv 8 1].

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x351d58) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x351d7b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x351b3c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x351b48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b17ec : word) mem rom)
                 (mkst regs' (0x2b17a0 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2b1854
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Malk Mahd.
  unfold mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_26bc00 D_26bc00. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_26bc04 D_26bc04 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_26bc08 D_26bc08 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26bc0c D_26bc0c.
    stepn F_26bc10 D_26bc10. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_26bc14 D_26bc14 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_26bc18 D_26bc18.
    stepn F_26bc1c D_26bc1c.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_26bc20 | reflexivity | exact D_26bc20
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_26bc24 | reflexivity | exact D_26bc24 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_26bc28 | reflexivity | exact D_26bc28
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_26bc2c D_26bc2c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26bc30 D_26bc30.
    (* [comment removed for export] *)
    stepb_ft F_26bc34 D_26bc34 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_26bc38 D_26bc38 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26bc5c D_26bc5c. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_26bc60 D_26bc60.
    (* [comment removed for export] *)
    stepn F_26ba1c D_26ba1c. sp_renorm.
    stepST F_26ba20 D_26ba20 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b1850) ltac:(sok_stack SOK).
    stepST F_26ba24 D_26ba24 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_26ba28 D_26ba28 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_26ba2c D_26ba2c (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_26ba30 D_26ba30 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26ba34 D_26ba34.
    stepn F_26ba38 D_26ba38.
    stepn F_26ba3c D_26ba3c.
    stepn F_26ba40 D_26ba40.
    stepn F_26ba44 D_26ba44.
    (* [comment removed for export] *)
    stepn F_2772d8 D_2772d8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2772dc | reflexivity | exact D_2772dc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_2772e0 D_2772e0 ltac:(cond_compute).
    stepret F_2774d0 D_2774d0 (0x2b1634 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_26ba48 D_26ba48 (Z_to_bv 64 0).
    stepb_tk F_26ba4c D_26ba4c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26babc D_26babc.
    stepST F_26bac0 D_26bac0 (Z_to_bv 64 0x351b38) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_26bac4 D_26bac4.
    stepLD8 F_26bac8 D_26bac8 (Z_to_bv 64 0x2b1850).
    stepLD8 F_26bacc D_26bacc code.
    stepLD8 F_26bad0 D_26bad0 (getr regs 9).
    stepLD8 F_26bad4 D_26bad4 (getr regs 18).
    stepLD8 F_26bad8 D_26bad8 (getr regs 19).
    stepn F_26badc D_26badc. sp_renorm.
    stepn F_26bae0 D_26bae0.
    (* [comment removed for export] *)
    stepLD F_277560 D_277560 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_277564 D_277564 ltac:(cond_compute).
    stepret F_277568 D_277568 (0x2b1850 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26bc64 D_26bc64.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b1854)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b17d0)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c1730)))
    (Z_to_bv 64 (bv_unsigned sp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c1738)))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b17d0)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c1730)))
    (Z_to_bv 64 0x31ef08) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2b1854 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x31d5b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c1740)) ->
  rdn RSEGS mem (Z_to_bv 64 0x31d5c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c1730)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2c1730) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe18f0)) ->   (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x2c1738) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2670)) ->   (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x32efa0) 1%nat = Some [Z_to_bv 8 0] ->                                (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x31ef08) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x31cfe0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b16d0)) ->   (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x31cfe8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x31e5c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31e5c8)) ->   (* [comment removed for export] *)
  exists regs',
    msteps RSEGS (mkst regs (0x2b17a0 : word) mem rom)
                 (mkst regs' (0x2b5034 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2b1858
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mfa1 Mflag Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_26bbb4 D_26bbb4. rewrite Hsp. sp_renorm.
    stepST F_26bbb8 D_26bbb8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b1854) ltac:(sok_stack SOK).
    stepST F_26bbbc D_26bbbc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_26bbc0 D_26bbc0 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26bbc4 D_26bbc4.
    stepn F_26bbc8 D_26bbc8.
    stepLD8 F_26bbcc D_26bbcc (Z_to_bv 64 0x2c1740).
    stepLD8 F_26bbd0 D_26bbd0 (Z_to_bv 64 0x2c1730).
    (* [comment removed for export] *)
    stepb_ft F_26bbd4 D_26bbd4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_26bbd8 D_26bbd8 (Z_to_bv 64 0xe2670).
    stepn F_26bbdc D_26bbdc.
    stepjr F_26bbe0 D_26bbe0 (Z_to_bv 64 0xe2670) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_ddbd8 D_ddbd8. sp_renorm.
    stepST F_ddbdc D_ddbdc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2b17d0) ltac:(sok_stack SOK).
    stepST F_ddbe0 D_ddbe0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c1730) ltac:(sok_stack SOK).
    stepST F_ddbe4 D_ddbe4 (Z_to_bv 64 (bv_unsigned sp - 72)) (Z_to_bv 64 0x2c1738) ltac:(sok_stack SOK).
    stepn F_ddbe8 D_ddbe8.
    stepn F_ddbec D_ddbec.
    stepn F_ddbf0 D_ddbf0.
    stepLBU F_ddbf4 D_ddbf4 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mflag).
    stepb_tk F_ddbf8 D_ddbf8 ltac:(cond_compute).
    stepLD8 F_ddca8 D_ddca8 (Z_to_bv 64 0x2b17d0).
    stepLD8 F_ddcac D_ddcac (Z_to_bv 64 0x2c1730).
    stepLD8 F_ddcb0 D_ddcb0 (Z_to_bv 64 0x2c1738).
    stepn F_ddcb4 D_ddcb4. sp_renorm.
    stepret F_ddcb8 D_ddcb8 (0x2b17d0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26bbe4 D_26bbe4.
    stepb_tk F_26bbe8 D_26bbe8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_26bbd8 D_26bbd8 (Z_to_bv 64 0xe18f0).
    stepn F_26bbdc D_26bbdc.
    stepjr F_26bbe0 D_26bbe0 (Z_to_bv 64 0xe18f0) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_dcfb8 D_dcfb8. sp_renorm.
    stepST F_dcfbc D_dcfbc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2b17d0) ltac:(sok_stack SOK).
    stepST F_dcfc0 D_dcfc0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c1730) ltac:(sok_stack SOK).
    stepn F_dcfc4 D_dcfc4.
    stepn F_dcfc8 D_dcfc8.
    stepn F_dcfcc D_dcfcc.
    (* [comment removed for export] *)
    stepLBU F_dcfd0 D_dcfd0 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_dcfd4 D_dcfd4.
    stepb_tk F_dcfd8 D_dcfd8 ltac:(cond_compute).
    stepn F_dcfe4 D_dcfe4.
    stepn F_dcfe8 D_dcfe8.
    stepn F_dcfec D_dcfec.
    (* [comment removed for export] *)
    stepST F_dcff0 D_dcff0 (Z_to_bv 64 0x31ef08) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_dcff4 D_dcff4.
    stepLD8 F_dcff8 D_dcff8 (Z_to_bv 64 0x2b16d0).
    stepb_ft F_dcffc D_dcffc ltac:(cond_compute).
    stepn F_dd000 D_dd000.
    stepn F_dd004 D_dd004.
    stepn F_dd008 D_dd008.
    stepLD8 F_dd00c D_dd00c (Z_to_bv 64 0x31e5c8).
    stepn F_dd010 D_dd010.
    stepjr F_dd014 D_dd014 (0x2b1948 : word) ltac:(gres; first [reflexivity | bveq]). vnorm.
    stepret F_26bae4 D_26bae4 (0xe1950 : word) ltac:(bveq).
    stepn F_dd018 D_dd018.
    (* [comment removed for export] *)
    stepn F_dd01c D_dd01c.
    stepLD8 F_dd020 D_dd020 (Z_to_bv 64 0).
    stepb_tk F_dd024 D_dd024 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_dd03c D_dd03c (Z_to_bv 64 0x2b17d0).
    stepLD8 F_dd040 D_dd040 (Z_to_bv 64 0x2c1730).
    stepn F_dd044 D_dd044. sp_renorm.
    stepret F_dd048 D_dd048 (0x2b17d0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26bbe4 D_26bbe4.
    stepb_ft F_26bbe8 D_26bbe8 ltac:(cond_compute).
    stepLD8 F_26bbec D_26bbec (Z_to_bv 64 0x2b1854).
    stepLD8 F_26bbf0 D_26bbf0 code.
    stepLD8 F_26bbf4 D_26bbf4 s1v.
    stepn F_26bbf8 D_26bbf8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_26bbfc D_26bbfc.
    stepret F_26bbb0 D_26bbb0 (0x2b1854 : word) ltac:(bveq).
    stepn F_26bc68 D_26bc68.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End H0Exit_run1.

(* [comment removed for export] *)
Module H0Exit_run2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StepTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.WalkTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibAtomic HUExitBase.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b1858)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b5044)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2b1858 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x31edb0 wp1 rp1 ->
  file_clean mem 0x31ebd0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b5034 : word) mem rom)
                 (mkst regs' (0x2b15f4 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr & Gfa1 & Gflag & Galk & Gahd & Gdso & F0l & F0wp & F0wb & F0rp & F0re)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.   (* [comment removed for export] *)
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_26f448 D_26f448. rewrite Hsp. sp_renorm.
    stepST F_26f44c D_26f44c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b1858) ltac:(sok_stack SOK).
    stepST F_26f450 D_26f450 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26f454 D_26f454.
    stepn F_270394 D_270394. sp_renorm.
    stepST F_270398 D_270398 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x2b5044) ltac:(sok_stack SOK).
    stepST F_27039c D_27039c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_2703a0 D_2703a0.
    stepn F_2703a4 D_2703a4.
    stepn F_2703a8 D_2703a8.
    (* [comment removed for export] *)
    stepn F_2703ac D_2703ac.
    stepn F_2772d8 D_2772d8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2772dc | reflexivity | exact D_2772dc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_2772e0 D_2772e0 ltac:(cond_compute).
    stepret F_2774d0 D_2774d0 (0x2b5f9c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2703b0 D_2703b0.
    stepLD8 F_2703b4 D_2703b4 (Z_to_bv 64 0x2b5044).
    stepLD8 F_2703b8 D_2703b8 code.
    stepn F_2703bc D_2703bc. sp_renorm.
    stepret F_2703c0 D_2703c0 (0x2b5044 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_26f458 D_26f458 (Z_to_bv 64 0).
    stepb_ft F_26f45c D_26f45c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26f460 D_26f460.
    stepLD8 F_26f464 D_26f464 (Z_to_bv 64 0x31ecc0).
    stepb_ft F_26f468 D_26f468 ltac:(cond_compute).
    stepLD F_26f46c D_26f46c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_26f470 D_26f470 ltac:(cond_compute).
    stepLD8 F_26f47c D_26f47c (Z_to_bv 64 0).
    stepLD8 F_26f480 D_26f480 (Z_to_bv 64 0).
    stepb_tk F_26f484 D_26f484 ltac:(apply c_eq_refl).
    stepLD8 F_26f49c D_26f49c (Z_to_bv 64 0).
    stepLD8 F_26f4a0 D_26f4a0 (Z_to_bv 64 0).
    stepb_tk F_26f4a4 D_26f4a4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_26f4bc D_26f4bc.
    stepLD8 F_26f4c0 D_26f4c0 (Z_to_bv 64 0x31edb0).
    stepb_ft F_26f4c4 D_26f4c4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_26f4c8 D_26f4c8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_26f4cc D_26f4cc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_26f4d8 D_26f4d8 wp1.
    stepLD8 F_26f4dc D_26f4dc wp1.
    stepb_tk F_26f4e0 D_26f4e0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_26f4f8 D_26f4f8 rp1.
    stepLD8 F_26f4fc D_26f4fc rp1.
    stepb_tk F_26f500 D_26f500 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_26f518 D_26f518.
    stepLD8 F_26f51c D_26f51c (Z_to_bv 64 0x31ebd0).
    stepb_ft F_26f520 D_26f520 ltac:(cond_compute).
    stepLD F_26f524 D_26f524 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_26f528 D_26f528 ltac:(cond_compute).
    stepLD8 F_26f534 D_26f534 wp2.
    stepLD8 F_26f538 D_26f538 wp2.
    stepb_tk F_26f53c D_26f53c ltac:(apply c_eq_refl).
    stepLD8 F_26f554 D_26f554 rp2.
    stepLD8 F_26f558 D_26f558 rp2.
    stepb_tk F_26f55c D_26f55c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_26f5dc D_26f5dc (Z_to_bv 64 0x2b1858).
    stepLD8 F_26f5e0 D_26f5e0 code.
    stepn F_26f5e4 D_26f5e4. sp_renorm.
    stepret F_26f5e8 D_26f5e8 (0x2b1858 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26bc6c D_26bc6c.
    stepn F_26bc70 D_26bc70.
    stepn F_26ba00 D_26ba00.
    stepn F_26ba04 D_26ba04.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End H0Exit_run2.

(* [comment removed for export] *)
Module H0Exit_run3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StepTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.WalkTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibAtomic HUExitBase H0Exit_run2.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x31edb0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x31edb0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x31edb0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x31edb0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b55ac)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2b1858 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b5034 : word) mem rom)
                 (mkst regs' (0x2b55ac : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x31edb0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x2b50e4
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x31edb0
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr & Gfa1 & Gflag & Galk & Gahd & Gdso & F0l & F0wp & F0wb & F0rp & F0re) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.   (* [comment removed for export] *)
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_26f448 D_26f448. rewrite Hsp. sp_renorm.
    stepST F_26f44c D_26f44c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b1858) ltac:(sok_stack SOK).
    stepST F_26f450 D_26f450 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26f454 D_26f454.
    stepn F_270394 D_270394. sp_renorm.
    stepST F_270398 D_270398 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x2b5044) ltac:(sok_stack SOK).
    stepST F_27039c D_27039c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_2703a0 D_2703a0.
    stepn F_2703a4 D_2703a4.
    stepn F_2703a8 D_2703a8.
    (* [comment removed for export] *)
    stepn F_2703ac D_2703ac.
    stepn F_2772d8 D_2772d8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2772dc | reflexivity | exact D_2772dc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_2772e0 D_2772e0 ltac:(cond_compute).
    stepret F_2774d0 D_2774d0 (0x2b5f9c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2703b0 D_2703b0.
    stepLD8 F_2703b4 D_2703b4 (Z_to_bv 64 0x2b5044).
    stepLD8 F_2703b8 D_2703b8 code.
    stepn F_2703bc D_2703bc. sp_renorm.
    stepret F_2703c0 D_2703c0 (0x2b5044 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_26f458 D_26f458 (Z_to_bv 64 0).
    stepb_ft F_26f45c D_26f45c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26f460 D_26f460.
    stepLD8 F_26f464 D_26f464 (Z_to_bv 64 0x31ecc0).
    stepb_ft F_26f468 D_26f468 ltac:(cond_compute).
    stepLD F_26f46c D_26f46c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_26f470 D_26f470 ltac:(cond_compute).
    stepLD8 F_26f47c D_26f47c (Z_to_bv 64 0).
    stepLD8 F_26f480 D_26f480 (Z_to_bv 64 0).
    stepb_tk F_26f484 D_26f484 ltac:(apply c_eq_refl).
    stepLD8 F_26f49c D_26f49c (Z_to_bv 64 0).
    stepLD8 F_26f4a0 D_26f4a0 (Z_to_bv 64 0).
    stepb_tk F_26f4a4 D_26f4a4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_26f4bc D_26f4bc.
    stepLD8 F_26f4c0 D_26f4c0 (Z_to_bv 64 0x31edb0).
    stepb_ft F_26f4c4 D_26f4c4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_26f4c8 D_26f4c8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_26f4cc D_26f4cc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_26f4d8 D_26f4d8 (Z_to_bv 64 wp).
    stepLD8 F_26f4dc D_26f4dc (Z_to_bv 64 wb).
    stepb_ft F_26f4e0 D_26f4e0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_26f4e4 D_26f4e4 (Z_to_bv 64 0x2b55ac).
    stepn F_26f4e8 D_26f4e8.
    stepn F_26f4ec D_26f4ec.
    stepn F_26f4f0 D_26f4f0.
    stepjr F_26f4f4 D_26f4f4 (Z_to_bv 64 0x2b55ac) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x31edb0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b1858)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x31edb0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x31edb0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x31ecb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x31ebd0)) ->
  file_clean mem 0x31ebd0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b50e4 : word) mem rom)
                 (mkst regs' (0x2b15f4 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_26f4f8 D_26f4f8 rp1.
    stepLD8 F_26f4fc D_26f4fc rp1.
    stepb_tk F_26f500 D_26f500 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_26f518 D_26f518.
    stepLD8 F_26f51c D_26f51c (Z_to_bv 64 0x31ebd0).
    stepb_ft F_26f520 D_26f520 ltac:(cond_compute).
    stepLD F_26f524 D_26f524 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_26f528 D_26f528 ltac:(cond_compute).
    stepLD8 F_26f534 D_26f534 wp2.
    stepLD8 F_26f538 D_26f538 wp2.
    stepb_tk F_26f53c D_26f53c ltac:(apply c_eq_refl).
    stepLD8 F_26f554 D_26f554 rp2.
    stepLD8 F_26f558 D_26f558 rp2.
    stepb_tk F_26f55c D_26f55c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_26f5dc D_26f5dc (Z_to_bv 64 0x2b1858).
    stepLD8 F_26f5e0 D_26f5e0 code.
    stepn F_26f5e4 D_26f5e4. rewrite Hsp. sp_renorm.
    stepret F_26f5e8 D_26f5e8 (0x2b1858 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26bc6c D_26bc6c.
    stepn F_26bc70 D_26bc70.
    stepn F_26ba00 D_26ba00.
    stepn F_26ba04 D_26ba04.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End H0Exit_run3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StepTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.WalkTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibAtomic OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExitSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes Spec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibWritev HUStdioDefs H0Exit_run1 H0Exit_run2 H0Exit_run3 HUStdioWrite.H0StdioWrite_run1 HUStdioWrite.H0StdioWrite_run2 HUStdioWrite.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x31edb0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x2b17ec : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr & Gfa1 & Gflag & Galk & Gahd & Gdso & F0l & F0wp & F0wb & F0rp & F0re).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_26ba08 | exact E_26ba08 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x2b17ec : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr & Gfa1 & Gflag & Galk & Gahd & Gdso & F0l & F0wp & F0wb & F0rp & F0re).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct (w3b1 regs2 (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x2b50e4) with (0x2b50e4 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x31edb0 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x2b50e4 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_26ba08 | exact E_26ba08 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x2b17ec : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b17ec) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x2b17ec) with (0x2b17ec : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

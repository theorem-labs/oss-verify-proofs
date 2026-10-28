(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_code_1cc20_1d000 U_code_1d000_1e000 U_code_3b000_3c000 U_code_3c000_3d000 U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_exit_run1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "mem_w1"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "fx_slot_writes"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.atexit_none"; "mem_fx"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.atexit_reg"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.atexit_st"; "Corelib.Init.Datatypes.length"; "mem_w2"].


(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) := ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "(0.(0.(0.O5.(1.&40.(2.(3.&40.O4.)+8.))(4.#8.O3.))(1.&40.(2.(3.&40.O4.)+10.))(4.#8.O2.))(1.&40.+7=328.)(4.#4.(1.&40.O1.)))")
(* [comment removed for export] *).

Lemma w1 : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pregs,(5.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Prom,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Ptp,(6.&40.)Pcode,(6.&40.)Ptid,$8.P,(9.(6.&40.)(:.R7.(;.&5.+2.$<.))R4.)P,(9.(6.&40.)(:.R8.(;.&5.+4.$<.))R4.)P,(9.(6.&40.)(:.R9.(;.&5.+:.$<.))R4.)P,(=.+100000000.(2.(3.&40.R7.)+90.))P,(=.(3.&40.R8.)+800000000000.)P,(9.$>.(?.$10.R;.(1.&40.(2.(3.&40.R9.)+90.))#90.)$11.)P,(=.+:8.(3.&40.R9.))P,(=.(3.&40.R:.)+100000000.)P,(12.(13.=R9.)(13.R9.+80000000.))P,(9.(7.(14.(6.&8.)))(15.$10.R?.(1.&40.(2.(3.&40.R<.)+:8.))#4.)(16.(14.(6.&8.))(4.#4.(1.&40.R:.))))P,(9.(7.(14.(6.&8.)))(15.$10.R10.(1.&40.+7=328.)#4.)(16.(14.(6.&8.))(4.#4.(1.&40.=))))(17.(5.&5.(6.&40.))Lregs',(5.&5.(6.&40.))(12.(18.$10.(19.$1:.R13.(;.&40.+3?74<.$<.)R12.R11.)(19.$1:.R1.(;.&40.+3?568.$<.)(1;.R12.R10.(:.R13.(;.&5.+1.$<.))(:.R13.(;.&5.+8.$<.))R=.)R11.))(12.(9.(6.&40.)(:.R1.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R10.)+10.)))(12.(9.(6.&40.)(:.R1.(;.&5.+8.$<.))R>.)(12.(9.(6.&40.)(:.R1.(;.&5.+1.$<.))(1.&40.+3?7;0.))(12.(9.(6.&40.)(:.R1.(;.&5.+4.$<.))R?.)(12.(9.(6.&40.)(:.R1.(;.&5.+3.$<.))(:.R13.(;.&5.+3.$<.)))(12.(9.(6.&40.)(:.R1.(;.&5.+9.$<.))(:.R13.(;.&5.+9.$<.)))(12.(9.(6.&40.)(:.R1.(;.&5.+12.$<.))(:.R13.(;.&5.+12.$<.)))(9.(6.&40.)(:.R1.(;.&5.+13.$<.))(:.R13.(;.&5.+13.$<.))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock.
  unfold mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_3c000 D_3c000. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_3c004 D_3c004 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_3c008 D_3c008 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_3c00c D_3c00c.
    stepn F_3c010 D_3c010. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_3c014 D_3c014 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_3c018 D_3c018.
    stepn F_3c01c D_3c01c.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_3c020 | reflexivity | exact D_3c020
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_3c024 | reflexivity | exact D_3c024 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_3c028 | reflexivity | exact D_3c028
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_3c02c D_3c02c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_3c030 D_3c030.
    (* [comment removed for export] *)
    stepb_ft F_3c034 D_3c034 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_3c038 D_3c038 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_3c05c D_3c05c. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_3c060 D_3c060.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_hit4 : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Psegs,(14.$1<.)Pm,P,(6.&40.)(7.(6.&8.))Pa,(6.&40.)Pv,(6.&40.)P,(=.(1=.(3.&40.R2.)+4.)(1>.+2.+40.))(9.(7.(14.(6.&8.)))(15.R5.(0.R4.R3.(4.#4.R2.))R3.#4.)(16.(14.(6.&8.))(4.#4.R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Definition fx_spills (mem : word -> option byte) (sp code s1 s2 s3 : word) := ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "(0.(0.(0.(0.(0.O6.(1.&40.(2.(3.&40.O5.)+18.))(4.#8.(1.&40.+3?7;0.)))(1.&40.(2.(3.&40.O5.)+20.))(4.#8.O4.))(1.&40.(2.(3.&40.O5.)+28.))(4.#8.O3.))(1.&40.(2.(3.&40.O5.)+30.))(4.#8.O2.))(1.&40.(2.(3.&40.O5.)+38.))(4.#8.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fx_slot_writes (b : bool) (m : word -> option byte) : word -> option byte :=
  if b then
    wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 0x7d110) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x7d110) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0x7d110) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0x7d118) (word_to_le_bytes 8 (Z_to_bv 64 0))
  else m.

(* [comment removed for export] *)
Definition mem_fx (b : bool) (mem : word -> option byte) (sp code s1 s2 s3 : word) :=
  wbytes (fx_slot_writes b (fx_spills mem sp code s1 s2 s3)) (Z_to_bv 64 0x7d108) [Z_to_bv 8 1].

(* [comment removed for export] *)
Lemma fx_slot_writes_grows : forall b m, mem_grows m (fx_slot_writes b m).
Proof.
  intros [|] m; unfold fx_slot_writes; [|apply mem_grows_refl].
  repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Lemma rdn_fx_slot_writes_out : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pb,$>.Pm,P,(6.&40.)(7.(6.&8.))Pza,$8.Pn,$1?.P,(12.(=.=R2.)(12.(=.(1=.R2.(20.R1.))(1>.+2.+40.))(21.(=.(1=.R2.(20.R1.))+7=110.)(12.(=.+7=120.R2.)(13.R2.(1>.+2.+40.))))))(9.(7.(14.(6.&8.)))(15.$10.(22.R5.R4.)(1.&40.R3.)R2.)(15.$10.R4.(1.&40.R3.)R2.))")
(* [comment removed for export] *).
Proof.
  (intros [|] m za n dd_H; ddestruct dd_H as (H0 & Hn & Hd)); unfold fx_slot_writes; [|reflexivity].
  rewrite !rdn_wbytes_out_Z by (zlen; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac fx_lock k :=
  stepn F_43834 D_43834;
  (chain_step; [reflexivity
    | eapply step_lb with (b := Z_to_bv 8 0);
      [exact F_43838 | reflexivity | exact D_43838 | gres; imm_norm; addr_norm; rdn_solve]
    | step_simpl]); vnorm;
  stepb_tk F_4383c D_4383c ltac:(cond_compute);
  stepret F_43a2c D_43a2c k ltac:(bveq).

(* [comment removed for export] *)
Ltac fx_unlock k :=
  stepLD F_43abc D_43abc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
    ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
  stepb_ft F_43ac0 D_43ac0 ltac:(cond_compute);
  stepret F_43ac4 D_43ac4 k ltac:(bveq).

(* [comment removed for export] *)
Ltac fx_prologue Hsp SOK code s1 s2 s3 :=
  (* [comment removed for export] *)
  stepn F_3be1c D_3be1c; rewrite Hsp; sp_renorm;
  lazymatch goal with |- context [regupd _ 2 (Z_to_bv 64 (bv_unsigned ?sp - 64))] =>
  stepST F_3be20 D_3be20 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x3f7b0) ltac:(sok_stack SOK);
  stepST F_3be24 D_3be24 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK);
  stepST F_3be28 D_3be28 (Z_to_bv 64 (bv_unsigned sp - 40)) s1 ltac:(sok_stack SOK);
  stepST F_3be2c D_3be2c (Z_to_bv 64 (bv_unsigned sp - 48)) s2 ltac:(sok_stack SOK);
  stepST F_3be30 D_3be30 (Z_to_bv 64 (bv_unsigned sp - 56)) s3 ltac:(sok_stack SOK);
  (* [comment removed for export] *)
  stepn F_3be34 D_3be34;
  stepn F_3be38 D_3be38;
  stepn F_3be3c D_3be3c;
  stepn F_3be40 D_3be40;
  stepn F_3be44 D_3be44;
  fx_lock (0x3f594 : word)
  end.

(* [comment removed for export] *)
Ltac fx_epilogue code s1 s2 s3 :=
  (* [comment removed for export] *)
  stepn F_3bebc D_3bebc;
  stepST F_3bec0 D_3bec0 (Z_to_bv 64 0x7d108) (Z_to_bv 64 1) ltac:(sok_data);
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1);
  (* [comment removed for export] *)
  stepn F_3bec4 D_3bec4;
  stepLD8 F_3bec8 D_3bec8 (Z_to_bv 64 0x3f7b0);
  stepLD8 F_3becc D_3becc code;
  stepLD8 F_3bed0 D_3bed0 s1;
  stepLD8 F_3bed4 D_3bed4 s2;
  stepLD8 F_3bed8 D_3bed8 s3;
  stepn F_3bedc D_3bedc; sp_renorm;
  stepn F_3bee0 D_3bee0;
  fx_unlock (0x3f7b0 : word);
  (* [comment removed for export] *)
  stepn F_3c064 D_3c064.

Lemma wfx_none : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pregs,(5.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Prom,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Pcode,(6.&40.)Ps1,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)P,(9.(6.&40.)(:.R8.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R5.)+10.)))P,(9.(6.&40.)(:.R9.(;.&5.+8.$<.))R5.)P,(9.(6.&40.)(:.R:.(;.&5.+1.$<.))(1.&40.+3?7;0.))P,(9.(6.&40.)(:.R;.(;.&5.+9.$<.))R6.)P,(9.(6.&40.)(:.R<.(;.&5.+12.$<.))R6.)P,(9.(6.&40.)(:.R=.(;.&5.+13.$<.))R6.)P,(=.+100000000.(2.(3.&40.R;.)+90.))P,(=.(3.&40.R<.)+800000000000.)P,(9.$>.(?.$10.R?.(1.&40.(2.(3.&40.R=.)+90.))#90.)$11.)P,(9.(7.(14.(6.&8.)))(15.$10.R10.(1.&40.+7=353.)#1.)(16.(14.(6.&8.))(23.(6.&8.)(1.&8.=)(24.(6.&8.)))))P,(25.R11.)(17.(5.&5.(6.&40.))Lregs',(5.&5.(6.&40.))(12.(18.$10.(19.$1:.R14.(;.&40.+3?568.$<.)R13.R12.)(19.$1:.R1.(;.&40.+3?700.$<.)(26.$27.R13.R11.R10.R?.R>.R=.)R12.))(12.(9.(6.&40.)(:.R1.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R11.)+10.)))(12.(9.(6.&40.)(:.R1.(;.&5.+8.$<.))R10.)(12.(9.(6.&40.)(:.R1.(;.&5.+1.$<.))(1.&40.+3?7;4.))(12.(9.(6.&40.)(:.R1.(;.&5.+9.$<.))R?.)(12.(9.(6.&40.)(:.R1.(;.&5.+4.$<.))(:.R14.(;.&5.+4.$<.)))(9.(6.&40.)(:.R1.(;.&5.+3.$<.))(:.R14.(;.&5.+3.$<.))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom sp code s1 s2 s3 Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl (Ahead & Alock).
  unfold mem_fx, fx_slot_writes, fx_spills. eexists. split.
  - fx_prologue Hsp SOK code s1 s2 s3.
    (* [comment removed for export] *)
    stepLD8 F_3be48 D_3be48 (Z_to_bv 64 0).
    stepb_tk F_3be4c D_3be4c ltac:(cond_compute).
    fx_epilogue code s1 s2 s3.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma wfx_reg : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pregs,(5.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Prom,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Pcode,(6.&40.)Ps1,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)P,(9.(6.&40.)(:.R8.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R5.)+10.)))P,(9.(6.&40.)(:.R9.(;.&5.+8.$<.))R5.)P,(9.(6.&40.)(:.R:.(;.&5.+1.$<.))(1.&40.+3?7;0.))P,(9.(6.&40.)(:.R;.(;.&5.+9.$<.))R6.)P,(9.(6.&40.)(:.R<.(;.&5.+12.$<.))R6.)P,(9.(6.&40.)(:.R=.(;.&5.+13.$<.))R6.)P,(=.+100000000.(2.(3.&40.R;.)+90.))P,(=.(3.&40.R<.)+800000000000.)P,(9.$>.(?.$10.R?.(1.&40.(2.(3.&40.R=.)+90.))#90.)$11.)P,(9.(7.(14.(6.&8.)))(15.$10.R10.(1.&40.+7=353.)#1.)(16.(14.(6.&8.))(23.(6.&8.)(1.&8.=)(24.(6.&8.)))))P,(28.R11.)(17.(5.&5.(6.&40.))Lregs',(5.&5.(6.&40.))(12.(18.$10.(19.$1:.R14.(;.&40.+3?568.$<.)R13.R12.)(19.$1:.R1.(;.&40.+3?700.$<.)(26.$11.R13.R11.R10.R?.R>.R=.)R12.))(12.(9.(6.&40.)(:.R1.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R11.)+10.)))(12.(9.(6.&40.)(:.R1.(;.&5.+8.$<.))R10.)(12.(9.(6.&40.)(:.R1.(;.&5.+1.$<.))(1.&40.+3?7;4.))(12.(9.(6.&40.)(:.R1.(;.&5.+9.$<.))R?.)(12.(9.(6.&40.)(:.R1.(;.&5.+4.$<.))(:.R14.(;.&5.+4.$<.)))(9.(6.&40.)(:.R1.(;.&5.+3.$<.))(:.R14.(;.&5.+3.$<.))))))))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem rom sp code s1 s2 s3 Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl dd_H; ddestruct dd_H as (Ahead & Alock & Aslot & Anext & Af0 & Aa0 & Acb)).
  unfold mem_fx, fx_slot_writes, fx_spills. eexists. split.
  - fx_prologue Hsp SOK code s1 s2 s3.
    (* [comment removed for export] *)
    stepLD8 F_3be48 D_3be48 (Z_to_bv 64 0x7d120).
    stepb_ft F_3be4c D_3be4c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_3be50 D_3be50 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_3be54 D_3be54.
    (* [comment removed for export] *)
    stepn F_3be6c D_3be6c.
    stepST F_3be70 D_3be70 (Z_to_bv 64 0x7d110) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_3be74 D_3be74 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_3be78 D_3be78 (Z_to_bv 64 0x7d120).
    stepn F_3be7c D_3be7c.
    stepn F_3be80 D_3be80.
    stepLD8 F_3be84 D_3be84 (Z_to_bv 64 0x3f6f8).
    stepLD8 F_3be88 D_3be88 (Z_to_bv 64 0x1d674).
    (* [comment removed for export] *)
    stepn F_3be8c D_3be8c.
    stepn F_3be90 D_3be90.
    fx_unlock (0x3f5e0 : word).
    (* [comment removed for export] *)
    stepn F_3be94 D_3be94.
    stepjr F_3be98 D_3be98 (Z_to_bv 64 0x3f6f8) ltac:(gres; reflexivity). vnorm.
    stepret F_3bfac D_3bfac (0x1d674 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1d194 D_1d194.
    stepLBU F_1d198 D_1d198 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_1d19c D_1d19c ltac:(cond_compute).
    stepret F_1d1a0 D_1d1a0 (0x3f5e8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_3be9c D_3be9c.
    stepn F_3bea0 D_3bea0.
    fx_lock (0x3f5f0 : word).
    (* [comment removed for export] *)
    stepLD F_3bea4 D_3bea4 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; repeat rdn_peel1; apply rdn_wbytes_hit4; u_norm; lia)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_3bea8 D_3bea8.
    stepST F_3beac D_3beac (Z_to_bv 64 0x7d110) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_3beb0 D_3beb0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_3beb4 D_3beb4 (Z_to_bv 64 0x7d120).
    stepn F_3beb8 D_3beb8.
    stepLD8 F_3be58 D_3be58 (Z_to_bv 64 0).
    (* [comment removed for export] *)
    stepn F_3be5c D_3be5c.
    stepST F_3be60 D_3be60 (Z_to_bv 64 0x7d110) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_3be64 D_3be64 (Z_to_bv 64 0x7d118) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_3be68 D_3be68 ltac:(cond_compute).
    fx_epilogue code s1 s2 s3.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wfx : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pb,$>.Pregs,(5.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Prom,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Pcode,(6.&40.)Ps1,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)P,(9.(6.&40.)(:.R8.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R5.)+10.)))P,(9.(6.&40.)(:.R9.(;.&5.+8.$<.))R5.)P,(9.(6.&40.)(:.R:.(;.&5.+1.$<.))(1.&40.+3?7;0.))P,(9.(6.&40.)(:.R;.(;.&5.+9.$<.))R6.)P,(9.(6.&40.)(:.R<.(;.&5.+12.$<.))R6.)P,(9.(6.&40.)(:.R=.(;.&5.+13.$<.))R6.)P,(=.+100000000.(2.(3.&40.R;.)+90.))P,(=.(3.&40.R<.)+800000000000.)P,(9.$>.(?.$10.R?.(1.&40.(2.(3.&40.R=.)+90.))#90.)$11.)P,(9.(7.(14.(6.&8.)))(15.$10.R10.(1.&40.+7=353.)#1.)(16.(14.(6.&8.))(23.(6.&8.)(1.&8.=)(24.(6.&8.)))))P,(29.R13.R11.)(17.(5.&5.(6.&40.))Lregs',(5.&5.(6.&40.))(12.(18.$10.(19.$1:.R14.(;.&40.+3?568.$<.)R13.R12.)(19.$1:.R1.(;.&40.+3?700.$<.)(26.R15.R13.R11.R10.R?.R>.R=.)R12.))(12.(9.(6.&40.)(:.R1.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R11.)+10.)))(12.(9.(6.&40.)(:.R1.(;.&5.+8.$<.))R10.)(12.(9.(6.&40.)(:.R1.(;.&5.+1.$<.))(1.&40.+3?7;4.))(12.(9.(6.&40.)(:.R1.(;.&5.+9.$<.))R?.)(12.(9.(6.&40.)(:.R1.(;.&5.+4.$<.))(:.R14.(;.&5.+4.$<.)))(9.(6.&40.)(:.R1.(;.&5.+3.$<.))(:.R14.(;.&5.+3.$<.))))))))))")
(* [comment removed for export] *).
Proof. intros [|]; [exact wfx_reg | exact wfx_none]. Qed.

(* [comment removed for export] *)
Lemma wbytes_out_Z : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pbs,(14.(6.&8.))Pm,P,(6.&40.)(7.(6.&8.))Pzb,$8.Px,$8.P,(12.(=.=R2.)(12.(=.(1=.R2.(20.(2:.(6.&8.)R4.)))(1>.+2.+40.))(12.(12.(=.=R1.)(13.R1.(1>.+2.+40.)))(21.(13.R1.R2.)(=.(1=.R2.(20.(2:.(6.&8.)R4.)))R1.)))))(9.(7.(6.&8.))(0.R4.(1.&40.R3.)R5.(1.&40.R2.))A1.R4.(1.&40.R2.))")
(* [comment removed for export] *).
Proof.
  (intros bs m zb x dd_H; ddestruct dd_H as (Hb & Hbn & Hx & Hd)). destruct bs as [|b0 bs']; [reflexivity|]. cbn [length] in Hbn, Hd.
  destruct Hd as [Hlt | Hge].
  - apply wbytes_below; cbn [length]; rewrite ?u_Z2bv by lia; lia.
  - apply wbytes_above; cbn [length]; rewrite ?u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma atexit_st_w1 : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pb,$>.Pmem,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Pra,(6.&40.)Ps0,(6.&40.)Ptid,$8.P,(=.+100000000.(2.(3.&40.R4.)+90.))P,(=.(3.&40.R5.)+800000000000.)P,(29.R8.R7.)(29.R9.(1;.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros b mem sp ra s0 tid SPlo SPhi AT. eapply atexit_st_agree; [exact AT|].
  intros x Hx. unfold atexit_fp in Hx. unfold mem_w1.
  rewrite !wbytes_out_Z by (zlen; lia). reflexivity.
Qed.


(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) := ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "(0.(0.(0.(0.(0.(0.O4.(1.&40.(2.(3.&40.O3.)+18.))(4.#8.(1.&40.+3?7;4.)))(1.&40.(2.(3.&40.O3.)+20.))(4.#8.O2.))(1.&40.(2.(3.&40.O3.)+28.))(4.#8.O1.))(1.&40.(2.(3.&40.O3.)+38.))(4.#8.(1.&40.+3?730.)))(1.&40.(2.(3.&40.O3.)+40.))(4.#8.(1.&40.+48358.)))(1.&40.+4<?68.)(23.(6.&8.)(1.&8.+1.)(24.(6.&8.))))")
(* [comment removed for export] *).

Lemma w2 : ltac2:(CDefT.buildp (gd_tbl_P_exit_run1 ()) "Pregs,(5.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Prom,P,(6.&40.)(7.(6.&8.))Psp,(6.&40.)Pcode,(6.&40.)Ps1v,(6.&40.)P,(9.(6.&40.)(:.R6.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R3.)+10.)))P,(9.(6.&40.)(:.R7.(;.&5.+8.$<.))R3.)P,(9.(6.&40.)(:.R8.(;.&5.+1.$<.))(1.&40.+3?7;4.))P,(9.(6.&40.)(:.R9.(;.&5.+9.$<.))R4.)P,(=.+100000000.(2.(3.&40.R7.)+90.))P,(=.(3.&40.R8.)+800000000000.)P,(9.$>.(?.$10.R;.(1.&40.(2.(3.&40.R9.)+90.))#90.)$11.)P,(9.(7.(14.(6.&8.)))(15.$10.R<.(1.&40.+4;<>0.)#8.)(16.(14.(6.&8.))(4.#8.(1.&40.+48360.))))P,(9.(7.(14.(6.&8.)))(15.$10.R=.(1.&40.+4;<>8.)#8.)(16.(14.(6.&8.))(4.#8.(1.&40.+48358.))))P,(9.(7.(14.(6.&8.)))(15.$10.R>.(1.&40.+48358.)#8.)(16.(14.(6.&8.))(4.#8.(1.&40.+1=1;<.))))P,(9.(7.(14.(6.&8.)))(15.$10.R?.(1.&40.+4<?68.)#1.)(16.(14.(6.&8.))(23.(6.&8.)(1.&8.=)(24.(6.&8.)))))P,(9.(7.(14.(6.&8.)))(15.$10.R10.(1.&40.+4;<80.)#8.)(16.(14.(6.&8.))(4.#8.(1.&40.+3?630.))))P,(9.(7.(14.(6.&8.)))(15.$10.R11.(1.&40.+4;<88.)#8.)(16.(14.(6.&8.))(4.#8.(1.&40.=))))P,(9.(7.(14.(6.&8.)))(15.$10.R12.(1.&40.+4<<?0.)#8.)(16.(14.(6.&8.))(4.#8.(1.&40.+4<<?0.))))(17.(5.&5.(6.&40.))Lregs',(5.&5.(6.&40.))(12.(18.$10.(19.$1:.R15.(;.&40.+3?700.$<.)R14.R13.)(19.$1:.R1.(;.&40.+41890.$<.)(2;.R14.R12.R11.R10.)R13.))(12.(9.(6.&40.)(:.R1.(;.&5.+2.$<.))(1.&40.(2.(3.&40.R12.)+10.)))(12.(9.(6.&40.)(:.R1.(;.&5.+8.$<.))R11.)(12.(9.(6.&40.)(:.R1.(;.&5.+1.$<.))(1.&40.+3?7;8.))(12.(9.(6.&40.)(:.R1.(;.&5.+9.$<.))R10.)(12.(9.(6.&40.)(:.R1.(;.&5.+4.$<.))(:.R15.(;.&5.+4.$<.)))(9.(6.&40.)(:.R1.(;.&5.+3.$<.))(:.R15.(;.&5.+3.$<.))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_3bfb4 D_3bfb4. rewrite Hsp. sp_renorm.
    stepST F_3bfb8 D_3bfb8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x3f7b4) ltac:(sok_stack SOK).
    stepST F_3bfbc D_3bfbc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_3bfc0 D_3bfc0 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_3bfc4 D_3bfc4.
    stepn F_3bfc8 D_3bfc8.
    stepLD8 F_3bfcc D_3bfcc (Z_to_bv 64 0x48360).
    stepLD8 F_3bfd0 D_3bfd0 (Z_to_bv 64 0x48358).
    (* [comment removed for export] *)
    stepb_ft F_3bfd4 D_3bfd4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_3bfd8 D_3bfd8 (Z_to_bv 64 0x1d1bc).
    stepn F_3bfdc D_3bfdc.
    stepjr F_3bfe0 D_3bfe0 (Z_to_bv 64 0x1d1bc) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_1ccdc D_1ccdc. sp_renorm.
    stepST F_1cce0 D_1cce0 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x3f730) ltac:(sok_stack SOK).
    stepST F_1cce4 D_1cce4 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x48358) ltac:(sok_stack SOK).
    stepn F_1cce8 D_1cce8.
    stepn F_1ccec D_1ccec.
    stepn F_1ccf0 D_1ccf0.
    (* [comment removed for export] *)
    stepLBU F_1ccf4 D_1ccf4 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_1ccf8 D_1ccf8.
    stepb_tk F_1ccfc D_1ccfc ltac:(cond_compute).
    stepn F_1cd08 D_1cd08.
    stepn F_1cd0c D_1cd0c.
    stepn F_1cd10 D_1cd10.
    (* [comment removed for export] *)
    stepST F_1cd14 D_1cd14 (Z_to_bv 64 0x4cf68) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_1cd18 D_1cd18.
    stepLD8 F_1cd1c D_1cd1c (Z_to_bv 64 0x3f630).
    stepb_ft F_1cd20 D_1cd20 ltac:(cond_compute).
    stepn F_1cd24 D_1cd24.
    stepn F_1cd28 D_1cd28.
    stepn F_1cd2c D_1cd2c.
    stepLD8 F_1cd30 D_1cd30 (Z_to_bv 64 0x4ccf0).
    stepn F_1cd34 D_1cd34.
    stepret F_3bee4 D_3bee4 (0x1d218 : word) ltac:(bveq).
    stepn F_1cd38 D_1cd38.
    (* [comment removed for export] *)
    stepn F_1cd3c D_1cd3c.
    stepLD8 F_1cd40 D_1cd40 (Z_to_bv 64 0).
    stepb_tk F_1cd44 D_1cd44 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1cd5c D_1cd5c (Z_to_bv 64 0x3f730).
    stepLD8 F_1cd60 D_1cd60 (Z_to_bv 64 0x48358).
    stepn F_1cd64 D_1cd64. sp_renorm.
    stepret F_1cd68 D_1cd68 (0x3f730 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_3bfe4 D_3bfe4.
    stepb_ft F_3bfe8 D_3bfe8 ltac:(cond_compute).
    stepLD8 F_3bfec D_3bfec (Z_to_bv 64 0x3f7b4).
    stepLD8 F_3bff0 D_3bff0 code.
    stepLD8 F_3bff4 D_3bff4 s1v.
    stepn F_3bff8 D_3bff8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_3bffc D_3bffc.
    stepret F_3bfb0 D_3bfb0 (0x3f7b4 : word) ltac:(bveq).
    stepn F_3c068 D_3c068.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_code_1cc20_1d000 U_code_3b000_3c000.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_startup1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BB.MemSplit.wfJ"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "regs_init"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.MemSplit.cmem"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.wrap_mem"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.phdrs"; "Corelib.Init.Datatypes.None"; "P1.J1"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"].

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Let argc : word := argcN av.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr sp0 av.
  Let pn : word := cat_argv_ptr sp0 av ev 0.

  #[using="Hva"] Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof. exact (u_argcN av Hva). Qed.

  #[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup1 ()) "(0.(0.(0.(0.(0.(0.(0.(0.O1.(1.&40.(2.(3.&40.Vsp0,)+8.))(4.#8.(1.&40.=)))(1.&40.(2.(3.&40.Vsp0,)+10.))(4.#8.(1.&40.=)))(1.&40.(2.(3.&40.Vsp0,)+18.))(4.#8.(1.&40.=)))(1.&40.(2.(3.&40.Vsp0,)+20.))(4.#8.(1.&40.=)))(1.&40.(2.(3.&40.Vsp0,)+28.))(4.#8.(1.&40.+3?238.)))(1.&40.(2.(3.&40.Vsp0,)+30.))(4.#8.(1.&40.(5.(3.&40.Vsp0,)+8.))))(1.&40.(2.(3.&40.Vsp0,)+38.))(4.#8.Vargc,))(1.&40.(2.(3.&40.Vsp0,)+40.))(4.#8.(1.&40.+1=24<.)))")
(* [comment removed for export] *).

  #[using="Hva Hve Hlo Hhi Hal"] Lemma p1_run : ltac2:(CDefT.buildp (gd_tbl_P_startup1 ()) "Prom,P,(6.&40.)(7.(6.&8.))PJ,P,(6.&40.)(7.(6.&8.))P,(8.Vsp0,R1.)(9.(:.&5.(6.&40.))Lregs',(:.&5.(6.&40.))(;.(<.$=.(>.$?.(10.Vsp0,)(11.&40.+1=100.$12.)(13.Vsp0,(14.$15.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R3.L,(6.&40.)(16.(6.&8.)))R4.)(>.$?.R1.(11.&40.+46>44.$12.)(13.Vsp0,(14.$15.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)(17.R3.)L,(6.&40.)(16.(6.&8.)))R4.))(;.(18.(6.&40.)(19.R1.(11.&5.+1.$12.))(1.&40.+3>?;8.))(;.(18.(6.&40.)(19.R1.(11.&5.+2.$12.))(1.&40.(2.(3.&40.Vsp0,)+1:0.)))(;.(18.(6.&40.)(19.R1.(11.&5.+3.$12.))(1.&40.+10800.))(;.(18.(6.&40.)(19.R1.(11.&5.+4.$12.))(1.&40.=))(;.(18.(6.&40.)(19.R1.(11.&5.+8.$12.))Vpn,)(;.(18.(6.&40.)(19.R1.(11.&5.+9.$12.))Venvp,)(;.(18.(6.&40.)(19.R1.(11.&5.+:.$12.))(1.&40.(2.(3.&40.Vsp0,)+170.)))(;.(18.(6.&40.)(19.R1.(11.&5.+;.$12.))(1.&40.=))(;.(18.(6.&40.)(19.R1.(11.&5.+<.$12.))(1.&40.+130.))(;.(18.(6.&40.)(19.R1.(11.&5.+12.$12.))(1.&40.+1=24<.))Pr,(6.&5.)P,(1:.(6.&5.)R1.(1;.(6.&5.)(11.&5.+5.$12.)(1;.(6.&5.)(11.&5.+13.$12.)(1;.(6.&5.)(11.&5.+14.$12.)(1;.(6.&5.)(11.&5.+15.$12.)(1;.(6.&5.)(11.&5.+16.$12.)(1;.(6.&5.)(11.&5.+17.$12.)(1;.(6.&5.)(11.&5.+18.$12.)(1;.(6.&5.)(11.&5.+19.$12.)(1;.(6.&5.)(11.&5.+1:.$12.)(1;.(6.&5.)(11.&5.+1;.$12.)(1<.(6.&5.)))))))))))))(18.(6.&40.)(19.R3.R2.)(1.&40.=))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_1cc20 D_1cc20.    (* [comment removed for export] *)
      stepn F_1cc24 D_1cc24.    (* [comment removed for export] *)
      stepn F_1cc28 D_1cc28.    (* [comment removed for export] *)
      stepn F_1cc2c D_1cc2c.    (* [comment removed for export] *)
      stepn F_1cc30 D_1cc30.    (* [comment removed for export] *)
      stepiv F_1cc34 D_1cc34 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_1cc38 D_1cc38.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_1cc3c | reflexivity | exact D_1cc3c
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_1cc40 D_1cc40.    (* [comment removed for export] *)
      stepn F_1cc44 D_1cc44.    (* [comment removed for export] *)
      stepn F_1cc48 D_1cc48.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x1d24c);
        [exact F_1cc4c | reflexivity | exact D_1cc4c | rd_img img_48518_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x3ef88);
        [exact F_1cc50 | reflexivity | exact D_1cc50 | rd_img img_48520_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x3f6fc);
        [exact F_1cc54 | reflexivity | exact D_1cc54 | rd_img img_48528_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_1cc58 D_1cc58 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_1cc5c D_1cc5c.    (* [comment removed for export] *)
      stepn F_1cc60 D_1cc60.    (* [comment removed for export] *)
      stepn F_1cc64 D_1cc64.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_3baac D_3baac (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_3bab0 D_3bab0 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_3bab4 D_3bab4 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_3bab8 D_3bab8 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_3babc D_3babc (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_3bac0 D_3bac0.    (* [comment removed for export] *)
      stepn F_3bac4 D_3bac4.    (* [comment removed for export] *)
      stepn F_3bac8 D_3bac8.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_3bacc | reflexivity | exact D_3bacc
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_3bad0 D_3bad0 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_3bad4 D_3bad4 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_3bad8 D_3bad8 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_3badc D_3badc.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_3b834 D_3b834 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_3b838 D_3b838 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x3f238) ltac:(ok_win HJ).
      stw F_3b83c D_3b83c (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_3b840 D_3b840 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_3b844 D_3b844 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x1d24c) ltac:(ok_win HJ).
      stepn F_3b848 D_3b848.    (* [comment removed for export] *)
      stepn F_3b84c D_3b84c.    (* [comment removed for export] *)
      sv F_3b850 D_3b850 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_3b854 D_3b854.    (* [comment removed for export] *)
      stepn F_3b858 D_3b858.    (* [comment removed for export] *)
      stepn F_3b85c D_3b85c.    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section is over the launch input, with its valid_launch and entry_launch_ok_va premises, and the argv pointer sits at the stack top; J1 and p1_run written out in plain text; per-lemma #[using] attributes replaced by a default; comment placeholders removed). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_code_1cc20_1d000 U_code_3b000_3c000.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Local Set Default Proof Using "All".
Abbreviation SEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.
Section P1.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation mem0 := (wrap_mem inp mbase RPH entry sp0 rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw)) (only parsing).
  Let argc : word := argcN inp.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr inp sp0.
  Let pn : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof. exact (u_argcN inp Hva). Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x3f238)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1d24c)).
  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x1d100 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x46e44 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x3efb8
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x1d24c
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_1cc20 D_1cc20.
      stepn F_1cc24 D_1cc24.
      stepn F_1cc28 D_1cc28.
      stepn F_1cc2c D_1cc2c.
      stepn F_1cc30 D_1cc30.
      stepiv F_1cc34 D_1cc34 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
      stepn F_1cc38 D_1cc38.
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_1cc3c | reflexivity | exact D_1cc3c
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          eapply read_argc_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi]
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_1cc40 D_1cc40.
      stepn F_1cc44 D_1cc44.
      stepn F_1cc48 D_1cc48.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x1d24c);
        [exact F_1cc4c | reflexivity | exact D_1cc4c | rd_img img_48518_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x3ef88);
        [exact F_1cc50 | reflexivity | exact D_1cc50 | rd_img img_48520_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x3f6fc);
        [exact F_1cc54 | reflexivity | exact D_1cc54 | rd_img img_48528_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_1cc58 D_1cc58 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      stepn F_1cc5c D_1cc5c.
      stepn F_1cc60 D_1cc60.
      stepn F_1cc64 D_1cc64.
      sv F_3baac D_3baac (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stw F_3bab0 D_3bab0 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_3bab4 D_3bab4 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_3bab8 D_3bab8 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_3babc D_3babc (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_3bac0 D_3bac0.
      stepn F_3bac4 D_3bac4.
      stepn F_3bac8 D_3bac8.
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_3bacc | reflexivity | exact D_3bacc
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          eapply read_argv_ptr_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi | lia]
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_3bad0 D_3bad0 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
      stepiv F_3bad4 D_3bad4 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
      stepiv F_3bad8 D_3bad8 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
      stepn F_3badc D_3badc.
      sv F_3b834 D_3b834 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stw F_3b838 D_3b838 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x3f238) ltac:(ok_win HJ).
      stw F_3b83c D_3b83c (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_3b840 D_3b840 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_3b844 D_3b844 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x1d24c) ltac:(ok_win HJ).
      stepn F_3b848 D_3b848.
      stepn F_3b84c D_3b84c.
      sv F_3b850 D_3b850 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      stepn F_3b854 D_3b854.
      stepn F_3b858 D_3b858.
      stepn F_3b85c D_3b85c.
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

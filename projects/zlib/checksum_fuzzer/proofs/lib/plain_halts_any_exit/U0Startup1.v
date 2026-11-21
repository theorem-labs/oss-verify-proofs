(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  StartupTac ArgvEnv RefLayout U0Img
 U0_code_13bc4_14000 U0_code_15000_16000 U0_code_1d000_1d8c4             .
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_chain_step.

Abbreviation SEGS := Tgt_checksum_fuzzer_ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Tgt_checksum_fuzzer_ubsan.M.phdrs.

Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  (* port727 (): the launch as Common/ArgvEnv's Scaffold has it: one ProcInput, the mmap base,
     the stack pointer and break, the draw, with valid_launch and entry_launch_ok_va. *)
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation ENT := (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) (only parsing).
  Local Notation mem0 := (wrap_mem inp mbase RPH ENT sp0 rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH ENT sp0 rdraw)) (only parsing).

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
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x15820)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d70)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst (regs_init sp0) (0x13c24 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x1d38c : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x155a0
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x13d70
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_13bc4 D_13bc4.
      stepn F_13bc8 D_13bc8.
      stepn F_13bcc D_13bcc.
      stepn F_13bd0 D_13bd0.
      stepn F_13bd4 D_13bd4.
      stepiv F_13bd8 D_13bd8 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
      stepn F_13bdc D_13bdc.
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_13be0 | reflexivity | exact D_13be0
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes (run_segments SEGS rc_inp rc_sp rc_mb) mem0 sp0 argc 4); [lia|];
          eapply read_argc_w; eassumption
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_13be4 D_13be4.
      stepn F_13be8 D_13be8.
      stepn F_13bec D_13bec.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x13d70);
        [exact F_13bf0 | reflexivity | exact D_13bf0 | rd_img img_1e8f8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x15570);
        [exact F_13bf4 | reflexivity | exact D_13bf4 | rd_img img_1e900_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x15db8);
        [exact F_13bf8 | reflexivity | exact D_13bf8 | rd_img img_1e908_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_13bfc D_13bfc (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      stepn F_13c00 D_13c00.
      stepn F_13c04 D_13c04.
      stepn F_13c08 D_13c08.
      sv F_15740 D_15740 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stw F_15744 D_15744 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15748 D_15748 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_1574c D_1574c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15750 D_15750 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_15754 D_15754.
      stepn F_15758 D_15758.
      stepn F_1575c D_1575c.
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_15760 | reflexivity | exact D_15760
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          eapply read_argv_ptr_w; [eassumption .. | lia]
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_15764 D_15764 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
      stepiv F_15768 D_15768 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
      stepiv F_1576c D_1576c envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
      stepn F_15770 D_15770.
      sv F_154c8 D_154c8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stw F_154cc D_154cc (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x15820) ltac:(ok_win HJ).
      stw F_154d0 D_154d0 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_154d4 D_154d4 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_154d8 D_154d8 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x13d70) ltac:(ok_win HJ).
      stepn F_154dc D_154dc.
      stepn F_154e0 D_154e0.
      sv F_154e4 D_154e4 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      stepn F_154e8 D_154e8.
      stepn F_154ec D_154ec.
      stepn F_154f0 D_154f0.
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_chain_step_kit.

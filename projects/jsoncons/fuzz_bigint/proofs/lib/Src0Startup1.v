(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the start-up section reads the launch input, mmap base and launch facts (valid_launch, entry_launch_ok_va), as the launch's stack image needs. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  StartupTac ArgvEnv RefLayout Src0Img
 Src0_code_1ffac_20088 Src0_code_20088_210bc Src0_code_4abb8_4b0b4 Src0_code_4b104_4b654 Src0_code_58828_59540      .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Set Default Proof Using "All".

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

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
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x4ae68)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x200f8)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x1ffac : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x58ea4 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x4abe8
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x200f8
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_1ffac D_1ffac.
      stepn F_1ffb0 D_1ffb0.
      stepn F_1ffb4 D_1ffb4.
      stepn F_1ffb8 D_1ffb8.
      stepn F_1ffbc D_1ffbc.
      stepiv F_1ffc0 D_1ffc0 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
      stepn F_1ffc4 D_1ffc4.
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_1ffc8 | reflexivity | exact D_1ffc8
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          eapply read_argc_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi]
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_1ffcc D_1ffcc.
      stepn F_1ffd0 D_1ffd0.
      stepn F_1ffd4 D_1ffd4.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x200f8);
        [exact F_1ffd8 | reflexivity | exact D_1ffd8 | rd_img img_5e4a8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x4abb8);
        [exact F_1ffdc | reflexivity | exact D_1ffdc | rd_img img_5e4b0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x4b40c);
        [exact F_1ffe0 | reflexivity | exact D_1ffe0 | rd_img img_5e4b8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_1ffe4 D_1ffe4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      stepn F_1ffe8 D_1ffe8.
      stepn F_1ffec D_1ffec.
      stepn F_1fff0 D_1fff0.
      sv F_4ae34 D_4ae34 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stw F_4ae38 D_4ae38 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_4ae3c D_4ae3c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_4ae40 D_4ae40 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_4ae44 D_4ae44 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_4ae48 D_4ae48.
      stepn F_4ae4c D_4ae4c.
      stepn F_4ae50 D_4ae50.
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_4ae54 | reflexivity | exact D_4ae54
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          eapply read_argv_ptr_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi | lia]
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_4ae58 D_4ae58 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
      stepiv F_4ae5c D_4ae5c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
      stepiv F_4ae60 D_4ae60 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
      stepn F_4ae64 D_4ae64.
      sv F_4abbc D_4abbc (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stw F_4abc0 D_4abc0 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x4ae68) ltac:(ok_win HJ).
      stw F_4abc4 D_4abc4 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_4abc8 D_4abc8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_4abcc D_4abcc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x200f8) ltac:(ok_win HJ).
      stepn F_4abd0 D_4abd0.
      stepn F_4abd4 D_4abd4.
      sv F_4abd8 D_4abd8 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      stepn F_4abdc D_4abdc.
      stepn F_4abe0 D_4abe0.
      stepn F_4abe4 D_4abe4.
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

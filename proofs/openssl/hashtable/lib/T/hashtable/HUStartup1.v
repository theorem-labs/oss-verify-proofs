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
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  StartupTac ArgvEnv RefLayout HUImg HU_code_26b000_26c000 HU_code_276000_277000 HU_code_dc000_dd000 HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
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

  Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof. exact (u_argcN av Hva). Qed.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b10e8)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1984)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0xe1830 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x2bc5a4 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2b0e68
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0xe1984
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_dcef8 D_dcef8.    (* [comment removed for export] *)
      stepn F_dcefc D_dcefc.    (* [comment removed for export] *)
      stepn F_dcf00 D_dcf00.    (* [comment removed for export] *)
      stepn F_dcf04 D_dcf04.    (* [comment removed for export] *)
      stepn F_dcf08 D_dcf08.    (* [comment removed for export] *)
      stepiv F_dcf0c D_dcf0c sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_dcf10 D_dcf10.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_dcf14 | reflexivity | exact D_dcf14
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_dcf18 D_dcf18.    (* [comment removed for export] *)
      stepn F_dcf1c D_dcf1c.    (* [comment removed for export] *)
      stepn F_dcf20 D_dcf20.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0xe1984);
        [exact F_dcf24 | reflexivity | exact D_dcf24 | rd_img img_2d7588_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x2b0e38);
        [exact F_dcf28 | reflexivity | exact D_dcf28 | rd_img img_2d7590_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x2b179c);
        [exact F_dcf2c | reflexivity | exact D_dcf2c | rd_img img_2d7598_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_dcf30 D_dcf30 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_dcf34 D_dcf34.    (* [comment removed for export] *)
      stepn F_dcf38 D_dcf38.    (* [comment removed for export] *)
      stepn F_dcf3c D_dcf3c.    (* [comment removed for export] *)
      stepjr F_dcf40 D_dcf40 (0x2b1874 : word) ltac:(gres; pin; first [reflexivity | bveq]); vnorm.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_26b4bc D_26b4bc (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_26b4c0 D_26b4c0 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_26b4c4 D_26b4c4 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_26b4c8 D_26b4c8 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_26b4cc D_26b4cc (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_26b4d0 D_26b4d0.    (* [comment removed for export] *)
      stepn F_26b4d4 D_26b4d4.    (* [comment removed for export] *)
      stepn F_26b4d8 D_26b4d8.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_26b4dc | reflexivity | exact D_26b4dc
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_26b4e0 D_26b4e0 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_26b4e4 D_26b4e4 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_26b4e8 D_26b4e8 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_26b4ec D_26b4ec.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_26b244 D_26b244 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_26b248 D_26b248 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x2b10e8) ltac:(ok_win HJ).
      stw F_26b24c D_26b24c (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_26b250 D_26b250 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_26b254 D_26b254 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0xe1984) ltac:(ok_win HJ).
      stepn F_26b258 D_26b258.    (* [comment removed for export] *)
      stepn F_26b25c D_26b25c.    (* [comment removed for export] *)
      sv F_26b260 D_26b260 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_26b264 D_26b264.    (* [comment removed for export] *)
      stepn F_26b268 D_26b268.    (* [comment removed for export] *)
      stepn F_26b26c D_26b26c.    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

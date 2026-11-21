(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ArgvEnv OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefLayout OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8Img OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_146ec_15000 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_18000_19000 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_20000_20a98.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
(* [comment removed for export] *)

Abbreviation SEGS := SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs.

(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  (* a worker port727 (): the launch as Common/ArgvEnv's Scaffold has it: one ProcInput, the mmap base,
     the stack pointer and break, the draw, with valid_launch and entry_launch_ok_va (a worker's VLAUNCH + LOK). *)
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation ENT := (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc)) (only parsing).
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

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x18c64)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x148d4)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst (regs_init sp0) (0x14788 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x20638 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x189e4
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x148d4
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_146ec D_146ec.    (* [comment removed for export] *)
      stepn F_146f0 D_146f0.    (* [comment removed for export] *)
      stepn F_146f4 D_146f4.    (* [comment removed for export] *)
      stepn F_146f8 D_146f8.    (* [comment removed for export] *)
      stepn F_146fc D_146fc.    (* [comment removed for export] *)
      stepiv F_14700 D_14700 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_14704 D_14704.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_14708 | reflexivity | exact D_14708
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes (run_segments SEGS rc_inp rc_sp rc_mb) mem0 sp0 argc 4); [lia|];
          eapply read_argc_w; eassumption
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_1470c D_1470c.    (* [comment removed for export] *)
      stepn F_14710 D_14710.    (* [comment removed for export] *)
      stepn F_14714 D_14714.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x148d4);
        [exact F_14718 | reflexivity | exact D_14718 | rd_img img_21ac8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x189b4);
        [exact F_1471c | reflexivity | exact D_1471c | rd_img img_21ad0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x1911c);
        [exact F_14720 | reflexivity | exact D_14720 | rd_img img_21ad8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_14724 D_14724 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_14728 D_14728.    (* [comment removed for export] *)
      stepn F_1472c D_1472c.    (* [comment removed for export] *)
      stepn F_14730 D_14730.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_18aac D_18aac (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_18ab0 D_18ab0 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab4 D_18ab4 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab8 D_18ab8 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18abc D_18abc (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_18ac0 D_18ac0.    (* [comment removed for export] *)
      stepn F_18ac4 D_18ac4.    (* [comment removed for export] *)
      stepn F_18ac8 D_18ac8.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_18acc | reflexivity | exact D_18acc
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          eapply read_argv_ptr_w; [eassumption .. | lia]
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_18ad0 D_18ad0 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_18ad4 D_18ad4 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_18ad8 D_18ad8 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_18adc D_18adc.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_18834 D_18834 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_18838 D_18838 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x18c64) ltac:(ok_win HJ).
      stw F_1883c D_1883c (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_18840 D_18840 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_18844 D_18844 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x148d4) ltac:(ok_win HJ).
      stepn F_18848 D_18848.    (* [comment removed for export] *)
      stepn F_1884c D_1884c.    (* [comment removed for export] *)
      sv F_18850 D_18850 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_18854 D_18854.    (* [comment removed for export] *)
      stepn F_18858 D_18858.    (* [comment removed for export] *)
      stepn F_1885c D_1885c.    (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.

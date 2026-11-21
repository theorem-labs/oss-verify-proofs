(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: section P1 takes the whole ProcInput, the mmap base, brk and the entry draw with the valid_launch and entry_launch_ok_va premises; its memory adds the Plain image's entry for the auxv; argc/argv reads use the launch facts, the program name the draw's stack top and AT_EXECFN; Proof using lines added. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PStartupImg PStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
(** The image's entry, as [Run.init_machine_state] hands it to the auxv. *)
Abbreviation RENT := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)).

(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).

  Local Notation mem0 := (wrap_mem inp mbase RPH RENT sp0 rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH RENT sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.
  (* the launch facts a layout lemma of ArgvEnv/RefLayout asks for *)
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal ].

  Let argc : word := argcN inp.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr inp sp0.
  Let pn : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.

  Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof using Hva. exact (u_argcN inp Hva). Qed.

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
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x14aac)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1214c)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x12000 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x20dec : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1482c
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x1214c
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_12000 D_12000.    (* [comment removed for export] *)
      stepn F_12004 D_12004.    (* [comment removed for export] *)
      stepn F_12008 D_12008.    (* [comment removed for export] *)
      stepn F_1200c D_1200c.    (* [comment removed for export] *)
      stepn F_12010 D_12010.    (* [comment removed for export] *)
      stepiv F_12014 D_12014 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_12018 D_12018.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_1201c | reflexivity | exact D_1201c
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          eapply read_argc_w; lctx
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_12020 D_12020.    (* [comment removed for export] *)
      stepn F_12024 D_12024.    (* [comment removed for export] *)
      stepn F_12028 D_12028.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x1214c);
        [exact F_1202c | reflexivity | exact D_1202c | rd_img img_22478_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x147fc);
        [exact F_12030 | reflexivity | exact D_12030 | rd_img img_22480_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x14f64);
        [exact F_12034 | reflexivity | exact D_12034 | rd_img img_22488_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_12038 D_12038 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_1203c D_1203c.    (* [comment removed for export] *)
      stepn F_12040 D_12040.    (* [comment removed for export] *)
      stepn F_12044 D_12044.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_14a78 D_14a78 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_14a7c D_14a7c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_14a80 D_14a80 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_14a84 D_14a84 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_14a88 D_14a88 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_14a8c D_14a8c.    (* [comment removed for export] *)
      stepn F_14a90 D_14a90.    (* [comment removed for export] *)
      stepn F_14a94 D_14a94.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_14a98 | reflexivity | exact D_14a98
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          eapply read_argv_ptr_w; first [lctx | lia]
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_14a9c D_14a9c (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_14aa0 D_14aa0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_14aa4 D_14aa4 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_14aa8 D_14aa8.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_14800 D_14800 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_14804 D_14804 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x14aac) ltac:(ok_win HJ).
      stw F_14808 D_14808 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_1480c D_1480c (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_14810 D_14810 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x1214c) ltac:(ok_win HJ).
      stepn F_14814 D_14814.    (* [comment removed for export] *)
      stepn F_14818 D_14818.    (* [comment removed for export] *)
      sv F_1481c D_1481c (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_14820 D_14820.    (* [comment removed for export] *)
      stepn F_14824 D_14824.    (* [comment removed for export] *)
      stepn F_14828 D_14828.    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg
 Ref_code_47284_47870 Ref_code_d9dac_da94c Ref_code_eacac_eb420           .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Set Default Proof Using "All".

(* LPS 75d69e00: stated explicitly over the ProcInput (argcN / envp_ptr / wrap_mem take inp).
   p1_run's proof is boost-beast's RefStartup1 translated per instruction: _start and the
   __libc_start_main prologue align at +0x1c768 / +0x72f54 / +0x75b84 (30 of 42 used words
   identical; the 12 others are auipc/ld/jal immediates).  The three literal-pool reads
   (img_f8620_8 / img_f8628_8 / img_f8630_8) hold 0x473d0 / 0xd9dac / 0xda76c; the third is
   NOT the donor's value mapped by region (0xda77c), which the local check at 75d69e00 refuted
   ("Unable to unify 894844 with 894828"). *)

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.
End FPX1.

Section P1.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable entry : word.
  Variable sp0 brk : word.
  Variable rnd : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem inp mbase RPH entry sp0 rnd) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd)) (only parsing).

  Let argc : word := argcN inp.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr inp sp0.
  Let pn : word := cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) 0.

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
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xda05c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x473d0)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x47284 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0xeb328 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xd9ddc
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x473d0
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_47284 D_47284.    (* [comment removed for export] *)
      stepn F_47288 D_47288.    (* [comment removed for export] *)
      stepn F_4728c D_4728c.    (* [comment removed for export] *)
      stepn F_47290 D_47290.    (* [comment removed for export] *)
      stepn F_47294 D_47294.    (* [comment removed for export] *)
      stepiv F_47298 D_47298 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_4729c D_4729c.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_472a0 | reflexivity | exact D_472a0
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          eapply read_argc_w; eassumption
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_472a4 D_472a4.    (* [comment removed for export] *)
      stepn F_472a8 D_472a8.    (* [comment removed for export] *)
      stepn F_472ac D_472ac.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x473d0);
        [exact F_472b0 | reflexivity | exact D_472b0 | rd_img img_f8620_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0xd9dac);
        [exact F_472b4 | reflexivity | exact D_472b4 | rd_img img_f8628_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0xda76c);
        [exact F_472b8 | reflexivity | exact D_472b8 | rd_img img_f8630_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_472bc D_472bc (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_472c0 D_472c0.    (* [comment removed for export] *)
      stepn F_472c4 D_472c4.    (* [comment removed for export] *)
      stepn F_472c8 D_472c8.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_da028 D_da028 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_da02c D_da02c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_da030 D_da030 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_da034 D_da034 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_da038 D_da038 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_da03c D_da03c.    (* [comment removed for export] *)
      stepn F_da040 D_da040.    (* [comment removed for export] *)
      stepn F_da044 D_da044.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_da048 | reflexivity | exact D_da048
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          eapply read_argv_ptr_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi | lia]
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_da04c D_da04c (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_da050 D_da050 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_da054 D_da054 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_da058 D_da058.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_d9db0 D_d9db0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_d9db4 D_d9db4 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0xda05c) ltac:(ok_win HJ).
      stw F_d9db8 D_d9db8 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_d9dbc D_d9dbc (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_d9dc0 D_d9dc0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x473d0) ltac:(ok_win HJ).
      stepn F_d9dc4 D_d9dc4.    (* [comment removed for export] *)
      stepn F_d9dc8 D_d9dc8.    (* [comment removed for export] *)
      sv F_d9dcc D_d9dcc (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_d9dd0 D_d9dd0.    (* [comment removed for export] *)
      stepn F_d9dd4 D_d9dd4.    (* [comment removed for export] *)
      stepn F_d9dd8 D_d9dd8.    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Nodes FileSim StartupNodes StartupTac ArgvEnv RefLayout StartupRnd U.S0Img U.S0StartupDefs.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require StartupTac ArgvEnv RefLayout U.S0Img U.S0_code_1337c_1378c U.S0_code_1ed68_1f620 U.S0_code_26728_26f04.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSt.
Module S0Startup1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Img OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_1337c_1378c OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_1ed68_1f620 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_26728_26f04.
(* [comment removed for export] *)

Import WalkHideSt.OptIn.
Import ListNotations.
Local Open Scope bv_scope.

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
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rnd) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

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
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x28bd8)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x13580)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x13434 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x30ab0 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28958
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x13580
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_1337c D_1337c.    (* [comment removed for export] *)
      stepn F_13380 D_13380.    (* [comment removed for export] *)
      stepn F_13384 D_13384.    (* [comment removed for export] *)
      stepn F_13388 D_13388.    (* [comment removed for export] *)
      stepn F_1338c D_1338c.    (* [comment removed for export] *)
      stepiv F_13390 D_13390 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_13394 D_13394.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_13398 | reflexivity | exact D_13398
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rnd Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_1339c D_1339c.    (* [comment removed for export] *)
      stepn F_133a0 D_133a0.    (* [comment removed for export] *)
      stepn F_133a4 D_133a4.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x13580);
        [exact F_133a8 | reflexivity | exact D_133a8 | rd_img img_27f30_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x28928);
        [exact F_133ac | reflexivity | exact D_133ac | rd_img img_27f38_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x29170);
        [exact F_133b0 | reflexivity | exact D_133b0 | rd_img img_27f40_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_133b4 D_133b4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_133b8 D_133b8.    (* [comment removed for export] *)
      stepn F_133bc D_133bc.    (* [comment removed for export] *)
      stepn F_133c0 D_133c0.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_1efe4 D_1efe4 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_1efe8 D_1efe8 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_1efec D_1efec (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_1eff0 D_1eff0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_1eff4 D_1eff4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_1eff8 D_1eff8.    (* [comment removed for export] *)
      stepn F_1effc D_1effc.    (* [comment removed for export] *)
      stepn F_1f000 D_1f000.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_1f004 | reflexivity | exact D_1f004
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rnd Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_1f008 D_1f008 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_1f00c D_1f00c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_1f010 D_1f010 envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_1f014 D_1f014.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_1ed6c D_1ed6c (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_1ed70 D_1ed70 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x28bd8) ltac:(ok_win HJ).
      stw F_1ed74 D_1ed74 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_1ed78 D_1ed78 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_1ed7c D_1ed7c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x13580) ltac:(ok_win HJ).
      stepn F_1ed80 D_1ed80.    (* [comment removed for export] *)
      stepn F_1ed84 D_1ed84.    (* [comment removed for export] *)
      sv F_1ed88 D_1ed88 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_1ed8c D_1ed8c.    (* [comment removed for export] *)
      stepn F_1ed90 D_1ed90.    (* [comment removed for export] *)
      stepn F_1ed94 D_1ed94.    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Startup1.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Module S0Memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_26728_26f04.
(* [comment removed for export] *)

Import WalkHideSt.OptIn.
Import ListNotations.

Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Local Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x30ab0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_26938 D_26938 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2693c D_2693c (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_26940 D_26940 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_26944 D_26944.  (* [comment removed for export] *)
    stw F_26948 D_26948 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2694c D_2694c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26950 D_26950 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26954 D_26954 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26958 D_26958.  (* [comment removed for export] *)
    stw F_2695c D_2695c (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26960 D_26960 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_26964 D_26964 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26968 D_26968 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2696c D_2696c.  (* [comment removed for export] *)
    stw F_26970 D_26970 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_26974 D_26974 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_26978 D_26978.  (* [comment removed for export] *)
    sn F_2697c D_2697c.  (* [comment removed for export] *)
    sn F_26980 D_26980.  (* [comment removed for export] *)
    stepiv F_26984 D_26984 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_26988 D_26988.  (* [comment removed for export] *)
    sn F_2698c D_2698c.  (* [comment removed for export] *)
    sv F_26990 D_26990 (d).  (* [comment removed for export] *)
    sn F_26994 D_26994.  (* [comment removed for export] *)
    sn F_26998 D_26998.  (* [comment removed for export] *)
    sn F_2699c D_2699c.  (* [comment removed for export] *)
    stw F_269a0 D_269a0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_269a4 D_269a4 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_269a8 D_269a8 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_269ac D_269ac ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_269b0 D_269b0 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269b4 D_269b4 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_269b8 D_269b8.  (* [comment removed for export] *)
    stw F_269bc D_269bc (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269c0 D_269c0 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_269c4 D_269c4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_269c8 D_269c8 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269cc D_269cc (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269d0 D_269d0 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269d4 D_269d4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_269d8 D_269d8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_269dc D_269dc.  (* [comment removed for export] *)
    sn F_269e0 D_269e0.  (* [comment removed for export] *)
    sn F_269e4 D_269e4.  (* [comment removed for export] *)
    stw F_269e8 D_269e8 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269ec D_269ec (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269f0 D_269f0 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_269f4 D_269f4 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_269f8 D_269f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_269fc D_269fc.  (* [comment removed for export] *)
    sv F_26a00 D_26a00 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_26a04 D_26a04.  (* [comment removed for export] *)
    sn F_26a08 D_26a08.  (* [comment removed for export] *)
    sn F_26a0c D_26a0c.  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_26a10 D_26a10 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a14 D_26a14 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a18 D_26a18 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_26a1c D_26a1c (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_26a20 D_26a20.  (* [comment removed for export] *)
    sv F_26a24 D_26a24 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_26a28 D_26a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_26a2c D_26a2c ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Memset.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0Startup2 U.S0Startup3 U.S0Startup4 U.S0_code_1337c_1378c U.S0_code_1f188_1f438 U.S0_code_1ed68_1f620.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.FileSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Img OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StartupDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup.S0Startup1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup.S0Memset OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_1337c_1378c OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_1f188_1f438 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_1ed68_1f620.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSt.
Import WalkHideSt.OptIn.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main (sp0 : word) (av ev : list (list byte)) (uid hw : word) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x28a3c) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x64470)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x28a44)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x28c38)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x28b88)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x32090)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (sp0 : word) (av ev : list (list byte)) (uid hw : word) (rnd : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x28c48;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x441e0;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x13580;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev uid hw s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd) J (D_main sp0 av ev hw rnd tid)
}.

Section Assembly.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Variable uid : word.      (* [comment removed for export] *)
  Variable hw : word.       (* [comment removed for export] *)
  Variable rnd : EntryDraw. (* [comment removed for export] *)
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim (inp : ProcInput) K,
    in_argv inp = argv -> in_envp inp = envp -> in_uid inp = uid -> in_hwcap inp = hw ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp argv envp uid hw rnd tid regs mem ->
       realizes rsegs (mkCfg (mkst regs (0x13580 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
  Proof.
    intros brk mbase lim inp K Eav Eev Euid Ehw HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model]. rewrite Eav, Eev, Euid, Ehw.
    set (model := init_model (segments_reserved rsegs) brk mbase sp lim inp).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x13434 : word) by (apply bv_eq; reflexivity).
    rewrite cmem_init. fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run sp argv envp uid hw rnd Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x28958 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rnd) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x28958 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp argv envp uid hw rnd) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    (* [comment removed for export] *)
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp uid hw rnd) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp uid hw rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp uid hw rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp uid hw rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (su_rz_set_tid SEGS regs4 (0x28ea8 : word) _ (seg_rom SEGS) model K W_1f3e4 F_1f3e4 E_1f3e4);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x28ea8 : word) 4) with (0x28eac : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite su_with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite su_with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp uid hw rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp uid hw rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp uid hw rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp uid hw rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp uid hw rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd tid regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x13580 : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve HK.
  exact (ref_startup_sec sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd Hva Hve Hsp
           brk mbase lim inp K eq_refl eq_refl eq_refl eq_refl HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rnd tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev uid hw rnd) a n.
  Proof.
    intros segs a n Ha Hn. cps_destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. cps_destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev hw rnd tid a.
  Proof.
    intros a Ha. cps_destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev hw rnd tid) a n.
  Proof.
    intros segs a n Ha. cps_destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.

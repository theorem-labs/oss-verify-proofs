(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported section P1 to the new process model, replacing argv/envp/uid/hwcap variables with a ProcInput record plus launch hypotheses, writing u_argc, len_av and p1_run as plain statements, and using eapply for read_argc_w and read_argv_ptr_w; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Src0Startup1.v, lines 16, 29-41, 46-57, 72-87, 104, 134. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
StartupTac ArgvEnv RefLayout Js0Img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Startup1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Startup1.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Startup1.FPX_1.P1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "0J"; "4bvmap"; "5msteps"; "7J1"; "6regs_init"]; ["8cmem"; "8wfJ"; "9getr"; "9mkst"; "9wrap_mem"; ":loaded_segments"; ":phdrs"; ";In"; "<le"; "<of_nat"; "<sub"; "0argc"; "0av"; "0envp"; "0ev"; "0fx"]; ["0hw"; "0pn"; "0r"; "0rdraw"; "0regs'"; "0rom"; "0sp0"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0uid"]]).
Local Set Default Proof Using "All".
Abbreviation SEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
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
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x98414)))
(Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x33bac)).
Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x33a60 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0xa96e0 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x98194
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x33bac
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
Proof.
intros rom J.
intros HJ.
pose proof len_av as Hlen. pose proof u_argc as Hargc.
eexists. split.
- unfold regs_init.
stepn (ltac:(oF' 0x33a60%Z)) (ltac:(oD' 0x33a60%Z)).
stepn (ltac:(oF' 0x33a64%Z)) (ltac:(oD' 0x33a64%Z)).
stepn (ltac:(oF' 0x33a68%Z)) (ltac:(oD' 0x33a68%Z)).
stepn (ltac:(oF' 0x33a6c%Z)) (ltac:(oD' 0x33a6c%Z)).
stepn (ltac:(oF' 0x33a70%Z)) (ltac:(oD' 0x33a70%Z)).
stepiv (ltac:(oF' 0x33a74%Z)) (ltac:(oD' 0x33a74%Z)) sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
stepn (ltac:(oF' 0x33a78%Z)) (ltac:(oD' 0x33a78%Z)).
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
[ exact (ltac:(oF' 0x33a7c%Z)) | reflexivity | exact (ltac:(oD' 0x33a7c%Z))
| addr_norm; rewrite rdn_cmem_above by region_side;
apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
eapply read_argc_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi]
| apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
| step_simpl]; vnorm.
rewrite (v_lw_small argc) by (rewrite Hargc; lia).
stepn (ltac:(oF' 0x33a80%Z)) (ltac:(oD' 0x33a80%Z)).
stepn (ltac:(oF' 0x33a84%Z)) (ltac:(oD' 0x33a84%Z)).
stepn (ltac:(oF' 0x33a88%Z)) (ltac:(oD' 0x33a88%Z)).
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x33bac);
[exact (ltac:(oF' 0x33a8c%Z)) | reflexivity | exact (ltac:(oD' 0x33a8c%Z)) | rd_img img_b4d40_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x98164);
[exact (ltac:(oF' 0x33a90%Z)) | reflexivity | exact (ltac:(oD' 0x33a90%Z)) | rd_img img_b4d48_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x98a80);
[exact (ltac:(oF' 0x33a94%Z)) | reflexivity | exact (ltac:(oD' 0x33a94%Z)) | rd_img img_b4d50_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
sv (ltac:(oF' 0x33a98%Z)) (ltac:(oD' 0x33a98%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
stepn (ltac:(oF' 0x33a9c%Z)) (ltac:(oD' 0x33a9c%Z)).
stepn (ltac:(oF' 0x33aa0%Z)) (ltac:(oD' 0x33aa0%Z)).
stepn (ltac:(oF' 0x33aa4%Z)) (ltac:(oD' 0x33aa4%Z)).
sv (ltac:(oF' 0x983e0%Z)) (ltac:(oD' 0x983e0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stw (ltac:(oF' 0x983e4%Z)) (ltac:(oD' 0x983e4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983e8%Z)) (ltac:(oD' 0x983e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983ec%Z)) (ltac:(oD' 0x983ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983f0%Z)) (ltac:(oD' 0x983f0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stepn (ltac:(oF' 0x983f4%Z)) (ltac:(oD' 0x983f4%Z)).
stepn (ltac:(oF' 0x983f8%Z)) (ltac:(oD' 0x983f8%Z)).
stepn (ltac:(oF' 0x983fc%Z)) (ltac:(oD' 0x983fc%Z)).
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
[ exact (ltac:(oF' 0x98400%Z)) | reflexivity | exact (ltac:(oD' 0x98400%Z))
| addr_norm; rewrite rdn_cmem_above by region_side;
replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
by (rewrite word_add_nat; f_equal; lia);
eapply read_argv_ptr_w; first [exact Hva | exact Hvl | exact Hlau | exact Hlo | exact Hhi | lia]
| apply bytes_le_to_Z_8 ]
| step_simpl]; vnorm.
stepiv (ltac:(oF' 0x98404%Z)) (ltac:(oD' 0x98404%Z)) (Z_to_bv 64 (8 * Z.of_nat (length av)))
ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
stepiv (ltac:(oF' 0x98408%Z)) (ltac:(oD' 0x98408%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
stepiv (ltac:(oF' 0x9840c%Z)) (ltac:(oD' 0x9840c%Z)) envp
ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
stepn (ltac:(oF' 0x98410%Z)) (ltac:(oD' 0x98410%Z)).
sv (ltac:(oF' 0x98168%Z)) (ltac:(oD' 0x98168%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stw (ltac:(oF' 0x9816c%Z)) (ltac:(oD' 0x9816c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x98414) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98170%Z)) (ltac:(oD' 0x98170%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98174%Z)) (ltac:(oD' 0x98174%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
stw (ltac:(oF' 0x98178%Z)) (ltac:(oD' 0x98178%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x33bac) ltac:(ok_win HJ).
stepn (ltac:(oF' 0x9817c%Z)) (ltac:(oD' 0x9817c%Z)).
stepn (ltac:(oF' 0x98180%Z)) (ltac:(oD' 0x98180%Z)).
sv (ltac:(oF' 0x98184%Z)) (ltac:(oD' 0x98184%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 368)).
stepn (ltac:(oF' 0x98188%Z)) (ltac:(oD' 0x98188%Z)).
stepn (ltac:(oF' 0x9818c%Z)) (ltac:(oD' 0x9818c%Z)).
stepn (ltac:(oF' 0x98190%Z)) (ltac:(oD' 0x98190%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity.
intros r Hr. cbn [In] in Hr.
repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
[ .. | contradiction]; gres; apply getr_empty.
Qed.
End P1.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

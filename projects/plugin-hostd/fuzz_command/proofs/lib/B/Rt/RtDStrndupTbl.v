(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The strndup interceptor body ___interceptor_strndup 0x4575c (196 instructions, nm size 0x310) of
   fuzz_command.asan-ubsan is outside YE34's icpt_ranges, which hold its trampoline 0x45184 (in the block 0x4517c,
   46) and the helpers it calls before the allocation: TryAsanInitFromRtl 0x5f68c and internal_strnlen 0x69dc0.
   tbl_snd is tbl_icpt plus the body. The code is fuzz_command.asan's (lib/A/Rt/RtDStrndupTbl.v) word for word
   modulo pc-relative fields; the lemma names keep that image's addresses. *)
Definition snd_ranges : list (Z * nat) := [(0x4575c, 196%nat)].
Definition tbl_snd : ctable := Eval vm_compute in build_ranges snd_ranges tbl_icpt.
Lemma tbl_snd_eq : tbl_snd = build_ranges snd_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_snd). Qed.
Lemma tbl_snd_ok : table_ok tfibsegs tbl_snd.
Proof.
rewrite tbl_snd_eq. apply build_ranges_ok; [| exact tbl_icpt_ok].
unfold snd_ranges. repeat constructor; cbn; discriminate.
Qed.
(* the trampoline (j 0x4575c), the first and the last instruction word of the body *)
Lemma tbl_snd_probe :
clookup tbl_snd 0x45184 = Some 0x5d80006f /\
clookup tbl_snd 0x4575c = Some 0x81010113 /\
clookup tbl_snd 0x45a68 = Some 0xe31ff06f.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_snd : forall (p : word) (w : bv 32),
clookup tbl_snd (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof.
intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply tbl_snd_ok. exact H.
Qed.
Lemma snd_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_snd FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_snd tbl_snd_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
End f.
Ltac ftac_s := apply fetch_snd; vm_compute; reflexivity.

(* The instruction words the walk steps one at a time: the stretch from internal_strnlen's return to the call of
   the malloc body (0x457ac-0x457b8), and everything after the malloc body returns (0x457bc-0x457d4, 0x4583c-0x458e8,
   0x458ec-0x458fc, 0x45968-0x459b0); the strict_string_checks arm 0x457d8-0x457f4 and the uninitialised arm
   0x457f8-0x45838 are not reached on this image (common_flags()->strict_string_checks = 0, asan_inited = 1). *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma S_45760 : fetch_word tfibsegs (Z_to_bv 64 0x457ac) = Some (0x00050913%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45760 : decode_any (0x00050913%bv : bv 32) = Some (OpImm ALU_ADD 18 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45764 : fetch_word tfibsegs (Z_to_bv 64 0x457b0) = Some (0x00150a93%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45764 : decode_any (0x00150a93%bv : bv 32) = Some (OpImm ALU_ADD 21 10 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45768 : fetch_word tfibsegs (Z_to_bv 64 0x457b4) = Some (0x000a8513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45768 : decode_any (0x000a8513%bv : bv 32) = Some (OpImm ALU_ADD 10 21 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4576c : fetch_word tfibsegs (Z_to_bv 64 0x457b8) = Some (0x3ec130ef%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4576c : decode_any (0x3ec130ef%bv : bv 32) = Some (Jal 1 78828, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45770 : fetch_word tfibsegs (Z_to_bv 64 0x457bc) = Some (0x00060597%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45770 : decode_any (0x00060597%bv : bv 32) = Some (Auipc 11 96, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45774 : fetch_word tfibsegs (Z_to_bv 64 0x457c0) = Some (0x7845bb03%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45774 : decode_any (0x7845bb03%bv : bv 32) = Some (Load SZ8 true 22 11 1924, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45778 : fetch_word tfibsegs (Z_to_bv 64 0x457c4) = Some (0x0fcb4583%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45778 : decode_any (0x0fcb4583%bv : bv 32) = Some (Load SZ1 false 11 22 252, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4577c : fetch_word tfibsegs (Z_to_bv 64 0x457c8) = Some (0x00050993%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4577c : decode_any (0x00050993%bv : bv 32) = Some (OpImm ALU_ADD 19 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45780 : fetch_word tfibsegs (Z_to_bv 64 0x457cc) = Some (0x0c058663%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45780 : decode_any (0x0c058663%bv : bv 32) = Some (Branch BC_EQ 11 0 204, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45784 : fetch_word tfibsegs (Z_to_bv 64 0x457d0) = Some (0x0f5b4503%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45784 : decode_any (0x0f5b4503%bv : bv 32) = Some (Load SZ1 false 10 22 245, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45788 : fetch_word tfibsegs (Z_to_bv 64 0x457d4) = Some (0x06050463%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45788 : decode_any (0x06050463%bv : bv 32) = Some (Branch BC_EQ 10 0 104, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_457f0 : fetch_word tfibsegs (Z_to_bv 64 0x4583c) = Some (0x0b5a7863%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_457f0 : decode_any (0x0b5a7863%bv : bv 32) = Some (Branch BC_GEU 20 21 176, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_457f4 : fetch_word tfibsegs (Z_to_bv 64 0x45840) = Some (0xfff4c513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_457f4 : decode_any (0xfff4c513%bv : bv 32) = Some (OpImm ALU_XOR 10 9 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_457f8 : fetch_word tfibsegs (Z_to_bv 64 0x45844) = Some (0x80040b93%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_457f8 : decode_any (0x80040b93%bv : bv 32) = Some (OpImm ALU_ADD 23 8 2048, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_457fc : fetch_word tfibsegs (Z_to_bv 64 0x45848) = Some (0xf98b8b93%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_457fc : decode_any (0xf98b8b93%bv : bv 32) = Some (OpImm ALU_ADD 23 23 3992, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45800 : fetch_word tfibsegs (Z_to_bv 64 0x4584c) = Some (0x0b456a63%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45800 : decode_any (0x0b456a63%bv : bv 32) = Some (Branch BC_LTU 10 20 180, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45804 : fetch_word tfibsegs (Z_to_bv 64 0x45850) = Some (0xfbfa0513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45804 : decode_any (0xfbfa0513%bv : bv 32) = Some (OpImm ALU_ADD 10 20 4031, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45808 : fetch_word tfibsegs (Z_to_bv 64 0x45854) = Some (0xfbf00593%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45808 : decode_any (0xfbf00593%bv : bv 32) = Some (OpImm ALU_ADD 11 0 4031, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4580c : fetch_word tfibsegs (Z_to_bv 64 0x45858) = Some (0x10a5f863%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4580c : decode_any (0x10a5f863%bv : bv 32) = Some (Branch BC_GEU 11 10 272, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45810 : fetch_word tfibsegs (Z_to_bv 64 0x4585c) = Some (0x00060517%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45810 : decode_any (0x00060517%bv : bv 32) = Some (Auipc 10 96, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45814 : fetch_word tfibsegs (Z_to_bv 64 0x45860) = Some (0x6f453503%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45814 : decode_any (0x6f453503%bv : bv 32) = Some (Load SZ8 true 10 10 1780, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45818 : fetch_word tfibsegs (Z_to_bv 64 0x45864) = Some (0x01448633%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45818 : decode_any (0x01448633%bv : bv 32) = Some (Op ALU_ADD 12 9 20, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4581c : fetch_word tfibsegs (Z_to_bv 64 0x45868) = Some (0x00053583%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4581c : decode_any (0x00053583%bv : bv 32) = Some (Load SZ8 true 11 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45820 : fetch_word tfibsegs (Z_to_bv 64 0x4586c) = Some (0x0034d513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45820 : decode_any (0x0034d513%bv : bv 32) = Some (ShiftImm ALU_SRL 10 9 3, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45824 : fetch_word tfibsegs (Z_to_bv 64 0x45870) = Some (0xfff60613%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45824 : decode_any (0xfff60613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45828 : fetch_word tfibsegs (Z_to_bv 64 0x45874) = Some (0x00365693%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45828 : decode_any (0x00365693%bv : bv 32) = Some (ShiftImm ALU_SRL 13 12 3, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4582c : fetch_word tfibsegs (Z_to_bv 64 0x45878) = Some (0x00a58533%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4582c : decode_any (0x00a58533%bv : bv 32) = Some (Op ALU_ADD 10 11 10, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45830 : fetch_word tfibsegs (Z_to_bv 64 0x4587c) = Some (0x00d585b3%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45830 : decode_any (0x00d585b3%bv : bv 32) = Some (Op ALU_ADD 11 11 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45834 : fetch_word tfibsegs (Z_to_bv 64 0x45880) = Some (0xff857693%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45834 : decode_any (0xff857693%bv : bv 32) = Some (OpImm ALU_AND 13 10 4088, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45838 : fetch_word tfibsegs (Z_to_bv 64 0x45884) = Some (0xff85f713%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45838 : decode_any (0xff85f713%bv : bv 32) = Some (OpImm ALU_AND 14 11 4088, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4583c : fetch_word tfibsegs (Z_to_bv 64 0x45888) = Some (0x0006b683%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4583c : decode_any (0x0006b683%bv : bv 32) = Some (Load SZ8 true 13 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45840 : fetch_word tfibsegs (Z_to_bv 64 0x4588c) = Some (0x00073703%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45840 : decode_any (0x00073703%bv : bv 32) = Some (Load SZ8 true 14 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45844 : fetch_word tfibsegs (Z_to_bv 64 0x45890) = Some (0x00d766b3%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45844 : decode_any (0x00d766b3%bv : bv 32) = Some (Op ALU_OR 13 14 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45848 : fetch_word tfibsegs (Z_to_bv 64 0x45894) = Some (0x0c069e63%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45848 : decode_any (0x0c069e63%bv : bv 32) = Some (Branch BC_NE 13 0 220, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4584c : fetch_word tfibsegs (Z_to_bv 64 0x45898) = Some (0x00098e63%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4584c : decode_any (0x00098e63%bv : bv 32) = Some (Branch BC_EQ 19 0 28, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45850 : fetch_word tfibsegs (Z_to_bv 64 0x4589c) = Some (0x00098513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45850 : decode_any (0x00098513%bv : bv 32) = Some (OpImm ALU_ADD 10 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45854 : fetch_word tfibsegs (Z_to_bv 64 0x458a0) = Some (0x00048593%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45854 : decode_any (0x00048593%bv : bv 32) = Some (OpImm ALU_ADD 11 9 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45858 : fetch_word tfibsegs (Z_to_bv 64 0x458a4) = Some (0x00090613%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45858 : decode_any (0x00090613%bv : bv 32) = Some (OpImm ALU_ADD 12 18 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4585c : fetch_word tfibsegs (Z_to_bv 64 0x458a8) = Some (0x0e4240ef%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4585c : decode_any (0x0e4240ef%bv : bv 32) = Some (Jal 1 147684, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45860 : fetch_word tfibsegs (Z_to_bv 64 0x458ac) = Some (0x01298933%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45860 : decode_any (0x01298933%bv : bv 32) = Some (Op ALU_ADD 18 19 18, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45864 : fetch_word tfibsegs (Z_to_bv 64 0x458b0) = Some (0x00090023%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45864 : decode_any (0x00090023%bv : bv 32) = Some (Store SZ1 18 0 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45868 : fetch_word tfibsegs (Z_to_bv 64 0x458b4) = Some (0x00098513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45868 : decode_any (0x00098513%bv : bv 32) = Some (OpImm ALU_ADD 10 19 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4586c : fetch_word tfibsegs (Z_to_bv 64 0x458b8) = Some (0x08010113%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4586c : decode_any (0x08010113%bv : bv 32) = Some (OpImm ALU_ADD 2 2 128, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45870 : fetch_word tfibsegs (Z_to_bv 64 0x458bc) = Some (0x7e813083%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45870 : decode_any (0x7e813083%bv : bv 32) = Some (Load SZ8 true 1 2 2024, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45874 : fetch_word tfibsegs (Z_to_bv 64 0x458c0) = Some (0x7e013403%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45874 : decode_any (0x7e013403%bv : bv 32) = Some (Load SZ8 true 8 2 2016, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45878 : fetch_word tfibsegs (Z_to_bv 64 0x458c4) = Some (0x7d813483%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45878 : decode_any (0x7d813483%bv : bv 32) = Some (Load SZ8 true 9 2 2008, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4587c : fetch_word tfibsegs (Z_to_bv 64 0x458c8) = Some (0x7d013903%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4587c : decode_any (0x7d013903%bv : bv 32) = Some (Load SZ8 true 18 2 2000, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45880 : fetch_word tfibsegs (Z_to_bv 64 0x458cc) = Some (0x7c813983%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45880 : decode_any (0x7c813983%bv : bv 32) = Some (Load SZ8 true 19 2 1992, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45884 : fetch_word tfibsegs (Z_to_bv 64 0x458d0) = Some (0x7c013a03%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45884 : decode_any (0x7c013a03%bv : bv 32) = Some (Load SZ8 true 20 2 1984, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45888 : fetch_word tfibsegs (Z_to_bv 64 0x458d4) = Some (0x7b813a83%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45888 : decode_any (0x7b813a83%bv : bv 32) = Some (Load SZ8 true 21 2 1976, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4588c : fetch_word tfibsegs (Z_to_bv 64 0x458d8) = Some (0x7b013b03%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4588c : decode_any (0x7b013b03%bv : bv 32) = Some (Load SZ8 true 22 2 1968, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45890 : fetch_word tfibsegs (Z_to_bv 64 0x458dc) = Some (0x7a813b83%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45890 : decode_any (0x7a813b83%bv : bv 32) = Some (Load SZ8 true 23 2 1960, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45894 : fetch_word tfibsegs (Z_to_bv 64 0x458e0) = Some (0x7a013c03%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45894 : decode_any (0x7a013c03%bv : bv 32) = Some (Load SZ8 true 24 2 1952, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45898 : fetch_word tfibsegs (Z_to_bv 64 0x458e4) = Some (0x7f010113%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45898 : decode_any (0x7f010113%bv : bv 32) = Some (OpImm ALU_ADD 2 2 2032, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4589c : fetch_word tfibsegs (Z_to_bv 64 0x458e8) = Some (0x00008067%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4589c : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_458a0 : fetch_word tfibsegs (Z_to_bv 64 0x458ec) = Some (0x000a8a13%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_458a0 : decode_any (0x000a8a13%bv : bv 32) = Some (OpImm ALU_ADD 20 21 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_458a4 : fetch_word tfibsegs (Z_to_bv 64 0x458f0) = Some (0xfff4c513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_458a4 : decode_any (0xfff4c513%bv : bv 32) = Some (OpImm ALU_XOR 10 9 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_458a8 : fetch_word tfibsegs (Z_to_bv 64 0x458f4) = Some (0x80040b93%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_458a8 : decode_any (0x80040b93%bv : bv 32) = Some (OpImm ALU_ADD 23 8 2048, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_458ac : fetch_word tfibsegs (Z_to_bv 64 0x458f8) = Some (0xf98b8b93%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_458ac : decode_any (0xf98b8b93%bv : bv 32) = Some (OpImm ALU_ADD 23 23 3992, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_458b0 : fetch_word tfibsegs (Z_to_bv 64 0x458fc) = Some (0xf5557ae3%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_458b0 : decode_any (0xf5557ae3%bv : bv 32) = Some (Branch BC_GEU 10 21 8020, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4591c : fetch_word tfibsegs (Z_to_bv 64 0x45968) = Some (0x020a1e63%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4591c : decode_any (0x020a1e63%bv : bv 32) = Some (Branch BC_NE 20 0 60, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45920 : fetch_word tfibsegs (Z_to_bv 64 0x4596c) = Some (0xf2dff06f%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45920 : decode_any (0xf2dff06f%bv : bv 32) = Some (Jal 0 2096940, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45924 : fetch_word tfibsegs (Z_to_bv 64 0x45970) = Some (0x00058683%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45924 : decode_any (0x00058683%bv : bv 32) = Some (Load SZ1 true 13 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45928 : fetch_word tfibsegs (Z_to_bv 64 0x45974) = Some (0x00767613%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45928 : decode_any (0x00767613%bv : bv 32) = Some (OpImm ALU_AND 12 12 7, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4592c : fetch_word tfibsegs (Z_to_bv 64 0x45978) = Some (0x00d03733%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4592c : decode_any (0x00d03733%bv : bv 32) = Some (Op ALU_SLTU 14 0 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45930 : fetch_word tfibsegs (Z_to_bv 64 0x4597c) = Some (0x00d62633%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45930 : decode_any (0x00d62633%bv : bv 32) = Some (Op ALU_SLT 12 12 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45934 : fetch_word tfibsegs (Z_to_bv 64 0x45980) = Some (0x00164613%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45934 : decode_any (0x00164613%bv : bv 32) = Some (OpImm ALU_XOR 12 12 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45938 : fetch_word tfibsegs (Z_to_bv 64 0x45984) = Some (0x00c77633%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45938 : decode_any (0x00c77633%bv : bv 32) = Some (Op ALU_AND 12 14 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4593c : fetch_word tfibsegs (Z_to_bv 64 0x45988) = Some (0x00b57a63%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4593c : decode_any (0x00b57a63%bv : bv 32) = Some (Branch BC_GEU 10 11 20, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45940 : fetch_word tfibsegs (Z_to_bv 64 0x4598c) = Some (0x00054683%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45940 : decode_any (0x00054683%bv : bv 32) = Some (Load SZ1 false 13 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45944 : fetch_word tfibsegs (Z_to_bv 64 0x45990) = Some (0x00150513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45944 : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45948 : fetch_word tfibsegs (Z_to_bv 64 0x45994) = Some (0x00c6e633%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45948 : decode_any (0x00c6e633%bv : bv 32) = Some (Op ALU_OR 12 13 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4594c : fetch_word tfibsegs (Z_to_bv 64 0x45998) = Some (0xfeb51ae3%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4594c : decode_any (0xfeb51ae3%bv : bv 32) = Some (Branch BC_NE 10 11 8180, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45950 : fetch_word tfibsegs (Z_to_bv 64 0x4599c) = Some (0x0ff67513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45950 : decode_any (0x0ff67513%bv : bv 32) = Some (OpImm ALU_AND 10 12 255, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45954 : fetch_word tfibsegs (Z_to_bv 64 0x459a0) = Some (0xee050ce3%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45954 : decode_any (0xee050ce3%bv : bv 32) = Some (Branch BC_EQ 10 0 7928, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45958 : fetch_word tfibsegs (Z_to_bv 64 0x459a4) = Some (0x00048513%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45958 : decode_any (0x00048513%bv : bv 32) = Some (OpImm ALU_ADD 10 9 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_4595c : fetch_word tfibsegs (Z_to_bv 64 0x459a8) = Some (0x000a0593%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_4595c : decode_any (0x000a0593%bv : bv 32) = Some (OpImm ALU_ADD 11 20 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45960 : fetch_word tfibsegs (Z_to_bv 64 0x459ac) = Some (0x04d140ef%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45960 : decode_any (0x04d140ef%bv : bv 32) = Some (Jal 1 84044, 4%Z). Proof. vm_refl_bv. Qed.
Lemma S_45964 : fetch_word tfibsegs (Z_to_bv 64 0x459b0) = Some (0xee0504e3%bv : bv 32). Proof. ftac_s. Qed.
Lemma DS_45964 : decode_any (0xee0504e3%bv : bv 32) = Some (Branch BC_EQ 10 0 7912, 4%Z). Proof. vm_refl_bv. Qed.
End g.

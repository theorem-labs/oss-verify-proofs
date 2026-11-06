(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: relocated from a Theorem Labs lane's cgif_file_fuzzer-coordinate copy (a working branch f8664b31b9c, proofs/cgif/cgif_file_fuzzer/lib/A/FMstrlen_musl.v) to fuzz_identity.asan-ubsan by an address map recorded by the porting lane; module paths, the record class TfibSyms (unchanged), YA0m import dropped. *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms, and the core modules are Required by full path at the applied B core's names: lib/B/A<x>.v -> lib/ReusableB/Y<x>.v (AB1v AB1w AE20 AE2y AE34 AE39 AE3a AE6y AF0l AF0m AF0x -> YB1v YB1w YE20 YE2y YE34 YE39 YE3a YE6y YF0l YF0m YF0x, qualified names included), lib/Reusable/YA0m, YE08, YE21. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP02.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1v
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YE3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(* musl strlen, tfib_A_musl_strlen .. tfib_E_musl_strlen (0x94f50 .. 0x94fe0 in fuzz_identity.asan-ubsan):
   0x00 andi a1,a0,7; 0x04 mv a2,a0; 0x08 beqz a1 -> 0x3c (word loop)
   0x0c lbu a1,0(a0); 0x10 beqz a1 -> 0x88; 0x14 addi a2,a0,1; 0x18 mv a1,a0
   0x1c L1: addi a3,a1,1; andi a3,a3,7; beqz a3 -> 0x3c; lbu a3,0(a2); addi a2,a2,1; addi a1,a1,1; bnez a3 -> 0x1c
   0x38 j 0x80
   0x3c auipc a1; auipc a4; ld a3 (ONES); ld a4 (HIGHS); addi a1,a2,-9; addi a2,a2,-8
   0x54 L2: ld a5,8(a2); addi a2,a2,8; sub a6,a3,a5; or a5,a6,a5; and a5,a5,a4; addi a1,a1,8; beq a5,a4 -> 0x54
   0x70 L3: lbu a3,0(a2); addi a2,a2,1; addi a1,a1,1; bnez a3 -> 0x70
   0x80 sub a0,a1,a0; ret
   0x88 sub a0,a0,a0; ret *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma FS_000 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)) = Some (0x00757593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_000 : decode_any (0x00757593%bv : bv 32) = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_004 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x4)) = Some (0x00050613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_004 : decode_any (0x00050613%bv : bv 32) = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_008 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x8)) = Some (0x02058a63%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_008 : decode_any (0x02058a63%bv : bv 32) = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_00c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0xc)) = Some (0x00054583%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_00c : decode_any (0x00054583%bv : bv 32) = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_010 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x10)) = Some (0x06058c63%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_010 : decode_any (0x06058c63%bv : bv 32) = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_014 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x14)) = Some (0x00150613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_014 : decode_any (0x00150613%bv : bv 32) = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_018 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x18)) = Some (0x00050593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_018 : decode_any (0x00050593%bv : bv 32) = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_01c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x1c)) = Some (0x00158693%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_01c : decode_any (0x00158693%bv : bv 32) = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_020 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x20)) = Some (0x0076f693%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_020 : decode_any (0x0076f693%bv : bv 32) = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_024 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x24)) = Some (0x00068c63%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_024 : decode_any (0x00068c63%bv : bv 32) = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_028 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x28)) = Some (0x00064683%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_028 : decode_any (0x00064683%bv : bv 32) = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_02c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x2c)) = Some (0x00160613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_02c : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_030 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x30)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_030 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_034 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x34)) = Some (0xfe0694e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_034 : decode_any (0xfe0694e3%bv : bv 32) = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_038 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x38)) = Some (0x0480006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_038 : decode_any (0x0480006f%bv : bv 32) = Some (Jal 0 72, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_04c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x4c)) = Some (0xff760593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_04c : decode_any (0xff760593%bv : bv 32) = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_050 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x50)) = Some (0xff860613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_050 : decode_any (0xff860613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_054 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) = Some (0x00863783%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_054 : decode_any (0x00863783%bv : bv 32) = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_058 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x58)) = Some (0x00860613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_058 : decode_any (0x00860613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_05c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x5c)) = Some (0x40f68833%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_05c : decode_any (0x40f68833%bv : bv 32) = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_060 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x60)) = Some (0x00f867b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_060 : decode_any (0x00f867b3%bv : bv 32) = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_064 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x64)) = Some (0x00e7f7b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_064 : decode_any (0x00e7f7b3%bv : bv 32) = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_068 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x68)) = Some (0x00858593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_068 : decode_any (0x00858593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_06c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x6c)) = Some (0xfee784e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_06c : decode_any (0xfee784e3%bv : bv 32) = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_070 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x70)) = Some (0x00064683%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_070 : decode_any (0x00064683%bv : bv 32) = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_074 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x74)) = Some (0x00160613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_074 : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_078 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x78)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_078 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_07c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x7c)) = Some (0xfe069ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_07c : decode_any (0xfe069ae3%bv : bv 32) = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_080 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x80)) = Some (0x40a58533%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_080 : decode_any (0x40a58533%bv : bv 32) = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_084 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x84)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_084 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_088 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x88)) = Some (0x40a50533%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_088 : decode_any (0x40a50533%bv : bv 32) = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_08c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x8c)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_08c : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
(* the two auipc/ld pairs that load the constants; their words are read from the table so that
   the file carries no address-dependent immediate *)
Definition tfib_strlen_w03c : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x3c).
Definition tfib_strlen_w040 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x40).
Definition tfib_strlen_w044 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x44).
Definition tfib_strlen_w048 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x48).
Definition tfib_strlen_i03c : Z := Eval vm_compute in auipc_imm20 tfib_strlen_w03c.
Definition tfib_strlen_i040 : Z := Eval vm_compute in auipc_imm20 tfib_strlen_w040.
Definition tfib_strlen_i044 : Z := Eval vm_compute in ld_imm12 tfib_strlen_w044.
Definition tfib_strlen_i048 : Z := Eval vm_compute in ld_imm12 tfib_strlen_w048.
Definition tfib_strlen_aui1 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) (Z.shiftl (bv_signed (Z_to_bv 20 tfib_strlen_i03c)) 12)).
Definition tfib_strlen_aui2 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (tfib_A_musl_strlen + 0x40)) (Z.shiftl (bv_signed (Z_to_bv 20 tfib_strlen_i040)) 12)).
Lemma FS_03c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) = Some (Z_to_bv 32 tfib_strlen_w03c).
Proof. ftac. Qed.
Lemma DS_03c : decode_any (Z_to_bv 32 tfib_strlen_w03c) = Some (Auipc 11 (Z_to_bv 20 tfib_strlen_i03c), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_040 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x40)) = Some (Z_to_bv 32 tfib_strlen_w040).
Proof. ftac. Qed.
Lemma DS_040 : decode_any (Z_to_bv 32 tfib_strlen_w040) = Some (Auipc 14 (Z_to_bv 20 tfib_strlen_i040), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_044 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x44)) = Some (Z_to_bv 32 tfib_strlen_w044).
Proof. ftac. Qed.
Lemma DS_044 : decode_any (Z_to_bv 32 tfib_strlen_w044) = Some (Load SZ8 true 13 11 (Z_to_bv 12 tfib_strlen_i044), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_048 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x48)) = Some (Z_to_bv 32 tfib_strlen_w048).
Proof. ftac. Qed.
Lemma DS_048 : decode_any (Z_to_bv 32 tfib_strlen_w048) = Some (Load SZ8 true 14 14 (Z_to_bv 12 tfib_strlen_i048), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_strlen_ld_targets :
bv_unsigned (v_addi (Z_to_bv 64 tfib_strlen_aui1) (bv_signed (Z_to_bv 12 tfib_strlen_i044))) = tfib_D_const_ONES_0x0101010101010100 /\
bv_unsigned (v_addi (Z_to_bv 64 tfib_strlen_aui2) (bv_signed (Z_to_bv 12 tfib_strlen_i048))) = tfib_D_const_HIGHS_0x8080808080808080.
Proof. vm_compute. split; reflexivity. Qed.
Lemma v_sub_w : forall (z : Z) (x : word), v_sub (Z_to_bv 64 z) x = Z_to_bv 64 (z - bv_unsigned x).
Proof. intros z x. rewrite <- (v_sub_lit z (bv_unsigned x)), Z_to_bv_bv_unsigned. reflexivity. Qed.
End f.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable s : list byte.
Variable p : word.
Variable mem rom : word -> option byte.
Definition Ps : Z := bv_unsigned p.
Definition Ls : Z := Z.of_nat (length s).
Definition Es : Z := Ps + Ls.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hfit : bv_unsigned p + Z.of_nat (length s) + 8 < 2^64.
Hypothesis Hstr : forall j, (j <= length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Lemma Es_eq : Es = bv_unsigned p + Z.of_nat (length s). Proof. reflexivity. Qed.
Lemma Ps_eq : Ps = bv_unsigned p. Proof. reflexivity. Qed.
Lemma Ls_eq : Ls = Z.of_nat (length s). Proof. reflexivity. Qed.
Ltac epl := pose proof Es_eq; pose proof Ps_eq; pose proof Ls_eq; pose proof (u64_range p).
Lemma sl_byte_nz : forall j, (j < length s)%nat -> nth j (s ++ [NUL]) NUL <> NUL.
Proof. intros j Hj Hc. apply Hnul. rewrite <- Hc. apply nth_app_nul_in. exact Hj. Qed.
Lemma p_lit : Z_to_bv 64 (bv_unsigned p + Z.of_nat 0) = p.
Proof. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* L3, the byte loop after the word loop: a2 = E - d is the next byte, a1 = a2 - 1 *)
Lemma sl_tail : forall d regs,
(d <= length s)%nat ->
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 (Es - Z.of_nat d - 1) ->
getr regs 12 = Z_to_bv 64 (Es - Z.of_nat d) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x70)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 Ls
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
induction d as [|d IH]; intros regs Hd H10 H11 H12; epl.
- eexists. split.
+ norm_pc.
steplbu FS_070 DS_070
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_0;
replace (Es - Z.of_nat 0) with (bv_unsigned p + Z.of_nat (length s)) by lia;
apply Hstr; lia).
rewrite nth_app_nul_last.
stepiv' FS_074 DS_074 (Z_to_bv 64 (Es + 1))
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepiv' FS_078 DS_078 (Z_to_bv 64 Es)
ltac:(gr; rewrite H11; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepbf FS_07c DS_07c ltac:(gr; vm_compute; reflexivity).
stepov FS_080 DS_080 (Z_to_bv 64 Ls)
ltac:(rewrite alu_sub; gr; rewrite H10, v_sub_w; f_equal; lia).
stepret FS_084 DS_084. msteps_done.
+ split; [gr; reflexivity|].
intros r Hr10 Hr11 Hr12 Hr13. rewrite !getr_other by assumption. reflexivity.
- set (b := nth (length s - S d) (s ++ [NUL]) NUL).
assert (Hb : b <> NUL) by (apply sl_byte_nz; lia).
set (regs1 := regupd (regupd (regupd regs 13 (Z_to_bv 64 (bv_unsigned b)))
12 (Z_to_bv 64 (Es - Z.of_nat d))) 11 (Z_to_bv 64 (Es - Z.of_nat d - 1))).
destruct (IH regs1) as (regs' & Hms & H10' & Hfr).
{ lia. }
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
steplbu FS_070 DS_070
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_0;
replace (Es - Z.of_nat (S d)) with (bv_unsigned p + Z.of_nat (length s - S d)) by lia;
apply Hstr; lia).
fold b.
stepiv' FS_074 DS_074 (Z_to_bv 64 (Es - Z.of_nat d))
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepiv' FS_078 DS_078 (Z_to_bv 64 (Es - Z.of_nat d - 1))
ltac:(gr; rewrite H11; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepbt FS_07c DS_07c
ltac:(gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
subst regs1. msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Hypothesis Hrd : forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 <> None.
Lemma sl_word_at : forall w, Ps <= w -> w + 8 <= Es - Es mod 8 + 8 ->
exists bs, rdn tfibsegs mem (Z_to_bv 64 w) 8 = Some bs /\ length bs = 8%nat /\
(forall i, (i < 8)%nat -> w + Z.of_nat i <= Es ->
nth i bs NUL = nth (Z.to_nat (w - Ps) + i) (s ++ [NUL]) NUL).
Proof.
intros w Hlo Hhi. unfold Es, Ps, Ls in *.
pose proof (u64_range p) as Hp.
assert (Hm2 : 0 <= (bv_unsigned p + Z.of_nat (length s)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (rdn_total tfibsegs mem 8 (Z_to_bv 64 w)) as [bs Hbs].
{ intros k Hk. rewrite word_add_nat, u_Z2bv by lia.
destruct (Z_lt_le_dec (bv_unsigned p + Z.of_nat (length s)) (w + Z.of_nat k)) as [Hpast|Hin].
- apply Hrd. lia.
- replace (w + Z.of_nat k) with (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + k)) by lia.
rewrite Hstr by lia. discriminate. }
exists bs. split; [exact Hbs|]. split; [exact (rdn_length _ _ _ _ _ Hbs)|].
intros i Hi HiE.
pose proof (rdn_nth tfibsegs mem 8 (Z_to_bv 64 w) bs i Hbs ltac:(lia)) as H1.
rewrite word_add_nat, u_Z2bv in H1 by lia.
pose proof (Hstr (Z.to_nat (w - bv_unsigned p) + i)%nat ltac:(lia)) as H2.
replace (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + i)) with (w + Z.of_nat i) in H2 by lia.
rewrite H1 in H2. injection H2 as H3. exact H3.
Qed.
(* L2, the word loop: a2 = w - 8 where w is the next word, a1 = w - 9, a3 = ONES, a4 = HIGHS *)
Lemma sl_words : forall k regs (w : Z),
w + 8 * Z.of_nat k = Es - Es mod 8 ->
Ps <= w ->
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 (w - 9) ->
getr regs 12 = Z_to_bv 64 (w - 8) ->
getr regs 13 = Z_to_bv 64 C1 ->
getr regs 14 = Z_to_bv 64 HZ.HIGHS ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 Ls
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv ->
getr regs' r = getr regs r).
Proof.
induction k as [|k IH]; intros regs w Hk Hpw H10 H11 H12 H13 H14.
all: epl.
all: assert (Hm2 : 0 <= Es mod 8 < 8) by (apply Z.mod_pos_bound; lia).
all: assert (HmE : Es mod 8 <= Es) by (apply Z.mod_le; lia).
all: destruct (sl_word_at w) as (bs & Hbs & Hlen & Hnth); [lia|lia|].
all: set (x := bytes_le_to_Z bs).
all: pose proof (bytes_le_to_Z_range bs Hlen) as Hx; fold x in Hx.
all: set (v := Z_to_bv 64 x).
all: assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
all: set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS)).
all: set (regs5 := regupd (regupd (regupd (regupd (regupd (regupd regs 15 v) 12 (Z_to_bv 64 w))
16 (v_sub (Z_to_bv 64 C1) v)) 15 (v_or (v_sub (Z_to_bv 64 C1) v) v)) 15 tw) 11 (Z_to_bv 64 (w - 1))).
all: assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) mem rom)
(mkst regs5 (Z_to_bv 64 (tfib_A_musl_strlen + 0x6c)) mem rom)).
1,3: norm_pc;
(chain_step; [reflexivity | eapply step_ld with (bs := bs) (v := v);
[exact_lit FS_054 | reflexivity | exact DS_054
| rewrite H12; imm_norm; rewrite v_addi_lit; replace (w - 8 + 8) with w by lia; exact Hbs
| rewrite Hv; reflexivity ] | step_simpl ]);
stepiv' FS_058 DS_058 (Z_to_bv 64 w) ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia);
stepov FS_05c DS_05c (v_sub (Z_to_bv 64 C1) v) ltac:(rewrite alu_sub; gr; rewrite H13; reflexivity);
stepov FS_060 DS_060 (v_or (v_sub (Z_to_bv 64 C1) v) v) ltac:(rewrite alu_or; gr; reflexivity);
stepov FS_064 DS_064 tw ltac:(rewrite alu_and; gr; rewrite H14; reflexivity);
stepiv' FS_068 DS_068 (Z_to_bv 64 (w - 1)) ltac:(gr; rewrite H11; imm_norm; rewrite v_addi_lit; f_equal; lia);
subst regs5; msteps_done.
all: assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz x) by (subst tw; rewrite haszero_ref, Hv; reflexivity).
all: pose proof (HZ.Tz_range x) as HT.
-
assert (Hw : w = Es - Es mod 8) by lia.
assert (HTnz : HZ.Tz x <> 0).
{ apply (HZ.Tz_haszero x (Z.to_nat (Es mod 8))); [lia|lia| |].
- subst x. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia.
replace (Z.to_nat (w - Ps) + Z.to_nat (Es mod 8))%nat with (length s) by lia.
rewrite nth_app_nul_last. reflexivity.
- intros j Hj. subst x. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia.
apply byte_nz_u. apply sl_byte_nz. lia. }
destruct (sl_tail (Z.to_nat (Es mod 8)) regs5) as (regs' & Hms & H10' & Hfr).
{ lia. }
{ subst regs5. gr. exact H10. }
{ subst regs5. gr. f_equal. lia. }
{ subst regs5. gr. f_equal. lia. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs5 1) by (subst regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbf FS_06c DS_06c
ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken]; unfold bv_eqb;
rewrite Htw, u_Z2bv by (unfold HZ.HIGHS; lia); apply Z.eqb_neq; lia).
msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13). subst regs5.
rewrite !getr_other by assumption. reflexivity.
-
assert (HTz : HZ.Tz x = 0).
{ apply HZ.Tz_nozero; [lia|]. intros i Hi. subst x. rewrite zb_of_bytes by lia. fold NUL.
rewrite Hnth by lia. apply byte_nz_u. apply sl_byte_nz. lia. }
destruct (IH regs5 (w + 8)) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs5; gr; first [reflexivity | assumption | f_equal; lia]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs5 1) by (subst regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_06c DS_06c
ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken]; unfold bv_eqb;
rewrite Htw, HTz, u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r, Z.eqb_refl; reflexivity).
msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13 Hr15 Hr16). subst regs5.
rewrite !getr_other by assumption. reflexivity.
Qed.
Hypothesis Hrom : forall a : Z, tfib_D_const_HIGHS_0x8080808080808080 <= a < (tfib_D_const_ONES_0x0101010101010100 + 8) ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Lemma sl_rd_C1 : exists bs, rdn tfibsegs mem (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) 8 = Some bs /\ bytes_le_to_Z bs = C1.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
Lemma sl_rd_HIGHS : exists bs, rdn tfibsegs mem (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) 8 = Some bs /\ bytes_le_to_Z bs = HZ.HIGHS.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
(* the word-loop set-up at 0x3c: a2 = q, the first aligned address, P <= q <= E *)
Lemma sl_aligned : forall regs (q : Z),
Ps <= q <= Es -> q mod 8 = 0 ->
getr regs 10 = p ->
getr regs 12 = Z_to_bv 64 q ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 Ls
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros regs q Hq Hq8 H10 H12. epl.
destruct sl_rd_C1 as (bs1 & Hbs1 & Hv1).
destruct sl_rd_HIGHS as (bs2 & Hbs2 & Hv2).
set (regs2 := regupd (regupd (regupd (regupd (regupd (regupd regs
11 (Z_to_bv 64 tfib_strlen_aui1))
14 (Z_to_bv 64 tfib_strlen_aui2))
13 (Z_to_bv 64 C1))
14 (Z_to_bv 64 HZ.HIGHS))
11 (Z_to_bv 64 (q - 9)))
12 (Z_to_bv 64 (q - 8))).
assert (HE8 : Es = 8 * (Es / 8) + Es mod 8) by (apply Z.div_mod; lia).
assert (Hq8' : q = 8 * (q / 8)) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
assert (Hm2 : 0 <= Es mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (sl_words (Z.to_nat (Es / 8 - q / 8)) regs2 q) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs2; gr; first [reflexivity | assumption]).
exists regs'. split.
+ eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2; gr; reflexivity); exact Hms].
norm_pc.
stepiv' FS_03c DS_03c (Z_to_bv 64 tfib_strlen_aui1) ltac:(bveq).
stepiv' FS_040 DS_040 (Z_to_bv 64 tfib_strlen_aui2) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs1) (v := Z_to_bv 64 C1);
[ exact_lit FS_044 | reflexivity | exact DS_044
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) by bveq end; exact Hbs1
| rewrite Hv1; reflexivity ] | step_simpl ].
chain_step; [reflexivity | eapply step_ld with (bs := bs2) (v := Z_to_bv 64 HZ.HIGHS);
[ exact_lit FS_048 | reflexivity | exact DS_048
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) by bveq end; exact Hbs2
| rewrite Hv2; reflexivity ] | step_simpl ].
stepiv' FS_04c DS_04c (Z_to_bv 64 (q - 9))
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepiv' FS_050 DS_050 (Z_to_bv 64 (q - 8))
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia).
subst regs2. msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13 Hr15 Hr16). subst regs2.
rewrite !getr_other by assumption. reflexivity.
Qed.
(* L1, the byte loop before alignment: a1 = P + j, a2 = P + j + 1, bytes 0 .. j are not NUL;
   m counts the passes left until a1 + 1 is aligned *)
Lemma sl_prologue : forall m regs (j : nat),
Ps mod 8 <> 0 ->
(0 < m)%nat -> Z.of_nat j + Z.of_nat m = 8 - Ps mod 8 ->
(j < length s)%nat ->
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 (Ps + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 (Ps + Z.of_nat j + 1) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x1c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 Ls
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
induction m as [|m IH]; intros regs j HA Hm Hjm Hj H10 H11 H12; [lia|].
epl.
assert (HA8 : 0 <= Ps mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HP8 : Ps = 8 * (Ps / 8) + Ps mod 8) by (apply Z.div_mod; lia).
assert (Hm8 : 0 <= (Ps + Z.of_nat j + 1) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd (regupd regs 13 (Z_to_bv 64 (Ps + Z.of_nat j + 1)))
13 (Z_to_bv 64 ((Ps + Z.of_nat j + 1) mod 8))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x1c)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x24)) mem rom)).
{ norm_pc.
stepiv' FS_01c DS_01c (Z_to_bv 64 (Ps + Z.of_nat j + 1))
ltac:(gr; rewrite H11; imm_norm; rewrite v_addi_lit; reflexivity).
stepiv' FS_020 DS_020 (Z_to_bv 64 ((Ps + Z.of_nat j + 1) mod 8))
ltac:(gr; imm_norm; unfold v_andi; rewrite u_Z2bv by lia;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
subst regs1. msteps_done. }
destruct (Z.eq_dec ((Ps + Z.of_nat j + 1) mod 8) 0) as [Hal|Hal].
-
destruct (sl_aligned regs1 (Ps + Z.of_nat j + 1)) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs1; gr; first [reflexivity | assumption]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_024 DS_024 ltac:(subst regs1; gr; rewrite Hal; vm_compute; reflexivity).
msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16).
subst regs1. rewrite !getr_other by assumption. reflexivity.
-
set (b := nth (S j) (s ++ [NUL]) NUL).
set (regs2 := regupd (regupd (regupd regs1
13 (Z_to_bv 64 (bv_unsigned b)))
12 (Z_to_bv 64 (Ps + Z.of_nat j + 2)))
11 (Z_to_bv 64 (Ps + Z.of_nat j + 1))).
assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x24)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_strlen + 0x34)) mem rom)).
{ norm_pc.
stepbf FS_024 DS_024 ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
steplbu FS_028 DS_028
ltac:(subst regs1; gr; rewrite H12; imm_norm; rewrite v_addi_0;
replace (Ps + Z.of_nat j + 1) with (bv_unsigned p + Z.of_nat (S j)) by lia;
apply Hstr; lia).
stepiv' FS_02c DS_02c (Z_to_bv 64 (Ps + Z.of_nat j + 2))
ltac:(subst regs1; gr; rewrite H12; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepiv' FS_030 DS_030 (Z_to_bv 64 (Ps + Z.of_nat j + 1))
ltac:(subst regs1; gr; rewrite H11; imm_norm; rewrite v_addi_lit; f_equal; lia).
subst regs2 regs1 b. msteps_done. }
destruct (Nat.eq_dec (S j) (length s)) as [HjL|HjL].
+
assert (Hb : b = NUL) by (subst b; rewrite HjL; apply nth_app_nul_last).
eexists. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
norm_pc.
stepbf FS_034 DS_034 ltac:(subst regs2; gr; rewrite Hb; vm_compute; reflexivity).
stepj' FS_038 DS_038.
stepov FS_080 DS_080 (Z_to_bv 64 Ls)
ltac:(rewrite alu_sub; subst regs2 regs1; gr; rewrite H10, v_sub_w; f_equal; lia).
replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity).
stepret FS_084 DS_084. msteps_done.
* split; [gr; reflexivity|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
+
assert (Hb : b <> NUL) by (apply sl_byte_nz; lia).
assert (Hm' : (0 < m)%nat).
{ destruct m; [|lia]. exfalso. apply Hal.
replace (Ps + Z.of_nat j + 1) with (8 * (Ps / 8 + 1)) by lia.
rewrite Z.mul_comm. apply Z_mod_mult. }
destruct (IH regs2 (S j)) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs2 regs1; gr; first [reflexivity | assumption | f_equal; lia]).
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_034 DS_034
ltac:(subst regs2; gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
msteps_done.
* split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16).
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma sl_entry : forall regs,
getr regs 10 = p ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s))
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10. epl.
assert (HA8 : 0 <= Ps mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd (regupd regs 11 (Z_to_bv 64 (Ps mod 8))) 12 p).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x8)) mem rom)).
{ norm_pc.
stepiv' FS_000 DS_000 (Z_to_bv 64 (Ps mod 8))
ltac:(gr; rewrite H10; imm_norm; unfold v_andi;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
stepiv' FS_004 DS_004 p ltac:(gr; rewrite H10; imm_norm; apply v_addi_0).
subst regs1. msteps_done. }
destruct (Z.eq_dec (Ps mod 8) 0) as [HA|HA].
-
destruct (sl_aligned regs1 Ps) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs1; gr; first [assumption | (unfold Ps; symmetry; apply Z_to_bv_bv_unsigned)]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_008 DS_008 ltac:(subst regs1; gr; rewrite HA; vm_compute; reflexivity).
msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16).
subst regs1. rewrite !getr_other by assumption. reflexivity.
-
set (b := nth 0 (s ++ [NUL]) NUL).
set (regs2 := regupd regs1 11 (Z_to_bv 64 (bv_unsigned b))).
assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x8)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_strlen + 0x10)) mem rom)).
{ norm_pc.
stepbf FS_008 DS_008 ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
steplbu FS_00c DS_00c
ltac:(subst regs1; gr; rewrite H10; imm_norm; rewrite v_addi_0;
pose proof (Hstr 0%nat ltac:(lia)) as Hs0; rewrite p_lit in Hs0; exact Hs0).
subst regs2 regs1 b. msteps_done. }
destruct (Nat.eq_dec (length s) 0) as [HL0|HL0].
+
assert (Hb : b = NUL) by (subst b; rewrite <- HL0; apply nth_app_nul_last).
eexists. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
norm_pc.
stepbt FS_010 DS_010 ltac:(subst regs2; gr; rewrite Hb; vm_compute; reflexivity).
stepov FS_088 DS_088 (Z_to_bv 64 0)
ltac:(rewrite alu_sub; subst regs2 regs1; gr; rewrite H10; unfold v_sub; rewrite Z.sub_diag; reflexivity).
replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity).
stepret FS_08c DS_08c. msteps_done.
* split; [gr; rewrite HL0; reflexivity|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
+
assert (Hb : b <> NUL) by (apply sl_byte_nz; lia).
set (regs3 := regupd (regupd regs2 12 (Z_to_bv 64 (Ps + Z.of_nat 0 + 1))) 11 (Z_to_bv 64 (Ps + Z.of_nat 0))).
destruct (sl_prologue (Z.to_nat (8 - Ps mod 8)) regs3 0) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs3 regs2 regs1; gr; first [reflexivity | assumption]).
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FS_010 DS_010
ltac:(subst regs2; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FS_014 DS_014 (Z_to_bv 64 (Ps + Z.of_nat 0 + 1))
ltac:(subst regs2 regs1; gr; rewrite H10; imm_norm; unfold v_addi; f_equal; lia).
stepiv' FS_018 DS_018 (Z_to_bv 64 (Ps + Z.of_nat 0))
ltac:(subst regs2 regs1; gr; rewrite H10; imm_norm; rewrite v_addi_0; symmetry; apply p_lit).
subst regs3 regs2 regs1. msteps_done.
* split; [exact H10'|].
intros r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16. rewrite (Hfr r Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16).
subst regs3 regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
End h.
Theorem tfib_musl_strlen : forall (s : list byte) (p : word) (mem rom : word -> option byte) regs,
~ In NUL s ->
bv_unsigned p + Z.of_nat (length s) + 8 < 2 ^ 64 ->
(forall j, (j <= length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
(forall a : Z, bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 <> None) ->
(forall a : Z, YE3a.tfib_D_const_HIGHS_0x8080808080808080 <= a < YE3a.tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
getr regs 10 = p ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_strlen) mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s))
/\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
getr regs' r = getr regs r).
Proof.
intros. change (Z_to_bv 64 tfib_A_musl_strlen) with (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)).
eapply sl_entry; eassumption.
Qed.
End g.

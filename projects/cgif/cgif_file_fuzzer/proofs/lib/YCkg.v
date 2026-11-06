(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq YCbp.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0m YF0l YCej YD2l YCeh.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE2k YE32 YE2a YE25 YE6i YE6h YE28 YE2e YE24.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10 YI12 YC4a YC8i YCbj YC1f YC20 YC8g YC44 YCk4.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7x YC21.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5n YCed YCee.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCk0 YCk1 YCke.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Remark tfib_cgif_newgifX_pc : @pa_val _ _ PB_tfib A_TEXT + AF_both3_cgif_newgif = 0x80cf0.   Proof. reflexivity. Qed.
Remark tfib_cgif_newgifX_wfn : @pa_val _ _ PB_tfib A_TEXT + 0x62c = 0x8131c.   Proof. reflexivity. Qed.
Remark tfib_cgif_newgifX_sigma_rawnew : @pa_sigma _ _ PB_tfib AS_cgif_raw_newgif = 0x83dcc.   Proof. reflexivity. Qed.
Remark tfib_cgif_newgifX_sigma_fopen : @pa_sigma _ _ PB_tfib AS_fopen = FF_pc_wrap_fopen.   Proof. reflexivity. Qed.
Remark tfib_cgif_newgifX_mode : @pa_val _ _ PB_tfib (A_OBJ 4) = ak_mode tfib_K.   Proof. reflexivity. Qed.
Remark tfib_cgif_newgifX_got : @pa_val _ _ PB_tfib (A_OBJ 3) = 0x9ee80.   Proof. reflexivity. Qed.
Definition tfib_cgif_newgifX := @YCk1.pb_cgif_newgifX fx rc tfib_sink_head PB_tfib.
Check tfib_cgif_newgifX.
Definition NP_tfibX : ng_params := {| ngp_hw := 0; ngp_ctx := CTX_cgif_newgif |}.
Theorem tfib_newgifX_closed : tnewgif_x tfibsegs tfib_K TfibB ameter_triv XN0 0x80cf0 CTX_cgif_newgif 0x8131c 0x9dca8 0x9ef18.
Proof.
assert (AINTR : aintrin_realizes tfibsegs TfibB OSet PC_MEMSET).
{ intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (memset_icpt_realizes TfibB tfibX_LAWS TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham). }
refine (@YCk1.pb_cgif_newgifX fx rc tfib_sink_head PB_tfib tfibX_RO0 NP_tfibX TfibB tfibX_PALib0 tfibX_LAWS tfibX_ML
tfibX_AMEMSET tfibX_AMEMCPY tfibX_ASM1 tfibX_SMP tfibX_ASF tfibX_FFL
CTX_cgif_raw_newgif _ tfibX_PALibF0 _ _ _
tfib_K tfibX_AIL ameter_triv ameter_triv_laws ameter_triv_fs_laws tfibX_AMALLOC4 XN0 _ _ (afile_meter_trivB _ _) tfibX_AFREE4
FO_MALLOC_RA (tfib_afopen_x TfibB tfibX_LAWS TfibB_syms tfibX_AIL tfibX_env tfibX_ML tfibX_AMALLOC AINTR (tfib_ff_cells_ok TfibB TfibB_syms)) _
FC_FREE1_RA FC_JOIN (tfib_afclose_spec TfibB tfibX_LAWS TfibB_syms tfibX_AIL tfibX_env tfibX_ML tfibX_AFREE) _ _
eq_refl eq_refl (tfib_rawnewX_closed 0 ltac:(lia) eq_refl)).
-
intros l Hl. cbv [CTX_cgif_newgif ngp_ctx NP_tfibX In] in Hl.
repeat (destruct Hl as [<- | Hl]; [vm_compute; tauto|]). destruct Hl.
-   cbn. lia.
-
intros H mem HRO.
apply (tfibX_rom_cell H mem 0x9ee80 0x9ee88); [exact HRO | intros x Hx; apply tfibX_ro_relro; lia | vm_compute; reflexivity | lia | lia
| (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | vm_compute; reflexivity].
-
intros c t Hc Ht. cbv [CTX_cgif_newgif ngp_ctx NP_tfibX In] in Hc. unfold ng_traces in Ht.
apply memZL_In.
repeat (destruct Hc as [<- | Hc]; [cbn [In] in Ht; repeat (destruct Ht as [<- | Ht]; [vm_compute; reflexivity|]); destruct Ht|]). destruct Hc.
-   intros ngp Hn. unfold ng_msum, ng_macc3, ng_macc2, ng_macc1. cbn. lia.
- intros ngp Hn. unfold ng_msum, ng_macc3, ng_macc2, ng_macc1. cbn. lia.
- apply memZL_In. vm_compute. reflexivity.
- apply memZL_In. vm_compute. reflexivity.
- apply memZL_In. vm_compute. reflexivity.
Qed.
End a.

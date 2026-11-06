(* Image B twin of lib/A/RT_IImgA_ok_k.v at 18e7a8d9d50 (sha256 a25ae90bda9b; internal record): module paths lib.A -> lib.B; no image numeral moved: GXA symbol keys and code sizes kept, checked by `inst` at B's A_img (CHAINKB-numerals.tsv sha256 86a76b0550d0; internal record). *) (* The keep-FP twin's pop_arg call contracts (lib/CJ/RL/GK/G_pop_arg.v pop_arg_contract and
   lib/CJ/RL/GXK/G_pop_arg_x.v pop_arg_x_contract, see provenance/keepfx/README.md), DISCHARGED at RT_IImgA.v's
   instance A_img on the pinned fuzz_reply.asan-ubsan.  A copy of lib/A/RT_IImgA_ok.v:99-127 pointed at the twin: the
   image facts are the same vm_compute checks (IInst.v's `inst`), restated at the twin's constants, and the contracts
   close with the twin's own proofs (GK pop_arg_contract_ok, extenddftf2_contract_ok; GXK pop_arg_x_contract_ok). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import GRoTab.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GK Require Import G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK Require Import G_pop_arg_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_IImgA.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance A_img.

Lemma fr_CODE_extenddftf2 : CodeAtT img_segs (sym 0x1af98) (G_extenddftf2.PROGAT_CODE_extenddftf2 A_img). Proof. inst. Qed.
Lemma fr_RB_extenddftf2 : RelCode (sym 0x1af98) 400. Proof. inst. Qed.
Lemma fr_CODE_pop_arg : CodeAtT img_segs (sym 0x19534) (PROGAT_CODE_pop_arg A_img). Proof. inst. Qed.
Lemma fr_RB_pop_arg : RelCode (sym 0x19534) 308. Proof. inst. Qed.
Lemma fr_RO_10984 : RoB img_segs (sym 0x10984) ROT_0x10984. Proof. inst. Qed.
Lemma fr_RN_B_extenddftf2 : RelNear (sym 0x19534) (sym 0x1af98). Proof. inst. Qed.
Lemma fr_RS_K_10984 : RelSym (sym 0x10984). Proof. inst. Qed.

Lemma fr_extenddftf2_contract : @G_extenddftf2.extenddftf2_contract A_img.
Proof.
unshelve eapply G_extenddftf2.extenddftf2_contract_ok.
all: first [exact fr_CODE_extenddftf2 | exact fr_RB_extenddftf2].
Qed.
Lemma fr_pop_arg_contract : @pop_arg_contract A_img.
Proof.
unshelve eapply pop_arg_contract_ok.
all: first [exact fr_CODE_pop_arg | exact fr_RB_pop_arg | exact fr_RO_10984 | exact fr_RN_B_extenddftf2
          | exact fr_RS_K_10984 | exact fr_extenddftf2_contract].
Qed.
Lemma fr_pop_arg_x_contract : @pop_arg_x_contract A_img.
Proof.
unshelve eapply pop_arg_x_contract_ok.
all: first [exact fr_CODE_pop_arg | exact fr_RB_pop_arg | exact fr_RO_10984 | exact fr_RN_B_extenddftf2
          | exact fr_RS_K_10984 | exact fr_extenddftf2_contract | exact fr_pop_arg_contract].
Qed.

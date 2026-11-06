(* Modified by Theorem Labs, 2026-10: the build-B (asan-ubsan) copy of lib/A/Prog/IdentFrameImg.v: build-B listing names, module paths and image addresses. *)
(* IdentBFrame.PALibF for fuzz_identity.asan-ubsan's image (IdentBImg.PI_identb): the side-stack flag's GOT
   slot is object 0 (0x9c6e8, IdentBAddr.v identb_obj 0), the shadow GOT slot is object 1 (0x9c690) and the
   shadow-base cell object 31 (0xa52b8); the flag __asan_option_detect_stack_use_after_return is the 4-byte
   cell 0xa52c0 (.bss, inside the image); the side-stack entries of frame classes 0, 3 and 4 are 0x3cfe8,
   0x3d15c and 0x3d308 (IdentBAddr.v identb_sigma). The image part is proved here; what is left are the five
   equalities the allocator symbols B of fuzz_identity.asan-ubsan give, checked by computation once B is fixed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBAddr IdentBPa IdentBImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma identb_val_obj0 : @pa_val _ identb_listing PI_identb (A_OBJ 0) = 0x9c6e8.
Proof. vm_compute. reflexivity. Qed.
Lemma identb_val_obj1 : @pa_val _ identb_listing PI_identb (A_OBJ 1) = 0x9c690.
Proof. vm_compute. reflexivity. Qed.
Lemma identb_val_obj31 : @pa_val _ identb_listing PI_identb (A_OBJ 31) = 0xa52b8.
Proof. vm_compute. reflexivity. Qed.
Lemma identb_palf : forall B : asyms,
as_got_uar B = 0x9c6e8 -> as_uar_cell B = 0xa52c0 ->
pc_stack_malloc (as_code B) 0 = 0x3cfe8 -> pc_stack_malloc (as_code B) 3 = 0x3d15c ->
pc_stack_malloc (as_code B) 4 = 0x3d308 ->
PALibF (PI := PI_identb) B.
Proof.
intros B Hgot Hcell H0 H3 H4. split.
- rewrite Hgot, identb_val_obj0. reflexivity.
- rewrite Hcell. lia.
- rewrite Hcell. reflexivity.
- rewrite H0. vm_compute. reflexivity.
- rewrite H3. vm_compute. reflexivity.
- rewrite H4. vm_compute. reflexivity.
- rewrite Hcell, identb_val_obj0, identb_val_obj1, identb_val_obj31. cbn [zseps zseps_from fst snd]. lia.
Qed.
End c.

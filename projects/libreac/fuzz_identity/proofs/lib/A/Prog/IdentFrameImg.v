(* IdentFrame.PALibF for fuzz_identity.asan's image (IdentImg.PI_ident): the side-stack flag's GOT slot is
   object 0 (0x9c408, IdentAddr.v ident_obj 0), the flag __asan_option_detect_stack_use_after_return is the
   4-byte cell 0xa4fc0 (.bss, inside the image), the side-stack entries of frame classes 0, 3 and 4 are
   0x3cf80, 0x3d0f4 and 0x3d2a0 (IdentAddr.v ident_sigma). The image part is proved here; what is left are
   the five equalities the allocator symbols B of fuzz_identity.asan give, checked by computation once B is
   fixed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun IdentSyms IdentList IdentAddr IdentPa IdentImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ident_val_obj0 : @pa_val _ ident_listing PI_ident (A_OBJ 0) = 0x9c408.
Proof. vm_compute. reflexivity. Qed.
Lemma ident_val_obj1 : @pa_val _ ident_listing PI_ident (A_OBJ 1) = 0x9c3b0.
Proof. vm_compute. reflexivity. Qed.
Lemma ident_val_obj30 : @pa_val _ ident_listing PI_ident (A_OBJ 30) = 0xa4fb8.
Proof. vm_compute. reflexivity. Qed.
Lemma ident_palf : forall B : asyms,
as_got_uar B = 0x9c408 -> as_uar_cell B = 0xa4fc0 ->
pc_stack_malloc (as_code B) 0 = 0x3cf80 -> pc_stack_malloc (as_code B) 3 = 0x3d0f4 ->
pc_stack_malloc (as_code B) 4 = 0x3d2a0 ->
PALibF (PI := PI_ident) B.
Proof.
intros B Hgot Hcell H0 H3 H4. split.
- rewrite Hgot, ident_val_obj0. reflexivity.
- rewrite Hcell. lia.
- rewrite Hcell. reflexivity.
- rewrite H0. vm_compute. reflexivity.
- rewrite H3. vm_compute. reflexivity.
- rewrite H4. vm_compute. reflexivity.
- rewrite Hcell, ident_val_obj0, ident_val_obj1, ident_val_obj30. cbn [zseps zseps_from fst snd]. lia.
Qed.
End c.

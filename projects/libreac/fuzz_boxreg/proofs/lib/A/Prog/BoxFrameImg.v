(* Modified by Theorem Labs, 2026-10: BoxFrame.PALibF for fuzz_boxreg.asan's image (BoxImg.PI_box), as
   fuzz_identity's lib/A/Prog/IdentFrameImg.v (ea5560a967b) carries it for fuzz_identity.asan: module paths
   changed and every numeral re-derived from fuzz_boxreg.asan. The side-stack flag's GOT slot is object 0
   (0x98f10, BoxAddr.v box_obj 0; the .got word holds 0xa0f80), the flag
   __asan_option_detect_stack_use_after_return is the 4-byte cell 0xa0f80 (.bss, inside the image, and
   object 13 of BoxAddr.v), the shadow-base cell __asan_shadow_memory_dynamic_address is object 12
   (0xa0f78) and the only side-stack entry the listing calls is frame class 3,
   __asan_stack_malloc_3 at 0x3c520 (BoxAddr.v box_sigma BS___asan_stack_malloc_3); identity's classes 0
   and 4 have no entry in bsym. The image part is proved here; what is left are the three equalities the
   allocator symbols B of fuzz_boxreg.asan give, checked by computation once B is fixed. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun BoxSyms BoxList BoxAddr BoxPa BoxImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_val_obj0 : @pa_val _ box_listing PI_box (A_OBJ 0) = 0x98f10.
Proof. vm_compute. reflexivity. Qed.
Lemma box_val_obj1 : @pa_val _ box_listing PI_box (A_OBJ 1) = 0x98eb8.
Proof. vm_compute. reflexivity. Qed.
Lemma box_val_obj12 : @pa_val _ box_listing PI_box (A_OBJ 12) = 0xa0f78.
Proof. vm_compute. reflexivity. Qed.
Lemma box_val_obj13 : @pa_val _ box_listing PI_box (A_OBJ 13) = 0xa0f80.
Proof. vm_compute. reflexivity. Qed.
Lemma box_palf : forall B : asyms,
as_got_uar B = 0x98f10 -> as_uar_cell B = 0xa0f80 ->
pc_stack_malloc (as_code B) 3 = 0x3c520 ->
PALibF (PI := PI_box) B.
Proof.
intros B Hgot Hcell H3. split.
- rewrite Hgot, box_val_obj0. reflexivity.
- rewrite Hcell. lia.
- rewrite Hcell. reflexivity.
- rewrite H3. vm_compute. reflexivity.
- rewrite Hcell, box_val_obj0, box_val_obj1, box_val_obj12. cbn [zseps zseps_from fst snd]. lia.
Qed.
End c.

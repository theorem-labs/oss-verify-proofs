(* Window guard for seg_K of the B (asan-ubsan) walk of LLVMFuzzerTestOneInput (measured
   2026-10-29). kkeep's first clause keeps every byte >= alloc_ceiling outside [mf - (16 + 2 * ESTACK), mf); it holds
   only if every callee seg_K calls at sp = mf stays inside that window. The callees were measured on the image
   (__wrap_strlen x3, check_str x3, __wrap_strcmp x3, reac_box_catalogue x1, reac_box_catalogue_defect x2; no memchr)
   and their maximum window was equal to the bound, i.e. zero slack. This lemma states each callee's contract window
   against the bound, so a future growth of any of them fails this build instead of silently falsifying kkeep. The
   wrappers' window is [sp - 2 * ESTACK, sp) (lib/B/Rt/StrlenDef.v, lib/Reusable/AStrcmpDef.v). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require check_str reac_box_catalogue reac_box_catalogue_defect.
Open Scope Z_scope.

Lemma k_callee_windows :
  check_str.CHECK_STR_STK <= 16 + 2 * ESTACK /\
  reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK <= 16 + 2 * ESTACK /\
  reac_box_catalogue.CAT_STK <= 16 + 2 * ESTACK /\
  2 * ESTACK <= 16 + 2 * ESTACK.
Proof. vm_compute. repeat split; discriminate. Qed.

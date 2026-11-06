(* The two functions calloc and __malloc_allzerop by name, at segconf's concrete instance (plain build).
   calloc (plain 0x16904): calloc_contract_big (CallocBigC.v) at src0_msyms / zlib_API / CALLOC_PC, and its cut-free
   twin for the agreement. __malloc_allzerop (plain 0x18270): the run lemma CallocAZ.az_SR (from the allocator state
   free_pre to its return, a0 <> 0 only when the block is all zero), which CallocBig.v consumes inside calloc. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26 YN0b YN07 YN0a YN09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import CallocAZ ZAllocator CallocBigC CallocBigOk.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem calloc_holds : calloc_contract_big src0_msyms zlib_API CALLOC_PC.
Proof using. exact zlib_calloc_contract_big. Qed.
Theorem calloc_cf_holds : calloc_contract_big_cf src0_msyms zlib_API CALLOC_PC.
Proof using. exact zlib_calloc_contract_big_cf. Qed.
Definition malloc_allzerop_contract : Prop :=
  forall k r v m md, free_pre k r v m -> YK0s.ret_ok (getr (fv_regs v) 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg (mkst (fv_regs v) (Z_to_bv 64 src0_A_malloc_allzerop) m (seg_rom src0segs)) md)
(fun c' => exists regs', c' = mkCfg (mkst regs' (getr (fv_regs v) 1) m (seg_rom src0segs)) md /\
(forall i : reg, (bv_unsigned i < 10 \/ 16 < bv_unsigned i) -> getr regs' i = getr (fv_regs v) i) /\
(getr regs' 10 <> Z_to_bv 64 0 -> az_true k v)).
Theorem malloc_allzerop_holds : malloc_allzerop_contract.
Proof using. exact az_SR. Qed.
End a.

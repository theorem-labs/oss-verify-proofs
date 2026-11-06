From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26 YN0b YN07 YN0a YN09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import CallocAZ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM06_cf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN0b_cf.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem az_SR_cf : forall k r v m md, free_pre k r v m -> YK0s.ret_ok (getr (fv_regs v) 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
SR_cfv src0segs (mkCfg (mkst (fv_regs v) (Z_to_bv 64 src0_A_malloc_allzerop) m (seg_rom src0segs)) md)
(fun c' => exists regs', c' = mkCfg (mkst regs' (getr (fv_regs v) 1) m (seg_rom src0segs)) md /\
(forall i : reg, (bv_unsigned i < 10 \/ 16 < bv_unsigned i) -> getr regs' i = getr (fv_regs v) i) /\
(getr regs' 10 <> Z_to_bv 64 0 -> az_true k v)).
Proof using.
intros k r v m md FP Hra Hh Hlz.
destruct (az_facts k r) as (Hrun & Hkeep & Ha0 & Hrv).
eapply SR_cfv_bind; [exact (YN0b_cf.SR_run_to (AZ_RET k) _ _ _ _ md (az_entry k r v m FP) Hrun Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HF1).
assert (Hm1 : ms_mem ms1 = m).
{ apply FunctionalExtensionality.functional_extensionality. intros x.
exact (HF1 x (in_wrange_nowin _ (free_mem k r) _)). }
destruct Hrun as [_ Hpc].
rewrite (st_ok_mkst src0segs _ _ _ HS1 Hrv), Hm1, Hpc.
assert (KEEP : forall i : reg, (bv_unsigned i < 10 \/ 16 < bv_unsigned i) -> getr (ms_regs ms1) i = getr (fv_regs v) i).
{ intros i Hi. rewrite (st_ok_reg src0segs _ _ _ i HS1), (free_regs_ok v i). f_equal. apply keep_get; assumption. }
assert (A0 : getr (ms_regs ms1) 10 = sv_denot (EV (xvf v)) (az_a0 k)).
{ rewrite (st_ok_reg src0segs _ _ _ 10%bv HS1). rewrite <- Ha0. reflexivity. }
assert (R1e : getr (ms_regs ms1) 1 = getr (fv_regs v) 1) by (apply KEEP; left; reflexivity).
eapply SR_cfv_step; [exact Hh | exact Hlz | reflexivity | |].
{ eapply step_jalr_x0; [apply fetch_az_ret | reflexivity | exact decode_az_ret | exact R1e]. }
cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hra. rewrite Hra.
apply SR_cfv_ret. exists (ms_regs ms1). split; [reflexivity|]. split; [exact KEEP|].
intros Hnz. rewrite A0 in Hnz. exact (az_a0_true k r v m FP Hnz).
Qed.
End a.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YH00 YH03 YN0b_cf YN07_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.Q Require Import YW0e_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM06_cf YO0d_cf.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record arr_ok (E : env) (r : rcase) (mem0 : word -> option byte) (regs4 : bvmap 5 word) (mem4 : word -> option byte) : Prop := ARR {
ar_ra : getr regs4 1 = Z_to_bv 64 RA_MALLOC;
ar_sp : getr regs4 2 = sv_denot E (SOff aSP (-64));
ar_s0 : getr regs4 8 = sv_denot E (SOff aN 0);
ar_s1 : getr regs4 9 = sv_denot E (SOff aP 0);
ar_a0 : getr regs4 10 = sv_denot E (SOff aN 0);
ar_s2 : getr regs4 18 = sv_denot E (ENDR r);
ar_keep : forall i, In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr regs4 (nat_to_reg i) = sv_denot E (SOff i 0);
ar_frame : Forall (chunk_ok src0segs E mem4 (base_val E (Some aSP))) frame_chunks;
ar_stk : forall o, -8256 <= o < 0 -> writable_at src0segs mem4 (base_val E (Some aSP) + o);
ar_err : forall o, -164 <= o < -160 -> writable_at src0segs mem4 (base_val E (Some aTP) + o);
ar_raw : forall x, ~ in_wrange E (entry_mem r) (bv_unsigned x) -> mem4 x = mem0 x }.
Definition arrives (E : env) (r : rcase) (mem0 : word -> option byte) (md : Model) (c : config) : Prop :=
exists regs4 mem4, c = mkCfg (mkst regs4 (Z_to_bv 64 src0_A_libc_malloc_impl) mem4 (seg_rom src0segs)) md /\
arr_ok E r mem0 regs4 mem4.
End a.

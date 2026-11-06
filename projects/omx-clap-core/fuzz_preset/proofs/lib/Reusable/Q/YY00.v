From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN03 YN02 YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN0b YN07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FB_SLOTS : list (Z * nat) :=
[(-64, 22%nat); (-56, 21%nat); (-48, 20%nat); (-40, 19%nat); (-32, 18%nat); (-24, 9%nat); (-16, 8%nat); (-8, 1%nat)].
Definition fb_stk (regs : bvmap 5 word) (x : Z) : Prop := spZ regs - REALLOC_STACK <= x < spZ regs.
Definition fb_errno (x : Z) : Prop := errno_addr src0_msyms <= x < errno_addr src0_msyms + 4.
Record fb_arrival (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (nold n : Z) (regs4 : bvmap 5 word) (mem4 : word -> option byte) : Prop := FBA {
fa_pre : call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md;
fa_in : In (p, nold) (user_blocks A);
fa_a0 : getr regs 10 = Z_to_bv 64 (ptr_addr L p);
fa_a1 : getr regs 11 = Z_to_bv 64 n;
fa_n : 0 <= n < 2 ^ 62;
fa_ra : getr regs4 1 = Z_to_bv 64 RA_MALLOC;
fa_sp : getr regs4 2 = Z_to_bv 64 (spZ regs - 64);
fa_s0 : getr regs4 8 = Z_to_bv 64 n;
fa_s1 : getr regs4 9 = Z_to_bv 64 (ptr_addr L p);
fa_arg : getr regs4 10 = Z_to_bv 64 n;
fa_s2 : getr regs4 18 = Z_to_bv 64 (ptr_addr L p + nold);
fa_keep : forall i, In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr regs4 (nat_to_reg i) = getr regs (nat_to_reg i);
fa_frame : forall o r i, In (o, r) FB_SLOTS -> 0 <= i < 8 ->
mbyte src0segs mem4 (spZ regs + o + i) = Some (byte_of_word (getr regs (nat_to_reg r)) i);
fa_stk : forall x, fb_stk regs x -> writable_at src0segs mem4 x;
fa_err : forall x, fb_errno x -> writable_at src0segs mem4 x;
fa_raw : forall x, 0 <= x < 2 ^ 64 -> ~ fb_stk regs x -> ~ fb_errno x -> mem4 (Z_to_bv 64 x) = mem (Z_to_bv 64 x) }.
Definition OBL_fb_gen : Prop :=
forall L A regs mem md p nold n regs4 mem4,
fb_arrival L A regs mem md p nold n regs4 mem4 ->
mreal src0segs (mkCfg (mkst regs4 (Z_to_bv 64 src0_A_libc_malloc_impl) mem4 (seg_rom src0segs)) md)
(realloc_move p n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n).
End a.

(* The contract of ___errno_location on fuzz_link.asan (0x90a7c, 12 bytes) in the form a caller's walk applies at its
   call site: SRr from cfg_at, as the runtime contracts of lib/A/Rt/RtString.v are stated. The code is

     0x90a7c  mv   a0, tp          00020513
     0x90a80  addi a0, a0, -164    f5c50513
     0x90a84  ret                  00008067

   so the entry writes a0 := tp - 164 (mod 2^64), no other register (ret writes x0) and no memory, and returns to ra.
   Premises, per instruction:
   - `YK0s.ret_ok (getr regs 1)`: the `ret` at 0x90a84 jumps to ra with bit 0 cleared; the configuration after it is
     cfg_at (raZ regs) only when ra is the value the clearing leaves unchanged.
   - `AR segs B ly S W mem md`: no instruction reads it; it is there so that the post can give AR of the memory and
     the model after the call, as every runtime contract's post does (art_post, RtDefs.v). A step may materialize
     lazy pages of the model, so the post names the new model md' with same_but_materialized md md'.
   No byte of the stack is used: the contract has no stack window and no stack premise.
   The post: the world is unchanged; the call returns to ra; a0 = tp - 164; every other register x1..x31 is as at
   entry; every memory cell is as at entry. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition aerrno_location_realizes (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall ly S (W : world segs) regs mem md,
AR segs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at segs (raZ regs) regs' mem' md' /\
  AR segs B ly S W mem' md' /\ same_but_materialized md md' /\
  getr regs' 10 = w64 (bv_unsigned (getr regs 4) - 164) /\
  (forall r, 1 <= r < 32 -> r <> 10 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  (forall x, mem' x = mem x)).

End b.

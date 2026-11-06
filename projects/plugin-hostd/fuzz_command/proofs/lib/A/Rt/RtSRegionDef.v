From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
Import ListNotations.
Open Scope Z_scope.

(* The range check __asan_region_is_poisoned (0x5a1ac) with its scratch window as a parameter. The contract
   aregion_poisoned_zero_realizes (RtString.v) states it under ecall_pre, which asks for ESTACK bytes of stack
   below the entry sp. The string entries call the range check from inside their own frame (2,144 to 2,192
   bytes), and strlen, memchr and strcpy have a window of ESTACK only, so at their call the ESTACK form does not
   compose (2,144 + 4,096 > 4,096). The code writes 72 bytes below its entry sp (its own frame of 64 bytes, and
   mem_is_zero's ra at 16 - 8 below that), so this form asks for [stk] bytes with
   72 <= stk instead of ecall_pre's ESTACK. The checked size is n > 64: every check site calls the range check
   only when its size is over 64, and for a small n the code can reach CheckFailed (when
   x mod 8 <> 0 and RoundUp(x, 8) is the end of a memory range, MemToShadow 0x59d20 on it fails its AddrIsInMem
   CHECK; found by the walk of RtSRegion.v), so this form and the contract both take n > 64. The other premises
   and the conclusion are those of the contract with ESTACK replaced by [stk]; [aregion_zero_contract] below gives
   the contract from it. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Definition RGN_SCR : Z := 72.

Definition aregion_zero_at (stk pc : Z) : Prop :=
forall ly S W regs mem md x n,
AR segs B ly S W mem md ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + stk <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 64 < n < 2 ^ 32 -> 0 < x ->
aread_ok segs stk W regs mem x n ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(art_post segs B stk ly S W regs mem md (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0)).

Definition aregion_zero_stk (pc : Z) : Prop := forall stk, RGN_SCR <= stk -> aregion_zero_at stk pc.

Lemma aregion_zero_contract : forall pc, aregion_zero_stk pc -> aregion_poisoned_zero_realizes segs B pc.
Proof.
intros pc H ly S W regs mem md x n HPRE G10 G11 Hn Hx HRD HROM.
destruct HPRE as ((HAR & Hra & Hal & _ & Hhi & _ & _ & _) & Hlo & Hpres).
assert (HS : RGN_SCR <= ESTACK) by (unfold RGN_SCR, ESTACK; lia).
exact (H ESTACK HS ly S W regs mem md x n HAR Hra Hal Hlo Hhi Hpres G10 G11 Hn Hx HRD HROM).
Qed.

End c.
End b.

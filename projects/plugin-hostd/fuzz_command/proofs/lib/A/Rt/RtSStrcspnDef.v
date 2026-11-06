(* The interface between the two halves of the strcspn walk (contract RtString.astrcspn_realizes at the trampoline
   PC_strcspn 0x4514c of plugin-hostd/fuzz_command's ASan build).

   ___interceptor_strcspn 0x46c98 calls musl's strcspn 0x9f2b4 through the REAL slot 0xa8140 at 0x46cec
   (`jalr a2`, return address 0x46cf0), with its own frame of 2032 + 128 = 2160 bytes below the caller's sp. musl's
   strcspn has a frame of 80 bytes; it calls the memset interceptor 0x57628 (`jal` at 0x9f304, the 32-byte bitset at
   its own sp) under aintrin_realizes OSet (window ESTACK), and strchrnul 0x9f0b4 (frame 16) at 0x9f388, which calls
   the strlen interceptor 0x45130 (`jal` at 0x9f154) under RtString.astrlen_realizes (window ESTACK) when the set is
   empty. Its deepest window below its entry sp is therefore 80 + 16 + ESTACK = MCSPN_K (the memset path needs
   80 + ESTACK). The interceptor calls it at 2160 below its own entry sp, and 2160 + MCSPN_K = 6352 <= 2 * ESTACK.

   amcspn_realizes is the contract of musl's strcspn at that window, in the form RtString.astrcspn_realizes states
   the interceptor's: the musl half of the walk proves it (at MCSPN_ENTRY, with A_SSP_GOT and A_SSP_GUARD), and the
   interceptor half takes it at its REAL call. The set argument needs no tail premise: musl's strcspn reads the set
   byte by byte. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strcspn_c.
Import ListNotations.
Open Scope Z_scope.

Definition MCSPN_ENTRY : Z := 0x9f2b4.
Definition MCSPN_RA : Z := 0x46cf0.
Definition MCSPN_K : Z := 80 + 16 + ESTACK.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition amcspn_realizes (B : asyms) (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x y str set,
aguard_ok tfibsegs W mem gotw guard ->
ecall_pre_stk tfibsegs B MCSPN_K ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
astr_at tfibsegs W mem x str -> astr_at tfibsegs W mem y set ->
aread_ok tfibsegs MCSPN_K W regs mem x (astr_len str + 1) ->
aread_ok tfibsegs MCSPN_K W regs mem y (astr_len set + 1) ->
atail_vis tfibsegs W mem (x + astr_len str) ->
rt_rom_view tfibsegs B W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(art_post tfibsegs B MCSPN_K ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 (Z.of_nat (strcspn_c.cspn_len set str)))).

End b.

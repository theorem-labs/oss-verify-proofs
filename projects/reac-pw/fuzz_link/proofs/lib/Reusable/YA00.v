(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA00.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK16 YK11 YK15 YK18 YK0y YK00 YK01 YK13 YK0v YK02 YK04 YK0g YK06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YA05.
Local Instance asanfixedcommit_fx : YK11.FPState := YK11.fx0.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
Definition FixedCommit2 (segs : list Segment) : Prop :=
forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
(prot = 0 \/ prot = 3)%Z ->
mmap_flags_core flags = 50%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs us [] [] =>
if errno_ret_in mmap_errnos r
then match zs, us with
| [], [] => CheckOk model []
| _, _ => CheckReject
end
else if (Z.eqb prot 0)
then match zs with
| [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
else match us with
| [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
| _ => CheckReject
end.

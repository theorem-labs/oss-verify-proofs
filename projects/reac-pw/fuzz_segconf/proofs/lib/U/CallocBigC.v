(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 52 of its 66 lines of code are new or changed and 52 lines of the source are left out. *)
(* segconf's calloc (musl mallocng; plain 0x16904) with no 4096-byte cap: the statements only.
   calloc_realizes_big / _cf: YO0d.calloc_realizes and knock's AllocCallocCf.calloc_realizes_cf without the
   ms_calloc premise (this frame fixes ms_calloc = None) and with the cap m * n <= CALLOC_BIG_CAP.
   calloc_contract_big / _cf: Contract.calloc_contract and SlotAgree.calloc_contract_cf, changed the same way.
   Proofs: CallocBig.v, CallocBig_cf.v (certificates), CallocBigOk.v (contracts). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i YM06_cf YO0d_cf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract AllocSlots SlotAgree.
Import ListNotations.
Local Open Scope Z_scope.

(* The largest m * n the contracts cover. segconf asks for 1 * 9236 and (cap + 1) * 18, (cap + 1) * 20 with
   cap < 40 (LLVMFuzzerTestOneInput ubsan 0x13980, 0x13e7c, 0x13e8c). *)
Definition CALLOC_BIG_CAP : Z := 65536.

(* calloc's entry: ubsan 0x172a0 (plain 0x16904), 312 bytes. *)
Definition CALLOC_PC : Z := 0x172a0.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.

Definition calloc_realizes_big (pc : Z) : Prop :=
  forall L A regs mem md m n,
  call_pre_k B MR CALLOC_STACK L A regs mem md ->
  getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n ->
  0 <= m -> 0 <= n -> m * n <= CALLOC_BIG_CAP ->
  (forall a, match find_segment segs (bv_unsigned a) 1 with Some seg => negb (seg_writable seg) | None => false end = true ->
    match mem a with Some b => Some b | None => seg_rom segs a end = seg_rom segs a) ->
  @mreal segs AcfgMode _ (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
    (malloc (m * n) A)
    (calloc_leaf B MR L A regs mem md (m * n)).

Definition calloc_realizes_big_cf (pc : Z) : Prop :=
  forall L A regs mem md m n,
  call_pre_k B MR CALLOC_STACK L A regs mem md ->
  getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n ->
  0 <= m -> 0 <= n -> m * n <= CALLOC_BIG_CAP ->
  (forall a, match find_segment segs (bv_unsigned a) 1 with Some seg => negb (seg_writable seg) | None => false end = true ->
    match mem a with Some b => Some b | None => seg_rom segs a end = seg_rom segs a) ->
  mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
    (malloc (m * n) A)
    (calloc_leaf B MR L A regs mem md (m * n)).
End R.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition calloc_contract_big (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n <= CALLOC_BIG_CAP ->
    res_ok_slots A b -> room_slots b (m * n) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n -> mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

Definition calloc_contract_big_cf (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n <= CALLOC_BIG_CAP ->
    res_ok_slots A b -> room_cf md b (m * n) ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n -> mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).
End C.

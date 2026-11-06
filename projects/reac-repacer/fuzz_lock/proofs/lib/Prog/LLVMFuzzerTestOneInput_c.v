(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths, addresses and numbers changed; 39 of its 99 lines of code are new or changed and 7 lines of the source are left out. *)
(* Contract of fuzz_lock's LLVMFuzzerTestOneInput (fuzz_lock.c:181-207) in fuzz_lock.plain, 0x12b78, in the form of
   libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_c.v (release 25e3d17bdb50), with the return value
   lock_ret pl, 0 or -1, in place of decode's 0. Written by Theorem Labs.

   The image facts are fuzz_lock.plain's, read from the unstripped ELF
   unstripped/fuzz_lock/fuzz_lock.plain of reac-repacer's pinned build (the twin of the pinned fuzz_lock.plain)
   with pyelftools (python3: ELFFile(...).get_section_by_name('.symtab'), the st_value of each symbol; the .got slot
   whose value is __stack_chk_guard):
     LLVMFuzzerTestOneInput 0x12b78, malloc 0x13fdc, free 0x13e9c, __stack_chk_guard 0x4df40 (its .got slot
     0x1c958), RATES 0x10390 (40 bytes of .rodata: 44100, 48000, 96000, 88200, 0).
   They are the values FrameAPI.v binds (ENTRY, ms_malloc, ms_free, ms_guard, ms_got_guard). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import check_no_overread_c check_lookup_c
  FrameRet.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x12b78.
(* addi sp, sp, -0x40 at 0x12b90; the deeper of the two callees is check_lookup (CL_STACK >= CNO_STACK) *)
Definition LLVM_FRAME : Z := 64.
Definition LLVM_K : Z := LLVM_FRAME + CL_STACK.
Definition LLVM_MALLOC : Z := 0x13fdc.
Definition LLVM_FREE : Z := 0x13e9c.
Definition LLVM_GUARD_GOT : Z := 0x1c958.
Definition LLVM_GUARD : Z := 0x4df40.

Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := frame_RELRO.
Definition llvm_GI : nat -> (word -> option byte) -> Prop := fun _ _ => True.

(* fuzz_lock.c:196: a name byte that is NUL, LF or a separator (space, tab, CR) *)
Definition lock_bad (b : byte) : bool := (bz b =? 0) || (bz b =? 10) || is_sep (bz b).

(* The value LLVMFuzzerTestOneInput returns on the payload pl (fuzz_lock.c:185-206; FUZZ_INPUT_MAX = 64 MiB, fuzz.h:18):
   0 for a payload too short or too long, -1 for a name of length 0 or one holding a bad byte, else 0 after the
   two checks. *)
Definition lock_ret (pl : list byte) : Z :=
  let n := Z.of_nat (length pl) in
  let k := bz (nth 1 pl (Z_to_bv 8 0)) mod 16 in
  if (n <? 2) || (2 ^ 26 <=? n) then 0
  else if n <? 2 + k then 0
  else if k =? 0 then -1
  else if existsb lock_bad (firstn (Z.to_nat k) (skipn 2 pl)) then -1
  else 0.

Lemma lock_ret_cases : forall pl, lock_ret pl = 0 \/ lock_ret pl = -1.
Proof.
  intros pl. unfold lock_ret. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; auto.
Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition llvm_binds : Prop :=
  ms_segs B = rsegs /\ ms_malloc B = LLVM_MALLOC /\ ms_free B = LLVM_FREE /\
  ms_got_guard B = LLVM_GUARD_GOT /\ ms_guard B = LLVM_GUARD /\ AllocExtra B MR.

Definition llvm_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX.

Definition llvm_ls_laws : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL (lock_ret pl) fs []))) /\
  (forall b n, lib_room b n -> llvm_room b) /\
  (forall n b, lib_delta n b = b).

(* YL0g.v lib_post, with the return register equal to r *)
Definition lib_post_r (G : list (Z * Z)) (r stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p : Z)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
  getr regs' 10 = Z_to_bv 64 r /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B stk regs a -> writable_at segs mem' a).

Definition LLVMFuzzerTestOneInput_contract : Prop :=
  llvm_binds -> llvm_ls_laws ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_gr B API lock_ret llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

Definition LLVMFuzzerTestOneInput_sr_contract : Prop :=
  llvm_binds ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b,
    lib_pre B API stk empty L A regs mem md ra p n ->
    n = Z.of_nat (length pl) -> blk_data B mem p pl ->
    sink_none B mem md -> spZ regs <= 2 ^ 47 ->
    res_ok_slots A b ->
    llvm_room b ->
    ro_agree rsegs mem -> G_img_c B llvm_RELRO mem ->
    llvm_GI j mem ->
    frm_zero fp_csr ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         lib_post_r llvm_G (lock_ret pl) stk L A regs mem md p L' A' regs' mem' md' /\
         sink_none B mem' md' /\
         res_ok_slots A' b /\
         (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
         ro_agree rsegs mem' /\
         llvm_GI (S j) mem').

End K.

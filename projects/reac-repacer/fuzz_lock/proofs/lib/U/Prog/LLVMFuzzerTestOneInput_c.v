(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths, addresses and numbers changed; 51 of its 103 lines of code are new or changed and 15 lines of the source are left out. *)
(* Contract of fuzz_lock's LLVMFuzzerTestOneInput (fuzz_lock.c:181-207) in fuzz_lock.ubsan, 0x12bbc, in the form of
   libreac/fuzz_decode's lib/U/Prog/LLVMFuzzerTestOneInput_c.v, for a function that returns 0 or -1: the return
   register holds lock_ret pl (lib_post_r, lib_contract_gr of U/Prog/FrameRet.v). lock_bad and lock_ret are the
   text of lib/Prog/LLVMFuzzerTestOneInput_c.v, stated over U/Spec/LockSpec's bz and is_sep (the UBSan files
   import only lib/U files). The frame is 64 bytes (addi sp, sp, -0x40 at 0x12bbc); the deepest callee is
   check_lookup (CL_STACK). Image facts: malloc 0x14178, free 0x14038, the stack guard's GOT slot 0x1caf8 and
   __stack_chk_guard 0x4e0e0, the RELRO ranges of U/FrameAPI.v frame_RELRO (all as U/FrameAPI.v frame_ubsan
   binds them). Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import check_no_overread_c check_lookup_c FrameRet.
Import ListNotations.
Local Open Scope Z_scope.

(* as in lib/Prog/LLVMFuzzerTestOneInput_c.v: the return value of fuzz_lock.c:181-207 on the payload pl *)
Definition lock_bad (b : byte) : bool := (bz b =? 0) || (bz b =? 10) || is_sep (bz b).
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
  intros pl. unfold lock_ret.
  destruct (_ || _); [left; reflexivity|].
  destruct (_ <? _); [left; reflexivity|].
  destruct (_ =? 0); [right; reflexivity|].
  destruct (existsb _ _); [right | left]; reflexivity.
Qed.

Definition LLVM_ENTRY : Z := 0x12bbc.
Definition LLVM_FRAME : Z := 64.
Definition LLVM_K : Z := LLVM_FRAME + CL_STACK.
Definition LLVM_MALLOC : Z := 0x14178.
Definition LLVM_FREE : Z := 0x14038.
Definition LLVM_GUARD_GOT : Z := 0x1caf8.
Definition LLVM_GUARD : Z := 0x4e0e0.

Definition llvm_G : list (Z * Z) := [].
Definition llvm_RELRO : list (Z * Z) := [(0x1ca58, 160); (0x1cb00, 16)].
Definition llvm_GI : nat -> (word -> option byte) -> Prop := fun _ _ => True.

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

(* Reusable/YL0g.v lib_post with the return register equal to r *)
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

(* the post of the contract, as a definition so that a walk may rewrite its own goal with ms_segs B = rsegs *)
Definition llvm_post (r stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ra p n : Z) (b : sbound) (j : nat) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_r llvm_G r stk L A regs mem md p L' A' regs' mem' md' /\
    sink_none B mem' md' /\
    res_ok_slots A' b /\
    (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
    ro_agree rsegs mem' /\
    llvm_GI (S j) mem'.

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
      (llvm_post (lock_ret pl) stk L A regs mem md ra p n b j).

End K.

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Export URz.
Import ListNotations.
Local Open Scope Z_scope.

Definition BUF_OF : Z := 0x140f0.
Definition MALLOC : Z := 0x15ab4.
Definition BUF_OF_FRAME : Z := 16.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RzCi : RzC}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Context {RzAi : RzA B API}.

Definition buf_of_contract : Prop :=
  forall L A regs mem md c b,
    ms_segs B = rsegs -> ms_malloc B = MALLOC -> errno_addr B + 4 <= alloc_ceiling ->
    call_pre_k B MR (BUF_OF_FRAME + ALLOC_STACK) L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 c -> 0 <= c <= 2 ^ 28 - 1 ->
    res_ok_slots A b -> RzRoom md b (Z.max c 1) ->
    Rz segs (mkCfg (mkst regs (Z_to_bv 64 BUF_OF) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' q,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR (BUF_OF_FRAME + ALLOC_STACK) L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 q /\
         q <> 0 /\ q mod 16 = 0 /\ fresh_block B q (Z.max c 1) /\
         (exists b1 b2, blocks L' A' = b1 ++ (q, Z.max c 1) :: b2 /\ blocks L A = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_malloc b (Z.max c 1))).

End K.

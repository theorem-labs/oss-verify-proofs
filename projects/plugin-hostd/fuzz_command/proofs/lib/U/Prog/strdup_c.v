From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition STRDUP : Z := 0x20f68.
Definition STRDUP_STACK : Z := ALLOC_STACK + 32.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition strdup_contract : Prop :=
  forall L A regs mem md (s : Z) (str slack : list byte) b,
    call_pre_k B MR STRDUP_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 s ->
    (forall i, (i < length (str ++ Z_to_bv 8 0 :: slack))%nat ->
       mbyte segs mem (s + Z.of_nat i) = nth_error (str ++ Z_to_bv 8 0 :: slack) i) ->
    ~ In (Z_to_bv 8 0) str ->
    (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    0 <= s ->
    (s + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= spZ regs - STRDUP_STACK \/
     (spZ regs <= s /\ s + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= 2 ^ 64)) ->
    str_home B L A (spZ regs) s (Z.of_nat (length str) + 1) ->
    Z.of_nat (length str) + 1 <= 2 ^ 28 ->
    res_ok_slots A b -> room_slots b (Z.of_nat (length str) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 STRDUP) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' d,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR STRDUP_STACK L A regs mem md (fun a => d <= a < d + Z.of_nat (length str) + 1)
           L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 d /\ d <> 0 /\ d mod 16 = 0 /\
         fresh_block B d (Z.of_nat (length str) + 1) /\
         (exists b1 b2, blocks L' A' = b1 ++ (d, Z.of_nat (length str) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (forall i, (i < S (length str))%nat -> mbyte segs mem' (d + Z.of_nat i) = nth_error (str ++ [Z_to_bv 8 0]) i) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\ st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_malloc b (Z.of_nat (length str) + 1))).

End K.

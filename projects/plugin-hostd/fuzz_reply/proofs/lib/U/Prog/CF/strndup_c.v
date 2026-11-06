From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition STRNDUP : Z := 0x1de84.
Definition STRNDUP_STACK : Z := ALLOC_STACK + 32.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* Over any resource form F of the frame (Contract.v Section Forms): the allocator call consumes rf_room F b (l + 1)
   and the post gives rf_ok F A' (rf_malloc F b (l + 1)). strndup_contract is the instance at sb_form. *)
Definition strndup_contract_r (F : ResForm) : Prop :=
  forall L A regs mem md (s n : Z) (buf : list byte) b,
    call_pre_k B MR STRNDUP_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
    (forall i, (i < length buf)%nat -> mbyte segs mem (s + Z.of_nat i) = nth_error buf i) ->
    memchr_ok s 0 n buf ->
    0 < s < 2 ^ 64 ->
    (s + Z.of_nat (length buf) <= spZ regs - STRNDUP_STACK \/
     (spZ regs <= s /\ s + Z.of_nat (length buf) <= 2 ^ 64)) ->
    str_home B L A (spZ regs) s (strnlen_res n buf) ->
    strnlen_res n buf + 1 <= 2 ^ 28 ->
    rf_ok F A b -> rf_room F b (strnlen_res n buf + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 STRNDUP) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' d,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR STRNDUP_STACK L A regs mem md (fun a => d <= a < d + strnlen_res n buf + 1)
           L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 d /\ d <> 0 /\ d mod 16 = 0 /\
         fresh_block B d (strnlen_res n buf + 1) /\
         (exists b1 b2, blocks L' A' = b1 ++ (d, strnlen_res n buf + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (forall i, (i <= Z.to_nat (strnlen_res n buf))%nat ->
            mbyte segs mem' (d + Z.of_nat i) = nth_error (firstn (Z.to_nat (strnlen_res n buf)) buf ++ [Z_to_bv 8 0]) i) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\ st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rf_ok F A' (rf_malloc F b (strnlen_res n buf + 1))).

Definition strndup_contract : Prop := strndup_contract_r sb_form.

End K.

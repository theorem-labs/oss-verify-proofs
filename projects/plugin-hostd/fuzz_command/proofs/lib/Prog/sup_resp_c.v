From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInvP RecKindB xstrdup_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_RESP : Z := 0x158c8.
Definition SUP_RESP_K : Z := 48 + XSTRDUP_K.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_resp_contract : Prop :=
  forall L A regs mem md (code : Z) b,
    call_pre_t B API SUP_RESP_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_malloc b (Z.of_nat (length (resp code)) + 1)) (Z.of_nat (length (resp code)) + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_RESP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' q,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         fp_kept fx fx' /\
         call_post_k B MR SUP_RESP_K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 q /\ q <> 0 /\ q mod 16 = 0 /\
         fresh_block B q (Z.of_nat (length (resp code)) + 1) /\
         (exists b1 b2, blocks L' A' = b1 ++ (q, Z.of_nat (length (resp code)) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
         Mem.bytes_at segs mem' q (resp code ++ [Z_to_bv 8 0]) /\
         (forall R O, g_rec_rep segs L A mem R O -> g_rec_rep segs L' A' mem' (fst (sup_resp_m R code)) O) /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_malloc b (Z.of_nat (length (resp code)) + 1))).

End K.
